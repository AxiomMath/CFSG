module

public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {W : Type*} [CommGroup W] [Finite W]

private theorem e9_one_le_rk_commV (hV : ∀ v : W, v ^ 2 = 1) {t : MulAut W} (ht1 : t ≠ 1) :
    1 ≤ rk (commV (Subgroup.zpowers t)) := by
  by_contra h
  have h0 : rk (commV (Subgroup.zpowers t)) = 0 := by omega
  have hbot := (rk_eq_zero_iff hV).mp h0
  apply ht1
  ext v
  have : t v * v⁻¹ ∈ commV (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, rfl⟩
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this

private theorem e9_mem_sup_of_comm {G : Type*} [Group G] {K P : Subgroup G}
    (h : ∀ a ∈ K, ∀ b ∈ P, a * b = b * a) {x : G} (hx : x ∈ K ⊔ P) :
    ∃ a ∈ K, ∃ b ∈ P, a * b = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ K, ∃ b ∈ P, a * b = x}
      one_mem' := ⟨1, K.one_mem, 1, P.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine ⟨a * c, K.mul_mem ha hc, b * d, P.mul_mem hb hd, ?_⟩
        have hbc : b * c = c * b := (h c hc b hb).symm
        calc a * c * (b * d) = a * (c * b) * d := by simp only [mul_assoc]
          _ = a * (b * c) * d := by rw [hbc]
          _ = a * b * (c * d) := by simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, K.inv_mem ha, b⁻¹, P.inv_mem hb, by
          rw [mul_inv_rev]; exact h a⁻¹ (K.inv_mem ha) b⁻¹ (P.inv_mem hb)⟩ }
  have hle : K ⊔ P ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, P.one_mem, mul_one a⟩)
      (fun b hb => ⟨1, K.one_mem, b, hb, one_mul b⟩)
  exact hle hx

private theorem e9_exists_K (hV : ∀ v : W, v ^ 2 = 1) (hrk : rk W = 4) {F : Subgroup (MulAut W)}
    (hF9 : Nat.card F = 9) :
    ∃ K : Subgroup (MulAut W), K ≤ F ∧ Nat.card K = 3 ∧ commV K ⊔ fixV K = ⊤ ∧
      commV K ⊓ fixV K = ⊥ ∧ rk (commV K) = 2 ∧ rk (fixV K) = 2 := by
  obtain ⟨q, hqF, hq3, v, hv1, hqv⟩ := exists_order_three_fixed hV hrk hF9
  have hq1 : q ≠ 1 := fun h => by rw [h, orderOf_one] at hq3; omega
  have hK3 : Nat.card (Subgroup.zpowers q) = 3 := by rw [Nat.card_zpowers, hq3]
  obtain ⟨h1, h2, h3, h4⟩ := commV_card_three hV hK3
  have hfix : rk (fixV (Subgroup.zpowers q)) ≠ 0 := by
    intro h0
    have hbot := (rk_eq_zero_iff hV).mp h0
    have hv : v ∈ fixV (Subgroup.zpowers q) := mem_fixV_zpowers_iff.mpr hqv
    rw [hbot, Subgroup.mem_bot] at hv
    exact hv1 hv
  have hcomm := e9_one_le_rk_commV hV hq1
  obtain ⟨m, hm⟩ := h4
  exact ⟨Subgroup.zpowers q, Subgroup.zpowers_le.mpr hqF, hK3, h1, h2, by omega, by omega⟩

private theorem e9_kernel (hV : ∀ v : W, v ^ 2 = 1) {F K : Subgroup (MulAut W)} {U : Subgroup W}
    (hF9 : Nat.card F = 9) (hK3 : Nat.card K = 3) (hKF : K ≤ F) (hFU : F ≤ stabSub U)
    (hU : rk U = 2) (hnt : ¬ U ≤ fixV K) :
    ∃ P : Subgroup (MulAut W), P ≤ F ∧ Nat.card P = 3 ∧ P ≤ centSub U ∧ P ⊓ K = ⊥ := by
  have hVU : ∀ v : U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV v)
  have h6 : Nat.card (MulAut U) = 6 := card_mulAut_of_rk_two hVU hU
  have hprod := card_autSub_mul hFU
  rw [hF9] at hprod
  have hd6 : Nat.card (autSub F U) ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card (autSub F U)
    rwa [h6] at this
  have hd9 : Nat.card (autSub F U) ∣ 9 := Dvd.intro _ hprod
  have hd3 : Nat.card (autSub F U) ∣ 3 := by
    have := Nat.dvd_gcd hd9 hd6
    simpa using this
  have hne1 : Nat.card (autSub F U) ≠ 1 := by
    intro h1
    apply hnt
    intro u hu x hx
    have hxs : x ∈ stabSub U := hFU (hKF hx)
    have hmem : resHom U ⟨x, hxs⟩ ∈ autSub F U := mem_autSub.mpr ⟨⟨x, hxs⟩, hKF hx, rfl⟩
    rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at hmem
    have := congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : W)) hmem
    simpa [resHom_apply] using this
  have h3 : Nat.card (autSub F U) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hd3).resolve_left hne1
  rw [h3] at hprod
  refine ⟨F ⊓ centSub U, inf_le_left, by omega, inf_le_right, ?_⟩
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  by_contra hx1
  obtain ⟨⟨hxF, hxc⟩, hxK⟩ := hx
  have hz := zpowers_eq_of_prime_card hK3 hxK hx1
  apply hnt
  intro u hu y hy
  rw [← hz] at hy
  exact (Subgroup.zpowers_le.mpr hxc : Subgroup.zpowers x ≤ centSub U) hy u hu

private theorem e9_sup_eq {G : Type*} [Group G] [Finite G] {F K P : Subgroup G}
    (hF9 : Nat.card F = 9) (hK3 : Nat.card K = 3) (hP3 : Nat.card P = 3) (hKF : K ≤ F)
    (hPF : P ≤ F) (hPK : P ⊓ K = ⊥) : K ⊔ P = F := by
  have hle : K ⊔ P ≤ F := sup_le hKF hPF
  have hd1 : 3 ∣ Nat.card ↥(K ⊔ P) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : K ≤ K ⊔ P)
    rwa [hK3] at this
  have hd2 : Nat.card ↥(K ⊔ P) ∣ 9 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hF9] at this
  have hn9 : Nat.card ↥(K ⊔ P) ≤ 9 := Nat.le_of_dvd (by norm_num) hd2
  have hcases : Nat.card ↥(K ⊔ P) = 3 ∨ Nat.card ↥(K ⊔ P) = 9 := by
    generalize Nat.card ↥(K ⊔ P) = n at hd1 hd2 hn9
    interval_cases n <;> omega
  rcases hcases with h3 | h9
  · exfalso
    have hKeq : K = K ⊔ P :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left : K ≤ K ⊔ P) (by rw [h3, hK3])
    have hPK' : P ≤ K := by rw [hKeq]; exact le_sup_right
    have : P ⊓ K = P := inf_eq_left.mpr hPK'
    rw [hPK] at this
    have h1 : Nat.card P = 1 := by rw [← this]; simp
    omega
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hF9])

private theorem e9_commV_eq (hV : ∀ v : W, v ^ 2 = 1) {F K P : Subgroup (MulAut W)}
    (hsup : commV K ⊔ fixV K = ⊤) (hPF : P ≤ F) (hP3 : Nat.card P = 3)
    (hFU₂ : F ≤ stabSub (fixV K)) (hPU₁ : commV K ≤ fixV P) (hU₂ : rk (fixV K) = 2) :
    commV P = fixV K := by
  have hle : commV P ≤ fixV K := by
    rw [commV_eq_commSub, ← hsup, commSub_sup_left, commSub_eq_bot_iff.mpr hPU₁, bot_sup_eq]
    exact commSub_le_of_invariant fun x hx w hw => ((hFU₂ (hPF hx)) w).mpr hw
  obtain ⟨-, -, -, hev⟩ := commV_card_three hV hP3
  have hpos : 1 ≤ rk (commV P) := by
    obtain ⟨y, -, hy1, hyz, -⟩ := exists_generator_of_prime_card (p := 3) hP3
    have := e9_one_le_rk_commV hV hy1
    rwa [hyz] at this
  have hrle : rk (commV P) ≤ 2 := hU₂ ▸ rk_mono hle
  obtain ⟨m, hm⟩ := hev
  exact eq_of_le_of_rk_le hV hle (by omega)

private theorem e9_fixed_free (hV : ∀ v : W, v ^ 2 = 1) {F K Q : Subgroup (MulAut W)}
    (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hK3 : Nat.card K = 3) (hQ3 : Nat.card Q = 3)
    (hKF : K ≤ F) (hQF : Q ≤ F) (hF : K ⊔ Q = F) (hsup : commV K ⊔ fixV K = ⊤)
    (hinf : commV K ⊓ fixV K = ⊥) (hFU₁ : F ≤ stabSub (commV K))
    (hFU₂ : F ≤ stabSub (fixV K)) (hQU₁ : commV K ≤ fixV Q) (hcQ : commV Q = fixV K)
    {P : Subgroup (MulAut W)} (hPF : P ≤ F) (hP3 : Nat.card P = 3) (hPK : P ≠ K) (hPQ : P ≠ Q) :
    fixV P = ⊥ := by
  obtain ⟨x, hxP, -, hxz, -⟩ := exists_generator_of_prime_card (p := 3) hP3
  have hxF : x ∈ F := hPF hxP
  obtain ⟨a, haK, b, hbQ, hab⟩ := e9_mem_sup_of_comm
    (fun a ha b hb => hFab a (hKF ha) b (hQF hb)) (by rw [hF]; exact hxF)
  have hPle : ∀ {R : Subgroup (MulAut W)}, x ∈ R → Nat.card R = 3 → P = R :=
    fun {R} hxR hR3 => Subgroup.eq_of_le_of_card_ge
      (by rw [← hxz]; exact Subgroup.zpowers_le.mpr hxR) (by rw [hP3, hR3])
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at hab
    exact hPQ (hPle (hab ▸ hbQ) hQ3)
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [mul_one] at hab
    exact hPK (hPle (hab ▸ haK) hK3)
  refine (Subgroup.eq_bot_iff_forall _).mpr fun u hu => ?_
  have hxu : x u = u := hu x hxP
  have hu' : u ∈ commV K ⊔ fixV K := by rw [hsup]; exact Subgroup.mem_top u
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu'
  have hbu₁ : b u₁ = u₁ := hQU₁ hu₁ b hbQ
  have hbu₂ : b u₂ ∈ fixV K := ((hFU₂ (hQF hbQ)) u₂).mpr hu₂
  have hau₂ : a (b u₂) = b u₂ := hbu₂ a haK
  have hau₁ : a u₁ ∈ commV K := ((hFU₁ (hKF haK)) u₁).mpr hu₁
  have hxeq : x (u₁ * u₂) = a u₁ * b u₂ := by
    rw [← hab]
    show a (b (u₁ * u₂)) = a u₁ * b u₂
    rw [map_mul b, hbu₁, map_mul a, hau₂]
  have hcancel : a u₁ * b u₂ = u₁ * u₂ := hxeq ▸ hxu
  have hdisj : Disjoint (commV K) (fixV K) := disjoint_iff.mpr hinf
  have hone : (a u₁ * u₁⁻¹) * (b u₂ * u₂⁻¹) = 1 := by
    rw [mul_mul_mul_comm, hcancel, ← mul_inv, mul_inv_cancel]
  have hone' := (Subgroup.disjoint_iff_mul_eq_one.mp hdisj
    (Subgroup.mul_mem _ hau₁ (Subgroup.inv_mem _ hu₁))
    (Subgroup.mul_mem _ hbu₂ (Subgroup.inv_mem _ hu₂)) hone)
  have h1' : a u₁ = u₁ := mul_inv_eq_one.mp hone'.1
  have h2' : b u₂ = u₂ := mul_inv_eq_one.mp hone'.2
  have hz₁ : u₁ = 1 := by
    have hKz : Subgroup.zpowers a = K := zpowers_eq_of_prime_card hK3 haK ha1
    have hf : u₁ ∈ fixV K := by rw [← hKz]; exact mem_fixV_zpowers_iff.mpr h1'
    have hm : u₁ ∈ commV K ⊓ fixV K := ⟨hu₁, hf⟩
    rwa [hinf, Subgroup.mem_bot] at hm
  have hz₂ : u₂ = 1 := by
    have hQz : Subgroup.zpowers b = Q := zpowers_eq_of_prime_card hQ3 hbQ hb1
    have hf : u₂ ∈ fixV Q := by rw [← hQz]; exact mem_fixV_zpowers_iff.mpr h2'
    have hc : u₂ ∈ commV Q := by rw [hcQ]; exact hu₂
    have hQinf := (commV_card_three hV hQ3).2.1
    have hm : u₂ ∈ commV Q ⊓ fixV Q := ⟨hc, hf⟩
    rwa [hQinf, Subgroup.mem_bot] at hm
  rw [hz₁, hz₂, mul_one]

private theorem e9_aux (hV : ∀ v : W, v ^ 2 = 1) {F : Subgroup (MulAut W)}
    (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hF9 : Nat.card F = 9) (hrk : rk W = 4) :
    ∃ P₁ P₂ : Subgroup (MulAut W), P₁ ≤ F ∧ P₂ ≤ F ∧ Nat.card P₁ = 3 ∧ Nat.card P₂ = 3 ∧
      rk (commV P₁) = 2 ∧ rk (commV P₂) = 2 ∧ Disjoint (commV P₁) (commV P₂) ∧
      commV P₁ ⊔ commV P₂ = ⊤ ∧ commV P₁ ≤ fixV P₂ ∧ commV P₂ ≤ fixV P₁ ∧ P₁ ⊔ P₂ = F ∧
      ∀ P : Subgroup (MulAut W), P ≤ F → Nat.card P = 3 → fixV P ≠ ⊥ → P = P₁ ∨ P = P₂ := by
  obtain ⟨K, hKF, hK3, hsup, hinf, hr1, hr2⟩ := e9_exists_K hV hrk hF9
  have hcomm : ∀ y ∈ K, ∀ z ∈ F, y * z = z * y := fun y hy z hz => hFab y (hKF hy) z hz
  obtain ⟨hFU₁, hFU₂⟩ := commute_stab hcomm
  have hnt : ¬ commV K ≤ fixV K := by
    intro h
    have hbot : commV K = ⊥ := by rw [← hinf]; exact (inf_eq_left.mpr h).symm
    rw [hbot, rk_bot] at hr1
    omega
  obtain ⟨Q, hQF, hQ3, hQc, hQK⟩ := e9_kernel hV hF9 hK3 hKF hFU₁ hr1 hnt
  have hQU₁ : commV K ≤ fixV Q := fun u hu x hx => hQc hx u hu
  have hFeq : K ⊔ Q = F := e9_sup_eq hF9 hK3 hQ3 hKF hQF hQK
  have hcQ : commV Q = fixV K := e9_commV_eq hV hsup hQF hQ3 hFU₂ hQU₁ hr2
  refine ⟨K, Q, hKF, hQF, hK3, hQ3, hr1, by rw [hcQ]; exact hr2, ?_, ?_, hQU₁, ?_, hFeq, ?_⟩
  · rw [hcQ]; exact disjoint_iff.mpr hinf
  · rw [hcQ]; exact hsup
  · rw [hcQ]
  · intro P hPF hP3 hfix
    by_contra hcon
    push Not at hcon
    exact hfix (e9_fixed_free hV hFab hK3 hQ3 hKF hQF hFeq hsup hinf hFU₁ hFU₂ hQU₁ hcQ hPF hP3
      hcon.1 hcon.2)

theorem exists_planes_E9 (hV : ∀ v : W, v ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hF : IsElemAbelian 3 (fittingOf Y)) (hF9 : Nat.card (fittingOf Y) = 9)
    (hcomm : commV (fittingOf Y) = ⊤) (hrk : rk W = 4) :
    ∃ P₁ P₂ : Subgroup (MulAut W), P₁ ∈ Xk Y 1 ∧ P₂ ∈ Xk Y 1 ∧
      Disjoint (commV P₁) (commV P₂) ∧ commV P₁ ⊔ commV P₂ = ⊤ ∧
      commV P₁ ≤ fixV P₂ ∧ commV P₂ ≤ fixV P₁ ∧ P₁ ⊔ P₂ = fittingOf Y ∧
      ∀ P : Subgroup (MulAut W), P ≤ fittingOf Y → Nat.card P = 3 → fixV P ≠ ⊥ →
        P = P₁ ∨ P = P₂ := by
  have _ := hcomm
  have hFab : ∀ a ∈ fittingOf Y, ∀ b ∈ fittingOf Y, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨P₁, P₂, h1F, h2F, h13, h23, hr1, hr2, hdisj, hsup, hle₁, hle₂, hFeq, hall⟩ :=
    e9_aux hV hFab hF9 hrk
  refine ⟨P₁, P₂, ⟨h1F, by omega, by omega⟩, ⟨h2F, by omega, by omega⟩, hdisj, hsup, hle₁, hle₂,
    hFeq, hall⟩

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.S1549DBr
public import CFSG.Quasithin.Background.S1549CC
public import CFSG.Quasithin.Background.S1549DGen

public section

namespace CFSG.Quasithin

namespace S153L

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.S1549C
  CFSG.Quasithin.S1549D

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem pCoreOf_Y0_ne_bot (h113 : StageLemma14113) (h : Hyp153 G T Mc M) (hc2 : Case157Two T Mc M) :
    pCoreOf 2 (Y0 T Mc M) ≠ ⊥ := by
  intro hbot
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ h.T_le
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S, hSM⟩
  have hYM : Y0 T Mc M ≤ M := (Y0_le T Mc M).trans (inf_le_left.trans (Y153_le Mc M))
  have hYn := le_normalizer_Y0 h
  have h1 : Y0 T Mc M ⊓ pCoreOf 2 M ≤ pCoreOf 2 (Y0 T Mc M) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 M (hYM hg)⟩)
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
  rw [hbot] at h1
  have hne : Y0 T Mc M ≠ ⊥ := fun hb => not_Y0_le_pCoreOf h113 h hc2 (hb ▸ bot_le)
  apply hne
  rw [eq_bot_iff]
  intro y hy
  have hyM : y ∈ M := hYM hy
  have hcomm : ∀ o ∈ pCoreOf 2 M, y * o * y⁻¹ * o⁻¹ = 1 := by
    intro o ho
    have hoM : o ∈ M := pCoreOf_le 2 M ho
    have hA : y * o * y⁻¹ * o⁻¹ ∈ Y0 T Mc M := by
      have e : y * o * y⁻¹ * o⁻¹ = y * (o * y⁻¹ * o⁻¹) := by group
      rw [e]
      refine Subgroup.mul_mem _ hy ?_
      exact (Subgroup.mem_normalizer_iff.mp (hYn hoM) y⁻¹).mp (Subgroup.inv_mem _ hy)
    have hB : y * o * y⁻¹ * o⁻¹ ∈ pCoreOf 2 M := by
      refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ ho)
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hyM) o).mp ho
    have := h1 ⟨hA, hB⟩
    simpa using this
  have hyF : y ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    refine ⟨hyM, Subgroup.mem_centralizer_iff.2 fun o ho => ?_⟩
    have := hcomm o ho
    calc o * y = (y * o * y⁻¹ * o⁻¹) * (o * y) := by rw [this, one_mul]
      _ = y * o := by group
  have hyO : y ∈ pCoreOf 2 M := hF hyF
  have := h1 ⟨hy, hyO⟩
  simpa using this

theorem normalizer_Y0_le_M (h113 : StageLemma14113) (h : Hyp153 G T Mc M) (hc2 : Case157Two T Mc M) :
    Subgroup.normalizer (Y0 T Mc M : Set G) ≤ M := by
  intro g hg
  have hgO : g ∈ Subgroup.normalizer (pCoreOf 2 (Y0 T Mc M) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _ hg
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (Y0 T Mc M) : Set G)) :=
    ⟨pCoreOf 2 (Y0 T Mc M), pCoreOf_Y0_ne_bot h113 h hc2, pCoreOf_isPGroup 2 _, rfl⟩
  have hle : M ≤ Subgroup.normalizer (pCoreOf 2 (Y0 T Mc M) : Set G) :=
    (le_normalizer_Y0 h).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have heq := h.inM.1.2 _ hloc hle
  rw [← heq]
  exact hgO

theorem exists_orderThree_lift {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    (hker : ∀ x : A, f x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) {y : B} (hy : orderOf y = 3)
    (hyr : y ∈ f.range) : ∃ x : A, orderOf x = 3 ∧ f x = y := by
  obtain ⟨x₀, rfl⟩ := hyr
  have hn : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  obtain ⟨e, n', hn', hdecomp⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  have hy3 : f x₀ ^ 3 = 1 := hy ▸ pow_orderOf_eq_one _
  have hy1 : f x₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    omega
  have hsq : n' ^ 2 % 3 = 1 := by
    have : n' % 3 = 1 ∨ n' % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  set x₁ : A := x₀ ^ (n' ^ 2) with hx₁
  have hfx₁ : f x₁ = f x₀ := by
    rw [hx₁, map_pow]
    have : n' ^ 2 = 3 * (n' ^ 2 / 3) + 1 := by omega
    rw [this, pow_add, pow_mul, hy3, one_pow, one_mul, pow_one]
  have hx₁ord : x₁ ^ 3 ^ e = 1 := by
    rw [hx₁, ← pow_mul]
    have : n' ^ 2 * 3 ^ e = orderOf x₀ * n' := by rw [hdecomp]; ring
    rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
  have hker3 : f (x₁ ^ 3) = 1 := by rw [map_pow, hfx₁, hy3]
  obtain ⟨k, hk⟩ := hker _ hker3
  have hd1 : orderOf (x₁ ^ 3) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hd2 : orderOf (x₁ ^ 3) ∣ 3 ^ e :=
    (orderOf_pow_dvd 3).trans (orderOf_dvd_of_pow_eq_one hx₁ord)
  have hcop : Nat.Coprime (2 ^ k) (3 ^ e) :=
    Nat.Coprime.pow k e (by norm_num)
  have h1 : orderOf (x₁ ^ 3) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have hx₁3 : x₁ ^ 3 = 1 := orderOf_eq_one_iff.mp h1
  have hd3 : orderOf x₁ ∣ 3 := orderOf_dvd_of_pow_eq_one hx₁3
  have hx₁1 : orderOf x₁ ≠ 1 := by
    intro h1
    have := orderOf_eq_one_iff.mp h1
    apply hy1
    rw [← hfx₁, this, map_one]
  refine ⟨x₁, ?_, hfx₁⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
  · exact absurd h hx₁1
  · exact h

section Lift

variable {T V L V₁ Vp H : Subgroup G}

theorem starHom_ker_pow (h : HypF91 T V L V₁ Vp H) (x : ↥H) (hx : starHom h x = 1) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have hq : (x : G) ∈ pCoreOf 2 H := (starHom_eq_one_iff h x).mp hx
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x, hq⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem exists_lift_orderThree (h : HypF91 T V L V₁ Vp H) {K : Subgroup G} (hKH : K ≤ H)
    {y : MulAut ↥(tildeOf V₁ (conjClosure Vp H))} (hy : orderOf y = 3)
    (hyK : y ∈ starOfSub h K) :
    ∃ x : G, x ∈ K ∧ orderOf x = 3 ∧ ∃ hx : x ∈ H, starHom h ⟨x, hx⟩ = y := by
  let f : ↥K →* MulAut ↥(tildeOf V₁ (conjClosure Vp H)) :=
    (starHom h).comp (Subgroup.inclusion hKH)
  have hker : ∀ x : ↥K, f x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := starHom_ker_pow h (Subgroup.inclusion hKH x) hx
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hyr : y ∈ f.range := by
    obtain ⟨x, hxK, rfl⟩ := (mem_starOfSub h).mp hyK
    exact ⟨⟨x, hxK⟩, rfl⟩
  obtain ⟨x, hx3, hxy⟩ := exists_orderThree_lift f hker hy hyr
  refine ⟨(x : G), x.2, ?_, hKH x.2, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hx3
  · rw [← hxy]
    rfl

end Lift

section Ctx

variable {T Mc M V₁ V₂ : Subgroup G} {t : G} {cx : Ctx49 G T Mc M V₁ V₂ t} {H : Subgroup G}

theorem Y0_le_H (hb : InspBase cx H) : Y0 T Mc M ≤ H := le_sup_left.trans hb.adm.hY0

theorem Y0_le_inf (hb : InspBase cx H) : Y0 T Mc M ≤ M ⊓ H :=
  le_inf ((Y0_le T Mc M).trans (inf_le_left.trans (Y153_le Mc M))) (Y0_le_H hb)

theorem pCoreOf_le_inf (hb : InspBase cx H) : pCoreOf 2 H ≤ M ⊓ H :=
  le_inf ((IsSylowTwoOf.pCoreOf_le hb.hF98.toHypF91.sylow_H).trans cx.c.hyp.T_le) (pCoreOf_le 2 H)

theorem theta_star (hb : InspBase cx H) {y : MulAut ↥(tildeOf (quasithinOmegaOneCenter T)
      (conjClosure (ZS153 T M V₁) H))}
    (hy : orderOf y = 3) (hyM : y ∈ starOfSub hb.hF98.toHypF91 (M ⊓ H)) :
    y ∈ starOfSub hb.hF98.toHypF91 (Y0 T Mc M) := by
  obtain ⟨x, hxK, hx3, hxH, hxy⟩ := exists_lift_orderThree hb.hF98.toHypF91 inf_le_right hy hyM
  have hxY : x ∈ Y0 T Mc M := by
    rw [hb.claimB]
    exact Subgroup.subset_closure ⟨hxK, hx3⟩
  exact (mem_starOfSub _).mpr ⟨⟨x, hxH⟩, hxY, hxy⟩

theorem Ystar_gen (hb : InspBase cx H) :
    starOfSub hb.hF98.toHypF91 (Y0 T Mc M) =
      Subgroup.closure {y | y ∈ starOfSub hb.hF98.toHypF91 (Y0 T Mc M) ∧ orderOf y = 3} := by
  have h := hb.hF98.toHypF91
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hxY, rfl⟩ := (mem_starOfSub h).mp hy
    have hxc : (x : G) ∈ Subgroup.closure {z : G | z ∈ M ⊓ H ∧ orderOf z = 3} := by
      have := hxY
      rw [hb.claimB] at this
      exact this
    have key : ∀ z : G, z ∈ Subgroup.closure {z : G | z ∈ M ⊓ H ∧ orderOf z = 3} →
        ∃ hzH : z ∈ H, starHom h ⟨z, hzH⟩ ∈
          Subgroup.closure {y | y ∈ starOfSub h (Y0 T Mc M) ∧ orderOf y = 3} := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨hzM, hz3⟩ := hz
        have hzH : z ∈ H := hzM.2
        refine ⟨hzH, Subgroup.subset_closure ⟨?_, ?_⟩⟩
        · have hzY : z ∈ Y0 T Mc M := by
            rw [hb.claimB]
            exact Subgroup.subset_closure ⟨hzM, hz3⟩
          exact (mem_starOfSub h).mpr ⟨⟨z, hzH⟩, hzY, rfl⟩
        · have h3 : starHom h ⟨z, hzH⟩ ^ 3 = 1 := by
            rw [← map_pow]
            have : (⟨z, hzH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa [hz3] using pow_orderOf_eq_one z)
            rw [this, map_one]
          have h1 : starHom h ⟨z, hzH⟩ ≠ 1 := by
            intro h1
            obtain ⟨k, hk⟩ := starHom_ker_pow h _ h1
            have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
            have hd : 3 ∣ 2 ^ k := hz3 ▸ orderOf_dvd_of_pow_eq_one hk'
            exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
              (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
          have hd : orderOf (starHom h ⟨z, hzH⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
          rcases (Nat.dvd_prime Nat.prime_three).mp hd with h' | h'
          · exact absurd (orderOf_eq_one_iff.mp h') h1
          · exact h'
      | one =>
        refine ⟨H.one_mem, ?_⟩
        have : (⟨1, H.one_mem⟩ : ↥H) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _
      | mul a b _ _ iha ihb =>
        obtain ⟨haH, ha⟩ := iha
        obtain ⟨hbH, hb'⟩ := ihb
        refine ⟨H.mul_mem haH hbH, ?_⟩
        have : (⟨a * b, H.mul_mem haH hbH⟩ : ↥H) = ⟨a, haH⟩ * ⟨b, hbH⟩ := rfl
        rw [this, map_mul]
        exact Subgroup.mul_mem _ ha hb'
      | inv a _ iha =>
        obtain ⟨haH, ha⟩ := iha
        refine ⟨H.inv_mem haH, ?_⟩
        have : (⟨a⁻¹, H.inv_mem haH⟩ : ↥H) = (⟨a, haH⟩ : ↥H)⁻¹ := rfl
        rw [this, map_inv]
        exact Subgroup.inv_mem _ ha
    obtain ⟨hzH, hz⟩ := key (x : G) hxc
    exact hz
  · exact (Subgroup.closure_le _).mpr fun y hy => hy.1

omit [Finite G] in
theorem exists_mul_of_mem_sup_norm {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G))
    {g : G} (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a * (b * a' * b⁻¹), A.mul_mem ha
          ((Subgroup.mem_normalizer_iff.mp (hB hb) a').mp ha'), b * b', B.mul_mem hb hb',
          by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hB (B.inv_mem hb)) a⁻¹).mp (A.inv_mem ha)
        simpa using this }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hg

omit [Finite G] in
theorem pow_mul_mem_mul_pow {Y : Subgroup G} {y q : G} (hy : y ∈ Y)
    (hq : q ∈ Subgroup.normalizer (Y : Set G)) (n : ℕ) : ∃ y' ∈ Y, (y * q) ^ n = y' * q ^ n := by
  induction n with
  | zero => exact ⟨1, Y.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨y', hy', e⟩ := ih
    have hqn : q ^ n ∈ Subgroup.normalizer (Y : Set G) := Subgroup.pow_mem _ hq n
    have h1 : q ^ n * y * (q ^ n)⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hqn y).mp hy
    refine ⟨y' * (q ^ n * y * (q ^ n)⁻¹), Y.mul_mem hy' h1, ?_⟩
    rw [pow_succ, e]
    group

omit [Finite G] in
theorem oTwoUpper_sup_of_two_group {Y Q : Subgroup G} (hQY : Q ≤ Subgroup.normalizer (Y : Set G))
    (hQ : IsPGroup 2 Q) (hY : oTwoUpper Y = Y) : oTwoUpper (Y ⊔ Q) = Y := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, hodd⟩
    obtain ⟨y, hy, q, hq, rfl⟩ := exists_mul_of_mem_sup_norm hQY hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨q, hq⟩
    have hqk : q ^ 2 ^ k = 1 := by
      have : orderOf q = 2 ^ k := by rw [← Subgroup.orderOf_coe] at hk; simpa using hk
      rw [← this]; exact pow_orderOf_eq_one q
    obtain ⟨y', hy', e⟩ := pow_mul_mem_mul_pow hy (hQY hq) (2 ^ k)
    rw [hqk, mul_one] at e
    have hcop : Nat.Coprime (2 ^ k) (orderOf (y * q)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    have hmem := A4.mem_zpowers_pow_of_coprime hcop
    rw [e] at hmem
    exact (Subgroup.zpowers_le.mpr hy') hmem
  · calc Y = oTwoUpper Y := hY.symm
      _ ≤ oTwoUpper (Y ⊔ Q) := oTwoUpper_mono le_sup_left

theorem card_le_three_of_pGroup_le_Y0 (hc2 : Case157Two T Mc M)
    {P : Subgroup G} (hP : P ≤ Y0 T Mc M) (hP3 : IsPGroup 3 P) : Nat.card P ≤ 3 := by
  have hY0C : Y0 T Mc M ≤ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := Y0_le T Mc M
  have hPY : P ≤ Y153 Mc M := (hP.trans hY0C).trans inf_le_left
  let f₀ : ↥P →* OTwoQuot (Y153 Mc M) :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(Y153 Mc M))).comp (Subgroup.inclusion hPY)
  have hcen : ∀ x : ↥P, f₀ x ∈ Subgroup.center (OTwoQuot (Y153 Mc M)) := by
    intro x
    have hxO : (x : G) ∈ O2Z (Y153 Mc M) := by
      rw [hc2.2]
      exact hY0C (hP x.2)
    obtain ⟨hy, hc⟩ := mem_O2Z_iff.mp hxO
    exact hc
  let f : ↥P →* ↥(Subgroup.center (OTwoQuot (Y153 Mc M))) := f₀.codRestrict _ hcen
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : f₀ x = 1 := by
      have := congrArg Subtype.val hx
      simpa [f] using this
    have h2 : ((x : G)) ∈ pCoreOf 2 (Y153 Mc M) :=
      (mk_eq_one_iff_mem_pCoreOf (⟨(x : G), hPY x.2⟩ : ↥(Y153 Mc M))).mp h1
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (Y153 Mc M) ⟨(x : G), h2⟩
    obtain ⟨m, hm⟩ := hP3 x
    have hk' : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : (x : G) ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hd1 : orderOf (x : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf (x : G) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
    have hcop : Nat.Coprime (2 ^ k) (3 ^ m) := Nat.Coprime.pow k m (by norm_num)
    have h3 : orderOf (x : G) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact Subtype.ext (orderOf_eq_one_iff.mp h3)
  have hc3 := hc2.1.1.center_order_p
  calc Nat.card P ≤ Nat.card ↥(Subgroup.center (OTwoQuot (Y153 Mc M))) :=
        Nat.card_le_card_of_injective f hinj
    _ = 3 := hc3

omit [Finite G] in
theorem oTwoUpper_idem (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2

theorem not_nine_dvd_card_Y0 (hc2 : Case157Two T Mc M) :
    ¬ 9 ∣ Nat.card ↥(Y0 T Mc M) := by
  intro hd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(Y0 T Mc M)) 3 (n := 2)
    (by simpa using hd)
  have hKp : IsPGroup 3 ↥K := by
    refine IsPGroup.of_card (n := 2) (by simpa using hK)
  have hmap : IsPGroup 3 ↥(K.map (Y0 T Mc M).subtype) :=
    hKp.of_equiv (Subgroup.equivMapOfInjective K _ (Y0 T Mc M).subtype_injective)
  have hle : K.map (Y0 T Mc M).subtype ≤ Y0 T Mc M := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  have h3 := card_le_three_of_pGroup_le_Y0 hc2 hle hmap
  rw [Subgroup.card_map_of_injective (Y0 T Mc M).subtype_injective, hK] at h3
  norm_num at h3

theorem hY3_star (hb : InspBase cx H)
    {E : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)))}
    (hE : E ≤ starOfSub hb.hF98.toHypF91 (Y0 T Mc M)) (hE3 : IsPGroup 3 E) : Nat.card E ≤ 3 := by
  have h := hb.hF98.toHypF91
  have hcard : Nat.card ↥(starOfSub h (Y0 T Mc M)) ∣ Nat.card ↥(Y0 T Mc M) := by
    let f : ↥(Y0 T Mc M) →* ↥(starOfSub h (Y0 T Mc M)) :=
      ((starHom h).comp (Subgroup.inclusion (Y0_le_H hb))).codRestrict _
        (fun x => (mem_starOfSub h).mpr ⟨Subgroup.inclusion (Y0_le_H hb) x, x.2, rfl⟩)
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hxK, rfl⟩ := (mem_starOfSub h).mp hy
      exact ⟨⟨x, hxK⟩, rfl⟩
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at this
    exact ⟨_, this⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hE3.exists_card_eq
  by_contra hlt
  push Not at hlt
  have ha2 : 2 ≤ a := by
    by_contra hnot
    push Not at hnot
    have : 3 ^ a ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h9 : 9 ∣ Nat.card E := by
    rw [ha]
    exact (pow_dvd_pow 3 ha2 : 3 ^ 2 ∣ 3 ^ a)
  exact not_nine_dvd_card_Y0 cx.case2
    (dvd_trans h9 (dvd_trans (Subgroup.card_dvd_of_le hE) hcard))

theorem hKL_star (h113 : StageLemma14113) (hb : InspBase cx H)
    (X : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H))))
    (hXH : X ≤ starOfSub hb.hF98.toHypF91 H)
    (hXY : ∀ x ∈ X, ∀ y ∈ starOfSub hb.hF98.toHypF91 (Y0 T Mc M), x * y = y * x) :
    X ≤ starOfSub hb.hF98.toHypF91 (M ⊓ H) := by
  have h := hb.hF98.toHypF91
  have hc2 := cx.case2
  have hQnorm : pCoreOf 2 H ≤ Subgroup.normalizer (Y0 T Mc M : Set G) :=
    (pCoreOf_le_inf hb).trans (inf_le_left.trans (le_normalizer_Y0 cx.c.hyp))
  have hstable : ∀ g : ↥H, starHom h g ∈ X → ∀ w ∈ Y0 T Mc M ⊔ pCoreOf 2 H,
      (g : G) * w * (g : G)⁻¹ ∈ Y0 T Mc M ⊔ pCoreOf 2 H := by
    intro g hgX w hw
    obtain ⟨y, hy, q, hq, rfl⟩ := exists_mul_of_mem_sup_norm hQnorm hw
    have hyH : y ∈ H := Y0_le_H hb hy
    have hc : (g : G) * y * (g : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 H := by
      have hrho : starHom h (g * ⟨y, hyH⟩ * g⁻¹ * ⟨y, hyH⟩⁻¹) = 1 := by
        have hy' : starHom h ⟨y, hyH⟩ ∈ starOfSub h (Y0 T Mc M) :=
          (mem_starOfSub h).mpr ⟨⟨y, hyH⟩, hy, rfl⟩
        have hcomm := hXY _ hgX _ hy'
        simp only [map_mul, map_inv]
        calc starHom h g * starHom h ⟨y, hyH⟩ * (starHom h g)⁻¹ * (starHom h ⟨y, hyH⟩)⁻¹
            = starHom h ⟨y, hyH⟩ * starHom h g * (starHom h g)⁻¹ * (starHom h ⟨y, hyH⟩)⁻¹ := by
              rw [hcomm]
          _ = 1 := by group
      exact (starHom_eq_one_iff h _).mp hrho
    have hqg : (g : G) * q * (g : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H g.2) q).mp hq
    have e : (g : G) * (y * q) * (g : G)⁻¹ =
        ((g : G) * y * (g : G)⁻¹ * y⁻¹) * y * ((g : G) * q * (g : G)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
      (Subgroup.mem_sup_left hy)) (Subgroup.mem_sup_right hqg)
  intro x' hx'
  obtain ⟨x, -, rfl⟩ := (mem_starOfSub h).mp (hXH hx')
  have hxinv : starHom h x⁻¹ ∈ X := by rw [map_inv]; exact X.inv_mem hx'
  have hnormW : (x : G) ∈ Subgroup.normalizer ((Y0 T Mc M ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hstable x hx' w, fun hw => ?_⟩
    have := hstable x⁻¹ hxinv _ hw
    simpa [mul_assoc] using this
  have hnormY : (x : G) ∈ Subgroup.normalizer (Y0 T Mc M : Set G) := by
    have h1 := normalizer_le_normalizer_oTwoUpper _ hnormW
    rwa [oTwoUpper_sup_of_two_group hQnorm (pCoreOf_isPGroup 2 H) (oTwoUpper_idem _)] at h1
  have hxM : (x : G) ∈ M := normalizer_Y0_le_M h113 cx.c.hyp hc2 hnormY
  exact (mem_starOfSub h).mpr ⟨x, ⟨hxM, x.2⟩, rfl⟩

end Ctx

end S153L

end CFSG.Quasithin

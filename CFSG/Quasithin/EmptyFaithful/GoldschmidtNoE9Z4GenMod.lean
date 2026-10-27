module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenDefs
public import CFSG.Quasithin.EmptyFaithful.S14612GA0

public section

namespace CFSG.Quasithin.NoE9Z4GenGrp

open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem exists_gens_of_card_four_aux {K : Type*} [CommGroup K] [Finite K]
    (hK : ∀ v : K, v ^ 2 = 1) {W : Subgroup K} (hW : Nat.card W = 4) :
    ∃ w₁ ∈ W, ∃ w₂ ∈ W, ∀ w ∈ W, w = 1 ∨ w = w₁ ∨ w = w₂ ∨ w = w₁ * w₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ {g y : K}, g ^ 2 = 1 → y ∈ Subgroup.zpowers g → y = 1 ∨ y = g := by
    intro g y hg hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [zpow_eq_zpow_emod' k hg]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      simp [h]
    · right
      simp [h]
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW
    omega
  obtain ⟨⟨w₁, hw₁⟩, hw₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
  have hw₁1' : w₁ ≠ 1 := fun e => hw₁1 (Subtype.ext e)
  have hS₁ : Nat.card (Subgroup.zpowers w₁) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hK w₁) hw₁1'
  have hS₁W : Subgroup.zpowers w₁ ≤ W := (Subgroup.zpowers_le).mpr hw₁
  obtain ⟨w₂, hw₂, hw₂S⟩ : ∃ w₂ ∈ W, w₂ ∉ Subgroup.zpowers w₁ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun w hw => hcon w hw)
    omega
  have hBW : Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ≤ W :=
    sup_le hS₁W ((Subgroup.zpowers_le).mpr hw₂)
  have hB1 : 2 ∣ Nat.card ↥(Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) := by
    rw [← hS₁]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hB2 : Nat.card ↥(Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) ≤ 4 :=
    hW ▸ Subgroup.card_le_of_le hBW
  have hB3 : 2 < Nat.card ↥(Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) := by
    by_contra hcon
    have hEq : Subgroup.zpowers w₁ = Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    exact hw₂S (hEq ▸ (le_sup_right : Subgroup.zpowers w₂ ≤ _) (Subgroup.mem_zpowers w₂))
  have hBeq : Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ = W :=
    Subgroup.eq_of_le_of_card_ge hBW (by omega)
  refine ⟨w₁, hw₁, w₂, hw₂, fun w hw => ?_⟩
  rw [← hBeq] at hw
  obtain ⟨y, hy, y', hy', rfl⟩ := Subgroup.mem_sup.mp hw
  rcases hpow (hK w₁) hy with rfl | rfl <;> rcases hpow (hK w₂) hy' with rfl | rfl <;> simp

section ClassMap

variable {Q U Z Cq Hs : Subgroup G} {z : G} {P : PairCtx Q U Z Cq Hs z} {U0 : Subgroup G}
  {K : Type*} [CommGroup K] {β : ↥Hs →* MulAut K} {cls : G → K}

private theorem cls_one_aux (D : ClsData P U0 β cls) : cls 1 = 1 :=
  (D.ker0 1 U0.one_mem).mpr Z.one_mem

private theorem cls_inv_aux (D : ClsData P U0 β cls) {u : G} (hu : u ∈ U) :
    cls u⁻¹ = (cls u)⁻¹ := by
  have h := D.mul u hu u⁻¹ (U.inv_mem hu)
  rw [mul_inv_cancel, cls_one_aux D] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private def clsPre (D : ClsData P U0 β cls) (W : Subgroup K) : Subgroup G where
  carrier := {u | u ∈ U0 ∧ cls u ∈ W}
  one_mem' := ⟨U0.one_mem, by rw [cls_one_aux D]; exact W.one_mem⟩
  mul_mem' := fun hu hu' => ⟨U0.mul_mem hu.1 hu'.1, by
    rw [D.mul _ (D.U0_le hu.1) _ (D.U0_le hu'.1)]; exact W.mul_mem hu.2 hu'.2⟩
  inv_mem' := fun hu => ⟨U0.inv_mem hu.1, by
    rw [cls_inv_aux D (D.U0_le hu.1)]; exact W.inv_mem hu.2⟩

private theorem mem_clsPre_aux (D : ClsData P U0 β cls) {W : Subgroup K} {u : G} :
    u ∈ clsPre D W ↔ u ∈ U0 ∧ cls u ∈ W := Iff.rfl

private theorem exists_eq_mul_aux (D : ClsData P U0 β cls) {u v : G} (hu : u ∈ U0) (hv : v ∈ U0)
    (h : cls u = cls v) : ∃ c ∈ Z, u = v * c := by
  have hvu : v⁻¹ * u ∈ U0 := U0.mul_mem (U0.inv_mem hv) hu
  refine ⟨v⁻¹ * u, (D.ker0 _ hvu).mp ?_, (mul_inv_cancel_left v u).symm⟩
  rw [D.mul _ (U.inv_mem (D.U0_le hv)) _ (D.U0_le hu), cls_inv_aux D (D.U0_le hv), h,
    inv_mul_cancel]

private theorem clsPre_decomp_aux (D : ClsData P U0 β cls) {W₁ W₂ : Subgroup K}
    (h : W₁ ⊔ W₂ = ⊤) :
    ∀ u ∈ U, ∃ u₁ ∈ clsPre D W₁, ∃ u₂ ∈ clsPre D W₂, ∃ c ∈ Cq, u = u₁ * u₂ * c := by
  intro u hu
  have hk : cls u ∈ W₁ ⊔ W₂ := by rw [h]; exact Subgroup.mem_top _
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := Subgroup.mem_sup.mp hk
  obtain ⟨u₁, hu₁, rfl⟩ := D.surj k₁
  obtain ⟨u₂, hu₂, rfl⟩ := D.surj k₂
  have hu₁U := D.U0_le hu₁
  have hu₂U := D.U0_le hu₂
  have hprod : u₁ * u₂ ∈ U := U.mul_mem hu₁U hu₂U
  have hcU : (u₁ * u₂)⁻¹ * u ∈ U := U.mul_mem (U.inv_mem hprod) hu
  refine ⟨u₁, ⟨hu₁, hk₁⟩, u₂, ⟨hu₂, hk₂⟩, (u₁ * u₂)⁻¹ * u, D.ker _ hcU ?_, by group⟩
  rw [D.mul _ (U.inv_mem hprod) _ hu, cls_inv_aux D hprod, D.mul _ hu₁U _ hu₂U, hk, inv_mul_cancel]

private theorem comm_mem_Z_aux (D : ClsData P U0 β cls) {W : Subgroup K} {y : ↥Hs}
    (hy : ∀ c ∈ W, β y c = c) {u : G} (hu : u ∈ clsPre D W) : ⁅(y : G), u⁆ ∈ Z := by
  obtain ⟨hu0, huW⟩ := (mem_clsPre_aux D).mp hu
  have huU := D.U0_le hu0
  have h1 : (y : G) * u * (y : G)⁻¹ ∈ U0 := D.normU0 _ y.2 u hu0
  have h1U := D.U0_le h1
  rw [commutatorElement_def]
  refine (D.ker0 _ (U0.mul_mem h1 (U0.inv_mem hu0))).mp ?_
  rw [D.mul _ h1U _ (U.inv_mem huU), D.conj y u huU, cls_inv_aux D huU, hy _ huW, mul_inv_cancel]

private theorem conj_mem_clsPre_aux (D : ClsData P U0 β cls) {W : Subgroup K} {y : ↥Hs}
    (hy : ∀ c ∈ W, β y c ∈ W) {u : G} (hu : u ∈ clsPre D W) :
    (y : G) * u * (y : G)⁻¹ ∈ clsPre D W := by
  obtain ⟨hu0, huW⟩ := (mem_clsPre_aux D).mp hu
  exact ⟨D.normU0 _ y.2 u hu0, by rw [D.conj y u (D.U0_le hu0)]; exact hy _ huW⟩

private theorem kill_mem_Z_aux (D : ClsData P U0 β cls) {W : Subgroup K} {x : ↥Hs}
    (hinv : ∀ c ∈ W, β x c ∈ W) (hord : ∀ c : K, β x (β x (β x c)) = c)
    (hfree : ∀ c ∈ W, β x c = c → c = 1) {u : G} (hu : u ∈ clsPre D W) :
    u * ((x : G) * u * (x : G)⁻¹) * ((x : G) * (x : G) * u * (x : G)⁻¹ * (x : G)⁻¹) ∈ Z := by
  obtain ⟨hu0, huW⟩ := (mem_clsPre_aux D).mp hu
  have huU := D.U0_le hu0
  have h10 : (x : G) * u * (x : G)⁻¹ ∈ U0 := D.normU0 _ x.2 u hu0
  have h1 : (x : G) * u * (x : G)⁻¹ ∈ U := D.U0_le h10
  have e2 : (x : G) * (x : G) * u * (x : G)⁻¹ * (x : G)⁻¹ =
      ((x * x : ↥Hs) : G) * u * ((x * x : ↥Hs) : G)⁻¹ := by
    rw [Subgroup.coe_mul]; group
  have h20 : (x : G) * (x : G) * u * (x : G)⁻¹ * (x : G)⁻¹ ∈ U0 := by
    rw [e2]; exact D.normU0 _ (x * x).2 u hu0
  have h2 : (x : G) * (x : G) * u * (x : G)⁻¹ * (x : G)⁻¹ ∈ U := D.U0_le h20
  have hc1 : cls ((x : G) * u * (x : G)⁻¹) = β x (cls u) := D.conj x u huU
  have hc2 : cls ((x : G) * (x : G) * u * (x : G)⁻¹ * (x : G)⁻¹) = β x (β x (cls u)) := by
    rw [e2, D.conj (x * x) u huU, map_mul]; rfl
  have hprod : cls (u * ((x : G) * u * (x : G)⁻¹) *
      ((x : G) * (x : G) * u * (x : G)⁻¹ * (x : G)⁻¹)) =
      cls u * β x (cls u) * β x (β x (cls u)) := by
    rw [D.mul _ (U.mul_mem huU h1) _ h2, D.mul _ huU _ h1, hc1, hc2]
  have hmW : cls u * β x (cls u) * β x (β x (cls u)) ∈ W :=
    W.mul_mem (W.mul_mem huW (hinv _ huW)) (hinv _ (hinv _ huW))
  have hfix : β x (cls u * β x (cls u) * β x (β x (cls u))) =
      cls u * β x (cls u) * β x (β x (cls u)) := by
    rw [map_mul, map_mul, hord (cls u)]
    ac_rfl
  refine (D.ker0 _ (U0.mul_mem (U0.mul_mem hu0 h10) h20)).mp ?_
  rw [hprod]
  exact hfree _ hmW hfix

private theorem Z_le_clsPre_aux (D : ClsData P U0 β cls) (W : Subgroup K) : Z ≤ clsPre D W :=
  fun c hc => ⟨D.Z_le_U0 hc, by rw [(D.ker0 c (D.Z_le_U0 hc)).mpr hc]; exact W.one_mem⟩

private theorem clsPre_le_aux (D : ClsData P U0 β cls) (W : Subgroup K) : clsPre D W ≤ U :=
  fun _ hu => D.U0_le ((mem_clsPre_aux D).mp hu).1

private theorem gen_clsPre_aux [Finite K] (D : ClsData P U0 β cls) (hK : ∀ v : K, v ^ 2 = 1)
    {W : Subgroup K} (hW : Nat.card W = 4) :
    ∃ w₁ ∈ clsPre D W, ∃ w₂ ∈ clsPre D W, ∀ u ∈ clsPre D W,
      ∃ c ∈ Z, u = c ∨ u = w₁ * c ∨ u = w₂ * c ∨ u = w₁ * w₂ * c := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := exists_gens_of_card_four_aux hK hW
  obtain ⟨w₁, hw₁, rfl⟩ := D.surj k₁
  obtain ⟨w₂, hw₂, rfl⟩ := D.surj k₂
  refine ⟨w₁, ⟨hw₁, hk₁⟩, w₂, ⟨hw₂, hk₂⟩, fun u hu => ?_⟩
  obtain ⟨hu0, huW⟩ := (mem_clsPre_aux D).mp hu
  have hw₁0 : w₁ ∈ U0 := hw₁
  have hw₂0 : w₂ ∈ U0 := hw₂
  rcases hk _ huW with h | h | h | h
  · exact ⟨u, (D.ker0 u hu0).mp h, Or.inl rfl⟩
  · obtain ⟨c, hc, e⟩ := exists_eq_mul_aux D hu0 hw₁0 h
    exact ⟨c, hc, Or.inr (Or.inl e)⟩
  · obtain ⟨c, hc, e⟩ := exists_eq_mul_aux D hu0 hw₂0 h
    exact ⟨c, hc, Or.inr (Or.inr (Or.inl e))⟩
  · obtain ⟨c, hc, e⟩ := exists_eq_mul_aux D hu0 (U0.mul_mem hw₁0 hw₂0)
      (by rw [h, D.mul _ (D.U0_le hw₁0) _ (D.U0_le hw₂0)])
    exact ⟨c, hc, Or.inr (Or.inr (Or.inr e))⟩

end ClassMap

private theorem plane_aux {K : Type*} [CommGroup K] [Finite K] (hK : ∀ v : K, v ^ 2 = 1)
    {P₁ : Subgroup (MulAut K)} {α : MulAut K} (hz : Subgroup.zpowers α = P₁)
    (ho : orderOf α = 3) (hcard : Nat.card P₁ = 3) :
    (∀ c : K, α (α (α c)) = c) ∧ (∀ c ∈ commV P₁, α c = c → c = 1) ∧
      ∀ g ∈ P₁, ∀ c ∈ commV P₁, g c ∈ commV P₁ := by
  refine ⟨fun c => ?_, fun c hc hαc => ?_, fun g hg c hc => ?_⟩
  · have h3 : α ^ 3 = 1 := by rw [← ho]; exact pow_orderOf_eq_one α
    calc α (α (α c)) = (α ^ 3) c := by rw [pow_three]; rfl
      _ = c := by rw [h3]; rfl
  · have hfix : c ∈ fixV P₁ := by rw [← hz]; exact mem_fixV_zpowers_iff.mpr hαc
    have h : c ∈ commV P₁ ⊓ fixV P₁ := ⟨hc, hfix⟩
    rw [(commV_card_three hK hcard).2.1, Subgroup.mem_bot] at h
    exact h
  · exact commV_smul_mem (fun p hp => P₁.mul_mem (P₁.mul_mem hg hp) (P₁.inv_mem hg)) hc

theorem exists_wtCtx_t {Q U Z Cq Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Cq Hs z)
    {U0 : Subgroup G} {K : Type} [CommGroup K] [Finite K] {β : ↥Hs →* MulAut K} {cls : G → K}
    (D : ClsData P U0 β cls) {Tb Pb : Subgroup (MulAut K)}
    (hES : CFSG.Quasithin.E9Z4Str β.range Tb Pb) :
    ∃ (a b : G) (Ua Ub : Subgroup G) (W : WtCtx P a b Ua Ub), Ua ≤ U0 ∧ Ub ≤ U0 ∧
      ∃ t : ↥Hs, β (t * t) = 1 ∧ β (t * ⟨a, W.a_mem⟩ * t⁻¹ * ⟨a, W.a_mem⟩) = 1 ∧
        β (t * ⟨b, W.b_mem⟩ * t⁻¹ * ⟨b, W.b_mem⟩) = 1 ∧
        (∀ u ∈ Ua, (t : G)⁻¹ * u * (t : G) ∈ Ua) ∧ (∀ u ∈ Ub, (t : G)⁻¹ * u * (t : G) ∈ Ub) := by
  obtain ⟨P₁, P₂, hP₁Pb, hP₂Pb, hc₁, hc₂, -, hdisj, hcsup, hf₁, hf₂, σ, -, hσP⟩ := hES.planes
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨α₁, hα₁, -, hz₁, ho₁⟩ := exists_generator_of_prime_card hc₁
  obtain ⟨α₂, hα₂, -, hz₂, ho₂⟩ := exists_generator_of_prime_card hc₂
  have hPbX : Pb ≤ β.range := by rw [hES.eq]; exact le_sup_left
  have hTbX : Tb ≤ β.range := by rw [hES.eq]; exact le_sup_right
  obtain ⟨x₁, rfl⟩ := MonoidHom.mem_range.mp (hPbX (hP₁Pb hα₁))
  obtain ⟨x₂, rfl⟩ := MonoidHom.mem_range.mp (hPbX (hP₂Pb hα₂))
  obtain ⟨t', ht'Tb, ht'ord, ht'inv⟩ := hES.inv
  obtain ⟨τ, rfl⟩ := MonoidHom.mem_range.mp (hTbX ht'Tb)
  have ht2 : β τ * β τ = 1 := by
    have h1 := pow_orderOf_eq_one (β τ)
    rwa [ht'ord, pow_two] at h1
  have htinv : (β τ)⁻¹ = β τ := inv_eq_of_mul_eq_one_right ht2
  have hrkBA : rk (commV P₂) = rk (commV P₁) := by rw [← hσP, rk_commV_conjBy]
  have hinf : commV P₁ ⊓ commV P₂ = ⊥ := disjoint_iff.mp hdisj
  have hsum := rk_sup_add_rk_inf (commV P₁) (commV P₂)
  rw [hcsup, hinf, rk_top, rk_bot, hES.rk_four] at hsum
  have hcard₁ : Nat.card (commV P₁) = 4 := by
    rw [card_eq_two_pow hES.sq, show rk (commV P₁) = 2 by omega]
    norm_num
  have hcard₂ : Nat.card (commV P₂) = 4 := by
    rw [card_eq_two_pow hES.sq, show rk (commV P₂) = 2 by omega]
    norm_num
  obtain ⟨hord₁, hfree₁, hinv₁⟩ := plane_aux hES.sq hz₁ ho₁ hc₁
  obtain ⟨hord₂, hfree₂, hinv₂⟩ := plane_aux hES.sq hz₂ ho₂ hc₂
  have hinvx₁ : ∀ c ∈ commV P₁, β x₁⁻¹ c ∈ commV P₁ := fun c hc =>
    hinv₁ _ (by rw [map_inv]; exact P₁.inv_mem hα₁) c hc
  have hinvx₂ : ∀ c ∈ commV P₂, β x₂⁻¹ c ∈ commV P₂ := fun c hc =>
    hinv₂ _ (by rw [map_inv]; exact P₂.inv_mem hα₂) c hc
  have hτP : ∀ (P' : Subgroup (MulAut K)), P' ≤ Pb → ∀ c ∈ commV P',
      (∀ p ∈ P', β τ * p * (β τ)⁻¹ = p⁻¹) → β τ⁻¹ c ∈ commV P' := by
    intro P' hP' c hc hinvp
    refine commV_smul_mem (fun p hp => ?_) hc
    rw [map_inv, htinv, hinvp p hp]
    exact P'.inv_mem hp
  have hτ₁ : ∀ c ∈ commV P₁, β τ⁻¹ c ∈ commV P₁ := fun c hc =>
    hτP P₁ hP₁Pb c hc fun p hp => ht'inv p (hP₁Pb hp)
  have hτ₂ : ∀ c ∈ commV P₂, β τ⁻¹ c ∈ commV P₂ := fun c hc =>
    hτP P₂ hP₂Pb c hc fun p hp => ht'inv p (hP₂Pb hp)
  have hW : WtCtx P (x₁ : G) (x₂ : G) (clsPre D (commV P₁)) (clsPre D (commV P₂)) :=
    { a_mem := x₁.2
      b_mem := x₂.2
      Ua_le := clsPre_le_aux D _
      Ub_le := clsPre_le_aux D _
      Z_le_Ua := Z_le_clsPre_aux D _
      Z_le_Ub := Z_le_clsPre_aux D _
      decomp := clsPre_decomp_aux D hcsup
      b_triv := fun u hu => comm_mem_Z_aux D (fun c hc => hf₁ hc _ hα₂) hu
      a_triv := fun u hu => comm_mem_Z_aux D (fun c hc => hf₂ hc _ hα₁) hu
      a_kill := fun u hu => kill_mem_Z_aux D (fun c hc => hinv₁ _ hα₁ c hc) hord₁ hfree₁ hu
      b_kill := fun u hu => kill_mem_Z_aux D (fun c hc => hinv₂ _ hα₂ c hc) hord₂ hfree₂ hu
      a_inv := fun u hu => by simpa using conj_mem_clsPre_aux D hinvx₁ hu
      b_inv := fun u hu => by simpa using conj_mem_clsPre_aux D hinvx₂ hu
      a_gen := gen_clsPre_aux D hES.sq hcard₁
      b_gen := gen_clsPre_aux D hES.sq hcard₂ }
  refine ⟨(x₁ : G), (x₂ : G), clsPre D (commV P₁), clsPre D (commV P₂), hW,
    fun u hu => ((mem_clsPre_aux D).mp hu).1, fun u hu => ((mem_clsPre_aux D).mp hu).1, τ,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact ht2
  · show β (τ * x₁ * τ⁻¹ * x₁) = 1
    rw [map_mul, map_mul, map_mul, map_inv, ht'inv _ (hP₁Pb hα₁), inv_mul_cancel]
  · show β (τ * x₂ * τ⁻¹ * x₂) = 1
    rw [map_mul, map_mul, map_mul, map_inv, ht'inv _ (hP₂Pb hα₂), inv_mul_cancel]
  · intro u hu
    simpa using conj_mem_clsPre_aux D hτ₁ hu
  · intro u hu
    simpa using conj_mem_clsPre_aux D hτ₂ hu

theorem exists_wtCtx {Q U Z Cq Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Cq Hs z)
    {U0 : Subgroup G} {K : Type} [CommGroup K] [Finite K] {β : ↥Hs →* MulAut K} {cls : G → K}
    (D : ClsData P U0 β cls) {Tb Pb : Subgroup (MulAut K)}
    (hES : CFSG.Quasithin.E9Z4Str β.range Tb Pb) :
    ∃ (a b : G) (Ua Ub : Subgroup G), WtCtx P a b Ua Ub := by
  obtain ⟨a, b, Ua, Ub, W, -⟩ := exists_wtCtx_t P D hES
  exact ⟨a, b, Ua, Ub, W⟩

end CFSG.Quasithin.NoE9Z4GenGrp

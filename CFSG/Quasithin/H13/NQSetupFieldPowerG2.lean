module

public import CFSG.Quasithin.H13.NQSetupFieldPower
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.Quasithin.SteinbergCDEvenOrdinaryThreeFreeBorel

public section

namespace CFSG.Quasithin.H13.NQSetup

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Subgroup
open scoped Pointwise

theorem units_map_entrywiseHom_eq_pow_of_mem_torusGroup
    {τ : Tag} {K : Type} [Field K]
    (σ : K →+* K) {n : ℕ} (hσ : ∀ c, σ c = c ^ n) {t : ModGL τ K}
    (ht : t ∈ torusGroup τ K) : Units.map (entrywiseHom σ) t = t ^ n := by
  obtain ⟨hh, hr⟩ := (triangular_borel_structure.{0, 0} τ K).2.1 t ht
  apply Units.ext
  rw [Units.coe_map, Units.val_pow_eq_pow_val]
  change entrywise σ (t : Module.End K (RootModule τ K)) = (t : Module.End K (RootModule τ K)) ^ n
  set T : Module.End K (RootModule τ K) := (t : Module.End K (RootModule τ K)) with hT
  have hpow_h : ∀ (m : ℕ) j, (T ^ m) (hVec τ K j) = hVec τ K j := by
    intro m j
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, Module.End.mul_apply, hh j, ih]
  have hpow_r : ∀ α (c : K), T (rootVec τ K α) = c • rootVec τ K α →
      ∀ m : ℕ, (T ^ m) (rootVec τ K α) = c ^ m • rootVec τ K α := by
    intro α c hc m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Module.End.mul_apply, hc, map_smul, ih, smul_smul, ← pow_succ']
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single]
  rcases b with j | ⟨α, hα⟩
  · have e : (Finsupp.single (Sum.inl j) 1 : RootModule τ K) = hVec τ K j := rfl
    rw [e, hh j, hpow_h n j, hVec, Finsupp.mapRange_single, map_one]
  · have e : (Finsupp.single (Sum.inr ⟨α, hα⟩) 1 : RootModule τ K) = rootVec τ K α := by
      simp [rootVec, hα]
    obtain ⟨c, hc⟩ := hr α hα
    rw [e, hc, hpow_r α c hc n, ← e, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one, Finsupp.mapRange_single, hσ]

theorem even_G2_field_power_of_posUnipotent
    {f : ℕ} (hf : 2 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = 2 ^ f) (A : Subgroup (adjointGroup .G2 k)) (hAodd : Odd (Nat.card A))
    (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set (adjointGroup .G2 k)) *
        ((posUnipotent .G2 k).subgroupOf (adjointGroup .G2 k) : Set (adjointGroup .G2 k)) =
      ((posUnipotent .G2 k).subgroupOf (adjointGroup .G2 k) : Set (adjointGroup .G2 k)) *
        (A : Set (adjointGroup .G2 k))) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∀ α : MulAut (adjointGroup .G2 k), A.map α.toMonoidHom = A →
        ((posUnipotent .G2 k).subgroupOf (adjointGroup .G2 k)).map α.toMonoidHom =
          (posUnipotent .G2 k).subgroupOf (adjointGroup .G2 k) →
        ∃ i < f, ∀ a ∈ A, α a = a ^ 2 ^ i := by
  classical
  set Up := posUnipotent .G2 k with hUpdef
  set U' := Up.subgroupOf (adjointGroup .G2 k) with hU'
  have hf1 : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf1 hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := .G2) (K := k)
  obtain ⟨hTcomm, -, -, -, hBTU, -, -, -, hUnB, -, -, hBC⟩ :=
    triangular_borel_structure.{0, 0} .G2 k
  have hBC' : borelGroup .G2 k ≤ (adjointGroup .G2 k) := (hBC k).1
  have hUB : Up ≤ borelGroup .G2 k := le_sup_right
  have hTB : torusGroup .G2 k ≤ borelGroup .G2 k := le_sup_left
  have hUC : Up ≤ (adjointGroup .G2 k) := hUB.trans hBC'
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem .G2).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_ordinary_Sylow_opposition .G2 k 2 w₀ hw₀
  have hU'2 : IsPGroup 2 U' := by
    rw [hU', ← hP]
    exact P.isPGroup'
  obtain ⟨m, hm⟩ := hU'2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card U') := by
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hAodd)
  have hdisj : Disjoint A U' := disjoint_of_coprime_natCard hcop
  obtain ⟨D₀, hAD, hUD, hDcard⟩ := exists_subgroup_mul_eq A U' hAU hdisj
  have hDC : D₀.map (adjointGroup .G2 k).subtype ≤ (adjointGroup .G2 k) := map_subtype_le D₀
  have hUD' : Up ≤ D₀.map (adjointGroup .G2 k).subtype := by
    intro u hu
    exact ⟨⟨u, hUC hu⟩, hUD (show (⟨u, hUC hu⟩ : (adjointGroup .G2 k)) ∈ U' from hu), rfl⟩
  have hD3 : ¬ 3 ∣ Nat.card (D₀.map (adjointGroup .G2 k).subtype) := by
    rw [Subgroup.card_map_of_injective (adjointGroup .G2 k).subtype_injective, hDcard, hm]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · exact hA3 h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at this
  have hDB := SteinbergCD.even_ordinary_three_free_posUnipotent_overgroups_le_borelGroup hDC
    hUD' hD3
  set A' := A.map (adjointGroup .G2 k).subtype with hA'def
  have hA'B : A' ≤ borelGroup .G2 k := (map_mono hAD).trans hDB
  have hA'U : A' ⊓ Up = ⊥ := by
    rw [eq_bot_iff]
    rintro x hx
    obtain ⟨⟨a, ha, rfl⟩, hxU⟩ := mem_inf.1 hx
    have h1 : a ∈ A ⊓ U' := mem_inf.2 ⟨ha, hxU⟩
    rw [hdisj.eq_bot, mem_bot] at h1
    rw [h1, map_one]
    exact one_mem _
  have hUn : ∀ b ∈ borelGroup .G2 k, ∀ u ∈ Up, b * u * b⁻¹ ∈ Up := by
    intro b hb u hu
    have := hUnB.conj_mem ⟨u, hUB hu⟩ (show (⟨u, hUB hu⟩ : borelGroup .G2 k) ∈
      Up.subgroupOf (borelGroup .G2 k) from hu) ⟨b, hb⟩
    rw [mem_subgroupOf] at this
    simpa using this
  have hBTU' : ∀ b ∈ borelGroup .G2 k, ∃ t ∈ torusGroup .G2 k, ∃ u ∈ Up, b = t * u := by
    intro b hb
    have hb' : b ∈ (torusGroup .G2 k : Set (ModGL .G2 k)) * (Up : Set (ModGL .G2 k)) := by
      rw [← hBTU]
      exact hb
    obtain ⟨t, ht, u, hu, rfl⟩ := hb'
    exact ⟨t, ht, u, hu, rfl⟩
  obtain ⟨hcommA, hpow⟩ := borel_power_action hTB hUB hUn hTcomm hBTU' hA'B hA'U
  refine ⟨fun a ha b hb => Subtype.ext (hcommA _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩),
    fun α hαA hαU => ?_⟩
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      hf k hk).1 α
  simp only at hgδ
  obtain ⟨i, hi, hδi⟩ := exists_pow_two_pow_of_ringEquiv hf1 hk δ
  set δ' : ModGL .G2 k →* ModGL .G2 k := Units.map (entrywiseHom δ.toRingHom) with hδ'
  have hδU : Up.map δ' = Up := ((chevalley_root_character_and_field_conjugation .G2 k).2.2.2.2.1
    δ).2.1
  have hδU' : ∀ u ∈ Up, δ' u ∈ Up := fun u hu => hδU ▸ mem_map_of_mem δ' hu
  have hδT : ∀ t ∈ torusGroup .G2 k, δ' t = t ^ 2 ^ i := fun t ht =>
    units_map_entrywiseHom_eq_pow_of_mem_torusGroup δ.toRingHom (fun c => hδi c) ht
  have hgB : (g : ModGL .G2 k) ∈ borelGroup .G2 k := by
    rw [← (borel_self_normalizers .G2 k).1]
    refine mem_inf.2 ⟨g.2, ?_⟩
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : x ∈ Up.map δ' := by rw [hδU]; exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      have hyC : y ∈ (adjointGroup .G2 k) := hUC hy
      have h2 : α ⟨y, hyC⟩ ∈ U' := by
        rw [← hαU]
        exact mem_map_of_mem _ (show (⟨y, hyC⟩ : (adjointGroup .G2 k)) ∈ U' from hy)
      rw [mem_subgroupOf, hgδ] at h2
      exact h2
    · intro hx
      have hxC : x ∈ (adjointGroup .G2 k) := by
        have h1 : (g : ModGL .G2 k)⁻¹ * ((g : ModGL .G2 k) * x * (g : ModGL .G2 k)⁻¹) *
            (g : ModGL .G2 k) ∈ (adjointGroup .G2 k) := mul_mem (mul_mem (inv_mem g.2) (hUC hx)) g.2
        simpa [mul_assoc] using h1
      have h2 : (⟨_, hUC hx⟩ : (adjointGroup .G2 k)) ∈ U'.map α.toMonoidHom := by
        rw [hαU]
        exact hx
      obtain ⟨y, hy, hyx⟩ := h2
      have h3 := hgδ y
      rw [show (α y : (adjointGroup .G2 k)) = ⟨_, hUC hx⟩ from hyx] at h3
      have h4 : x = δ' y := by
        have := congrArg (fun z => (g : ModGL .G2 k)⁻¹ * z * g) h3
        simpa [mul_assoc] using this
      rw [h4]
      exact hδU' _ hy
  have hgA : ∀ a ∈ A', (g : ModGL .G2 k) * δ' a * (g : ModGL .G2 k)⁻¹ ∈ A' := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.coe_subtype, ← hgδ a]
    refine ⟨α a, ?_, rfl⟩
    rw [← hαA]
    exact mem_map_of_mem _ ha
  refine ⟨i, hi, fun a ha => Subtype.ext ?_⟩
  rw [hgδ a, coe_pow]
  exact hpow δ' (2 ^ i) hδU' hδT g hgB hgA a ⟨a, ha, rfl⟩

theorem even_G2_common_Sylow_normalizer_acts_by_field_power_on_odd_subgroup
    {f : ℕ}
    (hf : 2 ≤ f) (k : Type) [Field k] (hk : Nat.card k = 2 ^ f)
    (U : Sylow 2 (adjointGroup .G2 k)) (A : Subgroup (adjointGroup .G2 k))
    (hAodd : Odd (Nat.card A)) (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set (adjointGroup .G2 k)) * ((U : Subgroup (adjointGroup .G2 k)) :
        Set (adjointGroup .G2 k)) =
      ((U : Subgroup (adjointGroup .G2 k)) : Set (adjointGroup .G2 k)) *
        (A : Set (adjointGroup .G2 k))) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ α : MulAut (adjointGroup .G2 k), A.map α.toMonoidHom = A →
        (U : Subgroup (adjointGroup .G2 k)).map α.toMonoidHom = U →
        ∃ i < f, ∀ a ∈ A, α a = a ^ 2 ^ i) ∧
      ∀ α : MulAut (adjointGroup .G2 k), A.map α.toMonoidHom = A →
        (U : Subgroup (adjointGroup .G2 k)).map α.toMonoidHom = U →
        ∀ p : ℕ, p.Prime → ∀ (N : Subgroup A) [N.Characteristic],
          CFSG.IsElementaryAbelian p (A ⧸ N) →
          ∃ c : ZMod p, ∀ a b : A, (b : adjointGroup .G2 k) = α a →
            (b : A ⧸ N) = (a : A ⧸ N) ^ c.val := by
  have hf1 : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf1 hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := .G2) (K := k)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem .G2).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_ordinary_Sylow_opposition .G2 k 2 w₀ hw₀
  exact field_power_of_sylow _ P hP f (even_G2_field_power_of_posUnipotent hf k hk) U A hAodd hA3
    hAU

end CFSG.Quasithin.H13.NQSetup

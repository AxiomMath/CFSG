module

public import CFSG.Quasithin.H13.NQSetupFieldPowerG2
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.Quasithin.SteinbergCDEvenFixedThreeFreeBorel

public section

namespace CFSG.Quasithin.H13.NQSetup

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Subgroup
open scoped Pointwise

theorem even_triality_field_power_of_posUnipotent
    {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = (2 ^ f) ^ 3) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (A : Subgroup (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) (hAodd : Odd (Nat.card A))
    (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) *
        ((graphFixedPosUnipotent TwistTag.D4 k σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 k σ.toRingHom) :
          Set (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) =
      ((graphFixedPosUnipotent TwistTag.D4 k σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 k σ.toRingHom) :
          Set (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) *
        (A : Set (graphFixedRootGroup TwistTag.D4 k σ.toRingHom))) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 k σ.toRingHom), A.map α.toMonoidHom = A →
        ((graphFixedPosUnipotent TwistTag.D4 k σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)).map α.toMonoidHom =
          (graphFixedPosUnipotent TwistTag.D4 k σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 k σ.toRingHom) →
        ∃ i < 3 * f, ∀ a ∈ A, α a = a ^ 2 ^ i := by
  classical
  have hK3 : Nat.card k = 2 ^ (3 * f) := by rw [hk, ← pow_mul, mul_comm]
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := k)
  set Up := graphFixedPosUnipotent TwistTag.D4 k σ.toRingHom with hUpdef
  set U' := Up.subgroupOf (graphFixedRootGroup TwistTag.D4 k σ.toRingHom) with hU'
  set B1 := graphFixedRootBorel TwistTag.D4 k σ.toRingHom with hB1
  set H1 := graphFixedRootTorus TwistTag.D4 k σ.toRingHom with hH1
  obtain ⟨hBHU, -, -, -, hUB, hUnB, -, hHcomm, -⟩ := fixed_root_Bruhat_decomposition TwistTag.D4 k σ
  have hHB : H1 ≤ B1 := graphFixedRootTorus_le_graphFixedRootBorel
  have hUC : Up ≤ graphFixedRootGroup TwistTag.D4 k σ.toRingHom := le_sup_left
  have hCΓ : graphFixedRootGroup TwistTag.D4 k σ.toRingHom ≤
      twistedFixedGroup TwistTag.D4 k σ.toRingHom := graphFixedRootGroup_le _ _ _
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 k 2 σ w₀ hw₀
  have hU'2 : IsPGroup 2 U' := by
    rw [hU', ← hP]
    exact P.isPGroup'
  obtain ⟨m, hm⟩ := hU'2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card U') := by
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hAodd)
  have hdisj : Disjoint A U' := disjoint_of_coprime_natCard hcop
  obtain ⟨D₀, hAD, hUD, hDcard⟩ := exists_subgroup_mul_eq A U' hAU hdisj
  have hDC : D₀.map (graphFixedRootGroup TwistTag.D4 k σ.toRingHom).subtype ≤
      graphFixedRootGroup TwistTag.D4 k σ.toRingHom := map_subtype_le D₀
  have hUD' : Up ≤ D₀.map (graphFixedRootGroup TwistTag.D4 k σ.toRingHom).subtype := by
    intro u hu
    exact ⟨⟨u, hUC hu⟩, hUD (show (⟨u, hUC hu⟩ : graphFixedRootGroup TwistTag.D4 k σ.toRingHom) ∈
      U' from hu), rfl⟩
  have hD3 : ¬ 3 ∣ Nat.card (D₀.map (graphFixedRootGroup TwistTag.D4 k σ.toRingHom).subtype) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hDcard, hm]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · exact hA3 h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at this
  have hDB := SteinbergCD.even_diagram_fixed_three_free_posUnipotent_overgroups_le_borel
    TwistTag.D4 k σ hDC hUD' hD3
  set A' := A.map (graphFixedRootGroup TwistTag.D4 k σ.toRingHom).subtype with hA'def
  have hA'B : A' ≤ B1 := (map_mono hAD).trans hDB
  have hA'U : A' ⊓ Up = ⊥ := by
    rw [eq_bot_iff]
    rintro x hx
    obtain ⟨⟨a, ha, rfl⟩, hxU⟩ := mem_inf.1 hx
    have h1 : a ∈ A ⊓ U' := mem_inf.2 ⟨ha, hxU⟩
    rw [hdisj.eq_bot, mem_bot] at h1
    rw [h1, map_one]
    exact one_mem _
  have hUn : ∀ b ∈ B1, ∀ u ∈ Up, b * u * b⁻¹ ∈ Up := by
    intro b hb u hu
    have := hUnB.conj_mem ⟨u, hUB hu⟩ (show (⟨u, hUB hu⟩ : B1) ∈ Up.subgroupOf B1 from hu) ⟨b, hb⟩
    rw [mem_subgroupOf] at this
    simp only [coe_mul, coe_inv] at this
    exact this
  have hBTU' : ∀ b ∈ B1, ∃ t ∈ H1, ∃ u ∈ Up, b = t * u := by
    intro b hb
    have hb' : b ∈ (H1 : Set (ModGL TwistTag.D4.tag k)) * (Up : Set (ModGL TwistTag.D4.tag k)) := by
      rw [← hBHU]
      exact hb
    obtain ⟨t, ht, u, hu, rfl⟩ := hb'
    exact ⟨t, ht, u, hu, rfl⟩
  obtain ⟨hcommA, hpow⟩ := borel_power_action hHB hUB hUn hHcomm hBTU' hA'B hA'U
  refine ⟨fun a ha b hb => Subtype.ext (hcommA _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩),
    fun α hαA hαU => ?_⟩
  obtain ⟨hcoe, hNF, -⟩ := even_triality_exact_automorphism_normal_form hf k hk σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF α
  simp only at hgδ
  obtain ⟨i, hi, hδi⟩ := exists_pow_two_pow_of_ringEquiv (by omega : 1 ≤ 3 * f) hK3 δ
  set δ' : ModGL TwistTag.D4.tag k →* ModGL TwistTag.D4.tag k :=
    Units.map (entrywiseHom δ.toRingHom) with hδ'
  have hα : ∀ x : graphFixedRootGroup TwistTag.D4 k σ.toRingHom,
      (α x : ModGL TwistTag.D4.tag k) = (g : ModGL TwistTag.D4.tag k) * δ' x *
        (g : ModGL TwistTag.D4.tag k)⁻¹ := by
    intro x
    rw [hgδ, MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_mul, hcoe, coe_inv]
  have hδC : ∀ x ∈ graphFixedRootGroup TwistTag.D4 k σ.toRingHom,
      δ' x ∈ graphFixedRootGroup TwistTag.D4 k σ.toRingHom := fun x hx => by
    have := (fieldActor σ δ ⟨x, hx⟩).2
    rwa [hcoe] at this
  have hδpos : ∀ x, x ∈ posUnipotent TwistTag.D4.tag k → δ' x ∈ posUnipotent TwistTag.D4.tag k :=
    fun x hx => ((chevalley_root_character_and_field_conjugation TwistTag.D4.tag k).2.2.2.2.1
      δ).2.1 ▸ mem_map_of_mem _ hx
  have hδpos' : ∀ x, δ' x ∈ posUnipotent TwistTag.D4.tag k →
      x ∈ posUnipotent TwistTag.D4.tag k := by
    intro x hx
    have h1 := ((chevalley_root_character_and_field_conjugation TwistTag.D4.tag k).2.2.2.2.1
      δ⁻¹).2.1 ▸ mem_map_of_mem (Units.map (entrywiseHom δ⁻¹.toRingHom)) hx
    have e : Units.map (entrywiseHom δ⁻¹.toRingHom) (δ' x) = x := by
      refine Units.ext ?_
      change entrywise δ⁻¹.toRingHom (entrywise δ.toRingHom (x : Module.End k
        (RootModule TwistTag.D4.tag k))) = _
      rw [entrywise_entrywise]
      have hid : (δ⁻¹.toRingHom).comp δ.toRingHom = RingHom.id k := by
        ext c
        simp
      rw [hid, entrywise_id]
    rw [e] at h1
    exact h1
  have hδU : ∀ x ∈ graphFixedRootGroup TwistTag.D4 k σ.toRingHom, x ∈ Up ↔ δ' x ∈ Up := by
    intro x hx
    constructor
    · intro hxU
      exact mem_inf.2 ⟨hδpos x (mem_inf.1 hxU).1, hCΓ (hδC x hx)⟩
    · intro hxU
      exact mem_inf.2 ⟨hδpos' x (mem_inf.1 hxU).1, hCΓ hx⟩
  have hδU' : ∀ u ∈ Up, δ' u ∈ Up := fun u hu => (hδU u (hUC hu)).1 hu
  have hδT : ∀ t ∈ H1, δ' t = t ^ 2 ^ i := fun t ht =>
    units_map_entrywiseHom_eq_pow_of_mem_torusGroup δ.toRingHom (fun c => hδi c)
      (mem_inf.1 (mem_inf.1 ht).1).1
  have hgB : (g : ModGL TwistTag.D4.tag k) ∈ B1 := by
    rw [hB1, ← (fixed_Borel_self_normalizers TwistTag.D4 k σ w₀ hw₀).2.2.2.2.2.2.1]
    refine mem_inf.2 ⟨g.2, ?_⟩
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      set y := (fieldActor σ δ)⁻¹ ⟨x, hUC hx⟩ with hy
      have hyx : δ' y = x := by
        have := congrArg Subtype.val (MulAut.apply_inv_self _ (fieldActor σ δ) ⟨x, hUC hx⟩)
        rw [hcoe] at this
        exact this
      have hyU : (y : ModGL TwistTag.D4.tag k) ∈ Up := (hδU y y.2).2 (by rw [hyx]; exact hx)
      have h2 : α y ∈ U' := by
        rw [← hαU]
        exact mem_map_of_mem _ (show y ∈ U' from hyU)
      rw [mem_subgroupOf, hα, hyx] at h2
      exact h2
    · intro hx
      have hxC : x ∈ graphFixedRootGroup TwistTag.D4 k σ.toRingHom := by
        have h1 : (g : ModGL TwistTag.D4.tag k)⁻¹ * ((g : ModGL TwistTag.D4.tag k) * x *
            (g : ModGL TwistTag.D4.tag k)⁻¹) * (g : ModGL TwistTag.D4.tag k) ∈
            graphFixedRootGroup TwistTag.D4 k σ.toRingHom :=
          mul_mem (mul_mem (inv_mem g.2) (hUC hx)) g.2
        simpa [mul_assoc] using h1
      have h2 : (⟨_, hUC hx⟩ : graphFixedRootGroup TwistTag.D4 k σ.toRingHom) ∈
          U'.map α.toMonoidHom := by
        rw [hαU]
        exact hx
      obtain ⟨y, hy, hyx⟩ := h2
      have h3 := hα y
      rw [show (α y : graphFixedRootGroup TwistTag.D4 k σ.toRingHom) = ⟨_, hUC hx⟩ from hyx] at h3
      have h4 : x = δ' y := by
        have := congrArg (fun z => (g : ModGL TwistTag.D4.tag k)⁻¹ * z * g) h3
        simpa [mul_assoc] using this
      rw [h4]
      exact hδU' _ hy
  have hgA : ∀ a ∈ A', (g : ModGL TwistTag.D4.tag k) * δ' a * (g : ModGL TwistTag.D4.tag k)⁻¹ ∈
      A' := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.coe_subtype, ← hα a]
    refine ⟨α a, ?_, rfl⟩
    rw [← hαA]
    exact mem_map_of_mem _ ha
  refine ⟨i, hi, fun a ha => Subtype.ext ?_⟩
  rw [hα a, coe_pow]
  exact hpow δ' (2 ^ i) hδU' hδT g hgB hgA a ⟨a, ha, rfl⟩

theorem even_triality_common_Sylow_normalizer_acts_by_field_power_on_odd_subgroup
    {f : ℕ}
    (hf : 1 ≤ f) (k : Type) [Field k] (hk : Nat.card k = (2 ^ f) ^ 3) (σ : k ≃+* k)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (U : Sylow 2 (graphFixedRootGroup TwistTag.D4 k σ.toRingHom))
    (A : Subgroup (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) (hAodd : Odd (Nat.card A))
    (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) *
        ((U : Subgroup (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) =
      ((U : Subgroup (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) *
        (A : Set (graphFixedRootGroup TwistTag.D4 k σ.toRingHom))) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ α : MulAut (graphFixedRootGroup TwistTag.D4 k σ.toRingHom), A.map α.toMonoidHom = A →
        (U : Subgroup (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)).map α.toMonoidHom = U →
        ∃ i < 3 * f, ∀ a ∈ A, α a = a ^ 2 ^ i) ∧
      ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 k σ.toRingHom), A.map α.toMonoidHom = A →
        (U : Subgroup (graphFixedRootGroup TwistTag.D4 k σ.toRingHom)).map α.toMonoidHom = U →
        ∀ p : ℕ, p.Prime → ∀ (N : Subgroup A) [N.Characteristic],
          CFSG.IsElementaryAbelian p (A ⧸ N) →
          ∃ c : ZMod p, ∀ a b : A,
            (b : graphFixedRootGroup TwistTag.D4 k σ.toRingHom) = α a →
            (b : A ⧸ N) = (a : A ⧸ N) ^ c.val := by
  have hK3 : Nat.card k = 2 ^ (3 * f) := by rw [hk, ← pow_mul, mul_comm]
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := k)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 k 2 σ w₀ hw₀
  exact field_power_of_sylow _ P hP (3 * f) (even_triality_field_power_of_posUnipotent hf k hk σ hσ)
    U A hAodd hA3 hAU

end CFSG.Quasithin.H13.NQSetup

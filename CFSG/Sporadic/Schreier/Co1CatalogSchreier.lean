module

public import CFSG.Sporadic.Schreier.Co1Normalizer
public import CFSG.Sporadic.Schreier.Co1ModuleUniq

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.GroupActions CFSG.RepresentationTheory

section Generic

variable {G : Type*} [Group G] (K : Subgroup G)

theorem normalizerMonoidHom_injective (hC : Subgroup.centralizer (K : Set G) = ⊥) :
    Function.Injective K.normalizerMonoidHom := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC, Subgroup.bot_subgroupOf]

theorem normalizerMonoidHom_surjective_of
    (h : ∀ α : MulAut K, ∃ T : G, ∀ g : K, T * (α g : G) = g * T) :
    Function.Surjective K.normalizerMonoidHom := by
  intro α
  obtain ⟨T, hT⟩ := h α
  have hα : ∀ g : K, (α g : G) = T⁻¹ * g * T := fun g => by
    rw [mul_assoc, ← hT g, ← mul_assoc, inv_mul_cancel, one_mul]
  have hmem : T⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [inv_inv]
    constructor
    · intro hx
      rw [← hα ⟨x, hx⟩]
      exact (α ⟨x, hx⟩).2
    · intro hx
      have he := hα (α.symm ⟨T⁻¹ * x * T, hx⟩)
      rw [MulEquiv.apply_symm_apply] at he
      have hxe : x = (α.symm ⟨T⁻¹ * x * T, hx⟩ : G) := mul_left_cancel (mul_right_cancel he)
      rw [hxe]
      exact (α.symm _).2
  refine ⟨⟨T⁻¹, hmem⟩, MulEquiv.ext fun g => Subtype.ext ?_⟩
  rw [normalizerMonoidHom_coe, hα, Subgroup.coe_inv, inv_inv]

theorem exists_normalizer_equiv (hC : Subgroup.centralizer (K : Set G) = ⊥)
    (h : ∀ α : MulAut K, ∃ T : G, ∀ g : K, T * (α g : G) = g * T) :
    ∃ e : Subgroup.normalizer (K : Set G) ≃* MulAut K,
      (∀ (A : Subgroup.normalizer (K : Set G)) (g : K), ((e A g : K) : G) = A * g * (A : G)⁻¹) ∧
      ∃ e' : Subgroup.normalizer (K : Set G) ⧸ K.subgroupOf (Subgroup.normalizer (K : Set G)) ≃*
        Outer K, ∀ A : Subgroup.normalizer (K : Set G),
          e' (QuotientGroup.mk A) = ((e A : MulAut K) : Outer K) := by
  let e := MulEquiv.ofBijective K.normalizerMonoidHom
    ⟨normalizerMonoidHom_injective K hC, normalizerMonoidHom_surjective_of K h⟩
  have he : (K.subgroupOf (Subgroup.normalizer (K : Set G))).map (e : _ →* MulAut K) =
      inner K := by
    ext α
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨A, hA, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hA
      refine ⟨⟨A, hA⟩, ?_⟩
      show MulAut.conj ⟨(A : G), hA⟩ = K.normalizerMonoidHom A
      rw [← normalizerMonoidHom_of_mem]
    · rintro ⟨k, rfl⟩
      refine ⟨⟨k, Subgroup.le_normalizer k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, ?_⟩
      show K.normalizerMonoidHom ⟨k, Subgroup.le_normalizer k.2⟩ = MulAut.conj k
      exact normalizerMonoidHom_of_mem K k
  refine ⟨e, fun A g => ?_, QuotientGroup.congr _ _ e he,
    fun A => QuotientGroup.congr_mk _ _ e he A⟩
  show ((K.normalizerMonoidHom A g : K) : G) = A * g * (A : G)⁻¹
  rw [normalizerMonoidHom_coe, Subgroup.coe_inv]

end Generic

theorem catalog_schreier_of_inputs
    (hCo2 : ∀ (K : Type*) [Group K], K ≃* Blueprint.NativeSporadic.Co2 →
      Finite (Outer K) ∧ IsPGroup 2 (Outer K) ∧ Group.IsSolvable (Outer K)) :
    (∃ e : linNorm ≃* MulAut GA,
      (∀ (A : linNorm) (g : GA), ((e A g : GA) : GL24) = A * g * (A : GL24)⁻¹) ∧
      ∃ e' : linNorm ⧸ GA.subgroupOf linNorm ≃* Outer GA, ∀ A : linNorm,
        e' (A : linNorm ⧸ GA.subgroupOf linNorm) = ((e A : MulAut GA) : Outer GA)) ∧
    Finite (Outer Blueprint.NativeSporadic.Co1) ∧
    IsPGroup 2 (Outer Blueprint.NativeSporadic.Co1) ∧
    Nat.card (Outer Blueprint.NativeSporadic.Co1) ∣
      Nat.card (Outer Blueprint.NativeSporadic.Co2) := by
  obtain ⟨-, -, huniq3, huniq4⟩ := degree_twenty_four_module_uniqueness.{0}
  obtain ⟨e, he, e', he'⟩ := exists_normalizer_equiv GA centralizer_GA huniq4
  obtain ⟨-, hdiv, -, -, hred⟩ := linear_normalizer_and_module_uniqueness_reduction_of_inputs hCo2
  obtain ⟨hfin, hp⟩ := hred fun ρ hρ _ => by
    obtain ⟨T, hT⟩ := huniq3 ρ hρ
    refine ⟨T⁻¹, fun g => ?_⟩
    rw [inv_inv, Subgroup.coe_subtype, mul_assoc, ← hT g, ← mul_assoc, inv_mul_cancel, one_mul]
  have hCo1GA : Nat.card (Outer Blueprint.NativeSporadic.Co1) = Nat.card (Outer GA) :=
    card_outer_congr co1GAEquiv
  have hcard : Nat.card (Outer Blueprint.NativeSporadic.Co1) =
      Nat.card (linNorm ⧸ GA.subgroupOf linNorm) := by
    rw [hCo1GA]
    exact Nat.card_congr e'.symm.toEquiv
  refine ⟨⟨e, he, e', he'⟩, hfin, hp, ?_⟩
  rw [hcard]
  exact hdiv

end CFSG.Sporadic.Co1Schreier

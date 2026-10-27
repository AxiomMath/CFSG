module

public import CFSG.Monster.B.E6.StdF4RadicalChars

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4
open scoped commutatorElement

theorem mem_diagramOrbit_iff (a b : Fin TwistTag.E6.tag.rank → ℤ) :
    b ∈ TwistTag.E6.diagramOrbit a ↔ b = a ∨ b = rho a := by
  unfold TwistTag.diagramOrbit
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < 2 := by simpa [show TwistTag.E6.order = 2 from rfl] using hk
    interval_cases k
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [show TwistTag.E6.order = 2 from rfl], rfl⟩
    · exact ⟨1, by simp [show TwistTag.E6.order = 2 from rfl], rfl⟩

theorem rhoCommCheck : (List.range 21).all (fun k => !cC k (rhoIdx k)) = true := by decide +kernel

theorem X1_rho_comm
    {a : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a) (h1 : 0 < a 1) :
    X1 a * X1 (rho a) = X1 (rho a) * X1 a := by
  obtain ⟨k, hk, rfl⟩ := exists_rr_eq ha h1
  have h := rhoCommCheck
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  have e := rels_xr.rel k (mem_range_21 hk) (rhoIdx k) (mem_range_21 (rhoIdx_lt hk))
  rw [h k hk, zb_false, mul_one] at e
  rw [rho, permLattice_rr hk]
  exact e

theorem standard_F4_radical_center_and_64_character_orbits :
    (∀ g : stdGroup, (g : ModGL Tag.E6 K) ∈ groupJ ↔
      Commute (SemidirectProduct.inl g : FieldExtension.GStar) betaStarElt) ∧
    (∀ a : Fin Tag.E6.rank → ℤ, a ∈ radRootList ↔ IsRoot Tag.E6 a ∧ 0 < height a ∧ 0 < a 1) ∧
    radRootList.length = 21 ∧ radRootList.Nodup ∧
    (∀ a b : Fin TwistTag.E6.tag.rank → ℤ, b ∈ TwistTag.E6.diagramOrbit a ↔ b = a ∨ b = rho a) ∧
    (∀ a : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 a → 0 < a 1 →
      X1 a * X1 (rho a) = X1 (rho a) * X1 a) ∧
    radicalQ ≤ groupJ ∧ Nat.card radicalQ = 2 ^ 15 ∧
    ⁅radicalQ, radicalQ⁆ = Subgroup.zpowers rootInvM ∧
    radicalZ = (Subgroup.center radicalQ).map radicalQ.subtype ∧
    (∀ z ∈ radicalZ, ∀ z' ∈ radicalZ, z * z' = z' * z) ∧ (∀ z ∈ radicalZ, z * z = 1) ∧
    Nat.card radicalZ = 2 ^ 7 ∧
    (radicalZ.subgroupOf radicalQ).index = 2 ^ 8 ∧
    (∀ x ∈ radicalQ, x * x ∈ radicalZ) ∧
    (∀ x ∈ radicalQ, ∀ y ∈ radicalQ, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = rootInvM) ∧
    (∀ x ∈ radicalQ, ∀ x' ∈ radicalQ, ∀ y ∈ radicalQ, ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆) ∧
    (∀ x ∈ radicalQ, x ∈ radicalZ ↔ ∀ y ∈ radicalQ, ⁅x, y⁆ = 1) ∧
    (∀ i, sympA i ∈ radicalQ) ∧ (∀ i, sympB i ∈ radicalQ) ∧
    (∀ i j : Fin 4, ⁅sympA i, sympB j⁆ = (if i = j then rootInvM else 1) ∧
      ⁅sympA i, sympA j⁆ = 1 ∧ ⁅sympB i, sympB j⁆ = 1) ∧
    radicalQ = radicalZ ⊔ Subgroup.closure (Set.range sympA ∪ Set.range sympB) ∧
    leviL0 ≤ groupJ ∧ leviL0 ≤ Subgroup.normalizer (radicalQ : Set (ModGL Tag.E6 K)) ∧
    leviL0 ≤ Subgroup.normalizer (radicalZ : Set (ModGL Tag.E6 K)) ∧
    leviL0 ≤ Subgroup.centralizer {rootInvM} ∧
    zB 0 = rootInvM ∧ Function.Bijective zMap ∧
    (∀ j : Fin 7, zMap (Multiplicative.ofAdd (Pi.single j 1)) = zBZ j) ∧
    (∀ (k : Fin 6) (i : Fin 7), leviGen k * zB i * (leviGen k)⁻¹ = zProdM (centerCols k i)) ∧
    Nat.card {χ : radicalZ →* ℂˣ // χ tZ = -1} = 64 ∧
    ∃ χ₁ χ₂ : radicalZ →* ℂˣ, χ₁ tZ = -1 ∧ χ₂ tZ = -1 ∧
      (leviOrbit χ₁).ncard = 28 ∧ (leviOrbit χ₂).ncard = 36 ∧
      Disjoint (leviOrbit χ₁) (leviOrbit χ₂) ∧
      ∀ χ : radicalZ →* ℂˣ, χ tZ = -1 ↔ χ ∈ leviOrbit χ₁ ∨ χ ∈ leviOrbit χ₂ :=
  ⟨mem_groupJ_iff_commute, fun _ => mem_radRootList_iff, radRootList_length, radRootList_nodup,
    mem_diagramOrbit_iff,
    fun _ ha h1 => X1_rho_comm ha h1, radicalQ_le_groupJ, card_radicalQ, commutator_radicalQ, rfl,
    fun _ hz _ hz' => mul_comm_of_mem_radicalZ hz hz', fun _ hz => mul_self_of_mem_radicalZ hz,
    card_radicalZ, index_radicalZ, fun _ hx => mul_self_mem_radicalZ hx,
    fun _ hx _ hy => commutator_eq_one_or_eq hx hy,
    fun _ hx _ hx' _ hy => commutator_mul_left hx hx' hy,
    fun _ hx => mem_radicalZ_iff_commutator hx, sympA_mem, sympB_mem, symp_relations,
    radicalQ_eq_sup, leviL0_le_groupJ, leviL0_le_normalizer_radicalQ,
    leviL0_le_normalizer_radicalZ, leviL0_le_centralizer, zB_zero, zMap_bijective, zMap_single,
    leviGen_conj_zB, card_negChars, levi_char_orbits⟩

end CFSG.Monster.B.E6.StdF4Radical

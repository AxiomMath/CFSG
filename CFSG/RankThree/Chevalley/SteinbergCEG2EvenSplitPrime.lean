module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenSplitCentralizers
public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise

namespace EvenG2

theorem odd_card_of_injective_pi_units {X : Type*} [Group X] {L : Type} [Field L] [Finite L]
    [CharP L 2] {n : ℕ} (φ : X →* (Fin n → Lˣ)) (hφ : Function.Injective φ) :
    Odd (Nat.card X) := by
  have hL : Odd (Nat.card (Fin n → Lˣ)) := by
    rw [Nat.card_fun, Nat.card_units, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    have h1 : 1 ≤ Nat.card L := Nat.card_pos
    obtain ⟨m, hm⟩ := even_card_of_charTwo (K := L)
    refine Odd.pow ⟨m - 1, ?_⟩
    have : 2 ≤ Nat.card L := Finite.one_lt_card
    omega
  refine Odd.of_dvd_nat hL ?_
  rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end EvenG2

open EvenG2

theorem even_G2_split_prime_centralizers_and_plane_normalizers (K : Type) [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) :
    (∀ P : Subgroup (adjointGroup .G2 K), IsPGroup p P →
      ∃ g : adjointGroup .G2 K, P.map (MulAut.conj g).toMonoidHom ≤
        (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)) ∧
    Nonempty ((Fin Tag.G2.rank → Kˣ) ≃* torusGroup .G2 K) ∧
    (∀ a : Fin Tag.G2.rank → Kˣ, rootDiagUnit .G2 a ∈ torusGroup .G2 K) ∧
    (∀ h ∈ torusGroup .G2 K, ∃! a : Fin Tag.G2.rank → Kˣ, rootDiagUnit .G2 a = h) ∧
    Odd (Nat.card (torusGroup .G2 K)) ∧
    (∀ a : Fin Tag.G2.rank → Kˣ, orderOf (rootDiagUnit .G2 a) = p →
      ((rootCharKernel a = ∅ ∧ toralCentralizer .G2 K a = torusGroup .G2 K) ∨
        ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} ∧
          toralCentralizer .G2 K a =
            torusGroup .G2 K ⊔ (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ∧
          (toralCentralizer .G2 K a : Set (ModGL .G2 K)) =
            (torusGroup .G2 K : Set (ModGL .G2 K)) *
              ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
                Set (ModGL .G2 K)) ∧
          Function.Injective (rootSL2 .G2 K α) ∧
          (rootSL2 .G2 K α).range = rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) ∧
          IsSimpleGroup (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) :
            Subgroup (ModGL .G2 K)) ∧
          Group.IsPerfect (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) :
            Subgroup (ModGL .G2 K)) ∧
          (∃ x y : (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)),
            x * y ≠ y * x) ∧
          ⁅toralCentralizer .G2 K a, toralCentralizer .G2 K a⁆ =
            rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) ∧
          toralCentralizer .G2 K a ⊓ Subgroup.centralizer
              ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
                Set (ModGL .G2 K)) =
            (Subgroup.center (toralCentralizer .G2 K a)).map
              (toralCentralizer .G2 K a).subtype ∧
          (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ≤
            torusGroup .G2 K) ∧
      Odd (Nat.card (Subgroup.center (toralCentralizer .G2 K a)))) ∧
    (∀ h : ModGL .G2 K, h ∈ torusTorsion K p ↔ h ∈ torusGroup .G2 K ∧ h ^ p = 1) ∧
    CFSG.IsElementaryAbelian p (torusTorsion K p) ∧ Nat.card (torusTorsion K p) = p ^ 2 ∧
    adjointGroup .G2 K ⊓ Subgroup.centralizer (torusTorsion K p : Set (ModGL .G2 K)) =
      torusGroup .G2 K ∧
    (∀ g ∈ adjointGroup .G2 K ⊓ Subgroup.normalizer (torusTorsion K p : Set (ModGL .G2 K)),
      ∃ h ∈ torusGroup .G2 K, ∃ w : WeylGroup .G2,
        g = h * canonicalRep (coxeterSystem .G2) K w) ∧
    (∀ h ∈ torusGroup .G2 K, ∀ h' ∈ torusGroup .G2 K, ∀ w w' : WeylGroup .G2,
      h * canonicalRep (coxeterSystem .G2) K w = h' * canonicalRep (coxeterSystem .G2) K w' →
        h = h' ∧ w = w') ∧
    (∀ h ∈ torusGroup .G2 K, ∀ w : WeylGroup .G2, h * canonicalRep (coxeterSystem .G2) K w ∈
      adjointGroup .G2 K ⊓ Subgroup.normalizer (torusTorsion K p : Set (ModGL .G2 K))) ∧
    (∀ h ∈ torusGroup .G2 K, ∀ (w : WeylGroup .G2) (a : ZMod p),
      (∀ x ∈ torusTorsion K p, h * canonicalRep (coxeterSystem .G2) K w * x *
        (h * canonicalRep (coxeterSystem .G2) K w)⁻¹ = x ^ a.val) →
      (w = 1 ∧ a = 1) ∨ ((∀ v : Fin Tag.G2.rank → ℤ, w • v = -v) ∧ a = -1)) ∧
    (∀ h ∈ torusGroup .G2 K, ∀ x ∈ torusTorsion K p,
      h * canonicalRep (coxeterSystem .G2) K 1 * x *
        (h * canonicalRep (coxeterSystem .G2) K 1)⁻¹ = x) ∧
    (∀ h ∈ torusGroup .G2 K, ∀ w : WeylGroup .G2, (∀ v : Fin Tag.G2.rank → ℤ, w • v = -v) →
      ∀ x ∈ torusTorsion K p, h * canonicalRep (coxeterSystem .G2) K w * x *
        (h * canonicalRep (coxeterSystem .G2) K w)⁻¹ = x⁻¹) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  have hq6 := six_le_card_of_dvd hp hp3 hpq
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 K).1
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  have hHodd : Odd (Nat.card (torusGroup .G2 K)) :=
    odd_card_of_injective_pi_units e.symm.toMonoidHom e.symm.injective
  obtain ⟨hVab, hVcard, hVcent, hVnorm, hVuniq, hVconv, hVscal, hVinv⟩ :=
    G2_toral_prime_plane_centralizer_and_scalar_normalizers K hp hp3 hpq
  refine ⟨fun P hP =>
      exists_conj_map_le_of_not_dvd_index (not_dvd_index_torusGroup_G2 hp hp3 hpq) hP,
    ⟨e⟩, rootDiagUnit_mem_torusGroup_G2, fun h hh => ?_, hHodd, fun a ha => ?_,
    fun h => mem_torusTorsion_iff, hVab, hVcard, hVcent, hVnorm, hVuniq, hVconv, hVscal,
    fun h hh x hx => ?_, hVinv⟩
  · obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    exact ⟨l, hl.symm, fun b hb => rootDiagUnit_injective (hb.trans hl)⟩
  ·
    set X := toralCentralizer .G2 K a with hXdef
    have hZH : (Subgroup.center X).map X.subtype ≤ torusGroup .G2 K → Odd (Nat.card
        (Subgroup.center X)) := fun hle => by
      refine Odd.of_dvd_nat hHodd ?_
      rw [← Subgroup.card_map_of_injective X.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    rcases toral_centralizer_cases_G2_of_charTwo K hp hp3 hpq a ha with ⟨hker, hXH⟩ |
      ⟨α, hα, hker, hXQ, hXset, hcomm, hZ, hZle⟩
    · exact ⟨Or.inl ⟨hker, hXH⟩, hZH ((Subgroup.map_subtype_le _).trans hXH.le)⟩
    · obtain ⟨hinj, hrange, -, -, -, -, -, -, -, -, -, hfin⟩ :=
        even_Chevalley_pinned_root_SL2_maps .G2 K hα
      obtain ⟨hsimple, hperf, hnonab⟩ := hfin inferInstance (by omega)
      exact ⟨Or.inr ⟨α, hα, hker, hXQ, hXset, hinj, hrange, hsimple, hperf, hnonab, hcomm, hZ,
        hZle⟩, hZH hZle⟩
  ·
    rw [canonicalRep_one, mul_one]
    rw [hTcomm h hh x (torusTorsion_le_torusGroup p hx), mul_inv_cancel_right]

end CFSG.RankThree.Chevalley

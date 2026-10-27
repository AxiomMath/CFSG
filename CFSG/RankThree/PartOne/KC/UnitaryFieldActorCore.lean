module

public import CFSG.RankThree.PartOne.KC.ThetaCoreSimpleFixedGroup
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneStatements
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.RankThree.GroupTheory.SteinbergBY (mulAut_conj_apply_eq)

theorem unitary_field_actor_core {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hsim : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) →
      IsSimpleGroup (fieldFixedPSU h n σ) ∧ (¬∀ x y : fieldFixedPSU h n σ, x * y = y * x) ∧
        fixingSubgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
            (fieldFixedPSU h n σ : Set (primeFormP h
              ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
          (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
            (primeFormFieldHom h (isPrimeFormGram_one (n := n))) ∧
        (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
            (primeFormFieldHom h (isPrimeFormGram_one (n := n))) =
          Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) ∧
        Nat.card (Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) = p)
    (hexc : n = 3 ∧ ℓ ^ (f / p) = 2 → ∀ x ∈ fieldFixedPSU h n σ, orderOf x ≠ p)
    (B : Subgroup (MulAut (primeFormP h (idGram K n)))) (hB : innU h n ≤ B)
    {a : MulAut (primeFormP h (idGram K n))} (hord : orderOf a = p)
    (hσa : primeFormFieldFactor h isPrimeFormGram_one hn hne a = σ) :
    (n = 3 ∧ ℓ ^ (f / p) = 2 → ∀ g ∈ innU h n, a * g = g * a → orderOf g ≠ p) ∧
    (¬(n = 3 ∧ ℓ ^ (f / p) = 2) →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) := by
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hTfin : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have : Finite (MulAut (primeFormP h (idGram K n))) := inferInstance
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ a
      hord σ hσa hσ
  have hconjinj := KCUnitaryRegular.conj_injective_primeFormP h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn hne
  set u := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  have hua : u⁻¹ * a * u = fσ := hM
  set φ : MulAut (MulAut (primeFormP h (idGram K n))) := MulAut.conj u⁻¹ with hφ
  have hφapp : ∀ x, φ.toMonoidHom x = u⁻¹ * x * u := fun x => by simp [hφ]
  have hφa : φ a = fσ := by
    show φ.toMonoidHom a = _
    rw [hφapp, hua]
  refine ⟨fun hexcp g hg hag hgp => ?_, fun hnexc => ?_⟩
  ·
    obtain ⟨y, rfl⟩ := hg
    have hc : MulAut.conj (u⁻¹ y) = u⁻¹ * MulAut.conj y * u := by
      rw [mulAut_conj_apply_eq, inv_inv]
    have hcomm : fσ * MulAut.conj (u⁻¹ y) = MulAut.conj (u⁻¹ y) * fσ := by
      rw [← hua, hc]
      calc u⁻¹ * a * u * (u⁻¹ * MulAut.conj y * u) = u⁻¹ * (a * MulAut.conj y) * u := by group
        _ = u⁻¹ * (MulAut.conj y * a) * u := by rw [hag]
        _ = u⁻¹ * MulAut.conj y * u * (u⁻¹ * a * u) := by group
    have hfix : fσ (u⁻¹ y) = u⁻¹ y := by
      apply hconjinj
      rw [mulAut_conj_apply_eq, hcomm]
      group
    have hmem : (u⁻¹ y) ∈ fieldFixedPSU h n σ := hfix
    refine hexc hexcp _ hmem ?_
    have h1 : orderOf (MulAut.conj (u⁻¹ y) : MulAut (primeFormP h (idGram K n))) =
        orderOf (u⁻¹ y) := orderOf_injective _ hconjinj (u⁻¹ y)
    have h2 : orderOf (φ (MulAut.conj y)) = orderOf (MulAut.conj y) :=
      orderOf_injective φ.toMonoidHom φ.injective _
    have h3 : φ (MulAut.conj y) = MulAut.conj (u⁻¹ y) := by
      show φ.toMonoidHom _ = _
      rw [hφapp, hc]
    rw [← h1, ← h3, h2]
    exact hgp
  · obtain ⟨hsimple, hnonab, hfix, hz, hcard⟩ := hsim hnexc
    have hordfσ : orderOf fσ = p := by rw [← Nat.card_zpowers]; exact hcard
    have key : ∀ B' : Subgroup (MulAut (primeFormP h (idGram K n))), innU h n ≤ B' →
        inSubgroup (aschbacherSolvableCore p)
          (B' ⊓ Subgroup.centralizer ({fσ} : Set (MulAut (primeFormP h (idGram K n))))) = ⊥ :=
      fun B' hB' => inSubgroup_theta_centralizer_eq_bot_of_simple_fixed_group hp hconjinj
        (a := fσ) hordfσ (H := fieldFixedPSU h n σ) (fun x => Iff.rfl) hsimple hnonab
        (fun s hs => by
          rw [← hz, ← hfix]
          exact (mem_fixingSubgroup_iff (MulAut (primeFormP h (idGram K n)))).mpr fun y hy =>
            hs y hy)
        hB'
    set B' : Subgroup (MulAut (primeFormP h (idGram K n))) := B.map φ.toMonoidHom with hB'
    have hB'conj : innU h n ≤ B' := by
      rintro _ ⟨x, rfl⟩
      refine Subgroup.mem_map.mpr ⟨MulAut.conj (u x), hB ⟨u x, rfl⟩, ?_⟩
      rw [hφapp, mulAut_conj_apply_eq u x]
      group
    have h1 := map_inSubgroup_theta_centralizer_mulEquiv hp φ B a
    rw [hφa, key B' hB'conj] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1

end CFSG.RankThree.PartOne

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRCore
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRAlg

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X P Z : Subgroup G} {y : G}

theorem prop41_core (h : PushHyp X P Z) (hB : BaumannC X Z) (hN : NatFacts X P Z)
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hne : ⁅Z, cj y Z⁆ ≠ ⊥)
    (hle : (cj y (pCoreOf 2 X) ⊓ Z).relIndex Z ≤ (pCoreOf 2 X ⊓ cj y Z).relIndex (cj y Z)) :
    cj y (pCoreOf 2 X) ≠ pCoreOf 2 X ∧ y * y ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) ∧
      ∀ n ∈ Subgroup.normalizer (P : Set G), n ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) →
        n ∈ Subgroup.normalizer ((cj y (pCoreOf 2 X) : Subgroup G) : Set G) := by
  set Q := pCoreOf 2 X with hQ
  have hne' : cj y Q ≠ Q := prop41_core_ne h hy hne
  have hQP : Q ≤ P := h.core_le
  have hQn : P ≤ Subgroup.normalizer (Q : Set G) := h.P_le_normalizer_core
  have hQ'n : P ≤ Subgroup.normalizer ((cj y Q : Subgroup G) : Set G) := h.P_le_normalizer_cj hy
  have hZ'P : cj y Z ≤ P := h.hZ'P hy
  have hZ'Q' : cj y Z ≤ cj y Q := cj_mono y h.le_core
  have hZ'c : ∀ z ∈ cj y Z, ∀ a ∈ cj y Q, z * a = a * z := by
    intro z hz a ha
    have ha' : a ∈ P ⊓ Subgroup.centralizer ((cj y Z : Subgroup G) : Set G) := by
      rw [h.inf_centralizer_cj hy]; exact ha
    exact Subgroup.mem_centralizer_iff.mp ha'.2 z hz
  have hZe : ∀ z ∈ Z, z * z = 1 := fun z hz => by
    have := h.elemAbelian.2 z hz
    simpa [pow_two] using this
  have hZ'e : ∀ z ∈ cj y Z, z * z = 1 := fun z hz => by
    rw [mem_cj] at hz
    have := hZe _ hz
    have e : z * z = y * ((y⁻¹ * z * y) * (y⁻¹ * z * y)) * y⁻¹ := by group
    rw [e, this]; group
  obtain ⟨hP1, hP2⟩ := prop41_P_le h hN hy hne hle
  obtain ⟨hphi, hE⟩ := pr_alg hQP (h.hQ'P hy) hQn hQ'n h.le_core hZ'Q' h.Z_le hZ'P
    (fun z hz a ha => h.commute_Z_core hz ha) hZ'c hZe hZ'e hP1 hP2
    (fun z hz b hb => h.hcZ hy hz hb) (prop41_hG h hB hN hy hne hle)
  refine ⟨hne', ?_, ?_⟩
  ·
    have hyphi : ∀ u ∈ phi Q, y * u * y⁻¹ ∈ phi Q := by
      intro u hu
      have h1 : y * u * y⁻¹ ∈ cj y (phi Q) := by
        rw [mem_cj]; simpa [mul_assoc] using hu
      rwa [← phi_cj, hphi] at h1
    have hEP : cj y (cj y Q) ≤ P := cj_le_of_le_of_mem_normalizer hy (h.hQ'P hy)
    have hsq : ∀ x ∈ cj y (cj y Q), x * x ∈ phi Q := by
      intro x hx
      rw [mem_cj] at hx
      have h1 : (y⁻¹ * x * y) * (y⁻¹ * x * y) ∈ phi Q := by
        have := sq_mem_phi hx
        rwa [hphi] at this
      have h2 := hyphi _ h1
      have e : y * ((y⁻¹ * x * y) * (y⁻¹ * x * y)) * y⁻¹ = x * x := by group
      rwa [e] at h2
    rcases hE _ hEP hsq with hEQ | hEQ'
    · rw [cj_cj] at hEQ
      exact mem_normalizer_of_cj_le hEQ
    · exfalso
      have h1 : cj y (cj y Q) ≤ cj y Q := hEQ'
      have h2 : cj y Q ≤ Q := by
        have := cj_mono y⁻¹ h1
        rwa [cj_inv_cj, cj_inv_cj] at this
      exact hne' (cj_eq_of_cj_le h2)
  · intro n hnP hnQ
    have hEP : cj n (cj y Q) ≤ P := cj_le_of_le_of_mem_normalizer hnP (h.hQ'P hy)
    have hsq : ∀ x ∈ cj n (cj y Q), x * x ∈ phi Q := by
      intro x hx
      rw [mem_cj] at hx
      have h1 : (n⁻¹ * x * n) * (n⁻¹ * x * n) ∈ phi Q := by
        have := sq_mem_phi hx
        rwa [hphi] at this
      have h2 := conj_mem_phi hnQ h1
      have e : n * ((n⁻¹ * x * n) * (n⁻¹ * x * n)) * n⁻¹ = x * x := by group
      rwa [e] at h2
    rcases hE _ hEP hsq with hEQ | hEQ'
    · exfalso
      have h2 : cj y Q ≤ Q := by
        have := cj_mono n⁻¹ hEQ
        rwa [cj_inv_cj, cj_eq_of_mem_normalizer (Subgroup.inv_mem _ hnQ)] at this
      exact hne' (cj_eq_of_cj_le h2)
    · exact mem_normalizer_of_cj_le hEQ'

omit [Finite G] in
theorem relIndex_cj_swap (y : G) (Q Z : Subgroup G) :
    (cj y⁻¹ Q ⊓ Z).relIndex Z = (Q ⊓ cj y Z).relIndex (cj y Z) ∧
      (Q ⊓ cj y⁻¹ Z).relIndex (cj y⁻¹ Z) = (cj y Q ⊓ Z).relIndex Z := by
  constructor
  · rw [← relIndex_cj_cj y, cj_inf, cj_cj_inv]
  · rw [← relIndex_cj_cj y, cj_inf, cj_cj_inv]

theorem prop41 (h : PushHyp X P Z) (hB : BaumannC X Z) (hN : NatFacts X P Z)
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hne : ⁅Z, cj y Z⁆ ≠ ⊥) :
    y * y ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) ∧
      y ∉ Subgroup.normalizer (pCoreOf 2 X : Set G) ∧ cj y (pCoreOf 2 X) ≠ pCoreOf 2 X ∧
      ∀ n ∈ Subgroup.normalizer (P : Set G), n ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) →
        n ∈ Subgroup.normalizer ((cj y (pCoreOf 2 X) : Subgroup G) : Set G) := by
  rcases le_total ((cj y (pCoreOf 2 X) ⊓ Z).relIndex Z)
      ((pCoreOf 2 X ⊓ cj y Z).relIndex (cj y Z)) with hle | hle
  · obtain ⟨h1, h2, h3⟩ := prop41_core h hB hN hy hne hle
    exact ⟨h2, fun hmem => h1 (cj_eq_of_mem_normalizer hmem), h1, h3⟩
  · have hy' : y⁻¹ ∈ Subgroup.normalizer (P : Set G) := Subgroup.inv_mem _ hy
    have hne' : ⁅Z, cj y⁻¹ Z⁆ ≠ ⊥ := by
      intro hbot
      apply hne
      have e : cj y ⁅Z, cj y⁻¹ Z⁆ = ⁅cj y Z, Z⁆ := by
        unfold cj
        rw [Subgroup.map_commutator]
        have := cj_cj_inv y Z
        unfold cj at this
        rw [this]
      have h0 : ⁅cj y Z, Z⁆ = ⊥ := by
        rw [← e, hbot]; exact Subgroup.map_bot _
      rw [Subgroup.commutator_comm]
      exact h0
    have hle' : (cj y⁻¹ (pCoreOf 2 X) ⊓ Z).relIndex Z ≤
        (pCoreOf 2 X ⊓ cj y⁻¹ Z).relIndex (cj y⁻¹ Z) := by
      rw [(relIndex_cj_swap y _ _).1, (relIndex_cj_swap y _ _).2]
      exact hle
    obtain ⟨c1, c2, c3⟩ := prop41_core h hB hN hy' hne' hle'
    have hne1 : cj y (pCoreOf 2 X) ≠ pCoreOf 2 X := by
      intro e
      apply c1
      calc cj y⁻¹ (pCoreOf 2 X) = cj y⁻¹ (cj y (pCoreOf 2 X)) := by rw [e]
        _ = pCoreOf 2 X := cj_inv_cj _ _
    refine ⟨?_, fun hmem => hne1 (cj_eq_of_mem_normalizer hmem), hne1, ?_⟩
    · have := Subgroup.inv_mem _ c2
      simpa using this
    · intro n hnP hnQ
      set N' : Subgroup G := Subgroup.normalizer (P : Set G) ⊓
        Subgroup.normalizer (pCoreOf 2 X : Set G) with hN'
      have key : ∀ m ∈ N', y * m * y⁻¹ ∈ N' := by
        intro m hm
        have h1 := c3 m hm.1 hm.2
        rw [mem_normalizer_cj_iff] at h1
        refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hm.1) (Subgroup.inv_mem _ hy), ?_⟩
        simpa using h1
      have hle3 : cj y N' ≤ N' := fun x hx => by
        rw [mem_cj] at hx
        have := key _ hx
        simpa [mul_assoc] using this
      have heq := cj_eq_of_cj_le hle3
      have hn : n ∈ cj y N' := by rw [heq]; exact ⟨hnP, hnQ⟩
      rw [mem_cj] at hn
      rw [mem_normalizer_cj_iff]
      exact hn.2

end CFSG.Quasithin.F53Push

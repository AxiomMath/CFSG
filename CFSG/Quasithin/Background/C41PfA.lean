module

public import CFSG.Quasithin.Background.C24PfB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace C41Pf

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem conjClosure_le_normalizer (hA3 : A3Orbits G) (h : HypC28 H R M L V)
    (hK : K ∈ cComp H) : conjClosure L M ≤ Subgroup.normalizer (K : Set G) := by
  have hRH : R ≤ H := h.le_M.trans h.le_H
  obtain ⟨T, hT, -⟩ := EscapingLocal.exists_isSylowTwoOf_ge hRH h.pgroup
  obtain ⟨hHT, hcase⟩ := hA3 H T K h.sqtk hT hK
  have hM₀H : conjClosure L M ≤ H := (C2Nine.conjClosure_le_M h).trans h.le_H
  suffices hHH : ⁅H, H⁆ ≤ Subgroup.normalizer (K : Set G) by
    rw [← C2Nine.perfect_conjClosure_of_hyp h]
    exact (Subgroup.commutator_mono hM₀H hM₀H).trans hHH
  have hmemH : ∀ x ∈ H, conjByElt x K ∈ conjSubgroupsBy T K := fun x hx => by
    rw [← hHT]
    exact ⟨x, hx, rfl⟩
  rcases hcase with hTN | ⟨t, htT, htN, hTK, -, -, -⟩
  · have hHN : H ≤ Subgroup.normalizer (K : Set G) := fun x hx => by
      obtain ⟨y, hy, he⟩ := hmemH x hx
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change conjByElt x K = K
      rw [he]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN y hy)
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHN ha) (hHN hb))
      (Subgroup.inv_mem _ (hHN ha))) (Subgroup.inv_mem _ (hHN hb))
  set K' := conjByElt t K with hK'
  have hne : K' ≠ K := fun he => htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have hTH : T ≤ H := hT.1
  have hdi : ∀ x ∈ H, (conjByElt x K = K ∧ conjByElt x K' = K') ∨
      (conjByElt x K = K' ∧ conjByElt x K' = K) := by
    intro x hx
    have h1 : conjByElt x K = K ∨ conjByElt x K = K' := by
      have := hmemH x hx
      rw [hTK] at this
      exact this
    have h2 : conjByElt x K' = K ∨ conjByElt x K' = K' := by
      have e : conjByElt x K' = conjByElt (x * t) K := C22Pf.map_conj_map_conj K t x
      have := hmemH (x * t) (H.mul_mem hx (hTH htT))
      rw [hTK] at this
      rw [e]
      exact this
    have hinj := C2Thirteen.conjByElt_injective x
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (hinj (h1.trans h2.symm)) hne.symm
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (hinj (h1.trans h2.symm)) hne.symm
  have hmul : ∀ x ∈ H, ∀ y ∈ H,
      (conjByElt (x * y) K = K ↔ (conjByElt x K = K ↔ conjByElt y K = K)) := by
    intro x hx y hy
    have e : conjByElt (x * y) K = conjByElt x (conjByElt y K) :=
      (C22Pf.map_conj_map_conj K y x).symm
    rw [e]
    rcases hdi y hy with ⟨hy1, -⟩ | ⟨hy1, -⟩
    · rw [hy1]
      simp
    · rw [hy1]
      rcases hdi x hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · rw [hx1, hx2]
        simp [hne]
      · rw [hx1, hx2]
        simp [hne]
  have hinv : ∀ x : G, (conjByElt x⁻¹ K = K ↔ conjByElt x K = K) := by
    intro x
    constructor
    · intro he
      have := C24Pf.conjByElt_inv_conjByElt x⁻¹ K
      rw [inv_inv, he] at this
      exact this
    · intro he
      have := C24Pf.conjByElt_inv_conjByElt x K
      rw [he] at this
      exact this
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjByElt (a * b * a⁻¹ * b⁻¹) K = K
  have e : a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) := by group
  rw [e, hmul _ (H.mul_mem ha hb) _ (H.mul_mem (H.inv_mem ha) (H.inv_mem hb)),
    hmul _ ha _ hb, hmul _ (H.inv_mem ha) _ (H.inv_mem hb), hinv, hinv]

theorem le_normalizer_conjClosure_of {X : Subgroup G}
    (hX : ∀ m ∈ M, X ≤ Subgroup.normalizer ((conjByElt m L : Subgroup G) : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure L M : Set G) := by
  intro k hk
  refine C22Pf.mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : conjClosure L M ≤ (conjClosure L M).comap (MulAut.conj k).toMonoidHom := by
    refine conjClosure_le fun m hm l hl => ?_
    show k * (m * l * m⁻¹) * k⁻¹ ∈ conjClosure L M
    have hml : m * l * m⁻¹ ∈ conjByElt m L := by
      rw [mem_conjByElt]
      simpa [mul_assoc] using hl
    exact conjByElt_le_conjClosure hm
      ((Subgroup.mem_normalizer_iff.mp (hX m hm hk) _).mp hml)
  exact hle hx

theorem not_commutator_le_pCoreOf (hC129 : ASC129Statement G) (hC111 : ASC111Statement G)
    (hC19 : ASC19Statement G) (hA3 : A3Orbits G) (h : HypC28 H R M L V) (hK : K ∈ cComp H)
    (hKM : ¬ K ≤ M) : ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  apply hKM
  set M₀ := conjClosure L M with hM₀
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hM₀M : M₀ ≤ M := C2Nine.conjClosure_le_M h
  have hNK : M₀ ≤ Subgroup.normalizer (K : Set G) := conjClosure_le_normalizer hA3 h hK
  have hOK : pCoreOf 2 K ≤ M :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans
      ((c2_1_pCore_le (c2_9_two h).2).trans h.le_M)
  set Y := pCoreOf 2 K ⊔ M₀ with hY
  have hYN : Y ≤ Subgroup.normalizer (M₀ : Set G) :=
    sup_le (hOK.trans (le_normalizer_conjClosure L M)) Subgroup.le_normalizer
  have hM₀Y : IsSubnormal M₀ Y :=
    A4.subnormal_of_normal le_sup_right (Subgroup.normal_subgroupOf_of_le_normalizer hYN)
  have hOY : pCoreOf 2 K ≤ pCoreOf 2 Y := by
    refine le_pCoreOf_of_le_normalizer 2 le_sup_left (sup_le ?_ ?_) (pCoreOf_isPGroup 2 K)
    · exact Subgroup.le_normalizer
    · exact hNK.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hKN : ∀ m ∈ M, K ≤ Subgroup.normalizer ((conjByElt m L : Subgroup G) : Set G) := by
    intro m hm
    have hLm : conjByElt m L ∈ cComp M :=
      C2Nine.conjByElt_mem_cComp h.comp (Subgroup.le_normalizer hm)
    have hLmM₀ : conjByElt m L ∈ cComp M₀ :=
      cComp_mem_of_le hLm (conjByElt_le_conjClosure hm) hM₀M
    have hLmY : conjByElt m L ∈ cComp Y := cComp_mem_of_subnormal hM₀Y hLmM₀
    refine C24Pf.le_normalizer_of_commutator_le hLmY ?_
    exact ((Subgroup.commutator_mono (conjByElt_le_conjClosure hm) le_rfl).trans
      hc).trans hOY
  have hKM₀ : K ≤ H ⊓ Subgroup.normalizer (M₀ : Set G) := le_inf hKH
    (le_normalizer_conjClosure_of hKN)
  obtain ⟨T, hT, hRT⟩ := EscapingLocal.exists_isSylowTwoOf_ge h.le_M h.pgroup
  rwa [c2_12 hC129 hC111 hC19 hA3 h hT hRT] at hKM₀

end C41Pf

end CFSG.Quasithin

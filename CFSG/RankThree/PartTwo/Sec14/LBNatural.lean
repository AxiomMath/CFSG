module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec13.Naturality
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

theorem lA_map_eq_singleton (φ : G ≃* G') {A L : Subgroup G} {b : G} (h : lA A b = {L}) :
    lA (A.map φ.toMonoidHom) (φ b) = {L.map φ.toMonoidHom} := by
  ext L'
  rw [Set.mem_singleton_iff]
  constructor
  · intro hL'
    have hL'' : (L'.map φ.symm.toMonoidHom).map φ.toMonoidHom = L' := by
      have := map_symm_map φ.symm L'
      rwa [MulEquiv.symm_symm] at this
    rw [← hL''] at hL' ⊢
    have hmem := (mem_lA_map_iff φ).mp hL'
    rw [h, Set.mem_singleton_iff] at hmem
    rw [hmem]
  · rintro rfl
    exact (mem_lA_map_iff φ).mpr (h ▸ Set.mem_singleton L)

omit [Finite G] [Finite G'] in
theorem nonempty_quot_pCore_two_map (φ : G ≃* G') {L : Subgroup G} {Q : Type*} [Group Q]
    (h : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Q)) :
    Nonempty (↥(L.map φ.toMonoidHom) ⧸ CFSG.pCore 2 ↥(L.map φ.toMonoidHom) ≃* Q) := by
  obtain ⟨e⟩ := h
  let ψ : ↥L ≃* ↥(L.map φ.toMonoidHom) := φ.subgroupMap L
  exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥(L.map φ.toMonoidHom)) ψ
    (CFSG.pCore_map_iso 2 ψ)).symm.trans e⟩

omit [Finite G'] in
theorem exists_sylow_center_map (φ : G ≃* G') {L : Subgroup G} {d : G}
    (h : ∃ hd : d ∈ L, ∃ S : Sylow 3 ↥L, (⟨d, hd⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hd⟩ : ↥L)}) :
    ∃ hd : φ d ∈ L.map φ.toMonoidHom, ∃ S : Sylow 3 ↥(L.map φ.toMonoidHom),
      (⟨φ d, hd⟩ : ↥(L.map φ.toMonoidHom)) ∈ (S : Subgroup ↥(L.map φ.toMonoidHom)) ∧
      (S : Subgroup ↥(L.map φ.toMonoidHom)) ≤
        Subgroup.centralizer {(⟨φ d, hd⟩ : ↥(L.map φ.toMonoidHom))} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hd, S, hdS, hSc⟩ := h
  let ψ : ↥L ≃* ↥(L.map φ.toMonoidHom) := φ.subgroupMap L
  have hψd : ψ ⟨d, hd⟩ = ⟨φ d, ⟨d, hd, rfl⟩⟩ := rfl
  have hsurj : Function.Surjective ψ.toMonoidHom := ψ.surjective
  refine ⟨⟨d, hd, rfl⟩, S.mapSurjective hsurj, ?_, ?_⟩
  · change _ ∈ (S : Subgroup ↥L).map ψ.toMonoidHom
    rw [← hψd]
    exact Subgroup.mem_map_of_mem _ hdS
  · change (S : Subgroup ↥L).map ψ.toMonoidHom ≤ _
    rw [← hψd]
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp (hSc hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change ψ y * ψ ⟨d, hd⟩ = ψ ⟨d, hd⟩ * ψ y
    rw [← map_mul, ← map_mul, hy']

theorem IsLBConfig.map (φ : G ≃* G') {A B L : Subgroup G} {b d : G}
    (h : IsLBConfig A B b d L) :
    IsLBConfig (A.map φ.toMonoidHom) (B.map φ.toMonoidHom) (φ b) (φ d) (L.map φ.toMonoidHom) := by
  obtain ⟨hB, hb, hL, hJ, hd⟩ := h
  refine ⟨?_, ?_, lA_map_eq_singleton φ hL, nonempty_quot_pCore_two_map φ hJ,
    exists_sylow_center_map φ hd⟩
  · rw [hB, MonoidHom.map_closure, Set.image_pair]
    rfl
  · have h := map_mem_omegaA φ hb
    rwa [MonoidHom.map_zpowers] at h

theorem map_lB_le (φ : G ≃* G') (A B : Subgroup G) :
    (lB A B).map φ.toMonoidHom ≤ lB (A.map φ.toMonoidHom) (B.map φ.toMonoidHom) := by
  simp only [lB, Subgroup.map_iSup]
  refine iSup_le fun b => iSup_le fun d => iSup_le fun L => iSup_le fun hc => ?_
  refine le_iSup_of_le (φ b) (le_iSup_of_le (φ d) (le_iSup_of_le (L.map φ.toMonoidHom)
    (le_iSup_of_le (hc.map φ) (le_of_eq ?_))))
  rw [map_inSubgroup_perfectResidual, Subgroup.map_inf_eq _ _ _ φ.injective,
    map_centralizer_singleton]

theorem lB_map (φ : G ≃* G') (A B : Subgroup G) :
    (lB A B).map φ.toMonoidHom = lB (A.map φ.toMonoidHom) (B.map φ.toMonoidHom) := by
  refine le_antisymm (map_lB_le φ A B) ?_
  have h := map_lB_le φ.symm (A.map φ.toMonoidHom) (B.map φ.toMonoidHom)
  rw [map_symm_map, map_symm_map] at h
  have hback := map_symm_map φ.symm (lB (A.map φ.toMonoidHom) (B.map φ.toMonoidHom))
  rw [MulEquiv.symm_symm] at hback
  calc lB (A.map φ.toMonoidHom) (B.map φ.toMonoidHom) =
        ((lB (A.map φ.toMonoidHom) (B.map φ.toMonoidHom)).map φ.symm.toMonoidHom).map
          φ.toMonoidHom := hback.symm
    _ ≤ (lB A B).map φ.toMonoidHom := Subgroup.map_mono h

theorem isNaturalFamily_lB (A : Subgroup G) : IsNaturalFamily A (lB A) := by
  intro w hw B _
  rw [lB_map (MulAut.conj w), map_conj_eq_of_mem_normalizer hw]

end CFSG.RankThree.PartTwo.Sec14

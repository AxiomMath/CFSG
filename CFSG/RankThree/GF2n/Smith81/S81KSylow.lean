module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionLevi
public import CFSG.RankThree.GF2n.Smith81.S81XD6Def
public import CFSG.RankThree.GF2n.Smith81.S81E7Cent

public section

namespace CFSG.RankThree.GF2n.Smith81.SK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction CFSG.SeitzReduction.E7Pilot CFSG.SeitzReduction.EPilot
  CFSG.RankThree.GF2n.Smith81.D6X CFSG.RankThree.GF2n.Smith81.E7X
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.LieType.Steinberg.Minuscule


variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def psiD : ↥(EPilot.perpLevi .E7 K) →* Gp K :=
  (e7Psi K).comp (EPilot.perpLevi .E7 K).subtype

theorem psiD_injective : Function.Injective (psiD K) :=
  ((e7Equiv (K := K)).symm.injective).comp Subtype.val_injective

theorem psiD_range : (psiD K).range = LamG K := by
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    rw [mem_LamG, Lam_eq_map]
    exact ⟨e7Psi K d.1, Subgroup.mem_map_of_mem _ d.2, rfl⟩
  · intro hx
    rw [mem_LamG, Lam_eq_map] at hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hz
    have hdx : e7Psi K d = x := Subtype.ext hzx
    exact ⟨⟨d, hd⟩, hdx⟩

theorem mem_posPerpRoots_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ posPerpRoots) :
    β ∈ Perp ∧ 0 < height β := by
  have hβP : β ∈ EPilot.perpRoots .E7 := ⟨hβ.1, hβ.2.2⟩
  refine ⟨?_, hβ.2.1⟩
  rw [← perpRoots_eq]
  exact hβP

theorem posPerpRoots_of_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (hpos : 0 < height β) :
    β ∈ posPerpRoots := by
  have hβP : β ∈ EPilot.perpRoots .E7 := by
    rw [perpRoots_eq]
    exact hβ
  exact ⟨hβP.1, hpos, hβP.2⟩

theorem psiD_map_posPerpU :
    ((posPerpU K).subgroupOf (EPilot.perpLevi .E7 K)).map (psiD K) = ULG K := by
  apply le_antisymm
  ·
    obtain ⟨M, hM⟩ : ∃ M : Subgroup ↥(adjointGroup .E7 K), ∀ x, x ∈ M ↔ e7Psi K x ∈ ULG K :=
      ⟨(ULG K).comap (e7Psi K), fun x => Iff.rfl⟩
    have hspan : rootSpan .E7 K posPerpRoots ≤ M.map (adjointGroup .E7 K).subtype := by
      unfold rootSpan
      refine iSup₂_le fun β hβ => ?_
      unfold rootSubgroup
      rw [Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      obtain ⟨hβP, hpos⟩ := mem_posPerpRoots_perp hβ
      have hβR : IsRoot .E7 β := (perp_iff.1 hβP).1
      have hMem : pinnedElt .E7 β c ∈ M := by
        rw [hM, e7Psi_pinnedElt' hβR c, mem_ULG]
        exact Subgroup.subset_closure ⟨β, hβR, hβP.2, hpos, c, rfl⟩
      exact Subgroup.mem_map_of_mem (adjointGroup .E7 K).subtype hMem
    have hle : posPerpU K ≤ M := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hspan (Subgroup.mem_subgroupOf.1 hx))
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]
      exact hy
    rintro _ ⟨y, hy, rfl⟩
    exact (hM y.1).1 (hle (Subgroup.mem_subgroupOf.1 hy))
  ·
    intro x hx
    rw [mem_ULG] at hx
    have hgen : UL K ≤ (((posPerpU K).subgroupOf (EPilot.perpLevi .E7 K)).map (psiD K)).map
        (e7Data_valid.minGroup K).subtype := by
      rw [UL, Subgroup.closure_le]
      rintro g ⟨β, hβR, hβP, hpos, c, rfl⟩
      have hβ' : β ∈ Perp := ⟨hβR, hβP⟩
      have hmemP : β ∈ posPerpRoots := posPerpRoots_of_perp hβ' hpos
      have hβE : β ∈ EPilot.perpRoots .E7 := by
        rw [perpRoots_eq]
        exact hβ'
      have hD : pinnedElt .E7 β c ∈ EPilot.perpLevi .E7 K := EPilot.pinnedElt_mem_perpLevi hβE c
      have hU : pinnedElt .E7 β c ∈ posPerpU K := by
        refine Subgroup.mem_subgroupOf.2 ?_
        unfold rootSpan
        exact Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem hmemP
          (Subgroup.subset_closure ⟨c, rfl⟩))
      have h1 : psiD K ⟨pinnedElt .E7 β c, hD⟩ = e7Data_valid.xm K β c :=
        e7Psi_pinnedElt' hβR c
      exact ⟨e7Data_valid.xm K β c, ⟨⟨pinnedElt .E7 β c, hD⟩, Subgroup.mem_subgroupOf.2 hU, h1⟩,
        rfl⟩
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hgen hx)
    have : z = x := Subtype.ext hzx
    rw [← this]
    exact hz

theorem lam_conj_into_ULG (A : Subgroup (Gp K)) (hA : A ≤ LamG K) (h2 : IsPGroup 2 A) :
    ∃ g ∈ LamG K, A.map (MulAut.conj g).toMonoidHom ≤ ULG K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_perpLevi_eq (K := K)
  set A' : Subgroup ↥(EPilot.perpLevi .E7 K) := A.comap (psiD K) with hA'
  have hA'2 : IsPGroup 2 A' := h2.comap_of_injective (psiD K) (psiD_injective (K := K))
  obtain ⟨S', hS'⟩ := hA'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(EPilot.perpLevi .E7 K)) S' S
  refine ⟨psiD K g, ?_, ?_⟩
  · rw [← psiD_range]
    exact ⟨g, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨d, rfl⟩ : a ∈ (psiD K).range := by
      rw [psiD_range]
      exact hA ha
    have hdA' : d ∈ A' := ha
    have h1 : g * d * g⁻¹ ∈ (S : Subgroup ↥(EPilot.perpLevi .E7 K)) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨d, hS' hdA', rfl⟩
    rw [hS] at h1
    rw [← psiD_map_posPerpU (K := K)]
    refine ⟨g * d * g⁻¹, h1, ?_⟩
    simp [map_mul, map_inv]

end CFSG.RankThree.GF2n.Smith81.SK

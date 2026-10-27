module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderKnownAux

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7CLOKnownAux_concl_transport {lab labM : LargeEvenLabel} {k : ℕ}
    (hiso : GGLabelIso lab labM)
    (h : ((labM.tag = .B ∨ labM.tag = .C) ∧ k < labM.rank ∧ labM.n = 1) ∨
      (k = 3 ∧ labM.tag = .F4 ∧ labM.n = 1)) :
    ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ k < lab.rank) ∨
      (lab.tag = .F4 ∧ lab.n = 1 ∧ k = 3) := by
  have htag : labM.tag = .B ∨ labM.tag = .C ∨ labM.tag = .F4 := by
    rcases h with ⟨hBC, -, -⟩ | ⟨-, hF4, -⟩
    · rcases hBC with hB | hC
      · exact Or.inl hB
      · exact Or.inr (Or.inl hC)
    · exact Or.inr (Or.inr hF4)
  rcases hiso with heq | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · subst heq
    rcases h with ⟨hBC, hlt, hn⟩ | ⟨hF4, hn, hlt⟩
    · exact Or.inl ⟨hBC, hn, hlt⟩
    · exact Or.inr ⟨hn, hlt, hF4⟩
  · obtain ⟨hlabBC, hlabMBC, hrank, hn⟩ := hBC
    rcases h with ⟨hBC', hlt, hnm⟩ | ⟨-, hF4, -⟩
    · exact Or.inl ⟨hlabBC, by omega, by omega⟩
    · exfalso
      rcases hlabMBC with hB | hC
      · exact absurd (hB.symm.trans hF4) (by decide)
      · exact absurd (hC.symm.trans hF4) (by decide)
  · exfalso
    have hA : labM.tag = .A := by rw [hDA.2]
    rcases htag with hB | hC | hF4
    · rw [hA] at hB; exact absurd hB (by decide)
    · rw [hA] at hC; exact absurd hC (by decide)
    · rw [hA] at hF4; exact absurd hF4 (by decide)
  · exfalso
    have hD : labM.tag = .D := by rw [hAD.2]
    rcases htag with hB | hC | hF4
    · rw [hD] at hB; exact absurd hB (by decide)
    · rw [hD] at hC; exact absurd hC (by decide)
    · rw [hD] at hF4; exact absurd hF4 (by decide)
  · exfalso
    have hA : labM.tag = .twA := by rw [hD3A3.2]
    rcases htag with hB | hC | hF4
    · rw [hA] at hB; exact absurd hB (by decide)
    · rw [hA] at hC; exact absurd hC (by decide)
    · rw [hA] at hF4; exact absurd hF4 (by decide)
  · exfalso
    have hD : labM.tag = .twD := by rw [hA3D3.2]
    rcases htag with hB | hC | hF4
    · rw [hD] at hB; exact absurd hB (by decide)
    · rw [hD] at hC; exact absurd hC (by decide)
    · rw [hD] at hF4; exact absurd hF4 (by decide)
  · exfalso
    have hA : labM.tag = .A := by rw [hD2A1.2]
    rcases htag with hB | hC | hF4
    · rw [hA] at hB; exact absurd hB (by decide)
    · rw [hA] at hC; exact absurd hC (by decide)
    · rw [hA] at hF4; exact absurd hF4 (by decide)
  · exfalso
    have hD : labM.tag = .twD := by rw [hA1D2.1]
    rcases htag with hB | hC | hF4
    · rw [hD] at hB; exact absurd hB (by decide)
    · rw [hD] at hC; exact absurd hC (by decide)
    · rw [hD] at hF4; exact absurd hF4 (by decide)

theorem hdRo7CLOKnownAux_assembly
    (hKG : GGPumpCLabelKnown) (hRig : GGLabelRigidInput)
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K) [Fact p.Prime]
    (hrow : GGResRowAt ggRowCorank2C p J K)
    (labJ : LargeEvenLabel) (hlabJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hJtag : labJ.tag = .B ∨ labJ.tag = .C) (hJn : labJ.n = 1)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) :
    ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ labJ.rank < lab.rank) ∨
      (lab.tag = .F4 ∧ lab.n = 1 ∧ labJ.rank = 3) := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have hp3 : p = 3 := hdRo7CLOKnownAux_p_eq_three hrow
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, hd, hdn⟩ := hdRo7CLOKnownAux_exists_d hH
  have hmark := hH.2.2.1.1
  unfold GGInnerDiagOn LargeEvenMarking at hmark
  obtain ⟨hcomm, labM, hlabM, hrawM⟩ := hmark
  have hrawKG := hKG p hp hp2 labM hlabM _ hrawM
  obtain ⟨R, hRgrp, I, F, hQ⟩ := largeEvenRawDatum_exists hrawKG
  letI : Group R := hRgrp
  obtain ⟨hsimple, hnonab, θ, hBsN, hinner⟩ := hQ.1
  have hKGinst := hQ.2
  let ψ : ↥L →* R := (θ : (↥L ⧸ Subgroup.center ↥L) →* R).comp
    (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ_surj : Function.Surjective ψ := by
    intro r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψ_ker : ψ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have he1 : hdRo7CLOKnownAux_e hH hd ≠ 1 := by
    intro he
    obtain ⟨l, hl, hne⟩ := hdRo7CLOKnownAux_e_ne_one hH hd hdn
    have h2 := congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) he
    simp only [MulAut.one_apply] at h2
    exact hne (by
      have := congrArg Subtype.val h2
      simpa [hdRo7CLOKnownAux_e] using this)
  have hep : (hdRo7CLOKnownAux_e hH hd) ^ p = 1 := hdRo7CLOKnownAux_e_pow_eq_one hH hd hdn
  have hdBs : d ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hd)
  obtain ⟨φ, hφI, hφ⟩ := hinner d hdBs
  have hφe : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ ((hdRo7CLOKnownAux_e hH hd) l) :=
    ⟨φ, hφI, fun l => hφ l ((hdRo7CLOKnownAux_e hH hd) l) (by simp [hdRo7CLOKnownAux_e])⟩
  have hcomp : CFSG.Assembly.IsComponentOf (J.subgroupOf L) (ggFixSub (hdRo7CLOKnownAux_e hH hd)) :=
    hdRo7CLOKnownAux_component hH hd hdn
  have hk3 : 3 ≤ labJ.rank := by
    have h2 : 2 ≤ labJ.rank := by
      have h := hlabJ
      unfold LargeEvenInLambda2 at h
      rcases hJtag with h' | h' <;> rw [h'] at h <;> exact h.2.1
    have hne : labJ.rank ≠ 2 := by
      intro h
      have hle : 2 ≤ labJ.n := by
        have h' := hlabJ
        unfold LargeEvenInLambda2 at h'
        rcases hJtag with hh | hh <;> rw [hh] at h' <;> exact h'.2.2 h
      omega
    omega
  have hJ_le_L : J ≤ L := (hH.1.2.2.1.2.2.2.2.2.1).1.trans inf_le_left
  have hJlab_C : GGHasLabel ⟨.C, labJ.rank, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
    have hlabJ_eq : labJ = ⟨labJ.tag, labJ.rank, labJ.n⟩ := rfl
    rw [hlabJ_eq] at hJlab
    rw [hJn] at hJlab
    rcases hJtag with hB | hC
    · rw [hB] at hJlab
      exact hJlab
    · rw [hC] at hJlab
      exact hJlab
  have hJlab' : GGHasLabel ⟨.C, labJ.rank, 1⟩
      (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJ_le_L)
      (Subgroup.map_center_eq _)).symm hJlab_C
  have hKGuse := hKGinst ↥L ψ hψ_surj hψ_ker hcomm (hdRo7CLOKnownAux_e hH hd) he1 hep hφe
    (J.subgroupOf L) labJ.rank 1 hcomp hk3 hJlab'
  have hhasM : GGHasLabel labM (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hrawM
    rintro R' _ I' F' ⟨-, -, θ', -⟩
    exact ⟨θ'⟩
  have hiso : GGLabelIso lab labM := by
    unfold GGLabelRigidInput at hRig
    exact hRig lab labM (↥L ⧸ Subgroup.center ↥L) hlab hlabM hLlab hhasM
  exact hdRo7CLOKnownAux_concl_transport hiso hKGuse

end CFSG.StandardType.HdRo7C

end

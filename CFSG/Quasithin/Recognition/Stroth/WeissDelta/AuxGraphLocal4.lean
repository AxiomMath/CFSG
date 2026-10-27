module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RootFacts
public import CFSG.Permutation.BurnsideSchur.RegularCyclic
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
public import CFSG.Quasithin.Vol2.Ch5Sec1DSC
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
import TauCeti.GroupTheory.GroupAction.Transitive
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.AuxGraphLocal2

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

attribute [local instance] auxAction

private noncomputable def auxLocal [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    Subgroup (Equiv.Perm {y : V // Γ.Adj (u : V) y}) :=
  ((auxGroup Γ (W.kernelAt 0) (W.x 0) ⊓ MulAction.stabilizer H (u : V)).subgroupOf
    (MulAction.stabilizer H (u : V))).map (localPermHom (H := H) Γ (u : V))

private theorem mem_auxLocal_iff [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)))
    (σ : Equiv.Perm {y : V // Γ.Adj (u : V) y}) :
    σ ∈ auxLocal hQ u ↔
      ∃ (g : H) (hgu : g • (u : V) = (u : V)), g ∈ auxGroup Γ (W.kernelAt 0) (W.x 0) ∧
        localPermHom (H := H) Γ (u : V) ⟨g, MulAction.mem_stabilizer_iff.mpr hgu⟩ = σ := by
  classical
  constructor
  · intro hσ
    rcases Subgroup.mem_map.mp hσ with ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.mp hx
    exact ⟨x, MulAction.mem_stabilizer_iff.mp x.2, hx'.1, rfl⟩
  · rintro ⟨g, hgu, hg, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hgu⟩,
      Subgroup.mem_subgroupOf.mpr ⟨hg, MulAction.mem_stabilizer_iff.mpr hgu⟩, rfl⟩

private theorem auxLocal_le_localGroup [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    auxLocal hQ u ≤ localGroup H Γ (u : V) := by
  intro σ hσ
  rw [mem_auxLocal_iff] at hσ
  obtain ⟨g, -, -, rfl⟩ := hσ
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

private theorem midEquiv_smul [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) {g : H}
    (hnorm : g ∈ Subgroup.normalizer ((W.kernelAt 0) : Set H))
    (hgu : g • (u : V) = (u : V)) (y : {y : V // Γ.Adj (u : V) y}) :
    midEquiv hQ u ⟨g • y.1, by
        have h := (GraphAction.adj_smul g (u : V) y.1).mpr y.2
        rwa [hgu] at h⟩ =
      ⟨⟨(g : H) • (((midEquiv hQ u y).1 : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) : V),
          by
            have hv : ((midEquiv hQ u y).1 : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))).1 ∈
                auxComp Γ (W.kernelAt 0) (u : V) := by
              rw [auxComp_eq_of_mem (K := W.kernelAt 0) u.2]
              exact ((midEquiv hQ u y).1 : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))).2
            have hmem := mem_auxComp_smul (K := W.kernelAt 0) (u₀ := (u : V)) hnorm hgu hv
            rwa [auxComp_eq_of_mem (K := W.kernelAt 0) u.2] at hmem⟩, by
        apply SimpleGraph.induce_adj.mpr
        have h := auxGraph_adj_smul (K := W.kernelAt 0) hnorm
          (SimpleGraph.induce_adj.mp (midEquiv hQ u y).2)
        rwa [hgu] at h⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  have hy' : Γ.Adj (u : V) (g • y.1) := by
    have h := (GraphAction.adj_smul g (u : V) y.1).mpr y.2
    rwa [hgu] at h
  rw [show midEquiv hQ u ⟨g • y.1, hy'⟩ = midFun hQ u ⟨g • y.1, hy'⟩ from
    Equiv.ofBijective_apply _ _ _]
  rw [show midEquiv hQ u y = midFun hQ u y from Equiv.ofBijective_apply _ _ _]
  exact step_smul hQ u y.2 hnorm hgu hy'

private theorem localPermHom_auxProj_eq [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)))
    (m : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0)))
    (hmu : (m : H) • (u : V) = (u : V)) :
    localPermHom (H := ↥W.auxS) W.auxI u
        ⟨auxProj W m, MulAction.mem_stabilizer_iff.mpr (by
          calc (auxProj W m) • u = m • u := auxProj_smul W m u
            _ = u := Subtype.ext hmu)⟩ =
      (midEquiv hQ u).permCongrHom
        (localPermHom (H := H) Γ (u : V) ⟨(m : H), MulAction.mem_stabilizer_iff.mpr hmu⟩) := by
  classical
  ext v
  rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply]
  simp only [localPermHom_apply, Subgroup.smul_def]
  have hnorm : (m : H) ∈ Subgroup.normalizer ((W.kernelAt 0) : Set H) :=
    (Subgroup.mem_inf.mp m.2).1
  have hstep := midEquiv_smul hQ u hnorm hmu ((midEquiv hQ u).symm v)
  rw [Equiv.apply_symm_apply] at hstep
  have hstepV := congrArg (fun z : {w // W.auxI.Adj u w} =>
    (((z.1 : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) : V))) hstep
  rw [hstepV]
  rfl

private theorem localGroup_aux_eq_auxLocal [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    localGroup (H := ↥W.auxS) W.auxI u =
      (auxLocal hQ u).map (midEquiv hQ u).permCongrHom := by
  classical
  have hsurj : Function.Surjective (auxProj W) := MonoidHom.rangeRestrict_surjective _
  ext σ
  constructor
  · intro hσ
    rw [localGroup, MonoidHom.mem_range] at hσ
    obtain ⟨s, rfl⟩ := hσ
    obtain ⟨m, hm⟩ := hsurj s
    have hsu : s • u = u := MulAction.mem_stabilizer_iff.mp s.2
    have hmu : (m : H) • (u : V) = (u : V) := by
      have h := auxProj_smul W m u
      rw [hm] at h
      exact congrArg Subtype.val (h.symm.trans hsu)
    refine Subgroup.mem_map.mpr ⟨localPermHom (H := H) Γ (u : V)
      ⟨(m : H), MulAction.mem_stabilizer_iff.mpr hmu⟩, ?_, ?_⟩
    · rw [mem_auxLocal_iff]
      exact ⟨(m : H), hmu, m.2, rfl⟩
    · have hs : s = ⟨auxProj W m, MulAction.mem_stabilizer_iff.mpr (by
          calc (auxProj W m) • u = m • u := auxProj_smul W m u
            _ = u := Subtype.ext hmu)⟩ := by
        apply Subtype.ext
        exact hm.symm
      rw [hs]
      exact (localPermHom_auxProj_eq hQ u m hmu).symm
  · intro hσ
    rcases Subgroup.mem_map.mp hσ with ⟨τ, hτ, rfl⟩
    rw [mem_auxLocal_iff] at hτ
    obtain ⟨g, hgu, hg, rfl⟩ := hτ
    let m : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0)) := ⟨g, hg⟩
    rw [localGroup, MonoidHom.mem_range]
    refine ⟨⟨auxProj W m, MulAction.mem_stabilizer_iff.mpr ?_⟩, ?_⟩
    · calc (auxProj W m) • u = m • u := auxProj_smul W m u
        _ = u := Subtype.ext hgu
    · exact localPermHom_auxProj_eq hQ u m hgu

private theorem isMultiplyPretransitive_permCongr {α β : Type*} (e : α ≃ β)
    (Y : Subgroup (Equiv.Perm α)) (h : MulAction.IsMultiplyPretransitive Y α 2) :
    MulAction.IsMultiplyPretransitive
      (Subgroup.map (e.permCongrHom : Equiv.Perm α →* Equiv.Perm β) Y) β 2 :=
  (CFSG.BurnsideSchur.isMultiplyPretransitive_map_permCongrHom_iff e Y 2).mpr h

private theorem midOf_comm [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} (h : W.auxI.Adj u v) :
    midOf hQ u v h = midOf hQ v u h.symm := by
  have h1 : midEquiv hQ u ⟨midOf hQ v u h.symm,
      (midOf_adj_right hQ v u h.symm).symm⟩ = ⟨v, h⟩ := by
    simpa using midEquiv_midOf_right hQ (h := h.symm)
  have h2 : midEquiv hQ u ⟨midOf hQ u v h, midOf_adj_left hQ u v h⟩ = ⟨v, h⟩ :=
    midEquiv_midOf hQ u v h
  exact (congrArg Subtype.val ((midEquiv hQ u).injective (h1.trans h2.symm))).symm

private theorem exists_fixed_path_penult [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) {ω : V}
    (hω : Γ.Adj (u : V) ω) :
    ∃ P : GPath Γ 8, P.NoBack ∧ P 0 ∈ auxComp Γ (W.kernelAt 0) (W.x 0) ∧
      P 8 = (u : V) ∧ P 7 = ω ∧
      (∀ i : ℕ, i ≤ 8 → ∀ h ∈ W.kernelAt 0, h • P i = P i) := by
  classical
  let z : {v // W.auxI.Adj u v} := midEquiv hQ u ⟨ω, hω⟩
  let p3 : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) := z.1
  have h3u : W.auxI.Adj p3 u := z.2.symm
  obtain ⟨p2, h32, h2u⟩ := exists_auxI_adj_ne hQ h3u
  obtain ⟨p1, h21, h1p3⟩ := exists_auxI_adj_ne hQ h32.symm
  obtain ⟨p0, h10, h0p2⟩ := exists_auxI_adj_ne hQ h21.symm
  let p : GPath W.auxI 4 :=
    GPath.cons p0 (GPath.cons p1 (GPath.cons p2 (GPath.cons p3 (GPath.nil u) h3u) h32.symm)
      h21.symm) h10.symm
  have hp0 : p 0 = p0 := rfl
  have hp1 : p 1 = p1 := rfl
  have hp2 : p 2 = p2 := rfl
  have hp3 : p 3 = p3 := rfl
  have hp4 : p 4 = u := rfl
  have hp : p.NoBack := by
    intro i hi
    have hi3 : i < 3 := by omega
    interval_cases i
    · rw [hp0, hp2]; exact h0p2
    · rw [hp1, hp3]; exact h1p3
    · rw [hp2, hp4]; exact h2u
  obtain ⟨P, hPnb, hP2, hPodd, hPfix⟩ := exists_lift hQ p hp
  refine ⟨P, hPnb, ?_, ?_, ?_, hPfix⟩
  · rw [hP2 0 (by omega)]
    exact (p 0).2
  · rw [← hp4]
    exact hP2 4 le_rfl
  · have h34 : W.auxI.Adj (p 3) (p 4) := p.adj 3 (by omega)
    have hP7 : P 7 = midOf hQ (p 3) (p 4) h34 := by
      have h := hPodd 3 (by omega); simpa using h
    have h34' : W.auxI.Adj p3 u := by simpa [hp3, hp4] using h34
    have hP7' : P 7 = midOf hQ p3 u h34' := by simpa [hp3, hp4] using hP7
    rw [hP7', midOf_comm hQ h34']
    have hsymm : midOf hQ u p3 h34'.symm = ω := by
      have h1 : midEquiv hQ u ⟨midOf hQ u p3 h34'.symm,
          midOf_adj_left hQ u p3 h34'.symm⟩ = ⟨p3, h34'.symm⟩ :=
        midEquiv_midOf hQ u p3 h34'.symm
      have h2 : midEquiv hQ u ⟨ω, hω⟩ = ⟨p3, h34'.symm⟩ := by
        apply Subtype.ext
        simp only [p3, z]
      exact congrArg Subtype.val ((midEquiv hQ u).injective (h1.trans h2.symm))
    exact hsymm

private theorem pathRootGroup_le_auxGroup [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} {P : GPath Γ 8}
    (hPnb : P.NoBack) (hP0 : P 0 ∈ auxComp Γ (W.kernelAt 0) (W.x 0))
    (hP8 : P 8 = (u : V))
    (hPfix : ∀ i : ℕ, i ≤ 8 → ∀ h ∈ W.kernelAt 0, h • P i = P i) :
    pathRootGroup H Γ P ≤
      auxGroup Γ (W.kernelAt 0) (W.x 0) ⊓ MulAction.stabilizer H (u : V) := by
  intro g hg
  have hgfix := smul_path_eq_self_of_mem_pathRootGroup (by norm_num : 3 ≤ 8) hg
  have hcomm : ∀ k ∈ W.kernelAt 0, g * k = k * g := by
    intro k hk
    have hgmem : k ∈ fixingSubgroup H (Γ.neighborSet (P 0)) ⊓ GPath.stabPath (H := H) P := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact mem_auxSet_of_mem_auxComp (self_mem_auxSet W) hP0 hk
      · rw [GPath.mem_stabPath_iff]
        exact fun i hi => hPfix i hi k hk
    exact (commute_of_mem_fixingSubgroup_inf_stabPath (by norm_num : 2 ≤ 8) hQ.weissFree
      hPnb hgmem hg).symm
  have hnorm : g ∈ Subgroup.normalizer ((W.kernelAt 0) : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [hcomm k hk]
      simpa using hk
    · intro hk
      have h2 := hcomm (g * k * g⁻¹) hk
      have h3 : g * k * g⁻¹ = k := by
        have h4 : g * (g * k * g⁻¹) = g * k := by rw [h2]; group
        exact mul_left_cancel h4
      rw [← h3]
      exact hk
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact mem_auxGroup_of_normalizes_of_fixes_mem hnorm hP0 (hgfix 0 (by omega))
  · rw [MulAction.mem_stabilizer_iff, ← hP8]
    exact hgfix 8 (by omega)

private theorem isMultiplyPretransitive_of_root_subgroups {Ω : Type*} [Nonempty Ω]
    (Y R R' : Subgroup (Equiv.Perm Ω)) (hR : R ≤ Y) (hR' : R' ≤ Y)
    {ω ω' : Ω} (hne : ω ≠ ω') (h3 : ∃ x : Ω, x ≠ ω ∧ x ≠ ω')
    (hRfix : ∀ r ∈ R, r ω = ω) (hR'fix : ∀ r ∈ R', r ω' = ω')
    (hRtrans : ∀ a b : Ω, a ≠ ω → b ≠ ω → ∃ r ∈ R, r a = b)
    (hR'trans : ∀ a b : Ω, a ≠ ω' → b ≠ ω' → ∃ r ∈ R', r a = b) :
    MulAction.IsMultiplyPretransitive Y Ω 2 := by
  classical
  have horb : ∀ b : Ω, ∃ y : Y, (y : Equiv.Perm Ω) ω = b := by
    intro b
    by_cases hb : b = ω'
    · subst b
      obtain ⟨x, hxω, hxω'⟩ := h3
      obtain ⟨r, hrR, hr⟩ := hRtrans x ω' hxω hne.symm
      obtain ⟨s, hsR, hs⟩ := hR'trans ω x hne hxω'
      refine ⟨⟨r * s, mul_mem (hR hrR) (hR' hsR)⟩, ?_⟩
      change r (s ω) = ω'
      rw [hs, hr]
    · obtain ⟨r, hrR, hr⟩ := hR'trans ω b hne hb
      exact ⟨⟨r, hR' hrR⟩, hr⟩
  have htrans : MulAction.IsPretransitive Y Ω := by
    constructor
    intro a b
    obtain ⟨y1, hy1⟩ := horb a
    obtain ⟨y2, hy2⟩ := horb b
    refine ⟨y2 * y1⁻¹, ?_⟩
    change (y2 : Equiv.Perm Ω) ((y1 : Equiv.Perm Ω)⁻¹ a) = b
    have hy1' : (y1 : Equiv.Perm Ω)⁻¹ a = ω := by
      rw [← hy1]
      exact Equiv.symm_apply_apply (y1 : Equiv.Perm Ω) ω
    rw [hy1']
    exact hy2
  have hstab : MulAction.IsPretransitive (MulAction.stabilizer Y ω)
      (SubMulAction.ofStabilizer Y ω) := by
    constructor
    intro a b
    obtain ⟨r, hrR, hr⟩ := hRtrans a.1 b.1 a.2 b.2
    refine ⟨⟨⟨r, hR hrR⟩, MulAction.mem_stabilizer_iff.mpr (hRfix r hrR)⟩, ?_⟩
    apply Subtype.ext
    exact hr
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (G := Y) (a := ω) (n := 1)).mpr
    (MulAction.is_one_pretransitive_iff.mpr hstab)

private theorem auxLocal_twoTransitive [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    MulAction.IsMultiplyPretransitive (auxLocal hQ u) {y : V // Γ.Adj (u : V) y} 2 := by
  classical
  let Ω := {y : V // Γ.Adj (u : V) y}
  let π : ↥(MulAction.stabilizer H (u : V)) →* Equiv.Perm Ω := localPermHom (H := H) Γ (u : V)
  obtain ⟨p, hp0, hp⟩ := exists_auxI_path hQ u
  have hz : W.auxI.Adj u (p 1) := by
    rw [← hp0]; exact p.adj 0 (by omega)
  let ω0 : V := midOf hQ u (p 1) hz
  have hω0 : Γ.Adj (u : V) ω0 := midOf_adj_left hQ u (p 1) hz
  obtain ⟨ω1, hω1, hω10⟩ := hQ.ne (u : V) ω0 hω0
  obtain ⟨P0, hP0nb, hP0mem, hP08, hP07, hP0fix⟩ :=
    exists_fixed_path_penult hQ u hω0
  obtain ⟨P1, hP1nb, hP1mem, hP18, hP17, hP1fix⟩ :=
    exists_fixed_path_penult hQ u hω1
  have hR0le := pathRootGroup_le_auxGroup hQ hP0nb hP0mem hP08 hP0fix
  have hR1le := pathRootGroup_le_auxGroup hQ hP1nb hP1mem hP18 hP1fix
  let R0' : Subgroup (Equiv.Perm Ω) :=
    (pathRootGroup H Γ P0).subgroupOf (MulAction.stabilizer H (u : V)) |>.map π
  let R1' : Subgroup (Equiv.Perm Ω) :=
    (pathRootGroup H Γ P1).subgroupOf (MulAction.stabilizer H (u : V)) |>.map π
  have hR0'sub : R0' ≤ auxLocal hQ u := by
    rintro _ ⟨⟨g, hg⟩, hgR, rfl⟩
    rw [mem_auxLocal_iff]
    exact ⟨g, hg, (hR0le (Subgroup.mem_subgroupOf.mp hgR)).1, rfl⟩
  have hR1'sub : R1' ≤ auxLocal hQ u := by
    rintro _ ⟨⟨g, hg⟩, hgR, rfl⟩
    rw [mem_auxLocal_iff]
    exact ⟨g, hg, (hR1le (Subgroup.mem_subgroupOf.mp hgR)).1, rfl⟩
  have hR0'fix : ∀ r ∈ R0', r ⟨ω0, hω0⟩ = ⟨ω0, hω0⟩ := by
    rintro _ ⟨⟨g, hg⟩, hgR, rfl⟩
    have hgR0 : g ∈ pathRootGroup H Γ P0 := Subgroup.mem_subgroupOf.mp hgR
    have hfix := smul_path_eq_self_of_mem_pathRootGroup (by norm_num : 3 ≤ 8) hgR0 7 (by omega)
    rw [hP07] at hfix
    apply Subtype.ext
    change (g : H) • ω0 = ω0
    exact hfix
  have hR1'fix : ∀ r ∈ R1', r ⟨ω1, hω1⟩ = ⟨ω1, hω1⟩ := by
    rintro _ ⟨⟨g, hg⟩, hgR, rfl⟩
    have hgR1 : g ∈ pathRootGroup H Γ P1 := Subgroup.mem_subgroupOf.mp hgR
    have hfix := smul_path_eq_self_of_mem_pathRootGroup (by norm_num : 3 ≤ 8) hgR1 7 (by omega)
    rw [hP17] at hfix
    apply Subtype.ext
    change (g : H) • ω1 = ω1
    exact hfix
  have hroot0 := isRootAt_pathRootGroup (n := 8) (by norm_num) hQ.moufang hQ.weissFree
    hQ.ne hQ.val (fun z => (hQ.localFacts z).kernel_le) hP0nb
  rw [hP08, hP07] at hroot0
  have hroot1 := isRootAt_pathRootGroup (n := 8) (by norm_num) hQ.moufang hQ.weissFree
    hQ.ne hQ.val (fun z => (hQ.localFacts z).kernel_le) hP1nb
  rw [hP18, hP17] at hroot1
  have hR0'trans : ∀ a b : Ω, a ≠ ⟨ω0, hω0⟩ → b ≠ ⟨ω0, hω0⟩ →
      ∃ r ∈ R0', r a = b := by
    intro a b ha hb
    obtain ⟨g, hgR, hgab⟩ := hroot0.2.2.1 a.1 b.1 a.2 b.2
      (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
    have hgstab : g ∈ MulAction.stabilizer H (u : V) := (hR0le hgR).2
    refine ⟨π ⟨g, hgstab⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨g, hgstab⟩,
        Subgroup.mem_subgroupOf.mpr (by simpa using hgR), rfl⟩
    · apply Subtype.ext
      change (g : H) • a.1 = b.1
      exact hgab
  have hR1'trans : ∀ a b : Ω, a ≠ ⟨ω1, hω1⟩ → b ≠ ⟨ω1, hω1⟩ →
      ∃ r ∈ R1', r a = b := by
    intro a b ha hb
    obtain ⟨g, hgR, hgab⟩ := hroot1.2.2.1 a.1 b.1 a.2 b.2
      (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
    have hgstab : g ∈ MulAction.stabilizer H (u : V) := (hR1le hgR).2
    refine ⟨π ⟨g, hgstab⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨g, hgstab⟩,
        Subgroup.mem_subgroupOf.mpr (by simpa using hgR), rfl⟩
    · apply Subtype.ext
      change (g : H) • a.1 = b.1
      exact hgab
  have h3 : ∃ x : Ω, x ≠ ⟨ω0, hω0⟩ ∧ x ≠ ⟨ω1, hω1⟩ := by
    obtain ⟨x, hx, hx0, hx1⟩ := hQ.three (u : V) ω0 ω1 hω0 hω1
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h),
      fun h => hx1 (congrArg Subtype.val h)⟩
  haveI : Nonempty Ω := ⟨h3.choose⟩
  exact isMultiplyPretransitive_of_root_subgroups (auxLocal hQ u) R0' R1' hR0'sub hR1'sub
    (fun h => hω10 (congrArg Subtype.val h).symm) h3 hR0'fix hR1'fix hR0'trans hR1'trans

private theorem isLocalSz_aux_of_auxLocal [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) {a : ℕ}
    (hcard : Nat.card {y : V // Γ.Adj (u : V) y} = 2 ^ (2 * (2 * a + 1)) + 1)
    (N : Subgroup ↥(localGroup H Γ (u : V)))
    (hN : N.Normal) (hNle : N ≤ (auxLocal hQ u).subgroupOf (localGroup H Γ (u : V)))
    (hNiso : Nonempty (↥N ≃* Sz a)) :
    IsLocalSz ↥W.auxS W.auxI u a := by
  classical
  let e := midEquiv hQ u
  let eh : Equiv.Perm {y : V // Γ.Adj (u : V) y} →*
      Equiv.Perm {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj u v} := e.permCongrHom
  let K' : Subgroup ↥(localGroup H Γ (u : V)) :=
    (auxLocal hQ u).subgroupOf (localGroup H Γ (u : V))
  let E : ↥K' ≃* ↥(auxLocal hQ u |>.map eh) :=
    (Subgroup.subgroupOfEquivOfLe (auxLocal_le_localGroup hQ u)).trans
      (MulEquiv.subgroupMap e.permCongrHom (auxLocal hQ u))
  let N'' : Subgroup ↥(auxLocal hQ u |>.map eh) :=
    (N.subgroupOf K').map E.toMonoidHom
  have hN'' : N''.Normal := (hN.subgroupOf K').map E.toMonoidHom E.surjective
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.card_congr e]
    exact hcard
  · rw [localGroup_aux_eq_auxLocal hQ u]
    exact isMultiplyPretransitive_permCongr e (auxLocal hQ u) (auxLocal_twoTransitive hQ u)
  · rw [localGroup_aux_eq_auxLocal hQ u]
    refine ⟨N'', hN'', ?_⟩
    obtain ⟨eN⟩ := hNiso
    exact ⟨(MulEquiv.subgroupMap E (N.subgroupOf K')).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hNle).trans eN)⟩

private theorem isLocalL2_aux_of_auxLocal [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) {m : ℕ}
    (hcard : Nat.card {y : V // Γ.Adj (u : V) y} = 2 ^ m + 1)
    (N : Subgroup ↥(localGroup H Γ (u : V)))
    (hN : N.Normal) (hNle : N ≤ (auxLocal hQ u).subgroupOf (localGroup H Γ (u : V)))
    (hNiso : Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m))) :
    IsLocalL2 ↥W.auxS W.auxI u m := by
  classical
  let e := midEquiv hQ u
  let eh : Equiv.Perm {y : V // Γ.Adj (u : V) y} →*
      Equiv.Perm {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj u v} := e.permCongrHom
  let K' : Subgroup ↥(localGroup H Γ (u : V)) :=
    (auxLocal hQ u).subgroupOf (localGroup H Γ (u : V))
  let E : ↥K' ≃* ↥(auxLocal hQ u |>.map eh) :=
    (Subgroup.subgroupOfEquivOfLe (auxLocal_le_localGroup hQ u)).trans
      (MulEquiv.subgroupMap e.permCongrHom (auxLocal hQ u))
  let N'' : Subgroup ↥(auxLocal hQ u |>.map eh) :=
    (N.subgroupOf K').map E.toMonoidHom
  have hN'' : N''.Normal := (hN.subgroupOf K').map E.toMonoidHom E.surjective
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.card_congr e]
    exact hcard
  · rw [localGroup_aux_eq_auxLocal hQ u]
    exact isMultiplyPretransitive_permCongr e (auxLocal hQ u) (auxLocal_twoTransitive hQ u)
  · rw [localGroup_aux_eq_auxLocal hQ u]
    refine ⟨N'', hN'', ?_⟩
    obtain ⟨eN⟩ := hNiso
    exact ⟨(MulEquiv.subgroupMap E (N.subgroupOf K')).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hNle).trans eN)⟩

private theorem perfectResidual_le_auxLocal [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥(localGroup H Γ (u : V)) ≤
      (auxLocal hQ u).subgroupOf (localGroup H Γ (u : V)) := by
  classical
  let Gz : Subgroup H := MulAction.stabilizer H (u : V)
  let X : Subgroup (Equiv.Perm {w : V // Γ.Adj (u : V) w}) := localGroup H Γ (u : V)
  let π : Gz →* X := (localPermHom (H := H) Γ (u : V)).rangeRestrict
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective _
  have hmap : (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual Gz).map π =
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual X :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq π hπ
  obtain ⟨p, hp0, hp⟩ := exists_auxI_path hQ u
  have hz : W.auxI.Adj u (p 1) := by
    rw [← hp0]; exact p.adj 0 (by omega)
  let ω0 : V := midOf hQ u (p 1) hz
  have hω0 : Γ.Adj (u : V) ω0 := midOf_adj_left hQ u (p 1) hz
  obtain ⟨ω1, hω1, hω10⟩ := hQ.ne (u : V) ω0 hω0
  obtain ⟨P0, hP0nb, hP0mem, hP08, hP07, hP0fix⟩ :=
    exists_fixed_path_penult hQ u hω0
  obtain ⟨P1, hP1nb, hP1mem, hP18, hP17, hP1fix⟩ :=
    exists_fixed_path_penult hQ u hω1
  have hR0le := pathRootGroup_le_auxGroup hQ hP0nb hP0mem hP08 hP0fix
  have hR1le := pathRootGroup_le_auxGroup hQ hP1nb hP1mem hP18 hP1fix
  have hne : P0 7 ≠ P1 7 := by rw [hP07, hP17]; exact hω10.symm
  have hroot := hQ.rootFacts (u : V)
  have hle := hroot.socle_le P0 P1 hP0nb hP1nb hP08 hP18 hne
  have hA : pathRootGroup H Γ P0 ≤ Gz := hR0le.trans inf_le_right
  have hB : pathRootGroup H Γ P1 ≤ Gz := hR1le.trans inf_le_right
  have hF : fixingSubgroup H (Γ.neighborSet (u : V)) ≤ Gz :=
    (hQ.localFacts (u : V)).kernel_le
  have hAaux : ((pathRootGroup H Γ P0).subgroupOf Gz).map π ≤ (auxLocal hQ u).subgroupOf X := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    rw [mem_auxLocal_iff]
    exact ⟨a.1, a.2, (hR0le (Subgroup.mem_subgroupOf.mp ha)).1, rfl⟩
  have hBaux : ((pathRootGroup H Γ P1).subgroupOf Gz).map π ≤ (auxLocal hQ u).subgroupOf X := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    rw [mem_auxLocal_iff]
    exact ⟨a.1, a.2, (hR1le (Subgroup.mem_subgroupOf.mp ha)).1, rfl⟩
  have hker : π.ker = (fixingSubgroup H (Γ.neighborSet (u : V))).subgroupOf Gz :=
    compatibleQuotient_ker (H := H) (Γ := Γ) (z := (u : V)) π (fun _ _ => rfl)
  have hFaux : ((fixingSubgroup H (Γ.neighborSet (u : V))).subgroupOf Gz).map π = ⊥ := by
    rw [← hker]
    exact Subgroup.map_ker_self π
  have hsocle_map : ((socleAt H Γ (u : V)).subgroupOf Gz).map π ≤ (auxLocal hQ u).subgroupOf X := by
    calc
      ((socleAt H Γ (u : V)).subgroupOf Gz).map π
          ≤ (((pathRootGroup H Γ P0 ⊔ pathRootGroup H Γ P1 ⊔
              fixingSubgroup H (Γ.neighborSet (u : V))).subgroupOf Gz)).map π :=
            Subgroup.map_mono (by
              intro x hx
              exact hle (Subgroup.mem_subgroupOf.mp hx))
      _ ≤ (auxLocal hQ u).subgroupOf X := by
            rw [Subgroup.subgroupOf_sup (sup_le hA hB) hF, Subgroup.subgroupOf_sup hA hB,
              Subgroup.map_sup, Subgroup.map_sup, hFaux, sup_bot_eq]
            exact sup_le hAaux hBaux
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  rw [← hmap] at hx
  obtain ⟨g, hgPR, hgx⟩ := Subgroup.mem_map.mp hx
  have hgGz : (g : H) ∈ MulAction.stabilizer H (u : V) := g.2
  have hgsoc : (g : H) ∈ socleAt H Γ (u : V) := by
    have hmem : (g : H) ∈ CFSG.inSubgroup CFSG.perfectResidual (MulAction.stabilizer H (u : V)) :=
      Subgroup.mem_map_of_mem (MulAction.stabilizer H (u : V)).subtype hgPR
    exact Subgroup.mem_sup_left hmem
  have hx' : x = π ⟨(g : H), hgGz⟩ := hgx.symm
  rw [hx']
  exact hsocle_map (Subgroup.mem_map_of_mem π
    (Subgroup.mem_subgroupOf.mpr hgsoc))

private noncomputable def szWeyl (a : ℕ) : ↥(CFSG.Open.Sz a) :=
  let K := GaloisField 2 (2 * a + 1)
  let W : Matrix (Fin 4) (Fin 4) K := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  have hW : W * W = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [W, Matrix.mul_apply, Fin.sum_univ_four]
  ⟨⟨W, W, hW, hW⟩, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

private theorem szWeyl_sq (a : ℕ) : szWeyl a * szWeyl a = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4)
      (GaloisField 2 (2 * a + 1))) * !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

private theorem szWeyl_ne_one (a : ℕ) : szWeyl a ≠ 1 := by
  intro h
  have hco := congrArg (fun x : ↥(CFSG.Open.Sz a) =>
    (((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) : Matrix (Fin 4) (Fin 4)
      (GaloisField 2 (2 * a + 1))) 0 0)) h
  simp [szWeyl] at hco

private theorem two_dvd_card_sz (a : ℕ) : 2 ∣ Nat.card ↥(CFSG.Open.Sz a) := by
  have h := orderOf_dvd_natCard (szWeyl a)
  have h2 : orderOf (szWeyl a) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using szWeyl_sq a) (szWeyl_ne_one a)
  rwa [h2] at h

private theorem not_isMulCommutative_of_isSimpleGroup_of_two_dvd {G : Type*} [Group G]
    (hsimple : IsSimpleGroup G) (h2 : 2 ∣ Nat.card G) (hgt : 2 < Nat.card G) :
    ¬ IsMulCommutative G := by
  intro _
  have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_two
    (Group.is_simple_iff_prime_card.mp hsimple)).mp h2
  omega

theorem ClosedGoodPath.QuarterHyp.isLocalSz_aux_of_one_le [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {a : ℕ} (ha : 1 ≤ a)
    (hT0 : IsLocalSz H Γ (W.x 0) a) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    IsLocalSz ↥W.auxS W.auxI u a := by
  classical
  obtain ⟨g, hg⟩ := (auxInv_of_mem_auxComp hQ u.2).1
  have hTu : IsLocalSz H Γ (u : V) a := by
    rw [← hg]
    exact isLocalSz_smul hT0 g
  obtain ⟨hcard, h2, N, hN, ⟨eN⟩⟩ := hTu
  haveI : IsSimpleGroup ↥(CFSG.Open.Sz a) :=
    CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup (n := a) ha
  haveI : IsSimpleGroup ↥N := MulEquiv.isSimpleGroup eN
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card ↥N = 1 := by rw [hbot, Subgroup.card_bot]
    have hbig : 64 ≤ Nat.card ↥N := by
      rw [Nat.card_congr eN.toEquiv]
      exact CFSG.Quasithin.H13.sixtyFour_le_card_sz ha
    omega
  have htrans : MulAction.IsPretransitive ↥N {y : V // Γ.Adj (u : V) y} :=
    CFSG.GH74.Uniqueness.Hering.isPretransitive_of_normal h2 N hNne
  have h2dvd : 2 ∣ Nat.card ↥N := by
    rw [Nat.card_congr eN.toEquiv]
    exact two_dvd_card_sz a
  haveI : Nonempty {y : V // Γ.Adj (u : V) y} :=
    Nat.card_pos_iff.mp (by rw [hcard]; positivity) |>.1
  have hdegdvd : Nat.card {y : V // Γ.Adj (u : V) y} ∣ Nat.card ↥N :=
    TauCeti.natCard_dvd_natCard_of_isPretransitive ↥N
  have hlarge : 2 < Nat.card ↥N := by
    have h5 : 5 ≤ Nat.card {y : V // Γ.Adj (u : V) y} := by
      rw [hcard]
      have h4 : 4 ≤ 2 ^ (2 * (2 * a + 1)) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * (2 * a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    haveI : Nonempty ↥N := ⟨⟨1, N.one_mem⟩⟩
    have hNpos : 0 < Nat.card ↥N := Nat.card_pos
    exact lt_of_lt_of_le (by omega) (le_trans h5 (Nat.le_of_dvd hNpos hdegdvd))
  have hnoncomm : ¬ IsMulCommutative ↥N :=
    not_isMulCommutative_of_isSimpleGroup_of_two_dvd inferInstance h2dvd hlarge
  have hperfect : Group.IsPerfect ↥N :=
    Group.IsPerfect.mk (CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup inferInstance hnoncomm)
  have hlePR : N ≤ CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
      ↥(localGroup H Γ (u : V)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual N hperfect
  have hle : N ≤ (auxLocal hQ u).subgroupOf (localGroup H Γ (u : V)) :=
    hlePR.trans (perfectResidual_le_auxLocal hQ u)
  exact isLocalSz_aux_of_auxLocal hQ u hcard N hN hle ⟨eN⟩

private theorem isLocalL2_aux_of_two_le [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {m : ℕ} (hm : 2 ≤ m)
    (hT0 : IsLocalL2 H Γ (W.x 0) m) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    IsLocalL2 ↥W.auxS W.auxI u m := by
  classical
  obtain ⟨g, hg⟩ := (auxInv_of_mem_auxComp hQ u.2).1
  have hTu : IsLocalL2 H Γ (u : V) m := by
    rw [← hg]
    exact isLocalL2_smul hT0 g
  obtain ⟨hcard, h2, N, hN, ⟨eN⟩⟩ := hTu
  have hK : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hF : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  haveI : IsSimpleGroup ↥N := MulEquiv.isSimpleGroup eN
  have h2dvd : 2 ∣ Nat.card ↥N := by
    rw [Nat.card_congr eN.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.Census.two_dvd_card_PSL2 (GaloisField 2 m)
  have hNne : N ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h2dvd
    norm_num at h2dvd
  have htrans : MulAction.IsPretransitive ↥N {y : V // Γ.Adj (u : V) y} :=
    CFSG.GH74.Uniqueness.Hering.isPretransitive_of_normal h2 N hNne
  haveI : Nonempty {y : V // Γ.Adj (u : V) y} :=
    Nat.card_pos_iff.mp (by rw [hcard]; positivity) |>.1
  have hdegdvd : Nat.card {y : V // Γ.Adj (u : V) y} ∣ Nat.card ↥N :=
    TauCeti.natCard_dvd_natCard_of_isPretransitive ↥N
  have hlarge : 2 < Nat.card ↥N := by
    have h5 : 5 ≤ Nat.card {y : V // Γ.Adj (u : V) y} := by
      rw [hcard]
      have : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    haveI : Nonempty ↥N := ⟨⟨1, N.one_mem⟩⟩
    have hNpos : 0 < Nat.card ↥N := Nat.card_pos
    exact lt_of_lt_of_le (by omega) (le_trans h5 (Nat.le_of_dvd hNpos hdegdvd))
  have hnoncomm : ¬ IsMulCommutative ↥N :=
    not_isMulCommutative_of_isSimpleGroup_of_two_dvd inferInstance h2dvd hlarge
  have hperfect : Group.IsPerfect ↥N :=
    Group.IsPerfect.mk (CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup inferInstance hnoncomm)
  have hlePR : N ≤ CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
      ↥(localGroup H Γ (u : V)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual N hperfect
  have hle : N ≤ (auxLocal hQ u).subgroupOf (localGroup H Γ (u : V)) :=
    hlePR.trans (perfectResidual_le_auxLocal hQ u)
  exact isLocalL2_aux_of_auxLocal hQ u hcard N hN hle ⟨eN⟩

private theorem isLocalL2_aux_of_small [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {m : ℕ} (hT0 : IsLocalL2 H Γ (W.x 0) m)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)))
    (hsmall : Nat.card {y : V // Γ.Adj (u : V) y} ≤ 3) :
    IsLocalL2 ↥W.auxS W.auxI u m := by
  classical
  obtain ⟨g, hg⟩ := (auxInv_of_mem_auxComp hQ u.2).1
  have hTu : IsLocalL2 H Γ (u : V) m := by
    rw [← hg]
    exact isLocalL2_smul hT0 g
  obtain ⟨hcard, h2, N, hN, ⟨eN⟩⟩ := hTu
  have hge2 : 2 ≤ Nat.card {y : V // Γ.Adj (u : V) y} := by
    rw [hcard]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  have hXtop : localGroup H Γ (u : V) = ⊤ := by
    haveI : MulAction.IsMultiplyPretransitive ↥(localGroup H Γ (u : V))
        {y : V // Γ.Adj (u : V) y} 2 := h2
    apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
    have hα : (2 : ℕ∞) ≤ ENat.card {y : V // Γ.Adj (u : V) y} := by
      rw [ENat.card_eq_coe_natCard]
      exact_mod_cast hge2
    exact MulAction.isMultiplyPretransitive_of_le'
      (m := Nat.card {y : V // Γ.Adj (u : V) y} - 1) (n := 2) (by omega) hα
  have hYtop : auxLocal hQ u = ⊤ := by
    haveI : MulAction.IsMultiplyPretransitive ↥(auxLocal hQ u)
        {y : V // Γ.Adj (u : V) y} 2 := auxLocal_twoTransitive hQ u
    apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
    have hα : (2 : ℕ∞) ≤ ENat.card {y : V // Γ.Adj (u : V) y} := by
      rw [ENat.card_eq_coe_natCard]
      exact_mod_cast hge2
    exact MulAction.isMultiplyPretransitive_of_le'
      (m := Nat.card {y : V // Γ.Adj (u : V) y} - 1) (n := 2) (by omega) hα
  have hNle : N ≤ (auxLocal hQ u).subgroupOf (localGroup H Γ (u : V)) := by
    simp [hYtop, hXtop]
  exact isLocalL2_aux_of_auxLocal hQ u hcard N hN hNle ⟨eN⟩

theorem ClosedGoodPath.QuarterHyp.isLocalL2_aux [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {m : ℕ} (hT0 : IsLocalL2 H Γ (W.x 0) m)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    IsLocalL2 ↥W.auxS W.auxI u m := by
  classical
  obtain ⟨g, hg⟩ := (auxInv_of_mem_auxComp hQ u.2).1
  have hTu : IsLocalL2 H Γ (u : V) m := by
    rw [← hg]
    exact isLocalL2_smul hT0 g
  by_cases hsmall : Nat.card {y : V // Γ.Adj (u : V) y} ≤ 3
  · exact isLocalL2_aux_of_small hQ hT0 u hsmall
  · have hm2 : 2 ≤ m := by
      by_contra hm
      have hmle : m ≤ 1 := by omega
      have hcard := hTu.1
      have : 2 ^ m ≤ 2 := Nat.pow_le_pow_right (by norm_num) hmle
      have : Nat.card {y : V // Γ.Adj (u : V) y} ≤ 3 := by rw [hcard]; omega
      exact hsmall this
    exact isLocalL2_aux_of_two_le hQ hm2 hT0 u

end CFSG.Quasithin.Stroth.WeissDelta

end

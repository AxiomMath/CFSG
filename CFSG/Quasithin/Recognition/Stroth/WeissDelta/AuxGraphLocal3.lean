module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.AuxGraphLocal2

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

attribute [local instance] auxAction

theorem comap_auxProj_fixingSubgroup [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    (fixingSubgroup ↥W.auxS (W.auxI.neighborSet u)).comap (auxProj W) =
      (auxGroup Γ (W.kernelAt 0) (W.x 0) ⊓
        fixingSubgroup H (Γ.neighborSet (u : V))).subgroupOf
        (auxGroup Γ (W.kernelAt 0) (W.x 0)) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_comap] at hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨g.2, mem_fixingSubgroup_of_fixes_auxI hQ
      (fun v hv => (mem_fixingSubgroup_iff (↥W.auxS)).mp hg v hv)⟩
  · intro hg
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hg
    obtain ⟨-, hgG⟩ := hg
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hgu : (g : H) • (u : V) = (u : V) :=
      MulAction.mem_stabilizer_iff.mp ((hQ.localFacts (u : V)).kernel_le hgG)
    have hm : Γ.Adj (u : V) (midOf hQ u v hv) := midOf_adj_left hQ u v hv
    have hgm : (g : H) • midOf hQ u v hv = midOf hQ u v hv :=
      (mem_fixingSubgroup_iff H).mp hgG _ hm
    have hy' : Γ.Adj (u : V) ((g : H) • midOf hQ u v hv) := by rw [hgm]; exact hm
    have h := step_smul hQ u hm (Subgroup.mem_inf.mp g.2).1 hgu hy'
    rw [step_midOf hQ u v hv] at h
    have h1 : step hQ u ((g : H) • midOf hQ u v hv) hy' = (v : V) := by
      rw [step_congr hQ u hy' hm hgm]
      exact step_midOf hQ u v hv
    apply Subtype.ext
    show (g : H) • (v : V) = (v : V)
    exact (h1.symm.trans h).symm

theorem ClosedGoodPath.QuarterHyp.isPGroup_fixingSubgroup_aux [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    IsPGroup 2 ↥(fixingSubgroup ↥W.auxS (W.auxI.neighborSet u)) := by
  classical
  obtain ⟨p, hp0, hp⟩ := exists_auxI_path hQ u
  obtain ⟨P, hPnb, hP2, hPodd, hPfix⟩ := exists_lift hQ p hp
  have h34 : W.auxI.Adj (p 3) (p 4) := p.adj 3 (by omega)
  obtain ⟨p9, hp9, hp97⟩ := hQ.ne ((p 4) : V) (midOf hQ (p 3) (p 4) h34)
    (midOf_adj_right hQ (p 3) (p 4) h34).symm
  have hP7 : P 7 = midOf hQ (p 3) (p 4) h34 := by
    have h := hPodd 3 (by omega); simpa using h
  have hp97' : p9 ≠ P 7 := by rw [hP7]; exact hp97
  have hP8p9 : Γ.Adj (P 8) p9 := by rw [hP2 4 le_rfl]; exact hp9
  have hKp9 : ∀ k ∈ W.kernelAt 0, k • p9 = p9 := by
    intro k hk
    exact (mem_fixingSubgroup_iff H).mp
      (mem_auxSet_of_mem_auxComp (self_mem_auxSet W) (p 4).2 hk) p9 hp9
  let P9 : GPath Γ 9 := P.snoc p9 hP8p9
  have hP9le : ∀ j : ℕ, j ≤ 8 → P9 j = P j := fun j hj => GPath.snoc_of_le P p9 hP8p9 hj
  have hP9nine : P9 9 = p9 := GPath.snoc_last P p9 hP8p9
  have hP9nb : P9.NoBack := by
    intro i hi
    by_cases h8 : i + 2 ≤ 8
    · rw [hP9le i (by omega), hP9le (i + 2) h8]
      exact hPnb i (by omega)
    · have hi7 : i = 7 := by omega
      subst hi7
      rw [hP9le 7 (by omega), hP9nine]
      exact fun h => hp97' h.symm
  have hP9fix : ∀ j, j ≤ 9 → ∀ k ∈ W.kernelAt 0, k • P9 j = P9 j := by
    intro j hj k hk
    by_cases h9 : j = 9
    · subst h9; rw [hP9nine]; exact hKp9 k hk
    · have hj8 : j < 9 := Nat.lt_of_le_of_ne hj h9
      rw [hP9le j (Nat.lt_succ_iff.mp hj8)]
      exact hPfix j (by omega) k hk
  have hP9zero : P9 0 = ((p 0) : V) := by rw [hP9le 0 (by omega), hP2 0 (by omega)]
  have hfix0 : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) (P9 0) := by
    rw [hP9zero]
    exact (hQ.localFacts ((p 0) : V)).kernel_le
  obtain ⟨e, he⟩ := two_pow_relIndex_stabPath (H := H) (n := 8) (by norm_num) hQ.moufang
    hQ.ne hQ.val hP9nb hfix0
  have hK := kernel_eq_of_fix (H := H) hQ (u := ((p 0) : V)) (p 0).2 hP9nb hP9zero hP9fix
  rw [show P9 0 = ((p 0) : V) from hP9zero] at he
  rw [hK, hp0] at he
  set M := auxGroup Γ (W.kernelAt 0) (W.x 0) with hM
  set A := fixingSubgroup ↥W.auxS (W.auxI.neighborSet u) with hA
  set B : Subgroup H := M ⊓ fixingSubgroup H (Γ.neighborSet (u : V)) with hB
  have hKleM : W.kernelAt 0 ≤ M := by
    refine le_inf Subgroup.le_normalizer ?_
    intro k hk
    rw [MulAction.mem_stabilizer_iff]
    ext v
    constructor
    · intro hv
      rw [Set.mem_smul_set] at hv
      obtain ⟨s, hs, rfl⟩ := hv
      rw [show k • s = s from MulAction.mem_stabilizer_iff.mp
        ((hQ.localFacts s).kernel_le (mem_auxSet_of_mem_auxComp (self_mem_auxSet W) hs hk))]
      exact hs
    · intro hv
      rw [Set.mem_smul_set]
      exact ⟨v, hv, MulAction.mem_stabilizer_iff.mp
        ((hQ.localFacts v).kernel_le (mem_auxSet_of_mem_auxComp (self_mem_auxSet W) hv hk))⟩
  have hKleG : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (u : V)) :=
    mem_auxSet_of_mem_auxComp (self_mem_auxSet W) u.2
  have hKleB : W.kernelAt 0 ≤ B := le_inf hKleM hKleG
  have hBleM : B ≤ M := inf_le_left
  have hBleG : B ≤ fixingSubgroup H (Γ.neighborSet (u : V)) := inf_le_right
  have hsurj : Function.Surjective (auxProj W) := MonoidHom.rangeRestrict_surjective _
  have hcomap : A.comap (auxProj W) = B.subgroupOf M := comap_auxProj_fixingSubgroup hQ u
  have hcard : Nat.card ↥A = (auxProj W).ker.relIndex (B.subgroupOf M) := by
    rw [← hcomap]
    have h := Subgroup.relIndex_ker (A.comap (auxProj W)) (auxProj W)
    rw [Subgroup.map_comap_eq_self_of_surjective hsurj] at h
    exact h.symm
  have hKleker : (W.kernelAt 0).subgroupOf M ≤ (auxProj W).ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro v
    apply Subtype.ext
    show (k : H) • (v : V) = (v : V)
    exact MulAction.mem_stabilizer_iff.mp ((hQ.localFacts (v : V)).kernel_le
      (mem_auxSet_of_mem_auxComp (self_mem_auxSet W) v.2 (Subgroup.mem_subgroupOf.mp hk)))
  have hkerleB : (auxProj W).ker ≤ B.subgroupOf M := by
    intro g hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨g.2, ?_⟩
    refine mem_fixingSubgroup_of_fixes_auxI hQ (g := g) (u := u) (fun v hv => ?_)
    rw [MonoidHom.mem_ker] at hg
    rw [hg, one_smul]
  have hdvd1 : Nat.card ↥A ∣ ((W.kernelAt 0).subgroupOf M).relIndex (B.subgroupOf M) := by
    rw [hcard, ← Subgroup.relIndex_mul_relIndex (H := (W.kernelAt 0).subgroupOf M)
      (K := (auxProj W).ker) (L := B.subgroupOf M) hKleker hkerleB]
    exact dvd_mul_left _ _
  have hsub : ((W.kernelAt 0).subgroupOf M).relIndex (B.subgroupOf M) =
      (W.kernelAt 0).relIndex B :=
    Subgroup.relIndex_subgroupOf (H := W.kernelAt 0) hBleM
  have hstep : (W.kernelAt 0).relIndex (fixingSubgroup H (Γ.neighborSet (u : V))) =
      (W.kernelAt 0).relIndex B * B.relIndex
        (fixingSubgroup H (Γ.neighborSet (u : V))) :=
    (Subgroup.relIndex_mul_relIndex (W.kernelAt 0) B
      (fixingSubgroup H (Γ.neighborSet (u : V))) hKleB hBleG).symm
  have hdvd2 : ((W.kernelAt 0).subgroupOf M).relIndex (B.subgroupOf M) ∣ 2 ^ e := by
    rw [hsub, ← he]
    exact ⟨_, hstep⟩
  have hdvd : Nat.card ↥A ∣ 2 ^ e := dvd_trans hdvd1 hdvd2
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card hn

private noncomputable def punctEquiv [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {v w : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} (hvw : W.auxI.Adj v w) :
    {y : V // Γ.Adj (v : V) y ∧ y ≠ midOf hQ v w hvw} ≃
      {y : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj v y ∧ y ≠ w} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (fun y => Γ.Adj (v : V) y)
    (fun y => y ≠ midOf hQ v w hvw)).symm.trans
    ((Equiv.subtypeEquiv (midEquiv hQ v) (fun y => by
      have hm : midEquiv hQ v ⟨midOf hQ v w hvw, midOf_adj_left hQ v w hvw⟩ = ⟨w, hvw⟩ :=
        midEquiv_midOf hQ v w hvw
      constructor
      · intro hy heq
        apply hy
        have h1 : midEquiv hQ v y = ⟨w, hvw⟩ := Subtype.ext heq
        have h2 : midEquiv hQ v y =
            midEquiv hQ v ⟨midOf hQ v w hvw, midOf_adj_left hQ v w hvw⟩ := by
          rw [hm]; exact h1
        exact congrArg Subtype.val ((midEquiv hQ v).injective h2)
      · intro hy heq
        apply hy
        have h1 : y = ⟨midOf hQ v w hvw, midOf_adj_left hQ v w hvw⟩ := Subtype.ext heq
        rw [h1]
        exact congrArg Subtype.val hm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun y => W.auxI.Adj v y) (fun y => y ≠ w)))

theorem auxI_three [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) :
    ∀ v w w' : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), W.auxI.Adj v w → W.auxI.Adj v w' →
      ∃ u, W.auxI.Adj v u ∧ u ≠ w ∧ u ≠ w' := by
  intro v w w' hvw hvw'
  by_cases hww : w = w'
  · obtain ⟨u, hu, hune⟩ := exists_auxI_adj_ne hQ hvw
    exact ⟨u, hu, hune, by rwa [← hww]⟩
  · have hm : Γ.Adj (v : V) (midOf hQ v w hvw) := midOf_adj_left hQ v w hvw
    have hm' : Γ.Adj (v : V) (midOf hQ v w' hvw') := midOf_adj_left hQ v w' hvw'
    obtain ⟨z, hz, hz1, hz2⟩ := hQ.three (v : V) (midOf hQ v w hvw)
      (midOf hQ v w' hvw') hm hm'
    refine ⟨⟨step hQ v z hz, step_mem hQ v z hz⟩, step_adjI hQ v z hz, ?_, ?_⟩
    · intro heq
      have hstep : step hQ v z hz = (w : V) := by
        have h := congrArg (fun u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) => (u : V)) heq
        simpa using h
      exact hz1 (congrArg Subtype.val (eq_midOf_of_step_eq hQ hvw hz hstep))
    · intro heq
      have hstep : step hQ v z hz = (w' : V) := by
        have h := congrArg (fun u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) => (u : V)) heq
        simpa using h
      exact hz2 (congrArg Subtype.val (eq_midOf_of_step_eq hQ hvw' hz hstep))

theorem ClosedGoodPath.QuarterHyp.aux_local [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) :
    (∀ v w, W.auxI.Adj v w → ∃ u, W.auxI.Adj v u ∧ u ≠ w) ∧
    (∀ v w w', W.auxI.Adj v w → W.auxI.Adj v w' → ∃ u, W.auxI.Adj v u ∧ u ≠ w ∧ u ≠ w') ∧
    (∀ v w, W.auxI.Adj v w → ∃ e : ℕ, Nat.card {y // W.auxI.Adj v y ∧ y ≠ w} = 2 ^ e) ∧
    (∀ w u v, W.auxI.Adj w u → W.auxI.Adj w v → ∃ g : ↥W.auxS, g • w = w ∧ g • u = v) ∧
    ∀ u, FixingNeighbourhoodFixesVertex (H := ↥W.auxS) (Γ := W.auxI) u := by
  classical
  refine ⟨fun v w hvw => exists_auxI_adj_ne hQ hvw, ?_, ?_, ?_, ?_⟩
  · intro v w w' hvw hvw'
    exact auxI_three hQ v w w' hvw hvw'
  · intro v w hvw
    obtain ⟨e, he⟩ := hQ.val (v : V) (midOf hQ v w hvw) (midOf_adj_left hQ v w hvw)
    exact ⟨e, (Nat.card_congr (punctEquiv hQ hvw)).symm.trans he⟩
  · intro w u v hwu hwv
    obtain ⟨x, hwx, hxu, hxv⟩ := auxI_three hQ w u v hwu hwv
    obtain ⟨p2, hx2, h2w⟩ := exists_auxI_adj_ne hQ hwx.symm
    obtain ⟨p1, hp12, hp1x⟩ := exists_auxI_adj_ne hQ hx2.symm
    obtain ⟨p0, hp01, hp0p2⟩ := exists_auxI_adj_ne hQ hp12.symm
    let pI : GPath W.auxI 4 :=
      GPath.cons p0 (GPath.cons p1 (GPath.cons p2 (GPath.cons x (GPath.nil w) hwx.symm)
        hx2.symm) hp12.symm) hp01.symm
    have hP0 : pI 0 = p0 := rfl
    have hP1 : pI 1 = p1 := rfl
    have hP2 : pI 2 = p2 := rfl
    have hP3 : pI 3 = x := rfl
    have hP4 : pI 4 = w := rfl
    have hpI : pI.NoBack := by
      intro i hi
      have hi3 : i < 3 := by omega
      interval_cases i
      · rw [hP0, hP2]; exact hp0p2
      · rw [hP1, hP3]; exact hp1x
      · rw [hP2, hP4]; exact h2w
    have hu4 : W.auxI.Adj (pI 4) u := by rw [hP4]; exact hwu
    have hv4 : W.auxI.Adj (pI 4) v := by rw [hP4]; exact hwv
    have hux : u ≠ pI 3 := by rw [hP3]; exact hxu.symm
    have hvx : v ≠ pI 3 := by rw [hP3]; exact hxv.symm
    obtain ⟨σ, hσfix, hσuv⟩ := hQ.moufangCondition_aux pI hpI u v hu4 hv4 hux hvx
    exact ⟨σ, hσfix 3 (by norm_num) (by norm_num) w (by rw [hP3]; exact hwx.symm), hσuv⟩
  · intro u h hh
    rw [MulAction.mem_stabilizer_iff]
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp h.2
    have hgeq : auxProj W g = h := Subtype.ext hg
    have hfix : (g : H) ∈ fixingSubgroup H (Γ.neighborSet (u : V)) :=
      mem_fixingSubgroup_of_fixes_auxI hQ
        (fun v hv => by rw [hgeq]; exact (mem_fixingSubgroup_iff (↥W.auxS)).mp hh v hv)
    rw [← hgeq]
    apply Subtype.ext
    show (g : H) • (u : V) = (u : V)
    exact MulAction.mem_stabilizer_iff.mp ((hQ.localFacts (u : V)).kernel_le hfix)

end CFSG.Quasithin.Stroth.WeissDelta

end

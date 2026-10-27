module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitFactor
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

@[expose] def K329Res {H : Type} [Group H] (C : Subgroup H) : Subgroup H :=
  (CFSG.perfectResidual ↥C).map C.subtype

@[expose] def K329Lres {H : Type} [Group H] (x : H) : Subgroup H :=
  K329Res (Subgroup.centralizer ({x} : Set H))

theorem k329_res_map {H H' : Type} [Group H] [Group H'] [Finite H] (f : H →* H')
    (C : Subgroup H) : (K329Res C).map f = K329Res (C.map f) := by
  have hres : ∀ (G : Type) [Group G] [Finite G], ∃ n, CFSG.perfectResidual G = derivedSeries G n :=
    fun G _ _ => CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_derivedSeries
  have hsurj : Function.Surjective (f.subgroupMap C) := f.subgroupMap_surjective C
  have h : (CFSG.perfectResidual ↥C).map (f.subgroupMap C) =
      CFSG.perfectResidual ↥(C.map f) := by
    apply le_antisymm
    · apply le_iInf
      intro n
      exact (Subgroup.map_mono (iInf_le _ n)).trans
        (map_derivedSeries_le_derivedSeries (f.subgroupMap C) n)
    · obtain ⟨n, hn⟩ := hres ↥C
      have hbound := derivedSeries_le_map_derivedSeries hsurj n
      rw [← hn] at hbound
      exact (iInf_le _ n).trans hbound
  have e : (C.map f).subtype.comp (f.subgroupMap C) = f.comp C.subtype := by
    ext x
    rfl
  calc (K329Res C).map f = (CFSG.perfectResidual ↥C).map (f.comp C.subtype) := by
        show ((CFSG.perfectResidual ↥C).map C.subtype).map f = _
        rw [Subgroup.map_map]
    _ = (CFSG.perfectResidual ↥C).map ((C.map f).subtype.comp (f.subgroupMap C)) := by rw [e]
    _ = ((CFSG.perfectResidual ↥C).map (f.subgroupMap C)).map (C.map f).subtype := by
        rw [Subgroup.map_map]
    _ = K329Res (C.map f) := congrArg (Subgroup.map (C.map f).subtype) h

theorem k329_perfect_le_res {H : Type} [Group H] {C P : Subgroup H} (hPC : P ≤ C)
    (hP : ⁅P, P⁆ = P) : P ≤ K329Res C := by
  have hP' : ⁅P.subgroupOf C, P.subgroupOf C⁆ = P.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC, hP]
  have key : ∀ n : ℕ, P.subgroupOf C ≤ derivedSeries C n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc P.subgroupOf C = ⁅P.subgroupOf C, P.subgroupOf C⁆ := hP'.symm
        _ ≤ ⁅derivedSeries C n, derivedSeries C n⁆ := Subgroup.commutator_mono ih ih
  intro x hx
  refine ⟨⟨x, hPC hx⟩, ?_, rfl⟩
  show (⟨x, hPC hx⟩ : C) ∈ ⨅ n : ℕ, derivedSeries C n
  rw [Subgroup.mem_iInf]
  intro n
  exact key n (Subgroup.mem_subgroupOf.2 hx)

theorem k329_res_le_commutator {H : Type} [Group H] (C : Subgroup H) : K329Res C ≤ ⁅C, C⁆ := by
  have h1 : CFSG.perfectResidual ↥C ≤ derivedSeries ↥C 1 := iInf_le _ 1
  have h2 : (derivedSeries ↥C 1).map C.subtype = ⁅C, C⁆ := by
    rw [derivedSeries_one, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  calc K329Res C = (CFSG.perfectResidual ↥C).map C.subtype := rfl
    _ ≤ (derivedSeries ↥C 1).map C.subtype := Subgroup.map_mono h1
    _ = ⁅C, C⁆ := h2

theorem k329_res_perfect {H : Type} [Group H] [Finite H] (C : Subgroup H) :
    ⁅K329Res C, K329Res C⁆ = K329Res C :=
  Subgroup.isPerfect_iff.1
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect C)

theorem k329_res_eq_of_commutator_le {H : Type} [Group H] [Finite H] {C M : Subgroup H}
    (hMC : M ≤ C) (hM : ⁅C, C⁆ ≤ M) : K329Res C = K329Res M :=
  le_antisymm (k329_perfect_le_res ((k329_res_le_commutator C).trans hM) (k329_res_perfect C))
    (k329_perfect_le_res ((Subgroup.map_subtype_le _).trans hMC) (k329_res_perfect M))

theorem k329_res_normal {H : Type} [Group H] {C D : Subgroup H} (hCD : C ≤ D)
    (hn : (C.subgroupOf D).Normal) : ((K329Res C).subgroupOf D).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer ((Subgroup.map_subtype_le _).trans hCD)).2
    (((Subgroup.normal_subgroupOf_iff_le_normalizer hCD).1 hn).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains C))

theorem k329_res_lift_preimage {H : Type} [Group H] (Z : Subgroup H) [Z.Normal]
    (L : Subgroup H) (Yb : Subgroup (H ⧸ Z)) (hYL : Yb ≤ L.map (QuotientGroup.mk' Z))
    (hYn : (Yb.subgroupOf (L.map (QuotientGroup.mk' Z))).Normal) :
    ∃ P : Subgroup H, P ≤ L ∧ (P.subgroupOf L).Normal ∧ P.map (QuotientGroup.mk' Z) = Yb := by
  refine ⟨L ⊓ Yb.comap (QuotientGroup.mk' Z), inf_le_left, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    refine ⟨L.mul_mem (L.mul_mem hk hh.1) (L.inv_mem hk), ?_⟩
    refine Subgroup.mem_comap.2 ?_
    have hh' : (QuotientGroup.mk' Z) h ∈ Yb := Subgroup.mem_comap.1 hh.2
    have hk' : (QuotientGroup.mk' Z) k ∈ L.map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map.2 ⟨k, hk, rfl⟩
    have hconj := (Subgroup.normal_subgroupOf_iff hYL).1 hYn
      ((QuotientGroup.mk' Z) h) ((QuotientGroup.mk' Z) k) hh' hk'
    simpa only [map_mul, map_inv] using hconj
  · apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_comap.1 hx.2
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 (hYL hy)
      exact Subgroup.mem_map.2 ⟨l, ⟨hl, Subgroup.mem_comap.2 hy⟩, rfl⟩

private theorem k329pg5_ker_le_center {H : Type} [Group H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (Q : Subgroup H) :
    ((QuotientGroup.mk' Z).subgroupMap Q).ker ≤ Subgroup.center ↥Q := by
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro y
  have hq1 : (QuotientGroup.mk' Z) (q : H) = 1 := by
    have h := (MonoidHom.mem_ker.1 hq : (QuotientGroup.mk' Z).subgroupMap Q q = 1)
    exact congrArg Subtype.val h
  have hqZ : (q : H) ∈ Z := (QuotientGroup.eq_one_iff (q : H)).1 hq1
  exact Subtype.ext ((Subgroup.mem_center_iff.1 (hZ hqZ)) (y : H))

private theorem k329pg5_center_eq_ker {H : Type} [Group H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (Q : Subgroup H) (hQ : ⁅Q, Q⁆ = Q)
    (hs : IsSimpleGroup ↥(Q.map (QuotientGroup.mk' Z)))
    (hna : ∃ a ∈ Q.map (QuotientGroup.mk' Z), ∃ b ∈ Q.map (QuotientGroup.mk' Z),
      a * b ≠ b * a) :
    Subgroup.center ↥Q = ((QuotientGroup.mk' Z).subgroupMap Q).ker := by
  have hP : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQ
  have hf : Function.Surjective ((QuotientGroup.mk' Z).subgroupMap Q) :=
    (QuotientGroup.mk' Z).subgroupMap_surjective Q
  have hker := k329pg5_ker_le_center Z hZ Q
  have hna' : ∃ a b : ↥(Q.map (QuotientGroup.mk' Z)), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hcenter : Subgroup.center ↥(Q.map (QuotientGroup.mk' Z)) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna').2
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hP
    ((QuotientGroup.mk' Z).subgroupMap Q) hf hker
  rw [hcenter, MonoidHom.comap_bot] at hcomap
  exact hcomap.symm

theorem k329_quasisimple_of_central_quotient {H : Type} [Group H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (Q : Subgroup H) (hQ : ⁅Q, Q⁆ = Q)
    (hs : IsSimpleGroup ↥(Q.map (QuotientGroup.mk' Z)))
    (hna : ∃ a ∈ Q.map (QuotientGroup.mk' Z), ∃ b ∈ Q.map (QuotientGroup.mk' Z),
      a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple ↥Q ∧
      Nat.card (↥Q ⧸ Subgroup.center ↥Q) = Nat.card ↥(Q.map (QuotientGroup.mk' Z)) := by
  let f : ↥Q →* ↥(Q.map (QuotientGroup.mk' Z)) := (QuotientGroup.mk' Z).subgroupMap Q
  have hf : Function.Surjective f := (QuotientGroup.mk' Z).subgroupMap_surjective Q
  have hP : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQ
  have hker : f.ker ≤ Subgroup.center ↥Q := k329pg5_ker_le_center Z hZ Q
  have hcenter_eq : Subgroup.center ↥Q = f.ker := k329pg5_center_eq_ker Z hZ Q hQ hs hna
  have hna' : ∃ a b : ↥(Q.map (QuotientGroup.mk' Z)), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hq' : CFSG.IsQuasisimple ↥(Q.map (QuotientGroup.mk' Z)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna').1
  have hQq : CFSG.IsQuasisimple ↥Q :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hP f hf hker).mpr hq'
  refine ⟨⟨Group.isPerfect_def.mp hQq.1, hQq.2.1⟩, ?_⟩
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcenter_eq).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)).toEquiv

theorem k329_res_lift {H : Type} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (L : Subgroup H) (Yb : Subgroup (H ⧸ Z))
    (hYL : Yb ≤ L.map (QuotientGroup.mk' Z))
    (hYn : (Yb.subgroupOf (L.map (QuotientGroup.mk' Z))).Normal)
    (hYs : IsSimpleGroup ↥Yb) (hYna : ∃ a ∈ Yb, ∃ b ∈ Yb, a * b ≠ b * a) :
    ∃ Q : Subgroup H, Q ≤ L ∧ (Q.subgroupOf L).Normal ∧ CFSG.Open.IsQuasisimple ↥Q ∧
      Nat.card (↥Q ⧸ Subgroup.center ↥Q) = Nat.card ↥Yb := by
  obtain ⟨P, hPL, hPn, hPmap⟩ := k329_res_lift_preimage Z L Yb hYL hYn
  have hYperf : ⁅Yb, Yb⁆ = Yb := by
    have hna : ∃ a b : ↥Yb, a * b ≠ b * a := by
      obtain ⟨a, ha, b, hb, hab⟩ := hYna
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
    exact Subgroup.isPerfect_iff.1 ⟨(k329_quasisimple_of_simple_nonabelian hYs hna).1⟩
  have hQmap : (K329Res P).map (QuotientGroup.mk' Z) = Yb := by
    rw [k329_res_map, hPmap]
    exact le_antisymm (Subgroup.map_subtype_le _) (k329_perfect_le_res le_rfl hYperf)
  have hs : IsSimpleGroup ↥((K329Res P).map (QuotientGroup.mk' Z)) := by
    rw [hQmap]
    exact hYs
  have hna : ∃ a ∈ (K329Res P).map (QuotientGroup.mk' Z),
      ∃ b ∈ (K329Res P).map (QuotientGroup.mk' Z), a * b ≠ b * a := by
    rw [hQmap]
    exact hYna
  obtain ⟨hq, hcard⟩ := k329_quasisimple_of_central_quotient Z hZ (K329Res P)
    (k329_res_perfect P) hs hna
  refine ⟨K329Res P, (Subgroup.map_subtype_le _).trans hPL, k329_res_normal hPL hPn, hq, ?_⟩
  rw [hcard, hQmap]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

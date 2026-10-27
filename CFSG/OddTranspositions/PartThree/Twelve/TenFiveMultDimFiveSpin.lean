module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultDimFive
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherProjective
public import CFSG.ClassicalInvolution.Asc77.AscC5OM1
public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LieType.Steinberg.CentralExt.POmegaOddMultiplier
public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.ClassicalInvolution.Asc77.AscC25W15

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open

theorem statedScalarsOmegaTwo_subgroupOf_eq_bot :
    (StatedScalars (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)).subgroupOf
      (StatedOmega (StatedQuadOdd 2 (ZMod 5))) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  have hxS : (x : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)) ∈
      StatedScalars (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5) := Subgroup.mem_subgroupOf.mp hx
  have hs : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)
      (x : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)) ∈
      CFSG.ClassicalGroups.Orthogonal.scalars (ZMod 5)
        (Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 5) :=
    (CFSG.ClassicalGroups.Orthogonal.mem_statedScalars_iff _).mp hxS
  have ho : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)
      (x : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)) ∈
      CFSG.RankThree.Classical2.orthDerived
        (CFSG.LieType.Universal.Spin.quadOdd 2 (ZMod 5)) := by
    have h3 : (x : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)) ∈
        (CFSG.RankThree.Classical2.orthDerived
          (CFSG.LieType.Universal.Spin.quadOdd 2 (ZMod 5))).comap
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
            (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)).toMonoidHom := by
      rw [← CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
        (CFSG.LieType.Universal.Spin.coe_quadOdd (n := 2) (K := ZMod 5))]
      exact x.2
    exact Subgroup.mem_comap.mp h3
  have h1 := CFSG.ComponentClassification.HarrisLit.T1.eq_one_of_mem_scalars_quadOdd ho hs
  apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)).injective
  rw [h1]
  exact (map_one (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
    (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5))).symm

@[expose] noncomputable def statedOmegaTwoProjEquiv :
    StatedProj (StatedOmega (StatedQuadOdd 2 (ZMod 5))) ≃*
      ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5))) :=
  (QuotientGroup.quotientMulEquivOfEq statedScalarsOmegaTwo_subgroupOf_eq_bot).trans
    QuotientGroup.quotientBot

@[expose] noncomputable def spTwoProj :
    ↥(StatedSp 2 (ZMod 5)) →* StatedProj (StatedSp 2 (ZMod 5)) :=
  QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5)))

@[expose] noncomputable def spTwoSigma :
    ↥(StatedSp 2 (ZMod 5)) →* StatedProj (StatedOmega (StatedQuadOdd 2 (ZMod 5))) :=
  statedProjQuadOddTwoEquiv.symm.toMonoidHom.comp spTwoProj

@[expose] noncomputable def spTwoOmega :
    ↥(StatedSp 2 (ZMod 5)) →* ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5))) :=
  statedOmegaTwoProjEquiv.toMonoidHom.comp spTwoSigma

@[expose] noncomputable def spTwoNegOne : ↥(StatedSp 2 (ZMod 5)) :=
  CFSG.ClassicalInvolution.Asc77.C5O.M.negOne (ZMod 5)

theorem spScalars_two_eq_zpowers_negOne :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 (ZMod 5) =
      Subgroup.zpowers (CFSG.ClassicalInvolution.Asc77.C5O.M.negOne (ZMod 5)) := by
  apply le_antisymm
  · intro x hx
    rcases CFSG.ClassicalInvolution.Asc77.C5O.M.mem_spScalars_iff.mp hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact CFSG.ClassicalInvolution.Asc77.C5O.M.negOne_mem_spScalars

theorem spTwoNegOne_ne_one : spTwoNegOne ≠ 1 := by
  exact CFSG.ClassicalInvolution.Asc77.C5O.M.negOne_ne_one (by decide)

theorem spTwoNegOne_mul_self : spTwoNegOne * spTwoNegOne = 1 :=
  CFSG.ClassicalInvolution.Asc77.C5O.M.negOne_mul_self

theorem spTwoProj_spTwoNegOne : spTwoProj spTwoNegOne = 1 :=
  MonoidHom.mem_ker.mp (by
    rw [show spTwoProj.ker =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 (ZMod 5)
        from QuotientGroup.ker_mk' _]
    exact CFSG.ClassicalInvolution.Asc77.C5O.M.negOne_mem_spScalars)

theorem spTwoSigma_ker_eq_spScalars :
    spTwoSigma.ker = CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 (ZMod 5) := by
  have hsig : spTwoSigma.ker = spTwoProj.ker := by
    ext u
    simp only [MonoidHom.mem_ker, spTwoSigma, MonoidHom.comp_apply]
    exact map_eq_one_iff statedProjQuadOddTwoEquiv.symm statedProjQuadOddTwoEquiv.symm.injective
  rw [hsig]
  exact QuotientGroup.ker_mk' _

theorem spTwoOmega_ker : spTwoOmega.ker = Subgroup.zpowers spTwoNegOne := by
  have h1 : spTwoOmega.ker = spTwoSigma.ker := by
    ext u
    simp only [MonoidHom.mem_ker, spTwoOmega, MonoidHom.comp_apply]
    exact map_eq_one_iff statedOmegaTwoProjEquiv statedOmegaTwoProjEquiv.injective
  rw [h1, spTwoSigma_ker_eq_spScalars, spScalars_two_eq_zpowers_negOne]
  rfl

theorem spTwoOmega_ker_eq_spScalars :
    spTwoOmega.ker = CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 (ZMod 5) := by
  rw [spTwoOmega_ker, spScalars_two_eq_zpowers_negOne]
  rfl
theorem spTwoSigma_surjective : Function.Surjective spTwoSigma := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5)))
    (statedProjQuadOddTwoEquiv y)
  refine ⟨x, ?_⟩
  simp only [spTwoSigma, spTwoProj, MonoidHom.comp_apply]
  rw [hx]
  exact MulEquiv.symm_apply_apply statedProjQuadOddTwoEquiv y

theorem spTwoOmega_surjective : Function.Surjective spTwoOmega := by
  intro y
  obtain ⟨x, hx⟩ := spTwoSigma_surjective (statedOmegaTwoProjEquiv.symm y)
  refine ⟨x, ?_⟩
  simp only [spTwoOmega, MonoidHom.comp_apply]
  rw [hx]
  exact MulEquiv.apply_symm_apply statedOmegaTwoProjEquiv y

theorem spTwoSigma_ker_le_center : spTwoSigma.ker ≤ Subgroup.center ↥(StatedSp 2 (ZMod 5)) := by
  intro u hu
  rw [spTwoSigma_ker_eq_spScalars] at hu
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center hu

theorem spTwoSigma_ker_card_le_four : Nat.card spTwoSigma.ker ≤ 4 := by
  rw [spTwoSigma_ker_eq_spScalars,
    CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd (ZMod 5) (by norm_num)]
  norm_num [Nat.card_zmod]

theorem statedOmegaTwoProjEquiv_mk (x : ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5)))) :
    statedOmegaTwoProjEquiv
      (QuotientGroup.mk x : StatedProj (StatedOmega (StatedQuadOdd 2 (ZMod 5)))) = x := by
  have hbot_mk : QuotientGroup.quotientBot
      (QuotientGroup.mk x : ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5))) ⧸
        (⊥ : Subgroup ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5))))) = x := by
    rw [← QuotientGroup.quotientBot_symm_apply x]
    exact MulEquiv.apply_symm_apply _ x
  change QuotientGroup.quotientBot (QuotientGroup.quotientMulEquivOfEq
    statedScalarsOmegaTwo_subgroupOf_eq_bot (QuotientGroup.mk x)) = x
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact hbot_mk

theorem spTwoSigma_eq_mk_spTwoOmega (u : ↥(StatedSp 2 (ZMod 5))) :
    spTwoSigma u = QuotientGroup.mk (spTwoOmega u) := by
  have h1 := statedOmegaTwoProjEquiv_mk (spTwoOmega u)
  have h2 : statedOmegaTwoProjEquiv (QuotientGroup.mk (spTwoOmega u)) =
      statedOmegaTwoProjEquiv (spTwoSigma u) := by
    rw [h1]
    rfl
  exact (statedOmegaTwoProjEquiv.injective h2).symm

@[expose] def ReflPairInvariant {G : Type*} [Group G] (x : G) : Prop :=
  ∃ y : G, IsConj y x ∧ Commute y x ∧ IsConj (x * y) x

theorem reflPairInvariant_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    ReflPairInvariant (e x) ↔ ReflPairInvariant x := by
  have hconj : ∀ a b : G, IsConj a b ↔ IsConj (e a) (e b) := by
    intro a b
    rw [isConj_iff, isConj_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨e c, by simpa only [map_mul, map_inv] using congrArg e hc⟩
    · rintro ⟨c, hc⟩
      refine ⟨e.symm c, ?_⟩
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hc
  have hcomm : ∀ a b : G, Commute (e a) (e b) ↔ Commute a b := by
    intro a b
    rw [commute_iff_eq, commute_iff_eq]
    constructor
    · intro h
      exact e.injective (by rw [map_mul, map_mul]; exact h)
    · intro h
      simpa only [map_mul] using congrArg e h
  constructor
  · rintro ⟨y, hy, hc, hxy⟩
    refine ⟨e.symm y, ?_, ?_, ?_⟩
    · rw [hconj (e.symm y) x, MulEquiv.apply_symm_apply]
      exact hy
    · rw [← hcomm (e.symm y) x, MulEquiv.apply_symm_apply]
      exact hc
    · rw [hconj (x * e.symm y) x, map_mul, MulEquiv.apply_symm_apply]
      exact hxy
  · rintro ⟨y, hy, hc, hxy⟩
    exact ⟨e y, (hconj y x).mp hy, (hcomm y x).mpr hc,
      by simpa only [map_mul] using (hconj (x * y) x).mp hxy⟩

theorem spTwoNegOne_comm (w : ↥(StatedSp 2 (ZMod 5))) :
    spTwoNegOne * w = w * spTwoNegOne :=
  CFSG.ClassicalInvolution.Asc77.C5O.M.negOne_comm w

theorem spTwoNegOne_eq_negOne :
    (spTwoNegOne : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1 :=
  Units.ext (CFSG.ClassicalInvolution.Asc77.C5O.M.mat_negOne)

theorem spTwoProj_eq_one_iff (w : ↥(StatedSp 2 (ZMod 5))) :
    spTwoProj w = 1 ↔ w = 1 ∨ w = spTwoNegOne := by
  rw [← MonoidHom.mem_ker,
    show spTwoProj.ker = CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars
      2 (ZMod 5) from QuotientGroup.ker_mk' _]
  exact CFSG.ClassicalInvolution.Asc77.C5O.M.mem_spScalars_iff

theorem spTwoProj_eq_iff (a b : ↥(StatedSp 2 (ZMod 5))) :
    spTwoProj a = spTwoProj b ↔ a = b ∨ a = b * spTwoNegOne := by
  constructor
  · intro h
    have h1 : spTwoProj (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [spTwoProj_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · left
      rwa [mul_inv_eq_one] at h1
    · right
      have h2 : a = spTwoNegOne * b := by
        have hh := congrArg (fun x => x * b) h1
        rwa [inv_mul_cancel_right] at hh
      rw [h2, spTwoNegOne_comm]
  · rintro (rfl | h)
    · rfl
    · rw [h, map_mul, spTwoProj_spTwoNegOne, mul_one]

theorem involution_invariant_fails (u : ↥(StatedSp 2 (ZMod 5)))
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (hum : u ≠ spTwoNegOne) :
    ¬ ReflPairInvariant (spTwoProj u) := by
  rintro ⟨y, hy, hc, hxy⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective
    ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5))) y
  rw [isConj_iff] at hy
  obtain ⟨g, hg⟩ := hy
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective
    ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5))) g
  have hconj : spTwoProj (g' * v * g'⁻¹) = spTwoProj u := by
    rw [map_mul, map_mul, map_inv]
    simpa only [spTwoProj] using hg
  change Commute (spTwoProj v) (spTwoProj u) at hc
  change IsConj (spTwoProj u * spTwoProj v) (spTwoProj u) at hxy
  have hw2 : (g' * v * g'⁻¹) * (g' * v * g'⁻¹) = 1 := by
    rw [spTwoProj_eq_iff] at hconj
    rcases hconj with h | h
    · rw [h, hu2]
    · rw [h, mul_assoc, ← mul_assoc spTwoNegOne u, spTwoNegOne_comm, mul_assoc,
        ← mul_assoc u u (spTwoNegOne * spTwoNegOne), hu2, one_mul, spTwoNegOne_mul_self]
  have hv2 : v * v = 1 := by
    have hvv : v * v = g'⁻¹ * ((g' * v * g'⁻¹) * (g' * v * g'⁻¹)) * g' := by group
    rw [hvv, hw2, mul_one, inv_mul_cancel]
  have hcomm : v * u = u * v ∨ v * u = spTwoNegOne * (u * v) := by
    have h' : spTwoProj (v * u) = spTwoProj (u * v) := by
      rw [map_mul, map_mul]
      exact hc.eq
    rw [spTwoProj_eq_iff] at h'
    rcases h' with h | h
    · exact Or.inl h
    · right
      rw [h, spTwoNegOne_comm]
  have hx1 : spTwoProj u ≠ 1 := by
    intro h
    rcases (spTwoProj_eq_one_iff u).mp h with h | h
    · exact hu1 h
    · exact hum h
  have hAm : (u : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) ≠ -1 := by
    intro h
    exact hum (Subtype.ext (h.trans spTwoNegOne_eq_negOne.symm))
  rcases hcomm with hcom | hanti
  · have hu2' : (u : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) * (u : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 := by
      simpa using congrArg Subtype.val hu2
    have hv2' : (v : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) * (v : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 := by
      simpa using congrArg Subtype.val hv2
    have hAB : (u : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) * (v : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) =
        (v : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) * (u : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) := by
      simpa using congrArg Subtype.val hcom.symm
    have hu1' : (u : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) ≠ 1 := by
      intro h
      exact hu1 (Subtype.ext h)
    have hmem := CFSG.RankThree.SubgroupLists.eq_of_commute_involution
      (K := ZMod 5) (h2 := by decide) u.2 v.2 hu2' hv2' hAB hu1' hAm
    have hy_eq : spTwoProj v = 1 ∨ spTwoProj v = spTwoProj u := by
      rcases hmem with h | h | h | h
      · left
        have : v = 1 := Subtype.ext h
        rw [this, map_one]
      · left
        have : v = spTwoNegOne := Subtype.ext (h.trans spTwoNegOne_eq_negOne.symm)
        rw [this, spTwoProj_spTwoNegOne]
      · right
        have : v = u := Subtype.ext h
        rw [this]
      · right
        have hvu : v = spTwoNegOne * u := by
          apply Subtype.ext
          change (v : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) =
            (spTwoNegOne : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) * (u : GL (Fin 2 ⊕ Fin 2) (ZMod 5))
          rw [h, spTwoNegOne_eq_negOne, neg_one_mul]
        rw [hvu, map_mul, spTwoProj_spTwoNegOne, one_mul]
    have hy1 : spTwoProj v ≠ 1 := by
      intro h1
      have h1' : QuotientGroup.mk'
          ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5))) v = 1 := by
        rw [show QuotientGroup.mk' _ v = spTwoProj v from rfl, h1]
      have h2 : spTwoProj u = 1 := by
        rw [← hg, h1', mul_one, mul_inv_cancel]
      exact hx1 h2
    have hyx : spTwoProj v = spTwoProj u := hy_eq.resolve_left hy1
    have hxy1 : spTwoProj u * spTwoProj v = 1 := by
      rw [hyx, ← map_mul, hu2, map_one]
    rw [hxy1, isConj_iff] at hxy
    obtain ⟨c, hc⟩ := hxy
    exact hx1 (by simpa using hc.symm)
  · have huv2 : (u * v) * (u * v) = spTwoNegOne := by
      have huv_eq : u * v = spTwoNegOne * (v * u) := by
        rw [hanti, ← mul_assoc, spTwoNegOne_mul_self, one_mul]
      nth_rw 1 [huv_eq]
      rw [mul_assoc, mul_assoc, ← mul_assoc u u v, hu2, one_mul, hv2, mul_one]
    have hprod : spTwoProj u * QuotientGroup.mk'
        ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5))) v =
        spTwoProj (u * v) := by
      simp only [spTwoProj, map_mul]
    have hxy' : IsConj (spTwoProj (u * v)) (spTwoProj u) := by
      rw [← hprod]
      exact hxy
    rw [isConj_iff] at hxy'
    obtain ⟨g'', hg''⟩ := hxy'
    obtain ⟨g3, rfl⟩ := QuotientGroup.mk'_surjective
      ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5))) g''
    have hconj2 : spTwoProj (g3 * (u * v) * g3⁻¹) = spTwoProj u := by
      simp only [spTwoProj] at hg'' ⊢
      rw [map_mul, map_mul, map_inv]
      exact hg''
    have hz : spTwoNegOne = 1 := by
      have hsq : (g3 * (u * v) * g3⁻¹) * (g3 * (u * v) * g3⁻¹) = spTwoNegOne := by
        have hge : (g3 * (u * v) * g3⁻¹) * (g3 * (u * v) * g3⁻¹) =
            g3 * ((u * v) * (u * v)) * g3⁻¹ := by group
        rw [hge, huv2, ← spTwoNegOne_comm g3, mul_assoc, mul_inv_cancel, mul_one]
      rw [spTwoProj_eq_iff] at hconj2
      rcases hconj2 with h | h
      · rw [h, hu2] at hsq
        exact hsq.symm
      · have hu1' : (u * spTwoNegOne) * (u * spTwoNegOne) = 1 := by
          rw [mul_assoc, ← mul_assoc spTwoNegOne u, spTwoNegOne_comm, mul_assoc,
            ← mul_assoc u u (spTwoNegOne * spTwoNegOne), hu2, one_mul, spTwoNegOne_mul_self]
        rw [h, hu1'] at hsq
        exact hsq.symm
    exact spTwoNegOne_ne_one hz

end CFSG.OddTranspositions.PartThree

module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def w1369_im (U C : Subgroup W) (M : Subgroup W) : Subgroup (Sect U C) :=
  (M.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))

@[expose] def w1369_pre (U C : Subgroup W) (N : Subgroup (Sect U C)) : Subgroup W :=
  (N.comap (QuotientGroup.mk' (C.subgroupOf U))).map U.subtype

theorem w1369_im_mono {U C : Subgroup W} {M M' : Subgroup W} (h : M ≤ M') :
    w1369_im U C M ≤ w1369_im U C M' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem w1369_pre_mono {U C : Subgroup W} {N N' : Subgroup (Sect U C)} (h : N ≤ N') :
    w1369_pre U C N ≤ w1369_pre U C N' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem w1369_pre_inf (U C : Subgroup W) (N N' : Subgroup (Sect U C)) :
    w1369_pre U C (N ⊓ N') = w1369_pre U C N ⊓ w1369_pre U C N' := by
  unfold w1369_pre
  rw [Subgroup.comap_inf, Subgroup.map_inf _ _ U.subtype U.subtype_injective]

theorem w1369_pre_im {U C M : Subgroup W} (hC : C ≤ M) (hM : M ≤ U) :
    w1369_pre U C (w1369_im U C M) = M := by
  unfold w1369_pre w1369_im
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hsup : M.subgroupOf U ⊔ C.subgroupOf U = M.subgroupOf U :=
    sup_eq_left.mpr (Subgroup.comap_mono hC)
  rw [hsup]
  exact Subgroup.map_subgroupOf_eq_of_le hM

theorem w1369_pre_im' {U C M : Subgroup W} (hCU : C ≤ U) (hM : M ≤ U) :
    w1369_pre U C (w1369_im U C M) = M ⊔ C := by
  unfold w1369_pre w1369_im
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', ← Subgroup.subgroupOf_sup hM hCU,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (sup_le hM hCU)]

theorem w1369_im_pre (U C : Subgroup W) (N : Subgroup (Sect U C)) :
    w1369_im U C (w1369_pre U C N) = N := by
  unfold w1369_im w1369_pre
  have h1 : ((N.comap (QuotientGroup.mk' (C.subgroupOf U))).map U.subtype).subgroupOf U =
      N.comap (QuotientGroup.mk' (C.subgroupOf U)) := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  rw [h1]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N

theorem w1369_im_C (U C : Subgroup W) : w1369_im U C C = ⊥ := by
  unfold w1369_im
  rw [Subgroup.map_eq_bot_iff]
  exact (QuotientGroup.ker_mk' (C.subgroupOf U)).ge

theorem w1369_im_top (U C : Subgroup W) : w1369_im U C U = ⊤ := by
  unfold w1369_im
  rw [Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem w1369_pre_bot {U C : Subgroup W} (hCU : C ≤ U) : w1369_pre U C ⊥ = C := by
  unfold w1369_pre
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
  exact Subgroup.map_subgroupOf_eq_of_le hCU

theorem w1369_im_sup {U C : Subgroup W} {A B : Subgroup W} (hA : A ≤ U) (hB : B ≤ U) :
    w1369_im U C (A ⊔ B) = w1369_im U C A ⊔ w1369_im U C B := by
  unfold w1369_im
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem w1369_subgroupOf_iSup {ι : Type*} {U : Subgroup W} {M : ι → Subgroup W}
    (hM : ∀ i, M i ≤ U) : (⨆ i, M i).subgroupOf U = ⨆ i, (M i).subgroupOf U := by
  apply Subgroup.map_injective_of_ker_le U.subtype (by simp) (by simp)
  rw [Subgroup.map_iSup]
  simp only [Subgroup.map_subgroupOf_eq_of_le (hM _)]
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (iSup_le hM)]

theorem w1369_im_iSup {ι : Type*} {U C : Subgroup W} {M : ι → Subgroup W} (hM : ∀ i, M i ≤ U) :
    w1369_im U C (⨆ i, M i) = ⨆ i, w1369_im U C (M i) := by
  unfold w1369_im
  rw [w1369_subgroupOf_iSup hM, Subgroup.map_iSup]

theorem w1369_secAut_mem_secSub {U C : Subgroup W} {A : Subgroup (MulAut W)}
    (hA : StabPair A U C) {a : MulAut W} (ha : a ∈ A) :
    secAut U C a (hA a ha).1 (hA a ha).2 ∈ secSub U C A := by
  rw [secSub, CFSG.Quasithin.autSec, CFSG.Quasithin.mem_autQuot]
  have hUa : a ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h1 := (hA a⁻¹ (A.inv_mem ha)).1 (a u) hu
      simpa using h1
    · exact (hA a ha).1 u
  let h : stabSub U := ⟨a, hUa⟩
  have hmem : (h : MulAut W) ∈ A := ha
  refine ⟨⟨resHom U h, ?_⟩, ?_, ?_⟩
  · intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
    constructor
    · intro hx
      have h1 := (hA a⁻¹ (A.inv_mem ha)).2 (a x) hx
      simpa using h1
    · exact (hA a ha).2 x
  · exact mem_autSub.mpr ⟨h, hmem, rfl⟩
  · refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v =>
        rw [quotHom_mk, secAut_mk]
        exact congrArg QuotientGroup.mk (Subtype.ext (by rw [resHom_apply]))

theorem w1369_stable_im {U C : Subgroup W} {A : Subgroup (MulAut W)} (hA : StabPair A U C)
    {M : Subgroup W} (hAM : StableUnder A M) :
    StableUnder (secSub U C A) (w1369_im U C M) := by
  intro γ hγ x hx
  rw [w1369_im, Subgroup.mem_map] at hx ⊢
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨g, hg, hgq⟩ := (CFSG.Quasithin.mem_autQuot).mp hγ
  obtain ⟨h, hh, heq⟩ := mem_autSub.mp hg
  rw [← hgq, QuotientGroup.mk'_apply, quotHom_mk, heq.symm]
  refine Subgroup.mem_map.mpr ⟨resHom U h m, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf, resHom_apply]
  exact hAM h hh (m : W) (Subgroup.mem_subgroupOf.mp hm)

theorem w1369_stable_pre {U C : Subgroup W} {A : Subgroup (MulAut W)} (hA : StabPair A U C)
    {N : Subgroup (Sect U C)} (hN : StableUnder (secSub U C A) N) :
    StableUnder A (w1369_pre U C N) := by
  intro a ha x hx
  rw [w1369_pre, Subgroup.mem_map] at hx ⊢
  obtain ⟨u, hu, rfl⟩ := hx
  have huN : QuotientGroup.mk u ∈ N := Subgroup.mem_comap.mp hu
  have hmem := hN (secAut U C a (hA a ha).1 (hA a ha).2)
    (w1369_secAut_mem_secSub hA ha) (QuotientGroup.mk u) huN
  rw [secAut_mk] at hmem
  exact ⟨⟨a (u : W), (hA a ha).1 u u.2⟩, hmem, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

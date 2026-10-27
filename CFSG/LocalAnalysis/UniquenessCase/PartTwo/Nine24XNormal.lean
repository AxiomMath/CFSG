module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XTits
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6CommAux1
public import CFSG.Quasithin.Background.B6Sections
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.GH74.Generic.Context
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem n924x_isPerfect_iSup {ι : Sort*} (A : ι → Subgroup G)
    (hA : ∀ i, Group.IsPerfect (A i)) : Group.IsPerfect (⨆ i, A i : Subgroup G) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h : ⁅g₁, g₂⁆ ∈ (⨆ i, A i : Subgroup G) := by
      rw [commutatorElement_def]
      exact (⨆ i, A i).mul_mem
        ((⨆ i, A i).mul_mem ((⨆ i, A i).mul_mem hg₁ hg₂) ((⨆ i, A i).inv_mem hg₁))
        ((⨆ i, A i).inv_mem hg₂)
    exact h
  · rw [iSup_le_iff]
    intro i
    have h : ⁅A i, A i⁆ ≤ ⁅(⨆ i, A i : Subgroup G), (⨆ i, A i : Subgroup G)⁆ :=
      Subgroup.commutator_mono (le_iSup A i) (le_iSup A i)
    rwa [Subgroup.isPerfect_iff.mp (hA i)] at h

theorem normal_subgroupOf_inf_of_pRank_le_one (D : Data G) {L P X H : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hLN : D.M ≤ normalizer (L : Set G)) (hn : 1 < n)
    (hU : IsU4 (Bar2 L) n) (hP : ParabolicOf L P) (hX : X = F07.DerInf P)
    (hL2 : IsL2 (Bar2 X) (2 * n)) (hXH : X ≤ H)
    (h3 : CFSG.Open.pRank 3 (F09.L9 X (H ⊓ D.M)) ≤ 1) : (X.subgroupOf (H ⊓ D.M)).Normal := by
  set K : Subgroup G := H ⊓ D.M with hK
  have hDerP : (CFSG.perfectResidual ↥P).map P.subtype ≤ P :=
    Subgroup.map_subtype_le (CFSG.perfectResidual ↥P)
  have hXL : X ≤ L := by
    rw [hX]
    exact hDerP.trans hP.2.1
  have hXDM : X ≤ D.M := hXL.trans (A3.subnormal_le hL.1)
  have hXK : X ≤ K := le_inf hXH hXDM
  have hXperf : Group.IsPerfect ↥X := by
    rw [hX]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map P
  have hsimple : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have h3dvd : 3 ∣ Nat.card (Bar2 X) :=
    CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two
      (CFSG.GH74.Generic.stated_of_lieModel_PSL hL2)
  have hOpp : Opp 3 X = X :=
    s16c6_opp3_eq_self (Subgroup.isPerfect_iff.mp hXperf) hsimple h3dvd
  set J : Subgroup G := F09.L9 X K with hJ
  have hJeq : J = ⨆ w : ↥K, X.map (MulAut.conj (w : G)).toMonoidHom := by
    simp only [hJ, F09.L9, hOpp]
  have hJperf : Group.IsPerfect ↥J := by
    rw [hJeq]
    exact n924x_isPerfect_iSup _
      fun w => hXperf.map (MulAut.conj (w : G)).toMonoidHom
  have hXJ : X ≤ J := by
    rw [hJeq]
    refine le_iSup_of_le (1 : ↥K) fun x hx => ?_
    simpa using (Subgroup.mem_map_of_mem (f := (MulAut.conj (1 : G)).toMonoidHom) hx)
  have hKL : K ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans hLN
  have hJL : J ≤ L := by
    rw [hJeq]
    refine iSup_le fun w => ?_
    have hw : (w : G) ∈ Subgroup.normalizer (L : Set G) := hKL w.2
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hw
    calc X.map (MulAut.conj (w : G)).toMonoidHom
        ≤ L.map (MulAut.conj (w : G)).toMonoidHom := Subgroup.map_mono hXL
      _ = L := hw
  have h3J : CFSG.Open.pRank 3 J ≤ 1 := by rw [hJ]; exact h3
  have hJP : J ≤ P := le_parabolic_of_pRank_le_one hn hU hP hX hL2 hXJ hJL h3J
  have hJX : J ≤ X := by
    rw [hX]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_perfectResidual_map_of_isPerfect
      hJperf hJP
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr ?_
  rw [Subgroup.le_normalizer_iff]
  intro k hk x hx
  have hle : X.map (MulAut.conj k).toMonoidHom ≤ J := by
    rw [hJeq]
    exact le_iSup (fun w : ↥K => X.map (MulAut.conj (w : G)).toMonoidHom) ⟨k, hk⟩
  have hmem : MulAut.conj k x ∈ X := (hle.trans hJX) (Subgroup.mem_map_of_mem _ hx)
  simpa [MulAut.conj_apply] using hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

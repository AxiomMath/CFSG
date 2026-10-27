module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Hyperplanes
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem f4e_commute_zpowers_of {a b : MulAut W} (hab : a * b = b * a) {g : MulAut W}
    (hg : g ∈ Subgroup.zpowers b) : a * g = g * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((show Commute a b from hab).zpow_right k).eq

omit [Finite W] in
theorem f4e_stable_commSub {A G : Subgroup (MulAut W)} {U : Subgroup W}
    (hcomm : ∀ a ∈ A, ∀ g ∈ G, a * g = g * a) (hU : StableUnder A U) :
    StableUnder A (commSub U G) := by
  intro a ha w hw
  rw [commSub] at hw ⊢
  refine Subgroup.closure_induction (p := fun c _ => a c ∈ commSub U G) ?_ ?_ ?_ ?_ hw
  · rintro c ⟨g, hg, u, hu, rfl⟩
    have h1 : a (g u) = g (a u) := by
      have := congrArg (fun f : MulAut W => f u) (hcomm a ha g hg)
      simpa [MulAut.mul_apply] using this
    have hmem : g (a u) * (a u)⁻¹ ∈ commSub U G :=
      Subgroup.subset_closure ⟨g, hg, a u, hU a ha u hu, rfl⟩
    simpa only [map_mul, map_inv, h1] using hmem
  · simp
  · intro b c _ _ ihb ihc
    rw [map_mul]
    exact (commSub U G).mul_mem ihb ihc
  · intro b _ ihb
    rw [map_inv]
    exact (commSub U G).inv_mem ihb

omit [Finite W] in
theorem f4e_map_conj_eq {E : Subgroup (MulAut W)} {n : MulAut W}
    (hn : n ∈ normalizer (E : Set (MulAut W))) :
    E.map (MulAut.conj n).toMonoidHom = E := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    have h := (Subgroup.mem_normalizer_iff.mp hn y).mp hy
    simpa [MulAut.conj_apply] using h
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * x * n, ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp
        ((normalizer (E : Set (MulAut W))).inv_mem hn) x).mp hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

omit [Finite W] in
theorem f4e_map_hypPart_conj {E D : Subgroup (MulAut W)} {n : MulAut W}
    (hn : n ∈ normalizer (E : Set (MulAut W))) :
    (hypPart E D).map n.toMonoidHom = hypPart E (D.map (MulAut.conj n).toMonoidHom) := by
  have hEimg := f4e_map_conj_eq (E := E) hn
  have hU : (commSub ⊤ E).map n.toMonoidHom = commSub ⊤ E := by
    have h := CFSG.Quasithin.Asc81c.commSub_map_conj E n
    rw [hEimg] at h
    exact h.symm
  unfold hypPart
  rw [Subgroup.map_inf _ _ _ n.injective, hU, ← CFSG.Quasithin.Asc81c.fixV_map_conj D n]

theorem f4e_three_dvd_component (hW : ∀ w : W, w ^ 2 = 1)
    {E : Subgroup (MulAut W)} {M : Subgroup W}
    (hEelem : CFSG.Open.IsElemAbelian 7 E) (hEcard : Nat.card ↥E = 49)
    (hMstab : StableUnder E M) (hMfix : M ⊓ fixV E = ⊥)
    {D : Subgroup (MulAut W)} (hD : D ∈ hyperplanes 7 E) :
    3 ∣ rk ↥(M ⊓ fixV D) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEelem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hproper : D ≠ E := by
    intro hEq
    have hrel := hD.2
    rw [hEq] at hrel
    simp at hrel
  have h_exists : ∃ y ∈ E, y ∉ D := by
    by_contra h
    push Not at h
    exact hproper (le_antisymm hD.1 fun z hz => h z hz)
  obtain ⟨y, hyE, hyD⟩ := h_exists
  have hy1 : y ≠ 1 := by
    intro h
    exact hyD (h.symm ▸ D.one_mem)
  have hy7 : y ^ 7 = 1 := hEelem.2 y hyE
  have hyord : orderOf y = 7 := by
    have hdvd : orderOf y ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hy7
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h7
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact h7
  have hyhyp : Subgroup.zpowers y ∈ hyperplanes 7 E := by
    have hycard : Nat.card ↥(Subgroup.zpowers y) = 7 := by
      rw [Nat.card_zpowers, hyord]
    have hyle : Subgroup.zpowers y ≤ E := Subgroup.zpowers_le.mpr hyE
    refine ⟨hyle, ?_⟩
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers y) (K := E)
    rw [inf_of_le_left hyle, hycard, hEcard] at h
    omega
  have hne : D ≠ Subgroup.zpowers y := by
    intro h
    exact hyD (h ▸ Subgroup.mem_zpowers y)
  have hsup : D ⊔ Subgroup.zpowers y = E :=
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.sup_eq_of_hyperplanes hD hyhyp hne
  have hUy : StableUnder (Subgroup.zpowers y) (M ⊓ fixV D) := by
    intro z' hz' m hm
    rw [Subgroup.mem_inf] at hm ⊢
    refine ⟨hMstab z' (Subgroup.zpowers_le.mpr hyE hz') m hm.1, ?_⟩
    rw [mem_fixV] at hm ⊢
    intro d hd
    have hcomm : d * z' = z' * d :=
      hEcomm d (hD.1 hd) z' (Subgroup.zpowers_le.mpr hyE hz')
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hm.2 d hd]
  have hfix : (M ⊓ fixV D) ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    rw [inf_assoc, ← w16g_fixV_sup D (Subgroup.zpowers y), hsup, hMfix]
  have hdvd := dParam_dvd_rk hW Nat.prime_seven (by norm_num) hyord
    (fun m hm => hUy y (Subgroup.mem_zpowers y) m hm) hfix
  have hdp : dParam 7 = 3 := by
    rw [dParam]
    exact orderOf_eq_prime (by decide) (by decide)
  rwa [hdp] at hdvd

end CFSG.LocalAnalysis.WeakClosure81

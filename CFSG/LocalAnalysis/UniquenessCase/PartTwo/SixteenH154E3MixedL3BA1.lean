module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA1A
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_three_ne_bot_dim_le_three
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowL3 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3) :
    rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 3 := by
  obtain ⟨hsl, hsum⟩ := hL3
  obtain ⟨K₀, hK₀f, hK₀fin, hK₀card, ⟨e⟩⟩ := hsl
  letI := hK₀f
  haveI : Group.IsPerfect ↥(StatedSL 3 K₀) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K₀
  have hperf : Group.IsPerfect ↥(lBar ⊥ V h.hyp151.isElemAbelian L) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hmem : ∀ l ∈ lBar ⊥ V h.hyp151.isElemAbelian L,
      ∀ y ∈ (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian)),
        l y ∈ (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian)) :=
    fun l _ y _ => Subgroup.mem_top (l y)
  have hUinv : ∀ l ∈ lBar ⊥ V h.hyp151.isElemAbelian L,
      ∀ u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L),
        l u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) :=
    s16jp_commSub_stable (L := lBar ⊥ V h.hyp151.isElemAbelian L) (Y := ⊤) hmem
  have hUc : commSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (lBar ⊥ V h.hyp151.isElemAbelian L) =
      commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) :=
    s16jp_commSub_commSub hperf (Y := ⊤) hmem
  have hW2 : ∀ w : Vtil ⊥ V h.hyp151.isElemAbelian, w ^ 2 = 1 := by
    intro w
    rw [pow_two]
    obtain ⟨y, rfl⟩ := mkTil_surjective ⊥ V h.hyp151.isElemAbelian w
    rw [← map_mul, ← sq, IntMod.sq_eq_one y, map_one]
  have hcard : Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2 ^ (1 * 3) :=
    s16fh_sum_cover hW2 hperf hUinv hUc inf_le_right
      (N := fun H U Z => BinaryNaturalSL H U Z 3 1) (k := 3) (c := 1)
      (fun I hI => by
        obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hI
        letI := hKf
        letI := hKfin
        exact ⟨FFModel.nat (StatedSL 3 K),
          s16h_e3_l3_three_ne_bot_boundCover (by simpa using hKcard),
          hreal, s16fh_commSub_sup_nat (by norm_num) hreal⟩) hsum
  change padicValNat 2 (Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
    fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) ≤ 3
  calc
    padicValNat 2 (Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) ≤
        Nat.log 2 (Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) := padicValNat_le_nat_log _
    _ ≤ Nat.log 2 (2 ^ 3) := Nat.log_mono_right (by simpa using hcard)
    _ = 3 := Nat.log_pow (b := 2) (by norm_num) 3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

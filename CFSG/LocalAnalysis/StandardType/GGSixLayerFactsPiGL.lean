module

public import CFSG.RankThree.PartOne.KC.LinearCommutantPiGL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

namespace LayerFacts

open CFSG.RankThree.PartOne.KCLinComm Matrix

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ b, Field (E b)] {m : ι → ℕ}

variable (E m) in
@[expose] def GoodBlock (b : ι) : Prop :=
  2 ≤ m b ∧ (3 ≤ m b ∨ ∃ s : Finset (E b), s.card = 4)

variable (E m) in
@[expose] def goodSL : Subgroup (PiGL E m) :=
  ⨆ b : {b : ι // GoodBlock E m b}, blockSL E m b.1

theorem blockSL_le_goodSL {b : ι} (hb : GoodBlock E m b) : blockSL E m b ≤ goodSL E m :=
  le_iSup (fun b : {b : ι // GoodBlock E m b} => blockSL E m b.1) ⟨b, hb⟩

theorem ggCommutator_self_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun _ hg _ hh =>
    H.mul_mem (H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)) (H.inv_mem hh)

theorem commutator_goodSL : ⁅goodSL E m, goodSL E m⁆ = goodSL E m := by
  refine le_antisymm (ggCommutator_self_le _) (iSup_le fun b => ?_)
  calc blockSL E m b.1 = ⁅blockSL E m b.1, blockSL E m b.1⁆ :=
        (CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect
          (isPerfect_blockSL b.1 b.2.1 b.2.2)).symm
    _ ≤ ⁅goodSL E m, goodSL E m⁆ :=
        Subgroup.commutator_mono (blockSL_le_goodSL b.2) (blockSL_le_goodSL b.2)

theorem apply_eq_one_of_mem_goodSL {w : PiGL E m} (hw : w ∈ goodSL E m) {b : ι}
    (hb : ¬ GoodBlock E m b) : w b = 1 := by
  let S : Subgroup (PiGL E m) := Subgroup.pi {b | ¬ GoodBlock E m b} fun _ => ⊥
  have hS : goodSL E m ≤ S := by
    refine iSup_le fun c => ?_
    rintro _ ⟨s, rfl⟩ b' hb'
    have hcb : b' ≠ c.1 := fun h => hb' (h ▸ c.2)
    rw [blockEmbed_apply_of_ne hcb]
    exact Subgroup.one_mem _
  exact (Subgroup.mem_bot.mp (hS hw b hb))

theorem mem_goodSL_of_forall [Finite ι] {w : PiGL E m}
    (hgood : ∀ b, GoodBlock E m b → GeneralLinearGroup.det (w b) = 1)
    (hbad : ∀ b, ¬ GoodBlock E m b → w b = 1) : w ∈ goodSL E m := by
  refine Subgroup.pi_mem_of_mulSingle_mem _ fun b => ?_
  by_cases hb : GoodBlock E m b
  · obtain ⟨s, hs⟩ : w b ∈
        (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m b)) (E b) →* _).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hgood b hb
    refine blockSL_le_goodSL hb ⟨s, ?_⟩
    simp only [blockEmbed, MonoidHom.coe_comp, MonoidHom.mulSingle_apply, Function.comp_apply, hs]
  · rw [hbad b hb, Pi.mulSingle_one]
    exact Subgroup.one_mem _

theorem derivedSeries_pi_le {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)] (k : ℕ) :
    derivedSeries (∀ i, Gs i) k ≤ Subgroup.pi Set.univ fun i => derivedSeries (Gs i) k := by
  induction k with
  | zero =>
    intro x _ i _
    exact Subgroup.mem_top _
  | succ k ih =>
    rw [derivedSeries_succ]
    exact (Subgroup.commutator_mono ih ih).trans (Subgroup.commutator_pi_pi_le _ _)

theorem natCard_eq_two_of_not_four {K : Type*} [Field K] [Finite K] [CharP K 2]
    (h4 : ¬ ∃ s : Finset K, s.card = 4) : Nat.card K = 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hlt : Fintype.card K < 4 := by
    by_contra hle
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K))
      (n := 4) (by rw [Finset.card_univ]; omega)
    exact h4 ⟨s, hs⟩
  have heven := FiniteField.even_card_iff_char_two.mp (ringChar.eq K 2)
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card]
  omega

omit [DecidableEq ι] in
theorem isSolvable_of_not_goodBlock [∀ b, Finite (E b)] [∀ b, CharP (E b) 2] {b : ι}
    (hb : ¬ GoodBlock E m b) : Group.IsSolvable (GL (Fin (m b)) (E b)) := by
  rcases Nat.lt_or_ge (m b) 1 with h0 | h1
  · have : Subsingleton (GL (Fin (m b)) (E b)) :=
      ⟨fun x y => Units.ext (Matrix.ext fun i => absurd i.2 (by omega))⟩
    infer_instance
  · refine CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable
      (m b) (E b) ?_
    by_cases h2 : 2 ≤ m b
    · have hm : m b = 2 := by
        by_contra hm
        exact hb ⟨h2, Or.inl (by omega)⟩
      refine Or.inr ⟨hm, Or.inl (natCard_eq_two_of_not_four fun h4 => hb ⟨h2, Or.inr h4⟩)⟩
    · exact Or.inl (by omega)

theorem exists_derivedSeries_le_goodSL [Finite ι] [∀ b, Finite (E b)] [∀ b, CharP (E b) 2] :
    ∃ k, derivedSeries (PiGL E m) k ≤ goodSL E m := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hk : ∀ b, ∃ k, ¬ GoodBlock E m b → derivedSeries (GL (Fin (m b)) (E b)) k = ⊥ := by
    intro b
    by_cases hb : GoodBlock E m b
    · exact ⟨0, fun h => absurd hb h⟩
    · obtain ⟨k, hk⟩ := (isSolvable_of_not_goodBlock hb).solvable
      exact ⟨k, fun _ => hk⟩
  choose k hk using hk
  refine ⟨Finset.univ.sup k + 1, fun w hw => ?_⟩
  have hw' := derivedSeries_pi_le _ hw
  refine mem_goodSL_of_forall (fun b _ => ?_) (fun b hb => ?_)
  · have h1 : derivedSeries (GL (Fin (m b)) (E b)) (Finset.univ.sup k + 1) ≤
        commutator (GL (Fin (m b)) (E b)) := by
      rw [← derivedSeries_one]
      exact derivedSeries_antitone _ (by omega)
    exact Abelianization.commutator_subset_ker GeneralLinearGroup.det (h1 (hw' b trivial))
  · have h1 : derivedSeries (GL (Fin (m b)) (E b)) (Finset.univ.sup k + 1) ≤
        derivedSeries (GL (Fin (m b)) (E b)) (k b) :=
      derivedSeries_antitone _ (by
        have := Finset.le_sup (f := k) (Finset.mem_univ b)
        omega)
    have h2 := h1 (hw' b trivial)
    rwa [hk b hb, Subgroup.mem_bot] at h2

theorem eq_one_of_sq_eq_one_charTwo {K : Type*} [Field K] [CharP K 2] {c : Kˣ} (hc : c ^ 2 = 1) :
    c = 1 := by
  have h : ((c : K) + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, one_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one,
      CharTwo.add_self_eq_zero]
  have h1 : (c : K) + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h
  exact Units.ext (by
    rw [Units.val_one, ← CharTwo.neg_eq (1 : K)]
    exact eq_neg_of_add_eq_zero_left h1)

theorem eq_one_of_mem_goodSL_of_commute [∀ b, CharP (E b) 2] {w : PiGL E m}
    (hw : w ∈ goodSL E m) (hc : ∀ g ∈ goodSL E m, w * g = g * w) (h2 : w ^ 2 = 1) : w = 1 := by
  funext b
  by_cases hb : GoodBlock E m b
  · have hcomm : ∀ s : SpecialLinearGroup (Fin (m b)) (E b),
        Commute (s : Matrix (Fin (m b)) (Fin (m b)) (E b))
          ((w b : GL (Fin (m b)) (E b)) : Matrix (Fin (m b)) (Fin (m b)) (E b)) := by
      intro s
      have h1 := congrFun (hc _ (blockSL_le_goodSL hb ⟨s, rfl⟩)) b
      simp only [Pi.mul_apply, blockEmbed_apply_self] at h1
      have h3 := congrArg (fun g : GL (Fin (m b)) (E b) =>
        (g : Matrix (Fin (m b)) (Fin (m b)) (E b))) h1
      show (s : Matrix (Fin (m b)) (Fin (m b)) (E b)) * _ = _ * _
      simpa using h3.symm
    have hsc : ((w b : GL (Fin (m b)) (E b)) : Matrix (Fin (m b)) (Fin (m b)) (E b)) ∈
        Set.range (Matrix.scalar (Fin (m b))) :=
      Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => hcomm ⟨t.toMatrix, t.det⟩
    have hmem : w b ∈ Subgroup.center (GL (Fin (m b)) (E b)) :=
      GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hsc
    rw [GeneralLinearGroup.center_eq_range_scalar] at hmem
    obtain ⟨c, hcw⟩ := hmem
    have hc2 : c ^ 2 = 1 := by
      have h4 := congrFun h2 b
      rw [Pi.pow_apply, ← hcw, ← map_pow, Pi.one_apply] at h4
      have h0 : 0 < m b := by have := hb.1; omega
      have h5 := congrArg (fun g : GL (Fin (m b)) (E b) =>
        (g : Matrix (Fin (m b)) (Fin (m b)) (E b)) ⟨0, h0⟩ ⟨0, h0⟩) h4
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Units.val_one, Matrix.one_apply_eq] at h5
      exact Units.ext h5
    rw [← hcw, eq_one_of_sq_eq_one_charTwo hc2, map_one, Pi.one_apply]
  · rw [apply_eq_one_of_mem_goodSL hw hb, Pi.one_apply]

end LayerFacts

end CFSG.StandardType

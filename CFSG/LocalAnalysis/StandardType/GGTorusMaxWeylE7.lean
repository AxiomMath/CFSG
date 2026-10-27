module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetStab
public import CFSG.ClassicalInvolution.Solomon73.YamakiPres
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxWeylE7Aux
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxWeylE7Aux2
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.RankThree.PartOne.KE.E7FiveData

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.OddStandard.SmallF3.Omega.E7RootSet

theorem tmW7_x_mem_evenWeyl
    (i : Fin 12) : tmW7_x i ∈ evenWeyl := by
  rw [tmW7_evenWeyl_eq_ker, MonoidHom.mem_ker]
  have h : tmW7_x i = (coxeterSystem Tag.E7).wordProd (tmW7_xWord i) := rfl
  rw [h, lengthParity_word, ofAdd_eq_one, ZMod.natCast_eq_zero_iff_even]
  exact tmW7_xWord_even i

theorem tmW7_x_zero_ne_one : tmW7_x 0 ≠ 1 := by
  intro h
  have h1 : ∀ j : Fin Tag.E7.rank,
      TableBExc.wordAct Tag.E7 (tmW7_xWord 0) (Pi.single j 1) = Pi.single j 1 := by
    intro j
    have := congrArg
      (fun w : WeylGroup Tag.E7 => w • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) h
    simpa [tmW7_x, wordW_smul] using this
  have h2 : ¬ (∀ j : Fin Tag.E7.rank,
      TableBExc.wordAct Tag.E7 (tmW7_xWord 0) (Pi.single j 1) = Pi.single j 1) := by
    decide +kernel
  exact h2 h1

theorem tmW7_closure_ne_bot : Subgroup.closure (Set.range tmW7_x) ≠ ⊥ := by
  intro h
  have hmem : tmW7_x 0 ∈ Subgroup.closure (Set.range tmW7_x) :=
    Subgroup.subset_closure ⟨0, rfl⟩
  rw [h] at hmem
  exact tmW7_x_zero_ne_one (Subgroup.mem_bot.mp hmem)

theorem tmW7_closure_le_evenWeyl :
    Subgroup.closure (Set.range tmW7_x) ≤ evenWeyl :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact tmW7_x_mem_evenWeyl i)

theorem tmW7_closure_mulEquiv_sp62 :
    Nonempty (↥(Subgroup.closure (Set.range tmW7_x)) ≃* StatedSp 3 (ZMod 2)) := by
  rcases CFSG.ClassicalInvolution.Solomon73.Yamaki.closure_eq_bot_or_nonempty_mulEquiv
    tmW7_x tmW7_x_rel with h | h
  · exact absurd h tmW7_closure_ne_bot
  · exact h

theorem tmW7_closure_eq_evenWeyl :
    Subgroup.closure (Set.range tmW7_x) = evenWeyl := by
  obtain ⟨f⟩ := tmW7_closure_mulEquiv_sp62
  have hcard : Nat.card ↥(Subgroup.closure (Set.range tmW7_x)) = 1451520 := by
    rw [Nat.card_congr f.toEquiv,
      CFSG.ClassicalInvolution.Solomon73.Yamaki.card_sp62]
  apply Subgroup.eq_of_le_of_card_ge tmW7_closure_le_evenWeyl
  rw [hcard, natCard_evenWeyl]

theorem tmW7_evenWeyl_mulEquiv_sp62 :
    Nonempty (evenWeyl ≃* ↥(StatedSp 3 (ZMod 2))) := by
  obtain ⟨f⟩ := tmW7_closure_mulEquiv_sp62
  exact ⟨(MulEquiv.subgroupCongr tmW7_closure_eq_evenWeyl).symm.trans f⟩

theorem tmW7_not_isMulCommutative_evenWeyl :
    ¬ IsMulCommutative evenWeyl := by
  obtain ⟨f⟩ := tmW7_evenWeyl_mulEquiv_sp62
  intro h
  refine tmW7_not_isMulCommutative_sp62 ⟨⟨fun a b => ?_⟩⟩
  calc a * b = f (f.symm a) * f (f.symm b) := by simp
    _ = f (f.symm a * f.symm b) := (map_mul f _ _).symm
    _ = f (f.symm b * f.symm a) := congrArg f (h.is_comm.comm (f.symm a) (f.symm b))
    _ = f (f.symm b) * f (f.symm a) := map_mul f _ _
    _ = b * a := by simp

theorem tmW7_commutator_le_evenWeyl :
    commutator (WeylGroup Tag.E7) ≤ evenWeyl := by
  rw [tmW7_evenWeyl_eq_ker]
  exact Abelianization.commutator_subset_ker (coxeterSystem Tag.E7).lengthParity

theorem tmW7_evenWeyl_le_commutator :
    evenWeyl ≤ commutator (WeylGroup Tag.E7) := by
  obtain ⟨f⟩ := tmW7_evenWeyl_mulEquiv_sp62
  haveI : IsSimpleGroup (StatedSp 3 (ZMod 2)) :=
    CFSG.ClassicalInvolution.Solomon73.Yamaki.isSimpleGroup_sp62
  haveI : IsSimpleGroup evenWeyl := f.isSimpleGroup
  have hperf : commutator (↥evenWeyl) = ⊤ :=
    CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup inferInstance
      tmW7_not_isMulCommutative_evenWeyl
  have htop : (⊤ : Subgroup ↥evenWeyl).map evenWeyl.subtype = evenWeyl := by
    ext x
    simp [Subgroup.mem_map]
  have hcomm : ⁅evenWeyl, evenWeyl⁆ = evenWeyl := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥evenWeyl) ⊤ evenWeyl.subtype
    rw [htop] at h1
    rw [← h1, ← commutator_def, hperf, htop]
  calc evenWeyl = ⁅evenWeyl, evenWeyl⁆ := hcomm.symm
    _ ≤ commutator (WeylGroup Tag.E7) := Subgroup.commutator_mono le_top le_top

theorem tmW7_commutator_eq_evenWeyl :
    commutator (WeylGroup Tag.E7) = evenWeyl :=
  le_antisymm tmW7_commutator_le_evenWeyl tmW7_evenWeyl_le_commutator

theorem tmW7_isSimpleGroup_commutator :
    IsSimpleGroup ↥(commutator (WeylGroup Tag.E7)) := by
  rw [tmW7_commutator_eq_evenWeyl]
  obtain ⟨f⟩ := tmW7_evenWeyl_mulEquiv_sp62
  haveI : IsSimpleGroup (StatedSp 3 (ZMod 2)) :=
    CFSG.ClassicalInvolution.Solomon73.Yamaki.isSimpleGroup_sp62
  exact f.isSimpleGroup

theorem tmW7_hom_trivial_of_le_nine
    {n : ℕ} (hn : n ≤ 9)
    (f : ↥(commutator (WeylGroup Tag.E7)) →* Equiv.Perm (Fin n)) : f = 1 := by
  haveI : IsSimpleGroup ↥(commutator (WeylGroup Tag.E7)) := tmW7_isSimpleGroup_commutator
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp h
    have hdvd : Nat.card ↥(commutator (WeylGroup Tag.E7)) ∣ Nat.card (Equiv.Perm (Fin n)) :=
      Subgroup.card_dvd_of_injective f hinj
    rw [tmW7_commutator_eq_evenWeyl, natCard_evenWeyl,
      Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
      Fintype.card_fin] at hdvd
    have h9 : ¬ (1451520 ∣ Nat.factorial 9) := by decide
    exact absurd (dvd_trans hdvd (Nat.factorial_dvd_factorial hn)) h9
  · exact MonoidHom.ext fun x => MonoidHom.mem_ker.mp (h.symm ▸ Subgroup.mem_top x)

end CFSG.StandardType.FrameRoute

end

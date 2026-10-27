module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AmalgamAseg
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AmalgamCells
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AmalgamCellsKT
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AmalgamPerfect
public import CFSG.Monster.GMS.MonsterUniquenessFinal
public import CFSG.Monster.GMS.TwoBabyUniqueOf
public import CFSG.Monster.GMS.ASegTitsTri
public import CFSG.Monster.GMS.ASegConnH87
public import CFSG.Monster.GMS.TwoAGraphIso
public import CFSG.Monster.GMS.ExistenceBridge
public import CFSG.Monster.Existence.AssemblyHS
public import CFSG.Monster.Existence.BabyOrder
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.Milestones.CL_LIT_Stroth_Leon_Sims_Baby_Monster_recognition
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.B
public import CFSG.LieType.Catalog.Realization
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.YGroups.DCE.MaximalB

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS
  CFSG.Monster.B.Recog CFSG.Monster.Existence CFSG.AGLEmbedding CFSG.Monster.GMS.S4Family


theorem kernelTrivialAt_MGriess_of_cells {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hCa : ∀ a : MGriess, orderOf a = 2 → IsTwoACentralizer a → PerfectCoreCell p (cent a))
    (hCz : ∀ z : MGriess, IsTwoBCentralizer z → PerfectCoreCell p (cent z)) :
    KernelTrivialAt MGriess p := by
  have hSLS : ∀ d₀ : NativeSporadic.B, orderOf d₀ = 2 → Matrix.rank (d₀.val.val - 1) = 1860 →
      SLSStatement d₀ := fun d₀ hd₀ hrank H _ _ _ d hd hc =>
    CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition_models d₀ hd₀ hrank H d hd hc
  have hT : Triangulable (twoAGraph tGriess) := triangulable_twoAGraph_tGriess hSLS
  have hI : GMSInterfaces (phiB uBar) MGriess :=
    (aSegLiterature_of twoBabyUnique babyTwoAAutInner hSLS).interfaces
      (hSLS _ orderOf_phiB_uBar' rank_phiB_uBar_sub_one) MGriess
  obtain ⟨⟨-, -, -, -⟩, hordT, -, -, -, hAt, -⟩ := monster_existence_clauses_one_two_of_stroth hSLS
  have hE : MonsterExistenceStatement MGriess := CFSG.Milestones.cl_lit_monster_existence_griess_conway
  obtain ⟨⟨hfin, -, -, -⟩, a, z₀, ha, hz₀, -, hcl, hA, hZ, hdata⟩ := hE
  have : Finite MGriess := hfin
  have hB : IsSimpleGroup NativeSporadic.B := CFSG.Sporadic.B.fam_b_simplicity
  have hd₀ : orderOf (phiB uBar) = 2 := orderOf_phiB_uBar'
  have hAa : IsTwoACentralizer a := hA a (IsConj.refl a)
  have hBcard : Nat.card NativeSporadic.B = monsterBabyOrder := card_nativeB
  have hG : GMSF1Type (phiB uBar) a z₀ :=
    ⟨GMSDoubleF2Centralizer.of_isTwoACentralizer ha hB hd₀ hAa,
      GMSLeechCentralizer.of_isTwoBCentralizer hz₀ (hZ z₀ (IsConj.refl z₀))⟩
  have hconj : IsConj tGriess a := by
    rcases hcl tGriess hordT with h | h
    · exact h.symm
    · exfalso
      have hZt := hZ tGriess h
      have hcard := card_cent_of_twoA hordT (hAt tGriess (IsConj.refl _))
      have h17 := hZt.2.2.2.2.2
      apply h17
      rw [hcard, hBcard]
      norm_num [monsterBabyOrder]
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hΓ : Triangulable (twoAGraph a) :=
    (triangulable_twoAGraph_iff_of_mulEquiv (MulAut.conj c) (by simpa using hc)).1 hT
  have hconn : (twoAGraph a).Preconnected := twoAGraph_preconnected hI hG
  obtain ⟨y, z, Dseg⟩ := exists_asegData hI hG
  let D : TitsData (twoAGraph a) MGriess Bool := asegTitsData hI hG Dseg hconn hΓ
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rw [ha] at this
    simpa [pow_two] using this
  have hyord : orderOf y = 2 := orderOf_eq_two_of_isConj_a hG Dseg.isConj_y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hyord; omega
  have hne : a ≠ y := Dseg.a_ne_y hG
  have hz : IsTwoBCentralizer z := hZ z Dseg.isConj_z
  have hCa' : PerfectCoreCell p (cent a) := hCa a ha hAa
  have hCz' : PerfectCoreCell p (cent z) := hCz z hz
  obtain ⟨-, cls, -, -, hc1, hc2, -, -, -, hshape, -⟩ := hdata
  have hK : PerfectCoreOf p (cent₂ a y) :=
    perfectCoreOf_twoPointOne hp2 isPerfect_twistedE6
      (hshape a y 1 (IsConj.refl a) Dseg.isConj_y (Dseg.isConj_ay.symm.trans hc1))
  have hJ' : PerfectCoreOf p (cent2 a (a * z)) :=
    perfectCoreOf_twoPointTwo hp2 isPerfect_Co2
      (hshape a (a * z) 2 (IsConj.refl a) Dseg.isConj_az (by
        rw [← mul_assoc, haa, one_mul]
        exact Dseg.isConj_z.symm.trans hc2))
  have hcz : cent2 a (a * z) = Subgroup.centralizer ({a} : Set MGriess) ⊓
      Subgroup.centralizer ({z} : Set MGriess) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, mul_left_cancel (a := a) ?_⟩
      calc a * (g * z) = (a * g) * z := by rw [mul_assoc]
        _ = (g * a) * z := by rw [h1]
        _ = g * (a * z) := by rw [mul_assoc]
        _ = (a * z) * g := h2
        _ = a * (z * g) := by rw [mul_assoc]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      calc g * (a * z) = (g * a) * z := by rw [mul_assoc]
        _ = (a * g) * z := by rw [h1]
        _ = a * (g * z) := by rw [mul_assoc]
        _ = a * (z * g) := by rw [h2]
        _ = (a * z) * g := by rw [mul_assoc]
  have hJ : PerfectCoreOf p (Subgroup.centralizer ({a} : Set MGriess) ⊓
      Subgroup.centralizer ({z} : Set MGriess)) := hcz ▸ hJ'
  have hXv : D.Xv = Subgroup.centralizer ({a} : Set MGriess) := rfl
  have hXe : ∀ g, g ∈ D.Xe ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a) := fun g => mem_edgeStab_iff Dseg
  have hXt0 : D.Xt false = Subgroup.normalizer ({a, y, a * y} : Set MGriess) := rfl
  have hXt1 : D.Xt true = Subgroup.centralizer ({z} : Set MGriess) ⊓
      Subgroup.normalizer ({a, y, a * y * z} : Set MGriess) := rfl
  have hdec : ∀ g ∈ Subgroup.normalizer ({a, y, a * y} : Set MGriess), ∃ k ∈ cent₂ a y,
      ∃ w ∈ Subgroup.normalizer ({a, y, a * y} : Set MGriess) ⊓
        Subgroup.centralizer ({z} : Set MGriess), g = k * w :=
    fun g hg => Dseg.exists_mul_of_mem_Xt0 (eightGroupLines_of hI hG) hG hg
  exact kernelTrivialAt_of_asegAmalgam D hp2 haa ha1 hy1 hne hXv hXe hXt0 hXt1 hdec hCa' hCz' hK hJ

theorem kernelTrivialAt_MGriess_of_amalgam {p : ℕ} [Fact p.Prime] (hp11 : 11 ≤ p)
    (hpB : ¬ p ^ 2 ∣ 2 * monsterBabyOrder) (hpZ : ¬ p ^ 2 ∣ twoBCentralizerOrder) :
    KernelTrivialAt MGriess p :=
  kernelTrivialAt_MGriess_of_cells (by omega)
    (fun _ ha hA => perfectCoreCell_cent_of_twoA ha hA (by
      rw [card_nativeB]; exact hpB))
    (fun _ hz => perfectCoreCell_cent_of_twoB hz (by omega) isPerfect_Co1 hpZ)

theorem kernelTrivialAt_MGriess_of_baby_co1 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hB : KernelTrivialAt NativeSporadic.B p) (hCo1 : KernelTrivialAt NativeSporadic.Co1 p) :
    KernelTrivialAt MGriess p :=
  kernelTrivialAt_MGriess_of_cells hp2
    (fun _ ha hA => perfectCoreCell_cent_of_twoA_of_kt ha hA (by omega) hB)
    (fun _ hz => perfectCoreCell_cent_of_twoB_of_kt hz (by omega) isPerfect_Co1 hCo1)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

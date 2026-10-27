module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieSet
public import CFSG.LocalAnalysis.EvenBN.U5.Model
public import CFSG.LocalAnalysis.EvenBN.U5.ModelLevi
public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieDefs
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Stab
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamStd
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] def un5c_A (s : K) : Matrix (Fin 2) (Fin 2) K := !![1, s; 0, 1]

@[expose] def un5c_Y (a b c : K) : Matrix (Fin 2) (Fin 2) K := !![a, b; b, c]

theorem un5c_det (s : K) : (un5c_A s).det = 1 := by
  simp [un5c_A, Matrix.det_fin_two]

theorem un5c_isUnit (s : K) : IsUnit (un5c_A s).det := by
  rw [un5c_det]
  exact isUnit_one

theorem un5c_isHerm {a b c : K} (ha : hK.bar a = a) (hb : hK.bar b = b) (hc : hK.bar c = c) :
    IsHerm hK (un5c_Y a b c) := by
  rw [isHerm_iff]
  simp [un5c_Y, ha, hb, hc]

@[expose] def un5c_g (s a b c : hK.fixedField) : hypSU hK 2 1 :=
  lev (un5c_A (s : K)) (un5c_isUnit _) *
    vSU hK (un5c_Y (a : K) b c) (un5c_isHerm hK a.2 b.2 c.2)

theorem un5c_mat_g (s a b c : hK.fixedField) :
    mat (un5c_g hK s a b c) =
      oddDiag hK (un5c_A (s : K)) 1 * oddUni hK 0 (un5c_Y (a : K) b c) := by
  rw [un5c_g, mat_mul, mat_lev, mat_vSU, un5c_det]
  simp

theorem un5c_g_mem_U (s a b c : hK.fixedField) :
    un5c_g hK s a b c ∈ hypUnitriangular hK 2 1 := by
  have hs : IsUnitriangular (un5c_A (s : K)) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [un5c_A] at hij ⊢
    · fin_cases i <;> simp [un5c_A]
  have hC : un5c_Y (a : K) b c + ((un5c_Y (a : K) b c).map hK.bar)ᵀ =
      -vecMulVec (0 : Fin 2 → K) (fun j => hK.bar ((0 : Fin 2 → K) j)) := by
    have h0 : vecMulVec (0 : Fin 2 → K) (fun j => hK.bar ((0 : Fin 2 → K) j)) = 0 := by
      ext i j
      simp [vecMulVec]
    rw [h0, neg_zero]
    exact un5c_isHerm hK a.2 b.2 c.2
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_odd_iff (h := hK) (r := 2)
    (oddDiag hK (un5c_A (s : K)) 1 * oddUni hK 0 (un5c_Y (a : K) b c))).2
    ⟨_, _, 0, hs, hC, rfl⟩
  rwa [← mat_injective (hgm.trans (un5c_mat_g hK s a b c).symm)]

theorem un5c_mat_fieldAut (σ : K ≃+* K) (g : hypSU hK 2 1) :
    mat (fieldAut hK σ g) = (mat g).map σ := rfl

theorem un5c_barInvT (s : hK.fixedField) :
    barInvT hK (un5c_A (s : K)) = !![1, 0; -(s : K), 1] := by
  symm
  apply eq_barInvT_of_mul_eq_one
  have hs : hK.bar (s : K) = s := s.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [un5c_A, Matrix.mul_apply, Fin.sum_univ_two, hs]

theorem un5c_fieldAut_g (s a b c : hK.fixedField) :
    fieldAut hK (bar5 hK) (un5c_g hK s a b c) = un5c_g hK s a b c := by
  apply mat_injective
  rw [un5c_mat_fieldAut, un5c_mat_g, oddDiag_mul_oddUni, un5c_barInvT]
  have hs : hK.bar (s : K) = s := s.2
  have ha : hK.bar (a : K) = a := a.2
  have hb : hK.bar (b : K) = b := b.2
  have hc : hK.bar (c : K) = c := c.2
  ext x y
  rcases x with i | k | i <;> rcases y with j | l | j <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [fld5_bar_apply, un5c_A, un5c_Y, hs, ha, hb, hc]

theorem un5c_comm {g : hypSU hK 2 1} (hg : fieldAut hK (bar5 hK) g = g) :
    fieldP hK (bar5 hK) * innM hK g = innM hK g * fieldP hK (bar5 hK) := by
  have h1 := aut5_mul_cj5_mul_inv hK (fieldP hK (bar5 hK)) (hypProj hK 2 1 g)
  rw [fieldP_apply, hg] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem un5c_g_inj {s a b c s' a' b' c' : hK.fixedField}
    (h : un5c_g hK s a b c = un5c_g hK s' a' b' c') : s = s' ∧ a = a' ∧ b = b' ∧ c = c' := by
  have h1 := congrArg mat h
  rw [un5c_mat_g, un5c_mat_g] at h1
  obtain ⟨hA, -, hY, -⟩ := oddProd_inj (un5c_isUnit _) h1
  have e1 := congrFun (congrFun hA 0) 1
  have e2 := congrFun (congrFun hY 0) 0
  have e3 := congrFun (congrFun hY 0) 1
  have e4 := congrFun (congrFun hY 1) 1
  simp [un5c_A, un5c_Y] at e1 e2 e3 e4
  exact ⟨e1, e2, e3, e4⟩

theorem un5_card_fixUh_ge {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K) :
    (2 ^ f) ^ 4 ≤ Nat.card ↥(Uh hK ⊓ Subgroup.centralizer
      ({fieldP hK (bar5 hK)} : Set (MulAut (hypPSU hK 2 1)))) := by
  have := finite_mulAut_hyp hK
  let φ : (hK.fixedField × hK.fixedField × hK.fixedField × hK.fixedField) →
      ↥(Uh hK ⊓ Subgroup.centralizer
        ({fieldP hK (bar5 hK)} : Set (MulAut (hypPSU hK 2 1)))) :=
    fun p => ⟨innM hK (un5c_g hK p.1 p.2.1 p.2.2.1 p.2.2.2),
      ⟨_, un5c_g_mem_U hK _ _ _ _, rfl⟩,
      Subgroup.mem_centralizer_iff.2 fun x hx => by
        rw [Set.mem_singleton_iff.1 hx]
        exact un5c_comm hK (un5c_fieldAut_g hK _ _ _ _)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨s, a, b, c⟩ ⟨s', a', b', c'⟩ h
    have h1 := congrArg Subtype.val h
    obtain ⟨e1, e2, e3, e4⟩ := un5c_g_inj hK (innM_injOn (u5_center_eq_bot hK)
      (un5c_g_mem_U hK _ _ _ _) (un5c_g_mem_U hK _ _ _ _) h1)
    exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))
  calc (2 ^ f) ^ 4
      = Nat.card (hK.fixedField × hK.fixedField × hK.fixedField × hK.fixedField) := by
        simp only [Nat.card_prod, hK.card_fixedField]
        ring
    _ ≤ _ := Nat.card_le_card_of_injective φ hinj

end CFSG.Quasithin.H13.F431.Un.OL5

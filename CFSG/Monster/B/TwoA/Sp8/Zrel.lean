
module

public import CFSG.Monster.B.TwoA.Sp8.ZrelBase

public import CFSG.Monster.B.TwoA.Sp8.Psi
public meta import CFSG.Monster.B.TwoA.Co2Inv.SixAction
public import CFSG.Monster.B.TwoA.Sp8.ZrelInputs
public import Certificates.Certificate3059
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8
public import CFSG.Monster.B.TwoA.Co2Inv.SixAction
public import CFSG.Monster.B.TwoA.Base.Space34A
public import CFSG.Monster.B.TwoA.Sp8.PsiInputs
public import CFSG.Monster.B.TwoA.Base.PairSpace
public import CFSG.Monster.B.TwoA.Base.Space34AInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.VisCert CFSG.Monster.B.Co2

@[expose] def psiB
    (v : Fin 8 → ZMod 2) : Wv v0 :=
    psiW
    ⟨PhiD v, B7_le_Ehat (PhiD_mem_B7 v)⟩

theorem psiB_add
    (v w : Fin 8 → ZMod 2) : psiB
    (v + w) = psiB v +
    psiB w := by
  rw [psiB, psiB, psiB, ← psiW_mul]
  congr 1
  exact Subtype.ext (PhiD_add v w)

theorem psiB_zero :
    psiB 0 = 0 := by
  have h : psiB 0 + psiB 0 = psiB 0 + 0 := by rw [← psiB_add, add_zero, add_zero]
  exact add_left_cancel h

theorem psiB_congr
    {v : Fin 8 → ZMod 2} {e : Ehat}
    (h : PhiD v = (e : Dfull)) :
    psiB v = psiW e := by
  rw [psiB]
  congr 1
  exact Subtype.ext h

theorem psiB_single
    (k : Fin 8) : psiB (Pi.single k 1) = psiGen k :=
    by
  fin_cases k
  · exact (psiB_congr (e := xhatE) PhiD_single_zero).trans psiW_xhatE
  · exact (psiB_congr (e := yhatE) PhiD_single_one).trans psiW_yhat8
  · exact (psiB_congr (e := dhatE 2 3) PhiD_single_two).trans psiW_d23
  · exact (psiB_congr (e := dhatE 2 4) PhiD_single_three).trans psiW_d24
  · exact (psiB_congr (e := dhatE 2 5) PhiD_single_four).trans psiW_d25
  · exact (psiB_congr (e := dhatE 2 6) PhiD_single_five).trans psiW_d26
  · exact (psiB_congr (e := uhatE) PhiD_single_six).trans psiW_uhat
  · exact (psiB_congr (e := 1) PhiD_seven).trans psiW_one

theorem psiB_single_smul
    (k : Fin 8) (a : ZMod 2) : psiB
    (Pi.single k a) = a • psiGen k := by
  rcases zmod2_cases a with rfl | rfl
  · rw [Pi.single_zero, psiB_zero, zero_smul]
  · rw [psiB_single, one_smul]

theorem psiB_mem
    (v : Fin 8 → ZMod 2) : psiB v ∈ Zsp := by
  have hv : v = ∑ k : Fin 8, Pi.single k (v k) := (Finset.univ_sum_single v).symm
  rw [hv]
  refine Finset.sum_induction _ (fun w => psiB w ∈ Zsp) (fun a b ha hb => ?_) ?_ fun k _ => ?_
  · rw [psiB_add]
    exact Zsp.add_mem ha hb
  · rw [psiB_zero]
    exact Zsp.zero_mem
  · rw [psiB_single_smul]
    exact Zsp.smul_mem _ (psiGen_mem k)

theorem exists_psiB
    {x : Wv v0} (hx : x ∈ Zsp) : ∃ v : Fin 8 → ZMod
    2, psiB v = x := by
  rw [← span_bVec, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  refine ⟨Pi.single (1 : Fin 8) (c 0) + Pi.single (2 : Fin 8) (c 1) +
    Pi.single (3 : Fin 8) (c 2) + Pi.single (4 : Fin 8) (c 3) + Pi.single (5 : Fin 8) (c 4) +
    Pi.single (6 : Fin 8) (c 5), ?_⟩
  simp only [psiB_add, psiB_single_smul, Fin.sum_univ_six]
  rfl

theorem mem_B7_iff
    (x : Dfull) : x ∈ B7 ↔ ∃ h : x ∈ Ehat, psiW ⟨x, h⟩
    ∈ Zsp := by
  constructor
  · intro hx
    refine ⟨B7_le_Ehat hx, ?_⟩
    rw [B7_eq_range] at hx
    obtain ⟨v, rfl⟩ := hx
    exact psiB_mem v.toAdd
  · rintro ⟨h, hz⟩
    obtain ⟨v, hv⟩ := exists_psiB hz
    have hP := B7_le_Ehat (PhiD_mem_B7 v)
    have h0 : psiW (⟨x, h⟩ * (⟨PhiD v, hP⟩ : Ehat)⁻¹) = 0 := by
      rw [psiW_mul, psiW_inv]
      change psiW ⟨x, h⟩ + -psiB v = 0
      rw [hv, add_neg_cancel]
    rcases (psiW_eq_zero_iff _).1 h0 with h1 | h1
    · have h2 : x * (PhiD v)⁻¹ = 1 := congrArg Subtype.val h1
      rw [mul_inv_eq_one.1 h2]
      exact PhiD_mem_B7 v
    · have h2 : x * (PhiD v)⁻¹ = xhat := congrArg Subtype.val h1
      rw [mul_inv_eq_iff_eq_mul.1 h2, ← PhiD_single_zero]
      exact B7.mul_mem (PhiD_mem_B7 _) (PhiD_mem_B7 v)

theorem cGen_nine :
    cGen ⟨9, by norm_num⟩ = rK := by
  rw [cGen_of_ge (by norm_num)]
  rfl

theorem wAct_rK :
    wAct v0 rK = rowsEnd (cRows 9) := by
  rw [← cGen_nine, wAct_cGen]

theorem rImg_spec : ∀ t < 22, rImg[t]! = (cRows 9)[t]! ^^^ 2 ^ t :=
  Certificates.certificate3059.1

theorem rImg_comb : ∀ t < 22, Native.actD 6 zBasis
    ([0, 2, 2, 2, 2, 2, 4, 14, 38, 0, 0, 23, 23, 23, 23, 23, 23, 22, 22, 22, 22, 22].getD t 0) =
      rImg[t]! :=
  Certificates.certificate3059.2.1

theorem zBasis_rComb : ∀ t : Fin 6, Native.actD 22 rImg
    ([133120, 2, 64, 194, 131138, 322].getD t 0) = zBasis[(t : ℕ)]! :=
  Certificates.certificate3059.2.2

theorem rK_sub_one_qbW
    (t : Fin 22) : (wAct v0 rK - 1)
    (qbW t) = decW
    rImg[(t : ℕ)]! := by
  rw [LinearMap.sub_apply, wAct_rK, rowsEnd_qbW, Module.End.one_apply, ← decW_two_pow,
    sub_eq_add_neg, ZModModule.neg_eq_self, ← decW_xor, rImg_spec t t.2]

theorem range_rK_sub_one :
    LinearMap.range
    (wAct v0 rK - 1) = Zsp :=
    by
  have hf : (fun t : Fin 22 => decW rImg[(t : ℕ)]!) = ⇑(wAct v0 rK - 1) ∘ ⇑qbWBasis := by
    funext t
    rw [Function.comp_apply, qbWBasis_apply, rK_sub_one_qbW]
  have hspan : LinearMap.range (wAct v0 rK - 1) =
      Submodule.span (ZMod 2) (Set.range fun t : Fin 22 => decW rImg[(t : ℕ)]!) := by
    rw [hf, Set.range_comp, ← Submodule.map_span, qbWBasis.span_eq, Submodule.map_top]
  rw [hspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    show decW rImg[(t : ℕ)]! ∈ Zsp
    rw [← rImg_comb t t.2]
    exact zComb_mem _
  · rw [Zsp, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    rw [zVec, ← zBasis_rComb t]
    exact decW_actD_mem_span rImg 22 _

end CFSG.Monster.B.TwoA.Sp8

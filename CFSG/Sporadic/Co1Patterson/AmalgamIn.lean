module

public import CFSG.Sporadic.Co1Patterson.AmalgamNative
public import CFSG.Sporadic.Co1Patterson.Rigid
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.NotConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Monster.GMS CFSG.Open
  CFSG.Sporadic.Co1Patterson.Native CFSG.LargeExtraspecial.S14
open CFSG.Blueprint (NativeSporadic.Co1)

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)


theorem tauT_two_mem_edgeStab : tauT 2 ∈ edgeStab vA vE :=
  mem_edgeStab.2 (Or.inr ⟨(locTri_spec 2).1.1, (locTri_spec 2).1.2.1⟩)

theorem edgeStab_mem_cent_vE {x : NativeSporadic.Co1} (hx : x ∈ edgeStab vA vE)
    (hxa : x ∈ C[aNC]) : x ∈ C[(vE : NativeSporadic.Co1)] := by
  rcases mem_edgeStab.1 hx with ⟨-, h⟩ | ⟨h, -⟩
  · exact (smul_eq_self_iff x vE).1 h
  · exact absurd (((smul_vA_eq_iff x).2 hxa).symm.trans h) vE_ne_vA.symm

theorem edgeStab_mul_inv_mem {x : NativeSporadic.Co1} (hx : x ∈ edgeStab vA vE)
    (hxa : x ∉ C[aNC]) : x * (tauT 2)⁻¹ ∈ C[aNC] := by
  rcases mem_edgeStab.1 hx with ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd ((smul_vA_eq_iff x).1 h) hxa
  · rw [← smul_vA_eq_iff, mul_smul, inv_smul_eq_iff.2 (locTri_spec 2).1.2.1.symm, h]

theorem kZero_mem_edgeStab : kZero ∈ edgeStab vA vE :=
  mem_edgeStab.2 (Or.inl ⟨(smul_vA_eq_iff _).2 (mem_inf.1 kZero_mem).1,
    (smul_eq_self_iff _ _).2 (mem_inf.1 kZero_mem).2⟩)

theorem triGrp_le (j : Fin 3) : triGrp j ≤ C[(wT j : NativeSporadic.Co1)] := inf_le_right

theorem kZero_conj_eq {j : Fin 3} (hj : (j : ℕ) ≠ 2) :
    kZero * (wT 2 : NativeSporadic.Co1) * kZero⁻¹ = (wT j : NativeSporadic.Co1) := by
  rw [kZero_conj]
  fin_cases j
  · rfl
  · rfl
  · exact absurd rfl hj

local notation "qW" => ((wT 2 : Vt) : NativeSporadic.Co1)

theorem exists_hom_of_rigid {X : Type} [Group X] [Finite X] {t : X} (h : PattersonCo1Hyp X t)
    (hw : NotWeaklyClosed h) (h1 : AutInnerModAt aNC qW)
    (h2 : AutRigidAt aNC (vE : NativeSporadic.Co1) qW) :
    ∃ Φ : NativeSporadic.Co1 →* X, Function.Injective Φ ∧ C[t] ≤ Φ.range := by
  obtain ⟨σ⟩ := nonempty_mulEquiv_centralizer h hw
  have haC : aNC ∈ C[aNC] := mem_centralizer_singleton_iff.2 rfl
  obtain ⟨A, hAdef⟩ : ∃ A : NativeSporadic.Co1 → X, A = extFun σ.symm := ⟨_, rfl⟩
  have hA : IsoOn A C[aNC] C[t] := by rw [hAdef]; exact isoOn_extFun σ.symm
  have hAval : ∀ x (hx : x ∈ C[aNC]), A x = σ.symm ⟨x, hx⟩ := fun x hx => by
    rw [hAdef, extFun_of_mem σ.symm hx]
  have hAa : A aNC = t := by
    rw [hAval _ haC]
    have hc : ∀ y : C[t], σ.symm ⟨aNC, haC⟩ * y = y * σ.symm ⟨aNC, haC⟩ := by
      intro y
      apply σ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (σ y).2).symm
    rcases TwistNative.setting_center_eq (setting h) (x := σ.symm ⟨aNC, haC⟩) hc with h1 | h1
    · exfalso
      have h0 : σ (σ.symm ⟨aNC, haC⟩) = σ 1 := congrArg σ h1
      rw [MulEquiv.apply_symm_apply, map_one] at h0
      have h0 := congrArg Subtype.val h0
      rw [OneMemClass.coe_one] at h0
      have h2' := orderOf_aNC
      rw [show aNC = 1 from h0, orderOf_one] at h2'
      exact absurd h2' (by norm_num)
    · exact congrArg Subtype.val h1
  have hqa : qW ∈ C[aNC] := wT_mem_cent_aNC 2
  have heC : (vE : NativeSporadic.Co1) ∈ C[aNC] := vE_mem_cent_aNC
  have hqe : qW ∈ C[(vE : NativeSporadic.Co1)] := wT_mem_cent_vE 2
  obtain ⟨hτw, hτa, hτe⟩ := tauT_two_conj
  obtain ⟨hρw, hρa, hρe⟩ := rhoT_two_conj
  have hWQ : A qW ∈ qOf t := hA.mem_qOf (wT_mem_qOf_aNC 2)
  have hW2 : orderOf (A qW) = 2 := by rw [hA.orderOf_eq hqa]; exact orderOf_vt (wT 2)
  have hWt : A qW ≠ t := by
    rw [← hAa]
    exact fun e => wT_ne_aNC 2 (hA.injOn hqa haC e)
  have hWconj : IsConj t (A qW) := isConj_of_mem_QG h hw hWQ hW2
  obtain ⟨⟨g, hg, hg1, hg2⟩, -, hT⟩ := exists_swap_trivModCore h hWQ hWconj hWt
  obtain ⟨⟨s, hs, hs1, hs2⟩, -, hT0⟩ := exists_swap_trivModCore pattersonCo1Hyp_native
    (wT_mem_qOf_aNC 2) (wT 2).2 (wT_ne_aNC 2)
  have hsO : ∀ k ∈ C[aNC] ⊓ C[qW], s⁻¹ * k * s * k⁻¹ ∈ coreOf (C[aNC] ⊓ C[qW]) := by
    intro k hk
    have := (mem_trivModCore.1 (inv_mem (hT0 hs))).2 k hk
    rwa [inv_inv] at this
  have hgO : ∀ k ∈ C[t] ⊓ C[A qW], g * k * g⁻¹ * k⁻¹ ∈ coreOf (C[t] ⊓ C[A qW]) :=
    fun k hk => (mem_trivModCore.1 (hT hg)).2 k hk
  obtain ⟨Z, hZ, hagree, -⟩ := exists_isoOn_agree hA hAa hqa rfl hs1 hs2 hg1 hg2 hsO hgO h1
  have hkey := keyId_of_rigid hA hAa heC hZ hqa hqe rfl hagree h2 aNC_mul_self
    (vt_mul_self vE) hτw hτa hτe hρw hρa hρe
  have hB1 : ∀ x ∈ edgeStab vA vE, x ∈ C[aNC] → x ∈ C[(vE : NativeSporadic.Co1)] :=
    fun x hx hxa => edgeStab_mem_cent_vE hx hxa
  have hB2 : ∀ x ∈ edgeStab vA vE, x ∉ C[aNC] → x * (tauT 2)⁻¹ ∈ C[aNC] :=
    fun x hx hxa => edgeStab_mul_inv_mem hx hxa
  have hFmul := edgeFun_mul hA hZ hagree hτw hτa hτe tauT_two_mem_edgeStab hB1 hB2 hkey
  have hFZ : ∀ x ∈ edgeStab vA vE, x ∈ C[qW] → edgeFun A Z aNC (tauT 2) x = Z x :=
    fun x hx hxw => edgeFun_eq_of_mem_cent hZ hagree hτw hB2 hx hxw
  let Ft : Fin 3 → NativeSporadic.Co1 → X := fun j => if (j : ℕ) = 2 then Z else conjFun A Z kZero
  have hFt2 : ∀ j : Fin 3, (j : ℕ) = 2 → Ft j = Z := fun j hj => by simp only [Ft, hj, ↓reduceIte]
  have hFt01 : ∀ j : Fin 3, (j : ℕ) ≠ 2 → Ft j = conjFun A Z kZero := fun j hj => by
    simp only [Ft, hj, ↓reduceIte]
  have hFt : ∀ j, ∀ x ∈ triGrp j, ∀ y ∈ triGrp j, Ft j (x * y) = Ft j x * Ft j y := by
    intro j x hx y hy
    by_cases hj : (j : ℕ) = 2
    · have hj' : j = 2 := Fin.ext hj
      subst hj'
      rw [hFt2 2 hj]
      exact hZ.map_mul _ (triGrp_le 2 hx) _ (triGrp_le 2 hy)
    · rw [hFt01 j hj]
      have hc := conjFun_mul (A := A) hZ (k := kZero)
      rw [kZero_conj_eq hj] at hc
      exact hc x (triGrp_le j hx) y (triGrp_le j hy)
  let φv : titsDataNative.Xv →* X := homOfMulOn A C[aNC] hA.map_mul
  let φe : titsDataNative.Xe →* X := homOfMulOn (edgeFun A Z aNC (tauT 2)) (edgeStab vA vE) hFmul
  let φt : ∀ j, titsDataNative.Xt j →* X := fun j => homOfMulOn (Ft j) (triGrp j) (hFt j)
  have hve : ∀ x (ha : x ∈ titsDataNative.Xv) (hb : x ∈ titsDataNative.Xe),
      φv ⟨x, ha⟩ = φe ⟨x, hb⟩ := fun x ha _ => (edgeFun_of_mem ha).symm
  have hvt : ∀ j x (ha : x ∈ titsDataNative.Xv) (hb : x ∈ titsDataNative.Xt j),
      φv ⟨x, ha⟩ = φt j ⟨x, hb⟩ := by
    intro j x ha hb
    show A x = Ft j x
    by_cases hj : (j : ℕ) = 2
    · have hj' : j = 2 := Fin.ext hj
      subst hj'
      rw [hFt2 2 hj, hagree x (mem_inf.2 ⟨ha, triGrp_le 2 hb⟩)]
    · rw [hFt01 j hj, conjFun_eq_A hA hagree (mem_inf.1 kZero_mem).1
        (mem_inf.2 ⟨ha, by rw [kZero_conj_eq hj]; exact triGrp_le j hb⟩)]
  have het : ∀ j x (ha : x ∈ titsDataNative.Xe) (hb : x ∈ titsDataNative.Xt j),
      φe ⟨x, ha⟩ = φt j ⟨x, hb⟩ := by
    intro j x ha hb
    show edgeFun A Z aNC (tauT 2) x = Ft j x
    by_cases hj : (j : ℕ) = 2
    · have hj' : j = 2 := Fin.ext hj
      subst hj'
      rw [hFt2 2 hj, hFZ x ha (triGrp_le 2 hb)]
    · rw [hFt01 j hj]
      exact (conjFun_eq_of hFmul hFZ kZero_mem_edgeStab (edgeFun_of_mem (mem_inf.1 kZero_mem).1)
        ha (by rw [kZero_conj_eq hj]; exact triGrp_le j hb)).symm
  obtain ⟨Φ, ⟨hΦv, -, -⟩, -⟩ := titsDataNative.existsUnique_hom φv φe φt hve hvt het
  have hΦ : ∀ x (hx : x ∈ C[aNC]), Φ x = A x := fun x hx => hΦv ⟨x, hx⟩
  refine ⟨Φ, titsDataNative.injective_of_isSimpleGroup CFSG.Sporadic.Co1.isSimpleGroup_Co1 Φ
    ⟨⟨aNC, haC⟩, ?_⟩, fun y hy => ⟨σ ⟨y, hy⟩, ?_⟩⟩
  · show Φ aNC ≠ 1
    rw [hΦ _ haC, hAa]
    intro e
    have := h.orderOf_eq
    rw [e, orderOf_one] at this
    exact absurd this (by norm_num)
  · rw [hΦ _ (σ ⟨y, hy⟩).2, hAval _ (σ ⟨y, hy⟩).2, Subtype.coe_eta, MulEquiv.symm_apply_apply]

end CFSG.Sporadic.Co1Patterson

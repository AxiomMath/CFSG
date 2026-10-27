module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatP
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR3S
public import CFSG.Quasithin.Background.HLUAlt6
public import CFSG.Quasithin.Background.HLURows

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.LU CFSG.Quasithin.H.LU24
  CFSG.Quasithin.E3 CFSG.Quasithin.H13 CFSG.Quasithin.B42Alt6 CFSG.Quasithin.S143

theorem pCoreOf_sxP0_le
    (hS : Nat.card ↥((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) ≤ 138240) :
    pCoreOf 2 (imgCd sxP0) ≤ imgCd sxKS := by
  obtain ⟨-, hρ, -, hKP, hKn, -, hKC, hCK⟩ := lu_code_std hS
  let ι : ↥(alternatingGroup (Fin 6)) ≃* ↥(autSub (imgCd sxP0) US) :=
    ((alternatingGroup (Fin 6)).equivMapOfInjective _ (rhoOf_injective usTheta)).trans
      (MulEquiv.subgroupCongr hρ)
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥(autSub (imgCd sxP0) US) := ι.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(autSub (imgCd sxP0) US), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := a6_noncomm
    exact ⟨ι a, ι b, fun h => hab (ι.injective (by rw [map_mul, map_mul, h]))⟩
  exact pCoreOf_le_of_index_three imgCd_P0_le_stab hnc hKP hKn hKC hCK

theorem row3_std_B
    (hS : Nat.card ↥((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) ≤ 138240)
    (Xs : Subgroup (MulAut W11))
    (hXN : Xs ≤ Subgroup.normalizer ((rhoC11 AutPerm le_rfl).range : Set (MulAut W11)))
    (hU : fixV Xs = US) :
    s828BPrime (rhoC11 AutPerm le_rfl).range Xs = maskSub 11 mb3L10 := by
  obtain ⟨hPS, -⟩ := lu_code_std hS
  have hP : perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub (fixV Xs)) = imgCd sxP0 :=
    (congrArg (fun U => perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub U)) hU).trans hPS
  have e1 : s828BPrime (rhoC11 AutPerm le_rfl).range Xs =
      commV Xs ⊔ commV (imgCd sxP0) ⊔ US :=
    congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) rfl (congrArg commV hP)) hU
  have hidx : (commV (imgCd sxP0) ⊔ US).index = 2 := by
    have h1 : (commV (imgCd sxP0) ⊔ US).index = (maskSub 11 mb3L10).index :=
      congrArg Subgroup.index std3_commV_sup
    exact h1.trans ((index_maskSub mb3L10_lt mb3L10_nodup).trans (by decide))
  have hconj : ∀ x ∈ Xs, ∀ y ∈ imgCd sxP0, x * y * x⁻¹ ∈ imgCd sxP0 := by
    intro x hx y hy
    have hxH : x ∈ (rhoC11 AutPerm le_rfl).range := by
      have := hXN hx
      rwa [normalizer_rhoC11_autPerm] at this
    have hxs : x ∈ stabSub US := by
      refine centSub_le_stabSub US ?_
      intro u hu
      exact (mem_fixV.1 (hU ▸ hu)) x hx
    set N := (rhoC11 AutPerm le_rfl).range ⊓ stabSub US with hN
    have hxN : x ∈ N := ⟨hxH, hxs⟩
    have hyP : y ∈ perfectCore N := hPS ▸ hy
    have hyN : y ∈ N := perfectCore_le N hyP
    have h1 := (perfectCore_normal N).conj_mem ⟨y, hyN⟩
      (Subgroup.mem_subgroupOf.2 hyP) ⟨x, hxN⟩
    have h2 : x * y * x⁻¹ ∈ perfectCore N := Subgroup.mem_subgroupOf.1 h1
    exact hPS ▸ h2
  have hcomm : commV Xs ≤ commV (imgCd sxP0) ⊔ US := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    refine comm_mem_of_index_two_mat (hconj x hx) (fun u hu => ?_) hidx v
    exact (mem_fixV.1 (hU ▸ hu)) x hx
  exact e1.trans ((sup_assoc _ _ _).trans ((sup_eq_right.2 hcomm).trans std3_commV_sup))

theorem row3_classify
    {V : Type} [CommGroup V]
    [Finite V] {H X : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rkIdx (fixV X) = 7) :
    ∃ e : V ≃* W11, H.map (congrHom e) = (rhoC11 AutPerm le_rfl).range ∧
      fixV (X.map (congrHom e)) = US := by
  obtain ⟨e₀, he₀⟩ := code24_std h
  have hV : ∀ v : V, v ^ 2 = 1 := sq_eq_one_of_equiv e₀
  have hVc : Nat.card V = 2 ^ 11 := card_of_equiv e₀
  have hXc : Nat.card ↥X = 2 ^ 6 := hX ▸ card_eq_of_isElemAbelian2 hXe
  have hrk : rk V = 11 := by
    unfold rk
    rw [hVc, padicValNat.prime_pow]
  have hfr : rk ↥(fixV X) = 4 := by
    have := CFSG.Quasithin.rk_add_rkIdx (fixV X)
    omega
  have hfXc : Nat.card ↥(fixV X) = 2 ^ 4 := hfr ▸ card_eq_two_pow hV (fixV X)
  obtain ⟨g, hXU⟩ := fixV_eq_US he₀ hXc hfXc hXN (isElemAbelian2_iff.1 hXe)
  have hH : H.map (congrHom (twistEquiv e₀ psiC24 g)) = (rhoC11 AutPerm le_rfl).range :=
    (map_congrHom_trans e₀ (psiC24 g) H).trans
      ((congrArg (fun K => K.map (congrHom (psiC24 g))) he₀).trans
        (map_congrHom_self (⟨g, rfl⟩ : psiC24 g ∈ (rhoC11 AutPerm le_rfl).range)))
  exact ⟨twistEquiv e₀ psiC24 g, hH, hXU⟩

section Final

variable
  {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}

private theorem row3_data
    (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rkIdx (fixV X) = 7) :
    ∃ e : V ≃* W11, H.map (congrHom e) = (rhoC11 AutPerm le_rfl).range ∧
      s828BPrime (rhoC11 AutPerm le_rfl).range (X.map (congrHom e)) = maskSub 11 mb3L10 ∧
      perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub (fixV (X.map (congrHom e)))) =
        imgCd sxP0 ∧ fixV (X.map (congrHom e)) = US := by
  obtain ⟨e, hH, hU⟩ := row3_classify hXN hXe h hX hfX
  have hS := card_stab_US_le
  have hXN' : X.map (congrHom e) ≤
      Subgroup.normalizer (((rhoC11 AutPerm le_rfl).range : Subgroup (MulAut W11)) :
        Set (MulAut W11)) := by
    have := map_le_normalizer_congrHom e hXN
    rwa [hH] at this
  refine ⟨e, hH, row3_std_B hS _ hXN' hU, ?_, hU⟩
  exact (congrArg (fun U => perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub U)) hU).trans
    (lu_code_std hS).1

theorem mb0_row3 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rkIdx (fixV X) = 7) :
    mQuot ⊤ (s828BPrime H X) = 1 := by
  obtain ⟨e, hH, hB, -, -⟩ := row3_data hXN hXe h hX hfX
  exact (mb0_of_map' e H X _ _ hH rfl).trans ((congrArg (mQuot ⊤) hB).trans std3_mQuot)

theorem mb1_row3 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rkIdx (fixV X) = 7) :
    s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X =
      s828BPrime H X := by
  obtain ⟨e, hH, hB, hP, hU⟩ := row3_data hXN hXe h hX hfX
  refine mb1_eq_of_map' e H X _ _ hH rfl ?_
  have h1 : s828CommSub (perfectCore ((rhoC11 AutPerm le_rfl).range ⊓
        stabSub (fixV (X.map (congrHom e))))) (s828BPrime (rhoC11 AutPerm le_rfl).range
        (X.map (congrHom e))) ⊔ fixV (X.map (congrHom e)) =
      s828CommSub (imgCd sxP0) (maskSub 11 mb3L10) ⊔ US :=
    congrArg₂ (· ⊔ ·) (congrArg₂ s828CommSub hP hB) hU
  exact h1.trans (std3_MB1.trans hB.symm)

theorem mb3_row3 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rkIdx (fixV X) = 7) :
    ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))), ∀ b ∈ s828BPrime H X,
      x b * b⁻¹ ∈ fixV X := by
  obtain ⟨e, hH, hB, hP, hU⟩ := row3_data hXN hXe h hX hfX
  refine mb3_of_map' e H X _ _ hH rfl ?_
  intro x hx b hb
  have hx' : x ∈ pCoreOf 2 (imgCd sxP0) :=
    Eq.mp (congrArg (fun K => x ∈ pCoreOf 2 K) hP) hx
  have hxK : x ∈ imgCd sxKS := pCoreOf_sxP0_le card_stab_US_le hx'
  have hb' : b ∈ maskSub 11 mb3L10 := Eq.mp (congrArg (fun K => b ∈ K) hB) hb
  have := std3_trivK x hxK b hb'
  exact Eq.mpr (congrArg (fun K => x b * b⁻¹ ∈ K) hU) this

end Final

end CFSG.Quasithin.H13.Mat

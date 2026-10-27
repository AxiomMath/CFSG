module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828MBStd1
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SMB
public import CFSG.Quasithin.Background.HLURows
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H.L34Z CFSG.Quasithin.H.LU
  CFSG.Quasithin.E3 CFSG.Quasithin.H13.Ch9.Herm9

theorem row1_transport_mb {V : Type} [CommGroup V] [Finite V]
    {H X : Subgroup (MulAut V)} (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian2 X) (h : BinaryNineTensor H ⊤ ⊥ 1) (hX : rk ↥X = 4)
    (hfX : rk ↥(fixV X) = 4) :
    ∃ e : V ≃* W9, H.map (congrHom e) = img9 ∧ X.map (congrHom e) = QW9 ∧
      (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) = P2 := by
  obtain ⟨e₀, he₀⟩ := exists_equiv_w9 h
  have hV : ∀ v : V, v ^ 2 = 1 := sq_eq_one_of_equiv e₀
  have hXc : Nat.card ↥X = 2 ^ 4 := hX ▸ card_eq_of_isElemAbelian2 hXe
  have hfXc : Nat.card ↥(fixV X) = 2 ^ 4 := hfX ▸ card_eq_two_pow hV (fixV X)
  have hX'N := map_le_normalizer_congrHom e₀ hXN
  rw [he₀] at hX'N
  obtain ⟨c, hc, hcX⟩ := exists_conj_eq_QW9 hX'N
    (isElemAbelian_map_hom (isElemAbelian2_iff.1 hXe) _)
    ((card_map_congrHom e₀ X).trans hXc) ((card_fixV_map_congrHom e₀ X).trans hfXc)
  have hH : H.map (congrHom (e₀.trans c)) = img9 :=
    (map_congrHom_trans e₀ c H).trans ((congrArg (fun K => K.map (congrHom c)) he₀).trans
      (map_congrHom_of_mem_normalizer hc))
  have hXQ : X.map (congrHom (e₀.trans c)) = QW9 :=
    (map_congrHom_trans e₀ c X).trans ((map_congrHom_self_eq_conj c _).trans
      (hcX.trans QW9_eq_Q2.symm))
  have hXU : fixV (X.map (congrHom (e₀.trans c))) = U0 := (congrArg fixV hXQ).trans fixV_QW9
  have hPe : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom (e₀.trans c)) = P2 :=
    (perfectCore_inf_stab_map (e₀.trans c) H X).trans
      ((congrArg (fun K => perfectCore (K ⊓ stabSub (fixV (X.map (congrHom (e₀.trans c))))))
        hH).trans (by rw [hXU]; exact perfectCore_stab_U0))
  exact ⟨e₀.trans c, hH, hXQ, hPe⟩

theorem sBPrime_map_row1_mb {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}
    (e : V ≃* W9) (hX : X.map (congrHom e) = QW9)
    (hP : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) = P2) :
    (s828BPrime H X).map e.toMonoidHom = BStd_mb := by
  unfold s828BPrime
  have h1 : (CFSG.Quasithin.commV X).map e.toMonoidHom = CFSG.Quasithin.commV QW9 :=
    (commV_map_congrHom e X).symm.trans (congrArg CFSG.Quasithin.commV hX)
  have h2 : (CFSG.Quasithin.commV (perfectCore (H ⊓ stabSub (fixV X)))).map e.toMonoidHom =
      CFSG.Quasithin.commV P2 :=
    (commV_map_congrHom e _).symm.trans (congrArg CFSG.Quasithin.commV hP)
  have h3 : (fixV X).map e.toMonoidHom = U0 :=
    ((fixV_map_congrHom e X).symm.trans (congrArg fixV hX)).trans fixV_QW9
  rw [Subgroup.map_sup, Subgroup.map_sup, h1, h2, h3]

theorem mQuot_top_map_mb {V W : Type} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (B : Subgroup V) : mQuot ⊤ (B.map e.toMonoidHom) = mQuot ⊤ B := by
  unfold mQuot
  have h := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) B ⊤ e.injective
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h
  rw [h]

theorem mb0_row1_mb : ∀ (V : Type) [CommGroup V] [Finite V]
    (H X : Subgroup (MulAut V)), X ≤ Subgroup.normalizer (H : Set (MulAut V)) →
    IsElemAbelian2 X → (BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) →
      mQuot ⊤ (s828BPrime H X) = 1 := by
  intro V _ _ H X hXN hXe hrow
  obtain ⟨e, hH, hX, hP⟩ := row1_transport_mb hXN hXe hrow.1 hrow.2.1 hrow.2.2
  calc mQuot ⊤ (s828BPrime H X) = mQuot ⊤ ((s828BPrime H X).map e.toMonoidHom) :=
        (mQuot_top_map_mb e _).symm
    _ = mQuot ⊤ BStd_mb := congrArg (mQuot ⊤) (sBPrime_map_row1_mb e hX hP)
    _ = 1 := mbMB0_std_mb

theorem mb3_row1_mb : ∀ (V : Type) [CommGroup V] [Finite V]
    (H X : Subgroup (MulAut V)), X ≤ Subgroup.normalizer (H : Set (MulAut V)) →
    IsElemAbelian2 X → (BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) →
      ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))),
        ∀ b ∈ s828BPrime H X, x b * b⁻¹ ∈ fixV X := by
  intro V _ _ H X hXN hXe hrow x hx b hb
  obtain ⟨e, hH, hX, hP⟩ := row1_transport_mb hXN hXe hrow.1 hrow.2.1 hrow.2.2
  have hS := sBPrime_map_row1_mb e hX hP
  have hfixU : (fixV X).map e.toMonoidHom = U0 :=
    ((fixV_map_congrHom e X).symm.trans (congrArg fixV hX)).trans fixV_QW9
  have hxQ : congrHom e x ∈ QW9 := by
    have h1 : congrHom e x ∈ (pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X)))).map (congrHom e) :=
      Subgroup.mem_map_of_mem _ hx
    have E : (pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X)))).map (congrHom e) =
        pCoreOf 2 P2 :=
      (pCoreOf_map_congrHom e _).symm.trans (congrArg (pCoreOf 2) hP)
    have h2 : congrHom e x ∈ pCoreOf 2 P2 := by
      rw [← E]
      exact h1
    exact pCoreOf_P2_le h2
  have hbB : e b ∈ BStd_mb := by
    rw [← hS]
    exact Subgroup.mem_map_of_mem _ hb
  have key := mbMB3_std_mb _ hxQ _ hbB
  have hpull : e (x b * b⁻¹) ∈ (fixV X).map e.toMonoidHom := by
    rw [hfixU]
    have e1 : e (x b * b⁻¹) = congrHom e x (e b) * (e b)⁻¹ := by
      have hs : e.symm (e b) = b := e.symm_apply_apply b
      show e (x b * b⁻¹) = e (x (e.symm (e b))) * (e b)⁻¹
      rw [hs, map_mul, map_inv]
    rw [e1]
    exact key
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hpull
  have hyb : y = x b * b⁻¹ := e.injective hye
  rw [← hyb]
  exact hy

end CFSG.Quasithin.H13

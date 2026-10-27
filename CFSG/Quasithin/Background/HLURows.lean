module

public import CFSG.Quasithin.Background.HLUL34
public import CFSG.Quasithin.Background.HLUCode22
public import CFSG.Quasithin.Background.HFL3W9
public import CFSG.Quasithin.Background.HFCode22U
public import CFSG.Quasithin.Background.HParabQW
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.HMathieuO2Data
public import CFSG.Quasithin.Background.HModelTransp

public section

namespace CFSG.Quasithin.H.LU

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9

theorem wn_sq (n : ℕ) (w : Wn n) : w ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  show 2 • Multiplicative.toAdd w i = 0
  generalize Multiplicative.toAdd w i = a
  revert a
  decide

theorem sq_eq_one_of_equiv {V : Type*} [CommGroup V] {n : ℕ} (e : V ≃* Wn n) (v : V) :
    v ^ 2 = 1 :=
  e.injective (by rw [map_pow, wn_sq, map_one])

theorem card_of_equiv {V : Type*} [CommGroup V] {n : ℕ} (e : V ≃* Wn n) : Nat.card V = 2 ^ n :=
  (Nat.card_congr e.toEquiv).trans (natCard_Wn n)

theorem card_eq_of_isElemAbelian2 {V : Type*} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)}
    (hXe : IsElemAbelian2 X) : Nat.card ↥X = 2 ^ rk ↥X := by
  have : Finite (MulAut V) := finite_mulAut_z (V := V)
  exact card_eq_two_pow_of_isPGroup
    (isPGroup_two_of_sq_eq_one fun x => Subtype.ext (hXe.2 x x.2))

theorem luRow_L34 {V : Type} [CommGroup V] [Finite V]
    {H X : Subgroup (MulAut V)} (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian2 X) (h : BinaryNineTensor H ⊤ ⊥ 1) (hX : rk ↥X = 4)
    (hfX : rk ↥(fixV X) = 4) :
    (CFSG.IsQuasisimple (↥(perfectCore (H ⊓ stabSub (fixV X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabSub (fixV X)))) ∧
      AlternatingNatural (V := ↥(fixV X)) (autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X))
        ⊤ ⊥ 5) ∧ Nat.card V = 2 ^ 9 := by
  obtain ⟨e₀, he₀⟩ := exists_equiv_w9 h
  have hV : ∀ v : V, v ^ 2 = 1 := sq_eq_one_of_equiv e₀
  have hXc : Nat.card ↥X = 2 ^ 4 := hX ▸ card_eq_of_isElemAbelian2 hXe
  have hfXc : Nat.card ↥(fixV X) = 2 ^ 4 := hfX ▸ card_eq_two_pow hV (fixV X)
  have hX'N := map_le_normalizer_congrHom e₀ hXN
  rw [he₀] at hX'N
  obtain ⟨c, hc, hcX⟩ := exists_conj_eq_QW9 hX'N (isElemAbelian_map_hom
    (isElemAbelian2_iff.1 hXe) _) ((card_map_congrHom e₀ X).trans hXc)
    ((card_fixV_map_congrHom e₀ X).trans hfXc)
  have hH : H.map (congrHom (e₀.trans c)) = img9 :=
    (map_congrHom_trans e₀ c H).trans ((congrArg (fun K => K.map (congrHom c)) he₀).trans
      (map_congrHom_of_mem_normalizer hc))
  have hXQ : X.map (congrHom (e₀.trans c)) = L34Z.QW9 :=
    (map_congrHom_trans e₀ c X).trans ((map_congrHom_self_eq_conj c _).trans
      (hcX.trans L34Z.QW9_eq_Q2.symm))
  have hXU : fixV (X.map (congrHom (e₀.trans c))) = L34Z.U0 :=
    (congrArg fixV hXQ).trans L34Z.fixV_QW9
  have hPe : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom (e₀.trans c)) = L34Z.P2 :=
    (perfectCore_inf_stab_map (e₀.trans c) H X).trans
      ((congrArg (fun K => perfectCore (K ⊓ stabSub (fixV (X.map (congrHom (e₀.trans c))))))
        hH).trans (by rw [hXU]; exact L34Z.perfectCore_stab_U0))
  exact ⟨lu_A5_of_std (e₀.trans c) hPe hXU L34Z.card_P2 L34Z.card_autSub_P2_le L34Z.luX_mem
    L34Z.luY_mem L34Z.luBeta L34Z.luBeta_X L34Z.luBeta_Y, card_of_equiv e₀⟩

theorem luRow_M22
    {V : Type} [CommGroup V] [Finite V]
    {H X : Subgroup (MulAut V)} (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian2 X) (h : MathieuCode22 H ⊤ ⊥) (hX : rk ↥X = 5)
    (hfX : rkIdx (fixV X) = 6) :
    (CFSG.IsQuasisimple (↥(perfectCore (H ⊓ stabSub (fixV X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabSub (fixV X)))) ∧
      AlternatingNatural (V := ↥(fixV X)) (autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X))
        ⊤ ⊥ 5) ∧ Nat.card V = 2 ^ 10 := by
  obtain ⟨e₀, -⟩ := code22_std h
  have hV : ∀ v : V, v ^ 2 = 1 := sq_eq_one_of_equiv e₀
  have hVc : Nat.card V = 2 ^ 10 := card_of_equiv e₀
  have hXc : Nat.card ↥X = 2 ^ 5 := hX ▸ card_eq_of_isElemAbelian2 hXe
  have hrk : rk V = 10 := by
    unfold rk
    rw [hVc, padicValNat.prime_pow]
  have hfr : rk ↥(fixV X) = 4 := by
    have := rk_add_rkIdx (fixV X)
    omega
  have hfXc : Nat.card ↥(fixV X) = 2 ^ 4 := hfr ▸ card_eq_two_pow hV (fixV X)
  obtain ⟨e, he, hXU⟩ := code22_E32_std h hXN (isElemAbelian2_iff.1 hXe) hXc hfXc
  have hPe : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) = Code22.imgC Code22.hbQ :=
    (perfectCore_inf_stab_map e H X).trans
      ((congrArg (fun K => perfectCore (K ⊓ stabSub (fixV (X.map (congrHom e))))) he).trans
        (by rw [hXU]; exact Code22.perfectCore_stab_UC))
  exact ⟨lu_A5_of_std e hPe hXU Code22.card_imgC_hbQ Code22.card_autSub_hbQ_le Code22.luX_mem
    Code22.luY_mem Code22.luBeta Code22.luBeta_X Code22.luBeta_Y, hVc⟩

end CFSG.Quasithin.H.LU

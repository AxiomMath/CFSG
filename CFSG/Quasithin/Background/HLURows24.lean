module

public import CFSG.Quasithin.Background.HLURows
public import CFSG.Quasithin.Background.HLUCode24
public import CFSG.Quasithin.Background.HLUCoc24
public import CFSG.Quasithin.Background.HLUAlt6

public section

namespace CFSG.Quasithin.H.LU

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.Coc24 CFSG.Monster.Code

theorem luRow_Code24
    {V : Type} [CommGroup V]
    [Finite V] {H X : Subgroup (MulAut V)} (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian2 X) (h : MathieuCode24 H ⊤ ⊥) (hX : rk ↥X = 6)
    (hfX : rkIdx (fixV X) = 7) :
    (CFSG.IsQuasisimple (↥(perfectCore (H ⊓ stabSub (fixV X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabSub (fixV X)))) ∧
      AlternatingNatural (V := ↥(fixV X)) (autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X))
        ⊤ ⊥ 6) ∧ Nat.card V = 2 ^ 11 := by
  obtain ⟨e₀, he₀⟩ := code24_std h
  have hV : ∀ v : V, v ^ 2 = 1 := sq_eq_one_of_equiv e₀
  have hVc : Nat.card V = 2 ^ 11 := card_of_equiv e₀
  have hXc : Nat.card ↥X = 2 ^ 6 := hX ▸ card_eq_of_isElemAbelian2 hXe
  have hrk : rk V = 11 := by
    unfold rk
    rw [hVc, padicValNat.prime_pow]
  have hfr : rk ↥(fixV X) = 4 := by
    have := rk_add_rkIdx (fixV X)
    omega
  have hfXc : Nat.card ↥(fixV X) = 2 ^ 4 := hfr ▸ card_eq_two_pow hV (fixV X)
  obtain ⟨g, hXU⟩ := fixV_eq_US he₀ hXc hfXc hXN (isElemAbelian2_iff.1 hXe)
  set e := twistEquiv e₀ psiC24 g
  have hH : H.map (congrHom e) = (rhoC11 AutPerm le_rfl).range :=
    (map_congrHom_trans e₀ (psiC24 g) H).trans
      ((congrArg (fun K => K.map (congrHom (psiC24 g))) he₀).trans
        (map_congrHom_self (⟨g, rfl⟩ : psiC24 g ∈ (rhoC11 AutPerm le_rfl).range)))
  obtain ⟨hPS, hρ, hperf, hKP, hKn, hK2, hKC, hCK⟩ := lu_code_std card_stab_US_le
  have hPe : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) = imgCd sxP0 :=
    (perfectCore_inf_stab_map e H X).trans
      ((congrArg (fun K => perfectCore (K ⊓ stabSub (fixV (X.map (congrHom e))))) hH).trans
        (by rw [hXU]; exact hPS))
  exact ⟨lu_A6_of_std e hPe hXU usTheta hρ hperf hKP hKn hK2 hKC hCK, hVc⟩

theorem luRow_Coc24
    {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCocode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rk ↥(fixV X) = 3) :
    (CFSG.IsQuasisimple (↥(perfectCore (H ⊓ stabSub (fixV X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabSub (fixV X)))) ∧
      autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X) = ⊤) ∧ Nat.card V = 2 ^ 11 := by
  obtain ⟨e₀, he₀⟩ := cocode24_std h
  have hV : ∀ v : V, v ^ 2 = 1 := sq_eq_one_of_equiv e₀
  have hVc : Nat.card V = 2 ^ 11 := card_of_equiv e₀
  have hXc : Nat.card ↥X = 2 ^ 6 := hX ▸ card_eq_of_isElemAbelian2 hXe
  have hfXc : Nat.card ↥(fixV X) = 2 ^ 3 := hfX ▸ card_eq_two_pow hV (fixV X)
  obtain ⟨g, hXU⟩ := fixV_eq_UT he₀ hXc hfXc hXN (isElemAbelian2_iff.1 hXe)
  set e := twistEquiv e₀ rhoM24 g
  have hR : (rho11 AutPerm le_rfl).range.map (congrHom (rhoM24 g)) = img11 AutPerm :=
    (map_congrHom_self (⟨g, rfl⟩ : rhoM24 g ∈ (rho11 AutPerm le_rfl).range)).trans
      (range_rho11_eq_img11 AutPerm le_rfl)
  have hH : H.map (congrHom e) = img11 AutPerm :=
    (map_congrHom_trans e₀ (rhoM24 g) H).trans
      ((congrArg (fun K => K.map (congrHom (rhoM24 g))) he₀).trans hR)
  obtain ⟨hPS, htop, hS, hnc, hC⟩ := lu_coc_std card_stab_UT_le
  have hPe : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) = img11 trQ :=
    (perfectCore_inf_stab_map e H X).trans
      ((congrArg (fun K => perfectCore (K ⊓ stabSub (fixV (X.map (congrHom e))))) hH).trans
        (by rw [hXU]; exact hPS))
  exact ⟨lu_L32_of_std e hPe hXU htop hS hnc hC, hVc⟩

end CFSG.Quasithin.H.LU

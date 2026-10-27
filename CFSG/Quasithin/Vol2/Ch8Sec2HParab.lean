module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsB
public import CFSG.Quasithin.Background.HModelTransp
public import CFSG.Quasithin.Background.HParabCode22
public import CFSG.Quasithin.Background.HParabQW

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H.Code22 CFSG.Quasithin.H.L34Z

theorem hParab82_of
    (hL : ∀ {X : Subgroup (MulAut W9)}, X ≤ Subgroup.normalizer (img9 : Set (MulAut W9)) →
      IsElemAbelian 2 X → Nat.card ↥X = 2 ^ 4 → Nat.card ↥(fixV X) = 2 ^ 4 →
      ∃ c ∈ Subgroup.normalizer (img9 : Set (MulAut W9)), X.map (MulAut.conj c).toMonoidHom =
        (CFSG.Quasithin.H.L3Nine.Q2 CFSG.Fischer.F4).map
          (rho9.comp Matrix.SpecialLinearGroup.toGL))
    (hM : ∀ {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)},
      MathieuCode22 H ⊤ ⊥ → X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian 2 X →
      Nat.card ↥X = 2 ^ 5 → Nat.card ↥(fixV X) = 2 ^ 4 →
      ∃ e : V ≃* W10, H.map (congrHom e) = imgC mog22 ∧
        fixV (X.map (congrHom e)) = maskSub 10 [19, 194, 354, 513]) :
    HParab82 := by
  intro V _ _ H X hcase hXN hXe hfX
  rcases hcase with ⟨h, hX⟩ | ⟨h, hX⟩
  · obtain ⟨e₀, he₀⟩ := exists_equiv_w9 h
    have hX'N := map_le_normalizer_congrHom e₀ hXN
    rw [he₀] at hX'N
    obtain ⟨c, hc, hcX⟩ := hL hX'N (isElemAbelian_map_hom hXe _)
      ((card_map_congrHom e₀ X).trans hX) ((card_fixV_map_congrHom e₀ X).trans hfX)
    have hH : H.map (congrHom (e₀.trans c)) = img9 :=
      (map_congrHom_trans e₀ c H).trans ((congrArg (fun K => K.map (congrHom c)) he₀).trans
        (map_congrHom_of_mem_normalizer hc))
    have hXQ : X.map (congrHom (e₀.trans c)) = QW9 :=
      (map_congrHom_trans e₀ c X).trans ((map_congrHom_self_eq_conj c _).trans
        (hcX.trans QW9_eq_Q2.symm))
    obtain ⟨h1, h2⟩ := L34Z.parab_std (X₀ := X.map (congrHom (e₀.trans c)))
      ((congrArg fixV hXQ).trans fixV_QW9) hXQ.ge
    have hPe : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom (e₀.trans c)) =
        perfectCore (img9 ⊓ stabSub (fixV (X.map (congrHom (e₀.trans c))))) :=
      (perfectCore_inf_stab_map (e₀.trans c) H X).trans
        (congrArg (fun K => perfectCore (K ⊓ stabSub (fixV (X.map (congrHom (e₀.trans c))))))
          hH)
    refine ⟨(card_map_congrHom (e₀.trans c) _).symm.trans
      ((congrArg (fun K : Subgroup (MulAut W9) => Nat.card ↥K) hPe).trans h1),
      pCoreOf_le_comm_of_map (e₀.trans c) (hPe ▸ h2), fun h22 => ?_⟩
    exfalso
    obtain ⟨e', he'⟩ := code22_std h22
    have c1 : Nat.card ↥H = 20160 := (card_map_congrHom e₀ H).symm.trans
      ((congrArg (fun K : Subgroup (MulAut W9) => Nat.card ↥K) he₀).trans card_img9)
    have c2 : Nat.card ↥H = 443520 := (card_map_congrHom e' H).symm.trans
      ((congrArg (fun K : Subgroup (MulAut W10) => Nat.card ↥K)
        (he'.trans range_rhoC10_eq_imgC)).trans card_imgC_mog22)
    omega
  · obtain ⟨e, he, hXU⟩ := hM h hXN hXe hX hfX
    have hX'N := map_le_normalizer_congrHom e hXN
    rw [he] at hX'N
    obtain ⟨h1, h2, K₀, hPK, hKH, hK⟩ :=
      Code22.parab_std (X₀ := X.map (congrHom e)) hXU hX'N ((card_map_congrHom e X).trans hX)
    have hPe : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) =
        perfectCore (imgC mog22 ⊓ stabSub (fixV (X.map (congrHom e)))) :=
      (perfectCore_inf_stab_map e H X).trans
        (congrArg (fun K => perfectCore (K ⊓ stabSub (fixV (X.map (congrHom e))))) he)
    refine ⟨(card_map_congrHom e _).symm.trans
      ((congrArg (fun K : Subgroup (MulAut W10) => Nat.card ↥K) hPe).trans h1),
      pCoreOf_le_comm_of_map e (hPe ▸ h2), fun _ => ⟨K₀.map (congrHom e.symm), ?_, ?_, ?_⟩⟩
    · rw [← map_congrHom_symm_map e (perfectCore (H ⊓ stabSub (fixV X))), hPe]
      exact Subgroup.map_mono hPK
    · rw [← map_congrHom_symm_map e H, he]
      exact Subgroup.map_mono hKH
    · exact isPSL_of_mulEquiv' (K₀.equivMapOfInjective _ (congrHom_injective e.symm)).symm hK

end CFSG.Quasithin.H13

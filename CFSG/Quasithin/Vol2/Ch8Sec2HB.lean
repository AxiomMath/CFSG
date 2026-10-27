module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsC
public import CFSG.Quasithin.Background.HModelTransp
public import CFSG.Quasithin.Background.HB82Coc24
public import CFSG.Quasithin.Background.HB82Code22
public import CFSG.Quasithin.Background.HParabQW

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H.Code22 CFSG.Quasithin.H.L34Z

theorem hB82_of
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
    HB82 := by
  intro V _ _ H X z hcase hXN hXe hz1 hS
  obtain ⟨S, hSH, hS, hzS⟩ := hS
  rcases hcase with ⟨h, hX, hfX⟩ | ⟨h, hX, hfX⟩ | ⟨h, hX, hfX⟩
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
    have hXU : fixV (X.map (congrHom (e₀.trans c))) = U0 := (congrArg fixV hXQ).trans fixV_QW9
    exact hbConcl_of_equiv (e₀.trans c) hH hXU
      (fun hX' _ hz1' _ hSH' hS' hz' => L34Z.hbConcl_std hX' hz1' hSH' hS' hz') hz1 hSH hS hzS
  · obtain ⟨e, he, hXU⟩ := hM h hXN hXe hX hfX
    exact hbConcl_of_equiv e he hXU
      (fun hX' _ hz1' _ hSH' hS' hz' => Code22.hbConcl_std hX' hz1' hSH' hS' hz') hz1 hSH hS hzS
  · exact CFSG.Quasithin.H.Coc24.hbConcl_of_cocode24 h hX hfX hXN hXe hz1 hSH hS hzS

end CFSG.Quasithin.H13

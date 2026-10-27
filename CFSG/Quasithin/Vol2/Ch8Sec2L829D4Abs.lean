module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829D4Std34
public import CFSG.Quasithin.Vol2.Ch8Sec2L829D4StdM22
public import CFSG.Quasithin.Background.HFL3W9
public import CFSG.Quasithin.Background.HParabQW
public import CFSG.Quasithin.Background.HFCode22U
public import CFSG.Quasithin.Background.HModelTransp

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin.H.L34Z CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Code22 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H13.Ch9.Herm9

theorem D4NF_sd4_conj_sd4 {W : Type} [CommGroup W] [Finite W] (c : MulAut W)
    {H : Subgroup (MulAut W)} (hc : c ∈ Subgroup.normalizer (H : Set (MulAut W)))
    {U : Subgroup W} (h : D4NF_sd4 H U) : D4NF_sd4 H (U.map c.toMonoidHom) := by
  have h1 := D4NF_sd4_of_equiv_sd4 c H U h
  have h2 := CFSG.Quasithin.H.ZTrans.map_congrHom_of_mem_normalizer hc
  exact (congrArg (fun K => D4NF_sd4 K (U.map c.toMonoidHom)) h2).mp h1

theorem map_conj_eq_congrHom_sd4 {W : Type} [CommGroup W] (c : MulAut W)
    (A : Subgroup (MulAut W)) :
    A.map (MulAut.conj c).toMonoidHom = A.map (CFSG.Quasithin.H.congrHom c) := by
  congr 1

theorem map_inv_map_sd4 {W : Type} [CommGroup W] (c : MulAut W) (U : Subgroup W) :
    (U.map c.toMonoidHom).map (c⁻¹ : MulAut W).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : (c⁻¹ : MulAut W).toMonoidHom.comp c.toMonoidHom = MonoidHom.id W := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem D4NF_L34_of_sd4 {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}
    (h : BinaryNineTensor H ⊤ ⊥ 1) (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian 2 X) (hX : Nat.card ↥X = 2 ^ 4) (hfX : Nat.card ↥(fixV X) = 2 ^ 4) :
    D4NF_sd4 H (fixV X) := by
  obtain ⟨e, he⟩ : ∃ e : V ≃* W9, H.map (CFSG.Quasithin.H.congrHom e) = img9 :=
    exists_equiv_w9 h
  have hXN' : X.map (CFSG.Quasithin.H.congrHom e) ≤ Subgroup.normalizer (img9 : Set (MulAut W9)) :=
    he ▸ CFSG.Quasithin.H.ZTrans.map_le_normalizer_congrHom e hXN
  have hXe' : IsElemAbelian 2 (X.map (CFSG.Quasithin.H.congrHom e)) :=
    CFSG.Quasithin.H.isElemAbelian2_iff.1
      ((CFSG.Quasithin.H.isElemAbelian2_map_congrHom e (A := X)).2
        (CFSG.Quasithin.H.isElemAbelian2_iff.2 hXe))
  have hX' : Nat.card ↥(X.map (CFSG.Quasithin.H.congrHom e)) = 2 ^ 4 :=
    (CFSG.Quasithin.H.card_map_congrHom e X).trans hX
  have hfixe : fixV (X.map (CFSG.Quasithin.H.congrHom e)) = (fixV X).map e.toMonoidHom :=
    CFSG.Quasithin.H.fixV_map_congrHom e X
  have hfX' : Nat.card ↥(fixV (X.map (CFSG.Quasithin.H.congrHom e))) = 2 ^ 4 :=
    (congrArg (fun (A : Subgroup W9) => Nat.card ↥A) hfixe).trans
      ((Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).trans hfX)
  obtain ⟨c, hc, hcX⟩ := exists_conj_eq_QW9 hXN' hXe' hX' hfX'
  have hcX' : (X.map (CFSG.Quasithin.H.congrHom e)).map (CFSG.Quasithin.H.congrHom c) = QW9 :=
    ((map_conj_eq_congrHom_sd4 c _).symm.trans hcX).trans QW9_eq_Q2.symm
  have hU0 : ((fixV (X.map (CFSG.Quasithin.H.congrHom e))).map c.toMonoidHom) = U0 :=
    (CFSG.Quasithin.H.fixV_map_congrHom c (X.map (CFSG.Quasithin.H.congrHom e))).symm.trans
      ((congrArg fixV hcX').trans fixV_QW9)
  have hfixX' : fixV (X.map (CFSG.Quasithin.H.congrHom e)) = U0.map (c⁻¹ : MulAut W9).toMonoidHom :=
    (map_inv_map_sd4 c _).symm.trans (congrArg (fun A => A.map (c⁻¹ : MulAut W9).toMonoidHom) hU0)
  have hD : D4NF_sd4 img9 (fixV (X.map (CFSG.Quasithin.H.congrHom e))) := by
    rw [hfixX']
    exact D4NF_sd4_conj_sd4 (c⁻¹ : MulAut W9) (Subgroup.inv_mem _ hc) D4NF_std34_sd4
  have key := D4NF_sd4_of_equiv_sd4 e.symm img9 (fixV (X.map (CFSG.Quasithin.H.congrHom e))) hD
  have hHe : (H.map (CFSG.Quasithin.H.congrHom e)).map (CFSG.Quasithin.H.congrHom e.symm) = H :=
    CFSG.Quasithin.H.ZTrans.map_congrHom_symm_map e H
  have hback : ((fixV X).map e.toMonoidHom).map e.symm.toMonoidHom = fixV X :=
    map_equiv_symm_map_sd4 e (fixV X)
  have key2 : D4NF_sd4 ((H.map (CFSG.Quasithin.H.congrHom e)).map (CFSG.Quasithin.H.congrHom e.symm))
      ((fixV (X.map (CFSG.Quasithin.H.congrHom e))).map e.symm.toMonoidHom) := by
    rw [he]
    exact key
  rw [hHe] at key2
  rw [hfixe, hback] at key2
  exact key2

theorem D4NF_M22_of_sd4 {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}
    (h : MathieuCode22 H ⊤ ⊥) (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian 2 X) (hX : Nat.card ↥X = 2 ^ 5) (hfX : Nat.card ↥(fixV X) = 2 ^ 4) :
    D4NF_sd4 H (fixV X) := by
  obtain ⟨e, he1, he2⟩ : ∃ e : V ≃* Wn 10, H.map (CFSG.Quasithin.H.congrHom e) = imgC mog22 ∧
      fixV (X.map (CFSG.Quasithin.H.congrHom e)) = maskSub 10 [19, 194, 354, 513] :=
    code22_E32_std h hXN hXe hX hfX
  have hfixe : fixV (X.map (CFSG.Quasithin.H.congrHom e)) = (fixV X).map e.toMonoidHom :=
    CFSG.Quasithin.H.fixV_map_congrHom e X
  have hU : (fixV X).map e.toMonoidHom = UC := hfixe.symm.trans he2
  have h1 := D4NF_sd4_of_equiv_sd4 e.symm (imgC mog22) UC D4NF_stdM22_sd4
  have hHe : (H.map (CFSG.Quasithin.H.congrHom e)).map (CFSG.Quasithin.H.congrHom e.symm) = H :=
    CFSG.Quasithin.H.ZTrans.map_congrHom_symm_map e H
  have hback : ((fixV X).map e.toMonoidHom).map e.symm.toMonoidHom = fixV X :=
    map_equiv_symm_map_sd4 e (fixV X)
  have key2 : D4NF_sd4 ((H.map (CFSG.Quasithin.H.congrHom e)).map (CFSG.Quasithin.H.congrHom e.symm))
      ((UC).map e.symm.toMonoidHom) := by
    rw [he1]
    exact h1
  rw [hHe] at key2
  rw [← hU, hback] at key2
  exact key2

end CFSG.Quasithin.H13.L829N

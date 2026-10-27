module

public import CFSG.Quasithin.Background.H47WLower
public import CFSG.Quasithin.Background.H47WHyp
public import CFSG.Quasithin.Background.H47WW9
public import CFSG.Quasithin.Background.H47WW18
public import CFSG.Quasithin.Background.H47WW16
public import CFSG.Quasithin.Background.H47WW64
public import CFSG.Quasithin.Background.H47WTrans

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.L34M
  CFSG.Quasithin.H13.Ch9.L34N CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.L3W9
  CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H CFSG.ASVolI.ChH CFSG.Fischer
open scoped MatrixGroups

theorem congr_eq_conj9 (h g : MulAut W9) : MulAut.congr h g = h * g * h⁻¹ := by
  ext w
  simp [MulAut.congr_apply, MulAut.mul_apply]

theorem map_congr_img9 {h : MulAut W9} (hh : h ∈ rho9G.range) :
    img9.map (MulAut.congr h).toMonoidHom = img9 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    show MulAut.congr h x ∈ img9
    rw [congr_eq_conj9]
    exact img9_conj_mem hh hx
  · intro y hy
    refine ⟨h⁻¹ * y * h⁻¹⁻¹, ?_, ?_⟩
    · exact img9_conj_mem (Subgroup.inv_mem _ hh) hy
    · show MulAut.congr h (h⁻¹ * y * h⁻¹⁻¹) = y
      rw [congr_eq_conj9]
      group

theorem congr_symm_congr {V W : Type} [CommGroup V] [CommGroup W] (e : V ≃* W) (x : MulAut V) :
    MulAut.congr e.symm (MulAut.congr e x) = x := by
  ext v
  simp [MulAut.congr_apply]

theorem H47_main
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (M : Subgroup (MulAut V)) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hL : Nonempty (↥(CFSG.generalizedFitting ↥M) ≃* PSL(3, K)))
    (hirr : IsIrredOn ((CFSG.generalizedFitting ↥M).map M.subtype) ⊤)
    (t : MulAut V) (htM : t ∈ M) (ht2 : orderOf t = 2) :
    3 ≤ rk ↥(commV (Subgroup.zpowers t)) ∧
      (rk ↥(commV (Subgroup.zpowers t)) = 3 ↔
        ∃ e : V ≃* HMod 1 K,
          ((CFSG.generalizedFitting ↥M).map M.subtype).map (MulAut.congr e).toMonoidHom = img hK ∧
          ∃ l ∈ img hK, ∃ φ : K ≃+* K, φ ≠ 1 ∧ MulAut.congr e t = l * fldAut φ) := by
  classical
  have hlow := three_le_rk V hV M K hK hL hirr t htM ht2
  refine ⟨hlow, ?_⟩
  obtain ⟨hirrX, hLX, hXN, hPSL, hCX, hX2⟩ := factL34_hyps V hV M K hK hL hirr t htM ht2
  set L : Subgroup (MulAut V) := (CFSG.generalizedFitting ↥M).map M.subtype with hLdef
  set X : Subgroup (MulAut V) := L ⊔ Subgroup.zpowers t with hXdef
  have htX : t ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨φ0⟩ := exists_phi0 K hK
  set φ : K ≃+* K := φ0.trans (cjRing.trans φ0.symm) with hφdef
  have hφpt : ∀ x : K, φ0 (φ x) = cj (φ0 x) := fun x => by
    simp [hφdef]
    rfl
  have hφne : φ ≠ 1 := by
    intro h1
    apply cj_mk_ne
    have hx := hφpt (φ0.symm (mk 0 1))
    rw [h1] at hx
    simpa using hx.symm
  constructor
  ·
    intro hrk3
    rcases H13.Ch9.L34B.factL34Modules_holds V hV X hirrX L hLX hXN hPSL hCX hX2 with
      ⟨E, hE⟩ | ⟨E, hE⟩ | ⟨E, hE⟩ | ⟨E, hE⟩
    ·
      have hEN : MulAut.congr E t ∈ Subgroup.normalizer (img9 : Set (MulAut W9)) := by
        have h := H13.Ch9.L34M.map_le_normalizer E hXN hE
        exact h (Subgroup.mem_map_of_mem _ htX)
      have hEt : MulAut.congr E t * MulAut.congr E t = 1 := by
        rw [← map_mul, htt, map_one]
      have hrkE : rk ↥(commV (Subgroup.zpowers (MulAut.congr E t))) = 3 :=
        (rk_commV_congr_eq E t).trans hrk3
      obtain ⟨h, hh, u, hu⟩ := w9_outer_of_rank hEt (normalizer_img9_le hEN) hrkE
      have hE9 : L.map (MulAut.congr E).toMonoidHom = img9 := hE
      have h3 : L.map (MulAut.congr (E.trans h)).toMonoidHom = img9 :=
        (map_congr_trans' E h L).trans
          ((congrArg (fun S => S.map (MulAut.congr h).toMonoidHom) hE9).trans
            (map_congr_img9 hh))
      have h4 : L.map (MulAut.congr ((E.trans h).trans (hmodEquiv φ0).symm)).toMonoidHom =
          img hK :=
        (map_congr_trans' (E.trans h) (hmodEquiv φ0).symm L).trans
          ((congrArg (fun S => S.map (MulAut.congr (hmodEquiv φ0).symm).toMonoidHom) h3).trans
            ((congrArg (fun S => S.map (MulAut.congr (hmodEquiv φ0).symm).toMonoidHom)
              (map_img φ0 hK).symm).trans (map_congr_symm (hmodEquiv φ0) (img hK))))
      refine ⟨(E.trans h).trans (hmodEquiv φ0).symm, h4, ?_⟩
      set A : GL (Fin 3) K := gl3map φ0.symm (Matrix.SpecialLinearGroup.toGL u) with hA
      have hmapA : mapGLF φ0 A = Matrix.SpecialLinearGroup.toGL u := by
        apply Units.ext
        rw [coe_mapGLF, hA, coe_gl3map]
        ext i j
        simp
      have hdetA : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
        rw [hA, coe_gl3map]
        have h1 : ((Matrix.SpecialLinearGroup.toGL u : GL (Fin 3) F4) :
            Matrix (Fin 3) (Fin 3) F4).det = 1 := Matrix.SpecialLinearGroup.det_coe u
        calc ((((Matrix.SpecialLinearGroup.toGL u : GL (Fin 3) F4) :
              Matrix (Fin 3) (Fin 3) F4)).map φ0.symm).det
            = φ0.symm.toRingHom ((Matrix.SpecialLinearGroup.toGL u : GL (Fin 3) F4) :
              Matrix (Fin 3) (Fin 3) F4).det := (RingHom.map_det φ0.symm.toRingHom _).symm
          _ = 1 := by rw [h1, map_one]
      have hrhoA : MulAut.congr (hmodEquiv φ0).symm (rho9 (Matrix.SpecialLinearGroup.toGL u)) =
          rhoT hK A := by
        have h1 : congrHom (hmodEquiv φ0) (rhoT hK A) =
            rho9 (Matrix.SpecialLinearGroup.toGL u) := by
          rw [congrHom_hmodEquiv_rhoT φ0 hK A, hmapA]
        have h2 : MulAut.congr (hmodEquiv φ0).symm
            (MulAut.congr (hmodEquiv φ0) (rhoT hK A)) = rhoT hK A := congr_symm_congr _ _
        rw [← h1]
        exact h2
      have hfldφ : MulAut.congr (hmodEquiv φ0).symm fld9 = fldAut φ := by
        have h1 : congrHom (hmodEquiv φ0) (fldAut φ) = fld9 := congr_hmod_fldAut φ0 φ hφpt
        have h2 : MulAut.congr (hmodEquiv φ0).symm
            (MulAut.congr (hmodEquiv φ0) (fldAut φ)) = fldAut φ := congr_symm_congr _ _
        rw [← h1]
        exact h2
      have hc1 : MulAut.congr ((E.trans h).trans (hmodEquiv φ0).symm) t =
          MulAut.congr (hmodEquiv φ0).symm (MulAut.congr (E.trans h) t) :=
        congr_trans_apply _ _ _
      have hc2 : MulAut.congr (E.trans h) t = MulAut.congr h (MulAut.congr E t) :=
        congr_trans_apply _ _ _
      have hc3 : MulAut.congr h (MulAut.congr E t) = h * MulAut.congr E t * h⁻¹ :=
        congr_eq_conj9 _ _
      have hm : MulAut.congr (hmodEquiv φ0).symm (rho9 (Matrix.SpecialLinearGroup.toGL u) * fld9) =
          MulAut.congr (hmodEquiv φ0).symm (rho9 (Matrix.SpecialLinearGroup.toGL u)) *
            MulAut.congr (hmodEquiv φ0).symm fld9 := map_mul _ _ _
      refine ⟨rhoT hK A, rhoT_mem_img hK hdetA, φ, hφne, ?_⟩
      rw [hc1, hc2, hc3, hu, hm, hrhoA, hfldφ]
    · exact (not_irr_w18 L E hE hirr).elim
    ·
      exfalso
      have hN : MulAut.congr E t ∈ Subgroup.normalizer (img16 : Set (MulAut (Wn 16))) := by
        have h := H13.Ch9.L34M.map_le_normalizer E hXN hE
        exact h (Subgroup.mem_map_of_mem _ htX)
      have hEt : MulAut.congr E t * MulAut.congr E t = 1 := by
        rw [← map_mul, htt, map_one]
      have hne : MulAut.congr E t ≠ 1 := by
        intro h1
        apply ht1
        apply (MulAut.congr E).injective
        rw [h1, map_one]
      have hf := rk_fixV_w16_le hEt hne hN
      have hfE := rk_fixV_zpowers_congr E t
      have hV16 : rk V = 16 := by
        have h4 : rk V = rk (Wn 16) := by
          unfold rk
          rw [Nat.card_congr E.toEquiv]
        rw [h4, rk_Wn16]
      have hsum : rk ↥(commV (Subgroup.zpowers t)) + rk ↥(fixV (Subgroup.zpowers t)) = 16 :=
        (rk_commV_zpowers_eq_sub t).trans hV16
      have key : rk ↥(fixV (Subgroup.zpowers t)) ≤ 10 := (le_of_eq hfE.symm).trans hf
      omega
    ·
      exfalso
      have hN : MulAut.congr E t ∈ Subgroup.normalizer (img64 : Set (MulAut (Wn 64))) := by
        have h := H13.Ch9.L34M.map_le_normalizer E hXN hE
        exact h (Subgroup.mem_map_of_mem _ htX)
      have hEt : MulAut.congr E t * MulAut.congr E t = 1 := by
        rw [← map_mul, htt, map_one]
      have hne : MulAut.congr E t ≠ 1 := by
        intro h1
        apply ht1
        apply (MulAut.congr E).injective
        rw [h1, map_one]
      have hf := rk_fixV_w64_le hEt hne hN
      have hfE := rk_fixV_zpowers_congr E t
      have hV64 : rk V = 64 := by
        have h4 : rk V = rk (Wn 64) := by
          unfold rk
          rw [Nat.card_congr E.toEquiv]
        rw [h4, rk_Wn64]
      have hsum : rk ↥(commV (Subgroup.zpowers t)) + rk ↥(fixV (Subgroup.zpowers t)) = 64 :=
        (rk_commV_zpowers_eq_sub t).trans hV64
      have key : rk ↥(fixV (Subgroup.zpowers t)) ≤ 60 := (le_of_eq hfE.symm).trans hf
      omega
  ·
    rintro ⟨e, he, l, hl, φ', hφ', htl⟩
    have hpt := pointwise_of_ne_one φ0 φ' hφ'
    have hLe : L.map (MulAut.congr (e.trans (hmodEquiv φ0))).toMonoidHom = img9 :=
      (map_congr_trans' e (hmodEquiv φ0) L).trans
        ((congrArg (fun S => S.map (MulAut.congr (hmodEquiv φ0)).toMonoidHom) he).trans
          (map_img φ0 hK))
    have ht9 : MulAut.congr (e.trans (hmodEquiv φ0)) t * MulAut.congr (e.trans (hmodEquiv φ0)) t
        = 1 := by
      rw [← map_mul, htt, map_one]
    have hl9 : MulAut.congr (hmodEquiv φ0) l ∈ img9 := by
      exact (map_img φ0 hK) ▸ Subgroup.mem_map_of_mem _ hl
    have hfl : MulAut.congr (hmodEquiv φ0) (fldAut φ') = fld9 := congr_hmod_fldAut φ0 φ' hpt
    have hm2 : MulAut.congr (hmodEquiv φ0) (l * fldAut φ') =
        MulAut.congr (hmodEquiv φ0) l * MulAut.congr (hmodEquiv φ0) (fldAut φ') :=
      map_mul _ _ _
    have htl9 : MulAut.congr (e.trans (hmodEquiv φ0)) t =
        MulAut.congr (hmodEquiv φ0) l * fld9 :=
      (congr_trans_apply e (hmodEquiv φ0) t).trans
        ((congrArg (MulAut.congr (hmodEquiv φ0)) htl).trans (hm2.trans (by rw [hfl])))
    have hrank := w9_rank_of_fld ht9 hl9 htl9
    exact (rk_commV_congr_eq (e.trans (hmodEquiv φ0)) t).symm.trans hrank

end CFSG.Quasithin.H47W

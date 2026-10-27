module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9Four
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Coord

public section

namespace CFSG.Quasithin.H13.H9Four

open CFSG.Open CFSG.Quasithin.E3 CFSG.ComponentClassification.CatalogueBGraphForm H9Coord
open scoped Matrix

@[expose] def eltOf (A : GL (Fin 4) (ZMod 2)) (b : Bool) : Elt :=
  ⟨Mat.ofMatrix A, Mat.ofMatrix ↑A⁻¹, b⟩

theorem eltOf_valid (A : GL (Fin 4) (ZMod 2)) (b : Bool) : (eltOf A b).valid = true := by
  rw [Elt.valid_iff]
  simp only [eltOf, Mat.toMatrix_ofMatrix]
  exact ⟨Units.mul_inv A, Units.inv_mul A⟩

theorem Mat.app_ofMatrix (A : GL (Fin 4) (ZMod 2)) (x : Vec 4) :
    (Mat.ofMatrix A).app x = vecAut A x := by
  rw [Mat.app, Mat.toMatrix_ofMatrix]
  rfl

theorem Mat.app_tr_ofMatrix (A : GL (Fin 4) (ZMod 2)) (y : Vec 4) :
    (Mat.tr (Mat.ofMatrix ↑A⁻¹)).app y = vecAut (glGraphAut 4 (ZMod 2) A) y := by
  rw [Mat.app, Mat.toMatrix_tr, Mat.toMatrix_ofMatrix, vecAut_apply, glGraphAut_matrix]

theorem eltOf_act_false (A : GL (Fin 4) (ZMod 2)) (p : Pt) :
    (eltOf A false).act p = (vecAut A p.1, vecAut (glGraphAut 4 (ZMod 2) A) p.2) := by
  rw [Elt.act_of_false rfl]
  show ((Mat.ofMatrix A).app p.1, (Mat.tr (Mat.ofMatrix ↑A⁻¹)).app p.2) = _
  rw [Mat.app_ofMatrix, Mat.app_tr_ofMatrix]

theorem eltOf_act_true (A : GL (Fin 4) (ZMod 2)) (p : Pt) :
    (eltOf A true).act p = (vecAut A p.2, vecAut (glGraphAut 4 (ZMod 2) A) p.1) := by
  rw [Elt.act_of_true rfl]
  show ((Mat.ofMatrix A).app p.2, (Mat.tr (Mat.ofMatrix ↑A⁻¹)).app p.1) = _
  rw [Mat.app_ofMatrix, Mat.app_tr_ofMatrix]

@[expose] def Elt.gl (e : Elt) (he : e.valid = true) : GL (Fin 4) (ZMod 2) :=
  ⟨e.a.toMatrix, e.ai.toMatrix, ((Elt.valid_iff e).mp he).1, ((Elt.valid_iff e).mp he).2⟩

theorem eltOf_gl {e : Elt} (he : e.valid = true) : eltOf (e.gl he) e.b = e :=
  Elt.eq_of_a (eltOf_valid _ _) he (by simp [eltOf, Elt.gl, Mat.toMatrix_ofMatrix]) rfl

theorem card_pt' : Nat.card Pt = 2 ^ 4 * 2 ^ 4 := by
  show Nat.card (Vec 4 × Vec 4) = _
  rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd (α := Fin 4 → ZMod 2)), Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]

variable {W : Type} [CommGroup W] [Finite W] {M L T : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}

theorem exists_modelIso (hyp : H9Hyp 4 M L T W₁ W₂) :
    ∃ e : W ≃* Pt, H9Iso.isoAut e M = modelM4 ∧ H9Iso.isoAut e L = modelL4 ∧
      W₁.map e.toMonoidHom = ptW₁ ∧ W₂.map e.toMonoidHom = ptW₂ := by
  have hexp₁ : ∀ u : ↥W₁, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hyp.exp u)
  obtain ⟨e₁⟩ := exists_coord hexp₁ hyp.card₁
  obtain ⟨φ, hφ⟩ := exists_glRep hyp e₁
  obtain ⟨t, htT, htL, ht⟩ := hyp.swap
  have htM : t ∈ M := hyp.sylow_le htT
  obtain ⟨c, hc⟩ := exists_graph hyp (by norm_num) φ htM htL
  have hsq := phi_sq hyp φ htM htL hc
  let E : Pt →* W :=
    { toFun := fun p => (e₁.symm p.1 : W) * t (e₁.symm (vecAut c p.2) : W)
      map_one' := by
        show (e₁.symm 1 : W) * t (e₁.symm (vecAut c 1) : W) = 1
        simp
      map_mul' := fun p q => by
        show (e₁.symm (p.1 * q.1) : W) * t (e₁.symm (vecAut c (p.2 * q.2)) : W) =
          ((e₁.symm p.1 : W) * t (e₁.symm (vecAut c p.2) : W)) *
            ((e₁.symm q.1 : W) * t (e₁.symm (vecAut c q.2) : W))
        simp only [map_mul, Subgroup.coe_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hE : ∀ p : Pt, E p = (e₁.symm p.1 : W) * t (e₁.symm (vecAut c p.2) : W) := fun _ => rfl
  have hE' : ∀ x y : Vec 4, E (x, y) = (e₁.symm x : W) * t (e₁.symm (vecAut c y) : W) :=
    fun _ _ => rfl
  have hmem₁ : ∀ x, (e₁.symm x : W) ∈ W₁ := fun x => (e₁.symm x).2
  have hmem₂ : ∀ x, t (e₁.symm x : W) ∈ W₂ := fun x => by
    rw [ht]
    exact Subgroup.mem_map_of_mem t.toMonoidHom (e₁.symm x).2
  have hdisj : ∀ a ∈ W₁ ⊓ W₂, a = 1 := fun a ha => by
    rwa [hyp.inf, Subgroup.mem_bot] at ha
  have hcancel₁ : ∀ x, (e₁.symm x : W) = 1 → x = 1 := fun x h => by
    have h1 : e₁.symm x = 1 := Subtype.ext h
    simpa using congrArg e₁ h1
  have hcancel₂ : ∀ y, t (e₁.symm (vecAut c y) : W) = 1 → y = 1 := fun y h =>
    (map_eq_one_iff (vecAut c) (vecAut c).injective).mp
      (hcancel₁ _ ((map_eq_one_iff t t.injective).mp h))
  have hEinj : Function.Injective E := by
    rw [injective_iff_map_eq_one]
    intro p hp
    rw [hE] at hp
    have h2 : t (e₁.symm (vecAut c p.2) : W) = 1 := hdisj _ ⟨by
      have := W₁.mul_mem (W₁.inv_mem (hmem₁ p.1)) (hp ▸ W₁.one_mem)
      rwa [inv_mul_cancel_left] at this, hmem₂ _⟩
    rw [h2, mul_one] at hp
    exact Prod.ext (hcancel₁ _ hp) (hcancel₂ _ h2)
  have hEbij : Function.Bijective E :=
    hEinj.bijective_of_nat_card_le ((H9Conj.card_W hyp).trans card_pt'.symm).le
  let e : W ≃* Pt := (MulEquiv.ofBijective E hEbij).symm
  have he : ∀ p, e.symm p = E p := fun _ => rfl
  have heE : ∀ x y : Vec 4, e (E (x, y)) = (x, y) := fun x y =>
    MulEquiv.apply_symm_apply e (x, y)
  have hKL : ∀ l : ↥L, ∀ p : Pt, (l : MulAut W) (E p) =
      E (vecAut (φ l) p.1, vecAut (glGraphAut 4 (ZMod 2) (φ l)) p.2) := by
    intro l p
    have h1 : (l : MulAut W) (t (e₁.symm (vecAut c p.2) : W)) =
        t ((tConj hyp htM l : MulAut W) (e₁.symm (vecAut c p.2) : W)) := by
      rw [coe_tConj]
      simp [MulAut.mul_apply]
    have h2 : vecAut (c * glGraphAut 4 (ZMod 2) (φ l) * c⁻¹) (vecAut c p.2) =
        vecAut c (vecAut (glGraphAut 4 (ZMod 2) (φ l)) p.2) := by
      rw [vecAut_mul_apply, vecAut_mul_apply, ← vecAut_mul_apply c⁻¹ c, inv_mul_cancel,
        vecAut_one, MulAut.one_apply]
    rw [hE, hE', map_mul, hφ l, h1, hφ (tConj hyp htM l), hc l, h2]
  have hKt : ∀ p : Pt, t (E p) =
      E (vecAut (glGraphAut 4 (ZMod 2) c⁻¹) p.2, vecAut c⁻¹ p.1) := by
    intro p
    have ha : t (t (e₁.symm (vecAut c p.2) : W)) =
        (e₁.symm (vecAut (glGraphAut 4 (ZMod 2) c⁻¹) p.2) : W) := by
      rw [← hsq, vecAut_mul_apply]
      exact hφ ⟨t * t, mul_mem_L hyp htM htM htL htL⟩ (vecAut c p.2)
    have hb : vecAut c (vecAut c⁻¹ p.1) = p.1 := by
      rw [← vecAut_mul_apply, mul_inv_cancel, vecAut_one, MulAut.one_apply]
    rw [hE, hE', map_mul, ha, hb, mul_comm]
  have hcl : ∀ l : ↥L, MulAut.congr e (l : MulAut W) = (eltOf (φ l) false).sem := by
    intro l
    refine MulEquiv.ext fun p => ?_
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, he, hKL, heE,
      Elt.sem_apply (eltOf_valid _ _), eltOf_act_false]
  have hct : MulAut.congr e t = (eltOf (glGraphAut 4 (ZMod 2) c⁻¹) true).sem := by
    refine MulEquiv.ext fun p => ?_
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, he, hKt, heE,
      Elt.sem_apply (eltOf_valid _ _), eltOf_act_true,
      Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
  have hL : H9Iso.isoAut e L = modelL4 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨eltOf (φ ⟨l, hl⟩) false, eltOf_valid _ _, rfl, (hcl ⟨l, hl⟩).symm⟩
    · rintro _ ⟨f, hf, hfb, rfl⟩
      refine (H9Iso.mem_isoAut e).mpr ?_
      have h1 : f.sem = MulAut.congr e ((φ.symm (f.gl hf) : ↥L) : MulAut W) := by
        rw [hcl, MulEquiv.apply_symm_apply, ← hfb, eltOf_gl hf]
      rw [h1, MulEquiv.symm_apply_apply]
      exact (φ.symm (f.gl hf)).2
  have hctM : MulAut.congr e t ∈ modelM4 := by
    rw [hct]
    exact Elt.sem_mem (eltOf_valid _ _)
  have hLM : H9Iso.isoAut e L ≤ H9Iso.isoAut e M := (H9Iso.isoAut_le_iff e).mpr hyp.le
  have hM : H9Iso.isoAut e M = modelM4 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
      show MulAut.congr e m ∈ modelM4
      by_cases hmL : m ∈ L
      · have h1 : MulAut.congr e m ∈ H9Iso.isoAut e L := (H9Iso.congr_mem_isoAut e).mpr hmL
        rw [hL] at h1
        exact modelL4_le h1
      · have h1 : t⁻¹ * m ∈ L := mul_mem_L hyp (M.inv_mem htM) hm
          (fun h => htL (by simpa using L.inv_mem h)) hmL
        have h2 : MulAut.congr e (t⁻¹ * m) ∈ H9Iso.isoAut e L := (H9Iso.congr_mem_isoAut e).mpr h1
        rw [hL] at h2
        have h3 : MulAut.congr e m = MulAut.congr e t * MulAut.congr e (t⁻¹ * m) := by
          rw [← map_mul, mul_inv_cancel_left]
        rw [h3]
        exact modelM4.mul_mem hctM (modelL4_le h2)
    · rintro _ ⟨f, hf, rfl⟩
      cases hfb : f.b
      · have h1 : f.sem ∈ modelL4 := ⟨f, hf, hfb, rfl⟩
        rw [← hL] at h1
        exact hLM h1
      · have hy : (MulAut.congr e t)⁻¹ * f.sem ∈ modelL4 := by
          rw [hct, ← Elt.sem_inv (eltOf_valid _ _),
            ← Elt.sem_mul (Elt.valid_inv (eltOf_valid _ _)) hf]
          refine ⟨_, Elt.valid_mul (Elt.valid_inv (eltOf_valid _ _)) hf, ?_, rfl⟩
          show xor (eltOf _ true).inv.b f.b = false
          rw [Elt.inv_b, hfb]
          rfl
        rw [← hL] at hy
        have h2 : f.sem = MulAut.congr e t * ((MulAut.congr e t)⁻¹ * f.sem) := by group
        rw [h2]
        exact (H9Iso.isoAut e M).mul_mem ((H9Iso.congr_mem_isoAut e).mpr htM) (hLM hy)
  have hW₁ : W₁.map e.toMonoidHom = ptW₁ := by
    ext p
    rw [Subgroup.mem_map_equiv, he, mem_ptW₁, hE]
    constructor
    · intro h
      have h1 : t (e₁.symm (vecAut c p.2) : W) ∈ W₁ := by
        have := W₁.mul_mem (W₁.inv_mem (hmem₁ p.1)) h
        rwa [inv_mul_cancel_left] at this
      exact hcancel₂ _ (hdisj _ ⟨h1, hmem₂ _⟩)
    · intro h
      rw [h]
      simp
  have hW₂ : W₂.map e.toMonoidHom = ptW₂ := by
    ext p
    rw [Subgroup.mem_map_equiv, he, mem_ptW₂, hE]
    constructor
    · intro h
      have h1 : (e₁.symm p.1 : W) ∈ W₂ := by
        have := W₂.mul_mem h (W₂.inv_mem (hmem₂ (vecAut c p.2)))
        rwa [mul_inv_cancel_right] at this
      exact hcancel₁ _ (hdisj _ ⟨hmem₁ _, h1⟩)
    · intro h
      rw [h]
      simpa using hmem₂ (vecAut c p.2)
  exact ⟨e, hM, hL, hW₁, hW₂⟩

theorem lemH93Use_holds : LemH93Use := by
  intro W _ _ M L T W₁ W₂ hyp
  obtain ⟨e, hM, hL, hW₁, -⟩ := exists_modelIso hyp
  obtain ⟨A₀, A₁, A₂, hA, hcl, ⟨h0f, h0g⟩, ⟨h1f, h1g⟩, ⟨h2f, h2g, h2faith⟩, h7⟩ := model_lemH93
  have hinv : ∀ B : Subgroup (MulAut Pt), H9Iso.isoAut e (H9Iso.isoAut e.symm B) = B :=
    H9Iso.isoAut_symm e
  have hle : ∀ B : Subgroup (MulAut Pt), H9Iso.isoAut e.symm B ≤ M ↔ B ≤ modelM4 := fun B => by
    rw [← H9Iso.isoAut_le_iff e, hinv, hM]
  have hea : ∀ B : Subgroup (MulAut Pt),
      IsElemAbelian2 (H9Iso.isoAut e.symm B) ↔ IsElemAbelian2 B := fun B => by
    rw [← H9Iso.isElemAbelian2_isoAut_iff e, hinv]
  have hmemA : ∀ B ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut Pt))),
      H9Iso.isoAut e.symm B ≤ M ∧ IsElemAbelian2 (H9Iso.isoAut e.symm B) ∧
        Nat.card (H9Iso.isoAut e.symm B) = 2 ^ 4 := fun B hB => by
    obtain ⟨h1, h2, h3⟩ := hA B hB
    exact ⟨(hle B).mpr h1, (hea B).mpr h2, by rw [H9Iso.card_isoAut]; exact h3⟩
  refine ⟨H9Iso.isoAut e.symm A₀, H9Iso.isoAut e.symm A₁, H9Iso.isoAut e.symm A₂, ?_, ?_,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro A hA'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA'
    rcases hA' with rfl | rfl | rfl
    · exact hmemA A₀ (by simp)
    · exact hmemA A₁ (by simp)
    · exact hmemA A₂ (by simp)
  · intro A hAM hAe hAc
    have h1 : H9Iso.isoAut e A ≤ modelM4 := by
      rw [← hM]
      exact (H9Iso.isoAut_le_iff e).mpr hAM
    obtain ⟨m', hm', hm⟩ := hcl _ h1 (H9Iso.isElemAbelian2_isoAut e hAe)
      (by rw [H9Iso.card_isoAut]; exact hAc)
    have hmM : (MulAut.congr e).symm m' ∈ M := by
      rw [← H9Iso.mem_isoAut, hM]
      exact hm'
    have key : ∀ B, H9Iso.isoAut e A = conjAut B m' →
        A = conjAut (H9Iso.isoAut e.symm B) ((MulAut.congr e).symm m') := fun B h => by
      have h2 : H9Iso.isoAut e (conjAut (H9Iso.isoAut e.symm B) ((MulAut.congr e).symm m')) =
          H9Iso.isoAut e A := by
        rw [H9Iso.conjAut_isoAut, hinv, MulEquiv.apply_symm_apply, h]
      exact le_antisymm ((H9Iso.isoAut_le_iff e).mp h2.ge) ((H9Iso.isoAut_le_iff e).mp h2.le)
    refine ⟨_, hmM, ?_⟩
    rcases hm with h | h | h
    · exact Or.inl (key _ h)
    · exact Or.inr (Or.inl (key _ h))
    · exact Or.inr (Or.inr (key _ h))
  · rw [H9Iso.card_fixV_isoAut]
    exact h0f
  · rw [← H9Iso.gammaCheck_isoAut_eq_top_iff e, hinv]
    exact h0g
  · rw [H9Iso.card_fixV_isoAut]
    exact h1f
  · rw [H9Iso.card_gammaCheck_isoAut]
    exact h1g
  · rw [H9Iso.card_fixV_isoAut]
    exact h2f
  · rw [H9Iso.card_gammaCheck_isoAut]
    exact h2g
  · intro a ha hfa
    have ha' : MulAut.congr e a ∈ A₂ := by
      rw [← hinv A₂]
      exact (H9Iso.congr_mem_isoAut e).mpr ha
    have h1 := h2faith _ ha' fun w hw => by
      rw [← hinv A₂, H9Iso.gammaCheck_isoAut] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      rw [MulEquiv.coe_toMonoidHom, H9Iso.congr_apply', hfa u hu]
    rwa [map_eq_one_iff _ (MulAut.congr e).injective] at h1
  · have h7' : ∀ B ∈ ({A₁, A₂} : Set (Subgroup (MulAut Pt))),
        (∃ b ∈ H9Iso.isoAut e.symm B ⊓ L, IsTransvOn b W₁) ∧
          (∃ b ∈ H9Iso.isoAut e.symm B ⊓ L, b ≠ 1 ∧ ¬ IsTransvOn b W₁) ∧
          2 ^ 7 ≤ Nat.card (gammaCheck 3 (H9Iso.isoAut e.symm B)) := by
      intro B hB
      obtain ⟨⟨b, hb, hbt⟩, ⟨b', hb', hb'1, hb't⟩, hg3⟩ := h7 B hB
      have hmem : ∀ x ∈ B ⊓ modelL4,
          (MulAut.congr e).symm x ∈ H9Iso.isoAut e.symm B ⊓ L := fun x hx => by
        rw [← H9Iso.mem_isoAut, H9Iso.isoAut_inf, hinv, hL]
        exact hx
      have htr : ∀ x : MulAut Pt,
          IsTransvOn ((MulAut.congr e).symm x) W₁ ↔ IsTransvOn x ptW₁ := fun x => by
        rw [← H9Iso.isTransvOn_congr e, MulEquiv.apply_symm_apply, hW₁]
      refine ⟨⟨_, hmem b hb, (htr b).mpr hbt⟩, ⟨_, hmem b' hb', ?_,
        fun h => hb't ((htr b').mp h)⟩, by rw [H9Iso.card_gammaCheck_isoAut]; exact hg3⟩
      rwa [ne_eq, map_eq_one_iff _ (MulAut.congr e).symm.injective]
    intro A hA'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA'
    rcases hA' with rfl | rfl
    · exact h7' A₁ (by simp)
    · exact h7' A₂ (by simp)

theorem lemH9Rank4_holds : LemH9Rank4 := by
  intro W _ _ M L T W₁ W₂ hyp A hAM hA
  obtain ⟨e, hM, -, -, -⟩ := exists_modelIso hyp
  rw [← H9Iso.card_isoAut e A]
  exact model_card_le (by rw [← hM]; exact (H9Iso.isoAut_le_iff e).mpr hAM)
    (H9Iso.isElemAbelian2_isoAut e hA)

theorem lemH9FF4_holds : LemH9FF4 := by
  intro W _ _ M L T W₁ W₂ hyp A hAM hA hA1 hff
  obtain ⟨e, hM, hL, -, -⟩ := exists_modelIso hyp
  rw [← H9Iso.isoAut_le_iff e, hL]
  refine model_le_L (by rw [← hM]; exact (H9Iso.isoAut_le_iff e).mpr hAM)
    (H9Iso.isElemAbelian2_isoAut e hA) (fun h => hA1 ((H9Iso.isoAut_eq_bot_iff e).mp h)) ?_
  rw [H9Iso.card_isoAut, H9Iso.card_fixV_isoAut, ← Nat.card_congr e.toEquiv]
  exact hff

end CFSG.Quasithin.H13.H9Four

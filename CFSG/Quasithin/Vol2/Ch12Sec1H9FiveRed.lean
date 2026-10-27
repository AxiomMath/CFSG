module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9FiveU
public import CFSG.Quasithin.Vol2.Ch12Sec1H9LinFacts

public section

namespace CFSG.Quasithin.H13.H9Lin

open CFSG.Open CFSG.Quasithin.E3 CFSG.ComponentClassification.CatalogueBGraphForm H9Coord H9FiveU
open scoped Matrix

variable {W : Type} [CommGroup W]

theorem exists_fix_of_commOn [Finite W] {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    {U : Subgroup W}
    {w : W} (hw : w ∈ U) {k : ℕ} (hk : Nat.card (commOn A U) ≤ 2 ^ k) :
    ∃ X ≤ A, mQuot A X ≤ k ∧ w ∈ fixV X := by
  set X : Subgroup (MulAut W) := (MulAction.stabilizer ↥A w).map A.subtype with hXdef
  have hXA : X ≤ A := Subgroup.map_subtype_le _
  have hmemX : ∀ x ∈ X, x w = w := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  refine ⟨X, hXA, ?_, fun x hx => hmemX x hx⟩
  have h1 : Nat.card (MulAction.orbit ↥A w) * Nat.card (MulAction.stabilizer ↥A w) =
      Nat.card ↥A := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Subgroup.index_mul_card _
  have hXc : Nat.card X = Nat.card (MulAction.stabilizer ↥A w) :=
    Subgroup.card_map_of_injective A.subtype_injective
  have horb : Nat.card (MulAction.orbit ↥A w) ≤ Nat.card (commOn A U) := by
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1 * w⁻¹, ?_⟩) ?_
    · obtain ⟨g, hg⟩ := y.2
      rw [← hg]
      exact mem_commOn_of g.2 hw
    · intro y y' h
      have := congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel this)
  have hp : IsPGroup 2 ↥A := isPGroup_of_isElemAbelian2 hA
  have h2 := card_eq_two_pow_mul hp hXA
  have hpos : 0 < Nat.card X := Nat.card_pos
  have h3 : 2 ^ mQuot A X * Nat.card X ≤ 2 ^ k * Nat.card X := by
    rw [← h2, ← h1, hXc]
    exact Nat.mul_le_mul_right _ (horb.trans hk)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h3 hpos)

variable {L : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}

theorem mem_glImage {X : Subgroup (MulAut W)} {φ : ↥L ≃* GL (Fin 5) (ZMod 2)}
    {g : GL (Fin 5) (ZMod 2)} :
    g ∈ (X.subgroupOf L).map φ.toMonoidHom ↔ ∃ l : ↥L, (l : MulAut W) ∈ X ∧ φ l = g := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩

theorem glImage_props {X : Subgroup (MulAut W)} (hXL : X ≤ L) (hX : IsElemAbelian2 X)
    (φ : ↥L ≃* GL (Fin 5) (ZMod 2)) :
    (∀ x ∈ (X.subgroupOf L).map φ.toMonoidHom, ∀ y ∈ (X.subgroupOf L).map φ.toMonoidHom,
      x * y = y * x) ∧ (∀ x ∈ (X.subgroupOf L).map φ.toMonoidHom, x * x = 1) ∧
      Nat.card ((X.subgroupOf L).map φ.toMonoidHom) = Nat.card X := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hX.1 _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  · rintro _ ⟨x, hx, rfl⟩
    have h : x * x = 1 := Subtype.ext (by
      have := hX.2 _ (Subgroup.mem_subgroupOf.mp hx)
      rw [pow_two] at this
      exact this)
    rw [← map_mul, h, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv

theorem card_fixV_inf_W₁ [Finite W] {X : Subgroup (MulAut W)} (hXL : X ≤ L) (e : W ≃* Vec 5 × Vec 5)
    (φ : ↥L ≃* GL (Fin 5) (ZMod 2))
    (hLe : ∀ l : ↥L, ∀ w : W, e ((l : MulAut W) w) =
      (vecAut (φ l) (e w).1, vecAut (glGraphAut 5 (ZMod 2) (φ l)) (e w).2))
    (hW₁ : ∀ w, w ∈ W₁ ↔ (e w).2 = 1) :
    Nat.card ↥(fixV X ⊓ W₁) = Nat.card (fixVecS ((X.subgroupOf L).map φ.toMonoidHom)) := by
  refine Nat.card_congr
    { toFun := fun w => ⟨(e w.1).1.toAdd, fun g hg => ?_⟩
      invFun := fun x => ⟨e.symm (Multiplicative.ofAdd x.1, 1), Subgroup.mem_inf.mpr
        ⟨fun b hb => ?_, (hW₁ _).mpr (by simp)⟩⟩
      left_inv := fun w => Subtype.ext ?_
      right_inv := fun x => Subtype.ext (by simp) }
  · obtain ⟨l, hlX, rfl⟩ := mem_glImage.mp hg
    have h1 : e ((l : MulAut W) w.1) = e w.1 := by
      rw [(Subgroup.mem_inf.mp w.2).1 _ hlX]
    rw [hLe] at h1
    have h2 := congrArg (fun q => q.1.toAdd) h1
    simp only [vecAut_apply, toAdd_ofAdd] at h2
    exact h2
  · apply e.injective
    have h1 := hLe ⟨b, hXL hb⟩ (e.symm (Multiplicative.ofAdd x.1, 1))
    simp only [MulEquiv.apply_symm_apply] at h1
    have hg : (↑(φ ⟨b, hXL hb⟩) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x.1 = x.1 :=
      x.2 _ (mem_glImage.mpr ⟨⟨b, hXL hb⟩, hb, rfl⟩)
    rw [MulEquiv.apply_symm_apply]
    refine h1.trans (Prod.ext ?_ (map_one _))
    simp only [vecAut_apply, toAdd_ofAdd, hg]
  · have h2 : (e w.1).2 = 1 := (hW₁ _).mp (Subgroup.mem_inf.mp w.2).2
    show e.symm (Multiplicative.ofAdd (e w.1).1.toAdd, 1) = w.1
    rw [ofAdd_toAdd, ← h2, Prod.mk.eta, MulEquiv.symm_apply_apply]

theorem card_fixV_inf_W₂ [Finite W] {X : Subgroup (MulAut W)} (hXL : X ≤ L) (e : W ≃* Vec 5 × Vec 5)
    (φ : ↥L ≃* GL (Fin 5) (ZMod 2))
    (hLe : ∀ l : ↥L, ∀ w : W, e ((l : MulAut W) w) =
      (vecAut (φ l) (e w).1, vecAut (glGraphAut 5 (ZMod 2) (φ l)) (e w).2))
    (hW₂ : ∀ w, w ∈ W₂ ↔ (e w).1 = 1) :
    Nat.card ↥(fixV X ⊓ W₂) = Nat.card (fixVecTS ((X.subgroupOf L).map φ.toMonoidHom)) := by
  refine Nat.card_congr
    { toFun := fun w => ⟨(e w.1).2.toAdd, fun g hg => ?_⟩
      invFun := fun y => ⟨e.symm (1, Multiplicative.ofAdd y.1), Subgroup.mem_inf.mpr
        ⟨fun b hb => ?_, (hW₂ _).mpr (by simp)⟩⟩
      left_inv := fun w => Subtype.ext ?_
      right_inv := fun y => Subtype.ext (by simp) }
  · obtain ⟨l, hlX, rfl⟩ := mem_glImage.mp hg
    have h1 : e (((l⁻¹ : ↥L) : MulAut W) w.1) = e w.1 := by
      rw [(Subgroup.mem_inf.mp w.2).1 _ (by simpa using X.inv_mem hlX)]
    rw [hLe] at h1
    have h2 := congrArg (fun q => q.2.toAdd) h1
    simp only [vecAut_apply, toAdd_ofAdd] at h2
    rwa [glGraphAut_matrix, map_inv, inv_inv] at h2
  · apply e.injective
    have h1 := hLe ⟨b, hXL hb⟩ (e.symm (1, Multiplicative.ofAdd y.1))
    simp only [MulEquiv.apply_symm_apply] at h1
    have hg : (↑(φ ⟨b, hXL hb⟩)⁻¹ : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ y.1 = y.1 := by
      have := y.2 _ (mem_glImage.mpr ⟨⟨b, hXL hb⟩⁻¹, X.inv_mem hb, rfl⟩)
      rwa [map_inv] at this
    rw [MulEquiv.apply_symm_apply]
    refine h1.trans (Prod.ext (map_one _) ?_)
    simp only [vecAut_apply, toAdd_ofAdd, glGraphAut_matrix, hg]
  · have h2 : (e w.1).1 = 1 := (hW₂ _).mp (Subgroup.mem_inf.mp w.2).2
    show e.symm (1, Multiplicative.ofAdd (e w.1).2.toAdd) = w.1
    rw [ofAdd_toAdd, ← h2, Prod.mk.eta, MulEquiv.symm_apply_apply]

theorem lemH92Use_holds : LemH92Use := by
  intro W _ _ M L T W₁ W₂ β hyp hβ A hAM hA h32
  have hn : 3 ≤ 5 := by norm_num
  obtain ⟨e, φ, hLe, hMe, hW₁, hW₂⟩ := exists_linIso hyp hn
  obtain ⟨β', hβ', hcard₁, hcard₂⟩ := exists_goodDual hyp hn
  have hsurj : ∀ p, e (e.symm p) = p := fun p => MulEquiv.apply_symm_apply e p
  have hAL : A ≤ L := by
    intro a haA
    by_contra haL
    obtain ⟨P, hP⟩ := hMe a (hAM haA) haL
    have haa : ∀ w, a (a w) = w := fun w => by
      rw [← MulAut.mul_apply, ← pow_two, hA.2 a haA, MulAut.one_apply]
    have hPP : P * glGraphAut 5 (ZMod 2) P = 1 := by
      apply vecHom_injective
      refine MulEquiv.ext fun x => ?_
      show vecAut (P * _) x = vecAut 1 x
      rw [vecAut_mul_apply, vecAut_one, MulAut.one_apply]
      have h1 := congrArg (fun q => q.1) (congrArg e (haa (e.symm (x, 1))))
      simp only [hP, hsurj] at h1
      exact h1
    have hδ : glGraphAut 5 (ZMod 2) P = P⁻¹ := eq_inv_of_mul_eq_one_right hPP
    set Pm : Matrix (Fin 5) (Fin 5) (ZMod 2) := ↑P with hPm
    have hPsym : Pmᵀ = Pm := by
      set Qm : Matrix (Fin 5) (Fin 5) (ZMod 2) := ↑P⁻¹ with hQm
      have hPQ : Pm * Qm = 1 := by
        rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hQt : Qmᵀ = Qm := by
        rw [hQm, ← glGraphAut_matrix, hδ]
      have h1 : Qm * Pmᵀ = 1 := by
        rw [← hQt, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
      calc Pmᵀ = Pm * Qm * Pmᵀ := by rw [hPQ, Matrix.one_mul]
        _ = Pm := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    have hPdet : Pm.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).ne_zero
    have hcomP : ∀ l : ↥L, (l : MulAut W) ∈ A →
        (↑(φ l) : Matrix (Fin 5) (Fin 5) (ZMod 2)) * Pm *
          (↑(φ l) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = Pm := by
      intro l hl
      have hal : ∀ w, a ((l : MulAut W) w) = (l : MulAut W) (a w) := fun w => by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, hA.1 a haA _ hl]
      have hGL : P * glGraphAut 5 (ZMod 2) (φ l) = φ l * P := by
        apply vecHom_injective
        refine MulEquiv.ext fun y => ?_
        show vecAut (P * _) y = vecAut (φ l * P) y
        rw [vecAut_mul_apply, vecAut_mul_apply]
        have h1 := congrArg (fun q => q.1) (congrArg e (hal (e.symm (1, y))))
        simp only [hP, hLe, hsurj] at h1
        exact h1
      have hm := congrArg Units.val hGL
      rw [Units.val_mul, Units.val_mul, glGraphAut_matrix] at hm
      set G : Matrix (Fin 5) (Fin 5) (ZMod 2) := ↑(φ l) with hG
      set Gi : Matrix (Fin 5) (Fin 5) (ZMod 2) := ↑(φ l)⁻¹ with hGi
      have hGGi : G * Gi = 1 := by
        rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc G * Pm * Gᵀ = Pm * Giᵀ * Gᵀ := by rw [← hm]
        _ = Pm := by
          rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hGGi, Matrix.transpose_one,
            Matrix.mul_one]
    have hidx : L.relIndex A ≤ 2 := by
      have h1 := Subgroup.relIndex_le_of_le_right (H := L) hAM (by rw [hyp.index]; norm_num)
      rwa [hyp.index] at h1
    have h16 : 2 ^ 4 ≤ Nat.card ↥(A ⊓ L) := by
      have h1 := Subgroup.relIndex_mul_card (H := L) (K := A)
      have h2 : L.relIndex A * Nat.card ↥(L ⊓ A) ≤ 2 * Nat.card ↥(L ⊓ A) :=
        Nat.mul_le_mul_right _ hidx
      rw [inf_comm, show (2 : ℕ) ^ 4 = 16 by norm_num]
      rw [show (2 : ℕ) ^ 5 = 32 by norm_num] at h32
      omega
    have hAL' : IsElemAbelian2 (A ⊓ L) :=
      ⟨fun x hx y hy => hA.1 x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1,
        fun x hx => hA.2 x (Subgroup.mem_inf.mp hx).1⟩
    obtain ⟨hc, hs, hcard⟩ := glImage_props inf_le_right hAL' φ
    obtain ⟨g, hg, hne⟩ := gl5_noForm hc hs (hcard ▸ h16) hPsym hPdet
    obtain ⟨l, hlA, rfl⟩ := mem_glImage.mp hg
    exact hne (hcomP l (Subgroup.mem_inf.mp hlA).1)
  obtain ⟨hc, hs, hcardS⟩ := glImage_props hAL hA φ
  have hF₁ := card_fixV_inf_W₁ hAL e φ hLe hW₁
  have hF₂ := card_fixV_inf_W₂ hAL e φ hLe hW₂
  have hD := card_comm_mul_card_fixT ((A.subgroupOf L).map φ.toMonoidHom)
  have hC₂ := card_fix₂_mul hyp hβ' hcard₁ hAL
  have hC₁ := card_fix₁_mul hyp hβ' hcard₂ hAL
  have hlarge := gl5_large hc hs (hcardS ▸ h32)
  rw [show (2 : ℕ) ^ 5 = 32 by norm_num] at hD hC₁ hC₂
  have hgamma : ∀ U : Subgroup W, Nat.card (commOn A U) ≤ 2 ^ 3 → U ≤ gammaCheck 3 A := by
    intro U hU w hw
    obtain ⟨X, hXA, hXk, hwX⟩ := exists_fix_of_commOn hA hw hU
    exact H9Conj.fixV_le_gammaCheck hXA hXk hwX
  have hpos₁ : 0 < Nat.card ↥(fixV A ⊓ W₁) := Nat.card_pos
  have hpos₂ : 0 < Nat.card ↥(fixV A ⊓ W₂) := Nat.card_pos
  have hcomm : Nat.card (commOn A W₁) ≤ 2 ^ 3 ∧ Nat.card (commOn A W₂) ≤ 2 ^ 3 ∧
      (Nat.card ↥(fixV A ⊓ W₁) ≤ 2 ^ 2 ∨ Nat.card ↥(fixV A ⊓ W₂) ≤ 2 ^ 2) := by
    rw [hF₁] at hC₁ ⊢
    rw [hF₂] at hC₂ ⊢
    rcases hlarge with ⟨hc4, hf4⟩ | ⟨hc8, hf8⟩
    · have e1 : Nat.card (fixVecTS ((A.subgroupOf L).map φ.toMonoidHom)) = 8 := by
        rw [hc4] at hD
        omega
      rw [e1] at hC₂
      rw [hf4] at hC₁ ⊢
      refine ⟨?_, ?_, Or.inl (by norm_num)⟩ <;> norm_num <;> omega
    · have e1 : Nat.card (fixVecTS ((A.subgroupOf L).map φ.toMonoidHom)) = 4 := by
        rw [hc8] at hD
        omega
      rw [e1] at hC₂ ⊢
      rw [hf8] at hC₁
      refine ⟨?_, ?_, Or.inr (by norm_num)⟩ <;> norm_num <;> omega
  refine ⟨hAL, ?_, hcomm.2.2⟩
  rw [eq_top_iff, ← hyp.sup]
  exact sup_le (hgamma W₁ hcomm.1) (hgamma W₂ hcomm.2.1)

end CFSG.Quasithin.H13.H9Lin

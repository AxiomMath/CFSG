module

public import CFSG.Quasithin.Background.SmithB42LnL5Off

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix
open CFSG.Assembly.LowTwoRank

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

theorem comm_R4 : ∀ a ∈ R4, ∀ b ∈ R4, a * b = b * a := by
  intro a ha b hb
  obtain ⟨w, hw, hwa⟩ := mem_R4_iff.1 ha
  obtain ⟨w', hw', hwb⟩ := mem_R4_iff.1 hb
  apply Subtype.ext
  show (a : 𝕄) * (b : 𝕄) = (b : 𝕄) * (a : 𝕄)
  have h1 : (Pi.single 4 1 : Fin 5 → ZMod 2) ⬝ᵥ w' = 0 := by
    rw [single_dotProduct, one_mul, hw']
  have h2 : (Pi.single 4 1 : Fin 5 → ZMod 2) ⬝ᵥ w = 0 := by
    rw [single_dotProduct, one_mul, hw]
  rw [hwa, hwb, tv_mul_tv, tv_mul_tv, h1, h2, zero_smul, zero_smul, add_zero, add_zero]
  abel

theorem sq_R4 : ∀ a ∈ R4, a * a = 1 := by
  intro a ha
  obtain ⟨w, hw, hwa⟩ := mem_R4_iff.1 ha
  apply Subtype.ext
  show (a : 𝕄) * (a : 𝕄) = 1
  rw [hwa, tvR_mul_self w hw]

theorem aut5_cases (τ : G5 ≃* G5) : ∃ P : GL (Fin 5) (ZMod 2),
    (∀ x : G5, ((τ x : G5) : 𝕄) = (P : 𝕄) * (x : 𝕄) * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)) ∨
      (∀ x : G5, ((τ x : G5) : 𝕄) =
        (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)) := by
  obtain ⟨P, hP | hP⟩ := B5.Ln.aut_cases (by norm_num) ((E5.symm.trans τ).trans E5)
  · refine ⟨P, Or.inl fun x => ?_⟩
    have := hP (E5 x)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    rw [mat_E5, mat_E5] at this
    exact this
  · refine ⟨P, Or.inr fun x => ?_⟩
    have := hP (E5 x)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    rw [mat_E5, B5.Ln.dmat, ← map_inv, mat_E5] at this
    exact this

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

noncomputable abbrev fLk (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (κ : G5 ≃* G5) : G5 →* MulAut V :=
  (fL e).comp κ.symm.toMonoidHom

omit [Finite V] in
theorem fLk_injective (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (κ : G5 ≃* G5) :
    Function.Injective (fLk e κ) := fun _ _ h => κ.symm.injective (fL_injective e h)

section Coords

variable [Module (ZMod 2) (Additive V)] {e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))} {κ : G5 ≃* G5}
  {β : Additive V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)}

omit [Finite V] in
theorem coord_fLk (hβ : ∀ g w, β (repOf (phiOf e) g w) = wedgeRep (κ g) (β w)) (g : G5)
    (v : V) : β (Additive.ofMul (fLk e κ g v)) = wedgeMat (g : 𝕄) *ᵥ β (Additive.ofMul v) := by
  have h := hβ (κ.symm g) (Additive.ofMul v)
  rw [repOf_apply, MulEquiv.apply_symm_apply, wedgeRep_apply'] at h
  exact h

omit [Finite V] in
theorem card_fixV_map_fLk (hβ : ∀ g w, β (repOf (phiOf e) g w) = wedgeRep (κ g) (β w))
    (Y : Subgroup G5) : Nat.card (fixV (Y.map (fLk e κ))) = Nat.card (FixW Y) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨β (Additive.ofMul (v : V)), fun u hu => ?_⟩
      invFun := fun x => ⟨Additive.toMul (β.symm x.1), ?_⟩
      left_inv := fun v => Subtype.ext ?_
      right_inv := fun x => Subtype.ext ?_ }
  · rw [← coord_fLk hβ u v, v.2 (fLk e κ u) ⟨u, hu, rfl⟩]
  · rintro _ ⟨u, hu, rfl⟩
    apply Additive.ofMul.injective
    apply β.injective
    rw [coord_fLk hβ, ofMul_toMul, LinearEquiv.apply_symm_apply]
    exact x.2 u hu
  · show Additive.toMul (β.symm (β (Additive.ofMul (v : V)))) = v
    rw [LinearEquiv.symm_apply_apply, toMul_ofMul]
  · show β (Additive.ofMul (Additive.toMul (β.symm x.1))) = x.1
    rw [ofMul_toMul, LinearEquiv.apply_symm_apply]

omit [Finite V] in
theorem card_V_eq (β : Additive V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)) : Nat.card V = 2 ^ 10 := by
  rw [show Nat.card V = Nat.card (Additive V) from rfl, Nat.card_congr β.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  rfl

omit [Finite V] [Module (ZMod 2) (Additive V)] in
theorem map_fLk_comap {B : Subgroup (MulAut V)} (hBL : B ≤ L) :
    ((B.comap (fL e)).map κ.toMonoidHom).map (fLk e κ) = B := by
  ext x
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    show fL e (κ.symm (κ s)) ∈ B
    rw [MulEquiv.symm_apply_apply]
    exact hs
  · intro hx
    obtain ⟨g, rfl⟩ := exists_fL_eq e (hBL hx)
    refine ⟨κ g, ⟨g, hx, rfl⟩, ?_⟩
    show fL e (κ.symm (κ g)) = fL e g
    rw [MulEquiv.symm_apply_apply]

omit [Finite V] in
theorem card_mul_fixV_le_of_le (hβ : ∀ g w, β (repOf (phiOf e) g w) = wedgeRep (κ g) (β w))
    {B : Subgroup (MulAut V)} (hBL : B ≤ L) (hB : IsElemAbelian2 B) :
    Nat.card B * Nat.card (fixV B) ≤ 2 ^ 10 ∧
      (2 ^ 10 ≤ Nat.card B * Nat.card (fixV B) → B ≠ ⊥ →
        ∃ h : G5, B = (R4.map (MulAut.conj h).toMonoidHom).map (fLk e κ)) := by
  set Y : Subgroup G5 := (B.comap (fL e)).map κ.toMonoidHom with hY
  have hBY : Y.map (fLk e κ) = B := map_fLk_comap hBL
  have hcY : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, comm_of_comap hB a ha b hb]
  have h2Y : ∀ a ∈ Y, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, sq_of_comap hB a ha, map_one]
  have hcard : Nat.card B = Nat.card Y := by
    rw [← hBY]
    exact Subgroup.card_map_of_injective (fLk_injective e κ)
  have hfix : Nat.card (fixV B) = Nat.card (FixW Y) := by
    rw [← card_fixV_map_fLk hβ Y, hBY]
  have key := card_mul_fixW_le' hcY h2Y
  rw [hcard, hfix]
  refine ⟨key.1, fun hge hB1 => ?_⟩
  have hY1 : Y ≠ ⊥ := by
    intro h0
    apply hB1
    rw [← hBY, h0, Subgroup.map_bot]
  obtain ⟨h, hh⟩ := key.2 hge hY1
  exact ⟨h, by rw [← hBY, hh]⟩

omit [Module (ZMod 2) (Additive V)] in
theorem conj_fLk (hHyp : B4Hyp G L) {a : MulAut V} (haG : a ∈ G) (g : G5) :
    a * fLk e κ g * a⁻¹ = fLk e κ (κ (conjG5 hHyp e haG (κ.symm g))) := by
  show a * fL e (κ.symm g) * a⁻¹ = fL e (κ.symm (κ (conjG5 hHyp e haG (κ.symm g))))
  rw [MulEquiv.symm_apply_apply, fL_apply, fL_apply, conjG5_spec]

theorem eq_L (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (hβ : ∀ g w, β (repOf (phiOf e) g w) = wedgeRep (κ g) (β w)) : G = L := by
  by_contra hGL
  obtain ⟨a, haG, haL⟩ : ∃ a ∈ G, a ∉ L := by
    by_contra hall
    push Not at hall
    exact hGL (le_antisymm hall (le_G hHyp))
  set σ := conjG5 hHyp e haG with hσ
  set τ : G5 ≃* G5 := (κ.symm.trans σ).trans κ with hτ
  have hτapp : ∀ g, τ g = κ (σ (κ.symm g)) := fun g => rfl
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 5) (ZMod 2), ∀ x : G5,
      ((τ x : G5) : 𝕄) = (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) := by
    obtain ⟨P, hP | hP⟩ := aut5_cases τ
    · exfalso
      apply haL
      set m : G5 := κ.symm (ofGL5 P) with hm
      refine mem_of_conjG5_eq hHyp hZ e haG (Matrix.SpecialLinearGroup.toGL m) fun y => ?_
      have h1 : τ (κ y) = ofGL5 P * κ y * (ofGL5 P)⁻¹ := by
        apply Subtype.ext
        rw [hP, ofGL5_inv]
        rfl
      have h2 : σ y = m * y * m⁻¹ := by
        have : σ y = κ.symm (τ (κ y)) := by rw [hτapp, MulEquiv.symm_apply_apply,
          MulEquiv.symm_apply_apply]
        rw [this, h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rw [h2]
      rfl
    · exact ⟨P, hP⟩
  set p : 𝕄 := (P : 𝕄)
  set q : 𝕄 := ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)
  have hpq : p * q = 1 := GL_mul_inv P
  have hqp : q * p = 1 := GL_inv_mul P
  set R' : Subgroup G5 := R4.map τ.toMonoidHom with hR'
  have hcR' : ∀ x ∈ R', ∀ y ∈ R', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, comm_R4 x hx y hy]
  have h2R' : ∀ x ∈ R', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, sq_R4 x hx, map_one]
  have hmapR' : R'.map (fLk e κ) = (R4.map (fLk e κ)).map (MulAut.conj a).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨fLk e κ r, ⟨r, hr, rfl⟩, ?_⟩
      show a * fLk e κ r * a⁻¹ = fLk e κ (τ r)
      rw [conj_fLk hHyp haG, hτapp]
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨τ r, ⟨r, hr, rfl⟩, ?_⟩
      show fLk e κ (τ r) = a * fLk e κ r * a⁻¹
      rw [conj_fLk hHyp haG, hτapp]
  have hcardR' : Nat.card R' = 16 := by
    rw [hR', Subgroup.card_map_of_injective τ.injective, card_R4]
  have hfixR' : 64 ≤ Nat.card (FixW R') := by
    have hidx := CFSG.QuasithinUnique.B42A57.index_fixV_conj (R4.map (fLk e κ)) a
    have h1 := Subgroup.index_mul_card (fixV ((R4.map (fLk e κ)).map (MulAut.conj a).toMonoidHom))
    have h2 := Subgroup.index_mul_card (fixV (R4.map (fLk e κ)))
    rw [hidx] at h1
    have h3 : Nat.card (fixV ((R4.map (fLk e κ)).map (MulAut.conj a).toMonoidHom)) =
        Nat.card (fixV (R4.map (fLk e κ))) :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (h1.trans h2.symm)
    rw [← card_fixV_map_fLk hβ, hmapR', h3, card_fixV_map_fLk hβ]
    exact card_fixW_R4
  have hR'1 : R' ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hcardR'
    norm_num at hcardR'
  obtain ⟨h, hh⟩ := (card_mul_fixW_le' hcR' h2R').2
    (by rw [hcardR']; calc 2 ^ 10 = 16 * 64 := by norm_num
                        _ ≤ 16 * _ := Nat.mul_le_mul_left _ hfixR') hR'1
  have htv : ∀ (i : Fin 4) (hi : i.castSucc ≠ 4),
      IsTv (τ (eT i.castSucc 4 hi)) (p *ᵥ Pi.single 4 1) (Pi.single i.castSucc 1 ᵥ* q) := by
    intro i hi
    have hinv : (eT i.castSucc 4 hi)⁻¹ = eT i.castSucc 4 hi :=
      inv_eq_of_mul_eq_one_right (eT_mul_self _ _ hi)
    refine ⟨?_, fun h0 => ?_, fun h0 => ?_, ?_⟩
    · rw [hP, hinv, coe_eT, eTM_eq _ _ hi, transpose_add, transpose_one, transpose_vecMulVec,
        Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hpq, mul_vecMulVec, vecMulVec_mul]
    · have := congrArg (q *ᵥ ·) h0
      simp only [mulVec_mulVec, hqp, one_mulVec, mulVec_zero] at this
      exact absurd (congrFun this 4) (by simp)
    · have := congrArg (· ᵥ* p) h0
      simp only [vecMul_vecMul, hqp, vecMul_one, zero_vecMul] at this
      exact absurd (congrFun this i.castSucc) (by simp)
    · rw [dotProduct_mulVec, vecMul_vecMul, hqp, vecMul_one, single_dotProduct, one_mul,
        Pi.single_eq_of_ne hi]
  have haxis : ∀ (i : Fin 4) (hi : i.castSucc ≠ 4),
      Pi.single i.castSucc 1 ᵥ* q = Pi.single 4 1 ᵥ* ((h⁻¹ : G5) : 𝕄) := by
    intro i hi
    have hmem : τ (eT i.castSucc 4 hi) ∈ R4.map (MulAut.conj h).toMonoidHom := by
      rw [← hh]
      exact ⟨_, eT_mem_R4 i hi, rfl⟩
    obtain ⟨w, hw, hwe⟩ := (mem_conj_R4_iff h).1 hmem
    have hψ0 : Pi.single 4 1 ᵥ* ((h⁻¹ : G5) : 𝕄) ≠ 0 := by
      intro h0
      have := congrArg (· ᵥ* ((h : G5) : 𝕄)) h0
      simp only [vecMul_vecMul, coe_inv_mul, vecMul_one, zero_vecMul] at this
      exact absurd (congrFun this 4) (by simp)
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, zero_vecMulVec, add_zero] at hwe
      have h1 : τ (eT i.castSucc 4 hi) = 1 := Subtype.ext hwe
      have h2 : eT i.castSucc 4 hi = 1 := τ.injective (h1.trans (map_one τ).symm)
      have h3 := congrArg (fun g : G5 => (g : 𝕄) i.castSucc 4) h2
      simp only [coe_eT, Matrix.SpecialLinearGroup.coe_one] at h3
      revert h3
      fin_cases i <;> decide
    exact ((htv i hi).unique ⟨hwe, hw0, hψ0, hw⟩).2
  have h01 := (haxis 0 (by decide)).trans (haxis 1 (by decide)).symm
  have := congrArg (· ᵥ* p) h01
  simp only [vecMul_vecMul, hqp, vecMul_one] at this
  exact absurd (congrFun this 0) (by simp)

theorem case11 (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (hA : IsFFStarOffender G A)
    (hβ : ∀ g w, β (repOf (phiOf e) g w) = wedgeRep (κ g) (β w)) : B42Case11 G L A := by
  have hGL : G = L := eq_L hHyp hZ hβ
  have hV10 : Nat.card V = 2 ^ 10 := card_V_eq β
  have hJ : ffJ G = L := le_antisymm (hGL ▸ B6.ffJ_le G) (B5.Ln.le_ffJ_of_center hHyp hZ hA)
  have hAL : A ≤ L := hGL ▸ hA.1
  have hoff : 2 ^ 10 ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
    rwa [B1.card_bot_mul_card_fixV, hV10] at this
  obtain ⟨h, hh⟩ := (card_mul_fixV_le_of_le hβ hAL hA.2.2.1).2 hoff hA.2.1
  refine ⟨hGL.trans hJ.symm, hJ, hV10, ?_, piW e κ, realizesVia_extSq_of_wedge e hβ, ?_⟩
  ·
    refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hA, ?_⟩
    · have hBL : B ≤ L := hGL ▸ hB.1
      have hle := (card_mul_fixV_le_of_le hβ hBL hB.2.2.1).1
      rw [← not_lt, rAV_lt_one_iff hV hB.isA2, not_lt, hV10]
      exact hle
    · rw [rAV_le_one_iff hV hA.isA2, hV10]
      exact hoff
  ·
    right
    refine ⟨Pi.single 4 1 ᵥ* ((h⁻¹ : G5) : 𝕄), fun h0 => ?_, fun g => ?_⟩
    · have := congrArg (· ᵥ* ((h : G5) : 𝕄)) h0
      simp only [vecMul_vecMul, coe_inv_mul, vecMul_one, zero_vecMul] at this
      exact absurd (congrFun this 4) (by simp)
    · rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_piW]
      change fLk e κ (E5.symm g) ∈ A ↔ _
      rw [hh, Subgroup.mem_map_iff_mem (fLk_injective e κ), mem_conj_R4_iff, coe_E5_symm]
      rfl

end Coords

end CFSG.Quasithin.B42Ln

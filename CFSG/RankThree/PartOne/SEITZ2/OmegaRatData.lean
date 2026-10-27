module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaGen
public import CFSG.RankThree.PartOne.SEITZ2.OmegaLift
public import CFSG.RankThree.PartOne.SEITZ2.OmegaProj
public import CFSG.RankThree.PartOne.SEITZ2.OmegaFrameModel
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson
public import CFSG.RankThree.PartOne.SEITZ2.OmegaDescent

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (regular_coordinateQuadMinus
  minusIndexEquiv)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

section Data

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K} {p f₀ : ℕ} {b c : k}

theorem OmegaSetup.b_ne_zero (h : OmegaSetup K k σ p f₀ b c) : b ≠ 0 := by
  intro hb0
  have : CharP K 2 := h.charP
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  have hk2 : ringChar k = 2 := ringChar.eq k 2
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hk2 c
  apply h.irr r
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [hb0, zero_mul, add_zero, hr]
  linear_combination (r * r) * h2

theorem OmegaSetup.bK_ne_zero (h : OmegaSetup K k σ p f₀ b c) : (b : K) ≠ 0 :=
  fun hb => h.b_ne_zero (Subtype.ext hb)

omit [Finite K] in
theorem omega_isExtension :
    IsExtension k (omegaQuad k b c) (omegaQuad K (b : K) (c : K)) :=
  coordinateQuadMinus_isExtension k 4 (by norm_num) b c

theorem omega_reg_K (h : OmegaSetup K k σ p f₀ b c) :
    (polarBilin (omegaQuad K (b : K) (c : K))).Nondegenerate ∧
      ∃ T : Submodule K (Fin (2 * 4) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, omegaQuad K (b : K) (c : K) x = 0 :=
  regular_coordinateQuadMinus 4 K (b : K) (c : K) (le_refl 4) h.irr_K

theorem omega_reg_k (h : OmegaSetup K k σ p f₀ b c) :
    (polarBilin (omegaQuad k b c)).Nondegenerate ∧
      ∃ T : Submodule k (Fin (2 * 4) → k), Module.finrank k T = 3 ∧
        ∀ x ∈ T, omegaQuad k b c x = 0 :=
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  regular_coordinateQuadMinus 4 k b c (le_refl 4) h.irr

theorem omega_orthDerived_K (h : OmegaSetup K k σ p f₀ b c) :
    orthDerived (omegaQuad K (b : K) (c : K)) = elementaryGroup (omegaQuad K (b : K) (c : K)) :=
  (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure (omega_reg_K h).1
    (omega_reg_K h).2).1

theorem omega_orthDerived_k (h : OmegaSetup K k σ p f₀ b c) :
    orthDerived (omegaQuad k b c) = elementaryGroup (omegaQuad k b c) :=
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure (omega_reg_k h).1
    (omega_reg_k h).2).1

@[expose] noncomputable def omegaRat (K : Type) [Field K] (k : Subfield K) (b c : k) :
    Subgroup ((Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) :=
  (elementaryGroup (omegaQuad k b c)).map (liftLin k)

theorem fixed_eq_derivedImage (h : OmegaSetup K k σ p f₀ b c) :
    fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
      (h.quad_invariant (by norm_num) h.order)) =
      subfieldDerivedImage k (omega_isExtension (k := k) (b := b) (c := c)) := by
  have : CharP K 2 := h.charP
  have hodd : Odd p := h.prime.odd_of_ne_two h.ne_two
  have hσp : σ ^ p = 1 := by rw [← h.order]; exact pow_orderOf_eq_one σ
  have hQne : ∃ v, omegaQuad K (b : K) (c : K) v ≠ 0 :=
    exists_ne_zero_of_nondeg (by norm_num) (omega_reg_K h).1
  ext t
  have key := fieldAutT_eq_self_iff k (omegaQuad K (b : K) (c : K)) σ
    (h.quad_invariant (by norm_num) h.order) omega_isExtension h.fixed hodd hσp hQne t
  constructor
  · intro ht
    exact CFSG.RankThree.PartOne.FieldFix.subfieldFixedGroup_le_derivedImage omega_isExtension
      (omega_reg_k h).1 (omega_reg_k h).2 (omega_reg_K h).1 (key.1 ht)
  · intro ht
    exact key.2 (subfieldDerivedImage_le k omega_isExtension ht)

section WithChar

variable [CharP K 2]

theorem map_projLin_derivedImage (h : OmegaSetup K k σ p f₀ b c) :
    (subfieldDerivedImage k (omega_isExtension (k := k) (b := b) (c := c))).map
      (projLin (omega_reg_K h).1) = omegaRat K k b c := by
  have hmd : ∀ a : GL (Fin (2 * 4)) k, a ∈ matrixDerived (omegaQuad k b c) ↔
      matrixLinearIso a ∈ elementaryGroup (omegaQuad k b c) := fun a => by
    rw [← omega_orthDerived_k h, ← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived]
    exact ⟨fun ha => ⟨a, ha, rfl⟩, fun ⟨a', ha', haa'⟩ => (matrixLinearIso.injective haa') ▸ ha'⟩
  ext X
  constructor
  · rintro ⟨t, ⟨z, rfl⟩, rfl⟩
    obtain ⟨y₀, rfl⟩ := matrixProjectiveProjection_surjective (omegaQuad k b c) z
    rw [incl_mk, projLin_mk]
    exact ⟨matrixLinearIso y₀.val, (hmd _).1 y₀.2, liftLin_matrixLinearIso k y₀.val⟩
  · rintro ⟨ω, hω, rfl⟩
    obtain ⟨a, rfl⟩ := matrixLinearIso.surjective ω
    have ha := (hmd a).2 hω
    refine ⟨incl k omega_isExtension
      (matrixProjectiveProjection (omegaQuad k b c) ⟨a, ha⟩), ⟨_, rfl⟩, ?_⟩
    rw [incl_mk, projLin_mk]
    exact (liftLin_matrixLinearIso k a).symm

theorem map_projLin_fixed (h : OmegaSetup K k σ p f₀ b c) :
    (fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
      (h.quad_invariant (by norm_num) h.order))).map (projLin (omega_reg_K h).1) =
      omegaRat K k b c := by
  rw [fixed_eq_derivedImage h, map_projLin_derivedImage h]

theorem omegaFrame_e_eq (h : OmegaSetup K k σ p f₀ b c) (i : Fin 3) :
    (omegaFrame K (b : K) (c : K) h.bK_ne_zero).e i =
      vecIncl k ((omegaFrame k b c h.b_ne_zero).e i) := by
  have e1 : (omegaFrame K (b : K) (c : K) h.bK_ne_zero).e i =
      Pi.single (minusIndexEquiv 4 (by norm_num) (Sum.inl i)) 1 :=
    omegaFrame_vec K (b : K) (c : K) h.bK_ne_zero (Sum.inl i)
  have e2 : (omegaFrame k b c h.b_ne_zero).e i =
      Pi.single (minusIndexEquiv 4 (by norm_num) (Sum.inl i)) 1 :=
    omegaFrame_vec k b c h.b_ne_zero (Sum.inl i)
  rw [e1, e2, vecIncl_single]

theorem ratGroupData (h : OmegaSetup K k σ p f₀ b c) :
    RatGroupData (omegaFrame K (b : K) (c : K) h.bK_ne_zero) k (omegaRat K k b c) := by
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  have hext : IsExtension k (omegaQuad k b c) (omegaQuad K (b : K) (c : K)) := omega_isExtension
  have hQK := (omega_reg_K h).1
  have hQk := (omega_reg_k h).1
  have hrat : ∀ v, (omegaFrame K (b : K) (c : K) h.bK_ne_zero).IsRat k v ↔ ∀ j, v j ∈ k :=
    omegaFrame_isRat_iff (b : K) (c : K) h.bK_ne_zero k
  have hsing : ∀ u₀ : Fin (2 * 4) → k, omegaQuad K (b : K) (c : K) (vecIncl k u₀) = 0 →
      omegaQuad k b c u₀ = 0 := fun u₀ hu => by
    have h1 : ((omegaQuad k b c u₀ : k) : K) = 0 := (hext u₀).symm.trans hu
    exact_mod_cast h1
  have hpol : ∀ u₀ w₀ : Fin (2 * 4) → k,
      polar (omegaQuad K (b : K) (c : K)) (vecIncl k u₀) (vecIncl k w₀) = 0 →
        polar (omegaQuad k b c) u₀ w₀ = 0 := fun u₀ w₀ hu => by
    have h1 : ((polar (omegaQuad k b c) u₀ w₀ : k) : K) = 0 :=
      (polar_vecIncl k hext u₀ w₀).symm.trans hu
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hle : elementaryGroup (omegaQuad k b c) ≤
        (elementaryGroup (omegaQuad K (b : K) (c : K))).comap (liftLin k) :=
      elementaryGroup_le_of_eichler_mem fun u w hu huw => by
        rw [Subgroup.mem_comap, liftLin_eichler k hext hu huw]
        exact eichler_mem_elementaryGroup _ _ _
    exact Subgroup.map_le_iff_le_comap.2 hle
  · intro u w hu hw hQu huw
    obtain ⟨u₀, rfl⟩ := (exists_vecIncl_iff k u).2 ((hrat u).1 hu)
    obtain ⟨w₀, rfl⟩ := (exists_vecIncl_iff k w).2 ((hrat w).1 hw)
    have hu0 := hsing u₀ hQu
    have hw0 := hpol u₀ w₀ huw
    rw [← liftLin_eichler k hext hu0 hw0]
    exact ⟨_, eichler_mem_elementaryGroup _ _ _, rfl⟩
  · intro X hX hX'
    have hXΩ : X ∈ orthDerived (omegaQuad K (b : K) (c : K)) := (omega_orthDerived_K h).symm ▸ hX
    obtain ⟨t, rfl⟩ := (mem_range_projLin hQK).2 hXΩ
    obtain ⟨Y, rfl⟩ := matrixProjectiveProjection_surjective (omegaQuad K (b : K) (c : K)) t
    rw [projLin_mk] at hX' ⊢
    have hent : ∀ i j,
        ((Y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) i j ∈ k := by
      intro i j
      have hs : ∀ l, (Pi.single j (1 : K) : Fin (2 * 4) → K) l ∈ k := fun l => by
        by_cases hl : l = j
        · subst hl
          simp
        · simp [hl]
      have := (hrat _).1 (hX' _ ((hrat _).2 hs)) i
      change (((Y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        Pi.single j 1) i ∈ k at this
      rwa [Matrix.mulVec_single_one] at this
    have hfix : glFieldAut (Fin (2 * 4)) K σ (Y : GL (Fin (2 * 4)) K) = Y :=
      Units.ext (Matrix.ext fun i j => (h.fixed _).mp (hent i j))
    have hmemR : matrixProjectiveProjection (omegaQuad K (b : K) (c : K)) Y ∈
        fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
          (h.quad_invariant (by norm_num) h.order)) := by
      show fieldAutT _ σ _ (matrixProjectiveProjection _ Y) = matrixProjectiveProjection _ Y
      rw [fieldAutT_mk]
      congr 1
      apply Subtype.ext
      rw [matrixDerivedConjugation_fieldPair_val]
      exact hfix
    have hmem : projLin hQK (matrixProjectiveProjection (omegaQuad K (b : K) (c : K)) Y) ∈
        omegaRat K k b c := by
      rw [← map_projLin_fixed h]
      exact ⟨_, hmemR, rfl⟩
    rwa [projLin_mk] at hmem
  · rintro _ ⟨g, hg, rfl⟩
    have h1 := elementaryGroup_le_closure_ts (omegaFrame k b c h.b_ne_zero) hQk hg
    have h2 : liftLin k g ∈ (Subgroup.closure {Y | ∃ u w, omegaQuad k b c u = 0 ∧
        omegaQuad k b c w = 0 ∧ polar (omegaQuad k b c) u w = 0 ∧
        eichler (omegaQuad k b c) u w = Y}).map (liftLin k) := ⟨g, h1, rfl⟩
    rw [MonoidHom.map_closure] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨_, ⟨u, w, hu, hw, huw, rfl⟩, rfl⟩
    have hu' : omegaQuad K (b : K) (c : K) (vecIncl k u) = 0 := by rw [hext u, hu]; rfl
    have hw' : omegaQuad K (b : K) (c : K) (vecIncl k w) = 0 := by rw [hext w, hw]; rfl
    have huw' : polar (omegaQuad K (b : K) (c : K)) (vecIncl k u) (vecIncl k w) = 0 := by
      rw [polar_vecIncl k hext, huw]
      rfl
    exact ⟨vecIncl k u, vecIncl k w, (hrat _).2 fun j => (u j).2, (hrat _).2 fun j => (w j).2,
      hu', hw', huw', (liftLin_eichler k hext hu huw).symm⟩
  · intro x y hx hy hQx hQy hxy hx0 hya
    obtain ⟨x₀, rfl⟩ := (exists_vecIncl_iff k x).2 ((hrat x).1 hx)
    obtain ⟨y₀, rfl⟩ := (exists_vecIncl_iff k y).2 ((hrat y).1 hy)
    have hQx0 := hsing x₀ hQx
    have hQy0 := hsing y₀ hQy
    have hxy0 := hpol x₀ y₀ hxy
    have hx00 : x₀ ≠ 0 := fun h0 => hx0 (by rw [h0]; funext i; rfl)
    have hya0 : ∀ a : k, y₀ ≠ a • x₀ := fun a h0 => hya (a : K) (by rw [h0, vecIncl_smul])
    obtain ⟨g, hg, hgx, a, hga⟩ :=
      (omegaFrame k b c h.b_ne_zero).exists_normal_form hQk hQx0 hQy0 hxy0 hx00 hya0
    refine ⟨liftLin k g, ⟨g, hg, rfl⟩, ?_, (a : K), ?_⟩
    · rw [liftLin_apply_vecIncl, hgx, omegaFrame_e_eq h]
    · rw [liftLin_apply_vecIncl, hga, vecIncl_add, vecIncl_smul, omegaFrame_e_eq h,
        omegaFrame_e_eq h]

end WithChar

end Data

end CFSG.RankThree.PartOne.SEITZ2

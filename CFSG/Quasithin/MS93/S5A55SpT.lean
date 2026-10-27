module

public import CFSG.Quasithin.MS93.S5A55SpG
public import CFSG.Quasithin.MS93.S5A55A

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix MSP

variable {F : Type} [Field F]

@[expose] def Sp4Case55Std (F : Type) [Field F] [Fintype F] [CharP F 2] : Prop :=
  ∀ R A₀ D Z : Subgroup (Sp4 F),
    IsPGroup 2 R → candMax R = {A₀} → R ≤ MSP.stab (ln₀ F) → (∀ r ∈ R, mat r *ᵥ e₁ F = e₁ F) →
    A₀ = Q₁ F ⊓ R → Nat.card F ^ 2 ≤ Nat.card A₀ →
    (∀ p₁ p₂ : Submodule F (V4 F), IsPoint p₁ → IsPoint p₂ → A₀ ≠ xPoint p₁ ⊔ xPoint p₂) →
    (Nat.card F = 2 → ¬ R ≤ commutator (Sp4 F)) →
    D ≤ R → R ≤ Subgroup.normalizer (D : Set (Sp4 F)) → Nat.card A₀ ≤ Nat.card D →
    ¬ IsCandSp R D → ¬ D ≤ Q₁ F → Z ≤ R →
    ((∃ c : Submodule F (V4 F), IsPoint c ∧ Z = xPoint c) ∨
      (Nat.card F ^ 2 ≤ Nat.card Z ∧ commSp Z ≤ fixSp Z ∧ Module.finrank F (fixSp Z) ≤ 2) ∨
      (Nat.card F = 2 ∧ ∃ v₁ v₂ : V4 F, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧ form F v₁ v₂ = 0 ∧
        transv v₁ 1 ∈ R ∧ transv v₂ 1 ∈ R ∧
        (transv v₁ 1 ∈ Z ∨ transv v₂ 1 ∈ Z ∨ transv v₁ 1 * transv v₂ 1 ∈ Z))) →
    ∃ g : Sp4 F, pt₀ F ⊓ (ln₀ F).map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      (commutator (Sp4 F) ≤ D.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z ∨
        (R.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z = ⊤ ∧ Nat.card D = Nat.card A₀ ∧
          Nat.card ↥(D ⊓ A₀) ≤ Nat.card F ^ 2))

theorem isCandSp_map_conj' {R A : Subgroup (Sp4 F)} (hA : IsCandSp R A) (φ : Sp4 F) :
    IsCandSp (R.map (MulAut.conj φ).toMonoidHom) (A.map (MulAut.conj φ).toMonoidHom) := by
  have hcard : Nat.card (fixSp (A.map (MulAut.conj φ).toMonoidHom)) = Nat.card (fixSp A) := by
    rw [fixSp_map_conj]
    exact Nat.card_congr
      (Submodule.equivMapOfInjective _ (mulVec_mat_injective φ) _).toEquiv.symm
  refine ⟨Subgroup.map_mono hA.1, ?_, ?_⟩
  · rw [hcard, MSP.card_map_conj]
    exact hA.2.1
  · rw [hcard]
    exact hA.2.2

theorem map_conj_inv_map_conj (K : Subgroup (Sp4 F)) (φ : Sp4 F) :
    (K.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj φ⁻¹).toMonoidHom = K := by
  rw [map_conj_map_conj', inv_mul_cancel, map_conj_one]

theorem candMax_map_conj {R A₀ : Subgroup (Sp4 F)} (hA : candMax R = {A₀}) (φ : Sp4 F) :
    candMax (R.map (MulAut.conj φ).toMonoidHom) = {A₀.map (MulAut.conj φ).toMonoidHom} := by
  have hA₀ : A₀ ∈ candMax R := hA ▸ Set.mem_singleton A₀
  have hback : ∀ {B : Subgroup (Sp4 F)}, IsCandSp (R.map (MulAut.conj φ).toMonoidHom) B →
      IsCandSp R (B.map (MulAut.conj φ⁻¹).toMonoidHom) := fun {B} hB => by
    have := isCandSp_map_conj' hB φ⁻¹
    rwa [map_conj_inv_map_conj] at this
  ext B
  rw [Set.mem_singleton_iff]
  constructor
  · intro hB
    have hmem : B.map (MulAut.conj φ⁻¹).toMonoidHom ∈ candMax R := by
      refine ⟨hback hB.1, fun C hC => ?_⟩
      rw [MSP.card_map_conj]
      have := hB.2 _ (isCandSp_map_conj' hC φ)
      rwa [MSP.card_map_conj] at this
    rw [hA, Set.mem_singleton_iff] at hmem
    rw [← hmem, map_conj_map_conj', mul_inv_cancel, map_conj_one]
  · rintro rfl
    refine ⟨isCandSp_map_conj' hA₀.1 φ, fun C hC => ?_⟩
    rw [MSP.card_map_conj]
    have := hA₀.2 _ (hback hC)
    rwa [MSP.card_map_conj] at this

theorem map_conj_commutator (φ : Sp4 F) :
    (commutator (Sp4 F)).map (MulAut.conj φ).toMonoidHom = commutator (Sp4 F) := by
  have hN : (commutator (Sp4 F)).Normal := inferInstance
  ext x
  rw [mem_map_conj]
  constructor
  · intro h
    have := hN.conj_mem _ h φ
    convert this using 1
    group
  · intro h
    simpa using hN.conj_mem _ h φ⁻¹

theorem map_conj_map_conj_inv (K : Subgroup (Sp4 F)) (φ : Sp4 F) :
    (K.map (MulAut.conj φ⁻¹).toMonoidHom).map (MulAut.conj φ).toMonoidHom = K := by
  rw [map_conj_map_conj', mul_inv_cancel, map_conj_one]

theorem isPoint_map {p : Submodule F (V4 F)} (hp : IsPoint p) (g : Sp4 F) :
    IsPoint (p.map (mulVecLin (mat g))) := by
  have := (Submodule.equivMapOfInjective (mulVecLin (mat g)) (mulVec_mat_injective g) p).finrank_eq
  exact this.symm.trans hp

variable [Fintype F] [CharP F 2]

theorem sp4Case55Std_of_two_lt (hq2 : 2 < Nat.card F) : Sp4Case55Std F := by
  intro R A₀ D Z hR hA hRl hRe hA₀ hA₀c h51 _ hDR hDn hAD _ hDQ hZR hZ
  have hq := exists_ne_zero_ne_one hq2
  have hpR : pt₀ F ≤ fixSp R := by
    rw [pt₀_eq_span, Submodule.span_singleton_le_iff_mem]
    exact mem_fixSp.2 hRe
  have hZ' : (∃ c : Submodule F (V4 F), IsPoint c ∧ c ≤ ln₀ F ∧ xPoint c ≤ Z) ∨
      (Z ≤ Q₁ F ∧ Nat.card F ^ 2 ≤ Nat.card Z) := by
    rcases hZ with ⟨c, hc, rfl⟩ | ⟨hZc, hZq, hZf⟩ | ⟨hq2', -⟩
    · exact Or.inl ⟨c, hc, le_of_xPoint_le_stab hc isLine_ln₀ (hZR.trans hRl), le_rfl⟩
    · have hZ2 : IsPGroup 2 Z := hR.to_le hZR
      have hf2 : Module.finrank F (fixSp Z) = 2 := le_antisymm hZf (two_le_finrank_fixSp hZq)
      obtain ⟨hm, hZm⟩ := isLine_fixSp_of_finrank_two hZ2 hf2
      have hpm : pt₀ F ≤ fixSp Z := hpR.trans (fixSp_antitone hZR)
      by_cases hml : fixSp Z = ln₀ F
      · refine Or.inr ⟨?_, hZc⟩
        show Z ≤ qLine (ln₀ F)
        rw [← hml]
        exact hZm
      · have hinf : fixSp Z ⊓ ln₀ F = pt₀ F := by
          have h0 : fixSp Z ⊓ ln₀ F ≠ ⊥ := fun h =>
            isPoint_ne_bot isPoint_pt₀ (le_bot_iff.1 (h ▸ le_inf hpm pt₀_le_ln₀))
          have hpt := isPoint_inf hm isLine_ln₀ hml h0
          exact (Submodule.eq_of_le_of_finrank_eq (le_inf hpm pt₀_le_ln₀)
            (by rw [isPoint_pt₀, hpt])).symm
        have hZp : Z ≤ qLine (fixSp Z) ⊓ qPoint (pt₀ F) :=
          le_inf hZm ((le_inf hZm (hZR.trans hRl)).trans
            (qLine_inf_stab_le_qPoint hm isLine_ln₀ isPoint_pt₀ hinf))
        have heq : Z = qLine (fixSp Z) ⊓ qPoint (pt₀ F) := Subgroup.eq_of_le_of_card_ge hZp
          (by rw [card_qLine_inf_qPoint isPoint_pt₀ hm hpm]; exact hZc)
        refine Or.inl ⟨pt₀ F, isPoint_pt₀, pt₀_le_ln₀, ?_⟩
        rw [heq]
        exact le_inf (xPoint_le_qLine hm hpm) (xPoint_le_qPoint isPoint_pt₀)
    · omega
  obtain ⟨g, hg, hc⟩ := sp4Case55_std hq hR hA hRl hRe hA₀ hA₀c h51 hDR hDn hAD hDQ hZ'
  refine ⟨g, hg, hc.imp (fun h => ?_) id⟩
  rw [h]
  exact le_top

theorem sp4Case55_of_std (hstd : Sp4Case55Std F) (R A₀ D Z : Subgroup (Sp4 F))
    (l : Submodule F (V4 F)) (hR : IsPGroup 2 R) (hA : candMax R = {A₀}) (hl : IsLine l)
    (hRl : R ≤ MSP.stab l) (hA₀l : A₀ ≤ qLine l) (hA₀c : Nat.card F ^ 2 ≤ Nat.card A₀)
    (h51 : ∀ p₁ p₂ : Submodule F (V4 F), IsPoint p₁ → IsPoint p₂ → A₀ ≠ xPoint p₁ ⊔ xPoint p₂)
    (hodd : Nat.card F = 2 → ¬ R ≤ commutator (Sp4 F)) (hDR : D ≤ R)
    (hDn : R ≤ Subgroup.normalizer (D : Set (Sp4 F))) (hAD : Nat.card A₀ ≤ Nat.card D)
    (hDnc : ¬ IsCandSp R D) (hZR : Z ≤ R)
    (hZ : (∃ c : Submodule F (V4 F), IsPoint c ∧ Z = xPoint c) ∨
      (Nat.card F ^ 2 ≤ Nat.card Z ∧ commSp Z ≤ fixSp Z ∧ Module.finrank F (fixSp Z) ≤ 2) ∨
      (Nat.card F = 2 ∧ ∃ v₁ v₂ : V4 F, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧ form F v₁ v₂ = 0 ∧
        transv v₁ 1 ∈ R ∧ transv v₂ 1 ∈ R ∧
        (transv v₁ 1 ∈ Z ∨ transv v₂ 1 ∈ Z ∨ transv v₁ 1 * transv v₂ 1 ∈ Z))) :
    ∃ g : Sp4 F,
      fixSp R ⊓ fixSp (A₀.map (MulAut.conj g⁻¹).toMonoidHom) = ⊥ ∧
      (commutator (Sp4 F) ≤ D.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z ∨
        (R.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z = ⊤ ∧ Nat.card D = Nat.card A₀ ∧
          Nat.card ↥(D ⊓ A₀) ≤ Nat.card F ^ 2)) := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hqA : Nat.card F < Nat.card A₀ := by
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq1 (by norm_num)
      _ ≤ Nat.card A₀ := hA₀c
  have hA₀m : A₀ ∈ candMax R := hA ▸ Set.mem_singleton A₀
  have hA₀R : A₀ ≤ R := hA₀m.1.1
  have hfA : fixSp A₀ = l := fixSp_eq_of_le_qLine hl hA₀l hqA
  have hA₀eq : A₀ = qLine l ⊓ R := by
    have hle : A₀ ≤ qLine l ⊓ R := le_inf hA₀l hA₀R
    have hc : IsCandSp R (qLine l ⊓ R) :=
      isCandSp_qLine_inf hl (hA₀c.trans (Subgroup.card_le_of_le hle))
    exact Subgroup.eq_of_le_of_card_ge hle (hA₀m.2 _ hc)
  have hDQ : ¬ D ≤ qLine l := by
    intro hDl
    apply hDnc
    have hc := isCandSp_qLine_inf hl (R := D) (by rw [inf_eq_right.2 hDl]; exact hA₀c.trans hAD)
    rw [inf_eq_right.2 hDl] at hc
    exact ⟨hDR, hc.2.1, hc.2.2⟩
  have hfD := finrank_fixSp_eq_one_of_not_isCandSp hR hDR (hA₀c.trans hAD) hDnc
  have hfR : Module.finrank F (fixSp R) = 1 := by
    have h1 := Submodule.finrank_mono (fixSp_antitone hDR)
    have h0 := finrank_pos_of_ne_bot (fixSp_ne_bot hR)
    omega
  have hp : IsPoint (fixSp R) := hfR
  have hpl : fixSp R ≤ l := hfA ▸ fixSp_antitone hA₀R
  obtain ⟨φ, hφp, hφl⟩ := exists_map_flag hp hl hpl
  have hinj : Function.Injective (MulAut.conj φ⁻¹).toMonoidHom := (MulAut.conj φ⁻¹).injective
  have hl₀ : l.map (mulVecLin (mat φ⁻¹)) = ln₀ F := by rw [← hφl, map_map_mat_inv']
  have hp₀ : (fixSp R).map (mulVecLin (mat φ⁻¹)) = pt₀ F := by rw [← hφp, map_map_mat_inv']
  have hQl : (qLine l).map (MulAut.conj φ⁻¹).toMonoidHom = Q₁ F := by
    rw [fixer_map_conj, hl₀]
  have hmemc : ∀ {K : Subgroup (Sp4 F)} {x : Sp4 F}, x ∈ K →
      φ⁻¹ * x * φ⁻¹⁻¹ ∈ K.map (MulAut.conj φ⁻¹).toMonoidHom := fun {K x} hx => ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hcase⟩ := hstd (R.map (MulAut.conj φ⁻¹).toMonoidHom)
    (A₀.map (MulAut.conj φ⁻¹).toMonoidHom) (D.map (MulAut.conj φ⁻¹).toMonoidHom)
    (Z.map (MulAut.conj φ⁻¹).toMonoidHom) (hR.map _) (candMax_map_conj hA φ⁻¹)
    (by rw [← hl₀, ← MSP.stab_map_conj]; exact Subgroup.map_mono hRl)
    (fun r hr => by
      have : e₁ F ∈ fixSp (R.map (MulAut.conj φ⁻¹).toMonoidHom) := by
        rw [fixSp_map_conj, hp₀, pt₀_eq_span]
        exact Submodule.mem_span_singleton_self _
      exact mem_fixSp.1 this r hr)
    (by rw [hA₀eq, Subgroup.map_inf _ _ _ hinj, hQl])
    (by rw [MSP.card_map_conj]; exact hA₀c)
    (fun p₁ p₂ hp₁ hp₂ h => h51 _ _ (isPoint_map hp₁ φ) (isPoint_map hp₂ φ) (by
      have := congrArg (Subgroup.map (MulAut.conj φ).toMonoidHom) h
      rwa [map_conj_map_conj_inv, Subgroup.map_sup, xPoint_map_conj, xPoint_map_conj] at this))
    (fun hq2 hle => hodd hq2 (by
      have := Subgroup.map_mono (f := (MulAut.conj φ).toMonoidHom) hle
      rwa [map_conj_map_conj_inv, map_conj_commutator] at this))
    (Subgroup.map_mono hDR)
    ((Subgroup.map_mono hDn).trans (Subgroup.le_normalizer_map _))
    (by rw [MSP.card_map_conj, MSP.card_map_conj]; exact hAD)
    (fun h => hDnc (by
      have := isCandSp_map_conj' h φ
      rwa [map_conj_map_conj_inv, map_conj_map_conj_inv] at this))
    (fun h => hDQ (by
      have := Subgroup.map_mono (f := (MulAut.conj φ).toMonoidHom) h
      rwa [map_conj_map_conj_inv, ← hQl, map_conj_map_conj_inv] at this))
    (Subgroup.map_mono hZR)
    (by
      rcases hZ with ⟨c, hc, rfl⟩ | ⟨hZc, hZq, hZf⟩ | ⟨hq2, v₁, v₂, h₁, h₂, h₁₂, hf, hR₁, hR₂, hs⟩
      · exact Or.inl ⟨_, isPoint_map hc φ⁻¹, xPoint_map_conj _ _⟩
      · refine Or.inr (Or.inl ⟨by rw [MSP.card_map_conj]; exact hZc, ?_, ?_⟩)
        · rw [commSp_map_conj, fixSp_map_conj]
          exact Submodule.map_mono hZq
        · rw [fixSp_map_conj, ← (Submodule.equivMapOfInjective _ (mulVec_mat_injective φ⁻¹)
            (fixSp Z)).finrank_eq]
          exact hZf
      · refine Or.inr (Or.inr ⟨hq2, mat φ⁻¹ *ᵥ v₁, mat φ⁻¹ *ᵥ v₂, S59.mulVec_ne_zero _ h₁,
          S59.mulVec_ne_zero _ h₂, fun h => h₁₂ (mulVec_mat_injective _ h),
          by rw [form_mat]; exact hf, ?_, ?_, ?_⟩)
        · rw [← transv_conj]; exact hmemc hR₁
        · rw [← transv_conj]; exact hmemc hR₂
        · rcases hs with h | h | h
          · exact Or.inl (by rw [← transv_conj]; exact hmemc h)
          · exact Or.inr (Or.inl (by rw [← transv_conj]; exact hmemc h))
          · exact Or.inr (Or.inr (by rw [← conj_transv_mul_transv]; exact hmemc h)))
  have hback : ∀ K : Subgroup (Sp4 F),
      ((K.map (MulAut.conj φ⁻¹).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj φ).toMonoidHom = K.map (MulAut.conj (φ * g * φ⁻¹)⁻¹).toMonoidHom := by
    intro K
    rw [map_conj_map_conj', map_conj_map_conj']
    congr 3
    group
  refine ⟨φ * g * φ⁻¹, ?_, ?_⟩
  · rw [fixSp_map_conj, hfA, ← hφp]
    have hl' : l.map (mulVecLin (mat (φ * g * φ⁻¹)⁻¹)) =
        ((ln₀ F).map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat φ)) := by
      rw [show (φ * g * φ⁻¹)⁻¹ = φ * g⁻¹ * φ⁻¹ by group, map_mat_mul, map_mat_mul, hl₀]
    rw [hl', ← map_inf_map, hg, Submodule.map_bot]
  · rcases hcase with hc | ⟨htop, hcD, hcDA⟩
    · left
      have := Subgroup.map_mono (f := (MulAut.conj φ).toMonoidHom) hc
      rwa [map_conj_commutator, Subgroup.map_sup, hback, map_conj_map_conj_inv] at this
    · right
      refine ⟨?_, by rwa [MSP.card_map_conj, MSP.card_map_conj] at hcD, ?_⟩
      · have := congrArg (Subgroup.map (MulAut.conj φ).toMonoidHom) htop
        rwa [Subgroup.map_sup, hback, map_conj_map_conj_inv,
          Subgroup.map_top_of_surjective _ (MulAut.conj φ).surjective] at this
      · rwa [← Subgroup.map_inf _ _ _ hinj, MSP.card_map_conj] at hcDA

end CFSG.Quasithin.MS93.S5

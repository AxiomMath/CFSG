module

public import CFSG.Quasithin.Background.FFC9B
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldUnipotent

public section

namespace CFSG.Quasithin

namespace FFC

namespace SumNat

open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H
open scoped Matrix

variable {F : Type} [Field F]

theorem cAut_one : cAut (1 : GL (Fin 2) F) = 1 := cHom.map_one

theorem modelHom_one_right (s : ↥(StatedSL 3 F)) :
    modelHom (s, (1 : GL (Fin 2) F)) = diagAut (s : GL (Fin 3) F) := by
  rw [modelHom_apply, cAut_one, mul_one]

theorem eq_one_of_mul_self_eq_one [CharP F 2] {x : F} (h : x * x = 1) : x = 1 := by
  have h2 : (x + 1) * (x + 1) = 0 := by
    calc (x + 1) * (x + 1) = x * x + (x + x) + 1 := by ring
      _ = 0 := by rw [h, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h3 : x + 1 = 0 := mul_self_eq_zero.1 h2
  calc x = x + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h3, zero_add]

@[expose] def fixSubmod (E : Subgroup ↥(StatedSL 3 F)) : Submodule F (Fin 3 → F) where
  carrier := {n | ∀ s ∈ E, ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n = n}
  add_mem' {x y} hx hy s hs := by rw [Matrix.mulVec_add, hx s hs, hy s hs]
  zero_mem' s _ := Matrix.mulVec_zero _
  smul_mem' c x hx s hs := by rw [Matrix.mulVec_smul, hx s hs]

theorem card_fixSubmod_le [Finite F] (E : Subgroup ↥(StatedSL 3 F)) :
    Nat.card (fixSubmod E) ≤ Nat.card F ^ 3 := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := fixSubmod E)]
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  have := Submodule.finrank_le (fixSubmod E)
  rwa [Module.finrank_fin_fun] at this

theorem card_fixSubmod_le_of_ne_bot [Finite F] {E : Subgroup ↥(StatedSL 3 F)} (hE : E ≠ ⊥) :
    Nat.card (fixSubmod E) ≤ Nat.card F ^ 2 := by
  obtain ⟨⟨s, hsE⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE
  have hW : fixSubmod E ≠ ⊤ := by
    intro htop
    apply hs1
    have hfix : ∀ n : Fin 3 → F, ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n = n := by
      intro n
      have : n ∈ fixSubmod E := by rw [htop]; trivial
      exact this s hsE
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i l
    have := congrFun (hfix (Pi.single l 1)) i
    simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.one_apply] using this
  have hlt := Submodule.finrank_lt hW
  rw [Module.finrank_fin_fun] at hlt
  rw [Module.natCard_eq_pow_finrank (K := F) (V := fixSubmod E)]
  exact Nat.pow_le_pow_right Nat.card_pos (by omega)

theorem sum_fin_two_of_ne {α : Type*} [AddCommMonoid α] (f : Fin 2 → α) {k l : Fin 2}
    (hkl : k ≠ l) : ∑ j, f j = f k + f l := by
  fin_cases k <;> fin_cases l <;>
    first | exact absurd rfl hkl | simp [Fin.sum_univ_two, add_comm]

theorem fin_two_cases {k l : Fin 2} (hkl : k ≠ l) (j : Fin 2) : j = k ∨ j = l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl | simp
theorem mulVec_inv_mulVec_gl (S : GL (Fin 3) F) (x : Fin 3 → F) :
    ((S⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((S : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem card_fixV_le [Finite F] [CharP F 2]
    (A' : Subgroup (↥(StatedSL 3 F) × GL (Fin 2) F)) {A : Subgroup (MulAut (PM F))}
    (hA : ∀ g ∈ A', modelHom g ∈ A) {s₀ : ↥(StatedSL 3 F)} {c₀ : GL (Fin 2) F}
    (hx₀ : (s₀, c₀) ∈ A') (hc : c₀ ≠ 1) (hsq : c₀ * c₀ = 1) :
    Nat.card (fixV A) ≤
      Nat.card (fixSubmod (A'.comap (MonoidHom.inl ↥(StatedSL 3 F) (GL (Fin 2) F)))) := by
  classical
  set E' := A'.comap (MonoidHom.inl ↥(StatedSL 3 F) (GL (Fin 2) F)) with hE'
  have hoff : ∃ k l : Fin 2, k ≠ l ∧ (c₀ : Matrix (Fin 2) (Fin 2) F) k l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hc
    have hm : (c₀ : Matrix (Fin 2) (Fin 2) F) * (c₀ : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, hsq, Units.val_one]
    have h01 := hcon 0 1 (by decide)
    have h10 := hcon 1 0 (by decide)
    have h00 : (c₀ : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      apply eq_one_of_mul_self_eq_one
      have := congrFun (congrFun hm 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h01, Matrix.one_apply] using this
    have h11 : (c₀ : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      apply eq_one_of_mul_self_eq_one
      have := congrFun (congrFun hm 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h10, Matrix.one_apply] using this
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]
  obtain ⟨k, l, hkl, hckl⟩ := hoff
  have hfixE : ∀ v ∈ fixV A, ∀ j, Multiplicative.toAdd v j ∈ fixSubmod E' := by
    intro v hv j s hs
    have hmem : modelHom (s, (1 : GL (Fin 2) F)) ∈ A := hA _ hs
    have h1 := mem_fixV.1 hv _ hmem
    rw [modelHom_one_right] at h1
    have h2 : adP (diagAut (s : GL (Fin 3) F)) (Multiplicative.toAdd v) j =
        Multiplicative.toAdd v j := congrArg (fun x : PM F => Multiplicative.toAdd x j) h1
    rw [adP_diagAut] at h2
    exact h2
  have hfixeq : ∀ v ∈ fixV A, ∀ i, ((s₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (∑ j, (c₀ : Matrix (Fin 2) (Fin 2) F) i j • Multiplicative.toAdd v j) =
        Multiplicative.toAdd v i := by
    intro v hv i
    have h1 := mem_fixV.1 hv _ (hA _ hx₀)
    rw [modelHom_apply] at h1
    have h2 : adP (diagAut (s₀ : GL (Fin 3) F) * cAut c₀) (Multiplicative.toAdd v) i =
        Multiplicative.toAdd v i := congrArg (fun x : PM F => Multiplicative.toAdd x i) h1
    simpa [adP_mul, adP_diagAut, adP_cAut, cAct] using h2
  have hwl : ∀ v ∈ fixV A, Multiplicative.toAdd v l =
      ((c₀ : Matrix (Fin 2) (Fin 2) F) k l)⁻¹ •
        ((((s₀ : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            Multiplicative.toAdd v k - (c₀ : Matrix (Fin 2) (Fin 2) F) k k • Multiplicative.toAdd v k) := by
    intro v hv
    have h := hfixeq v hv k
    rw [sum_fin_two_of_ne (fun j => (c₀ : Matrix (Fin 2) (Fin 2) F) k j • Multiplicative.toAdd v j)
      hkl] at h
    have h' : (c₀ : Matrix (Fin 2) (Fin 2) F) k k • Multiplicative.toAdd v k +
        (c₀ : Matrix (Fin 2) (Fin 2) F) k l • Multiplicative.toAdd v l =
        ((((s₀ : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Multiplicative.toAdd v k) := by
      have h2 := congrArg (fun x => ((((s₀ : GL (Fin 3) F)⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) h
      simp only [mulVec_inv_mulVec_gl] at h2
      exact h2
    have h'' : (c₀ : Matrix (Fin 2) (Fin 2) F) k l • Multiplicative.toAdd v l =
        ((((s₀ : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            Multiplicative.toAdd v k - (c₀ : Matrix (Fin 2) (Fin 2) F) k k • Multiplicative.toAdd v k) :=
      eq_sub_of_add_eq' h'
    rw [← h'', smul_smul, inv_mul_cancel₀ hckl, one_smul]
  let Θ : ↥(fixV A) → ↥(fixSubmod E') := fun v => ⟨Multiplicative.toAdd v.1 k, hfixE v.1 v.2 k⟩
  have hΘ : Function.Injective Θ := by
    intro v₁ v₂ h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    have hk : Multiplicative.toAdd v₁.1 k = Multiplicative.toAdd v₂.1 k := congrArg Subtype.val h
    funext j
    rcases fin_two_cases hkl j with rfl | rfl
    · exact hk
    · rw [hwl v₁.1 v₁.2, hwl v₂.1 v₂.2, hk]
  exact Nat.card_le_card_of_injective Θ hΘ
omit [Field F] in
theorem card_pm [Finite F] : Nat.card (PM F) = Nat.card F ^ 6 := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_congr (Multiplicative.toAdd : PM F ≃ PV F), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem fixV_bot_eq_top : fixV (⊥ : Subgroup (MulAut (PM F))) = ⊤ := by
  ext v
  simp [mem_fixV]

theorem core [Finite F] [CharP F 2] {m : ℕ} (hm : Odd m) (hF : Nat.card F = 2 ^ m)
    {X : Subgroup (MulAut (PM F))}
    (hXN : X ≤ Subgroup.normalizer (natImage F : Set (MulAut (PM F))))
    {A : Subgroup (MulAut (PM F))} (hA : IsFFStarOffender X A) : A ≤ natImage F := by
  classical
  have hF3 : ∀ μ : F, μ ^ 3 = 1 → μ = 1 := pow_three_eq_one_iff hF hm
  have hι : Function.Injective
      (modelHom : ↥(StatedSL 3 F) × GL (Fin 2) F →* MulAut (PM F)) := modelHom_injective hF3
  obtain ⟨hAX, hA1, hAel, hAoff⟩ := hA
  have hmodel : ∀ a ∈ A, ∃ (s : ↥(StatedSL 3 F)) (c : GL (Fin 2) F),
      a = modelHom (s, c) ∧ s * s = 1 ∧ c * c = 1 := by
    intro a ha
    refine exists_model_of_involution hm hF (hXN (hAX ha)) ?_
    have := hAel.2 a ha
    rwa [pow_two] at this
  intro a₀ ha₀
  by_contra ha₀n
  obtain ⟨s₀, c₀, hac₀, hs₀, hc₀⟩ := hmodel a₀ ha₀
  have hc₀1 : c₀ ≠ 1 := by
    rintro rfl
    apply ha₀n
    rw [hac₀, modelHom_one_right]
    exact ⟨s₀, rfl⟩
  set A' : Subgroup (↥(StatedSL 3 F) × GL (Fin 2) F) := A.comap modelHom with hA'
  have hA'mem : ∀ g, g ∈ A' ↔ modelHom g ∈ A := fun g => Iff.rfl
  have hx₀ : (s₀, c₀) ∈ A' := by
    rw [hA'mem, ← hac₀]
    exact ha₀
  have hA'sq : ∀ g ∈ A', g * g = 1 := by
    intro g hg
    apply hι
    rw [map_mul, map_one]
    have := hAel.2 _ ((hA'mem g).1 hg)
    rwa [pow_two] at this
  have hA'comm : ∀ g ∈ A', ∀ h ∈ A', g * h = h * g := by
    intro g hg h hh
    apply hι
    rw [map_mul, map_mul]
    exact hAel.1 _ ((hA'mem g).1 hg) _ ((hA'mem h).1 hh)
  have hAA' : Nat.card A = Nat.card A' := by
    have h1 : A'.map modelHom = A := by
      rw [hA', Subgroup.map_comap_eq]
      refine inf_eq_right.2 fun a ha => ?_
      obtain ⟨s, c, hac, -, -⟩ := hmodel a ha
      exact ⟨(s, c), hac.symm⟩
    rw [← h1, Subgroup.card_map_of_injective hι]
  set E' := A'.comap (MonoidHom.inl ↥(StatedSL 3 F) (GL (Fin 2) F)) with hE'
  let f : ↥A' →* GL (Fin 2) F := (MonoidHom.snd ↥(StatedSL 3 F) (GL (Fin 2) F)).comp A'.subtype
  have hker : Nat.card f.ker = Nat.card E' := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, ?_⟩
        invFun := fun s => ⟨⟨(s.1, 1), s.2⟩, rfl⟩
        left_inv := fun x => ?_
        right_inv := fun s => rfl }
    · obtain ⟨⟨⟨s, c⟩, hmem⟩, hx⟩ := x
      have hc : c = 1 := hx
      subst hc
      exact hmem
    · obtain ⟨⟨⟨s, c⟩, hmem⟩, hx⟩ := x
      have hc : c = 1 := hx
      subst hc
      rfl
  have hcardA' : Nat.card A' = Nat.card E' * Nat.card f.range := by
    rw [← hker]
    exact (Subgroup.card_ker_mul_card_range f).symm
  have hQsq : ∀ c ∈ f.range, c * c = 1 := by
    rintro _ ⟨x, rfl⟩
    have := hA'sq x.1 x.2
    have h2 := congrArg Prod.snd this
    simpa [f] using h2
  have hQ : Nat.card f.range ≤ Nat.card F := by
    let Q' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      f.range.comap Matrix.SpecialLinearGroup.toGL
    have hdet : ∀ c : ↥f.range, ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
      fun c => det_eq_one_of_mul_self_eq_one (hQsq c c.2)
    have hle : Nat.card f.range ≤ Nat.card Q' := by
      refine Nat.card_le_card_of_injective
        (fun c => (⟨⟨((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), hdet c⟩, ?_⟩ : ↥Q')) ?_
      · show Matrix.SpecialLinearGroup.toGL ⟨((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), hdet c⟩ ∈
          f.range
        have : Matrix.SpecialLinearGroup.toGL
            (⟨((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), hdet c⟩ :
              Matrix.SpecialLinearGroup (Fin 2) F) = (c : GL (Fin 2) F) := Units.ext rfl
        rw [this]
        exact c.2
      · intro c d h
        have h1 := congrArg (fun x : ↥Q' => ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
        exact Subtype.ext (Units.ext h1)
    have hQ'p : IsPGroup 2 Q' := by
      intro g
      refine ⟨1, ?_⟩
      have h1 : Matrix.SpecialLinearGroup.toGL (g : Matrix.SpecialLinearGroup (Fin 2) F) *
          Matrix.SpecialLinearGroup.toGL (g : Matrix.SpecialLinearGroup (Fin 2) F) = 1 :=
        hQsq _ g.2
      apply Subtype.ext
      rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_mul, map_one]
      exact h1
    exact hle.trans (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.pgroup_sl2_card_le Q' hQ'p)
  have hE : Nat.card E' ≤ Nat.card F ^ 2 := by
    let E : Subgroup (GL (Fin 3) F) := E'.map (StatedSL 3 F).subtype
    have hEcard : Nat.card E = Nat.card E' :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [← hEcard]
    refine card_le_of_elemAbelian_GL3 E ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      have h1 := congrArg Prod.fst (hA'sq (s, 1) hs)
      have h2 : s * s = 1 := h1
      have h3 := congrArg (fun x : ↥(StatedSL 3 F) => (x : GL (Fin 3) F)) h2
      simpa using h3
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      have h1 := congrArg Prod.fst (hA'comm (s, 1) hs (t, 1) ht)
      have h2 : s * t = t * s := h1
      have h3 := congrArg (fun x : ↥(StatedSL 3 F) => (x : GL (Fin 3) F)) h2
      simpa using h3
  have hfix : Nat.card (fixV A) ≤ Nat.card (fixSubmod E') :=
    card_fixV_le A' (fun g hg => hg) hx₀ hc₀1 hc₀
  have hoff := hAoff ⊥ bot_le
  rw [Subgroup.card_bot, fixV_bot_eq_top, Subgroup.card_top, card_pm, one_mul, hAA', hcardA'] at hoff
  have hq : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
  have hq5 : Nat.card F ^ 5 < Nat.card F ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)
  have hq4 : Nat.card F ^ 4 < Nat.card F ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)
  by_cases hE1 : E' = ⊥
  · have hE1c : Nat.card E' = 1 := by rw [hE1, Subgroup.card_bot]
    have hM := card_fixSubmod_le E'
    rw [hE1c, one_mul] at hoff
    have h5 : Nat.card f.range * Nat.card (fixV A) ≤ Nat.card F * Nat.card F ^ 3 :=
      Nat.mul_le_mul hQ (hfix.trans hM)
    have : Nat.card F * Nat.card F ^ 3 = Nat.card F ^ 4 := by ring
    omega
  · have hM := card_fixSubmod_le_of_ne_bot hE1
    have h5 : Nat.card E' * Nat.card f.range * Nat.card (fixV A) ≤
        Nat.card F ^ 2 * Nat.card F * Nat.card F ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul hE hQ) (hfix.trans hM)
    have : Nat.card F ^ 2 * Nat.card F * Nat.card F ^ 2 = Nat.card F ^ 5 := by ring
    omega

end SumNat

end FFC

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.SmithD37Row

public section

namespace CFSG.Quasithin.SmithD37

open scoped Matrix

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}

theorem commute_of_fix_inv {I₀ : Subgroup U} {a : MulAut U}
    (haN : ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) (hI : ∀ l ∈ L₁, ∀ u ∈ I₀, l u ∈ I₀)
    (hfa : ∀ u ∈ I₀, a u = u) (hfaith : ∀ l ∈ L₁, (∀ u ∈ I₀, l u = u) → l = 1) :
    ∀ l ∈ L₁, a * l = l * a := by
  intro l hl
  have hc : a * l * a⁻¹ * l⁻¹ ∈ L₁ := L₁.mul_mem (haN l hl) (L₁.inv_mem hl)
  have h1 := hfaith _ hc fun u hu => by
    have hu' : l⁻¹ u ∈ I₀ := hI _ (L₁.inv_mem hl) u hu
    have ha' : a⁻¹ (l⁻¹ u) = l⁻¹ u := by
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
      exact (hfa _ hu').symm
    simp only [MulAut.mul_apply]
    rw [ha', show l (l⁻¹ u) = u by rw [MulAut.inv_apply, MulEquiv.apply_symm_apply], hfa u hu]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem false_of_sup_fixV [IsSimpleGroup ↥L₁] {A : Subgroup (MulAut U)} {I₀ : Subgroup U}
    (hL : ∀ l ∈ L₁, ∀ u ∈ I₀, l u ∈ I₀) (hA : ∀ a ∈ A, ∀ u ∈ I₀, a u ∈ I₀)
    (hAN : ∀ a ∈ A, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) (hsup : I₀ ⊔ fixV A = ⊤)
    (hnt : ∃ l ∈ L₁, ∃ u, l u * u⁻¹ ∉ I₀) (hnc : ∃ a ∈ A, ∃ l ∈ L₁, a * l ≠ l * a) : False := by
  let K : Subgroup (MulAut U) :=
    { carrier := {g | ∀ u, g u * u⁻¹ ∈ I₀}
      one_mem' := fun u => by simp
      mul_mem' := fun {g h} hg hh u => by
        have e : (g * h) u * u⁻¹ = (g (h u) * (h u)⁻¹) * (h u * u⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [e]
        exact I₀.mul_mem (hg _) (hh u)
      inv_mem' := fun {g} hg u => by
        have e : g⁻¹ u * u⁻¹ = (g (g⁻¹ u) * (g⁻¹ u)⁻¹)⁻¹ := by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
          group
        rw [e]
        exact I₀.inv_mem (hg _) }
  have hAK : A ≤ K := by
    intro a ha u
    have hu : u ∈ I₀ ⊔ fixV A := hsup ▸ Subgroup.mem_top u
    obtain ⟨i, hi, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    have e : a (i * c) * (i * c)⁻¹ = a i * i⁻¹ := by
      rw [map_mul, hc a ha]
      group
    rw [e]
    exact I₀.mul_mem (hA a ha i hi) (I₀.inv_mem hi)
  have hconj : ∀ l ∈ L₁, ∀ g ∈ K, l * g * l⁻¹ ∈ K := by
    intro l hl g hg u
    have e : (l * g * l⁻¹) u * u⁻¹ = l (g (l⁻¹ u) * (l⁻¹ u)⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv]
      rw [show l (l⁻¹ u) = u by rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]]
    rw [e]
    exact hL l hl _ (hg _)
  let H : Subgroup ↥L₁ := K.comap L₁.subtype
  have hH : H.Normal := ⟨fun g hg h => hconj h h.2 g hg⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with hb | ht
  · obtain ⟨a, ha, l, hl, hal⟩ := hnc
    apply hal
    have hc : (⟨a * l * a⁻¹ * l⁻¹, L₁.mul_mem (hAN a ha l hl) (L₁.inv_mem hl)⟩ : ↥L₁) ∈ H := by
      show a * l * a⁻¹ * l⁻¹ ∈ K
      rw [mul_assoc a, mul_assoc a]
      exact K.mul_mem (hAK ha)
        (by simpa [mul_assoc] using hconj l hl _ (K.inv_mem (hAK ha)))
    rw [hb, Subgroup.mem_bot] at hc
    have h1 : a * l * a⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hc
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · obtain ⟨l, hl, u, hu⟩ := hnt
    have : (⟨l, hl⟩ : ↥L₁) ∈ H := ht ▸ Subgroup.mem_top _
    exact hu (this u)

section Line

variable {F : Type} [Field F] {d : ℕ}

theorem β_apply_rank1 (Mm : MatModel L₁ L₂ F d) (l : ↥L₁) (x y : Fin d → F) :
    Mm.β ((l : MulAut U) (rank1 Mm x y)) =
      Multiplicative.ofAdd (Matrix.vecMulVec
        (((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ x) y) := by
  rw [Mm.act₁, β_rank1, toAdd_ofAdd, Matrix.mul_vecMulVec]

theorem faithful_line (Mm : MatModel L₁ L₂ F d) {y : Fin d → F} (hy : y ≠ 0) :
    ∀ l ∈ L₁, (∀ u ∈ rowSub Mm (Submodule.span F {y}), l u = u) → l = 1 := by
  intro l hl h
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (funext hc)
  have hR : Mm.R₁ ⟨l, hl⟩ = 1 := by
    ext a b
    have h1 := h _ (rank1_mem_rowSub Mm (Pi.single b 1) (Submodule.mem_span_singleton_self y))
    have h2 := congrArg (fun u => Multiplicative.toAdd (Mm.β u) a j) h1
    simp only [β_apply_rank1 Mm ⟨l, hl⟩, β_rank1, toAdd_ofAdd, Matrix.vecMulVec_apply] at h2
    have h3 := mul_right_cancel₀ hj h2
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h3
    rw [h3, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  have := Mm.inj₁ (hR.trans (map_one Mm.R₁).symm)
  exact congrArg Subtype.val this

theorem exists_not_mem_line (Mm : MatModel L₁ L₂ F d) (hd : 2 ≤ d) {y : Fin d → F}
    (hL : L₁ ≠ ⊥) : ∃ l ∈ L₁, ∃ u, l u * u⁻¹ ∉ rowSub Mm (Submodule.span F {y}) := by
  classical
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL
  obtain ⟨l, hl⟩ := g
  have hl1 : l ≠ 1 := fun h => hg (Subtype.ext h)
  set R := ((Mm.R₁ ⟨l, hl⟩ : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)
  obtain ⟨x, hx⟩ : ∃ x, R *ᵥ x ≠ x := by
    by_contra hc
    push Not at hc
    apply hl1
    have hR : Mm.R₁ ⟨l, hl⟩ = 1 := by
      ext a b
      have h1 := congrFun (hc (Pi.single b 1)) a
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
      rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
      exact h1
    exact congrArg Subtype.val (Mm.inj₁ (hR.trans (map_one Mm.R₁).symm))
  obtain ⟨z, hz⟩ : ∃ z, z ∉ Submodule.span F {y} := by
    by_contra hc
    push Not at hc
    have h1 : Module.finrank F (Fin d → F) ≤ 1 := by
      have := Submodule.finrank_mono (show (⊤ : Submodule F (Fin d → F)) ≤
        Submodule.span F {y} from fun z _ => hc z)
      rw [finrank_top] at this
      refine this.trans ?_
      by_cases hy : y = 0
      · rw [hy, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
        omega
      · rw [finrank_span_singleton hy]
    rw [Module.finrank_fin_fun] at h1
    omega
  obtain ⟨i, hi⟩ : ∃ i, (R *ᵥ x) i - x i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext fun i => sub_eq_zero.mp (hc i))
  refine ⟨l, hl, rank1 Mm x z, fun hmem => hz ?_⟩
  have h1 := hmem i
  rw [map_mul, map_inv, β_apply_rank1 Mm ⟨l, hl⟩, β_rank1, toAdd_mul, toAdd_inv, toAdd_ofAdd,
    toAdd_ofAdd] at h1
  have h2 : (Matrix.vecMulVec (R *ᵥ x) z + -Matrix.vecMulVec x z) i =
      ((R *ᵥ x) i - x i) • z := by
    ext j
    simp [Matrix.vecMulVec_apply, sub_mul]
    ring
  rw [h2] at h1
  have := (Submodule.smul_mem_iff _ hi).mp h1
  exact this

end Line

end CFSG.Quasithin.SmithD37

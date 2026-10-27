module

public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank Matrix

section Lin

variable {K : Type} [Field K]

abbrev spM (γ : ↥(StatedSp 2 K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

@[expose] def fixSp (D : Subgroup ↥(StatedSp 2 K)) : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {v | ∀ δ ∈ D, spM δ *ᵥ v = v}
  add_mem' := fun {a b} ha hb δ hδ => by rw [mulVec_add, ha δ hδ, hb δ hδ]
  zero_mem' := fun δ _ => mulVec_zero _
  smul_mem' := fun c v hv δ hδ => by rw [mulVec_smul, hv δ hδ]

theorem spForm_mulVec (γ : ↥(StatedSp 2 K)) (u v : Fin 2 ⊕ Fin 2 → K) :
    (LieType.BorelTits.spForm 2 K).β (spM γ *ᵥ u) (spM γ *ᵥ v) =
      (LieType.BorelTits.spForm 2 K).β u v := by
  rw [LieType.BorelTits.spForm_β, LieType.BorelTits.spForm_β, mulVec_mulVec, dotProduct_mulVec,
    ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc,
    LieType.BorelTits.transpose_mul_mul_of_mem_statedSp γ.2, ← dotProduct_mulVec]

theorem sub_mem_perp {D : Subgroup ↥(StatedSp 2 K)} {δ : ↥(StatedSp 2 K)} (hδ : δ ∈ D)
    (v : Fin 2 ⊕ Fin 2 → K) :
    spM δ *ᵥ v - v ∈ (LieType.BorelTits.spForm 2 K).perp (fixSp D) := by
  rw [LieType.BorelTits.ReflForm.mem_perp]
  intro h hh
  rw [LieType.BorelTits.ReflForm.β_sub_right]
  calc (LieType.BorelTits.spForm 2 K).β h (spM δ *ᵥ v) - (LieType.BorelTits.spForm 2 K).β h v
      = (LieType.BorelTits.spForm 2 K).β (spM δ *ᵥ h) (spM δ *ᵥ v) -
          (LieType.BorelTits.spForm 2 K).β h v := by rw [hh δ hδ]
    _ = 0 := by rw [spForm_mulVec, sub_self]

theorem eq_of_mulVec_eq {γ γ' : ↥(StatedSp 2 K)}
    (h : ∀ v, spM γ *ᵥ v = spM γ' *ᵥ v) : γ = γ' :=
  Subtype.ext (Units.ext (ext_of_mulVec_single fun _ => h _))

theorem eq_bot_of_fixSp_eq_top {D : Subgroup ↥(StatedSp 2 K)} (h : fixSp D = ⊤) : D = ⊥ := by
  rw [eq_bot_iff]
  intro δ hδ
  rw [Subgroup.mem_bot]
  refine eq_of_mulVec_eq fun v => ?_
  have hv : v ∈ fixSp D := by rw [h]; trivial
  rw [hv δ hδ]
  show v = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v
  rw [one_mulVec]

theorem card_le_of_finrank_fixSp_eq_three [Finite K] {D : Subgroup ↥(StatedSp 2 K)}
    (h3 : Module.finrank K (fixSp D) = 3) : Nat.card D ≤ Nat.card K := by
  classical
  have hfin : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ fixSp D := by
    by_contra hno
    push Not at hno
    have htop : fixSp D = ⊤ := eq_top_iff.2 fun v _ => hno v
    rw [htop, finrank_top, hfin] at h3
    omega
  have hsup : fixSp D ⊔ (K ∙ v₀) = ⊤ := by
    have hlt : fixSp D < fixSp D ⊔ (K ∙ v₀) := by
      refine lt_of_le_of_ne le_sup_left fun heq => hv₀ ?_
      rw [heq]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀)
    have h4 : 3 < Module.finrank K ↥(fixSp D ⊔ (K ∙ v₀)) :=
      h3 ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have h5 : Module.finrank K ↥(fixSp D ⊔ (K ∙ v₀)) ≤ 4 :=
      hfin ▸ Submodule.finrank_le (fixSp D ⊔ (K ∙ v₀))
    apply Submodule.eq_top_of_finrank_eq
    rw [hfin]
    omega
  set P := (LieType.BorelTits.spForm 2 K).perp (fixSp D) with hPdef
  have hP : Module.finrank K P = 1 := by
    have := (LieType.BorelTits.spForm 2 K).finrank_perp (fixSp D)
    rw [← hPdef, h3, hfin] at this
    omega
  have hPcard : Nat.card P = Nat.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K), hP, pow_one]
  rw [← hPcard]
  refine Nat.card_le_card_of_injective
    (fun δ : ↥D => (⟨spM (δ : ↥(StatedSp 2 K)) *ᵥ v₀ - v₀, sub_mem_perp δ.2 v₀⟩ : ↥P)) ?_
  intro δ δ' hδδ'
  have h1 : spM (δ : ↥(StatedSp 2 K)) *ᵥ v₀ = spM (δ' : ↥(StatedSp 2 K)) *ᵥ v₀ :=
    sub_left_injective (congrArg Subtype.val hδδ')
  have h2 : Matrix.mulVecLin (spM (δ : ↥(StatedSp 2 K))) =
      Matrix.mulVecLin (spM (δ' : ↥(StatedSp 2 K))) := by
    refine LinearMap.ext_on (s := (fixSp D : Set (Fin 2 ⊕ Fin 2 → K)) ∪ {v₀}) ?_ ?_
    · rw [Submodule.span_union, Submodule.span_eq, hsup]
    · rintro v (hv | hv)
      · show spM (δ : ↥(StatedSp 2 K)) *ᵥ v = spM (δ' : ↥(StatedSp 2 K)) *ᵥ v
        rw [hv _ δ.2, hv _ δ'.2]
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        exact h1
  exact Subtype.ext (eq_of_mulVec_eq fun v => LinearMap.congr_fun h2 v)

end Lin

end CFSG.Quasithin.B513N

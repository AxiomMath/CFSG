module

public import CFSG.LocalAnalysis.StandardType.ZS.WeylModule
public import CFSG.LocalAnalysis.StandardType.ZS.TypeA
public import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
public import CFSG.LocalAnalysis.StandardType.ZS.OrthClass
import CFSG.LocalAnalysis.StandardType.ZS.OrderBound

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem isRefl_iff_ggLinRefl (t : U ≃ₗ[ZMod p] U) : IsRefl p t ↔ GGLinRefl t :=
  Iff.rfl

theorem reflGen_iff_eq_closure_ggLinRefl (A : Subgroup (U ≃ₗ[ZMod p] U)) :
    ReflGen p A ↔ A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} := by
  unfold ReflGen
  have hset : {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsRefl p t} = {r | r ∈ A ∧ GGLinRefl r} := by
    ext t
    simp only [Set.mem_setOf_eq]
    rw [isRefl_iff_ggLinRefl]
  rw [hset]

theorem ExcRow.deg_le_six (k : ExcRow) : k.deg ≤ 6 := by
  cases k <;> decide

theorem ExcRow.deg_lt_five_of_admissible_three {k : ExcRow} (hk : k.admissible 3) :
    k.deg < 5 := by
  cases k <;> simp_all [ExcRow.admissible, ExcRow.deg]

theorem sl_le_and_pow_le_card_of_slpm [Module.Finite (ZMod p) U] {n : ℕ}
    (hn : Module.finrank (ZMod p) U = n) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) :
    (∀ g : U ≃ₗ[ZMod p] U, LinearEquiv.det g = 1 → g ∈ A) ∧
      p ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A := by
  have hSL : ∀ g : U ≃ₗ[ZMod p] U, LinearEquiv.det g = 1 → g ∈ A :=
    fun g hg => (hA g).2 (Or.inl hg)
  refine ⟨hSL, ?_⟩
  calc p ^ (n * (n - 1) / 2) ≤ Nat.card A := pow_le_card_of_sl_le hn A hSL
    _ = 1 * Nat.card A := (one_mul _).symm
    _ ≤ 8 * Nat.card A := Nat.mul_le_mul_right _ (by norm_num)

theorem ggWeylModel3_of_isCartanModel {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    {K : Matrix (Fin n) (Fin n) ℤ} {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : IsCartanModel 3 K A)
    (hdet : ((K.det : ℤ) : ZMod 3) ≠ 0) : GGWeylModel3 K A := by
  obtain ⟨u, φ, hφ, hK, hspan, _hker, hcl⟩ := hA
  have hmat : (Matrix.of fun i j => φ i (u j)) = K.map (Int.castRingHom (ZMod 3)) := by
    ext i j
    simpa using hK i j
  have hdet' : (Matrix.of fun i j => φ i (u j)).det ≠ 0 := by
    have heq : (Matrix.of fun i j => φ i (u j)).det = ((K.det : ℤ) : ZMod 3) := by
      rw [hmat]
      exact (RingHom.map_det (Int.castRingHom (ZMod 3)) K).symm
    rw [heq]
    exact hdet
  have hset : Set.range (fun i => Module.reflection (hφ i)) =
      {t : V ≃ₗ[ZMod 3] V | ∃ j, ∀ v, t v = v - φ j v • u j} := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, fun v => Module.reflection_apply v (hφ i)⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, LinearEquiv.ext fun v => by rw [hj v, Module.reflection_apply]⟩
  refine ⟨u, φ, linearIndependent_of_det_ne_zero u φ hdet', hspan, hK, ?_⟩
  rw [hcl, ggQ2WeylOf, hset]

theorem omegaLarge_rows_of_linWeyl [Module.Finite (ZMod p) U] (hp : p ≠ 2) {n : ℕ}
    (hn : Module.finrank (ZMod p) U = n) (h9 : 9 ≤ n) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hW : LinWeyl p A) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A ∨
      (¬ p ∣ n + 1 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 1)),
        ∀ r : A, GGLinRefl (r : U ≃ₗ[ZMod p] U) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
      (p ∣ n + 2 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 2)),
        ∀ r : A, GGLinRefl (r : U ≃ₗ[ZMod p] U) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  rcases isCartanModel_cases_of_linWeyl hp h3 hirr hW with
      ⟨ℓ, hA, T, hT⟩ | ⟨ℓ, hℓ, hA⟩ | ⟨ℓ, hℓ, hA⟩ | hA | hA | hA | hA
  · refine Or.inr ?_
    rcases symmetric_row_of_isCartanModel_A hp hn hA T hT with h | h
    · obtain ⟨hnot, e, he⟩ := h
      exact Or.inl ⟨hnot, e,
        fun r hr => he r ((isRefl_iff_ggLinRefl (r : U ≃ₗ[ZMod p] U)).mpr hr)⟩
    · obtain ⟨hdvd, e, he⟩ := h
      exact Or.inr ⟨hdvd, e,
        fun r hr => he r ((isRefl_iff_ggLinRefl (r : U ≃ₗ[ZMod p] U)).mpr hr)⟩
  · exact Or.inl (isImprimitiveOnV_of_isCartanModel_B hp hℓ hA)
  · exact Or.inl (isImprimitiveOnV_of_isCartanModel_D hp hℓ hA)
  · exfalso
    have hle := hA.finrank_le_card_index
    simp only [Fintype.card_fin] at hle
    omega
  · exfalso
    have hle := hA.finrank_le_card_index
    simp only [Fintype.card_fin] at hle
    omega
  · exfalso
    have hle := hA.finrank_le_card_index
    simp only [Fintype.card_fin] at hle
    omega
  · exfalso
    have hle := hA.finrank_le_card_index
    simp only [Fintype.card_fin] at hle
    omega

theorem omegaSmall_rows_of_linWeyl {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] {n : ℕ} (hn : Module.finrank (ZMod 3) V = n) (h5 : 5 ≤ n)
    (h8 : n ≤ 8) {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hirr : ∀ W : Submodule (ZMod 3) V, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hW : LinWeyl 3 A) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A ∨
      (GGOrthType A ∧ 3 ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A) ∨
      (¬ 3 ∣ n + 1 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 1)),
        ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
      (3 ∣ n + 2 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 2)),
        ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
      (n = 7 ∧ GGWeylModel3 (CartanMatrix.E 7) A) ∨
      (n = 8 ∧ GGWeylModel3 (CartanMatrix.E 8) A) := by
  have h3 : 3 ≤ Module.finrank (ZMod 3) V := by omega
  rcases isCartanModel_cases_of_linWeyl (p := 3) (by norm_num) h3 hirr hW with
      ⟨ℓ, hA, T, hT⟩ | ⟨ℓ, hℓ, hA⟩ | ⟨ℓ, hℓ, hA⟩ | hA | hA | hA | hA
  · rcases symmetric_row_of_isCartanModel_A (p := 3) (by norm_num) hn hA T hT with h | h
    · obtain ⟨hnot, e, he⟩ := h
      exact Or.inr (Or.inr (Or.inl
        ⟨hnot, e, fun r hr => he r ((isRefl_iff_ggLinRefl (r : V ≃ₗ[ZMod 3] V)).mpr hr)⟩))
    · obtain ⟨hdvd, e, he⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hdvd, e, fun r hr => he r ((isRefl_iff_ggLinRefl (r : V ≃ₗ[ZMod 3] V)).mpr hr)⟩)))
  · exact Or.inl (isImprimitiveOnV_of_isCartanModel_B (p := 3) (by norm_num) hℓ hA)
  · exact Or.inl (isImprimitiveOnV_of_isCartanModel_D (p := 3) (by norm_num) hℓ hA)
  · obtain ⟨-, horth⟩ := ggOrthType_of_isCartanModel_E6 hA
    exact Or.inr (Or.inl
      ⟨horth, pow_le_card_of_ggOrthType (p := 3) (by norm_num) hn h5 horth⟩)
  · have hdet : (((CartanMatrix.E 7).det : ℤ) : ZMod 3) ≠ 0 := by
      rw [CartanMatrix.E₇_det]
      decide
    have h7 : n = 7 := by
      have hfin := hA.finrank_eq_card_of_det hdet
      simp only [Fintype.card_fin] at hfin
      omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h7, ggWeylModel3_of_isCartanModel hA hdet⟩))))
  · have hdet : (((CartanMatrix.E 8).det : ℤ) : ZMod 3) ≠ 0 := by
      rw [CartanMatrix.E₈_det]
      decide
    have h8' : n = 8 := by
      have hfin := hA.finrank_eq_card_of_det hdet
      simp only [Fintype.card_fin] at hfin
      omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h8', ggWeylModel3_of_isCartanModel hA hdet⟩))))
  · exfalso
    have hle := hA.finrank_le_card_index
    simp only [Fintype.card_fin] at hle
    omega

theorem ggReflClassOmegaLarge_of_useInput (h : UseInput) : GGReflClassOmegaLarge := by
  intro p _ hp V _ _ _ n hn h9 A habs hgen
  have hgen' : ReflGen p A := (reflGen_iff_eq_closure_ggLinRefl A).2 hgen
  have h5 : 5 ≤ n := by omega
  have hfam : Family p A := h p V A hp (by omega) hgen' habs
  cases hfam with
  | weyl hW =>
      rcases omegaLarge_rows_of_linWeyl hp hn h9 habs.1 hW with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
  | slpm hA =>
      exact Or.inr (Or.inl (sl_le_and_pow_le_card_of_slpm hn hA))
  | orth Q hQ hA =>
      refine Or.inr (Or.inr (Or.inl ⟨ggOrthType_of_orth hQ hA, ?_⟩))
      exact pow_le_card_of_ggOrthType hp hn h5 (ggOrthType_of_orth hQ hA)
  | orthClass Q c hQ hc hA =>
      refine Or.inr (Or.inr (Or.inl ⟨ggOrthType_of_orthClass hp (by omega) hQ hc hA, ?_⟩))
      exact pow_le_card_of_ggOrthType hp hn h5 (ggOrthType_of_orthClass hp (by omega) hQ hc hA)
  | gmmn f i₀ i₁ ζ m hi hm hord hA =>
      refine Or.inl ?_
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      rw [hA]
      exact isImprimitiveOnV_gmmn (b := f) (hn := by omega) i₀ i₁ ζ
  | g2mmn f i₀ i₁ ζ m hi hm hord hA =>
      refine Or.inl ?_
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      rw [hA]
      exact isImprimitiveOnV_g2mmn (b := f) (hn := by omega) i₀ i₁ ζ
  | exc k hadm hfin hcard hcen hdmax hone hmodel =>
      exfalso
      have hk6 := k.deg_le_six
      omega
  | h4 _ hfin _ _ _ _ =>
      exfalso
      omega

theorem ggReflClassOmegaSmall_of_useInput (h : UseInput) : GGReflClassOmegaSmall := by
  intro V _ _ _ n hn h5 h8 A habs hgen
  have hgen' : ReflGen 3 A := (reflGen_iff_eq_closure_ggLinRefl A).2 hgen
  have hfam : Family 3 A := h 3 V A (by norm_num) (by omega) hgen' habs
  cases hfam with
  | weyl hW =>
      rcases omegaSmall_rows_of_linWeyl hn h5 h8 habs.1 hW with h1 | h2 | h3 | h4 | h6 | h7
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7)))))
  | slpm hA =>
      exact Or.inr (Or.inl (sl_le_and_pow_le_card_of_slpm hn hA))
  | orth Q hQ hA =>
      refine Or.inr (Or.inr (Or.inl ⟨ggOrthType_of_orth hQ hA, ?_⟩))
      exact pow_le_card_of_ggOrthType (p := 3) (by norm_num) hn h5 (ggOrthType_of_orth hQ hA)
  | orthClass Q c hQ hc hA =>
      refine Or.inr (Or.inr (Or.inl
        ⟨ggOrthType_of_orthClass (p := 3) (by norm_num) (by omega) hQ hc hA, ?_⟩))
      exact pow_le_card_of_ggOrthType (p := 3) (by norm_num) hn h5
        (ggOrthType_of_orthClass (p := 3) (by norm_num) (by omega) hQ hc hA)
  | gmmn f i₀ i₁ ζ m hi hm hord hA =>
      refine Or.inl ?_
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      rw [hA]
      exact isImprimitiveOnV_gmmn (b := f) (hn := by omega) i₀ i₁ ζ
  | g2mmn f i₀ i₁ ζ m hi hm hord hA =>
      refine Or.inl ?_
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      rw [hA]
      exact isImprimitiveOnV_g2mmn (b := f) (hn := by omega) i₀ i₁ ζ
  | exc k hadm hfin hcard hcen hdmax hone hmodel =>
      exfalso
      have hk5 := k.deg_lt_five_of_admissible_three hadm
      omega
  | h4 _ hfin _ _ _ _ =>
      exfalso
      omega

theorem ggReflClassOmegaInput_of_useInput (h : UseInput) : GGReflClassOmegaInput :=
  ⟨ggReflClassOmegaLarge_of_useInput h, ggReflClassOmegaSmall_of_useInput h⟩

end CFSG.StandardType.ZS

end

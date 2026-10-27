module

public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictDefs

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc (omegaZ)

@[expose] noncomputable def burnsideJ4NP_colCount {G : Type*} [Group G] (W : Subgroup G)
    (lab : G → ℕ) (q : G → G → ℕ) (x : G) (a b : ℕ) : ℕ :=
  {w : G | w ∈ W ∧ lab w = a ∧ q x w = b}.ncard

section Colour

variable {G : Type*} [Group G] (W : Subgroup G) (lab : G → ℕ) (q : G → G → ℕ)
  (hlab : ∀ g x : G, lab (g * x * g⁻¹) = lab x)
  (hq : ∀ g x w : G, q (g * x * g⁻¹) (g * w * g⁻¹) = q x w)
include hlab hq

theorem burnsideJ4NP_colCount_conj {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) (x : G)
    (a b : ℕ) :
    burnsideJ4NP_colCount W lab q (g * x * g⁻¹) a b = burnsideJ4NP_colCount W lab q x a b := by
  unfold burnsideJ4NP_colCount
  have himg : {w : G | w ∈ W ∧ lab w = a ∧ q (g * x * g⁻¹) w = b} =
      (fun w => g * w * g⁻¹) '' {w : G | w ∈ W ∧ lab w = a ∧ q x w = b} := by
    ext v
    constructor
    · rintro ⟨hv, hva, hvb⟩
      refine ⟨g⁻¹ * v * g, ⟨?_, ?_, ?_⟩, by group⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
        simpa using this
      · rw [← hva]
        have := hlab g⁻¹ v
        simpa using this
      · rw [← hvb]
        have := hq g (g⁻¹ * (g * x * g⁻¹) * g) (g⁻¹ * v * g)
        have e1 : g * (g⁻¹ * (g * x * g⁻¹) * g) * g⁻¹ = g * x * g⁻¹ := by group
        have e2 : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
        have e3 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [e1, e2, e3] at this
        exact this.symm
    · rintro ⟨w, ⟨hw, hwa, hwb⟩, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg w).mp hw, by rw [hlab]; exact hwa, ?_⟩
      rw [hq]
      exact hwb
  rw [himg]
  exact Set.ncard_image_of_injective _ fun u v huv => by simpa using huv

theorem burnsideJ4NP_fixed_of_colUnique {y : G} (hy : y ∈ W)
    (huniq : ∀ x ∈ W, lab x = lab y →
      (∀ a b, burnsideJ4NP_colCount W lab q x a b = burnsideJ4NP_colCount W lab q y a b) →
        x = y) :
    ∀ g ∈ Subgroup.normalizer (W : Set G), g * y * g⁻¹ = y := by
  intro g hg
  refine huniq _ ((Subgroup.mem_normalizer_iff.mp hg y).mp hy) (hlab g y) fun a b => ?_
  exact burnsideJ4NP_colCount_conj W lab q hlab hq hg y a b

theorem burnsideJ4NP_conj_mem_of_colUnion {O : Set G} (hOW : O ⊆ W)
    (hunion : ∀ x ∈ W, ∀ o ∈ O, lab x = lab o →
      (∀ a b, burnsideJ4NP_colCount W lab q x a b = burnsideJ4NP_colCount W lab q o a b) →
        x ∈ O)
    {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) {o : G} (ho : o ∈ O) :
    g * o * g⁻¹ ∈ O :=
  hunion _ ((Subgroup.mem_normalizer_iff.mp hg o).mp (hOW ho)) o ho (hlab g o)
    fun a b => burnsideJ4NP_colCount_conj W lab q hlab hq hg o a b

end Colour

theorem burnsideJ4NP_colMem_normalizer_closure {G : Type*} [Group G] [Finite G] {O : Set G} {g : G}
    (h : ∀ o ∈ O, g * o * g⁻¹ ∈ Subgroup.closure O) :
    g ∈ Subgroup.normalizer ((Subgroup.closure O : Subgroup G) : Set G) := by
  set Y := Subgroup.closure O
  have hle : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨o, ho, rfl⟩
    exact h o ho
  have heq : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem burnsideJ4NP_normalizer_le_of_colUnion {G : Type*} [Group G] [Finite G] (W : Subgroup G)
    (lab : G → ℕ) (q : G → G → ℕ) (hlab : ∀ g x : G, lab (g * x * g⁻¹) = lab x)
    (hq : ∀ g x w : G, q (g * x * g⁻¹) (g * w * g⁻¹) = q x w) {O : Set G} (hOW : O ⊆ W)
    (hunion : ∀ x ∈ W, ∀ o ∈ O, lab x = lab o →
      (∀ a b, burnsideJ4NP_colCount W lab q x a b = burnsideJ4NP_colCount W lab q o a b) →
        x ∈ O) :
    Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure O : Subgroup G) : Set G) := fun g hg =>
  burnsideJ4NP_colMem_normalizer_closure fun o ho => Subgroup.subset_closure
    (burnsideJ4NP_conj_mem_of_colUnion W lab q hlab hq hOW hunion hg ho)

section Verdicts


theorem burnsideJ4NP_col_normalizer_eq_of_node {A₀ R : Subgroup J} (hR : burnsideJ4NP_Hyp R) {c : J}
    (hAZ : A₀.map (MulAut.conj c).toMonoidHom ≤ omegaZ R)
    (hWA : burnsideJ4NP_W R ≤ A₀.map (MulAut.conj c).toMonoidHom) :
    Subgroup.normalizer (R : Set J) =
      (Subgroup.normalizer ((Subgroup.closure {x | x ∈ A₀ ∧ burnsideJ4NP_Is2A x} : Subgroup J) :
        Set J)).map (MulAut.conj c).toMonoidHom := by
  rw [← burnsideJ4NP_normalizer_W hR, burnsideJ4NP_W_eq_closure hAZ hWA,
    burnsideJ4NP_closure2A_map_conj, burnsideJ4NP_normalizer_map_conj]

theorem burnsideJ4NP_verdictW_fixed {W₀ : Subgroup J} {y : J} (hy2A : burnsideJ4NP_Is2A y)
    (hfix : ∀ g ∈ Subgroup.normalizer (W₀ : Set J), g * y * g⁻¹ = y) :
    burnsideJ4NP_VerdictW W₀ := by
  refine burnsideJ4NP_verdictW_of_false fun A₀ hA R hR h hAZ hWA => ?_
  obtain ⟨c, rfl⟩ := hy2A
  apply burnsideJ4NP_not_le_Cz0_conj hR (h * c)
  intro n hn
  rw [burnsideJ4NP_col_normalizer_eq_of_node hR hAZ hWA, hA, burnsideJ4NP_mem_map_conj] at hn
  have hm := hfix _ hn
  rw [burnsideJ4NP_mem_map_conj, Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have hk : ((h * c)⁻¹ * n * (h * c)) * CFSG.Quasithin.J4Loc.z0 *
      ((h * c)⁻¹ * n * (h * c))⁻¹ = CFSG.Quasithin.J4Loc.z0 := by
    calc ((h * c)⁻¹ * n * (h * c)) * CFSG.Quasithin.J4Loc.z0 * ((h * c)⁻¹ * n * (h * c))⁻¹
        = c⁻¹ * ((h⁻¹ * n * h) * (c * CFSG.Quasithin.J4Loc.z0 * c⁻¹) * (h⁻¹ * n * h)⁻¹) * c := by
          group
      _ = c⁻¹ * (c * CFSG.Quasithin.J4Loc.z0 * c⁻¹) * c := by rw [hm]
      _ = CFSG.Quasithin.J4Loc.z0 := by group
  calc CFSG.Quasithin.J4Loc.z0 * ((h * c)⁻¹ * n * (h * c))
      = (((h * c)⁻¹ * n * (h * c)) * CFSG.Quasithin.J4Loc.z0 * ((h * c)⁻¹ * n * (h * c))⁻¹) *
          ((h * c)⁻¹ * n * (h * c)) := by rw [hk]
    _ = (h * c)⁻¹ * n * (h * c) * CFSG.Quasithin.J4Loc.z0 := by group

theorem burnsideJ4NP_verdictW_subnp {W₀ Y : Subgroup J} (hY2 : IsPGroup 2 ↥Y) (hY1 : Y ≠ ⊥)
    (hNY : Subgroup.normalizer (W₀ : Set J) ≤ Subgroup.normalizer (Y : Set J)) {g : J}
    (hg : P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Y : Set J)) :
    burnsideJ4NP_VerdictW W₀ := by
  refine burnsideJ4NP_verdictW_of_false fun A₀ hA R hR c hAZ hWA => ?_
  have hN := burnsideJ4NP_col_normalizer_eq_of_node hR hAZ hWA
  rw [hA] at hN
  have hle : Subgroup.normalizer (R : Set J) ≤
      Subgroup.normalizer ((Y.map (MulAut.conj c).toMonoidHom : Subgroup J) : Set J) := by
    rw [hN, burnsideJ4NP_normalizer_map_conj]
    exact Subgroup.map_mono hNY
  have heq := hR.max _ (hY2.map _) (burnsideJ4KW_map_conj_ne_bot hY1 c) hle
  apply hR.np (c * g)
  rw [← heq, burnsideJ4NP_normalizer_map_conj, ← burnsideJ4KW_map_conj_map_conj]
  exact Subgroup.map_mono hg

end Verdicts

end CFSG.ASVolI

module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightMod
public import CFSG.LocalAnalysis.WeakClosure81.W19EightBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem odd_card_X (c : MinCex193 D V₀ V p X) : Odd (Nat.card X) := by
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 c.hyp.isPGroup
  rw [ha]
  exact Odd.pow (c.hyp.prime.odd_of_ne_two c.hyp.odd)

end MinCex193

namespace Hyp197

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X E F : Subgroup G} {g : G}

theorem not_comm_le_centralizerQuot (c : MinCex193 D V₀ V p X) (h : Hyp197 D V X E F g) :
    ¬ ⁅X, conjSubgroup V g⁆ ≤ centralizerQuot (X ⊔ D.T) E F := by
  intro hXA
  apply h.comm_ne
  have hXn : X ≤ normalizer (pCoreOf 2 (X ⊔ D.T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hAn : conjSubgroup V g ≤ normalizer (pCoreOf 2 (X ⊔ D.T) : Set G) :=
    h.A_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  calc ⁅twoResidual (X ⊔ D.T), conjSubgroup V g⁆
      ≤ ⁅X ⊔ pCoreOf 2 (X ⊔ D.T), conjSubgroup V g⁆ :=
        Subgroup.commutator_mono c.twoResidual_le_sup_pCoreOf le_rfl
    _ = ⁅conjSubgroup V g, X ⊔ pCoreOf 2 (X ⊔ D.T)⁆ := Subgroup.commutator_comm _ _
    _ ≤ ⁅conjSubgroup V g, X⁆ ⊔ pCoreOf 2 (X ⊔ D.T) := E1.commutator_sup_le hAn hXn
    _ ≤ centralizerQuot (X ⊔ D.T) E F :=
        sup_le (by rw [Subgroup.commutator_comm]; exact hXA) (h.pCoreOf_le_centralizerQuot c)

theorem mul_comm_of_comm_mem (c : MinCex193 D V₀ V p X) (h : Hyp197 D V X E F g) {x e : G}
    (hxX : x ∈ X) (he : e ∈ E) (hxe : ⁅x, e⁆ ∈ F) : x * e = e * x := by
  set f : G := ⁅x, e⁆ with hf
  have hfF : f ∈ F := hxe
  have hxF : x * f = f * x := by
    have h1 : ⁅f, x⁆ ∈ ⁅F, twoResidual (X ⊔ D.T)⁆ :=
      Subgroup.commutator_mem_commutator hfF (c.X_le_twoResidual hxX)
    rw [h.comm_F, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hpow : ∀ k : ℕ, x ^ k * e * (x ^ k)⁻¹ = f ^ k * e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : x ^ (k + 1) * e * (x ^ (k + 1))⁻¹ = x * (x ^ k * e * (x ^ k)⁻¹) * x⁻¹ := by
        group
      have hk : x * f ^ k = f ^ k * x := (Commute.pow_right (show Commute x f from hxF) k).eq
      have h3 : x * e * x⁻¹ = f * e := by rw [hf, commutatorElement_def]; group
      rw [h1, ih]
      calc x * (f ^ k * e) * x⁻¹ = (x * f ^ k) * e * x⁻¹ := by group
        _ = (f ^ k * x) * e * x⁻¹ := by rw [hk]
        _ = f ^ k * (x * e * x⁻¹) := by group
        _ = f ^ (k + 1) * e := by rw [h3, pow_succ]; group
  have hfp : f ^ p = 1 := by
    have h1 := hpow p
    rw [c.hyp.exponent x hxX, one_mul, inv_one, mul_one] at h1
    exact (mul_eq_right.1 h1.symm)
  have hf2 : f ^ 2 = 1 := h.isElemAbelian.2 f (h.F_le hfF)
  have hf1 : f ∈ (⊥ : Subgroup G) :=
    E1.mem_of_pow_mem_two_p c.hyp.prime c.hyp.odd (k := 1) (j := 1)
      (by rw [pow_one, hfp]; exact Subgroup.one_mem _)
      (by rw [pow_one, hf2]; exact Subgroup.one_mem _)
  rw [Subgroup.mem_bot, hf, commutatorElement_eq_one_iff_mul_comm] at hf1
  exact hf1

end Hyp197

namespace ModData

variable {H E F : Subgroup G} (M : ModData H E F)

theorem quadratic_module {A : Subgroup G} (hEn : H ≤ normalizer (E : Set G))
    (hq : ⁅⁅E, A⁆, A⁆ = ⊥) :
    ∀ a b : ↥H, (a : G) ∈ A → (b : G) ∈ A → ∀ w : M.W,
      M.ρ a (M.ρ b w - w) = M.ρ b w - w := by
  intro a b ha hb w
  obtain ⟨e, he, rfl⟩ := M.ι_surj w
  rw [M.ρ_sub_ι hEn b he]
  have hcE : ⁅(b : G), e⁆ ∈ E := commutator_mem_of_le_normalizer hEn b.2 he
  have hcEA : ⁅(b : G), e⁆ ∈ ⁅E, A⁆ := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator he hb)
  have h1 : ⁅⁅(b : G), e⁆, (a : G)⁆ ∈ ⁅⁅E, A⁆, A⁆ :=
    Subgroup.commutator_mem_commutator hcEA ha
  rw [hq, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  rw [M.ρ_ι a _ hcE]
  congr 1
  exact mul_inv_eq_iff_eq_mul.2 h1.symm

end ModData

end CFSG.LocalAnalysis.WeakClosure81

end

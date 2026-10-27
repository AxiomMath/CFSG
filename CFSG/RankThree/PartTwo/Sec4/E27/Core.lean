module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Hyper
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LieType.SeitzGeneration.HyperLeaf
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27

@[expose] def Seitz27 (K : Type) [Group K] : Prop :=
  ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → Nat.card E = 27 → seitzHyperGamma 3 E = ⊤

theorem conj_injective_of_center_bot {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun φ : MulAut X => φ z) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * g = g * z * g⁻¹ * g := by rw [this]
      _ = g * z := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem seitzHyperGamma_eq_top_of_hyperGen {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    {p : ℕ} (E : Subgroup (MulAut X))
    (h : HyperGen p ((MulAut.conj : X →* MulAut X).range) E) : seitzHyperGamma p E = ⊤ := by
  have hinj := conj_injective_of_center_bot hZ
  set H := seitzHyperGamma p E with hH
  rw [eq_top_iff]
  intro x _
  have hx : (MulAut.conj x : MulAut X) ∈ (MulAut.conj : X →* MulAut X).range := ⟨x, rfl⟩
  have h1 := h hx
  have hS : Subgroup.closure {k : MulAut X | k ∈ (MulAut.conj : X →* MulAut X).range ∧
      ∃ F : Subgroup (MulAut X), F ≤ E ∧ F.relIndex E = p ∧ ∀ f ∈ F, f * k = k * f} ≤
      H.map (MulAut.conj : X →* MulAut X) := by
    rw [Subgroup.closure_le]
    rintro k ⟨⟨x₀, rfl⟩, F, hFE, hrel, hcomm⟩
    refine ⟨x₀, ?_, rfl⟩
    have hfix : x₀ ∈ fixedPoints F := by
      intro f hf
      have h2 := hcomm f hf
      have h3 : (f * MulAut.conj x₀ * f⁻¹) = MulAut.conj (f x₀) := by
        ext y
        simp [MulAut.mul_apply, MulAut.conj_apply]
      have h4 : MulAut.conj (f x₀) = MulAut.conj x₀ := by
        rw [← h3, h2]
        group
      exact hinj h4
    exact (le_iSup₂_of_le F ⟨hFE, hrel⟩ le_rfl : fixedPoints F ≤ H) hfix
  obtain ⟨y, hy, hyx⟩ := hS h1
  rwa [hinj hyx] at hy

theorem seitz27_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : Seitz27 Y) :
    Seitz27 X := by
  intro E hE hEc
  refine CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map e
    (MulAut.congr e).toMonoidHom (fun a x => by simp [MulAut.congr_apply])
    (MulAut.congr e).injective (h _ (CFSG.Open.IsElemAbelian.map hE _) ?_)
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hEc]

end CFSG.RankThree.PartTwo.Sec4.E27

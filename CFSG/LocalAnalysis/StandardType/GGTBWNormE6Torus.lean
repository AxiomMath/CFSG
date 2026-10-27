module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormCenterless
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylAutInner
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize
public import CFSG.LocalAnalysis.StandardType.GGPZWeylExc
public import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv

public noncomputable section

namespace CFSG.StandardType.E6WNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover

variable {p : ℕ} [Fact p.Prime] [NeZero p]
theorem center_weyl_range_eq_bot
    (hp2 : p ≠ 2) :
    Subgroup.center ↥(ExcWeylOuter.torusMulAut Tag.E6 p).range = ⊥ := by
  have e := (MonoidHom.ofInjective (ExcWeylOuter.torusMulAut_injective (τ := Tag.E6) hp2)).symm
  have ew := ggE6Row_coxeterGroupEquiv
  have hc : Nat.card (Subgroup.center ↥(ExcWeylOuter.torusMulAut Tag.E6 p).range) = 1 := by
    rw [Nat.card_congr (Subgroup.centerCongr (e.trans ew.symm)).toEquiv]
    exact ggCoxeterE6_center
  exact Subgroup.eq_bot_of_card_le (H := Subgroup.center ↥(ExcWeylOuter.torusMulAut Tag.E6 p).range)
    (by rw [hc])


theorem commutant_scalar (hp5 : 5 ≤ p)
    (f : MulAut (Multiplicative (Fin Tag.E6.rank → ZMod p)))
    (hc : ∀ w ∈ (ExcWeylOuter.torusMulAut Tag.E6 p).range, f * w = w * f) :
    ∃ c : ZMod p, ∀ v : Fin Tag.E6.rank → ZMod p,
      Multiplicative.toAdd (f (Multiplicative.ofAdd v)) = c • v := by
  let F : (Fin Tag.E6.rank → ZMod p) → (Fin Tag.E6.rank → ZMod p) :=
    fun v => Multiplicative.toAdd (f (Multiplicative.ofAdd v))
  have hAdd : ∀ v w, F (v + w) = F v + F w := by
    intro v w
    change Multiplicative.toAdd (f (Multiplicative.ofAdd (v + w))) =
      Multiplicative.toAdd (f (Multiplicative.ofAdd v)) + Multiplicative.toAdd (f (Multiplicative.ofAdd w))
    exact f.toAdditive.map_add v w
  have hComm : ∀ (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ZMod p),
      F (TwE6TB.reflE6 p i v) = TwE6TB.reflE6 p i (F v) := by
    intro i v
    have he := congrArg (fun a : MulAut (Multiplicative (Fin Tag.E6.rank → ZMod p)) =>
      Multiplicative.toAdd (a (Multiplicative.ofAdd v)))
        (hc (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i)) ⟨_, rfl⟩)
    simp only [MulAut.mul_apply] at he
    have hi : ∀ a : Fin Tag.E6.rank → ZMod p,
        ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) (Multiplicative.ofAdd a) =
          Multiplicative.ofAdd (TwE6TB.reflE6 p i a) := by
      intro a
      exact (ExcWeylOuter.torusMulAut_apply (simple Tag.E6 i) a).trans
        (congrArg Multiplicative.ofAdd (ExcFrames.torusAct_simple_E6 i a))
    have hf : f (Multiplicative.ofAdd v) = Multiplicative.ofAdd (F v) := rfl
    rw [hi v, hf, hi (F v)] at he
    exact he
  exact TwE6TB.exists_smul_of_commute_reflE6 hp5 F hAdd hComm

theorem commutant_scalar_of_coordinates {Y : Type} [Group Y] [Finite Y]
    {A : Subgroup Y} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (hp5 : 5 ≤ p) (ι : Additive ↥A ≃+ V)
    (κ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* ↥A)
    (W : Subgroup (MulAut ↥A))
    (hW : (ExcWeylOuter.torusMulAut Tag.E6 p).range.map (MulAut.congr κ).toMonoidHom = W)
    (f : MulAut ↥A) (hf : ∀ w ∈ W, f * w = w * f) :
    ∃ c : ZMod p, ∀ v, ggLin (p := p) ι f v = c • v := by
  let g := (MulAut.congr κ).symm f
  have hgf : MulAut.congr κ g = f := (MulAut.congr κ).apply_symm_apply f
  have hg : ∀ w ∈ (ExcWeylOuter.torusMulAut Tag.E6 p).range, g * w = w * g := by
    intro w hw
    apply (MulAut.congr κ).injective
    rw [map_mul, map_mul, hgf]
    exact hf _ (hW ▸ Subgroup.mem_map_of_mem _ hw)
  obtain ⟨c, hc⟩ := commutant_scalar hp5 g hg
  refine ⟨c, ?_⟩
  intro v
  let a : A := Additive.toMul (ι.symm v)
  obtain ⟨u, hu⟩ := κ.surjective a
  have he : ggLin (p := p) ι f v =
      ι (Additive.ofMul (κ (g u))) := by
    rw [ggLin_apply]
    change ι (Additive.ofMul (f a)) = _
    rw [← hu]
    have hgval : κ (g u) = f (κ u) := by
      have he := congrArg (fun a : MulAut ↥A => a (κ u)) hgf
      change κ (g (κ.symm (κ u))) = f (κ u) at he
      rwa [κ.symm_apply_apply] at he
    rw [hgval]
  have hcu := hc (Multiplicative.toAdd u)
  change Multiplicative.toAdd (g u) = c • Multiplicative.toAdd u at hcu
  let j : (Fin Tag.E6.rank → ZMod p) ≃+ V := κ.toAdditive.trans ι
  have hj : ∀ u : Multiplicative (Fin Tag.E6.rank → ZMod p),
      j (Multiplicative.toAdd u) = ι (Additive.ofMul (κ u)) := fun _ => rfl
  rw [he, ← hj, hcu, ZMod.map_smul, hj, hu]
  exact congrArg (fun x : V => c • x) (ι.apply_symm_apply v)

end CFSG.StandardType.E6WNorm

module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNormDefs

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y]
  {A : Subgroup Y} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {Λ : Type} (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A)
  (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)

theorem ggLin_mem_ggHL_of_closure {W : Subgroup (MulAut ↥A)}
    (hW : W = Subgroup.closure (Set.range φ)) {w : MulAut ↥A} (hw : w ∈ W) :
    ggLin (p := p) ι w ∈ ggHL ι φ h α := by
  rw [hW] at hw
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨i, rfl⟩ := hs
    exact Subgroup.subset_closure (Or.inl (Or.inl (Set.mem_range_self i)))
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem ggWNormConcl_of_centerless [Nontrivial V] {W : Subgroup (MulAut ↥A)}
    (hW : W = Subgroup.closure (Set.range φ))
    (hZ : Subgroup.center ↥W = ⊥) (hNI : NormInducesInner W)
    (hC : ∀ f : MulAut ↥A, (∀ w ∈ W, f * w = w * f) →
      ∃ c : ZMod p, ∀ v, ggLin (p := p) ι f v = c • v)
    {s : MulAut ↥A} (hs : s ∈ Subgroup.normalizer (W : Set (MulAut ↥A))) :
    GGWNormConcl ι φ h α s := by
  obtain ⟨w, hw, hconj⟩ := hNI s hs
  let f : MulAut ↥A := w⁻¹ * s
  have hfc : ∀ u ∈ W, f * u = u * f := by
    intro u hu
    change (w⁻¹ * s) * u = u * (w⁻¹ * s)
    calc _ = w⁻¹ * (s * u * s⁻¹) * s := by group
      _ = u * (w⁻¹ * s) := by rw [hconj u hu]; group
  obtain ⟨c, hc⟩ := hC f hfc
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hc0 : c ≠ 0 := by
    intro hz
    have he : ggLin (p := p) ι f v₀ = ggLin (p := p) ι f 0 := by
      rw [hc, hz, zero_smul, map_zero]
    exact hv₀ ((ggLin (p := p) ι f).injective he)
  have hsf : s = w * f := by dsimp [f]; group
  have hsact : ∀ v, ggLin (p := p) ι s v = c • ggLin (p := p) ι w v := by
    intro v
    rw [hsf, map_mul, LinearEquiv.mul_apply, hc, map_smul]
  have hwm : ggLin (p := p) ι w ∈ ggHL ι φ h α :=
    ggLin_mem_ggHL_of_closure ι φ h α hW hw
  refine ⟨⟨Units.mk0 c hc0, ggLin (p := p) ι w, hwm, hsact⟩, ?_⟩
  intro hsr
  have hw2 : w ^ 2 = 1 := by
    have hz : (⟨w, hw⟩ : W) ^ 2 ∈ Subgroup.center ↥W := by
      rw [Subgroup.mem_center_iff]
      intro u
      apply Subtype.ext
      change (u : MulAut ↥A) * w ^ 2 = w ^ 2 * u
      have hu : s * (u : MulAut ↥A) * s⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp hs u).mp u.2
      have he : s * (s * (u : MulAut ↥A) * s⁻¹) * s⁻¹ = u := by
        calc _ = s ^ 2 * (u : MulAut ↥A) * (s ^ 2)⁻¹ := by simp only [pow_two]; group
          _ = u := by rw [hsr.1]; simp
      rw [hconj _ hu, hconj _ u.2] at he
      have he' : w ^ 2 * (u : MulAut ↥A) * (w ^ 2)⁻¹ = u := by
        calc _ = w * (w * (u : MulAut ↥A) * w⁻¹) * w⁻¹ := by simp only [pow_two]; group
          _ = u := he
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    rw [hZ] at hz
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hz)
  have hfw : Commute w f := (hfc w hw).symm
  have hf2 : f ^ 2 = 1 := by
    have he : w ^ 2 * f ^ 2 = 1 := by
      rw [← hfw.mul_pow, ← hsf, hsr.1]
    simpa only [hw2, one_mul] using he
  have he := congrArg (fun g : MulAut ↥A => ggLin (p := p) ι g v₀) hf2
  simp only [pow_two, map_mul, LinearEquiv.mul_apply, map_one] at he
  change ggLin (p := p) ι f (ggLin (p := p) ι f v₀) = v₀ at he
  rw [hc, hc, smul_smul] at he
  have hzero : (c * c - 1) • v₀ = 0 := by rw [sub_smul, one_smul, he, sub_self]
  have hsq : c * c - 1 = 0 := (smul_eq_zero.mp hzero).resolve_right hv₀
  have hfact : (c - 1) * (c + 1) = 0 := by
    calc _ = c * c - 1 := by ring
      _ = 0 := hsq
  rcases mul_eq_zero.mp hfact with hc1 | hcm
  · have hc1' : c = 1 := sub_eq_zero.mp hc1
    have heq : ggLin (p := p) ι s = ggLin (p := p) ι w := by
      apply LinearEquiv.ext
      intro v
      rw [hsact, hc1', one_smul]
    rw [heq]
    exact hwm
  · have hcm' : c = -1 := eq_neg_of_add_eq_zero_left hcm
    have heq : ggLin (p := p) ι s = LinearEquiv.neg (ZMod p) * ggLin (p := p) ι w := by
      apply LinearEquiv.ext
      intro v
      rw [hsact, hcm', LinearEquiv.mul_apply]
      change (- (1 : ZMod p)) • ggLin (p := p) ι w v = -ggLin (p := p) ι w v
      exact _root_.neg_one_smul (R := ZMod p) (ggLin (p := p) ι w v)
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))) hwm

end CFSG.StandardType

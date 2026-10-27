module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCMono

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_bigC_irr (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {ℓ : ℕ} (hℓ : 9 ≤ ℓ) (h3 : 3 ∣ ℓ + 1)
    (hdim : Module.finrank (ZMod 3) V = ℓ + 1)
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (hirr : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hsmall : 8 * Nat.card R < 3 ^ ((ℓ + 1) * ℓ / 2)) (hWR : W ≤ R)
    (s : Fin ℓ → (V ≃ₗ[ZMod 3] V))
    (hsR : ∀ i, s i ∈ R) (hsrefl : ∀ i, GGLinRefl (s i))
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ (CoxeterMatrix.A ℓ) i j = 1)
    (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hncomm : ∀ i j, i ≠ j → (CoxeterMatrix.A ℓ) i j ≠ 2 → s i * s j ≠ s j * s i)
    (hWs : W = Subgroup.closure (Set.range s)) (e : ↥W ≃* Equiv.Perm (Fin (ℓ + 1)))
    (xv : V) (hx : xv ≠ 0)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (f : V →ₗ[ZMod 3] ZMod 3) (hf : f xv ≠ 0) (hWf : ∀ w ∈ W, ∀ v, f (w v) = f v)
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hr : GGLinRefl r)
    (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv) :
    GGQ2S08M0 R W r xv = R := by
  have hfixx : ∀ w ∈ W, w xv = xv := (hWfix xv).2 (Submodule.mem_span_singleton_self xv)
  have hrW : r ∉ W := fun hrW => hrx ⟨1, by rw [hfixx r hrW, one_smul]⟩
  have hM0le : GGQ2S08M0 R W r xv ≤ R := by
    refine (Subgroup.closure_le _).2 ?_
    rintro a ((ha | ha) | ha)
    · exact hWR ha
    · rw [Set.mem_singleton_iff.mp ha]; exact hrR
    · exact ha.1
  have hclos : Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r}) ≤ GGQ2S08M0 R W r xv :=
    Subgroup.closure_mono (fun a ha => Or.inl ha)
  rcases ggRC_classify_frame3 hKG hdim (by omega) R hirr hgen hsmall with
    ⟨b, hb⟩ | ⟨e1, he1⟩ | ⟨e2, he2⟩
  · have hWm : ∀ w ∈ W, GGQ2S08Mono b w := by
      intro w hw
      rcases hb with h | h
      · exact (h w).1 (hWR hw)
      · obtain ⟨σ, ε, hε, -, hact⟩ := (h w).1 (hWR hw)
        exact ⟨σ, ε, hε, hact⟩
    exact (ggQ2s08_bigC_mono_false h3 (by omega) b e hWm xv hfixx f hf hWf).elim
  · have h1 := ggQ2s08core_sym1 hℓ R W hWR e1 he1 s (CoxeterMatrix.A ℓ) (Or.inl rfl)
      hsR hsrefl hrel hdist hncomm hWs r hrR hr hrW
    exact le_antisymm hM0le (h1.symm.le.trans hclos)
  · exact ggQ2s08core_sym2 hℓ R W hWR e2 he2 s (CoxeterMatrix.A ℓ) (Or.inl rfl)
      hsR hsrefl hrel hdist hncomm hWs xv hWfix r hrR hr hrx

end CFSG.StandardType

end


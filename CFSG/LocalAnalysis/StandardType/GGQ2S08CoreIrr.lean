module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreClassify
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreMono
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreSym1
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreSym2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_core_irr (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V]
    {ℓ : ℕ} (hℓ : 9 ≤ ℓ) (hdim : Module.finrank (ZMod 3) V = ℓ + 1)
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (hirr : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hsmall : 8 * Nat.card R < 3 ^ ((ℓ + 1) * ℓ / 2)) (hWR : W ≤ R)
    (s : Fin ℓ → (V ≃ₗ[ZMod 3] V)) (M : CoxeterMatrix (Fin ℓ))
    (hM : M = CoxeterMatrix.A ℓ ∨ M = CoxeterMatrix.B ℓ ∨ M = ggCoxeterMatrixD ℓ)
    (hsR : ∀ i, s i ∈ R) (hsrefl : ∀ i, GGLinRefl (s i))
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ M i j = 1) (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hncomm : ∀ i j, i ≠ j → M i j ≠ 2 → s i * s j ≠ s j * s i)
    (hWs : W = Subgroup.closure (Set.range s)) (xv : V) (hx : xv ≠ 0)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hWirr : ∀ U : Submodule (ZMod 3) V, Submodule.span (ZMod 3) {xv} ≤ U →
      (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = Submodule.span (ZMod 3) {xv} ∨ U = ⊤)
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hr : GGLinRefl r) (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv) :
    GGQ2S08M0 R W r xv = R ∨ GGQ2S08CoreRO (N := ℓ + 1) R W r xv := by
  have hsW : ∀ i, s i ∈ W := fun i => by rw [hWs]; exact Subgroup.subset_closure ⟨i, rfl⟩
  have hWgen : W = Subgroup.closure {t | t ∈ W ∧ GGLinRefl t} := by
    apply le_antisymm
    · calc W = Subgroup.closure (Set.range s) := hWs
        _ ≤ _ := Subgroup.closure_mono (by rintro _ ⟨i, rfl⟩; exact ⟨hsW i, hsrefl i⟩)
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
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
    ⟨b, hb⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact ggQ2s08_core_mono (by omega) b R W hb hWR hWgen xv hx hWfix hWirr r hrR hr hrx
  · left
    have h1 := ggQ2s08core_sym1 hℓ R W hWR e he s M hM hsR hsrefl hrel hdist hncomm hWs r hrR hr hrW
    exact le_antisymm hM0le (h1.symm.le.trans hclos)
  · left
    exact ggQ2s08core_sym2 hℓ R W hWR e he s M hM hsR hsrefl hrel hdist hncomm hWs xv hWfix r hrR hr
      hrx

end CFSG.StandardType

end

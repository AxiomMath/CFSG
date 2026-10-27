module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreIrr
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreRed
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreAbs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_core (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ℓ : ℕ} (hℓ : 9 ≤ ℓ) (hdim : Module.finrank (ZMod 3) V = ℓ + 1)
    (H : Submodule (ZMod 3) V) (xv : V) (hx : xv ≠ 0)
      (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (r t : V ≃ₗ[ZMod 3] V)
    (hR : R = Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r, t}))
    (s : Fin ℓ → (V ≃ₗ[ZMod 3] V)) (M : CoxeterMatrix (Fin ℓ))
    (hM : M = CoxeterMatrix.A ℓ ∨ M = CoxeterMatrix.B ℓ ∨ M = ggCoxeterMatrixD ℓ)
    (hsrefl : ∀ i, GGLinRefl (s i))
    (hsH : ∀ i, ∃ h ∈ H, h ≠ 0 ∧ ∀ v, s i v - v ∈ Submodule.span (ZMod 3) {h})
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ M i j = 1) (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hncomm : ∀ i j, i ≠ j → M i j ≠ 2 → s i * s j ≠ s j * s i)
    (hWs : W = Subgroup.closure (Set.range s))
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hWH : ∀ w ∈ W, ∀ h ∈ H, w h ∈ H)
    (hWirrH : ∀ U : Submodule (ZMod 3) V, U ≤ H → (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = ⊥ ∨ U = H)
    (hr : GGLinRefl r) (ht : GGLinRefl t) (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv)
    (htx : ¬ ∃ c : ZMod 3, t xv = c • xv)
    (hnt : ∀ a ∈ R, ¬
      (Module.finrank (ZMod 3) (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w))
    (hsmall_irr : 8 * Nat.card R < 3 ^ ((ℓ + 1) * ℓ / 2))
    (hsmall_red : (∀ a ∈ R, ∀ h ∈ H, a h ∈ H) → 8 * Nat.card R < 3 ^ (ℓ * (ℓ - 1) / 2)) :
    t ∈ GGQ2S08M0 R W r xv ∨ GGQ2S08CoreRO (N := ℓ + 1) R W r xv := by
  have hWR : W ≤ R := by
    intro w hw
    rw [hR]
    exact Subgroup.subset_closure (Or.inl hw)
  have hrR : r ∈ R := by
    rw [hR]
    exact Subgroup.subset_closure (Or.inr (by simp))
  have htR : t ∈ R := by
    rw [hR]
    exact Subgroup.subset_closure (Or.inr (by simp))
  have hsR : ∀ i, s i ∈ R := fun i => hWR (by
    rw [hWs]
    exact Subgroup.subset_closure ⟨i, rfl⟩)
  by_cases hirr : ∀ U : Submodule (ZMod 3) V,
      (∀ a ∈ R, ∀ u ∈ U, a u ∈ U) → U = ⊥ ∨ U = ⊤
  · have hgen : R = Subgroup.closure {a | a ∈ R ∧ GGLinRefl a} := by
      apply le_antisymm
      · conv_lhs => rw [hR]
        rw [Subgroup.closure_le]
        rintro a (hw | hr_or_t)
        · exact Subgroup.closure_mono (fun x hx => by
            obtain ⟨i, rfl⟩ := hx
            exact show s i ∈ {b | b ∈ R ∧ GGLinRefl b} from ⟨hsR i, hsrefl i⟩) (hWs ▸ hw)
        · rcases hr_or_t with rfl | rfl
          · exact Subgroup.subset_closure ⟨hrR, hr⟩
          · exact Subgroup.subset_closure ⟨htR, ht⟩
      · rw [Subgroup.closure_le]
        intro a ha
        exact ha.1
    have habs : ZS.AbsIrred 3 R :=
      ggQ2s08core_absIrred_of_irred R hgen ⟨r, hrR, hr⟩ hirr
    have hWirr : ∀ U : Submodule (ZMod 3) V, Submodule.span (ZMod 3) {xv} ≤ U →
        (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = Submodule.span (ZMod 3) {xv} ∨ U = ⊤ := by
      intro U hxU hWU
      have hUH : U ⊓ H = ⊥ ∨ U ⊓ H = H := by
        apply hWirrH (U ⊓ H) inf_le_right
        intro w hw u hu
        exact Submodule.mem_inf.mpr ⟨hWU w hw u hu.1, hWH w hw u hu.2⟩
      rcases hUH with h0 | hH'
      · left
        apply le_antisymm ?_ hxU
        intro u hu
        have husup : u ∈ H ⊔ Submodule.span (ZMod 3) {xv} := by
          rw [hH.sup_eq_top]; exact Submodule.mem_top
        rw [Submodule.mem_sup] at husup
        obtain ⟨h, hhH, z, hz, hsum⟩ := husup
        have hzU : z ∈ U := hxU hz
        have hhU : h ∈ U := by
          have huz : h = u - z := by rw [← hsum]; abel
          rw [huz]
          exact Submodule.sub_mem U hu hzU
        have hhbot : h ∈ (⊥ : Submodule (ZMod 3) V) := by
          rw [← h0]
          exact Submodule.mem_inf.mpr ⟨hhU, hhH⟩
        have hh0 : h = 0 := by simpa using hhbot
        have huz : u = z := by rw [← hsum, hh0, zero_add]
        rw [huz]; exact hz
      · right
        have hHU : H ≤ U := by rw [← hH']; exact inf_le_left
        have hle : H ⊔ Submodule.span (ZMod 3) {xv} ≤ U := sup_le hHU hxU
        rw [hH.sup_eq_top] at hle
        exact top_le_iff.mp hle
    rcases ggQ2s08_core_irr hKG hℓ hdim R W habs hgen hsmall_irr hWR s M hM hsR hsrefl
        hrel hdist hncomm hWs xv hx hWfix hWirr r hrR hr hrx with hM0 | hRO
    · left
      rw [hM0]
      exact htR
    · right
      exact hRO
  · rw [not_forall] at hirr
    obtain ⟨U, hU⟩ := hirr
    rw [not_imp] at hU
    obtain ⟨hUR, hUnot⟩ := hU
    rw [not_or] at hUnot
    obtain ⟨hU0, hU1⟩ := hUnot
    have hUH : U = H :=
      ggQ2s08core_red_invariant H xv hH W R hWR hWH hWfix hWirrH r hrR hrx U hU0 hU1 hUR
    have hpresH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H := by
      intro a ha h hh
      have hhU : h ∈ U := hUH.symm ▸ hh
      have hahU : a h ∈ U := hUR a ha h hhU
      rwa [hUH] at hahU
    have hsmall : 8 * Nat.card R < 3 ^ (ℓ * (ℓ - 1) / 2) := hsmall_red hpresH
    left
    exact ggQ2s08_core_red hKG hℓ hdim H xv hx hH R W hWR hWH s M hM hsrefl hsH hrel
      hdist hncomm hWs hWfix hWirrH r t hR hr ht hrx htx hnt hsmall ⟨U, hU0, hU1, hUR⟩

end CFSG.StandardType

end

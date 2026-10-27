module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_inCalWStar_of_hyp125 (D : Data G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h0 : V₀ = ⊥) : InCalWStar D.M D.T V := by
  rcases hV.1 with ⟨hW, -⟩ | ⟨hV0, -, -⟩
  · exact hW
  · rw [h0] at hV0
    exact absurd rfl hV0.1.1

theorem s16h_false_of_mixed_beta (D : Data G) (S : s16h_Std D) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L) (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {q : ℕ}
    (hq : q ∈ D.sig) {e : G} (heM : e ∈ D.M) (heq : e ^ q = 1)
    (heW : ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L, e * w = w * e)
    (heV : ∃ v ∈ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L, e * v ≠ v * e)
    (hc : ∀ T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      T ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
        normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
      (∀ g ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
        normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _),
          ∀ x ∈ T, g * x * g⁻¹ ∈ T) →
      (∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) →
      (∃ f ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
        normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _),
          ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
          f ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
          f ^ r ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) →
      T ≤ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) : False := by
  have hV := h.hyp151.isElemAbelian
  have hV125 := h.hyp151.hyp125
  let Z₁ : Subgroup G := wSub ⊥ V hV L ⊓ centralizer (L : Set G)
  let Y : Subgroup G := v1Sub D.M ⊥ V hV L
  have hs' : Set.ncard {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    simpa [s15, lBar] using hs
  obtain ⟨ψ, hψmem, hψne⟩ := (c23a_two_conj hs').1
  obtain ⟨ψst, hψM, hψeq⟩ := (mem_barSub ⊥ V hV D.M ψ).1 hψmem
  have hxM : (ψst : G) ∈ D.M := hψM
  have hx : (ψst : G) ∉ nBar D.M ⊥ V hV L := by
    intro hxn
    rw [nBar] at hxn
    obtain ⟨-, hstab, hnorm⟩ := (mem_preBarSub D.M ⊥ V hV _).1 hxn
    have heq : (⟨(ψst : G), hstab⟩ : stabTil ⊥ V) = ψst := Subtype.ext rfl
    rw [heq, hψeq] at hnorm
    exact hψne ((Subgroup.mem_normalizer_iff_map_conj_eq).1 hnorm)
  have hLbar : lBar ⊥ V hV L ≠ ⊥ := by
    intro hbot
    apply hψne
    rw [hbot, Subgroup.map_bot]
  have hsup : Y = Z₁ ⊔ Z₁.map (MulAut.conj (ψst : G)).toMonoidHom :=
    (s16h_v1Sub_eq_sup_of_s_two D h hs hxM hx).1
  have heZ₁ : ∀ z ∈ Z₁, e * z = z * e := by
    intro z hz
    exact heW z (Subgroup.mem_inf.1 hz).1
  have hne : Z₁.map (MulAut.conj (ψst : G)).toMonoidHom ≠ Z₁ := by
    intro hZ
    obtain ⟨v, hvY, hve⟩ := heV
    have hvZ : v ∈ Z₁ := by
      have hmem : v ∈ Z₁ ⊔ Z₁.map (MulAut.conj (ψst : G)).toMonoidHom := hsup ▸ hvY
      rw [hZ, sup_idem] at hmem
      exact hmem
    exact hve (heZ₁ v hvZ)
  have heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj (ψst : G)).toMonoidHom, e * z ≠ z * e := by
    by_contra h
    push Not at h
    obtain ⟨v, hvY, hve⟩ := heV
    apply hve
    have hcent : Z₁ ⊔ Z₁.map (MulAut.conj (ψst : G)).toMonoidHom ≤
        Subgroup.centralizer ({e} : Set G) := by
      apply sup_le
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst w
        exact heZ₁ z hz
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst w
        exact h z hz
    have hv : v ∈ Subgroup.centralizer ({e} : Set G) := by
      apply hcent
      rw [← hsup]
      exact hvY
    exact (Subgroup.mem_centralizer_iff.mp hv) e (by simp)
  have hB : s16h_MixedCfg D.M (nBar D.M ⊥ V hV L) Y Z₁ (ψst : G) :=
    s16h_mixedCfg_of_s_two D h hs hxM hx hne
  have hcG := s16h_cG_of_hc D h hc
  have hW : InCalW D.M D.T Y :=
    s16h_inCalW_of_mixed D S.h61 hB hq heM heq heZ₁ heZ₂ hcG
  have hStar : InCalWStar D.M D.T V := s16h_inCalWStar_of_hyp125 D hV125 rfl
  have hle : Y ≤ V := s15_Infra_v1Sub_le hV125 hV
  have hYV : Y = V := hStar.2 Y hW hle
  exact (s16h_v1Sub_ne_V D h hLbar) hYV

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

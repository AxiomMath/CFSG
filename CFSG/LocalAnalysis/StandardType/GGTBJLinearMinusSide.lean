module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBSupported
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBTwisted
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL

public section

namespace CFSG.StandardType.CoordSL

open CFSG CFSG.Assembly TypeBDatum

theorem prodEquiv_of_frameHom
    {G : Type} [Group G] {F : Type} [Field F]
    {n e m t p : ℕ} [NeZero p] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (A₁ : Matrix.SpecialLinearGroup (Fin n) F)
    (ε : Fin n ≃ (Fin e × Fin m) ⊕ Fin t)
    {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1) (hCp : C ^ p = 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    (he : 0 < e)
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1))
    (hrange : (frameHom ψ A₁ ε hC hCp).range = Bs ⊓ X)
    (hsup : (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Bs)
    (hdisj : Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    ∃ Θ : ((Fin m → Multiplicative (ZMod p)) ×
        ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs,
      ∀ w c, (Θ (w, c) : G) =
        frameHom ψ A₁ ε hC hCp ((MulEquiv.piMultiplicative
          fun _ : Fin m => ZMod p).symm w) * c := by
  classical
  let E := (MulEquiv.piMultiplicative fun _ : Fin m => ZMod p).symm
  let Θ₁ := (frameHom ψ A₁ ε hC hCp).comp E.toMonoidHom
  have hinj : Function.Injective Θ₁ :=
    (frameHom_injective ψ A₁ ε hC hCp hker he hunit).comp E.injective
  have hrange₁ : Θ₁.range = Bs ⊓ X := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [← hrange]
      exact ⟨E w, rfl⟩
    · intro hz
      rw [← hrange] at hz
      obtain ⟨w, rfl⟩ := hz
      refine ⟨E.symm w, ?_⟩
      change frameHom ψ A₁ ε hC hCp (E (E.symm w)) = _
      rw [E.apply_symm_apply]
  have hinf : Θ₁.range ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) = ⊥ := by
    rw [hrange₁]
    have hEq : (Bs ⊓ X) ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) =
        Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
      · intro hz
        exact ⟨hz.1, hz.1.1, hz.2⟩
    exact hEq.trans hdisj
  obtain ⟨Θ, hΘ⟩ := exists_prodEquiv_of_frame hBs Θ₁ hinj
    (by rw [hrange₁]; exact inf_le_left)
    (Bs ⊓ Subgroup.centralizer (X : Set G)) inf_le_left
    (by rw [hrange₁]; exact hsup) hinf
  exact ⟨Θ, hΘ⟩

theorem sideDatum_of_zero_pattern
    {G : Type} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : 3 ≤ m) {Bs X J : Subgroup G}
    (hBs : IsElemAbelian p Bs) {W₀ : Type} [Group W₀]
    (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (hX : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ))
    (β : Fin m → ZMod p) (hβ : β ≠ 0)
    (hsparse : ∃ j j' : Fin m, ∀ i, i ≠ j → i ≠ j' → β i = 0)
    (hJ : ggAutomizer J Bs =
      (signedSupportedAut m p (Finset.univ.filter fun i => β i = 0)).map (liftBs Θ)) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  let S := Finset.univ.filter fun i => β i = 0
  have hSsub : S ⊆ (Finset.univ : Finset (Fin m)) := Finset.filter_subset _ _
  have hdiff : (Finset.univ \ S).card + S.card = m := by
    simpa using Finset.card_sdiff_add_card_eq_card hSsub
  obtain ⟨j, j', hjj'⟩ := hsparse
  have hsub : Finset.univ \ S ⊆ ({j, j'} : Finset (Fin m)) := by
    intro i hi
    by_cases hij : i = j
    · simp [hij]
    by_cases hij' : i = j'
    · simp [hij']
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjj' i hij hij'⟩
    exact False.elim ((Finset.mem_sdiff.mp hi).2 hiS)
  have hpair : ({j, j'} : Finset (Fin m)).card ≤ 2 := by
    calc ({j, j'} : Finset (Fin m)).card ≤ ({j'} : Finset (Fin m)).card + 1 :=
      Finset.card_insert_le _ _
      _ = 2 := by simp
  have htwo : (Finset.univ \ S).card ≤ 2 := (Finset.card_le_card hsub).trans hpair
  have hSneq : S ≠ Finset.univ := by
    intro h
    apply hβ
    funext i
    have hi : i ∈ S := h.symm ▸ Finset.mem_univ i
    have hzi : β i = 0 := (Finset.mem_filter.mp hi).2
    simpa using hzi
  have hSlt : S.card < m := by
    have h := Finset.card_lt_card (lt_of_le_of_ne hSsub hSneq)
    simpa using h
  have hS1 : 1 ≤ S.card := by omega
  have hc1 : 1 ≤ m - S.card := by omega
  have hc3 : m - S.card ≤ 3 := by omega
  have hd := ggTBJTypeB_sideDatum_signedSupported hp2 (by omega) hBs Θ hX hS1 hc1 hc3 hJ
  by_cases hc : m - S.card = 1
  · exact Or.inl (hd.1 hc)
  · exact Or.inr (hd.2 (by omega))

theorem sideDatum_of_class_pattern
    {G : Type} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : 3 ≤ m) {Bs X J : Subgroup G}
    (hBs : IsElemAbelian p Bs) {W₀ : Type} [Group W₀]
    (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (hX : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ))
    (β : Fin m → ZMod p) (c : ZMod p)
    (hclass : ∃ k : Fin m, ∀ i, i ≠ k → β i = c)
    (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1)
    (hJ : ggAutomizer J Bs =
      (twistedPermAut m p (Finset.univ.filter fun i => β i = c) s hs).map (liftBs Θ)) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  let S := Finset.univ.filter fun i => β i = c
  have hSsub : S ⊆ (Finset.univ : Finset (Fin m)) := Finset.filter_subset _ _
  have hdiff : (Finset.univ \ S).card + S.card = m := by
    simpa using Finset.card_sdiff_add_card_eq_card hSsub
  obtain ⟨k, hk⟩ := hclass
  have hsub : Finset.univ \ S ⊆ ({k} : Finset (Fin m)) := by
    intro i hi
    by_cases hik : i = k
    · simp [hik]
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk i hik⟩
    exact False.elim ((Finset.mem_sdiff.mp hi).2 hiS)
  have hone : (Finset.univ \ S).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hS2 : 2 ≤ S.card := by omega
  have hc1 : 1 ≤ m + 1 - S.card := by omega
  have hc3 : m + 1 - S.card ≤ 3 := by omega
  have hd := ggTBJTypeB_sideDatum_twistedPerm hp2 (by omega) hBs Θ hX hS2 hc3 hs hJ
  by_cases hc : m + 1 - S.card = 1
  · exact Or.inl (hd.1 hc)
  · exact Or.inr (hd.2 (by omega))

end CFSG.StandardType.CoordSL

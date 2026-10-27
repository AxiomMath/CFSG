module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabTr
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabD
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabA
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMSel
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma p9uRMS_actsAs_of_map {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {β : Additive ↥Bs ≃+ DVec m} {A : Subgroup (MulAut ↥Bs)}
    {W : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)}
    (h : A.map (ggLin (p := 3) β) = W) : qtwoDActsAs β A W := by
  constructor
  · intro a ha
    exact ⟨ggLin (p := 3) β a, by rw [← h]; exact ⟨a, ha, rfl⟩,
      fun s => (ggLin_apply_ofMul (p := 3) β a s).symm⟩
  · intro w hw
    rw [← h] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    exact ⟨a, ha, fun s => (ggLin_apply_ofMul (p := 3) β a s).symm⟩

private lemma p9uRMS_ggLin_eq_of_apply {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {β : Additive ↥Bs ≃+ DVec m} {a : MulAut ↥Bs} {u : DVec m ≃ₗ[ZMod 3] DVec m}
    (h : ∀ b : ↥Bs, β (Additive.ofMul (a b)) = u (β (Additive.ofMul b))) :
    ggLin (p := 3) β a = u :=
  LinearEquiv.ext fun v => by
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, v = β (Additive.ofMul b) :=
      ⟨Additive.toMul (β.symm v), by simp⟩
    rw [ggLin_apply_ofMul]
    exact h b

private lemma p9uRMS_sign_mul {x y : ZMod 3} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

private def p9uRMS_MatSet (m : ℕ) (w : DVec m) : Set (DVec m ≃ₗ[ZMod 3] DVec m) :=
  {A | A w = w ∧ ∀ u ∈ dEvenStab m w, A * u * A⁻¹ ∈ dEvenStab m w}

private lemma p9uRMS_smul_eq_of_smul_eq {m : ℕ} {x y : DVec m} {c : ZMod 3} (hc : c ≠ 0)
    (h : c • x = c • y) : x = y := by
  have := congrArg (fun z => c⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using this

private lemma p9uRMS_dEvenStab_smul {m : ℕ} {w : DVec m} {c : ZMod 3} (hc : c ≠ 0) :
    dEvenStab m (c • w) = dEvenStab m w := by
  ext A
  change A ∈ dEven m ∧ A (c • w) = c • w ↔ A ∈ dEven m ∧ A w = w
  rw [map_smul]
  constructor
  · rintro ⟨hm, h⟩
    exact ⟨hm, p9uRMS_smul_eq_of_smul_eq hc h⟩
  · rintro ⟨hm, h⟩
    exact ⟨hm, by rw [h]⟩

private lemma p9uRMS_MatSet_smul {m : ℕ} {w : DVec m} {c : ZMod 3} (hc : c ≠ 0) :
    p9uRMS_MatSet m (c • w) = p9uRMS_MatSet m w := by
  ext A
  constructor
  · rintro ⟨hfix, hnorm⟩
    refine ⟨p9uRMS_smul_eq_of_smul_eq hc (by rwa [map_smul] at hfix), ?_⟩
    rw [p9uRMS_dEvenStab_smul (w := w) hc] at hnorm
    exact hnorm
  · rintro ⟨hfix, hnorm⟩
    refine ⟨?_, ?_⟩
    · rw [map_smul, hfix]
    · rw [p9uRMS_dEvenStab_smul (w := w) hc]
      exact hnorm

private lemma p9uRMS_signedPerm_apply {m : ℕ} {T : DVec m ≃ₗ[ZMod 3] DVec m}
    {σ : Equiv.Perm (Fin m)} {c : Fin m → ZMod 3}
    (hT : ∀ i, T (Pi.single i 1) = c i • Pi.single (σ i) 1) (v : DVec m) (j : Fin m) :
    T v j = v (σ.symm j) * c (σ.symm j) := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ZMod 3) := by
    ext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
    · intro i _ hi
      simp [Pi.smul_apply, Pi.single_apply, hi]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, hT]
  rw [Finset.sum_apply, Finset.sum_eq_single (σ.symm j)]
  · simp [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  · intro i _ hi
    have hne : σ i ≠ j := fun h =>
      hi (σ.injective (h.trans (Equiv.apply_symm_apply σ j).symm))
    simp [Pi.smul_apply, Pi.single_apply, hne]
  · intro hj
    exact absurd (Finset.mem_univ (σ.symm j)) hj

private lemma p9uRMS_unitary {m : ℕ} (hm : 7 ≤ m) {w : DVec m}
    (hw : ∀ i, w i = 1 ∨ w i = -1) :
    Nat.card (p9uRMS_MatSet m w) ≤ 2 ^ (m - 1) * (m - 1).factorial ∧
      ∀ A : DVec m ≃ₗ[ZMod 3] DVec m, A ∈ p9uRMS_MatSet m w → dIsRefl A →
        A ∈ dEvenStab m w ∨ ∃ i : Fin m, A = dNeg m i := by
  have hA := qtwoDRMStab_A (m := m) (by omega) hw
  refine ⟨hA.1, fun A hA' hrefl => Or.inl (hA.2 A hA'.1 hA'.2 hrefl)⟩

private lemma p9uRMS_orthogonal {m : ℕ} (hm : 7 ≤ m) {w : DVec m} {i₀ : Fin m} {c : ZMod 3}
    (hc : c ≠ 0) (hw : w = c • Pi.single i₀ 1) :
    Nat.card (p9uRMS_MatSet m w) ≤ 2 ^ (m - 1) * (m - 1).factorial ∧
      ∀ A : DVec m ≃ₗ[ZMod 3] DVec m, A ∈ p9uRMS_MatSet m w → dIsRefl A →
        A ∈ dEvenStab m w ∨ ∃ i : Fin m, A = dNeg m i := by
  subst hw
  have hD := qtwoDRMStab_D (m := m) (by omega) i₀
  refine ⟨?_, ?_⟩
  · rw [p9uRMS_MatSet_smul (w := Pi.single i₀ 1) hc]
    exact hD.1
  · intro A hA hrefl
    have hfix : A (c • Pi.single i₀ 1) = c • Pi.single i₀ 1 := hA.1
    have hnorm := hA.2
    rw [map_smul] at hfix
    have hfix' : A (Pi.single i₀ 1) = Pi.single i₀ 1 :=
      p9uRMS_smul_eq_of_smul_eq hc hfix
    rw [p9uRMS_dEvenStab_smul (w := Pi.single i₀ 1) hc] at hnorm
    have hD' := hD.2 A hfix' hnorm hrefl
    simpa only [p9uRMS_dEvenStab_smul (w := Pi.single i₀ 1) hc] using hD'

private lemma p9uRMS_stab_of {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (ha₀ : GGLNoncyclicInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hx : x ∈ Bs) {m : ℕ} {β : Additive ↥Bs ≃+ DVec m} {w : DVec m} {c : ZMod 3}
    (hc : c ≠ 0) (hxβ : β (Additive.ofMul ⟨x, hx⟩) = c • w)
    (hAβ : qtwoDActsAs β (ggAutomizer L Bs) (dEvenStab m w))
    (hbound : Nat.card (p9uRMS_MatSet m w) ≤ 2 ^ (m - 1) * (m - 1).factorial)
    (hclass : ∀ A : DVec m ≃ₗ[ZMod 3] DVec m, A ∈ p9uRMS_MatSet m w → dIsRefl A →
      A ∈ dEvenStab m w ∨ ∃ i : Fin m, A = dNeg m i) :
    Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} ≤
        2 ^ (m - 1) * (m - 1).factorial ∧
      ∀ a ∈ ggInduced ⊤ Bs, GGIsReflection 3 a → a ⟨x, hx⟩ = ⟨x, hx⟩ →
        a ∈ ggAutomizer L Bs ∨
          ∃ i : Fin m, ∀ b : ↥Bs, β (Additive.ofMul (a b)) = dNeg m i (β (Additive.ofMul b)) := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hfix_of : ∀ a : MulAut ↥Bs, a ⟨x, hx⟩ = ⟨x, hx⟩ → ggLin (p := 3) β a w = w := by
    intro a hax
    have h1 : ggLin (p := 3) β a (β (Additive.ofMul ⟨x, hx⟩)) = β (Additive.ofMul ⟨x, hx⟩) := by
      rw [ggLin_apply_ofMul, hax]
    rw [hxβ] at h1
    exact p9uRMS_smul_eq_of_smul_eq hc (by rwa [map_smul] at h1)
  have hnorm_of : ∀ a : MulAut ↥Bs, a ∈ ggInduced ⊤ Bs → a ⟨x, hx⟩ = ⟨x, hx⟩ →
      ∀ u ∈ dEvenStab m w, ggLin (p := 3) β a * u * (ggLin (p := 3) β a)⁻¹ ∈ dEvenStab m w := by
    intro a ha hax u hu
    obtain ⟨a', ha', hact⟩ := hAβ.2 u hu
    have haeq : ggLin (p := 3) β a' = u := p9uRMS_ggLin_eq_of_apply hact
    have hconj : a * a' * a⁻¹ ∈ ggAutomizer L Bs :=
      qtwoDRMStab_normalizes ha₀ hcfg hx ha hax ha'
    obtain ⟨w'', hw'', hw''act⟩ := hAβ.1 (a * a' * a⁻¹) hconj
    have heq : ggLin (p := 3) β (a * a' * a⁻¹) = w'' := p9uRMS_ggLin_eq_of_apply hw''act
    have heq2 : ggLin (p := 3) β (a * a' * a⁻¹) =
        ggLin (p := 3) β a * u * (ggLin (p := 3) β a)⁻¹ := by
      simp only [map_mul, map_inv, haeq]
    rw [← heq2, heq]
    exact hw''
  let Φ : {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} →
      p9uRMS_MatSet m w :=
    fun a => ⟨ggLin (p := 3) β a.1, hfix_of a.1 a.2.2, hnorm_of a.1 a.2.1 a.2.2⟩
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h1 : ggLin (p := 3) β a.1 = ggLin (p := 3) β b.1 := congrArg Subtype.val hab
    exact Subtype.ext (ggLin_injective (p := 3) β h1)
  haveI : Finite (p9uRMS_MatSet m w) :=
    Finite.of_injective (fun A : p9uRMS_MatSet m w => (A.1 : DVec m → DVec m))
      (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  have hcard : Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} ≤
      Nat.card (p9uRMS_MatSet m w) := Nat.card_le_card_of_injective Φ hΦinj
  refine ⟨hcard.trans hbound, ?_⟩
  intro a ha hrefl hax
  have hMrefl : dIsRefl (ggLin (p := 3) β a) := exists_of_ggIsReflection β hrefl
  have hMmem : ggLin (p := 3) β a ∈ p9uRMS_MatSet m w :=
    ⟨hfix_of a hax, hnorm_of a ha hax⟩
  rcases hclass (ggLin (p := 3) β a) hMmem hMrefl with hmem | ⟨i, hi⟩
  · left
    obtain ⟨a', ha', hact⟩ := hAβ.2 (ggLin (p := 3) β a) hmem
    have haeq : ggLin (p := 3) β a' = ggLin (p := 3) β a := p9uRMS_ggLin_eq_of_apply hact
    have : a' = a := ggLin_injective (p := 3) β haeq
    rwa [this] at ha'
  · exact Or.inr ⟨i, fun b => by rw [← ggLin_apply_ofMul (p := 3) β a b, hi]⟩

theorem ggQTwoDRMStabInput_of_coords (ha₀ : GGLNoncyclicInput) (hC : GGQTwoDRMBaseCoordInput) :
    GGQTwoDRMStabInput := by
  intro G instG instF p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hx β hβ
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  obtain ⟨hx₀, β₀, hJ₀, hcases⟩ := hC G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  have hJ : qtwoDActsAs β (ggAutomizerJoin L Bs 𝒦) (dEven m) :=
    p9uRMS_actsAs_of_map (qtwoD_image_eq (m := m) (by omega) hM β hβ)
  have hsub : (⟨x, hx₀⟩ : ↥Bs) = ⟨x, hx⟩ := Subtype.ext rfl
  rcases hcases with ⟨ε, hε, hxε, hAε⟩ | ⟨i₀, c, hc, hxc, hAe⟩
  · obtain ⟨T, hT, hTβ, hAT⟩ := qtwoDRMStab_transfer (m := m) (by omega) hJ₀ hJ hAε
    obtain ⟨σ, cT, hcT, hTd⟩ := hT
    have hw : β (Additive.ofMul ⟨x, hx⟩) = T ε := by
      rw [← hsub, hTβ, hxε]
    have hsign : ∀ i, (T ε) i = 1 ∨ (T ε) i = -1 := by
      intro i
      rw [p9uRMS_signedPerm_apply hTd ε i]
      exact p9uRMS_sign_mul (hε (σ.symm i)) (hcT (σ.symm i))
    obtain ⟨hbound, hclass⟩ := p9uRMS_unitary (m := m) hm hsign
    exact p9uRMS_stab_of ha₀ hcfg.1 hx (c := 1) one_ne_zero (by simpa using hw) hAT hbound hclass
  · obtain ⟨T, hT, hTβ, hAT⟩ := qtwoDRMStab_transfer (m := m) (by omega) hJ₀ hJ hAe
    obtain ⟨σ, cT, hcT, hTd⟩ := hT
    have hw : β (Additive.ofMul ⟨x, hx⟩) = c • T (Pi.single i₀ 1) := by
      rw [← hsub, hTβ, hxc, map_smul]
    have hcT0 : cT i₀ ≠ 0 := by rcases hcT i₀ with h | h <;> rw [h] <;> norm_num
    obtain ⟨hbound, hclass⟩ :=
      p9uRMS_orthogonal (m := m) hm (w := T (Pi.single i₀ 1)) hcT0 (hTd i₀)
    exact p9uRMS_stab_of ha₀ hcfg.1 hx (c := c) hc hw hAT hbound hclass

end CFSG.StandardType.QTwo

end

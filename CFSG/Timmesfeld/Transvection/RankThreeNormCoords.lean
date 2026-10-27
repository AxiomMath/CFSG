module

public import CFSG.Timmesfeld.Transvection.RankThreeA2Coords
public import CFSG.Timmesfeld.Transvection.RankThreeNorm

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule RankThree
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

namespace IsMaxFrame

variable [Finite G] (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
  (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hml : MeetsLines Δ)
  (hq : ∀ l, 4 ≤ Nat.card (P l)) {n : ℕ} (φ : ∀ l, SL2Coords (P l) (Q l) n)
  {μ : (GaloisField 2 n)ˣ} (hμ1 : μ ≠ 1)
  {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)
  {ξ : Fin r ⊕ Fin r → Fin r ⊕ Fin r → F → G} {ξL : Fin r ⊕ Fin r → F → G}
  (hmem : ∀ i j : Fin r, i ≠ j → ∀ s,
    ξ (.inl j) (.inr i) s ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
  (hsurj : ∀ i j : Fin r, i ≠ j → ∀ g ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j),
    ∃ s, ξ (.inl j) (.inr i) s = g)
  (hmemP : ∀ i j : Fin r, i ≠ j → ∀ s,
    ξ (.inl j) (.inl i) s ∈ shortRootGroup Δ (P i) (Q i) (P j) (Q j))
  (hmemL : ∀ (l : Fin r) (c : F), σ c = c → ξL (.inl l) c ∈ P l)
  (hinjL : ∀ (l : Fin r) (s t : F), σ s = s → σ t = t → ξL (.inl l) s = ξL (.inl l) t → s = t)
  (hsl : ∀ i j : Fin r, i ≠ j → ∀ s t, σ t = t →
    ⁅ξ (.inl j) (.inr i) s, ξL (.inl i) t⁆ =
      ξ (.inl j) (.inl i) (s * t) * ξL (.inl j) (σ s * s * t))
include hfr hΔ hiso hpts hml hq φ hμ1 hσ hmem hsurj hmemP hmemL hinjL hsl

omit hfr hΔ hiso hpts hml hq φ hμ1 hσ hmem hsurj hmemP hmemL hinjL hsl in
private theorem mul_inv_eq_of_decomposition {a₁ a₂ b₃ b₄ c₁ c₂ : G}
    (heq0 : a₁ * a₂ = c₁ * c₂ * (b₃ * b₄))
    (hc₁₃ : Commute a₁⁻¹ c₁) (hc₂₃ : Commute c₂ b₃) (hc₁b : Commute a₁⁻¹ b₃) :
    a₂ * b₄⁻¹ = c₁ * b₃ * (a₁⁻¹ * c₂) := by
  calc a₂ * b₄⁻¹ = a₁⁻¹ * (a₁ * a₂) * b₄⁻¹ := by group
    _ = a₁⁻¹ * (c₁ * c₂ * (b₃ * b₄)) * b₄⁻¹ := by rw [heq0]
    _ = a₁⁻¹ * c₁ * (c₂ * b₃) := by group
    _ = c₁ * a₁⁻¹ * (b₃ * c₂) := by rw [hc₁₃.eq, hc₂₃.eq]
    _ = c₁ * (a₁⁻¹ * b₃) * c₂ := by group
    _ = c₁ * (b₃ * a₁⁻¹) * c₂ := by rw [hc₁b.eq]
    _ = c₁ * b₃ * (a₁⁻¹ * c₂) := by group

omit hiso hpts hml hq φ hμ1 hσ hmem hsurj hmemP hmemL hinjL hsl in
private theorem commute_factors {a₁ b₃ c₁ c₂ : G} {i j k : Fin r}
    (ha₁ : a₁ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k))
    (hb₃ : b₃ ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k))
    (hc₁ : c₁ ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k))
    (hc₂ : c₂ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k)) :
    Commute a₁⁻¹ c₁ ∧ Commute c₂ b₃ ∧ Commute a₁⁻¹ b₃ := by
  have hLL : Commuting (lineGroup Δ (P i) (P k)) (lineGroup Δ (P j) (P k)) :=
    hfr.toIsFrame.commuting_lineGroup_lineGroup hΔ.root (a := Sum.inl i) (b := Sum.inl k)
      (c := Sum.inl j) (d := Sum.inl k) (by simp) (by simp) (by simp) (by simp)
  have hLik := shortRootGroup_le_lineGroup (Δ := Δ) (P i) (Q i) (P k) (Q k)
  have hLjk := shortRootGroup_le_lineGroup (Δ := Δ) (P j) (Q j) (P k) (Q k)
  exact ⟨(hLL _ (hLik ha₁) _ (hLjk hc₁)).inv_left, hLL _ (hLik hc₂) _ (hLjk hb₃),
    (hLL _ (hLik ha₁) _ (hLjk hb₃)).inv_left⟩

omit hml hσ hmem hsurj hmemP hmemL hinjL hsl in
private theorem eq_of_mul_inv_eq {a₁ a₂ b₃ b₄ c₁ c₂ : G} {i j k : Fin r}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (ha₂ : a₂ ∈ P k) (hb₄ : b₄ ∈ P k)
    (hc₁ : c₁ ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k))
    (hb₃ : b₃ ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k))
    (ha₁ : a₁ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k))
    (hc₂ : c₂ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k))
    (he : a₂ * b₄⁻¹ = c₁ * b₃ * (a₁⁻¹ * c₂)) : a₂ = b₄ := by
  have hF := hfr.toIsFrame
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 := (φ i).card_eq
    rw [h0, pow_zero] at h1
    have := hq i
    omega
  have hifpf : ∀ w ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k),
      Commute w ((φ i).torusElt μ) → w = 1 := fun w hw hc =>
    ((hF.toPairFrame hik).commute_shortRootGroup_iff hΔ hiso hpts (hq i) (φ i)
      ((φ i).torusElt_mem μ) ((φ i).mat_torusElt μ) hμ1 hw).1 hc
  have hinf : shortRootGroup Δ (P j) (Q j) (P k) (Q k) ⊓ P k = ⊥ := by
    refine eq_bot_iff.2 fun w hw => ?_
    rw [← (hF.toPairFrame hjk).shortRootGroup_inf_sup_eq_bot hΔ]
    exact ⟨hw.1, Subgroup.mem_sup_right hw.2⟩
  have he1 := hF.eq_one_of_mem_of_eq_mul hΔ hij hik ((φ i).torusElt_mem μ) hifpf hinf
    (Subgroup.mul_mem _ ha₂ (Subgroup.inv_mem _ hb₄)) (Subgroup.mul_mem _ hc₁ hb₃)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha₁) hc₂) he
  exact mul_inv_eq_one.1 he1

theorem exists_commutator_eq_norm_mul {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (s t : F) : ∃ u, ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) u ∧
      σ u * u = σ s * s * (σ t * t) := by
  have hF := hfr.toIsFrame
  have hfixN : ∀ c, σ (σ c * c) = σ c * c := fun c => by
    rw [map_mul, hσ, mul_comm]
  set x := ξ (.inl j) (.inr i) s with hx_def
  set y := ξ (.inl k) (.inr j) t with hy_def
  have hx := hmem i j hij s
  have hy := hmem j k hjk t
  have hz := hfr.commutator_mem_shortRootGroup_of_coords hΔ hiso hpts hml hq φ hμ1 hij hik hjk
    hx hy
  obtain ⟨u, hu⟩ := hsurj i k hik _ hz
  refine ⟨u, hu.symm, ?_⟩
  set p := ξL (.inl i) 1 with hp_def
  have hp : p ∈ P i := hmemL i 1 (map_one σ)
  have hd : ξL (.inl j) (σ s * s * 1) ∈ P j :=
    hmemL j _ (by rw [mul_one]; exact hfixN s)
  have hv := hmemP i j hij (s * 1)
  have hxp : ⁅x, p⁆ = ξ (.inl j) (.inl i) (s * 1) * ξL (.inl j) (σ s * s * 1) :=
    hsl i j hij s 1 (map_one σ)
  have hyv : ⁅y, ξ (.inl j) (.inl i) (s * 1)⁆ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k) := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _
      (hfr.commutator_mem_plus_left hΔ hiso hpts hml hq φ hμ1 hij hik hjk hv hy)
  obtain ⟨c₁, hc₁, c₂, hc₂, hcore⟩ := hF.exists_commutator_commutator_eq hΔ hij hik hx hy hp hv
    hd hxp hyv fun u' hu' => hfr.commutator_mem_plus_right hΔ hiso hpts hml hq φ hμ1 hij hik
      hjk hx hu'
  have h1 : ⁅⁅x, y⁆, p⁆ = ξ (.inl k) (.inl i) (u * 1) * ξL (.inl k) (σ u * u * 1) := by
    rw [← hu]
    exact hsl i k hik u 1 (map_one σ)
  have hfixd : σ (σ s * s * 1) = σ s * s * 1 := by rw [mul_one]; exact hfixN s
  have h2 : ⁅y, ξL (.inl j) (σ s * s * 1)⁆ = ξ (.inl k) (.inl j) (t * (σ s * s * 1)) *
      ξL (.inl k) (σ t * t * (σ s * s * 1)) := hsl j k hjk t _ hfixd
  set a₁ := ξ (.inl k) (.inl i) (u * 1)
  set a₂ := ξL (.inl k) (σ u * u * 1)
  set b₃ := ξ (.inl k) (.inl j) (t * (σ s * s * 1))
  set b₄ := ξL (.inl k) (σ t * t * (σ s * s * 1))
  have ha₁ : a₁ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k) := hmemP i k hik _
  have hb₃ : b₃ ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k) := hmemP j k hjk _
  have hfix₂ : σ (σ u * u * 1) = σ u * u * 1 := by rw [mul_one]; exact hfixN u
  have hfix₄ : σ (σ t * t * (σ s * s * 1)) = σ t * t * (σ s * s * 1) := by
    rw [map_mul, mul_one, hfixN t, hfixN s]
  have ha₂ : a₂ ∈ P k := hmemL k _ hfix₂
  have hb₄ : b₄ ∈ P k := hmemL k _ hfix₄
  obtain ⟨hc₁₃, hc₂₃, hc₁b⟩ := commute_factors hfr hΔ ha₁ hb₃ hc₁ hc₂
  have heq0 : a₁ * a₂ = c₁ * c₂ * (b₃ * b₄) := by rw [← h1, hcore, h2]
  have he := mul_inv_eq_of_decomposition heq0 hc₁₃ hc₂₃ hc₁b
  have h24 : a₂ = b₄ := eq_of_mul_inv_eq hfr hΔ hiso hpts hq φ hμ1 hij hjk hik ha₂ hb₄ hc₁
    hb₃ ha₁ hc₂ he
  have := hinjL k _ _ hfix₂ hfix₄ h24
  calc σ u * u = σ u * u * 1 := (mul_one _).symm
    _ = σ t * t * (σ s * s * 1) := this
    _ = σ s * s * (σ t * t) := by ring

end IsMaxFrame

theorem IsMaxFrame.exists_commutator_eq_sq_mul [Finite G]
    (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) (hq : ∀ l, 4 ≤ Nat.card (P l)) {n : ℕ}
    (φ : ∀ l, SL2Coords (P l) (Q l) n) {μ : (GaloisField 2 n)ˣ} (hμ1 : μ ≠ 1) {F : Type*}
    [Field F] {ξ : Fin r ⊕ Fin r → Fin r ⊕ Fin r → F → G} {ξL : Fin r ⊕ Fin r → F → G}
    (hmem : ∀ i j : Fin r, i ≠ j → ∀ s,
      ξ (.inl j) (.inr i) s ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hsurj : ∀ i j : Fin r, i ≠ j → ∀ g ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j),
      ∃ s, ξ (.inl j) (.inr i) s = g)
    (hmemP : ∀ i j : Fin r, i ≠ j → ∀ s,
      ξ (.inl j) (.inl i) s ∈ shortRootGroup Δ (P i) (Q i) (P j) (Q j))
    (hmemL : ∀ (l : Fin r) (c : F), ξL (.inl l) c ∈ P l)
    (hinjL : ∀ l : Fin r, Function.Injective (ξL (.inl l)))
    (hsl : ∀ i j : Fin r, i ≠ j → ∀ s t,
      ⁅ξ (.inl j) (.inr i) s, ξL (.inl i) t⁆ =
        ξ (.inl j) (.inl i) (s * t) * ξL (.inl j) (s ^ 2 * t))
    {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t : F) :
    ∃ u, ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) u ∧
      u ^ 2 = s ^ 2 * t ^ 2 := by
  obtain ⟨u, hu, hN⟩ := hfr.exists_commutator_eq_norm_mul hΔ hiso hpts hml hq φ hμ1
    (σ := RingEquiv.refl F) (fun _ => rfl) hmem hsurj hmemP (fun l c _ => hmemL l c)
    (fun l _ _ _ _ h => hinjL l h)
    (fun i j hij s t _ => by rw [hsl i j hij s t, RingEquiv.refl_apply, pow_two]) hij hjk hik s t
  refine ⟨u, hu, ?_⟩
  simp only [RingEquiv.refl_apply] at hN
  rw [pow_two, pow_two, pow_two, hN]

namespace RankThree

variable {K F : Type*} [Field K] [Field F] {σ : F ≃+* F} {ι : K →+* F}
  {ξ : Fin r ⊕ Fin r → Fin r ⊕ Fin r → F → G} {h : Fin r → Kˣ → G}

theorem shortSMul_of_torus (hι : ∀ c, σ c = c → ∃ c' : K, ι c' = c)
    (h0 : ∀ i j : Fin r, i ≠ j → ξ (.inl j) (.inr i) 0 = 1)
    (hti : ∀ i j : Fin r, i ≠ j → ∀ (c : Kˣ) (s : F),
      h i c * ξ (.inl j) (.inr i) s * (h i c)⁻¹ = ξ (.inl j) (.inr i) (ι c * s))
    (htj : ∀ i j : Fin r, i ≠ j → ∀ (c : Kˣ) (s : F),
      h j c * ξ (.inl j) (.inr i) s * (h j c)⁻¹ = ξ (.inl j) (.inr i) (ι (c⁻¹ : Kˣ) * s))
    (htk : ∀ i j k : Fin r, i ≠ j → i ≠ k → j ≠ k → ∀ (c : Kˣ) (s : F),
      Commute (h k c) (ξ (.inl j) (.inr i) s))
    {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {c s t u : F} (hc : σ c = c)
    (hu : ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) u) :
    ⁅ξ (.inl j) (.inr i) (c * s), ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) (c * u) ∧
      ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) (c * t)⁆ = ξ (.inl k) (.inr i) (c * u) := by
  obtain ⟨c', rfl⟩ := hι c hc
  by_cases hc0 : c' = 0
  · subst hc0
    simp only [map_zero, zero_mul, h0 i j hij, h0 j k hjk, h0 i k hik, commutatorElement_one_left,
      commutatorElement_one_right, and_self]
  set γ : Kˣ := Units.mk0 c' hc0 with hγ
  have hγc : ((γ : Kˣ) : K) = c' := rfl
  have hγc' : (((γ⁻¹)⁻¹ : Kˣ) : K) = c' := by rw [inv_inv, hγc]
  constructor
  ·
    have hy : h i γ * ξ (.inl k) (.inr j) t * (h i γ)⁻¹ = ξ (.inl k) (.inr j) t := by
      rw [(htk j k i hjk hij.symm hik.symm γ t).eq, mul_inv_cancel_right]
    have := congrArg (fun g => h i γ * g * (h i γ)⁻¹) hu
    simp only [conj_commutatorElement, hti i j hij, hy, hti i k hik, hγc] at this
    exact this
  ·
    have hx : h k γ⁻¹ * ξ (.inl j) (.inr i) s * (h k γ⁻¹)⁻¹ = ξ (.inl j) (.inr i) s := by
      rw [(htk i j k hij hik hjk γ⁻¹ s).eq, mul_inv_cancel_right]
    have := congrArg (fun g => h k γ⁻¹ * g * (h k γ⁻¹)⁻¹) hu
    simp only [conj_commutatorElement, hx, htj j k hjk, htj i k hik, hγc'] at this
    exact this

end RankThree

end CFSG.Timmesfeld.Transvection

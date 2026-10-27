module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsSigned
import CFSG.GroupTheory.SignedPermFThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open CFSG.GroupTheory

theorem exists_signedPerm_eq_point : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ((∀ i, v i = ε i * ![1, 0, 0] (σ i)) ∨ (∀ i, v i = ε i * ![1, 1, 0] (σ i)) ∨
        (∀ i, v i = ε i * ![1, 1, 1] (σ i))) := by
  decide +kernel

private theorem exists_mulEquiv_comp {V Y : Type} [Group V] [Group Y] {c₀ c : V →* Y}
    (h₀ : Function.Injective c₀) (h : Function.Injective c) (hr : c₀.range = c.range) :
    ∃ θ : V ≃* V, ∀ v, c₀ (θ v) = c v := by
  let e₀ : V ≃* c₀.range := MonoidHom.ofInjective h₀
  let e : V ≃* c.range := MonoidHom.ofInjective h
  refine ⟨(e.trans (MulEquiv.subgroupCongr hr.symm)).trans e₀.symm, fun v => ?_⟩
  exact congrArg Subtype.val (e₀.apply_symm_apply ((MulEquiv.subgroupCongr hr.symm) (e v)))

namespace IsSignedCoords

variable {Y : Type} [Group Y] {A A₀ : Subgroup Y}
  {c c₀ : Multiplicative (Fin 3 → ZMod 3) →* Y}

private theorem mem_normalizer_of_realizes (h : IsSignedCoords A c) {n : Y}
    (hn : ∀ v, ∃ w, n * c v * n⁻¹ = c w) : n ∈ Subgroup.normalizer (A : Set Y) := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)
  refine Coords.mem_normalizer_of_conj_mem fun a ha => ?_
  rw [← h.2.1] at ha ⊢
  obtain ⟨v, rfl⟩ := ha
  obtain ⟨w, hw⟩ := hn v
  rw [hw]
  exact ⟨w, rfl⟩

theorem exists_conj_eq (h₀ : IsSignedCoords A c₀) (h : IsSignedCoords A c) :
    ∃ n ∈ Subgroup.normalizer (A : Set Y), ∀ v, c v = n * c₀ v * n⁻¹ := by
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_comp h₀.1 h.1 (h₀.2.1.trans h.2.1.symm)
  let α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3) := AddEquiv.toMultiplicative.symm θ
  have hαθ : ∀ v : Fin 3 → ZMod 3, Multiplicative.ofAdd (α v) = θ (Multiplicative.ofAdd v) :=
    fun v => rfl
  have hα : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∃ (τ : Equiv.Perm (Fin 3)) (δ : Fin 3 → ZMod 3), (∀ i, δ i ≠ 0) ∧ ∀ v,
        α (fun i => ε i * v (σ i)) = fun i => δ i * α v (τ i) := by
    intro σ ε hε
    obtain ⟨n, hn⟩ := h.2.2.2 σ ε hε
    have hnN : n ∈ Subgroup.normalizer (A : Set Y) :=
      mem_normalizer_of_realizes h fun v => ⟨_, hn v⟩
    obtain ⟨τ, δ, hδ, hτ⟩ := h₀.2.2.1 n hnN
    refine ⟨τ, δ, hδ, fun v => ?_⟩
    apply Multiplicative.ofAdd.injective
    apply h₀.1
    have h1 := hn (Multiplicative.ofAdd v)
    simp only [toAdd_ofAdd] at h1
    have h2 := hτ (Multiplicative.ofAdd (α v))
    simp only [toAdd_ofAdd] at h2
    rw [hαθ, hθ, ← h1, ← hθ (Multiplicative.ofAdd v), ← hαθ v, h2]
  obtain ⟨σ₀, ε₀, hε₀, hα₀⟩ := eq_signedPerm_of_normalizes α hα
  obtain ⟨n₀, hn₀⟩ := h₀.2.2.2 σ₀ ε₀ hε₀
  refine ⟨n₀, mem_normalizer_of_realizes h₀ fun v => ⟨_, hn₀ v⟩, fun v => ?_⟩
  rw [hn₀ v, ← hθ v]
  congr 1
  have h3 := hαθ (Multiplicative.toAdd v)
  rw [ofAdd_toAdd, hα₀] at h3
  exact h3.symm

theorem exists_conj_eq_of_conj (h₀ : IsSignedCoords A₀ c₀) (h : IsSignedCoords A c)
    (hA : ∃ g : Y, A = A₀.map (MulAut.conj g).toMonoidHom) :
    ∃ n : Y, ∀ v, c v = n * c₀ v * n⁻¹ := by
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨n', -, hn'⟩ := exists_conj_eq (h₀.conj g) h
  refine ⟨n' * g, fun v => ?_⟩
  rw [hn' v]
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_conj_eq_point (h : IsSignedCoords A c) {x : Y} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ g : Y, g * x * g⁻¹ = c (Multiplicative.ofAdd ![1, 0, 0]) ∨
      g * x * g⁻¹ = c (Multiplicative.ofAdd ![1, 1, 0]) ∨
      g * x * g⁻¹ = c (Multiplicative.ofAdd ![1, 1, 1]) := by
  rw [← h.2.1] at hx
  obtain ⟨v, rfl⟩ := hx
  have hv : Multiplicative.toAdd v ≠ 0 := by
    intro h0
    apply hx1
    have : v = 1 := Multiplicative.toAdd.injective h0
    rw [this, map_one]
  obtain ⟨σ, ε, hε, hshape⟩ := exists_signedPerm_eq_point (Multiplicative.toAdd v) hv
  obtain ⟨n, hn⟩ := h.2.2.2 σ ε hε
  have key : ∀ w : Fin 3 → ZMod 3, (∀ i, Multiplicative.toAdd v i = ε i * w (σ i)) →
      n⁻¹ * c v * n⁻¹⁻¹ = c (Multiplicative.ofAdd w) := by
    intro w hw
    have h1 := hn (Multiplicative.ofAdd w)
    have h2 : (Multiplicative.ofAdd fun i => ε i *
        Multiplicative.toAdd (Multiplicative.ofAdd w) (σ i)) = v := by
      apply Multiplicative.toAdd.injective
      funext i
      simp [hw i]
    rw [h2] at h1
    rw [← h1]
    group
  refine ⟨n⁻¹, ?_⟩
  rcases hshape with hs | hs | hs
  · exact Or.inl (key _ hs)
  · exact Or.inr (Or.inl (key _ hs))
  · exact Or.inr (Or.inr (key _ hs))

theorem forall_centralizer_of_points (h : IsSignedCoords A c) {P : Subgroup Y → Prop}
    (hP : ∀ (g : Y) (H : Subgroup Y), P H → P (H.map (MulAut.conj g).toMonoidHom))
    (h₁ : P (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 0, 0])} : Set Y)))
    (h₂ : P (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, 0])} : Set Y)))
    (h₃ : P (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, 1])} : Set Y))) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → P (Subgroup.centralizer (X : Set Y)) := by
  intro X hXA hX3
  have hXne : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hX3
    norm_num at hX3
  obtain ⟨x, hxX, hx1⟩ := (Subgroup.bot_or_exists_ne_one X).resolve_left hXne
  rw [Coords.centralizer_eq_of_card_eq_three hX3 hxX hx1]
  obtain ⟨g, hg⟩ := exists_conj_eq_point h (hXA hxX) hx1
  have hx : ∀ y : Y, g * x * g⁻¹ = y → Subgroup.centralizer ({x} : Set Y) =
      (Subgroup.centralizer ({y} : Set Y)).map (MulAut.conj g⁻¹).toMonoidHom := by
    intro y hy
    exact Coords.centralizer_singleton_eq_map_conj (by rw [← hy]; group)
  rcases hg with hg | hg | hg
  · rw [hx _ hg]
    exact hP _ _ h₁
  · rw [hx _ hg]
    exact hP _ _ h₂
  · rw [hx _ hg]
    exact hP _ _ h₃

theorem le_pRank_centralizer_of_points [Finite Y] {r m : ℕ} (hr : 1 < r)
    (h : IsSignedCoords A c)
    (h₁ : m ≤ CFSG.Open.pRank r
      (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 0, 0])} : Set Y)))
    (h₂ : m ≤ CFSG.Open.pRank r
      (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, 0])} : Set Y)))
    (h₃ : m ≤ CFSG.Open.pRank r
      (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, 1])} : Set Y))) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      m ≤ CFSG.Open.pRank r (Subgroup.centralizer (X : Set Y)) :=
  forall_centralizer_of_points h (P := fun H => m ≤ CFSG.Open.pRank r H)
    (fun g H hH => by rw [Coords.pRank_map_conj hr]; exact hH) h₁ h₂ h₃

theorem dvd_card_centralizer_of_points {r : ℕ} (h : IsSignedCoords A c)
    (h₁ : r ∣ Nat.card (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 0, 0])} : Set Y)))
    (h₂ : r ∣ Nat.card (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, 0])} : Set Y)))
    (h₃ : r ∣ Nat.card (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, 1])} : Set Y))) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → r ∣ Nat.card (Subgroup.centralizer (X : Set Y)) :=
  forall_centralizer_of_points h (P := fun H => r ∣ Nat.card H)
    (fun g H hH => by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hH)
    h₁ h₂ h₃

theorem exists_conj_eq_of_model {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 3 → ZMod 3) →* H} (h₀ : IsSignedCoords A₀ c₀)
    (N : Subgroup H) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N))
    (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} {c : Multiplicative (Fin 3 → ZMod 3) →* Y} (h : IsSignedCoords A c) :
    ∃ g : H ⧸ N, ∀ v, e (QuotientGroup.mk' Z (c v)) =
      g * QuotientGroup.mk' N (c₀ v) * g⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc' := (h.map_quotient Z hZ).map_mulEquiv e
  have hc₀' := h₀.map_quotient N hN
  obtain ⟨g, hg⟩ := UniqueElemSylow.exists_conj_eq hU hc₀'.isElemAbelian
    (by rw [hc₀'.card_eq]; norm_num) hc'.isElemAbelian (by rw [hc'.card_eq]; norm_num)
  obtain ⟨n, hn⟩ := exists_conj_eq_of_conj hc₀' hc' ⟨g, hg⟩
  exact ⟨n, hn⟩

theorem exists_centralizer_eq_of_model {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 3 → ZMod 3) →* H} (h₀ : IsSignedCoords A₀ c₀)
    (N : Subgroup H) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N))
    (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} {c : Multiplicative (Fin 3 → ZMod 3) →* Y} (h : IsSignedCoords A c)
    (S : Set (Multiplicative (Fin 3 → ZMod 3))) :
    ∃ g : H ⧸ N,
      Subgroup.centralizer ((fun v => e (QuotientGroup.mk' Z (c v))) '' S) =
        (Subgroup.centralizer ((fun v => QuotientGroup.mk' N (c₀ v)) '' S)).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_conj_eq_of_model h₀ N hN hU Z hZ e h
  exact ⟨g, Coords.centralizer_image_eq_map_conj _ _ g hg S⟩

end IsSignedCoords

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

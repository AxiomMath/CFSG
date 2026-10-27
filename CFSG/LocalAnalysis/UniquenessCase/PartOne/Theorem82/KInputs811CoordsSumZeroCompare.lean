module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsSumZero
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Compare

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open CFSG.GroupTheory K6L4

namespace IsSumZeroCoords

private theorem centralizer_image_eq_map_conj_of_sign {G : Type*} [Group G]
    (f : Multiplicative (Fin 4 → ZMod 3) → G) (f₀ : Multiplicative (Fin 4 → ZMod 3) →* G) (g : G)
    {ε : ZMod 3} (hε : ε ≠ 0)
    (h : ∀ v, f v = g * f₀ (Multiplicative.ofAdd fun i => ε * Multiplicative.toAdd v i) * g⁻¹)
    (S : Set (Multiplicative (Fin 4 → ZMod 3))) :
    Subgroup.centralizer (f '' S) =
      (Subgroup.centralizer (f₀ '' S)).map (MulAut.conj g).toMonoidHom := by
  have hε3 : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = -1 := by decide
  rcases hε3 ε hε with rfl | rfl
  · refine Coords.centralizer_image_eq_map_conj f f₀ g (fun v => ?_) S
    have hv : (Multiplicative.ofAdd fun i => (1 : ZMod 3) * Multiplicative.toAdd v i) = v := by
      apply Multiplicative.toAdd.injective
      funext i
      simp
    rw [h v, hv]
  · have h' : ∀ v, f v = g * (f₀ v)⁻¹ * g⁻¹ := fun v => by
      have hv : (Multiplicative.ofAdd fun i => (-1 : ZMod 3) * Multiplicative.toAdd v i) =
          v⁻¹ := by
        apply Multiplicative.toAdd.injective
        funext i
        show (-1 : ZMod 3) * Multiplicative.toAdd v i = -Multiplicative.toAdd v i
        exact neg_one_mul _
      rw [h v, hv, show f₀ v⁻¹ = (f₀ v)⁻¹ from map_inv f₀ v]
    rw [Coords.centralizer_image_eq_map_conj f (fun v => (f₀ v)⁻¹) g h' S,
      Coords.centralizer_image_inv_eq f₀ S]

private theorem centralizer_sign_eq {Y : Type} [Group Y]
    (c : Multiplicative (Fin 4 → ZMod 3) →* Y) {ε : ZMod 3} (hε : ε ≠ 0)
    (a : Fin 4 → ZMod 3) :
    Subgroup.centralizer ({c (Multiplicative.ofAdd fun i => ε * a i)} : Set Y) =
      Subgroup.centralizer ({c (Multiplicative.ofAdd a)} : Set Y) := by
  have hε3 : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = -1 := by decide
  rcases hε3 ε hε with rfl | rfl
  · simp only [one_mul]
  · have hv : (Multiplicative.ofAdd fun i => (-1 : ZMod 3) * a i) =
        (Multiplicative.ofAdd a)⁻¹ := by
      apply Multiplicative.toAdd.injective
      funext i
      show (-1 : ZMod 3) * a i = -a i
      exact neg_one_mul _
    rw [hv, show c (Multiplicative.ofAdd a)⁻¹ = (c (Multiplicative.ofAdd a))⁻¹ from map_inv c _,
      Coords.centralizer_singleton_inv_eq]

variable {Y : Type} [Group Y] [Finite Y] {A A₀ : Subgroup Y}
  {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}

theorem exists_conj_eq (h₀ : IsSumZeroCoords A c₀) (h : IsSumZeroCoords A c) :
    ∃ n ∈ Subgroup.normalizer (A : Set Y), ∃ ε : ZMod 3, ε ≠ 0 ∧
      ∀ v, c v = n * c₀ (Multiplicative.ofAdd fun i => ε * Multiplicative.toAdd v i) * n⁻¹ := by
  obtain ⟨ε, τ, hε, hcv⟩ := compare_coords h h₀.1 h₀.2.1 h₀.2.2.1
  obtain ⟨n, hn⟩ := h₀.2.2.2 τ
  refine ⟨n, ?_, ε, hε, fun v => ?_⟩
  · refine Coords.mem_normalizer_of_conj_mem fun a ha => ?_
    rw [← h₀.1] at ha ⊢
    obtain ⟨w, rfl⟩ := ha
    rw [hn w]
    exact ⟨_, rfl⟩
  · refine (hcv v).trans ?_
    exact (hn (Multiplicative.ofAdd fun i => ε * Multiplicative.toAdd v i)).symm

theorem exists_conj_eq_of_conj (h₀ : IsSumZeroCoords A₀ c₀) (h : IsSumZeroCoords A c)
    (hA : ∃ g : Y, A = A₀.map (MulAut.conj g).toMonoidHom) :
    ∃ (n : Y) (ε : ZMod 3), ε ≠ 0 ∧
      ∀ v, c v = n * c₀ (Multiplicative.ofAdd fun i => ε * Multiplicative.toAdd v i) * n⁻¹ := by
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨n', -, ε, hε, hn'⟩ := exists_conj_eq (h₀.conj g) h
  refine ⟨n' * g, ε, hε, fun v => ?_⟩
  rw [hn' v]
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_conj_eq_point (h : IsSumZeroCoords A c) {x : Y} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ (g : Y) (a : Fin 4 → ZMod 3) (ε : ZMod 3), ε ≠ 0 ∧
      (a = ![1, 1, -1, -1] ∨ a = ![1, -1, 0, 0] ∨ a = ![1, 1, 1, 0]) ∧
      g * x * g⁻¹ = c (Multiplicative.ofAdd fun i => ε * a i) := by
  rw [← h.1] at hx
  obtain ⟨v, rfl⟩ := hx
  have hnc : ¬ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t := fun ht =>
    hx1 ((h.2.1 v).mpr ht)
  obtain ⟨ε, σ, t, hε, hshape⟩ := point_classes (Multiplicative.toAdd v) hnc
  obtain ⟨n, hn⟩ := h.2.2.2 σ
  have hconst : c (Multiplicative.ofAdd fun _ => t) = 1 := (h.2.1 _).mpr ⟨t, rfl⟩
  have key : ∀ a : Fin 4 → ZMod 3, (∀ i, Multiplicative.toAdd v i = ε * a (σ i) + t) →
      n⁻¹ * c v * n⁻¹⁻¹ = c (Multiplicative.ofAdd fun i => ε * a i) := by
    intro a ha
    have h1 := hn (Multiplicative.ofAdd fun i => ε * a i)
    have h2 : v = (Multiplicative.ofAdd fun i => ε * a (σ i)) *
        Multiplicative.ofAdd (fun _ => t) := by
      apply Multiplicative.toAdd.injective
      funext i
      simp [ha i]
    have h3 : c (Multiplicative.ofAdd fun i => ε * a (σ i)) =
        n * c (Multiplicative.ofAdd fun i => ε * a i) * n⁻¹ := h1.symm
    rw [h2, map_mul, hconst, mul_one, h3]
    group
  rcases hshape with hs | hs | hs
  · exact ⟨n⁻¹, ![1, 1, -1, -1], ε, hε, Or.inl rfl, key _ hs⟩
  · exact ⟨n⁻¹, ![1, -1, 0, 0], ε, hε, Or.inr (Or.inl rfl), key _ hs⟩
  · exact ⟨n⁻¹, ![1, 1, 1, 0], ε, hε, Or.inr (Or.inr rfl), key _ hs⟩

theorem forall_centralizer_of_points (h : IsSumZeroCoords A c) {P : Subgroup Y → Prop}
    (hP : ∀ (g : Y) (H : Subgroup Y), P H → P (H.map (MulAut.conj g).toMonoidHom))
    (h₁ : P (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, -1, -1])} : Set Y)))
    (h₂ : P (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, -1, 0, 0])} : Set Y)))
    (h₃ : P (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, 1, 0])} : Set Y))) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → P (Subgroup.centralizer (X : Set Y)) := by
  intro X hXA hX3
  have hXne : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hX3
    norm_num at hX3
  obtain ⟨x, hxX, hx1⟩ := (Subgroup.bot_or_exists_ne_one X).resolve_left hXne
  rw [Coords.centralizer_eq_of_card_eq_three hX3 hxX hx1]
  obtain ⟨g, a, ε, hε, ha, hg⟩ := exists_conj_eq_point h (hXA hxX) hx1
  have hx : Subgroup.centralizer ({x} : Set Y) =
      (Subgroup.centralizer ({c (Multiplicative.ofAdd a)} : Set Y)).map
        (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← centralizer_sign_eq c hε a]
    exact Coords.centralizer_singleton_eq_map_conj (by rw [← hg]; group)
  rw [hx]
  rcases ha with rfl | rfl | rfl
  · exact hP _ _ h₁
  · exact hP _ _ h₂
  · exact hP _ _ h₃

theorem le_pRank_centralizer_of_points {r m : ℕ} (hr : 1 < r) (h : IsSumZeroCoords A c)
    (h₁ : m ≤ CFSG.Open.pRank r
      (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, -1, -1])} : Set Y)))
    (h₂ : m ≤ CFSG.Open.pRank r
      (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, -1, 0, 0])} : Set Y)))
    (h₃ : m ≤ CFSG.Open.pRank r
      (Subgroup.centralizer ({c (Multiplicative.ofAdd ![1, 1, 1, 0])} : Set Y))) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      m ≤ CFSG.Open.pRank r (Subgroup.centralizer (X : Set Y)) :=
  forall_centralizer_of_points h (P := fun H => m ≤ CFSG.Open.pRank r H)
    (fun g H hH => by rw [Coords.pRank_map_conj hr]; exact hH) h₁ h₂ h₃

theorem exists_conj_eq_of_model {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 4 → ZMod 3) →* H} (h₀ : IsSumZeroCoords A₀ c₀)
    (N : Subgroup H) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N))
    (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} {c : Multiplicative (Fin 4 → ZMod 3) →* Y} (h : IsSumZeroCoords A c) :
    ∃ (g : H ⧸ N) (ε : ZMod 3), ε ≠ 0 ∧ ∀ v, e (QuotientGroup.mk' Z (c v)) =
      g * QuotientGroup.mk' N (c₀ (Multiplicative.ofAdd fun i => ε * Multiplicative.toAdd v i)) *
        g⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc' := (h.map_quotient Z hZ).map_mulEquiv e
  have hc₀' := h₀.map_quotient N hN
  obtain ⟨g, hg⟩ := UniqueElemSylow.exists_conj_eq hU hc₀'.isElemAbelian
    (by rw [hc₀'.card_eq]; norm_num) hc'.isElemAbelian (by rw [hc'.card_eq]; norm_num)
  obtain ⟨n, ε, hε, hn⟩ := exists_conj_eq_of_conj hc₀' hc' ⟨g, hg⟩
  exact ⟨n, ε, hε, hn⟩

theorem exists_centralizer_eq_of_model {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 4 → ZMod 3) →* H} (h₀ : IsSumZeroCoords A₀ c₀)
    (N : Subgroup H) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N))
    (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} {c : Multiplicative (Fin 4 → ZMod 3) →* Y} (h : IsSumZeroCoords A c)
    (S : Set (Multiplicative (Fin 4 → ZMod 3))) :
    ∃ g : H ⧸ N,
      Subgroup.centralizer ((fun v => e (QuotientGroup.mk' Z (c v))) '' S) =
        (Subgroup.centralizer ((fun v => QuotientGroup.mk' N (c₀ v)) '' S)).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, ε, hε, hg⟩ := exists_conj_eq_of_model h₀ N hN hU Z hZ e h
  exact ⟨g, centralizer_image_eq_map_conj_of_sign (fun v => e (QuotientGroup.mk' Z (c v)))
    ((QuotientGroup.mk' N).comp c₀) g hε hg S⟩

theorem le_pRank_centralizer_image_of_model {H Y : Type} [Group H] [Finite H] [Group Y]
    [Finite Y] {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 4 → ZMod 3) →* H}
    (h₀ : IsSumZeroCoords A₀ c₀) (N : Subgroup H) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* H ⧸ N) {A : Subgroup Y} {c : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (h : IsSumZeroCoords A c) (S : Set (Multiplicative (Fin 4 → ZMod 3))) {p m : ℕ} (hp : 1 < p)
    (hm : m ≤ CFSG.Open.pRank p
      (Subgroup.centralizer ((fun v => QuotientGroup.mk' N (c₀ v)) '' S))) :
    m ≤ CFSG.Open.pRank p
      (Subgroup.centralizer ((fun v => e (QuotientGroup.mk' Z (c v))) '' S)) := by
  obtain ⟨g, hg⟩ := exists_centralizer_eq_of_model h₀ N hN hU Z hZ e h S
  rw [hg, Coords.pRank_map_conj hp]
  exact hm

end IsSumZeroCoords

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

module

public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofDiag
public import CFSG.LieType.SeitzGeneration.HeisTorusUDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open Matrix
open CFSG.RankThree.PartTwo.Sec15.KSL3Two (IsMonomialWith)
open CFSG.LieType.SeitzGeneration (IsCoordBlockOn)

namespace SL3G

section Matrices

variable {K : Type} [Field K]

@[expose] def ActsAs {G : Type*} [Group G] (ι : G →* GL (Fin 3) K) (α : MulAut G) (σ : K ≃+* K)
    (B : GL (Fin 3) K) : Prop :=
  ∀ g : G, ((ι (α g) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    (B : Matrix (Fin 3) (Fin 3) K) * ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ *
      ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

@[expose] def IsFrame (T Q : Subgroup (GL (Fin 3) K)) (u θ : GL (Fin 3) K) (ε : Fin 3 → K) : Prop :=
  ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ε ∧ Function.Injective ε ∧
  (∃ j, ε j = 1) ∧
  (∀ x ∈ Q, ((θ⁻¹ * x * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) ∧
  (∀ s ∈ T, ∃ τ : Fin 3 → Fin 3,
    IsMonomialWith ((θ⁻¹ * s * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ)

private theorem isMonomialWith_pow_iterate {M : Matrix (Fin 3) (Fin 3) K} {τ : Fin 3 → Fin 3}
    (h : IsMonomialWith M τ) (m : ℕ) : IsMonomialWith (M ^ m) (τ^[m]) := by
  induction m with
  | zero =>
    simpa using CFSG.RankThree.PartTwo.Sec15.KSL3Two.isMonomialWith_smul_one
      (L := K) (c := 1) one_ne_zero
  | succ m ih =>
    rw [pow_succ, Function.iterate_succ]
    exact ih.mul h

private theorem cube_of_iterate_pow_eq_id {τ : Fin 3 → Fin 3} {n : ℕ}
    (hid : τ^[3 ^ n] = id) : τ ∘ τ ∘ τ = id := by
  have hinj : Function.Injective τ := by
    have hpos : 0 < 3 ^ n := pow_pos (by norm_num) n
    have : τ^[3 ^ n] = τ^[3 ^ n - 1] ∘ τ := by
      rw [← Function.iterate_succ]
      congr 1
      omega
    rw [this] at hid
    exact Function.Injective.of_comp (f := τ^[3 ^ n - 1])
      (by rw [hid]; exact Function.injective_id)
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj)
  have he : e ^ 3 ^ n = 1 := by
    ext x
    simp [e, Equiv.Perm.coe_pow, hid]
  have hord : orderOf e ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one he
  have hord6 : orderOf e ∣ 6 := by
    have := orderOf_dvd_card (x := e)
    simpa [Fintype.card_perm, Nat.factorial] using this
  obtain ⟨j, hj, hej⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 hj2
    have h96 : 9 ∣ 6 := by
      have := this.trans (hej ▸ hord6)
      simpa using this
    omega
  have he3 : e ^ 3 = 1 := by
    interval_cases j
    · have : orderOf e = 1 := by simpa using hej
      rw [orderOf_eq_one_iff] at this
      rw [this]; simp
    · have h3 : orderOf e = 3 := by simpa using hej
      calc e ^ 3 = e ^ orderOf e := by rw [h3]
        _ = 1 := pow_orderOf_eq_one e
  funext x
  have := congrArg (fun f : Equiv.Perm (Fin 3) => f x) he3
  simpa [e, pow_succ] using this

theorem monomial_perm_cube {G : Type*} [Group G] (ι : G →* GL (Fin 3) K) {T : Subgroup G}
    (hT : IsPGroup 3 T) {s : G} (hs : s ∈ T) {τ : Fin 3 → Fin 3}
    (hτ : IsMonomialWith ((ι s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ) :
    τ ∘ τ ∘ τ = id := by
  obtain ⟨n, hn⟩ := hT ⟨s, hs⟩
  have hsn : s ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 : IsMonomialWith (1 : Matrix (Fin 3) (Fin 3) K) (τ^[3 ^ n]) := by
    have := isMonomialWith_pow_iterate hτ (3 ^ n)
    rwa [← Units.val_pow_eq_pow_val, ← map_pow, hsn, map_one, Units.val_one] at this
  have h2 : IsMonomialWith (1 : Matrix (Fin 3) (Fin 3) K) id := by
    simpa using CFSG.RankThree.PartTwo.Sec15.KSL3Two.isMonomialWith_smul_one
      (L := K) (c := 1) one_ne_zero
  exact cube_of_iterate_pow_eq_id (h1.unique h2)

private theorem fixfree_of_cube : ∀ τ : Fin 3 → Fin 3, τ ∘ τ ∘ τ = id → τ ≠ id →
    ∀ j, τ j ≠ j := by
  decide

private theorem mul_diagonal_of_conj_eq {t B : GL (Fin 3) K} {ε : Fin 3 → K}
    (hu : ((t * B * t⁻¹ * B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ε) :
    (t : Matrix (Fin 3) (Fin 3) K) * B =
      diagonal ε * (B : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K) := by
  have hu' : (t : Matrix (Fin 3) (Fin 3) K) * B *
      ((t⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ε := by
    simpa only [Units.val_mul] using hu
  have e : (t * B * t⁻¹ * B⁻¹ : GL (Fin 3) K) * B * t = t * B := by group
  have h := congrArg Units.val e
  simp only [Units.val_mul] at h
  rw [hu'] at h
  exact h.symm

private theorem entries_eq_of_mul_eq {t B : GL (Fin 3) K} {τ : Fin 3 → Fin 3}
    (ht : IsMonomialWith (t : Matrix (Fin 3) (Fin 3) K) τ)
    (hB : (B : Matrix (Fin 3) (Fin 3) K).IsDiag) {ε : Fin 3 → K}
    (h1 : (t : Matrix (Fin 3) (Fin 3) K) * B =
      diagonal ε * (B : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K)) :
    ∀ i, (B : Matrix (Fin 3) (Fin 3) K) i i =
      ε (τ i) * (B : Matrix (Fin 3) (Fin 3) K) (τ i) (τ i) := by
  intro i
  have h2 := congrFun (congrFun h1 (τ i)) i
  rw [Matrix.mul_apply, Matrix.mul_apply] at h2
  have e1 : ∑ k, (t : Matrix (Fin 3) (Fin 3) K) (τ i) k *
      (B : Matrix (Fin 3) (Fin 3) K) k i =
      (t : Matrix (Fin 3) (Fin 3) K) (τ i) i * (B : Matrix (Fin 3) (Fin 3) K) i i := by
    rw [Finset.sum_eq_single i]
    · intro k _ hk
      rw [hB hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have e2 : ∑ k, ((diagonal ε * (B : Matrix (Fin 3) (Fin 3) K)) (τ i) k) *
      (t : Matrix (Fin 3) (Fin 3) K) k i =
      ((diagonal ε * (B : Matrix (Fin 3) (Fin 3) K)) (τ i) (τ i)) *
        (t : Matrix (Fin 3) (Fin 3) K) (τ i) i := by
    rw [Finset.sum_eq_single (τ i)]
    · intro k _ hk
      have : (t : Matrix (Fin 3) (Fin 3) K) k i = 0 := by
        by_contra h0
        exact hk ((ht i k).mp h0)
      rw [this, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have e3 : (diagonal ε * (B : Matrix (Fin 3) (Fin 3) K)) (τ i) (τ i) =
      ε (τ i) * (B : Matrix (Fin 3) (Fin 3) K) (τ i) (τ i) := by
    rw [Matrix.diagonal_mul]
  rw [e1, e2, e3] at h2
  have hti : (t : Matrix (Fin 3) (Fin 3) K) (τ i) i ≠ 0 := (ht i (τ i)).mpr rfl
  apply mul_left_cancel₀ hti
  rw [h2]
  ring

theorem equal_entries {t B : GL (Fin 3) K} {τ : Fin 3 → Fin 3}
    (ht : IsMonomialWith (t : Matrix (Fin 3) (Fin 3) K) τ) (hτ : τ ∘ τ ∘ τ = id)
    (hB : (B : Matrix (Fin 3) (Fin 3) K).IsDiag) {ε : Fin 3 → K}
    (hu : ((t * B * t⁻¹ * B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ε)
    (hε : Function.Injective ε) (hε1 : ∃ j, ε j = 1) :
    τ ≠ id ∧ ∃ i j : Fin 3, i ≠ j ∧
      (B : Matrix (Fin 3) (Fin 3) K) i i = (B : Matrix (Fin 3) (Fin 3) K) j j := by
  have hBne : ∀ i, (B : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    have hdet : (B : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      (B.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
    rw [← hB.diagonal_diag, Matrix.det_diagonal] at hdet
    intro i
    exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
  have hrel := entries_eq_of_mul_eq ht hB (mul_diagonal_of_conj_eq hu)
  have hne : τ ≠ id := by
    intro hid
    subst hid
    have hall : ∀ i, ε i = 1 := by
      intro i
      have h := hrel i
      simp only [id_eq] at h
      have h' : (1 : K) * (B : Matrix (Fin 3) (Fin 3) K) i i =
          ε i * (B : Matrix (Fin 3) (Fin 3) K) i i := by rw [one_mul]; exact h
      exact (mul_right_cancel₀ (hBne i) h').symm
    have : ε 0 = ε 1 := by rw [hall 0, hall 1]
    exact absurd (hε this) (by decide)
  refine ⟨hne, ?_⟩
  obtain ⟨j, hj⟩ := hε1
  have h3 : ∀ x, τ (τ (τ x)) = x := fun x => congrFun hτ x
  refine ⟨τ (τ j), j, ?_, ?_⟩
  · intro h
    have h' : τ j = j := by
      have e := h3 j
      rw [h] at e
      exact e
    exact fixfree_of_cube τ hτ hne j h'
  · have := hrel (τ (τ j))
    rw [h3 j, hj, one_mul] at this
    exact this

theorem plane_central {B : Matrix (Fin 3) (Fin 3) K} (hB : B.IsDiag) {a b : Fin 3}
    (hab : B a a = B b b) {g : Matrix (Fin 3) (Fin 3) K} (hg : IsCoordBlockOn a b g) :
    g * B = B * g := by
  obtain ⟨d, rfl⟩ : ∃ d, B = diagonal d := ⟨B.diag, hB.diagonal_diag.symm⟩
  simp only [diagonal_apply_eq] at hab
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hpq : p = q
  · subst hpq
    exact mul_comm _ _
  · by_cases hp : p = a ∨ p = b
    · by_cases hq : q = a ∨ q = b
      · rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        · exact absurd rfl hpq
        · rw [hab]; exact mul_comm _ _
        · rw [hab]; exact mul_comm _ _
        · exact absurd rfl hpq
      · have := hg p q (Or.inr ⟨fun h => hq (Or.inl h), fun h => hq (Or.inr h)⟩)
        rw [this, if_neg hpq]
        simp
    · have := hg p q (Or.inl ⟨fun h => hp (Or.inl h), fun h => hp (Or.inr h)⟩)
      rw [this, if_neg hpq]
      simp

private theorem monomial_mul_entry {t : GL (Fin 3) K} {τ : Fin 3 → Fin 3}
    (ht : IsMonomialWith (t : Matrix (Fin 3) (Fin 3) K) τ) (hτ : Function.Injective τ)
    {g X : Matrix (Fin 3) (Fin 3) K}
    (hX : (t : Matrix (Fin 3) (Fin 3) K) * X = g * (t : Matrix (Fin 3) (Fin 3) K)) :
    ∀ i j, (t : Matrix (Fin 3) (Fin 3) K) (τ i) i * X i j =
      g (τ i) (τ j) * (t : Matrix (Fin 3) (Fin 3) K) (τ j) j := by
  intro i j
  have h1 := congrFun (congrFun hX (τ i)) j
  have e1 : ∑ k, (t : Matrix (Fin 3) (Fin 3) K) (τ i) k * X k j =
      (t : Matrix (Fin 3) (Fin 3) K) (τ i) i * X i j := by
    rw [Finset.sum_eq_single i]
    · intro k _ hk
      have : (t : Matrix (Fin 3) (Fin 3) K) (τ i) k = 0 := by
        by_contra h0
        exact hk (hτ ((ht k (τ i)).mp h0)).symm
      rw [this, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have e2 : ∑ l, g (τ i) l * (t : Matrix (Fin 3) (Fin 3) K) l j =
      g (τ i) (τ j) * (t : Matrix (Fin 3) (Fin 3) K) (τ j) j := by
    rw [Finset.sum_eq_single (τ j)]
    · intro l _ hl
      have : (t : Matrix (Fin 3) (Fin 3) K) l j = 0 := by
        by_contra h0
        exact hl ((ht j l).mp h0)
      rw [this, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply, Matrix.mul_apply, e1, e2] at h1
  exact h1

private theorem isCoordBlockOn_conj {t : GL (Fin 3) K} {τ : Fin 3 → Fin 3}
    (ht : IsMonomialWith (t : Matrix (Fin 3) (Fin 3) K) τ) (hτ : Function.Injective τ)
    {a b : Fin 3} {g : Matrix (Fin 3) (Fin 3) K} (hg : IsCoordBlockOn (τ a) (τ b) g) :
    IsCoordBlockOn a b (((t⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g *
      (t : Matrix (Fin 3) (Fin 3) K)) := by
  set X : Matrix (Fin 3) (Fin 3) K := ((t⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g *
    (t : Matrix (Fin 3) (Fin 3) K) with hX
  have htX : (t : Matrix (Fin 3) (Fin 3) K) * X = g * (t : Matrix (Fin 3) (Fin 3) K) := by
    rw [hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have hent := monomial_mul_entry ht hτ htX
  intro i j hij
  have hti : (t : Matrix (Fin 3) (Fin 3) K) (τ i) i ≠ 0 := (ht i (τ i)).mpr rfl
  have hgij : g (τ i) (τ j) = if i = j then 1 else 0 := by
    rw [hg (τ i) (τ j) ?_]
    · simp [hτ.eq_iff]
    · rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨fun h => h1 (hτ h), fun h => h2 (hτ h)⟩
      · exact Or.inr ⟨fun h => h1 (hτ h), fun h => h2 (hτ h)⟩
  have h := hent i j
  rw [hgij] at h
  by_cases hij' : i = j
  · subst hij'
    simp only [if_true, one_mul] at h ⊢
    exact mul_left_cancel₀ hti (by rw [h, mul_one])
  · simp only [if_neg hij', zero_mul] at h ⊢
    exact (mul_eq_zero.mp h).resolve_left hti

private theorem plane_cover : ∀ τ : Fin 3 → Fin 3, τ ∘ τ ∘ τ = id → τ ≠ id →
    ∀ a b c d : Fin 3, a ≠ b → c ≠ d →
      (c = a ∧ d = b) ∨ (c = b ∧ d = a) ∨ (c = τ a ∧ d = τ b) ∨ (c = τ b ∧ d = τ a) ∨
      (c = τ (τ a) ∧ d = τ (τ b)) ∨ (c = τ (τ b) ∧ d = τ (τ a)) := by
  decide

private theorem plane_mem_conj {G : Type*} [Group G] (ι : G →* GL (Fin 3) K) (H : Subgroup G)
    {t : G} (ht : t ∈ H) {τ : Fin 3 → Fin 3} (hτ : Function.Injective τ) {x y : Fin 3}
    (hτm : IsMonomialWith ((ι t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ)
    (hxy : ∀ g : G, IsCoordBlockOn x y ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
      g ∈ H) :
    ∀ g : G, IsCoordBlockOn (τ x) (τ y) ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
      g ∈ H := by
  intro g hg
  have hconj : IsCoordBlockOn x y
      ((ι (t⁻¹ * g * t) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have := isCoordBlockOn_conj hτm hτ (a := x) (b := y) hg
    simp only [map_mul, map_inv, Units.val_mul]
    exact this
  have hmem := hxy _ hconj
  have hg' : g = t * (t⁻¹ * g * t) * t⁻¹ := by group
  rw [hg']
  exact H.mul_mem (H.mul_mem ht hmem) (H.inv_mem ht)

theorem planes_of_cycle {G : Type*} [Group G] (ι : G →* GL (Fin 3) K) (H : Subgroup G) {t : G}
    (ht : t ∈ H) {τ : Fin 3 → Fin 3}
    (hτ : IsMonomialWith ((ι t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ)
    (hτ3 : τ ∘ τ ∘ τ = id) (hτ1 : τ ≠ id) {a b : Fin 3} (hab : a ≠ b)
    (hplane : ∀ g : G, IsCoordBlockOn a b ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
      g ∈ H) :
    ∀ c d : Fin 3, c ≠ d → ∀ g : G,
      IsCoordBlockOn c d ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ H := by
  have h3 : ∀ x, τ (τ (τ x)) = x := fun x => congrFun hτ3 x
  have hinj : Function.Injective τ := fun x y hxy => by
    have := congrArg (fun z => τ (τ z)) hxy
    simp only [h3] at this
    exact this
  have symm : ∀ (x y : Fin 3) (g : Matrix (Fin 3) (Fin 3) K),
      IsCoordBlockOn x y g → IsCoordBlockOn y x g := by
    intro x y g hg i j hij
    apply hg i j
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  have hP1 := plane_mem_conj ι H ht hinj hτ hplane
  have hP2 := plane_mem_conj ι H ht hinj hτ hP1
  intro c d hcd g hg
  rcases plane_cover τ hτ3 hτ1 a b c d hab hcd with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1 h2
    exact hplane g hg
  · subst h1 h2
    exact hplane g (symm _ _ _ hg)
  · subst h1 h2
    exact hP1 g hg
  · subst h1 h2
    exact hP1 g (symm _ _ _ hg)
  · subst h1 h2
    exact hP2 g hg
  · subst h1 h2
    exact hP2 g (symm _ _ _ hg)

theorem isCoordBlockOn_transvection {i j : Fin 3} (hij : i ≠ j) (c : K) :
    IsCoordBlockOn i j ((SpecialLinearGroup.transvection hij c :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  intro p q hpq
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply_of_ne]
  · simp [Matrix.one_apply]
  · rintro ⟨rfl, rfl⟩
    rcases hpq with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1 rfl
    · exact h2 rfl

theorem center_of_scalar {G : Type*} [Group G] {ι : G →* GL (Fin 3) K}
    (hι : Function.Injective ι) {g : G} {c : K}
    (hg : ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply hι
  rw [map_mul, map_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg]
  simp [Matrix.mul_smul, Matrix.smul_mul]

end Matrices

section Diag

variable {G : Type*} [Group G] {K : Type} [Field K]

@[expose] def diagSub (ι : G →* GL (Fin 3) K) : Subgroup G where
  carrier := {x | ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Units.val_mul] at hx hy ⊢
    rw [← hx.diagonal_diag, ← hy.diagonal_diag, Matrix.diagonal_mul_diagonal]
    exact isDiag_diagonal _
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, Units.val_one]
    exact isDiag_one
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, map_inv] at hx ⊢
    rw [Matrix.coe_units_inv, ← hx.diagonal_diag, Matrix.inv_diagonal]
    exact isDiag_diagonal _

theorem mem_diagSub {ι : G →* GL (Fin 3) K} {x : G} :
    x ∈ diagSub ι ↔ ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := Iff.rfl

theorem diagSub_comm {ι : G →* GL (Fin 3) K} (hι : Function.Injective ι) {x y : G}
    (hx : x ∈ diagSub ι) (hy : y ∈ diagSub ι) : x * y = y * x := by
  apply hι
  apply Units.ext
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  exact CFSG.RankThree.PartTwo.Sec15.KSL3Two.commute_of_isDiag (mem_diagSub.mp hx)
    (mem_diagSub.mp hy)

theorem isDiag_conj_of_monomial {s : GL (Fin 3) K} {τ : Fin 3 → Fin 3}
    (hs : IsMonomialWith (s : Matrix (Fin 3) (Fin 3) K) τ) (hτ : τ ∘ τ ∘ τ = id)
    {d : Matrix (Fin 3) (Fin 3) K} (hd : d.IsDiag) :
    ((s : Matrix (Fin 3) (Fin 3) K) * d *
      ((s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).IsDiag := by
  obtain ⟨e, rfl⟩ : ∃ e, d = diagonal e := ⟨d.diag, hd.diagonal_diag.symm⟩
  have h3 : ∀ x, τ (τ (τ x)) = x := fun x => congrFun hτ x
  have key : (s : Matrix (Fin 3) (Fin 3) K) * diagonal e =
      diagonal (fun j => e (τ (τ j))) * (s : Matrix (Fin 3) (Fin 3) K) := by
    ext j i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h0 : (s : Matrix (Fin 3) (Fin 3) K) j i = 0
    · rw [h0]
      simp
    · have hj : j = τ i := (hs i j).mp h0
      subst hj
      rw [h3]
      ring
  have hcalc : (s : Matrix (Fin 3) (Fin 3) K) * diagonal e *
      ((s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun j => e (τ (τ j))) := by
    rw [key, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hcalc]
  exact isDiag_diagonal _

end Diag

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

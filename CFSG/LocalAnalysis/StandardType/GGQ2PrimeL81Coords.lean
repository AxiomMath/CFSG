module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeNamed

public section

namespace CFSG.GGQ2Prime

open Subgroup

theorem one_ne_ω3 : (1 : Multiplicative (ZMod 3)) ≠ ω3 := by decide

theorem weylCoords_ext {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut Bs)} {x : G}
    {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m : Fin 7} (hW : WeylCoords Bs A x κ m)
    {b b' : Bs} (h : ∀ j, κ j b = κ j b') : b = b' := by
  have := hW.inj (b * b'⁻¹) fun j => by rw [map_mul, map_inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.1 this

theorem exists_mem_of_perm_fix {G : Type} [Group G] {Bs : Subgroup G} {A AL : Subgroup (MulAut Bs)}
    {x : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m : Fin 7} (hW : WeylCoords Bs A x κ m)
    (hle : AL ≤ A) (hfix : ∀ φ ∈ AL, φ ⟨x, hW.x_mem⟩ = ⟨x, hW.x_mem⟩)
    (hcard : Nat.card AL = 720) (τ : Equiv.Perm (Fin 7)) (hτ : τ m = m) :
    ∃ φ ∈ AL, ∀ j b, κ j (φ b) = κ (τ.symm j) b := by
  classical
  have hσ : ∀ φ : AL, ∃ σ : Equiv.Perm (Fin 7), σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) m ∧
      ∀ j b, κ j ((φ : MulAut Bs) b) = κ (σ.symm j) b := fun φ => by
    obtain ⟨σ, hσ⟩ := hW.perm φ (hle φ.2)
    refine ⟨σ, ?_, hσ⟩
    have hx := fun j => congrArg (κ j) (hfix φ φ.2)
    have key : ∀ j, (σ.symm j = m ↔ j = m) := fun j => by
      have e := hx j
      rw [hσ, hW.x_coord, hW.x_coord] at e
      by_cases h1 : σ.symm j = m <;> by_cases h2 : j = m
      · exact ⟨fun _ => h2, fun _ => h1⟩
      · rw [if_pos h1, if_neg h2] at e; exact absurd e one_ne_ω3
      · rw [if_neg h1, if_pos h2] at e; exact absurd e.symm one_ne_ω3
      · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    have := (key (σ m)).1 (by simp)
    exact this
  choose F hFst hF using hσ
  have hinj : Function.Injective fun φ : AL => (⟨F φ, hFst φ⟩ :
      MulAction.stabilizer (Equiv.Perm (Fin 7)) m) := by
    intro φ ψ h
    have hFF : F φ = F ψ := congrArg Subtype.val h
    apply Subtype.ext
    refine MulEquiv.ext fun b => weylCoords_ext hW fun j => ?_
    rw [hF, hF, hFF]
  have hfinAL : Finite AL := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hst : Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 7)) m) = 720 := by
    have h1 := (MulAction.stabilizer (Equiv.Perm (Fin 7)) m).index_mul_card
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_perm, Nat.card_fin] at h1
    have : Nat.factorial 7 = 7 * 720 := by decide
    rw [this] at h1
    omega
  have hbij : Function.Bijective fun φ : AL => (⟨F φ, hFst φ⟩ :
      MulAction.stabilizer (Equiv.Perm (Fin 7)) m) := by
    refine (Function.Injective.bijective_of_nat_card_le hinj ?_)
    rw [hst, hcard]
  obtain ⟨φ, hφ⟩ := hbij.2 ⟨τ, by rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, hτ]⟩
  refine ⟨φ, φ.2, fun j b => ?_⟩
  have : F φ = τ := congrArg Subtype.val hφ
  rw [hF, this]

theorem exists_point {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut Bs)} {x : G}
    {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m : Fin 7} (hW : WeylCoords Bs A x κ m)
    (j : Fin 7) : ∃ u : Bs, ∀ i, κ i u = if i = j then 1 else ω3 := by
  obtain ⟨φ, -, hφ⟩ := hW.onto (Equiv.swap m j)
  refine ⟨φ ⟨x, hW.x_mem⟩, fun i => ?_⟩
  rw [hφ, hW.x_coord, Equiv.symm_swap]
  by_cases hij : i = j
  · subst hij; simp
  · by_cases him : i = m
    · subst him; simp [Equiv.swap_apply_left, Ne.symm hij, hij]
    · rw [Equiv.swap_apply_of_ne_of_ne him hij]; simp [him, hij]

theorem ker_eq_of_invariant {G : Type} [Group G] {Bs : Subgroup G} {A AL : Subgroup (MulAut Bs)}
    {x : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m : Fin 7} (hW : WeylCoords Bs A x κ m)
    (hle : AL ≤ A) (hfix : ∀ φ ∈ AL, φ ⟨x, hW.x_mem⟩ = ⟨x, hW.x_mem⟩)
    (hcard : Nat.card AL = 720) {O : Type*} [Group O] (ν : Bs →* O)
    (hinv : ∀ φ ∈ AL, ∀ b, ν (φ b) = ν b) (hne : ∃ b, ν b ≠ 1) :
    ∀ b, ν b = 1 ↔ κ m b = 1 := by
  classical
  choose u hu using exists_point hW
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Fin 7, s₀ ≠ m := ⟨m + 1, by
    intro h; have := congrArg Fin.val h; revert this; fin_cases m <;> decide⟩
  have hνu : ∀ r, r ≠ m → ν (u r) = ν (u s₀) := fun r hr => by
    obtain ⟨φ, hφ, hφk⟩ := exists_mem_of_perm_fix hW hle hfix hcard (Equiv.swap r s₀)
      (Equiv.swap_apply_of_ne_of_ne (Ne.symm hr) (Ne.symm hs₀))
    have : φ (u r) = u s₀ := weylCoords_ext hW fun i => by
      rw [hφk, Equiv.symm_swap, hu, hu]
      by_cases h1 : i = s₀
      · subst h1; simp
      · by_cases h2 : i = r
        · subst h2; simp [Equiv.swap_apply_left, h1, Ne.symm h1]
        · rw [Equiv.swap_apply_of_ne_of_ne h2 h1]; simp [h1, h2]
    rw [← this, hinv φ hφ]
  set d : Fin 7 → Bs := fun r => u r * (u s₀)⁻¹ with hd
  have hνd : ∀ r, r ≠ m → ν (d r) = 1 := fun r hr => by
    rw [hd, map_mul, map_inv, hνu r hr, mul_inv_cancel]
  have hκd : ∀ r i, κ i (d r) = (if i = r then 1 else ω3) * (if i = s₀ then 1 else ω3)⁻¹ :=
    fun r i => by rw [hd, map_mul, map_inv, hu, hu]
  set T : Finset (Fin 7) := (Finset.univ.erase m).erase s₀ with hT
  have hone : ∀ n : ℕ, ∀ b : Bs, κ m b = 1 →
      (T.filter fun r => κ r b ≠ 1).card = n → ν b = 1 := by
    intro n
    induction n with
    | zero =>
      intro b hbm hN
      have hT0 : ∀ r ∈ T, κ r b = 1 := fun r hr => by
        by_contra hc
        have : r ∈ T.filter fun r => κ r b ≠ 1 := Finset.mem_filter.2 ⟨hr, hc⟩
        rw [Finset.card_eq_zero.1 hN] at this
        simp at this
      have hoff : ∀ j, j ≠ s₀ → κ j b = 1 := fun j hj => by
        by_cases hjm : j = m
        · rw [hjm]; exact hbm
        · exact hT0 j (by simp [hT, hj, hjm])
      have hs : κ s₀ b = 1 := by
        have h := hW.sum_one b
        rwa [Fintype.prod_eq_single s₀ fun j hj => hoff j hj] at h
      have : b = 1 := hW.inj b fun j => by
        by_cases hj : j = s₀
        · rw [hj]; exact hs
        · exact hoff j hj
      rw [this, map_one]
    | succ n ih =>
      intro b hbm hN
      obtain ⟨r, hr⟩ : (T.filter fun r => κ r b ≠ 1).Nonempty :=
        Finset.card_pos.1 (by rw [hN]; omega)
      have hrT := (Finset.mem_filter.1 hr).1
      have hrm : r ≠ m := by simp [hT] at hrT; exact hrT.2
      have hrs : r ≠ s₀ := by simp [hT] at hrT; exact hrT.1
      set k := (Multiplicative.toAdd (κ r b)).val with hk
      set b' := b * d r ^ k with hb'
      have hκb' : ∀ i, κ i b' = κ i b * κ i (d r) ^ k := fun i => by
        rw [hb', map_mul, map_pow]
      have hb'm : κ m b' = 1 := by
        rw [hκb', hbm, hκd]
        simp [Ne.symm hrm, Ne.symm hs₀]
      have hb'r : κ r b' = 1 := by
        rw [hκb', hκd, if_pos rfl, if_neg hrs, one_mul, inv_pow]
        apply mul_inv_eq_one.2
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow]
        simp only [ω3, toAdd_ofAdd, nsmul_eq_mul, mul_one, hk, ZMod.natCast_zmod_val]
      have hfilter : (T.filter fun r => κ r b' ≠ 1) = (T.filter fun r => κ r b ≠ 1).erase r := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hiT, hi⟩
          have hir : i ≠ r := fun h => hi (h ▸ hb'r)
          refine ⟨hir, hiT, fun h => hi ?_⟩
          have his : i ≠ s₀ := by simp [hT] at hiT; exact hiT.1
          rw [hκb', h, hκd]
          simp [hir, his]
        · rintro ⟨hir, hiT, hi⟩
          refine ⟨hiT, fun h => hi ?_⟩
          have his : i ≠ s₀ := by simp [hT] at hiT; exact hiT.1
          rw [hκb', hκd] at h
          simpa [hir, his] using h
      have hN' : (T.filter fun r => κ r b' ≠ 1).card = n := by
        rw [hfilter, Finset.card_erase_of_mem hr, hN]
        rfl
      have hνb' := ih b' hb'm hN'
      rw [hb', map_mul, map_pow, hνd r hrm, one_pow, mul_one] at hνb'
      exact hνb'
  intro b
  constructor
  · intro hνb
    by_contra hb
    obtain ⟨b₀, hb₀⟩ := hne
    apply hb₀
    set A₀ := Multiplicative.toAdd (κ m b) with hA₀
    have hA0 : A₀ ≠ 0 := fun h => hb (by rw [← ofAdd_toAdd (κ m b), ← hA₀, h, ofAdd_zero])
    set i := (Multiplicative.toAdd (κ m b₀) * A₀⁻¹).val
    have hκi : κ m (b₀ * (b ^ i)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow]
      apply mul_inv_eq_one.2
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, ← hA₀, mul_assoc, inv_mul_cancel₀ hA0,
        mul_one]
    have := hone _ _ hκi rfl
    rw [map_mul, map_inv, map_pow, hνb, one_pow, inv_one, mul_one] at this
    exact this
  · intro hbm
    exact hone _ b hbm rfl

end CFSG.GGQ2Prime

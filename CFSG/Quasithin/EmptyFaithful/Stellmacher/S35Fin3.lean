module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin1

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem commW_zpowers_top {n : ℕ} (M : Model n) (σ : Perm (Fin n)) :
    commW M (Subgroup.zpowers σ) ⊤ = Subgroup.closure {w | ∃ u, w = M.act σ u * u⁻¹} := by
  apply le_antisymm
  · unfold commW
    rw [Subgroup.closure_le]
    rintro w ⟨b, hb, u, -, rfl⟩
    have key : ∀ b ∈ Subgroup.zpowers σ, ∀ u : M.W,
        M.act b u * u⁻¹ ∈ Subgroup.closure {w | ∃ u, w = M.act σ u * u⁻¹} := by
      intro b hb
      rw [Subgroup.zpowers_eq_closure] at hb
      induction hb using Subgroup.closure_induction with
      | mem x hx =>
        intro u
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Subgroup.subset_closure ⟨u, rfl⟩
      | one => intro u; simp
      | mul x y _ _ hx hy =>
        intro u
        have h := Subgroup.mul_mem _ (hx (M.act y u)) (hy u)
        have e : M.act (x * y) u * u⁻¹ =
            M.act x (M.act y u) * (M.act y u)⁻¹ * (M.act y u * u⁻¹) := by
          rw [act_mul_apply]; group
        rw [e]; exact h
      | inv x _ hx =>
        intro u
        have h := Subgroup.inv_mem _ (hx (M.act x⁻¹ u))
        have e : M.act x⁻¹ u * u⁻¹ = (M.act x (M.act x⁻¹ u) * (M.act x⁻¹ u)⁻¹)⁻¹ := by
          rw [act_act_inv]; group
        rw [e]; exact h
    exact key b hb u
  · rw [Subgroup.closure_le]
    rintro w ⟨u, rfl⟩
    exact Subgroup.subset_closure ⟨σ, Subgroup.mem_zpowers σ, u, trivial, rfl⟩

@[expose] def commF (σ : Perm (Fin 5)) : Finset orth.W :=
  Finset.univ.image fun u : orth.W => orth.act σ u * u⁻¹

@[expose] def commHom {n : ℕ} (M : Model n) (σ : Perm (Fin n)) : M.W →* M.W where
  toFun u := M.act σ u * u⁻¹
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _

theorem commW_zpowers_top_eq_range {n : ℕ} (M : Model n) (σ : Perm (Fin n)) :
    commW M (Subgroup.zpowers σ) ⊤ = (commHom M σ).range := by
  rw [commW_zpowers_top]
  have : {w | ∃ u, w = M.act σ u * u⁻¹} = ((commHom M σ).range : Set M.W) := by
    ext w
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, MonoidHom.mem_range]
    exact ⟨fun ⟨u, h⟩ => ⟨u, h.symm⟩, fun ⟨u, h⟩ => ⟨u, h.symm⟩⟩
  rw [this]
  exact Subgroup.closure_eq _

theorem mem_commW_zpowers_iff (σ : Perm (Fin 5)) (w : orth.W) :
    w ∈ commW orth (Subgroup.zpowers σ) ⊤ ↔ w ∈ commF σ := by
  rw [commW_zpowers_top_eq_range]
  simp only [MonoidHom.mem_range, commF, Finset.mem_image, Finset.mem_univ, true_and]
  rfl

theorem card_commW_zpowers (σ : Perm (Fin 5)) :
    Nat.card (commW orth (Subgroup.zpowers σ) ⊤) = (commF σ).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_commW_zpowers_iff σ w)

theorem mem_zpowers_iff_of_mul_self {G : Type} [Group G] {x y : G} (h : x * x = 1) :
    y ∈ Subgroup.zpowers x ↔ y = 1 ∨ y = x := by
  have hx : x ^ 2 = 1 := by rw [pow_two]; exact h
  rw [mem_zpowers_iff_of_pow_eq_one hx (by norm_num)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (pow_zero x)
    · exact Or.inr (pow_one x)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, pow_zero x⟩
    · exact ⟨1, by norm_num, pow_one _⟩

theorem ep_mul_self (a b : Fin 5) : ep a b * ep a b = 1 := orth.sq _

theorem vp_mul_self (p : Fin 5) : vp p * vp p = 1 := orth.sq _

theorem vp_ne_one (p : Fin 5) : vp p ≠ 1 := by revert p; decide +kernel

theorem ep_ne_one {a b : Fin 5} (h : a ≠ b) : ep a b ≠ 1 := by
  revert a b; decide +kernel

theorem vp_injective : Function.Injective vp := by
  intro p q h; revert p q; decide +kernel

theorem ep_mul_ep {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup) : ep a b * ep c d = vp p := by
  revert a b c d p; decide +kernel

theorem act_vp (g : Perm (Fin 5)) (p : Fin 5) : orth.act g (vp p) = vp (g p) := by
  revert g p; decide +kernel

theorem act_ep (g : Perm (Fin 5)) (a b : Fin 5) : orth.act g (ep a b) = ep (g a) (g b) := by
  revert g a b; decide +kernel

theorem wtO_vp (p : Fin 5) : wtO (vp p) = 4 := by revert p; decide +kernel

theorem wtO_ep {a b : Fin 5} (h : a ≠ b) : wtO (ep a b) = 2 := by
  revert a b; decide +kernel

@[expose] def IsDoubleSwap (g : Perm (Fin 5)) : Prop :=
  g ≠ 1 ∧ g ^ 2 = 1 ∧ Perm.sign g = 1

theorem idx_orth_eq_two_iff (g : Perm (Fin 5)) : idx orth g = 2 ↔ g.IsSwap := by
  by_cases h1 : g = 1
  · subst h1
    rw [idx_orth]
    simp only [↓reduceIte]
    constructor
    · intro h; omega
    · rintro ⟨x, y, hxy, h⟩
      exact absurd (by simpa using (congrArg (fun f => f x) h)) hxy
  · exact (transvections g h1).2

theorem idx_orth_ne_one {g : Perm (Fin 5)} (hg : g ≠ 1) : idx orth g ≠ 1 := by
  rw [idx_orth]
  simp only [hg, ↓reduceIte]
  split_ifs <;> omega

theorem eq_one_of_act_eq_self {g : Perm (Fin 5)} (h : ∀ w : orth.W, orth.act g w = w) :
    g = 1 := by
  by_contra hg
  have h1 := idx_orth_ne_one hg
  apply h1
  have h2 := idx_mul_card orth g
  have h3 : Nat.card {w : orth.W // orth.act g w = w} = Nat.card orth.W :=
    Nat.card_congr (Equiv.subtypeUnivEquiv h)
  rw [h3] at h2
  have h4 : 0 < Nat.card orth.W := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right h4 (by rw [h2, one_mul]))

theorem idx_orth_doubleSwap {g : Perm (Fin 5)} (h : IsDoubleSwap g) : idx orth g = 4 := by
  rw [idx_orth]
  obtain ⟨h1, h2, h3⟩ := h
  simp [h1, h2, h3]

end CFSG.Quasithin.F53.Stellmacher.S35.Fin

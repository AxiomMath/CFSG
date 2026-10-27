module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CKCoordAux_zmod3_eq_one_or_neg_one (z : ZMod 3) (hz : z ≠ 0) :
    z = 1 ∨ z = -1 := by
  have h : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = -1 := by decide
  rcases h z with h | h | h
  · exact absurd h hz
  · exact Or.inl h
  · exact Or.inr h

private lemma hdRo7CKCoordAux_sign3 {p : ℕ} {a b c : ZMod p}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    a * b * c = 1 ∨ a * b * c = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    norm_num

private lemma hdRo7CKCoordAux_swap_apply_of_ne {α : Type} [DecidableEq α] {x y z : α}
    (hx : z ≠ x) (hy : z ≠ y) : Equiv.swap x y z = z := by
  rw [Equiv.swap_apply_def]
  by_cases h1 : z = x
  · rw [if_pos h1]; exact absurd h1 hx
  · rw [if_neg h1]
    by_cases h2 : z = y
    · rw [if_pos h2]; exact absurd h2 hy
    · rw [if_neg h2]

private noncomputable def hdRo7CKCoordAux_coordAut {p : ℕ} {m : ℕ} (π : Equiv.Perm (Fin m))
    (s : Fin m → ZMod p) (hs : ∀ l, s l * s l = 1) :
    (Fin m → Multiplicative (ZMod p)) ≃* (Fin m → Multiplicative (ZMod p)) where
  toFun f := fun l => Multiplicative.ofAdd (s l * Multiplicative.toAdd (f (π l)))
  invFun g := fun l => Multiplicative.ofAdd (s (π.symm l) * Multiplicative.toAdd (g (π.symm l)))
  left_inv f := by
    funext l
    dsimp only
    rw [Equiv.apply_symm_apply]
    change Multiplicative.ofAdd (s (π.symm l) *
      (s (π.symm l) * Multiplicative.toAdd (f l))) = f l
    rw [← mul_assoc, hs (π.symm l), one_mul]
    rfl
  right_inv g := by
    funext l
    dsimp only
    rw [Equiv.symm_apply_apply]
    change Multiplicative.ofAdd (s l * (s l * Multiplicative.toAdd (g l))) = g l
    rw [← mul_assoc, hs l, one_mul]
    rfl
  map_mul' f g := by
    funext l
    show Multiplicative.ofAdd (s l *
        (Multiplicative.toAdd (f (π l)) + Multiplicative.toAdd (g (π l)))) =
      Multiplicative.ofAdd (s l * Multiplicative.toAdd (f (π l))) *
        Multiplicative.ofAdd (s l * Multiplicative.toAdd (g (π l)))
    rw [mul_add]
    rfl

private lemma hdRo7CKCoordAux_coordAut_apply {p : ℕ} {m : ℕ} (π : Equiv.Perm (Fin m))
    (s : Fin m → ZMod p) (hs : ∀ l, s l * s l = 1)
    (f : Fin m → Multiplicative (ZMod p)) (l : Fin m) :
    Multiplicative.toAdd (hdRo7CKCoordAux_coordAut π s hs f l) =
      s l * Multiplicative.toAdd (f (π l)) := rfl

private lemma hdRo7CKCoordAux_coordAut_symm_apply {p : ℕ} {m : ℕ} (π : Equiv.Perm (Fin m))
    (s : Fin m → ZMod p) (hs : ∀ l, s l * s l = 1)
    (g : Fin m → Multiplicative (ZMod p)) (l : Fin m) :
    Multiplicative.toAdd ((hdRo7CKCoordAux_coordAut π s hs).symm g l) =
      s (π.symm l) * Multiplicative.toAdd (g (π.symm l)) := rfl

private lemma hdRo7CKCoordAux_coordAut_mulSingle {p : ℕ} {m : ℕ} [NeZero m] (π : Equiv.Perm (Fin m))
    (s : Fin m → ZMod p) (hs : ∀ l, s l * s l = 1) (hπ0 : π 0 = 0) (hs0 : s 0 = 1) :
    hdRo7CKCoordAux_coordAut π s hs
        (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) 0
          (Multiplicative.ofAdd (1 : ZMod p))) =
      Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) 0
        (Multiplicative.ofAdd (1 : ZMod p)) := by
  funext l
  apply Multiplicative.toAdd.injective
  rw [hdRo7CKCoordAux_coordAut_apply]
  by_cases hl : l = 0
  · subst hl
    rw [hπ0, Pi.mulSingle_eq_same, hs0]
    ring
  · have hπl : π l ≠ 0 := fun h => hl (π.injective (by rw [h, hπ0]))
    rw [Pi.mulSingle_eq_of_ne hπl, Pi.mulSingle_eq_of_ne hl]
    simp

private def hdRo7CKCoordAux_CoordPerm {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (n : ℕ)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (a : MulAut ↥Bs) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod p), σ 0 = 0 ∧ c 0 = 1 ∧
    (∀ i, c i = 1 ∨ c i = -1) ∧
    ∀ (f : Fin (n + 1) → Multiplicative (ZMod p)) (i : Fin (n + 1)),
      Multiplicative.toAdd (τ.symm (a (τ f)) (σ i)) = c i * Multiplicative.toAdd (f i)

private theorem hdRo7CKCoordAux_conj_coordPerm {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G)
    (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (π : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod p)
    (hssq : ∀ l, s l * s l = 1) (hs0 : s 0 = 1) (hπ0 : π 0 = 0)
    (hsgn : ∀ l, s l = 1 ∨ s l = -1) (a : MulAut ↥Bs) :
    hdRo7CKCoordAux_CoordPerm p Bs n τ a ↔
      hdRo7CKCoordAux_CoordPerm p Bs n
        ((hdRo7CKCoordAux_coordAut π s hssq).trans τ) a := by
  classical
  let ρ := hdRo7CKCoordAux_coordAut π s hssq
  let τ' := ρ.trans τ
  have hπs0 : π.symm 0 = 0 := by
    rw [← hπ0, Equiv.symm_apply_apply]
    exact hπ0.symm
  constructor
  · rintro ⟨σ, c, hσ0, hc0, hcs, hform⟩
    let σ' : Equiv.Perm (Fin (n + 1)) := π.symm.trans (σ.trans π)
    let c' : Fin (n + 1) → ZMod p := fun i => s (σ (π.symm i)) * s (π.symm i) * c (π.symm i)
    have hσ'0 : σ' 0 = 0 := by
      dsimp only [σ']
      rw [Equiv.trans_apply, Equiv.trans_apply, hπs0, hσ0, hπ0]
    have hc'0 : c' 0 = 1 := by
      dsimp only [c']
      rw [hπs0, hσ0, hs0, hc0]
      ring
    have hc's : ∀ i, c' i = 1 ∨ c' i = -1 := by
      intro i
      dsimp only [c']
      exact hdRo7CKCoordAux_sign3 (hsgn (σ (π.symm i))) (hsgn (π.symm i))
        (hcs (π.symm i))
    have hform' : ∀ f i, Multiplicative.toAdd (τ'.symm (a (τ' f)) (σ' i)) =
        c' i * Multiplicative.toAdd (f i) := by
      intro f i
      have hτ'symm : τ'.symm (a (τ' f)) = ρ.symm (τ.symm (a (τ (ρ f)))) := rfl
      rw [hτ'symm, hdRo7CKCoordAux_coordAut_symm_apply π s hssq]
      have h1 : π.symm (σ' i) = σ (π.symm i) := by
        dsimp only [σ']
        rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
      rw [h1, hform (ρ f) (π.symm i), hdRo7CKCoordAux_coordAut_apply π s hssq]
      simp only [Equiv.apply_symm_apply]
      dsimp only [c']
      ring
    exact ⟨σ', c', hσ'0, hc'0, hc's, hform'⟩
  · rintro ⟨σ', c', hσ'0, hc'0, hcs', hform'⟩
    let σ : Equiv.Perm (Fin (n + 1)) := π.trans (σ'.trans π.symm)
    let c : Fin (n + 1) → ZMod p := fun i => s (σ i) * s i * c' (π i)
    have hσ0 : σ 0 = 0 := by
      dsimp only [σ]
      rw [Equiv.trans_apply, Equiv.trans_apply, hπ0, hσ'0, hπs0]
    have hc0 : c 0 = 1 := by
      dsimp only [c]
      rw [hπ0, hσ0, hs0, hc'0]
      ring
    have hcs : ∀ i, c i = 1 ∨ c i = -1 := by
      intro i
      dsimp only [c]
      exact hdRo7CKCoordAux_sign3 (hsgn (σ i)) (hsgn i) (hcs' (π i))
    refine ⟨σ, c, hσ0, hc0, hcs, ?_⟩
    intro f i
    have h := hform' (ρ.symm f) (π i)
    have hτ' : τ' (ρ.symm f) = τ f := by
      show τ (ρ (ρ.symm f)) = τ f
      rw [MulEquiv.apply_symm_apply]
    rw [hτ'] at h
    rw [show τ'.symm (a (τ f)) = ρ.symm (τ.symm (a (τ f))) from rfl,
      hdRo7CKCoordAux_coordAut_symm_apply π s hssq] at h
    have h1 : π.symm (σ' (π i)) = σ i := by
      dsimp only [σ]
      rw [Equiv.trans_apply, Equiv.trans_apply]
    rw [h1] at h
    rw [hdRo7CKCoordAux_coordAut_symm_apply π s hssq] at h
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
    dsimp only [c]
    calc
      Multiplicative.toAdd (τ.symm (a (τ f)) (σ i))
          = s (σ i) * (s (σ i) * Multiplicative.toAdd (τ.symm (a (τ f)) (σ i))) := by
            rw [← mul_assoc, hssq (σ i), one_mul]
      _ = s (σ i) * (c' (π i) * (s i * Multiplicative.toAdd (f i))) := by rw [h]
      _ = s (σ i) * s i * c' (π i) * Multiplicative.toAdd (f i) := by ring

theorem hdRo7CKCoordAux_normalize {G : Type} [Group G] (p : ℕ) (hp3 : p = 3) (Bs K : Subgroup G) (n : ℕ)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (y x : ↥Bs)
    (h0 : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = y)
    (hmodel : C2CoordModel p Bs K n τ) (i j : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
    (hsupp : ∀ l : Fin (n + 1), l ≠ 0 → (Multiplicative.toAdd (τ.symm x l) ≠ 0 ↔ l = i ∨ l = j)) :
    ∃ τ' : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs,
      τ' (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = y ∧ C2CoordModel p Bs K n τ' ∧
      ∃ c : ZMod p, ∀ l : Fin (n + 1), Multiplicative.toAdd (τ'.symm x l) =
        if l = 0 then c else if l = 1 ∨ l = 2 then 1 else 0 := by
  classical
  subst hp3
  have h3 : 3 ≤ n + 1 := by
    have h2 : ({i, j} : Finset (Fin (n + 1))).card = 2 := Finset.card_pair hij
    have hle : ({i, j} : Finset (Fin (n + 1))).card ≤ Fintype.card (Fin (n + 1)) :=
      Finset.card_le_univ _
    rw [h2, Fintype.card_fin] at hle
    omega
  have h1lt : 1 < n + 1 := by omega
  have h2lt : 2 < n + 1 := by omega
  let a : Fin (n + 1) := ⟨1, h1lt⟩
  let b : Fin (n + 1) := ⟨2, h2lt⟩
  have ha0 : a ≠ 0 := by intro h; have := congrArg Fin.val h; simp [a] at this
  have hb0 : b ≠ 0 := by intro h; have := congrArg Fin.val h; simp [b] at this
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  have ha_eq : (1 : Fin (n + 1)) = a := by
    apply Fin.ext
    simp [a, Fin.val_ofNat, Nat.mod_eq_of_lt h1lt]
  have hb_eq : (2 : Fin (n + 1)) = b := by
    apply Fin.ext
    simp [b, Fin.val_ofNat, Nat.mod_eq_of_lt h2lt]
  let u : Fin (n + 1) → Multiplicative (ZMod 3) := τ.symm x
  have hui : Multiplicative.toAdd (u i) ≠ 0 := by
    have := (hsupp i hi).mpr (Or.inl rfl)
    simpa [u] using this
  have huj : Multiplicative.toAdd (u j) ≠ 0 := by
    have := (hsupp j hj).mpr (Or.inr rfl)
    simpa [u] using this
  have hui1 : Multiplicative.toAdd (u i) = 1 ∨ Multiplicative.toAdd (u i) = -1 :=
    hdRo7CKCoordAux_zmod3_eq_one_or_neg_one _ hui
  have huj1 : Multiplicative.toAdd (u j) = 1 ∨ Multiplicative.toAdd (u j) = -1 :=
    hdRo7CKCoordAux_zmod3_eq_one_or_neg_one _ huj
  have hne_a_s : a ≠ Equiv.swap i a j := by
    intro h
    have hji : j = i := (Equiv.swap_apply_eq_iff.mp h.symm).trans (Equiv.swap_apply_right i a)
    exact hij hji.symm
  have hne_0_s : (0 : Fin (n + 1)) ≠ Equiv.swap i a j := by
    intro h
    have hj0 : j = 0 := (Equiv.swap_apply_eq_iff.mp h.symm).trans
      (hdRo7CKCoordAux_swap_apply_of_ne (fun h => hi h.symm) (fun h => ha0 h.symm))
    exact hj hj0
  have hne_0_b : (0 : Fin (n + 1)) ≠ b := fun h => hb0 h.symm
  let π : Equiv.Perm (Fin (n + 1)) := (Equiv.swap i a).trans (Equiv.swap (Equiv.swap i a j) b)
  have hπi : π i = a := by
    dsimp only [π]
    rw [Equiv.trans_apply, Equiv.swap_apply_left]
    exact hdRo7CKCoordAux_swap_apply_of_ne hne_a_s hab
  have hπj : π j = b := by
    dsimp only [π]
    rw [Equiv.trans_apply, Equiv.swap_apply_left]
  have hπ0 : π 0 = 0 := by
    dsimp only [π]
    rw [Equiv.trans_apply]
    have h0ia : Equiv.swap i a (0 : Fin (n + 1)) = 0 :=
      hdRo7CKCoordAux_swap_apply_of_ne (fun h => hi h.symm) (fun h => ha0 h.symm)
    rw [h0ia]
    exact hdRo7CKCoordAux_swap_apply_of_ne hne_0_s hne_0_b
  let s : Fin (n + 1) → ZMod 3 := fun l =>
    if l = i then Multiplicative.toAdd (u i) else if l = j then Multiplicative.toAdd (u j) else 1
  have hsi : s i = Multiplicative.toAdd (u i) := by
    dsimp only [s]
    rw [if_pos rfl]
  have hsj : s j = Multiplicative.toAdd (u j) := by
    dsimp only [s]
    rw [if_neg (fun h => hij h.symm), if_pos rfl]
  have hs0 : s 0 = 1 := by
    dsimp only [s]
    rw [if_neg (fun h => hi h.symm), if_neg (fun h => hj h.symm)]
  have hsgn : ∀ l, s l = 1 ∨ s l = -1 := by
    intro l
    dsimp only [s]
    by_cases h1 : l = i
    · rw [if_pos h1]; exact hui1
    · rw [if_neg h1]
      by_cases h2 : l = j
      · rw [if_pos h2]; exact huj1
      · rw [if_neg h2]; exact Or.inl rfl
  have hssq : ∀ l, s l * s l = 1 := by
    intro l
    rcases hsgn l with h | h <;> rw [h] <;> ring
  let ρ := hdRo7CKCoordAux_coordAut π s hssq
  let τ' := ρ.trans τ
  have hπs0 : π.symm 0 = 0 := by
    rw [← hπ0, Equiv.symm_apply_apply]
    exact hπ0.symm
  have hπsa : π.symm a = i := by rw [← hπi, Equiv.symm_apply_apply]
  have hπsb : π.symm b = j := by rw [← hπj, Equiv.symm_apply_apply]
  refine ⟨τ', ?_, ?_, Multiplicative.toAdd (u 0), ?_⟩
  · have hρe0 : ρ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod 3)) 0
          (Multiplicative.ofAdd (1 : ZMod 3))) =
        Pi.mulSingle (M := fun _ => Multiplicative (ZMod 3)) 0
          (Multiplicative.ofAdd (1 : ZMod 3)) :=
      hdRo7CKCoordAux_coordAut_mulSingle π s hssq hπ0 hs0
    show τ (ρ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod 3)) 0
      (Multiplicative.ofAdd (1 : ZMod 3)))) = y
    rw [hρe0, h0]
  · intro a'
    constructor
    · intro ha
      exact (hdRo7CKCoordAux_conj_coordPerm 3 Bs n τ π s hssq hs0 hπ0 hsgn a').mp
        ((hmodel a').mp ha)
    · intro hc
      exact (hmodel a').mpr
        ((hdRo7CKCoordAux_conj_coordPerm 3 Bs n τ π s hssq hs0 hπ0 hsgn a').mpr hc)
  · intro l
    rw [ha_eq, hb_eq]
    have hτ'symm : τ'.symm x = ρ.symm u := rfl
    rw [hτ'symm, hdRo7CKCoordAux_coordAut_symm_apply π s hssq]
    by_cases hl0 : l = 0
    · subst hl0
      rw [hπs0, if_pos rfl, hs0, one_mul]
    · rw [if_neg hl0]
      by_cases hla : l = a
      · subst hla
        rw [hπsa, hsi, if_pos (Or.inl rfl)]
        rcases hui1 with h | h <;> rw [h] <;> ring
      · by_cases hlb : l = b
        · subst hlb
          rw [hπsb, hsj, if_pos (Or.inr rfl)]
          rcases huj1 with h | h <;> rw [h] <;> ring
        · rw [if_neg (fun h => h.elim hla hlb)]
          have hne0 : π.symm l ≠ 0 := by
            intro h
            exact hl0 (by rw [← Equiv.apply_symm_apply π l, h, hπ0])
          have hnei : π.symm l ≠ i := by
            intro h
            exact hla (by rw [← Equiv.apply_symm_apply π l, h, hπi])
          have hnej : π.symm l ≠ j := by
            intro h
            exact hlb (by rw [← Equiv.apply_symm_apply π l, h, hπj])
          have hzu : Multiplicative.toAdd (u (π.symm l)) = 0 := by
            by_contra h
            exact (fun h' => h'.elim hnei hnej) ((hsupp (π.symm l) hne0).mp h)
          rw [hzu, mul_zero]

end CFSG.StandardType.HdRo7C

end

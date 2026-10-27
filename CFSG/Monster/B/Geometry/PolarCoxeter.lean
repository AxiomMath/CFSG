module

public import CFSG.Monster.B.Geometry.Gate
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}

@[expose] def natListGet : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, n + 1 => natListGet l n

@[expose] def b3Table : Fin 3 → List ℕ
  | 0 => [9, 1, 2, 6, 7, 5, 3, 4, 8, 0, 10, 11, 15, 16, 14, 12, 13, 17]
  | 1 => [1, 0, 2, 12, 5, 4, 6, 8, 7, 10, 9, 11, 3, 14, 13, 15, 17, 16]
  | 2 => [0, 2, 1, 4, 3, 14, 7, 6, 8, 9, 11, 10, 13, 12, 5, 16, 15, 17]

@[expose] def b3Fun (k : Fin 3) (r : Fin 18) : Fin 18 :=
  ⟨natListGet (b3Table k) r.val % 18, Nat.mod_lt _ (by norm_num)⟩

theorem b3Fun_b3Fun : ∀ (k : Fin 3) (r : Fin 18), b3Fun k (b3Fun k r) = r := by decide +kernel

@[expose] def b3Perm (k : Fin 3) : Equiv.Perm (Fin 18) :=
  ⟨b3Fun k, b3Fun k, b3Fun_b3Fun k, b3Fun_b3Fun k⟩

@[expose] def negCount (g : Equiv.Perm (Fin 18)) : ℕ :=
  (Finset.univ.filter fun r : Fin 18 => r.val < 9 ∧ 9 ≤ (g r).val).card

@[expose] def b3Simple : Fin 3 → Fin 18
  | 0 => 0
  | 1 => 3
  | 2 => 5

theorem b3Perm_simple : ∀ k : Fin 3, 9 ≤ (b3Perm k (b3Simple k)).val := by decide +kernel

theorem b3Perm_pos : ∀ (k : Fin 3) (r : Fin 18), r.val < 9 → r ≠ b3Simple k →
    (b3Perm k r).val < 9 ∧ b3Perm k r ≠ b3Simple k := by decide +kernel

theorem negCount_mul_le (g : Equiv.Perm (Fin 18)) (k : Fin 3) :
    negCount (g * b3Perm k) ≤ negCount g + 1 := by
  classical
  set A := Finset.univ.filter fun r : Fin 18 => r.val < 9 ∧ 9 ≤ ((g * b3Perm k) r).val
  set B := Finset.univ.filter fun r : Fin 18 => r.val < 9 ∧ 9 ≤ (g r).val
  have hAB : (A.erase (b3Simple k)).card ≤ (B.erase (b3Simple k)).card := by
    refine Finset.card_le_card_of_injOn (b3Perm k) (fun r hr => ?_) (b3Perm k).injective.injOn
    simp only [Finset.mem_coe] at hr ⊢
    rw [Finset.mem_erase, Finset.mem_filter] at hr
    obtain ⟨hne, -, hlt, hneg⟩ := hr
    obtain ⟨h1, h2⟩ := b3Perm_pos k r hlt hne
    rw [Finset.mem_erase, Finset.mem_filter]
    exact ⟨h2, Finset.mem_univ _, h1, by rwa [Equiv.Perm.mul_apply] at hneg⟩
  have h1 := Finset.pred_card_le_card_erase (s := A) (a := b3Simple k)
  have h2 := Finset.card_erase_le (s := B) (a := b3Simple k)
  change A.card ≤ B.card + 1
  omega

theorem negCount_one : negCount 1 = 0 := by decide +kernel

theorem negCount_longest_word :
    negCount ((b3Perm 0 * b3Perm 1 * b3Perm 2) * (b3Perm 0 * b3Perm 1 * b3Perm 2) *
      (b3Perm 0 * b3Perm 1 * b3Perm 2)) = 9 := by decide +kernel

theorem b3_relations :
    (b3Perm 0 * b3Perm 1) ^ 4 = 1 ∧ (b3Perm 1 * b3Perm 0) ^ 4 = 1 ∧
      (b3Perm 1 * b3Perm 2) ^ 3 = 1 ∧ (b3Perm 2 * b3Perm 1) ^ 3 = 1 ∧
      (b3Perm 0 * b3Perm 2) ^ 2 = 1 ∧ (b3Perm 2 * b3Perm 0) ^ 2 = 1 ∧
      (b3Perm 0 * b3Perm 0) ^ 1 = 1 ∧ (b3Perm 1 * b3Perm 1) ^ 1 = 1 ∧
      (b3Perm 2 * b3Perm 2) ^ 1 = 1 := by decide +kernel

section C3

open _root_.Classical in
@[expose] noncomputable def c3RootAction (l π : ι) (i : ι) : Equiv.Perm (Fin 18) :=
  if i = π then b3Perm 0 else if i = l then b3Perm 1 else b3Perm 2

theorem c3RootAction_π (l π : ι) : c3RootAction l π π = b3Perm 0 := by
  simp [c3RootAction]

theorem c3RootAction_l {l π : ι} (hlπ : l ≠ π) : c3RootAction l π l = b3Perm 1 := by
  simp [c3RootAction, hlπ]

theorem c3RootAction_p {p l π : ι} (hpl : p ≠ l) (hpπ : p ≠ π) :
    c3RootAction l π p = b3Perm 2 := by
  simp [c3RootAction, hpπ, hpl]

theorem exists_simple_of_length_eq_one {w : W} (hw : cs.length w = 1) :
    ∃ i, w = cs.simple i := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [hω.eq] at hw
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hw
  exact ⟨i, cs.wordProd_singleton i⟩

variable {p l π : ι} (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π)
  (hι : ∀ i, i = p ∨ i = l ∨ i = π) (hMpl : M p l = 3) (hMlπ : M l π = 4) (hMpπ : M p π = 2)
include hpl hlπ hpπ hι hMpl hMlπ hMpπ

omit [Group W] in
theorem isLiftable_c3RootAction : M.IsLiftable (c3RootAction l π) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := b3_relations
  have hπ := c3RootAction_π l π
  have hl := c3RootAction_l hlπ
  have hp := c3RootAction_p (l := l) (π := π) hpl hpπ
  have hlp : M l p = 3 := by rw [M.symmetric]; exact hMpl
  have hπl : M π l = 4 := by rw [M.symmetric]; exact hMlπ
  have hπp : M π p = 2 := by rw [M.symmetric]; exact hMpπ
  intro i j
  rcases hι i with hi | hi | hi <;> rcases hι j with hj | hj | hj <;> rw [hi, hj] <;>
    simp only [hπ, hl, hp, M.diagonal, hMpl, hMlπ, hMpπ, hlp, hπl, hπp] <;> assumption

noncomputable def c3RootHom : W →* Equiv.Perm (Fin 18) :=
  cs.lift ⟨c3RootAction l π, isLiftable_c3RootAction hpl hlπ hpπ hι hMpl hMlπ hMpπ⟩

theorem negCount_le_length (w : W) :
    negCount (c3RootHom (cs := cs) hpl hlπ hpπ hι hMpl hMlπ hMpπ w) ≤ cs.length w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [hω.eq]
  clear hω
  induction ω using List.reverseRecOn with
  | nil => simp [negCount_one]
  | append_singleton ω i ih =>
    rw [cs.wordProd_append, map_mul, cs.wordProd_singleton, c3RootHom, lift_apply_simple,
      List.length_append, List.length_singleton]
    have : ∃ k, c3RootAction l π i = b3Perm k := by
      rcases hι i with hi | hi | hi <;> rw [hi]
      · exact ⟨2, c3RootAction_p hpl hpπ⟩
      · exact ⟨1, c3RootAction_l hlπ⟩
      · exact ⟨0, c3RootAction_π l π⟩
    obtain ⟨k, hk⟩ := this
    rw [hk]
    exact (negCount_mul_le _ k).trans (by unfold c3RootHom at ih; omega)

theorem nine_le_length_longest_C3 [Finite W] : 9 ≤ cs.length (longest cs Set.univ) := by
  have h := negCount_le_length (cs := cs) hpl hlπ hpπ hι hMpl hMlπ hMpπ
    (cs.wordProd [π, l, p, π, l, p, π, l, p])
  have hval : c3RootHom (cs := cs) hpl hlπ hpπ hι hMpl hMlπ hMpπ
      (cs.wordProd [π, l, p, π, l, p, π, l, p]) =
      (b3Perm 0 * b3Perm 1 * b3Perm 2) * (b3Perm 0 * b3Perm 1 * b3Perm 2) *
        (b3Perm 0 * b3Perm 1 * b3Perm 2) := by
    simp only [c3RootHom, cs.wordProd_cons, cs.wordProd_nil, map_mul, mul_one,
      lift_apply_simple, c3RootAction_π, c3RootAction_l hlπ, c3RootAction_p hpl hpπ]
    group
  rw [hval, negCount_longest_word] at h
  exact h.trans ((isLongest_univ (cs := cs)).2 _ (by rw [cs.parabolic_univ]; trivial))

theorem longest_comm_C3 [Finite W] (w : W) :
    longest cs Set.univ * w = w * longest cs Set.univ := by
  have hL := isLongest_univ (cs := cs)
  have hmem : ∀ x : W, x ∈ cs.parabolic Set.univ := fun x => by
    rw [cs.parabolic_univ]; trivial
  have hconj : ∀ i, ∃ j, longest cs Set.univ * cs.simple i * longest cs Set.univ = cs.simple j := by
    intro i
    refine exists_simple_of_length_eq_one ?_
    have h1 := hL.length_mul (hmem (cs.simple i * longest cs Set.univ))
    have h2 := hL.length_mul_left (hmem (cs.simple i))
    rw [cs.length_simple] at h2
    rw [mul_assoc]
    omega
  choose σ hσ using hconj
  have hord : ∀ i j, M (σ i) (σ j) = M i j := by
    intro i j
    rw [← cs.orderOf_simple_mul_simple, ← cs.orderOf_simple_mul_simple, ← hσ i, ← hσ j]
    have : longest cs Set.univ * cs.simple i * longest cs Set.univ *
        (longest cs Set.univ * cs.simple j * longest cs Set.univ) =
        longest cs Set.univ * (cs.simple i * cs.simple j) * (longest cs Set.univ)⁻¹ := by
      rw [hL.inv_eq]
      simp only [mul_assoc]
      rw [← mul_assoc (longest cs Set.univ) (longest cs Set.univ), hL.mul_self, one_mul]
    rw [this]
    exact orderOf_injective (MulAut.conj (longest cs Set.univ)).toMonoidHom
      (MulAut.conj (longest cs Set.univ)).injective _
  have hσl : σ l = l := by
    rcases hι (σ l) with h | h | h
    · exfalso
      have := hord l π
      rw [h, hMlπ] at this
      rcases hι (σ π) with h' | h' | h' <;> rw [h'] at this
      · rw [M.diagonal] at this; omega
      · omega
      · omega
    · exact h
    · exfalso
      have := hord l p
      rw [h, M.symmetric l p, hMpl] at this
      rcases hι (σ p) with h' | h' | h' <;> rw [h'] at this
      · rw [M.symmetric, hMpπ] at this; omega
      · rw [M.symmetric, hMlπ] at this; omega
      · rw [M.diagonal] at this; omega
  have hσπ : σ π = π := by
    have := hord l π
    rw [hσl, hMlπ] at this
    rcases hι (σ π) with h' | h' | h'
    · rw [h', M.symmetric, hMpl] at this; omega
    · rw [h', M.diagonal] at this; omega
    · exact h'
  have hσp : σ p = p := by
    have := hord l p
    rw [hσl, M.symmetric l p, hMpl] at this
    rcases hι (σ p) with h' | h' | h'
    · exact h'
    · rw [h', M.diagonal] at this; omega
    · rw [h', hMlπ] at this; omega
  have hcomm : ∀ i, longest cs Set.univ * cs.simple i = cs.simple i * longest cs Set.univ := by
    intro i
    have hi : σ i = i := by
      rcases hι i with rfl | rfl | rfl
      · exact hσp
      · exact hσl
      · exact hσπ
    have := hσ i
    rw [hi] at this
    calc longest cs Set.univ * cs.simple i
        = longest cs Set.univ * cs.simple i * longest cs Set.univ * longest cs Set.univ := by
          rw [mul_assoc _ (longest cs Set.univ), hL.mul_self, mul_one]
      _ = cs.simple i * longest cs Set.univ := by rw [this]
  have hle : (⊤ : Subgroup W) ≤ Subgroup.centralizer {longest cs Set.univ} := by
    rw [← cs.parabolic_univ, cs.parabolic_le_iff]
    intro i _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm i).symm
  have := hle (Subgroup.mem_top w)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

end C3

section Residues

variable {C : Type*} {δ : C → C → W} (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem exists_dist_eq_mul_of_mem_residue {J : Set ι} {x y z : C}
    (hz : z ∈ residue cs δ J y) : ∃ v ∈ cs.parabolic J, δ x z = δ x y * v := by
  induction hz with
  | refl => exact ⟨1, one_mem _, by rw [mul_one]⟩
  | tail _ hbc ih =>
    obtain ⟨v, hv, hxb⟩ := ih
    obtain ⟨j, hj, hδj⟩ := hbc
    rcases (hδ.mul_simple x _ _ j hδj).1 with h | h
    · exact ⟨v, hv, by rw [h, hxb]⟩
    · exact ⟨v * cs.simple j, mul_mem hv (cs.simple_mem_parabolic hj), by
        rw [h, hxb, mul_assoc]⟩

omit hδ in
theorem length_mul_add_length_longest_le [Finite W] {K J : Set ι} {x y : W}
    (hx : x ∈ cs.parabolic K) (hy : y ∈ cs.parabolic J) :
    cs.length (x * y) + cs.length (longest cs (K ∩ J)) ≤
      cs.length (longest cs K) + cs.length (longest cs J) := by
  obtain ⟨⟨u, v⟩, ⟨hu, hv, hyuv⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul (K ∩ J) y⁻¹
  dsimp only at hu hv hyuv
  have hKJ := isLongest_of_finite (cs := cs) (K ∩ J)
  have hK := isLongest_of_finite (cs := cs) K
  have hJ := isLongest_of_finite (cs := cs) J
  have hvK : v⁻¹ ∈ cs.parabolic K := inv_mem (cs.parabolic_mono Set.inter_subset_left hv)
  have hvJ : v ∈ cs.parabolic J := cs.parabolic_mono Set.inter_subset_right hv
  have hy' : y = v⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← hyuv, inv_inv]
  have huJ : u ∈ cs.parabolic J := by
    have : u = y⁻¹ * v⁻¹ := by rw [hyuv, mul_inv_cancel_right]
    rw [this]
    exact mul_mem (inv_mem hy) (inv_mem hvJ)
  have h1 : cs.length (x * y) ≤ cs.length (x * v⁻¹) + cs.length u := by
    rw [hy', ← mul_assoc]
    have := cs.length_mul_le (x * v⁻¹) u⁻¹
    rwa [cs.length_inv] at this
  have h2 : cs.length (x * v⁻¹) ≤ cs.length (longest cs K) := hK.2 _ (mul_mem hx hvK)
  have h3 := cs.length_mul_of_isMinimalCosetRep hu hKJ.1
  have h4 : cs.length (u * longest cs (K ∩ J)) ≤ cs.length (longest cs J) :=
    hJ.2 _ (mul_mem huJ (cs.parabolic_mono Set.inter_subset_right hKJ.1))
  omega

theorem length_longest_le_of_mem_residue [Finite W]
    (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ) {J : Set ι}
    {c d a b : C} (hcd : δ c d = longest cs Set.univ) (ha : a ∈ residue cs δ J c)
    (hb : b ∈ residue cs δ J d) :
    cs.length (longest cs Set.univ) ≤ cs.length (δ a b) + cs.length (longest cs J) := by
  have hL := isLongest_univ (cs := cs)
  have hJ := isLongest_of_finite (cs := cs) J
  obtain ⟨v, hv, hab⟩ := exists_dist_eq_mul_of_mem_residue hδ (x := a) hb
  obtain ⟨v', hv', hda⟩ := exists_dist_eq_mul_of_mem_residue hδ (x := d) ha
  have had : δ a d = v'⁻¹ * longest cs Set.univ := by
    rw [dist_inv hδ d a, hda, dist_inv hδ c d, hcd, hL.inv_eq, mul_inv_rev, hL.inv_eq]
  have hab' : δ a b = longest cs Set.univ * (v'⁻¹ * v) := by
    rw [hab, had, ← hcent, mul_assoc]
  have h1 := hL.length_mul (cs := cs) (x := v'⁻¹ * v) (by rw [cs.parabolic_univ]; trivial)
  have h2 : cs.length (v'⁻¹ * v) ≤ cs.length (longest cs J) := hJ.2 _ (mul_mem (inv_mem hv') hv)
  rw [hab']
  omega

end Residues

end CFSG.Monster.B.Geometry

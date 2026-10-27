module

public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.PairChain
public import Certificates.Data.CFSGNative.HeldB.Tests

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native

variable {n : ℕ}

theorem commB_iff {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ} (hH : BaseFaithful H bs)
    {t : Array ℕ} {τ : Equiv.Perm (Fin n)} (ht : Rep n t τ) {w : List (Array ℕ)}
    {g : Equiv.Perm (Fin n)} (hw : RepW n w g) (hbs : ∀ b ∈ bs, b < n)
    (hmem : (g * τ)⁻¹ * (τ * g) ∈ H) : commB t bs w = true ↔ τ * g = g * τ := by
  have key : ∀ x : Fin n, (t[evR w (x : ℕ)]! = evR w t[(x : ℕ)]!) ↔ τ (g x) = g (τ x) := by
    intro x
    rw [hw x, ht (g x), ht x, hw (τ x)]
    exact ⟨Fin.ext, fun h => by rw [h]⟩
  rw [commB, List.all_eq_true]
  constructor
  · intro h
    have h1 : (g * τ)⁻¹ * (τ * g) = 1 := hH _ hmem fun x hx => by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply]
      exact (key x).1 (beq_iff_eq.1 (h x hx))
    exact (inv_mul_eq_one.1 h1).symm
  · intro h b hb
    have hx := (key ⟨b, hbs b hb⟩).2 (by
      rw [← Equiv.Perm.mul_apply, h, Equiv.Perm.mul_apply])
    exact beq_iff_eq.2 hx

theorem twistInvB_iff {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ} (hH : BaseFaithful H bs)
    {t : Array ℕ} {τ : Equiv.Perm (Fin n)} (ht : Rep n t τ) {w : List (Array ℕ)}
    {g : Equiv.Perm (Fin n)} (hw : RepW n w g) (hbs : ∀ b ∈ bs, b < n)
    (hmem : (τ * g) ^ 2 ∈ H) : twistInvB t bs w = true ↔ (τ * g) ^ 2 = 1 := by
  have key : ∀ x : Fin n, (t[evR w t[evR w (x : ℕ)]!]! = (x : ℕ)) ↔ ((τ * g) ^ 2) x = x := by
    intro x
    rw [hw x, ht (g x), hw (τ (g x)), ht (g (τ (g x))), sq]
    simp only [Equiv.Perm.mul_apply]
    exact ⟨Fin.ext, fun h => by rw [h]⟩
  rw [twistInvB, List.all_eq_true]
  constructor
  · intro h
    exact hH _ hmem fun x hx => (key x).1 (beq_iff_eq.1 (h x hx))
  · intro h b hb
    exact beq_iff_eq.2 ((key ⟨b, hbs b hb⟩).2 (by rw [h]; rfl))

theorem heBase_lt : ∀ b ∈ heBase, b < 8330 := by decide

theorem heP_baseFaithful :
    BaseFaithful heP heBase := fun h hh hfix =>
  eq_one_of_fix_base hh fun b hb => hfix b (by
    simp only [heBase, List.mem_cons, List.not_mem_nil, or_false]
    omega)

theorem countW3_eq (h : List (Array ℕ) → Bool) (B0 B1 B2 : Array (Array ℕ)) :
    countW h [B0, B1, B2] [] = (B0.toList.map fun t0 => (B1.toList.map fun t1 =>
      (B2.toList.map fun t2 => if h [t2, t1, t0] then 1 else 0).sum).sum).sum := by
  simp only [countW, foldl_array_add_eq_sum]

theorem sum_map_filter_of {α : Type*} (p : α → Bool) (F G : α → ℕ) :
    ∀ l : List α, (∀ a ∈ l, F a = if p a then G a else 0) →
      (l.map F).sum = ((l.filter p).map G).sum
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      sum_map_filter_of p F G l fun b hb => h b (List.mem_cons_of_mem _ hb)]
    by_cases hp : p a <;> simp [hp]

theorem countW3_filter (f g : List (Array ℕ) → Bool) (p : Array ℕ → Bool)
    (B0 B1 B2 : Array (Array ℕ))
    (hprune : ∀ t0 ∈ B0, ∀ t1 ∈ B1, ∀ t2 ∈ B2, g [t2, t1, t0] = (p t0 && f [t2, t1, t0])) :
    countW g [B0, B1, B2] [] = countW f [B0.filter p, B1, B2] [] := by
  rw [countW3_eq, countW3_eq, Array.toList_filter]
  refine sum_map_filter_of p _ _ _ fun t0 ht0 => ?_
  have ht0' : t0 ∈ B0 := Array.mem_toList_iff.1 ht0
  cases hp : p t0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨t1, ht1, rfl⟩ := List.mem_map.1 hx
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨t2, ht2, rfl⟩ := List.mem_map.1 hy
    rw [hprune t0 ht0' t1 (Array.mem_toList_iff.1 ht1) t2 (Array.mem_toList_iff.1 ht2)]
    simp [hp]
  · simp only [↓reduceIte]
    refine congrArg List.sum (List.map_congr_left fun t1 ht1 => ?_)
    refine congrArg List.sum (List.map_congr_left fun t2 ht2 => ?_)
    rw [hprune t0 ht0' t1 (Array.mem_toList_iff.1 ht1) t2 (Array.mem_toList_iff.1 ht2), hp,
      Bool.true_and]

theorem heGroups_flatten : heGroups.flatten = List.range heChain.baseCount := rfl

theorem card_heP_eq_count_filter {f g : List (Array ℕ) → Bool}
    (Pr : Equiv.Perm (Fin 8330) → Prop) [DecidablePred Pr] (p : Array ℕ → Bool) {sz : ℕ}
    (hsz : 0 < sz) (hgP : ∀ w x, RepW 8330 w x → x ∈ heP → (g w = true ↔ Pr x))
    (hprune : ∀ t0 ∈ heBlock0, ∀ t1 ∈ heBlock1, ∀ t2 ∈ heBlock2,
      g [t2, t1, t0] = (p t0 && f [t2, t1, t0])) :
    Nat.card {x : heP // Pr x} = countWPar sz f (heBlock0.filter p) [heBlock1, heBlock2] := by
  rw [countWPar_eq hsz, ← countW3_filter f g p _ _ _ hprune]
  have h := card_eq_countW (Pr := Pr) heChainArrays (by norm_num) heChain_check.1
    heGroups_flatten (f := g) fun w x hw hx => hgP w x hw (by rwa [heP_eq_originalSubgroup])
  rw [heP_eq_originalSubgroup, h]
  show countW g heBlocks [] = _
  rw [heBlocks_eq]

theorem evR3_zero {t0 t1 t2 : Array ℕ} (h1 : t1[0]! = 0) (h2 : t2[0]! = 0) :
    evR [t2, t1, t0] 0 = t0[0]! := by
  show t0[t1[t2[0]!]!]! = t0[0]!
  rw [h2, h1]

theorem commB_prune {t t0 t1 t2 : Array ℕ} (ht : t[0]! = 0) (h1 : t1[0]! = 0) (h2 : t2[0]! = 0) :
    commB t heBase [t2, t1, t0] = ((t[t0[0]!]! == t0[0]!) && commB t heBase [t2, t1, t0]) := by
  have key : commB t heBase [t2, t1, t0] =
      ((t[t0[0]!]! == t0[0]!) && commB t [1, 2, 3, 4] [t2, t1, t0]) := by
    rw [commB, heBase, List.all_cons, evR3_zero h1 h2, ht, evR3_zero h1 h2]
    rfl
  rw [key]
  cases (t[t0[0]!]! == t0[0]!) <;> simp

theorem zero_prune (f : List (Array ℕ) → Bool) {t0 t1 t2 : Array ℕ} (h1 : t1[0]! = 0)
    (h2 : t2[0]! = 0) :
    (f [t2, t1, t0] && (evR [t2, t1, t0] 0 == 0)) = ((t0[0]! == 0) && f [t2, t1, t0]) := by
  rw [evR3_zero h1 h2, Bool.and_comm]

theorem evR_zero_iff {w : List (Array ℕ)} {x : Equiv.Perm (Fin 8330)} (hw : RepW 8330 w x) :
    (evR w 0 == 0) = true ↔ x 0 = 0 := by
  rw [beq_iff_eq, show (0 : ℕ) = ((0 : Fin 8330) : ℕ) from rfl, hw 0]
  exact ⟨Fin.ext, fun h => by rw [h]⟩

theorem card_inf_centralizer {M : Type*} [Group M] (H : Subgroup M) (u : M) :
    Nat.card (H ⊓ Subgroup.centralizer {u} : Subgroup M) = Nat.card {x : H // u * x = x * u} :=
  Nat.card_congr {
    toFun := fun y => ⟨⟨y, (Subgroup.mem_inf.1 y.2).1⟩,
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2).symm⟩
    invFun := fun x => ⟨x.1, Subgroup.mem_inf.2 ⟨x.1.2,
      Subgroup.mem_centralizer_singleton_iff.2 x.2.symm⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end CFSG.Sporadic.HeldB

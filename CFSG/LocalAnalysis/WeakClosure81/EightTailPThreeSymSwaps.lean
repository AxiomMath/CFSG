module

public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMatching
import CFSG.LocalAnalysis.WeakClosure81.ThreeOneElems

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm

open scoped Pointwise

private lemma wc85sw_swap_eq_iff_pair {α : Type*} [DecidableEq α] [Fintype α] {x y z t : α}
    (hxy : x ≠ y) (hzt : z ≠ t) :
    Equiv.swap x y = Equiv.swap z t ↔ ({x, y} : Set α) = {z, t} := by
  constructor
  · intro h
    have h' := congrArg Equiv.Perm.support h
    rw [Equiv.Perm.support_swap hxy, Equiv.Perm.support_swap hzt] at h'
    rw [← Finset.coe_pair, ← Finset.coe_pair, h']
  · intro h
    have hx : x ∈ ({z, t} : Set α) := h ▸ Set.mem_insert x {y}
    have hy : y ∈ ({z, t} : Set α) := h ▸ Set.mem_insert_of_mem x (Set.mem_singleton y)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exact Equiv.swap_comm _ _
    · exact absurd rfl hxy

private theorem wc85sw_centralizer_swap_eq_stabilizer {m : ℕ} {a b : Fin m} (hab : a ≠ b) :
    Subgroup.centralizer ({Equiv.swap a b} : Set (Perm (Fin m))) =
      MulAction.stabilizer (Perm (Fin m)) ({a, b} : Set (Fin m)) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, MulAction.mem_stabilizer_iff, Set.smul_set_insert,
    Set.smul_set_singleton, Perm.smul_def, Perm.smul_def]
  have hconj : g * swap a b = swap a b * g ↔ swap (g a) (g b) = swap a b := by
    rw [Equiv.swap_apply_apply]
    constructor
    · intro h
      rw [h, mul_inv_cancel_right]
    · intro h
      calc g * swap a b = g * swap a b * g⁻¹ * g := by rw [inv_mul_cancel_right]
        _ = swap a b * g := by rw [h]
  rw [hconj, wc85sw_swap_eq_iff_pair (g.injective.ne hab) hab]

theorem isCoatom_centralizer_swap {m : ℕ} (hm : 5 ≤ m) {a b : Fin m} (hab : a ≠ b) :
    IsCoatom (Subgroup.centralizer ({Equiv.swap a b} : Set (Perm (Fin m)))) := by
  have hpair : ({a, b} : Finset (Fin m)).card = 2 := Finset.card_pair hab
  let s : Set.powersetCard (Fin m) 2 := Set.powersetCard.ofCard hpair
  have hs : (s : Set (Fin m)) = {a, b} := by
    rw [← Set.powersetCard.coe_coe, Set.powersetCard.val_ofCard, Finset.coe_pair]
  haveI : Nontrivial (Set.powersetCard (Fin m) 2) :=
    Set.powersetCard.nontrivial' (α := Fin m) (n := 2) (by norm_num)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  haveI : MulAction.IsPreprimitive (Perm (Fin m)) (Set.powersetCard (Fin m) 2) :=
    Set.powersetCard.isPreprimitive_perm (α := Fin m) (n := 2) (by norm_num)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hcoat : IsCoatom (MulAction.stabilizer (Perm (Fin m)) s) :=
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (Perm (Fin m)) s
  rw [Set.powersetCard.stabilizer_coe, hs] at hcoat
  rw [wc85sw_centralizer_swap_eq_stabilizer hab]
  exact hcoat

theorem exists_second_two_cycle {m : ℕ} (hm : 5 ≤ m) {σ : Perm (Fin m)}
    (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x y, σ x = x → σ y = y → x = y) {a b : Fin m}
    (hab : a ≠ b) (hσa : σ a = b) :
    ∃ c d : Fin m, σ c = d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d := by
  have hb : σ b = a := by rw [← hσ a, hσa]
  have hcard1 : ({a, b} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_pair hab, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard1
  have hp' : p ≠ a ∧ p ≠ b := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hp
  obtain ⟨hpa, hpb⟩ := hp'
  have hcard2 : (insert p {a, b} : Finset (Fin m)).card <
      (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_insert_of_notMem hp, Finset.card_pair hab, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard2
  have hq' : q ≠ p ∧ q ≠ a ∧ q ≠ b := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hq
  obtain ⟨hqp, hqa, hqb⟩ := hq'
  by_cases hpf : σ p = p
  · have hqnf : q ≠ σ q := fun h => hqp (hfix p q hpf h.symm).symm
    refine ⟨q, σ q, rfl, hqa, hqb, ?_, ?_, hqnf⟩
    · intro h
      have hqb' : q = b := by
        calc q = σ (σ q) := (hσ q).symm
          _ = σ a := by rw [h]
          _ = b := hσa
      exact hqb hqb'
    · intro h
      have hqa' : q = a := by
        calc q = σ (σ q) := (hσ q).symm
          _ = σ b := by rw [h]
          _ = a := hb
      exact hqa hqa'
  · refine ⟨p, σ p, rfl, hpa, hpb, ?_, ?_, fun h => hpf h.symm⟩
    · intro h
      have hpb' : p = b := by rw [← hσ p, h, hσa]
      exact hpb hpb'
    · intro h
      have hpa' : p = a := by rw [← hσ p, h, hb]
      exact hpa hpa'

theorem exchange_two_cycles_mem_centralizer {m : ℕ} {σ : Perm (Fin m)} (hσ : ∀ x, σ (σ x) = x)
    {a b c d : Fin m} (hσa : σ a = b) (hσc : σ c = d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (swap a c * swap b d) * σ = σ * (swap a c * swap b d) ∧
      (swap a c * swap b d) * swap a b * (swap a c * swap b d)⁻¹ = swap c d := by
  constructor
  · have hmem : swap a c * swap (σ a) (σ c) ∈
        Subgroup.centralizer ({σ} : Set (Perm (Fin m))) :=
      ThreeOne.swap_mul_swap_mem_centralizer hσ (by rw [hσa]; exact hab.symm)
        (by rw [hσc]; exact hcd.symm)
    rw [hσa, hσc] at hmem
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem
  · have hρa : (swap a c * swap b d) a = c := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab had, Equiv.swap_apply_left]
    have hρb : (swap a c * swap b d) b = d := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne had.symm hcd.symm]
    rw [← Equiv.swap_apply_apply (swap a c * swap b d) a b, hρa, hρb]

theorem closure_centralizer_sup_normalizer_swaps {m : ℕ} (hm : 5 ≤ m)
    (P' : Sylow 2 (Perm (Fin m))) {τ : Perm (Fin m)} (hτ : τ.IsSwap)
    (hτP : τ ∈ (P' : Subgroup (Perm (Fin m)))) :
    Subgroup.closure ((Subgroup.centralizer ({τ} : Set (Perm (Fin m))) : Set (Perm (Fin m))) ∪
      (Subgroup.setNormalizer {σ : Perm (Fin m) | σ.IsSwap ∧ σ ∈ (P' : Subgroup (Perm (Fin m)))} :
        Set (Perm (Fin m)))) = ⊤ := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := hτ
  have hPsyl : CFSG.Quasithin.IsSylowIn 2 (P' : Subgroup (Perm (Fin m))) ⊤ :=
    CFSG.Quasithin.isSylowIn_of_card_eq le_top (by
      rw [Subgroup.card_top]
      exact Sylow.card_eq_multiplicity P')
  obtain ⟨σ, hσ, hTσ, hfix⟩ := ThreeOne.exists_matching hPsyl
  have hσa : σ a = b := (hTσ a b hab).mp hτP
  obtain ⟨c, d, hσc, hca, hcb, hda, hdb, hcd⟩ :=
    exists_second_two_cycle hm hσ hfix hab hσa
  obtain ⟨hcomm, hconj⟩ := exchange_two_cycles_mem_centralizer hσ hσa hσc hab hca.symm hda.symm
    hcb.symm hdb.symm hcd
  set ρ : Perm (Fin m) := swap a c * swap b d with hρdef
  have hρCσ : ρ ∈ Subgroup.centralizer ({σ} : Set (Perm (Fin m))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hρnotCτ : ρ ∉ Subgroup.centralizer ({swap a b} : Set (Perm (Fin m))) := by
    intro hmem
    have hcommτ : ρ * swap a b = swap a b * ρ :=
      Subgroup.mem_centralizer_singleton_iff.mp hmem
    have hneq : swap a b ≠ swap c d := by
      intro heq
      have h := congrArg (fun f : Perm (Fin m) => f a) heq
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca.symm hda.symm] at h
      exact hab h.symm
    exact hneq (by rw [← hconj, hcommτ, mul_assoc, mul_inv_cancel, mul_one])
  have hN : Subgroup.setNormalizer
        {s : Perm (Fin m) | s.IsSwap ∧ s ∈ (P' : Subgroup (Perm (Fin m)))} =
      Subgroup.centralizer ({σ} : Set (Perm (Fin m))) := by
    have hset : {s : Perm (Fin m) | s.IsSwap ∧ s ∈ (P' : Subgroup (Perm (Fin m)))} =
        {t : Perm (Fin m) | t ∈ (P' : Subgroup (Perm (Fin m))) ∧ t.IsSwap} := by
      ext s
      exact and_comm
    rw [hset, ThreeOne.setNormalizer_eq_centralizer hσ hTσ]
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hN]
  have hCτ : IsCoatom (Subgroup.centralizer ({swap a b} : Set (Perm (Fin m)))) :=
    isCoatom_centralizer_swap hm hab
  refine hCτ.lt_iff.mp ?_
  rw [lt_iff_le_not_ge]
  exact ⟨le_sup_left, fun hle => hρnotCτ (hle (Subgroup.mem_sup_right hρCσ))⟩

end CFSG.LocalAnalysis.WeakClosure81

end

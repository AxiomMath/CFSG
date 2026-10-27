module

public import CFSG.OddTranspositions.O4PairClass65Lang
import all CFSG.OddTranspositions.O4PairTenGraph

public section

noncomputable section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

theorem commute_mk_frob25t_iff {p q : PSL2 F25t}
    (hp : psl2FieldAut F25t frob25t p = p) (hq : psl2FieldAut F25t frob25t q = q) :
    Commute (SemidirectProduct.mk p frob25t : PSigmaL2t)
      (SemidirectProduct.mk q frob25t) ↔ Commute p q := by
  have hmul : (SemidirectProduct.mk p frob25t : PSigmaL2t) *
        SemidirectProduct.mk q frob25t = SemidirectProduct.mk (p * q) 1 := by
    ext <;> simp [hq, frob25t_mul_self]
  have hmul' : (SemidirectProduct.mk q frob25t : PSigmaL2t) *
        SemidirectProduct.mk p frob25t = SemidirectProduct.mk (q * p) 1 := by
    ext <;> simp [hp, frob25t_mul_self]
  rw [commute_iff_eq, commute_iff_eq, hmul, hmul']
  constructor
  · intro h
    exact congrArg SemidirectProduct.left h
  · intro h
    rw [h]

@[expose] noncomputable def y (i : Fin 10) : PSigmaL225 :=
  psigmaL2Equiv (SemidirectProduct.mk (x i) frob25t)

theorem commuting_class65_eq :
    {d : PSigmaL225 | d ∈ class65 ∧ Commute d (SemidirectProduct.inr frob25)} =
      insert (SemidirectProduct.inr frob25) (Set.range y) := by
  have htransport : psigmaL2Equiv '' {x : PSigmaL2t | x ∈ class65t ∧
      Commute x (SemidirectProduct.inr frob25t)} =
      {d : PSigmaL225 | d ∈ class65 ∧ Commute d (SemidirectProduct.inr frob25)} := by
    ext d
    constructor
    · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← psigmaL2Equiv_image_class65t]
        exact Set.mem_image_of_mem _ hx
      · rw [← psigmaL2Equiv_inr_frob25t]
        exact (psigmaL2Equiv_conj_iff x (SemidirectProduct.inr frob25t)).mpr hc
    · rintro ⟨hd, hc⟩
      refine ⟨psigmaL2Equiv.symm d, ⟨?_, ?_⟩, psigmaL2Equiv.apply_symm_apply d⟩
      · have hcls : psigmaL2Equiv.symm d ∈ class65t ↔ d ∈ class65 := by
          rw [← psigmaL2Equiv_image_class65t]
          constructor
          · intro h
            exact ⟨psigmaL2Equiv.symm d, h, psigmaL2Equiv.apply_symm_apply d⟩
          · rintro ⟨x, hx, hxd⟩
            rwa [← hxd, MulEquiv.symm_apply_apply]
        exact hcls.mpr hd
      · refine (psigmaL2Equiv_conj_iff (psigmaL2Equiv.symm d)
          (SemidirectProduct.inr frob25t)).mp ?_
        rw [psigmaL2Equiv.apply_symm_apply, psigmaL2Equiv_inr_frob25t]
        exact hc
  rw [← htransport, commuting_class65t_eq, Set.image_insert_eq, ← Set.range_comp,
    psigmaL2Equiv_inr_frob25t]
  rfl

theorem y_mem_class65 (i : Fin 10) : y i ∈ class65 := by
  have h : y i ∈ {d : PSigmaL225 | d ∈ class65 ∧
      Commute d (SemidirectProduct.inr frob25)} := by
    rw [commuting_class65_eq]
    exact Set.mem_insert_of_mem _ (Set.mem_range_self i)
  exact h.1

theorem y_commute_base (i : Fin 10) : Commute (y i) (SemidirectProduct.inr frob25) := by
  have h : y i ∈ {d : PSigmaL225 | d ∈ class65 ∧
      Commute d (SemidirectProduct.inr frob25)} := by
    rw [commuting_class65_eq]
    exact Set.mem_insert_of_mem _ (Set.mem_range_self i)
  exact h.2

theorem y_injective : Function.Injective y := by
  intro i j hij
  have h : SemidirectProduct.mk (x i) frob25t = SemidirectProduct.mk (x j) frob25t :=
    psigmaL2Equiv.injective hij
  exact x_injective (congrArg SemidirectProduct.left h)

theorem y_commuting_others (i : Fin 10) :
    Nat.card {j : Fin 10 // j ≠ i ∧ Commute (y i) (y j)} = 3 := by
  have hiff : ∀ j : Fin 10, (j ≠ i ∧ Commute (y i) (y j)) ↔
      (j ≠ i ∧ Commute (x i) (x j)) := fun j =>
    and_congr Iff.rfl
      ((psigmaL2Equiv_conj_iff (SemidirectProduct.mk (x i) frob25t)
        (SemidirectProduct.mk (x j) frob25t)).trans
        (commute_mk_frob25t_iff (x_fixed i) (x_fixed j)))
  exact (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans (card_commuting_others i)

theorem y_nc_connected (i j : Fin 10) :
    Relation.ReflTransGen (fun a b : Fin 10 => a ≠ b ∧ ¬ Commute (y a) (y b)) i j := by
  have hedge : ∀ a b : Fin 10, ncTen a b → a ≠ b ∧ ¬ Commute (y a) (y b) := by
    intro a b hab
    have hab' : a ≠ b ∧ ¬ Commute (x a) (x b) := hab
    refine ⟨hab'.1, fun hc => hab'.2 ?_⟩
    exact (commute_mk_frob25t_iff (x_fixed a) (x_fixed b)).mp
      ((psigmaL2Equiv_conj_iff (SemidirectProduct.mk (x a) frob25t)
        (SemidirectProduct.mk (x b) frob25t)).mp hc)
  exact Relation.ReflTransGen.mono hedge i j (ncTen_connected i j)

end CFSG.OddTranspositions.QZ

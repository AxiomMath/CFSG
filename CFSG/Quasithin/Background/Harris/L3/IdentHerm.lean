module

public import CFSG.Quasithin.Background.Harris.L3.IdentDual
public import CFSG.Quasithin.Background.HL3NineComm
public import CFSG.Quasithin.Background.Harris.L3.Setup

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 CFSG.Quasithin.H.Tri Matrix
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] noncomputable def hmu (E : Multiplicative V ≃* HMod n F) :
    V →+ Matrix (Fin 3) (Fin 3) F where
  toFun u := mat (E (Multiplicative.ofAdd u))
  map_zero' := by
    show mat (E (Multiplicative.ofAdd 0)) = 0
    rw [ofAdd_zero, map_one, mat_one]
  map_add' u' v' := by
    show mat (E (Multiplicative.ofAdd (u' + v'))) =
      mat (E (Multiplicative.ofAdd u')) + mat (E (Multiplicative.ofAdd v'))
    rw [ofAdd_add, map_mul, mat_mul]

theorem hmu_apply (E : Multiplicative V ≃* HMod n F) (u : V) :
    hmu E u = mat (E (Multiplicative.ofAdd u)) := rfl

theorem hmu_injective (E : Multiplicative V ≃* HMod n F) : Function.Injective (hmu E) :=
  fun _ _ h => Multiplicative.ofAdd.injective (E.injective (mat_injective h))

theorem hmu_herm (E : Multiplicative V ≃* HMod n F) (u : V) :
    (conjM n (hmu E u))ᵀ = hmu E u := herm_mat _

theorem hmu_bar (E : Multiplicative V ≃* HMod n F) (u : V) (i j : Fin 3) :
    bar n (hmu E u j i) = hmu E u i j := herm_apply _ _ _

theorem exists_hmu_eq (E : Multiplicative V ≃* HMod n F) {X : Matrix (Fin 3) (Fin 3) F}
    (hX : (conjM n X)ᵀ = X) : ∃ u, hmu E u = X :=
  ⟨Multiplicative.toAdd (E.symm (mkH X hX)), by simp [hmu_apply, mat_mkH]⟩

@[expose] def upTv (j : Fin 3) (hj : (0 : Fin 3) ≠ j) (a : F) : SL(3, F) :=
  ⟨transvection 0 j a, det_transvection_of_ne 0 j hj a⟩

theorem hmu_act {L : Subgroup (GLV V)} {π : SL(3, F) →* ↥L} (hK : Nat.card F = (2 ^ n) ^ 2)
    {ψ : SL(3, F) →* SL(3, F)} (hψ : ∀ g, ψ (ψ g) = g) {E : Multiplicative V ≃* HMod n F}
    (hE : ∀ g u, E (Multiplicative.ofAdd (repOfHom L π g u)) =
      rho hK (ψ g) (E (Multiplicative.ofAdd u))) (g : SL(3, F)) (u : V) :
    hmu E (((π (ψ g) : ↥L) : GLV V) u) = tw n (g : Matrix (Fin 3) (Fin 3) F) (hmu E u) := by
  have h := hE (ψ g) u
  rw [hψ] at h
  rw [hmu_apply, hmu_apply]
  have h' : E (Multiplicative.ofAdd (((π (ψ g) : ↥L) : GLV V) u)) =
      rho hK g (E (Multiplicative.ofAdd u)) := h
  rw [h', mat_rho]

theorem tw_transvection_block (j : Fin 3) (hj : (0 : Fin 3) ≠ j) (a : F)
    (X : Matrix (Fin 3) (Fin 3) F) {i i' : Fin 3} (hi : i ≠ 0) (hi' : i' ≠ 0) :
    tw n (transvection 0 j a) X i i' = X i i' := by
  fin_cases i <;> fin_cases i' <;> fin_cases j <;>
    simp_all [tw, conjM, Matrix.mul_apply, transvection, Matrix.one_apply]

@[expose] def radSet {L : Subgroup (GLV V)} (π : SL(3, F) →* ↥L) (ψ : SL(3, F) →* SL(3, F)) :
    Set (GLV V) :=
  {q | ∃ (j : Fin 3) (hj : (0 : Fin 3) ≠ j) (a : F), q = ((π (ψ (upTv j hj a)) : ↥L) : GLV V)}

theorem radSet_subset {L : Subgroup (GLV V)} (π : SL(3, F) →* ↥L) (ψ : SL(3, F) →* SL(3, F)) :
    radSet π ψ ⊆ (L : Set (GLV V)) := by
  rintro q ⟨j, hj, a, rfl⟩
  exact (π _).2

structure HermQ (E : Multiplicative V ≃* HMod n F) (Q : Set (GLV V)) : Prop where
  act : ∀ q ∈ Q, ∃ (j : Fin 3) (_ : (0 : Fin 3) ≠ j) (a : F),
    ∀ u, hmu E ((q : GLV V) u) = tw n (transvection 0 j a) (hmu E u)
  exists_act : ∀ (j : Fin 3) (_ : (0 : Fin 3) ≠ j) (a : F), ∃ q ∈ Q,
    ∀ u, hmu E ((q : GLV V) u) = tw n (transvection 0 j a) (hmu E u)

theorem hermQ_radSet {L : Subgroup (GLV V)} {π : SL(3, F) →* ↥L} (hK : Nat.card F = (2 ^ n) ^ 2)
    {ψ : SL(3, F) →* SL(3, F)} (hψ : ∀ g, ψ (ψ g) = g) {E : Multiplicative V ≃* HMod n F}
    (hE : ∀ g u, E (Multiplicative.ofAdd (repOfHom L π g u)) =
      rho hK (ψ g) (E (Multiplicative.ofAdd u))) : HermQ E (radSet π ψ) where
  act := by
    rintro q ⟨j, hj, a, rfl⟩
    exact ⟨j, hj, a, fun u => hmu_act hK hψ hE (upTv j hj a) u⟩
  exists_act j hj a := ⟨_, ⟨j, hj, a, rfl⟩, fun u => hmu_act hK hψ hE (upTv j hj a) u⟩

theorem hmu_eq_zero_of_fixed (hn : 1 ≤ n) (hK : Nat.card F = (2 ^ n) ^ 2)
    {E : Multiplicative V ≃* HMod n F} {Q : Set (GLV V)} (hQ : HermQ E Q) {u : V}
    (hu : ∀ q ∈ Q, (q : GLV V) u = u) (i j : Fin 3) (hij : ¬ (i = 0 ∧ j = 0)) :
    hmu E u i j = 0 := by
  have key : ∀ (j : Fin 3) (hj : (0 : Fin 3) ≠ j) (a : F),
      rhoT hK (trGL (0 : Fin 3) j hj a) (E (Multiplicative.ofAdd u)) =
        E (Multiplicative.ofAdd u) := by
    intro j hj a
    obtain ⟨q, hq, hq'⟩ := hQ.exists_act j hj a
    apply mat_injective
    rw [mat_rhoT, coe_trGL]
    have := hq' u
    rw [hu q hq] at this
    exact this.symm
  exact eq_zero_of_fix hn hK (X := E (Multiplicative.ofAdd u)) (key 1 (by decide))
    (key 2 (by decide)) i j hij

theorem hmu_sub_block {E : Multiplicative V ≃* HMod n F} {Q : Set (GLV V)} (hQ : HermQ E Q)
    {q : GLV V} (hq : q ∈ Q) (v : V) {i i' : Fin 3} (hi : i ≠ 0) (hi' : i' ≠ 0) :
    hmu E (q v - v) i i' = 0 := by
  obtain ⟨j, hj, a, h⟩ := hQ.act q hq
  rw [map_sub, h v, Matrix.sub_apply, tw_transvection_block j hj a _ hi hi', sub_self]

@[expose] def lowerBlock : Matrix (Fin 3) (Fin 3) F →+ (Fin 2 → Fin 2 → F) where
  toFun X i j := X i.succ j.succ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem card_fixed_le_herm (hn : 1 ≤ n) (hK : Nat.card F = (2 ^ n) ^ 2)
    {E : Multiplicative V ≃* HMod n F} {Q : Set (GLV V)} (hQ : HermQ E Q) :
    Nat.card {y : V // ∀ q ∈ Q, (q : GLV V) y = y} ≤ 2 ^ n := by
  rw [← card_fixed hn hK]
  refine Nat.card_le_card_of_injective
    (fun y => (⟨hmu E y.1 0 0, hmu_bar E y.1 0 0⟩ : {b : F // bar n b = b})) fun a b hab => ?_
  have h00 : hmu E a.1 0 0 = hmu E b.1 0 0 := congrArg Subtype.val hab
  apply Subtype.ext
  apply hmu_injective E
  ext i j
  by_cases hij : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij
    exact h00
  · rw [hmu_eq_zero_of_fixed hn hK hQ a.2 i j hij, hmu_eq_zero_of_fixed hn hK hQ b.2 i j hij]

theorem card_block_le (hn : 1 ≤ n) (hK : Nat.card F = (2 ^ n) ^ 2)
    (E : Multiplicative V ≃* HMod n F) :
    Nat.card (kerSub (lowerBlock.comp (hmu E))) ≤ 2 ^ (5 * n) := by
  have hcard : Nat.card ({b : F // bar n b = b} × F × F) = 2 ^ (5 * n) := by
    rw [Nat.card_prod, Nat.card_prod, card_fixed hn hK, hK]
    ring
  rw [← hcard]
  refine Nat.card_le_card_of_injective
    (fun w => ((⟨hmu E w.1 0 0, hmu_bar E w.1 0 0⟩ : {b : F // bar n b = b}),
      hmu E w.1 0 1, hmu E w.1 0 2)) fun a b hab => ?_
  have hz : ∀ w : kerSub (lowerBlock.comp (hmu E)), ∀ i i' : Fin 3, i ≠ 0 → i' ≠ 0 →
      hmu E w.1 i i' = 0 := by
    intro w i i' hi hi'
    have := (mem_kerSub _ _).1 w.2
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hi
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi'
    exact congrFun (congrFun this i) i'
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
  obtain ⟨h00, h01, h02⟩ := hab
  apply Subtype.ext
  apply hmu_injective E
  ext i j
  have h10 : hmu E a.1 1 0 = hmu E b.1 1 0 := by
    rw [← hmu_bar E a.1 1 0, ← hmu_bar E b.1 1 0, h01]
  have h20 : hmu E a.1 2 0 = hmu E b.1 2 0 := by
    rw [← hmu_bar E a.1 2 0, ← hmu_bar E b.1 2 0, h02]
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h02
  · exact h10
  · exact (hz a 1 1 (by decide) (by decide)).trans (hz b 1 1 (by decide) (by decide)).symm
  · exact (hz a 1 2 (by decide) (by decide)).trans (hz b 1 2 (by decide) (by decide)).symm
  · exact h20
  · exact (hz a 2 1 (by decide) (by decide)).trans (hz b 2 1 (by decide) (by decide)).symm
  · exact (hz a 2 2 (by decide) (by decide)).trans (hz b 2 2 (by decide) (by decide)).symm

theorem not_selfDual_herm [Finite V] {L : Subgroup (GLV V)} (hn : 1 ≤ n)
    (hK : Nat.card F = (2 ^ n) ^ 2) {E : Multiplicative V ≃* HMod n F} {Q : Set (GLV V)}
    (hQ : HermQ E Q) (hQL : Q ⊆ (L : Set (GLV V))) (hV : Nat.card V = 2 ^ (9 * n)) :
    ¬ SelfDual L ⊤ := by
  intro hsd
  have hW : ∀ q ∈ Q, ∀ v, (q : GLV V) v - v ∈ kerSub (lowerBlock.comp (hmu E)) := by
    intro q hq v
    rw [mem_kerSub]
    ext i j
    exact hmu_sub_block hQ hq v (Fin.succ_ne_zero i) (Fin.succ_ne_zero j)
  have h1 := card_le_mul_card_fixed hsd Q hQL _ hW
  have h2 := Nat.mul_le_mul (card_block_le hn hK E) (card_fixed_le_herm hn hK hQ)
  rw [hV] at h1
  have h3 : 2 ^ (9 * n) ≤ 2 ^ (6 * n) := by
    calc 2 ^ (9 * n) ≤ _ := h1
      _ ≤ 2 ^ (5 * n) * 2 ^ n := h2
      _ = 2 ^ (6 * n) := by rw [← pow_add]; ring_nf
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  omega

end CFSG.Quasithin.G11.Harris.L3

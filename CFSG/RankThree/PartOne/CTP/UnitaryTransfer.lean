module

public import CFSG.RankThree.PartOne.CTP.TransferGen
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open scoped MatrixGroups

section Setup

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem suid_eq_gramSU :
    SUid (unitaryInvolution K 2 f) 3 =
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [SUid_eq_statedSU h.card_eq_sq 3, Units.val_one]
  exact unitarySU_eq_gramSU h 3

@[expose] noncomputable def suEquiv :
    SUid (unitaryInvolution K 2 f) 3 ≃*
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  MulEquiv.subgroupCongr (suid_eq_gramSU h)

theorem mem_center_iff_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    e x ∈ Subgroup.center H ↔ x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul]
    exact hx (e g)
  · intro hx g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx g']

omit [Finite K] [CharP K 2] in
theorem center_gramSU_one_eq (hq : 4 ≤ 2 ^ f) :
    Subgroup.center (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3 := by
  have hn : 3 ≤ 3 := le_rfl
  have hnq : ¬ (3 = 3 ∧ 2 ^ f = 2) := by rintro ⟨-, h2⟩; omega
  refine le_antisymm (fun z hz => ?_) (normOneScalars_le_center h _ 3)
  have hsimple := CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h hn hnq
  have hnc := CFSG.RankThree.Classical.not_commute_primeFormP_one h hn hnq
  have hzc : (QuotientGroup.mk z : primeFormP h ((1 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz g']
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (primeFormP h ((1 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K))) with hb | ht
  · rw [hb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzc
    exact hzc
  · exfalso
    apply hnc
    intro x y
    have hx : x ∈ Subgroup.center (primeFormP h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) := by rw [ht]; trivial
    exact (Subgroup.mem_center_iff.mp hx y).symm

@[expose] noncomputable def suProj :
    SUid (unitaryInvolution K 2 f) 3 →*
      primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  (QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3)).comp (suEquiv h).toMonoidHom

theorem suProj_surjective : Function.Surjective (suProj h) :=
  (QuotientGroup.mk'_surjective _).comp (suEquiv h).surjective

theorem suProj_ker (hq : 4 ≤ 2 ^ f) :
    (suProj h).ker = Subgroup.center (SUid (unitaryInvolution K 2 f) 3) := by
  ext x
  rw [MonoidHom.mem_ker, ← mem_center_iff_of_mulEquiv (suEquiv h), center_gramSU_one_eq h hq]
  change (QuotientGroup.mk' _) (suEquiv h x) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

include h in
theorem isPerfect_suid (hq : 4 ≤ 2 ^ f) :
    Group.IsPerfect (SUid (unitaryInvolution K 2 f) 3) := by
  have hnq : ¬ (3 = 3 ∧ 2 ^ f = 2) := by rintro ⟨-, h2⟩; omega
  have := CFSG.RankThree.Classical.isPerfect_gramSU_one h le_rfl hnq
  exact Group.IsPerfect.ofSurjective (f := (suEquiv h).symm.toMonoidHom)
    (suEquiv h).symm.surjective

theorem card_center_eq_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Subgroup.center G) = Nat.card (Subgroup.center H) :=
  Nat.card_congr
    { toFun := fun x => ⟨e x, (mem_center_iff_of_mulEquiv e x).mpr x.2⟩
      invFun := fun y => ⟨e.symm y, (mem_center_iff_of_mulEquiv e (e.symm y)).mp (by simp)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

include h in
theorem card_center_suid_odd (hq : 4 ≤ 2 ^ f) :
    ¬ 2 ∣ Nat.card (Subgroup.center (SUid (unitaryInvolution K 2 f) 3)) := by
  rw [card_center_eq_of_mulEquiv (suEquiv h), center_gramSU_one_eq h hq,
    CFSG.RankThree.Classical.card_normOneScalars_one h (by norm_num)]
  intro h2
  have := h2.trans (Nat.gcd_dvd_left 3 (2 ^ f + 1))
  omega

theorem edge_half_unitary (hq : 4 ≤ 2 ^ f) {G : Type} [Group G]
    (θ : SUid (unitaryInvolution K 2 f) 3 →* G) (hker : θ.ker ≤ Subgroup.center _) {r : ℕ}
    (hr : r.Prime) {E A B : Subgroup G} [CFSG.IsElementaryAbelian r E]
    (hE : EdgeTorus r E A B) (hAB : A ⊔ B = θ.range) {KA KB : Type} [Field KA] [Field KB]
    [CharP KB 2] (ρA : SL(2, KA) ≃* ↥A) (ρB : SL(2, KB) ≃* ↥B)
    (φA : SL(2, KA) →* SUid (unitaryInvolution K 2 f) 3)
    (φB : SL(2, KB) →* SUid (unitaryInvolution K 2 f) 3)
    (hφA : ∀ a, θ (φA a) = (ρA a : G)) (hφB : ∀ b, θ (φB b) = (ρB b : G)) :
    ∃ α : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      α ^ r = 1 ∧ (∀ a, α (suProj h (φA a)) = suProj h (φA a)) ∧
      (∀ b, ∃ b', α (suProj h (φB b)) = suProj h (φB b')) ∧
      ∃ b, α (suProj h (φB b)) ≠ suProj h (φB b) := by
  have := isPerfect_suid h hq
  exact edge_half_gen θ (suProj_ker h hq) (suProj_surjective h) hker hr hE hAB ρA ρB φA φB hφA hφB

include h in
theorem exists_sl2_lift_unitary (hq : 4 ≤ 2 ^ f) {G : Type} [Group G]
    (θ : SUid (unitaryInvolution K 2 f) 3 →* G) (hker : θ.ker ≤ Subgroup.center _)
    {KA : Type} [Field KA] [Finite KA] [CharP KA 2] {C : Subgroup G} (hC : C ≤ θ.range)
    (ρ : SL(2, KA) →* ↥C) :
    ∃ φ : SL(2, KA) →* SUid (unitaryInvolution K 2 f) 3, ∀ a, θ (φ a) = (ρ a : G) :=
  exists_sl2_lift_gen θ hker (card_center_suid_odd h hq) hC ρ

end Setup

end CFSG.RankThree.PartOne.CTP

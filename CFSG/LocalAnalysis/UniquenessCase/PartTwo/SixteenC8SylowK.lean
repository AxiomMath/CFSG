module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Defs
import CFSG.CharacterTheory.Semidihedral.PrimeOrderCyclicConfinementLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c8_sp6InL_normalizer (D : Data G) {L T₀ K C : Subgroup G} {v₀ : G}
    (hK : Sp6InL D L v₀ T₀ K) (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hCK : C ≤ K)
    (hCn : (C.subgroupOf K).Normal) : Sp6InL D L v₀ T₀ (normalizer (C : Set G)) := by
  have hKN : K ≤ normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).mp hCn
  exact ⟨hK.1.trans hKN, hK.2.1.trans hKN, fun h => hK.2.2.1 (hKN.trans h),
    D.standing.charTwo _ ⟨C, hC1, hC2, rfl⟩⟩

private theorem mem_normalizer_of_subgroupOf_of_le {X : Type*} [Group X] {A C : Subgroup X}
    (hAC : A ≤ C) {y : C}
    (hy : y ∈ Subgroup.normalizer ((A.subgroupOf C : Subgroup C) : Set C)) :
    (y : X) ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (Subgroup.mem_normalizer_iff.mp hy ⟨x, hAC hx⟩).mp
      (show (⟨x, hAC hx⟩ : C) ∈ A.subgroupOf C from hx)
  · intro hx
    have hxC : x ∈ C := by
      have e : x = (y : X)⁻¹ * ((y : X) * x * (y : X)⁻¹) * y := by group
      rw [e]
      exact C.mul_mem (C.mul_mem (C.inv_mem y.2) (hAC hx)) y.2
    exact (Subgroup.mem_normalizer_iff.mp hy ⟨x, hxC⟩).mpr hx

private theorem lt_inf_normalizer_of_isPGroup {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {R Q : Subgroup X} (hQ : IsPGroup p Q) (hRQ : R ≤ Q)
    (hne : R ≠ Q) : R < Q ⊓ Subgroup.normalizer (R : Set X) := by
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : R.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hRQ ?_)
    intro x hx
    have : (⟨x, hx⟩ : Q) ∈ R.subgroupOf Q := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨x, hxN, hxR⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (R.subgroupOf Q) hlt)
  refine lt_of_le_of_ne (le_inf hRQ Subgroup.le_normalizer) fun h => hxR ?_
  have hx' : (x : X) ∈ Q ⊓ Subgroup.normalizer (R : Set X) :=
    ⟨x.2, mem_normalizer_of_subgroupOf_of_le hRQ hxN⟩
  rw [← h] at hx'
  exact hx'

private theorem card_eq_prime_pow_padicValNat {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hP : IsPGroup p P) :
    Nat.card P = p ^ padicValNat p (Nat.card P) := by
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hP
  rw [hn, padicValNat.prime_pow]

private theorem padicValNat_le_of_dvd {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).mp ((pow_padicValNat_dvd (p := p) (n := a)).trans h)

private theorem padicValNat_card_lt_of_lt_of_isPGroup {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {P Q : Subgroup X} (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (h : P < Q) : padicValNat p (Nat.card P) < padicValNat p (Nat.card Q) := by
  have hcard : Nat.card P < Nat.card Q := Subgroup.card_lt_of_lt h
  rw [card_eq_prime_pow_padicValNat hP, card_eq_prime_pow_padicValNat hQ] at hcard
  exact (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).mp hcard

theorem c8_le_of_charNormal (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {v₀ : IntMod V hV} {T₀ K T' : Subgroup G} (hU : C8SetUp D V₀ V L hV v₀ T₀ K T')
    {C : Subgroup G} (hC1 : C ≠ ⊥) (hCS : C ≤ T' ⊓ K)
    (hCchar : (C.subgroupOf (T' ⊓ K)).Characteristic) (hCn : (C.subgroupOf K).Normal) :
    T' ≤ K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subgroup G := T' ⊓ K
  let N : Subgroup G := Subgroup.normalizer (C : Set G)
  have hS : S = T' ⊓ K := rfl
  by_contra hTK
  have hT'M : T' ≤ D.M := hU.sylowM.le
  have hT'2 : IsPGroup 2 T' := hU.sylowM.isPGroup
  have hST' : S ≤ T' := (le_of_eq hS).trans inf_le_left
  have hS2 : IsPGroup 2 S := hT'2.to_le hST'
  have hCS' : C ≤ S := hCS.trans (le_of_eq hS.symm)
  have hCchar' : (C.subgroupOf S).Characteristic := hCchar
  have hC2 : IsPGroup 2 C := hT'2.to_le (hCS.trans inf_le_left)
  have hNmem : Sp6InL D L v₀.val T₀ N :=
    c8_sp6InL_normalizer D hU.mem hC1 hC2 (hCS.trans inf_le_right) hCn
  have hmaxN : padicValNat 2 (Nat.card ↥(N ⊓ D.M)) ≤
      padicValNat 2 (Nat.card ↥(K ⊓ D.M)) := hU.max N hNmem
  have hcardK : padicValNat 2 (Nat.card ↥(K ⊓ D.M)) = padicValNat 2 (Nat.card ↥S) := by
    have h1 : Nat.card ↥(T' ⊓ K) = 2 ^ (Nat.card ↥(D.M ⊓ K)).factorization 2 :=
      IsSylowIn.card_eq hU.sylowK
    rw [hS, show K ⊓ D.M = D.M ⊓ K from inf_comm K D.M,
      ← Nat.factorization_def (Nat.card ↥(D.M ⊓ K)) Nat.prime_two, h1, padicValNat.prime_pow]
  have hSne : S ≠ T' := fun h => hTK (inf_eq_left.mp (hS.symm.trans h))
  have hltS : S < T' ⊓ Subgroup.normalizer (S : Set G) :=
    lt_inf_normalizer_of_isPGroup (R := S) (Q := T') hT'2 hST' hSne
  have hN₁le : T' ⊓ Subgroup.normalizer (S : Set G) ≤ N ⊓ D.M :=
    le_inf (inf_le_right.trans
      (CFSG.Semidihedral.PrimeOrderCyclicConfinementLift.normalizer_le_of_characteristic_subgroupOf
        hCS' hCchar')) (inf_le_left.trans hT'M)
  have hN₁2 : IsPGroup 2 ↥(T' ⊓ Subgroup.normalizer (S : Set G)) := hT'2.to_le inf_le_left
  have hlt2 : padicValNat 2 (Nat.card ↥S) < padicValNat 2 (Nat.card ↥(N ⊓ D.M)) :=
    lt_of_lt_of_le
      (padicValNat_card_lt_of_lt_of_isPGroup (P := S) (Q := T' ⊓ Subgroup.normalizer (S : Set G))
        hS2 hN₁2 hltS)
      (padicValNat_le_of_dvd (Nat.card_pos.ne') (Subgroup.card_dvd_of_le hN₁le))
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

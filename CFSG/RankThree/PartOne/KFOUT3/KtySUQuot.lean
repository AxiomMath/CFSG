module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KFOUT3.KtyAt
public import CFSG.RankThree.PartOne.KFOUT3.KtyLift

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne.KFU
open scoped commutatorElement

section Perfect

variable {G A : Type*} [Group G] [CommGroup A]

theorem perfect_le_ker (φ : G →* A) {T : Subgroup G} (hT : Group.IsPerfect T) : T ≤ φ.ker := by
  have h : ⁅T, T⁆ = T := Subgroup.isPerfect_iff.mp hT
  rw [← h, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

end Perfect

section Quot

variable {M Q : Type} [Group M] [Group Q] {p : ℕ} {q : M →* Q}

theorem bigAt_of_central (hp : p.Prime) (hq : IsCentralPQuot p q) {u : M} (hu : u ^ p = 1)
    {S₀ : Subgroup M} (hperf : Group.IsPerfect S₀) (hsimple : IsSimpleGroup S₀)
    (hord : ∃ s ∈ S₀, orderOf s = p) (hc : ∀ s ∈ S₀, u * s = s * u)
    (hn : ∀ x : M, u * x = x * u → ∀ s ∈ S₀, x * s * x⁻¹ ∈ S₀) {R : ℕ → Prop}
    (hR : R (Nat.card S₀)) : BigAt p (q u) R := by
  classical
  let qS : ↥S₀ →* Q := q.comp S₀.subtype
  have hinj : Function.Injective qS := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases (MonoidHom.normal_ker qS).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨s, hs, hsp⟩ := hord
      have hmem : (⟨s, hs⟩ : S₀) ∈ qS.ker := by rw [h]; trivial
      have hs1 : s ∈ q.ker := hmem
      have hspow : s ^ p = 1 := by rw [← hsp]; exact pow_orderOf_eq_one s
      have h1 := hq.eq_one_of_pow_eq_one hs1 hspow
      rw [h1, orderOf_one] at hsp
      exact hp.ne_one hsp.symm
  let e : ↥S₀ ≃* ↥(S₀.map q) :=
    MulEquiv.ofBijective (q.subgroupMap S₀) ⟨fun x y hxy => hinj (by
        have := congrArg Subtype.val hxy
        exact this), q.subgroupMap_surjective S₀⟩
  have h1 : Group.IsPerfect (S₀.map q) := by
    have := hperf
    exact Group.IsPerfect.map q
  refine ⟨S₀.map q, h1, e.symm.isSimpleGroup, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hsp⟩ := hord
    refine ⟨q s, Subgroup.mem_map_of_mem q hs, ?_⟩
    have := orderOf_injective qS hinj ⟨s, hs⟩
    rw [Subgroup.orderOf_mk] at this
    rw [← hsp]
    exact this
  · rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hc s hs]
  · intro x hx
    obtain ⟨m, rfl⟩ := hq.surjective x
    have hcomm : Commute u m := hq.commute_of_map_commute hu hx
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨m * s * m⁻¹, hn m hcomm.eq s hs, by simp⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact hR

theorem smallAt_of_central (hq : IsCentralPQuot p q) {u : M} (hu : u ^ p = 1) {R : ℕ → Prop}
    (h : ∀ T : Subgroup M, Group.IsPerfect T → (∀ τ ∈ T, u * τ = τ * u) → ∀ m, R m →
      ¬ m ∣ Nat.card T) : SmallAt (q u) R := by
  intro T hT hTc m hm hdvd
  have hSY : ∀ σ ∈ T, ∃ y ∈ Subgroup.centralizer ({u} : Set M), q y = σ := by
    intro σ hσ
    obtain ⟨y, rfl⟩ := hq.surjective σ
    refine ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (hq.commute_of_map_commute hu (hTc _ hσ)).eq
  obtain ⟨P, hPY, hPT, hPperf, -⟩ := exists_perfect_lift_core hq hSY hT
  have hP : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hPperf
  refine h P hP (fun τ hτ => ?_) m hm ?_
  · have := Subgroup.mem_centralizer_iff.mp (hPY hτ) u (Set.mem_singleton u)
    exact this
  · have h1 : Nat.card T ∣ Nat.card P := by
      rw [← hPT]
      exact Subgroup.card_map_dvd P q
    exact hdvd.trans h1

end Quot

end CFSG.RankThree.PartOne.KFOUT3

module

public import CFSG.RankThree.PartTwo.Sec21.Hering214ERank
public import CFSG.RankThree.PartTwo.Sec21.Hering214EV
import CFSG.RankThree.PartTwo.Sec21.HeringFFLLiftP
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (localRank)
open Item211Res2Proof
open scoped commutatorElement

@[expose] def EvenThetaFacts (X : Type) [Group X] : Prop :=
  Subgroup.center X = ⊥ ∧
  (∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range) ∧
  (∃ Q : Subgroup X, IsElemAbelian 3 Q ∧ Nat.card Q = 9) ∧
  ∀ Ē Ū : Subgroup (MulAut X), Ē ≤ (MulAut.conj : X →* MulAut X).range → IsElemAbelian 3 Ē →
    Nat.card Ē = 9 → IsElemAbelian 2 Ū → Ū ≠ ⊥ → Nat.card Ū ≤ 4 →
    (∀ u ∈ Ū, ∀ e ∈ Ē, u * e = e * u) →
    Ē ≤ ⁅(MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (Ū : Set (MulAut X)),
      (MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (Ū : Set (MulAut X))⁆ ∧
    ∀ P : Subgroup (MulAut X), IsPGroup 2 P →
      P ≤ ⁅(MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (Ū : Set (MulAut X)),
        (MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (Ū : Set (MulAut X))⁆ →
      ⁅(MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (Ū : Set (MulAut X)),
        (MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (Ū : Set (MulAut X))⁆ ≤
          Subgroup.normalizer (P : Set (MulAut X)) → P = ⊥

variable {G : Type} [Group G] [Finite G]

private theorem isElemAbelian_map_subtype {L : Subgroup G} {p : ℕ} {Q : Subgroup L}
    (hQ : IsElemAbelian p Q) : IsElemAbelian p (Q.map L.subtype) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    have h' := congrArg (fun w : Q => ((w : L) : G)) (hQ.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul] at h'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb]
    exact h'
  · obtain ⟨x', hx', rfl⟩ := hx
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hQ.2 x' hx', Subgroup.coe_one]

theorem false_of_even_of_facts {A E U L : Subgroup G} {c : G}
    (hPF : Item211LieProof.PairFacts A E U c L) (h3 : localRank 3 G ≤ 3) [Group.IsPerfect L]
    (hθc : aschbacherSolvableCore 3 L ≤ Subgroup.center L)
    (hnotdec : ¬ (U ∈ fourGroupsMinus E ∧ ∀ e ∈ E, ∃ x ∈ E ⊓ Subgroup.centralizer (U : Set G),
      ∃ y ∈ E ⊓ L, e = x * y))
    (heven : Even (Nat.card (aschbacherSolvableCore 3 L))) (hF : EvenThetaFacts (lBar L)) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ, hF1, ⟨Qb, hQb, hQb9⟩, hF3⟩ := hF
  obtain ⟨-, hTch, hT3, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
    Nat.prime_three
  have hZθ : Subgroup.center L ≤ aschbacherSolvableCore 3 L := by
    intro z hz
    have hmk : (z : lBar L) ∈ Subgroup.center (lBar L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ, Subgroup.mem_bot] at hmk
    exact (QuotientGroup.eq_one_iff z).mp hmk
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center L) := fun h =>
    hT3 (h.trans (Subgroup.card_dvd_of_le hZθ))
  have hinn : barImage L E ≤ (MulAut.conj : lBar L →* MulAut (lBar L)).range := fun τ hτ =>
    hF1 τ ((Item211LieProof.isElemAbelian_barImage_E hPF).2 τ hτ)
  have hQ : ∃ Q : Subgroup G, Q ≤ L ∧ IsElemAbelian 3 Q ∧ Nat.card Q = 9 := by
    haveI : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
    obtain ⟨Q, hQe, hQc⟩ := exists_elemAbelian_of_quotient (aschbacherSolvableCore 3 ↥L) hT3 hQb
    refine ⟨Q.map L.subtype, Subgroup.map_subtype_le Q, isElemAbelian_map_subtype hQe, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective, hQc, hQb9]
  obtain ⟨-, hdec⟩ := forall_eq_zpow_mul_of_even hPF h3 hθc heven hinn hZ3 hQ
  have hU : U ∈ fourGroups E := mem_fourGroups_iff.mpr ⟨hPF.EU, hPF.Ue, hPF.U4⟩
  rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus (fun e he => hPF.Ee.2 e he) hU with hP | hM
  ·
    have hUE : ⁅U, E⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro u hu e he
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp ((mem_fourGroupsPlus_iff.mp hP).2 he) u hu
    have hU4 : Nat.card (barImage L U) ≤ 4 := by
      have h4 := Item211LieProof.card_barImage_U_mul hPF
      exact Nat.le_of_dvd (by norm_num) (Dvd.intro _ h4)
    obtain ⟨hED, hO2⟩ := hF3 (barImage L E) (barImage L U) hinn
      (Item211LieProof.isElemAbelian_barImage_E hPF) (Item211LieProof.card_barImage_E hPF)
      (Item211LieProof.isElemAbelian_barImage_U hPF) (Item211LieProof.barImage_U_ne_bot hPF) hU4
      (Item211LieProof.barImage_U_comm_E_of_plus hP)
    exact false_of_comm_eq_bot hPF hUE hθc hZ hED hO2
  ·
    refine hnotdec ⟨hM, fun e he => ?_⟩
    obtain ⟨k, y, hy, rfl⟩ := hdec e he
    exact ⟨c ^ k, ⟨E.zpow_mem hPF.cE k, Subgroup.zpow_mem _ hPF.cU k⟩, y, hy, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214Even

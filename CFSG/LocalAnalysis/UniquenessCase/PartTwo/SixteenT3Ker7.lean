module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Ker
public import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

variable {T : Type} [CommGroup T] [Finite T]

theorem s16t_pGroup_fix_family {p : ℕ} [Fact p.Prime] {X Q : Subgroup (MulAut T)} (hQX : Q ≤ X)
    (hQ : IsPGroup p ↥Q) {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hlt : Fintype.card ι < p)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) :
    ∀ q ∈ Q, ∀ i, (Y i).map q.toMonoidHom = Y i := by
  classical
  intro q hq i
  have hsmul : ∀ (g : MulAut T) (S : Subgroup T), g • S = S.map g.toMonoidHom := by
    intro g S
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hsub : MulAction.orbit ↥Q (Y i) ⊆ Set.range Y := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨j, hj⟩ := hperm g (hQX hg) i
    exact ⟨j, by rw [← hj]; exact (hsmul g (Y i)).symm⟩
  obtain ⟨n, hn⟩ := hQ.card_orbit (Y i)
  have hle : Nat.card ↥(MulAction.orbit ↥Q (Y i)) ≤ Fintype.card ι := by
    calc Nat.card ↥(MulAction.orbit ↥Q (Y i)) ≤ Nat.card ↥(Set.range Y) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ ≤ Fintype.card ι := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_range_le Y
  have hn0 : n = 0 := by
    by_contra hn0
    have hp : p ≤ p ^ n := Nat.le_self_pow hn0 p
    omega
  have h1 : Nat.card ↥(MulAction.orbit ↥Q (Y i)) = 1 := by rw [hn, hn0, pow_zero]
  have hsingle : ∀ g : ↥Q, g • Y i = Y i := by
    intro g
    have hmem1 : g • Y i ∈ MulAction.orbit ↥Q (Y i) := MulAction.mem_orbit _ g
    have hmem2 : Y i ∈ MulAction.orbit ↥Q (Y i) := MulAction.mem_orbit_self _
    obtain ⟨hss, -⟩ := Nat.card_eq_one_iff_unique.1 h1
    exact congrArg Subtype.val (hss.elim ⟨_, hmem1⟩ ⟨_, hmem2⟩)
  exact (hsmul q (Y i)).symm.trans (hsingle ⟨q, hq⟩)

private theorem s16t_ker7_card_rank {X : Type} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem s16t_ker7_rank_comm_pow {p n : ℕ} {P : Type} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

theorem s16t_ker7_exists_Q {X A : Subgroup (MulAut T)} {r : ℕ} (hT : ∀ t : T, t ^ 2 = 1)
    (hr : 1 < r) (hA : IsElemAbelianOfRank 7 r ↥A) (hAP : A ≤ pCoreOf 7 X) {ι : Type}
    [Fintype ι] {Y : ι → Subgroup T} (hind : iSupIndep Y) (hinj : Function.Injective Y)
    (hsup : ⨆ i, Y i = ⊤) (hcard : Fintype.card ι = r + 1) (hrk : ∀ i, rk ↥(Y i) = dParam 7)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    (hsurj : ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i)) :
    ∃ Q : Subgroup (MulAut T), Q ≤ X ∧ IsPGroup 7 ↥Q ∧ Q ≠ ⊥ ∧
      (∀ φ ∈ X, Q.map (MulAut.conj φ).toMonoidHom = Q) ∧
      ∀ q ∈ Q, ∀ i, (Y i).map q.toMonoidHom = Y i := by
  classical
  have hAX : A ≤ X := hAP.trans (Subgroup.map_subtype_le _)
  by_cases hr3 : 3 ≤ r
  · have hcp := s16t_ker7_rank_comm_pow hA
    have hAel : IsElemAbelian 7 A := by
      refine ⟨isMulCommutative_iff.2 hcp.1, fun x hx => ?_⟩
      simpa using congrArg Subtype.val (hcp.2 ⟨x, hx⟩)
    have hge : 3 ≤ CFSG.Open.pRank 7 X :=
      hr3.trans (CFSG.SectionRank.le_pRank (by norm_num) hAX hAel (s16t_ker7_card_rank hA))
    obtain ⟨-, -, -, -, -, hQ⟩ := s16n9b_case4_kernel hT (Or.inr rfl) hr hA hAP hge hind hinj
      hsup hcard hrk hperm hsurj
    exact hQ rfl
  · have hr2 : r = 2 := by omega
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hQp : IsPGroup 7 ↥(pCoreOf 7 X) :=
      CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 7 X
    have hQne : pCoreOf 7 X ≠ ⊥ := by
      intro hbot
      have hAcard : Nat.card ↥A = 7 ^ r := s16t_ker7_card_rank hA
      have hA1 : A = ⊥ := le_bot_iff.1 (hbot ▸ hAP)
      rw [hA1, Subgroup.card_bot] at hAcard
      have : 1 < 7 ^ r := one_lt_pow' (by norm_num) (by omega)
      omega
    have hQnorm : ∀ φ ∈ X, (pCoreOf 7 X).map (MulAut.conj φ).toMonoidHom = pCoreOf 7 X := by
      intro φ hφ
      apply le_antisymm
      · rintro _ ⟨o, ho, rfl⟩
        exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hφ ho
      · intro o ho
        refine ⟨φ⁻¹ * o * φ, ?_, ?_⟩
        · simpa using CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (X.inv_mem hφ) ho
        · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
          group
    refine ⟨pCoreOf 7 X, Subgroup.map_subtype_le _, hQp, hQne, hQnorm, ?_⟩
    exact s16t_pGroup_fix_family (Subgroup.map_subtype_le _) hQp
      (by rw [hcard, hr2]; norm_num) hperm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

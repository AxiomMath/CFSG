module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105SuzukiRep
import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKlein
import CFSG.LieType.TwoRank.GLElementaryAbelian
import CFSG.Adapters.StatedPSLTwo
public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2

open Subgroup
open CFSG.GH74.Uniqueness.Hering (centralInvolutions conj_mem_centralInvolutions)
open scoped MatrixGroups

theorem card_le_two_pow_finrank {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] {M : Subgroup (Module.End L V)ˣ}
    (hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (hM2 : ∀ x ∈ M, x ^ 2 = 1) :
    Nat.card M ≤ 2 ^ Module.finrank L V := by
  classical
  let b := Module.finBasisOfFinrankEq L V rfl
  let e : (Module.End L V)ˣ ≃* GL (Fin (Module.finrank L V)) L :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let A : Subgroup (GL (Fin (Module.finrank L V)) L) := M.map e.toMonoidHom
  have : CFSG.IsElementaryAbelian 2 A :=
    { is_comm := ⟨fun x y => by
        obtain ⟨x, ⟨a, ha, rfl⟩⟩ := x
        obtain ⟨y, ⟨c, hc, rfl⟩⟩ := y
        exact Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul, hMc a ha c hc])⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        obtain ⟨x, ⟨a, ha, rfl⟩⟩ := x
        exact Subtype.ext (by simp only [Subgroup.coe_pow, ← map_pow, hM2 a ha, map_one,
          Subgroup.coe_one]) }
  have h := CFSG.LieType.TwoRank.card_le_two_pow_of_isElementaryAbelian h2 A
  rwa [Fintype.card_fin, show Nat.card A = Nat.card M from
    Subgroup.card_map_of_injective e.injective] at h

theorem kType_of_isL2 {K : Type} [Group K] {m : ℕ} (hL : UC22.IsL2 (K ⧸ CFSG.pCore 2 K) m)
    (hm : 4 ≤ m) :
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃*
        CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))) := by
  obtain ⟨e⟩ := exists_mulEquiv_sl2_of_isL2 hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Or.inr ⟨m, by omega,
    ⟨e.trans (CFSG.RankThree.PartTwo.KFacts.KS116Proof.projSLEquiv (GaloisField 2 m))⟩⟩

theorem rep_eq_one_of_finrank_le_two {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {m : ℕ}
    (hL : UC22.IsL2 (K ⧸ CFSG.pCore 2 K) m) (hm : 4 ≤ m) {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (hV : Module.finrank L V ≤ 2) (ρ : Representation L K V) : ρ = 1 := by
  have h := CFSG.RankThree.PartTwo.Sec20.Res11.rep_eq_one_of_finrank_le_two h2 hV ρ
    (fun hnt => CFSG.RankThree.PartTwo.Sec20.Res11.exists_klein_of_kType (kType_of_isL2 hL hm)
      ρ.asGroupHom hnt)
  exact MonoidHom.ext fun k => h k

section Small


variable {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {m : ℕ}
  {L : Type*} [Field L] [IsAlgClosed L]

theorem rep_eq_one_of_finrank_le_three (hL : UC22.IsL2 (K ⧸ CFSG.pCore 2 K) m) (hm : 4 ≤ m)
    (h2 : (2 : L) ≠ 0) {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (hV : Module.finrank L V ≤ 3) (ρ : Representation L K V) : ρ = 1 := by
  rcases Nat.lt_or_ge (Module.finrank L V) 3 with h3 | h3
  · exact rep_eq_one_of_finrank_le_two hL hm h2 (by omega) ρ
  have hV3 : Module.finrank L V = 3 := by omega
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL
  have hnd := not_card_dvd_20160_of_isL2 hL hm
  set ρu := ρ.asGroupHom with hρu
  set N : Subgroup (Module.End L V)ˣ := (CFSG.pCore 2 K).map ρu with hN
  by_cases hN1 : N = ⊥
  · refine rep_eq_one_of_pCore_center hL hm h2 (by omega) ρ fun o ho => ?_
    have : ρu o ∈ N := Subgroup.mem_map_of_mem _ ho
    rw [hN1, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  have hNp : IsPGroup 2 N := CFSG.pCore_isPGroup.map ρu
  have : Finite N := Finite.of_surjective
    (fun o : CFSG.pCore 2 K => (⟨ρu o, Subgroup.mem_map_of_mem _ o.2⟩ : N))
    (by rintro ⟨_, o, ho, rfl⟩; exact ⟨⟨o, ho⟩, rfl⟩)
  obtain ⟨z, hzM, hz1⟩ := exists_mem_centralInvolutions hNp hN1
  have hnorm : ∀ k, ρu k ∈ normalizer (N : Set (Module.End L V)ˣ) := fun k =>
    Subgroup.le_normalizer_map ρu
      ⟨k, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top k, rfl⟩
  have hMn : ∀ (k : K), ∀ x ∈ centralInvolutions N,
      ρu k * x * (ρu k)⁻¹ ∈ centralInvolutions N := fun k x hx =>
    conj_mem_centralInvolutions (hnorm k) hx
  have hMN : centralInvolutions N ≤ N := fun _ hx => hx.1
  have hMc : ∀ x ∈ centralInvolutions N, ∀ y ∈ centralInvolutions N, x * y = y * x :=
    fun _ hx y hy => hx.2.1 y hy.1
  have hM2 : ∀ x ∈ centralInvolutions N, x ^ 2 = 1 := fun _ hx => hx.2.2
  have : Finite (centralInvolutions N) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hMN)
  have hcard : Nat.card (centralInvolutions N) ≤ 16 :=
    (card_le_two_pow_finrank h2 hMc hM2).trans (by rw [hV3]; norm_num)
  have hfix := conj_eq_of_elementary hS hnd ρu hMc hM2 hcard hMn
  have hzK : ∀ k, Commute (ρ k) (z : Module.End L V) := fun k => by
    have h := hfix k hzM
    have h' : ρu k * z = z * ρu k := by
      calc ρu k * z = ρu k * z * (ρu k)⁻¹ * ρu k := by group
        _ = z * ρu k := by rw [h]
    have := congrArg Units.val h'
    simpa [hρu, Representation.asGroupHom_apply, Commute, SemiconjBy] using this
  have hz2 : (z : Module.End L V) ^ 2 = 1 := by
    have := congrArg Units.val (hM2 z hzM)
    simpa using this
  have hzs : ∀ c : L, (z : Module.End L V) ≠ algebraMap L (Module.End L V) c := by
    intro c hc
    have hc2 : c ^ 2 = 1 := by
      have h := hz2
      rw [hc, ← map_pow] at h
      exact (algebraMap L (Module.End L V)).injective (by rw [h, map_one])
    have hc1 : c ≠ 1 := fun h => hz1 (Units.ext (by rw [hc, h, map_one, Units.val_one]))
    have hcm : c = -1 := by
      have : (c - 1) * (c + 1) = 0 := by ring_nf; rw [hc2]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hc1
      · exact eq_neg_of_add_eq_zero_left h
    obtain ⟨o, -, ho⟩ := hMN hzM
    have hdet : LinearMap.det (z : Module.End L V) = 1 := by
      rw [← ho, hρu, Representation.asGroupHom_apply]
      exact CFSG.RankThree.PartTwo.Sec20.Res11.det_eq_one_of_isPerfect ρ o
    rw [hc, hcm, Algebra.algebraMap_eq_smul_one, LinearMap.det_smul, hV3] at hdet
    simp only [map_one, mul_one] at hdet
    have : (2 : L) = 0 := by linear_combination -hdet
    exact h2 this
  obtain ⟨W₁, W₂, hc, hW₁, hW₂, hi₁, hi₂⟩ :=
    exists_isCompl_of_commute hzK (N := 2) (by exact_mod_cast h2) hz2 hzs
  refine eq_one_of_isCompl_of_ih (fun W hW ρ' => ?_) hc hW₁ hW₂ hi₁ hi₂
  exact rep_eq_one_of_finrank_le_two hL hm h2 (by
    have := Submodule.finrank_lt hW
    omega) ρ'

end Small

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2

module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Cited
import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def Br4Good (A : Type) [Group A] : Prop :=
  IsSimpleGroup A ∧ (∃ E : Subgroup A, IsElemAbelian 3 E ∧ Nat.card E = 9) ∧
    ∀ (J : Type) [Group J] [Finite J] (Z : Subgroup J) [Z.Normal], Z ≤ Subgroup.center J →
      IsPGroup 3 Z → ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤ →
        Nonempty ((J ⧸ Z) ≃* A) → Z = ⊥

private theorem w183br4_center_eq_bot_of_simple_perfect {S : Type} [Group S]
    (hS : IsSimpleGroup S) (hperf : Group.IsPerfect S) : Subgroup.center S = ⊥ := by
  rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative S := Subgroup.center_eq_top_iff.mp h
    haveI : Group.IsPerfect S := hperf
    haveI : Subsingleton S := inferInstance
    exact (not_subsingleton S) inferInstance

private theorem w183br4_exceptionalOrders_psl_three {s f : ℕ} (hs2 : s ≠ 2) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 s f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | simp_all

private theorem w183br4_exceptionalOrders_psp_two (p : ℕ) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 p 1 = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | simp_all

private theorem w183br4_exists_e9_of_two_le_pRank {X : Type} [Group X] [Finite X]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := E) (n := 2)
    (by rw [hcard]; exact pow_dvd_pow 3 h)
  refine ⟨D.map E.subtype, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨x, -, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, -, rfl⟩⟩ := b
    apply Subtype.ext
    change (x : X) * y = y * x
    exact congrArg Subtype.val (hE.1.is_comm.comm x y)
  · rintro _ ⟨x, -, rfl⟩
    exact hE.2 x x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hD]
    norm_num

private theorem w183br4_two_le_pRank_psp {X : Type} [Group X] [Finite X] {p : ℕ}
    (h : LieModel X .PSp 2 p 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hSCM : StatedClassicalModel X .PSp 2 p 1 := h.statedClassicalModel (by decide)
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := hSCM
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact CFSG.Quasithin.R3c3.two_le_pRank_three_statedProj_statedSp_two

private theorem w183br4_good_of_table
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    (hsimp : IsSimpleGroup X)
    (hE9 : ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9)
    (htable : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
      CFSG.Models.LieModel X t n p f ∧
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
          ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
            (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) ∣ 2) :
    Br4Good X := by
  refine ⟨hsimp, hE9, ?_⟩
  intro J _ _ Z _ hZc hZp hperf hiso
  obtain ⟨e⟩ := hiso
  haveI : Finite X := Finite.of_equiv (J ⧸ Z) e.toEquiv
  haveI hperfJ : Group.IsPerfect J := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    exact hperf
  haveI hperfX : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' Z))
      (e.surjective.comp (QuotientGroup.mk'_surjective Z))
  have hcenterX : Subgroup.center X = ⊥ :=
    w183br4_center_eq_bot_of_simple_perfect hsimp hperfX
  have hcenter_le_Z : Subgroup.center J ≤ Z := by
    intro c hc
    have hcX : e (c : J ⧸ Z) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨u, rfl⟩ := e.surjective s
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z u
      change e (a : J ⧸ Z) * e (c : J ⧸ Z) = e (c : J ⧸ Z) * e (a : J ⧸ Z)
      rw [← map_mul, ← map_mul]
      congr 1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_center_iff.mp hc a]
    rw [hcenterX, Subgroup.mem_bot] at hcX
    have h1 : (c : J ⧸ Z) = 1 := e.injective (by rw [hcX, map_one])
    exact (QuotientGroup.eq_one_iff c).mp h1
  have hZeq : Z = Subgroup.center J := le_antisymm hZc hcenter_le_Z
  obtain ⟨t, n, p, f, hm, hdvd⟩ := htable
  have hdvd' : Nat.card (Subgroup.center J) ∣ 2 :=
    (CFSG.RankThree.PartTwo.Sec21.Item221Proof.card_center_dvd_table hGA hperfJ
      ((QuotientGroup.quotientMulEquivOfEq hZeq.symm).trans e) hm).trans hdvd
  have hZdvd : Nat.card ↥Z ∣ 2 := by rwa [hZeq]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
  have hZ1 : Nat.card ↥Z = 1 := by
    have h3k : 3 ^ k ∣ 2 := by rw [← hk]; exact hZdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h3k with h | h
    · rw [hk, h]
    · exfalso
      have h3dvd : 3 ∣ 2 := by
        have h3k' : 3 ∣ 3 ^ k := dvd_pow_self 3 (by rintro rfl; norm_num at h)
        rwa [h] at h3k'
      norm_num at h3dvd
  exact Subgroup.eq_bot_of_card_eq Z hZ1

namespace Br4Good

variable {A B : Type} [Group A] [Group B]

theorem nonabelian (h : Br4Good A) : ∃ a b : A, a * b ≠ b * a := by
  by_contra hc
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => by
    by_contra hne
    exact hc ⟨a, b, hne⟩
  haveI : IsMulCommutative A := ⟨⟨hcomm⟩⟩
  have hprime : (Nat.card A).Prime := (Group.is_simple_iff_prime_card).mp h.1
  obtain ⟨E, hE, hEcard⟩ := h.2.1
  have h9 : 9 ∣ Nat.card A := by
    rw [← hEcard]
    exact Subgroup.card_subgroup_dvd_card E
  rcases hprime.eq_one_or_self_of_dvd 9 h9 with h1 | h9'
  · exact absurd h1 (by norm_num)
  · rw [← h9'] at hprime
    exact absurd hprime (by norm_num)

theorem three_dvd [Finite A] (h : Br4Good A) : 3 ∣ Nat.card A := by
  obtain ⟨E, hE, hEcard⟩ := h.2.1
  have h9 : 9 ∣ Nat.card A := by
    rw [← hEcard]
    exact Subgroup.card_subgroup_dvd_card E
  exact (by norm_num : 3 ∣ 9).trans h9

theorem of_mulEquiv (e : A ≃* B) (h : Br4Good A) : Br4Good B := by
  haveI : IsSimpleGroup A := h.1
  refine ⟨e.symm.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨E, hE, hEcard⟩ := h.2.1
    exact ⟨E.map e.toMonoidHom, IsElemAbelian.map hE e.toMonoidHom, by
      rw [Subgroup.card_map_of_injective e.injective, hEcard]⟩
  · intro J _ _ Z _ hZ hZp hperf hiso
    obtain ⟨f⟩ := hiso
    exact h.2.2 J Z hZ hZp hperf ⟨f.trans e.symm⟩

end Br4Good

theorem br4Good_of_shapeIV
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    (h : ShapeIV X) : Br4Good X := by
  rcases h with hL | ⟨p, hp, hp5, hL⟩
  ·
    have hSCM : StatedClassicalModel X .PSL 3 3 1 := hL.statedClassicalModel (by decide)
    haveI : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSCM
    refine w183br4_good_of_table hGA
      (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL) ?_ ?_
    · exact w183br4_exists_e9_of_two_le_pRank
        (CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_three_three hSCM)
    · refine ⟨.PSL, 3, 3, 1, ⟨hL.admissible, Or.inl (hL.statedClassicalModel (by decide))⟩, ?_⟩
      have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 3 1 =
          (Nat.gcd 3 (3 ^ 1 - 1), 1) := rfl
      have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 3 1 = (1, 1) :=
        w183br4_exceptionalOrders_psl_three (by norm_num)
      rw [hgen, hexc]
      simp only [Prod.fst, Prod.snd, mul_one, one_mul]
      norm_num
  ·
    have hSCM : StatedClassicalModel X .PSp 2 p 1 := hL.statedClassicalModel (by decide)
    haveI : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSCM
    refine w183br4_good_of_table hGA
      (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL) ?_ ?_
    · exact w183br4_exists_e9_of_two_le_pRank (w183br4_two_le_pRank_psp hL)
    · refine ⟨.PSp, 2, p, 1, ⟨hL.admissible, Or.inl (hL.statedClassicalModel (by decide))⟩, ?_⟩
      have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSp 2 p 1 =
          (Nat.gcd 2 (p ^ 1 - 1), 1) := rfl
      have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 p 1 = (1, 1) :=
        w183br4_exceptionalOrders_psp_two p
      rw [hgen, hexc]
      simp only [Prod.fst, Prod.snd, mul_one, one_mul]
      exact Nat.gcd_dvd_left 2 (p ^ 1 - 1)

end CFSG.LocalAnalysis.WeakClosure81

end

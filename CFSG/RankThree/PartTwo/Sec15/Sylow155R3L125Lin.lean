module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.RankThree.PartTwo.Sec4 (IsoLThreePi)
open CFSG.Open (StatedClassicalModel StatedProj StatedSL StatedSU StatedScalars)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived

private theorem model_of_isoLThreePi {S : Type} [Group S] {p e : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (he : 1 ≤ e) (hS : IsoLThreePi S p e) :
    StatedClassicalModel S .PSL 3 p e ∨ StatedClassicalModel S .PSU 3 p e := by
  have hp : p.Prime := Fact.out
  have hpe : 5 ≤ p ^ e := hp5.trans (Nat.le_self_pow (by omega) p)
  rcases hS with ⟨-, ⟨f⟩⟩ | ⟨-, ⟨f⟩⟩
  · exact Or.inl (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL
      ⟨hp, he, by norm_num, by simp, by simp⟩ f)
  · refine Or.inr (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      ⟨hp, he, le_rfl, ?_⟩ f)
    intro h
    have h2 := congrArg Prod.snd h
    simp only at h2
    omega

theorem res3L125_odd_commutator_outer {S : Type} [Group S] {p e : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (he : 1 ≤ e) (hS : IsoLThreePi S p e) :
    Odd (Nat.card (commutator (Outer S))) := by
  rcases model_of_isoLThreePi hp5 he hS with h | h
  · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
    obtain ⟨N, hcyc, hcard, hcomm⟩ := exists_linear_outer_diagonal (K := K) (n := 3) le_rfl
    let eP : S ≃* LinearFlag.projectiveSL 3 K := eK.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
    obtain ⟨M, hMc, hMcard, hMcomm⟩ := exists_comap_of_injective
      (ι := (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eP).toMonoidHom)
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eP).injective hcyc hcard hcomm
    obtain ⟨-, hd, -⟩ := derived_of_commutator_mem hMc hMcard hMcomm
    exact Odd.of_dvd_nat (by decide : Odd 3) (hd.trans (Nat.gcd_dvd_left _ _))
  · obtain ⟨⟨hp, hf, hn, h32⟩, K, _, _, hK, ⟨eK⟩⟩ := h
    have hU : UnitaryFieldData p e K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq : ¬(3 = 3 ∧ p ^ e = 2) := fun ⟨_, h2⟩ => h32 (by rw [h2])
    obtain ⟨⟨eT⟩, -⟩ := UnitaryHigher.unitary_full_diagonal_outer_order hU hn hq
    obtain ⟨N, hcyc, hcard, hcomm⟩ := exists_unitary_outer_diagonal hU hn hq
    let eP := (eK.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm).trans
      eT.symm
    obtain ⟨M, hMc, hMcard, hMcomm⟩ := exists_comap_of_injective
      (ι := (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eP).toMonoidHom)
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eP).injective hcyc hcard hcomm
    obtain ⟨-, hd, -⟩ := derived_of_commutator_mem hMc hMcard hMcomm
    exact Odd.of_dvd_nat (by decide : Odd 3) (hd.trans (Nat.gcd_dvd_left _ _))

private theorem abelian_index_le_two_of_le {S : Type} [Group S] {R P : Subgroup S} [Finite P]
    (hRP : R ≤ P) {A : Subgroup P} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hi : A.index ≤ 2) :
    ∃ B : Subgroup R, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ B.index ≤ 2 := by
  refine ⟨A.comap (Subgroup.inclusion hRP), fun a ha b hb => ?_, ?_⟩
  · apply Subgroup.inclusion_injective hRP
    rw [map_mul, map_mul]
    exact hA _ ha _ hb
  · rw [Subgroup.index_comap]
    calc A.relIndex (Subgroup.inclusion hRP).range ≤ A.relIndex ⊤ :=
          Subgroup.relIndex_le_of_le_right le_top
            (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
      _ = A.index := Subgroup.relIndex_top_right A
      _ ≤ 2 := hi

private theorem exists_abelian_of_sylow {S : Type} [Group S] [Finite S] {p e : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (he : 1 ≤ e) (hS : IsoLThreePi S p e) (P : Sylow 2 S) :
    ∃ A : Subgroup P, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.index ≤ 2 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ε, hL⟩ : ∃ ε : ℤ, CFSG.GH74.GLS.IVK.IsLnEps 3 S ε (p ^ e) := by
    rcases model_of_isoLThreePi hp5 he hS with h | h
    · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
      exact ⟨1, Or.inl ⟨rfl, K, inferInstance, inferInstance, hK, ⟨eK⟩⟩⟩
    · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
      exact ⟨-1, Or.inr ⟨rfl, K, inferInstance, inferInstance, hK, ⟨eK⟩⟩⟩
  obtain ⟨hsd, hwr⟩ := CFSG.GH74.GLS.IVK.Proofs2.ivk_4_4b S ε p e hp hp2 hL P
  by_cases hmod : ((p ^ e : ℕ) : ℤ) ≡ ε [ZMOD 4]
  · obtain ⟨m, -, ⟨f⟩⟩ := hwr hmod
    haveI := CFSG.Wreathed.base_is_abelian (2 ^ m)
    let g : ↥P →* CFSG.Wreathed.Wreath (2 ^ m) := f.toMonoidHom
    refine ⟨(CFSG.Wreathed.baseSubgroup (2 ^ m)).comap g, fun a ha b hb => ?_, ?_⟩
    · apply f.injective
      have h := mul_comm' (⟨g a, ha⟩ : CFSG.Wreathed.baseSubgroup (2 ^ m)) ⟨g b, hb⟩
      simpa [g] using congrArg Subtype.val h
    · rw [Subgroup.index_comap_of_surjective _ (show Function.Surjective g from f.surjective),
        CFSG.Wreathed.base_index_two _ (by positivity)]
  · obtain ⟨m, hm4, ⟨f⟩⟩ := hsd hmod
    refine ⟨Subgroup.zpowers (f.symm (CFSG.Semidihedral.r m)), fun a ha b hb => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self _ i j).eq
    · exact ((CFSG.Semidihedral.supplied_index_two m hm4 f.symm _).2 (Or.inl rfl)).le

theorem res3L125_abelian_index_le_two {S : Type} [Group S] [Finite S] {p e : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (he : 1 ≤ e) (hS : IsoLThreePi S p e) :
    ∀ R : Subgroup S, IsPGroup 2 R →
      ∃ A : Subgroup R, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.index ≤ 2 := by
  intro R hR
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  obtain ⟨A, hA, hi⟩ := exists_abelian_of_sylow hp5 he hS P
  exact abelian_index_le_two_of_le hRP hA hi

private theorem card_le_four_of_pRank_le {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 2) (E : Subgroup G)
    (hE1 : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  have hP : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE2 x x.2)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hEA : CFSG.Open.IsElemAbelian 2 E := ⟨⟨⟨fun a b => Subtype.ext (hE1 _ a.2 _ b.2)⟩⟩, hE2⟩
  have hk2 : k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hEA hk
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hk2.trans h)
    _ = 4 := by norm_num

private theorem pRank_two_statedProj_le_two {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K)) {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K).det = 1) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (StatedProj H)) ≤ 2 := by
  classical
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hK
  have hZ : ¬ 2 ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf H) := by
    intro h2Z
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2Z
    have hg3 : g ^ 3 = 1 := by
      obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 g.2 : ((g : ↥H) : GL (Fin 3) K) ∈
        StatedScalars (Fin 3) K)
      have hdg := hdet (g : ↥H) (g : ↥H).2
      rw [← hc] at hdg
      have hc3 : c ^ 3 = 1 := by
        apply Units.ext
        have : (((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)).det = (c : K) ^ 3 := by
          simp
        rw [this] at hdg
        simpa using hdg
      apply Subtype.ext
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow]
      show (((g : ↥H) : GL (Fin 3) K)) ^ 3 = 1
      rw [← hc, ← map_pow, hc3, map_one]
    have := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at this
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq _ hZ]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hle : Nat.card (E.map H.subtype) ≤ 4 := by
    apply CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← sq, hE.2 x hx, map_one]
    · rintro _ ⟨x, -, rfl⟩
      exact hdet _ x.2
  have hc : Nat.card (E.map H.subtype) = Nat.card E :=
    Nat.card_congr (E.equivMapOfInjective _ H.subtype_injective).symm.toEquiv
  rw [hc] at hle
  simpa using hle

private theorem det_eq_one_of_le_ker {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)}
    (hH : H ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker) :
    ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  intro g hg
  have h2 := congrArg Units.val (MonoidHom.mem_ker.1 (hH hg))
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h2

theorem res3L125_card_elemAbelian_le_four {S : Type} [Group S] [Finite S] {p e : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (he : 1 ≤ e) (hS : IsoLThreePi S p e) :
    ∀ E : Subgroup S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card E ≤ 4 := by
  intro E hE1 hE2
  have hp : p.Prime := Fact.out
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two (by omega)).pow
  refine card_le_four_of_pRank_le ?_ E hE1 hE2
  rcases model_of_isoLThreePi hp5 he hS with h | h
  · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
    have hK' : Odd (Nat.card K) := hK ▸ hodd
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eK]
    refine pRank_two_statedProj_le_two hK' (det_eq_one_of_le_ker ?_)
    refine (Subgroup.closure_le _).2 fun A hA => ?_
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hA
  · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
    have hK' : Odd (Nat.card K) := by rw [hK]; exact hodd.pow
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eK]
    refine pRank_two_statedProj_le_two hK' (det_eq_one_of_le_ker ?_)
    refine (Subgroup.closure_le _).2 fun A hA => ?_
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hA.1

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3

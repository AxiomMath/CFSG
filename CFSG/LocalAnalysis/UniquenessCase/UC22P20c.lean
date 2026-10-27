module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

section Abstract

theorem uc22p20c_isQuasisimple_of_not_centralizer_le {B : Type} [Group B] [Finite B]
    (hperf : Group.IsPerfect B) (hsimple : IsSimpleGroup (B ⧸ CFSG.solvableRadical B))
    (hnonab : ∃ a b : B ⧸ CFSG.solvableRadical B, a * b ≠ b * a)
    (h : ¬ centralizer ((CFSG.solvableRadical B : Subgroup B) : Set B) ≤
      CFSG.solvableRadical B) : CFSG.IsQuasisimple B := by
  set X : Subgroup B := CFSG.solvableRadical B with hX
  haveI hXn : X.Normal := CFSG.Quasithin.A3.instNormalSolvableRadical B
  haveI hXs : Group.IsSolvable ↥X := CFSG.Quasithin.A3.solvableRadical_isSolvable
  set C : Subgroup B := centralizer (X : Set B) with hC
  haveI hCn : C.Normal := Subgroup.normal_centralizer
  haveI hmapn : (C.map (QuotientGroup.mk' X)).Normal :=
    Subgroup.Normal.map hCn _ (QuotientGroup.mk'_surjective X)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' X)) with hbot | htop
  · exfalso
    apply h
    intro c hc
    have hc' : QuotientGroup.mk' X c ∈ C.map (QuotientGroup.mk' X) := ⟨c, hc, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc'
    exact hc'
  · have hdecomp : ∀ b : B, ∃ c ∈ C, c⁻¹ * b ∈ X := by
      intro b
      have hb : QuotientGroup.mk' X b ∈ C.map (QuotientGroup.mk' X) := by
        rw [htop]; trivial
      obtain ⟨c, hc, hcb⟩ := hb
      refine ⟨c, hc, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcb
      exact hcb
    haveI : Group.IsSolvable (B ⧸ C) := by
      refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' C).comp X.subtype) ?_
      intro q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective C q
      obtain ⟨c, hc, hx⟩ := hdecomp b
      refine ⟨⟨c⁻¹ * b, hx⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      have h1 : (c⁻¹ * b)⁻¹ * b = b⁻¹ * c * b := by group
      rw [h1]
      have h2 := hCn.conj_mem c hc b⁻¹
      simpa using h2
    have hsub : Subsingleton (B ⧸ C) := by
      by_contra hns
      haveI : Nontrivial (B ⧸ C) := not_subsingleton_iff_nontrivial.mp hns
      exact Group.IsPerfect.not_isSolvable (B ⧸ C) inferInstance
    have hCtop : C = ⊤ := by
      rw [eq_top_iff]
      intro b _
      have h1 : (QuotientGroup.mk' C b) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff b).1 h1
    have hXZ : X ≤ center B := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := hCtop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg x hx).symm
    have hZX : center B ≤ X := by
      haveI : Group.IsSolvable ↥(center B) := inferInstance
      exact CFSG.Quasithin.A3.le_solvableRadical inferInstance inferInstance
    have hZeq : center B = X := le_antisymm hZX hXZ
    let e : B ⧸ center B ≃* B ⧸ X := QuotientGroup.quotientMulEquivOfEq hZeq
    haveI := hsimple
    refine ⟨hperf, e.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa [map_mul] using congrArg e h)⟩

theorem uc22p20c_le_center_of_cyclic_normal {B : Type} [Group B] [Finite B]
    (hperf : Group.IsPerfect B) (P : Subgroup B) [P.Normal] (hP : IsCyclic P) : P ≤ center B := by
  haveI := hP
  let f : B →* MulAut ↥P := MulAut.conjNormal
  have hcomm : ∀ φ ψ : MulAut ↥P, φ * ψ = ψ * φ := by
    intro φ ψ
    apply (IsCyclic.mulAutMulEquiv (G := ↥P)).injective
    rw [map_mul, map_mul, mul_comm]
  haveI : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  haveI : IsMulCommutative ↥f.range :=
    ⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩
  haveI : Subsingleton ↥f.range := inferInstance
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro b
  have h1 : (⟨f b, b, rfl⟩ : ↥f.range) = 1 := Subsingleton.elim _ _
  have h2 : f b = 1 := congrArg Subtype.val h1
  have h3 := congrArg (fun φ : MulAut ↥P => ((φ ⟨x, hx⟩ : ↥P) : B)) h2
  simp only [f, MulAut.conjNormal_apply, MulAut.one_apply] at h3
  calc b * x = b * x * b⁻¹ * b := by group
    _ = x * b := by rw [h3]

theorem uc22p20c_layer_eq_bot {B : Type} [Group B] [Finite B]
    (hcent : centralizer ((CFSG.solvableRadical B : Subgroup B) : Set B) ≤
      CFSG.solvableRadical B) : CFSG.layer B = ⊥ := by
  haveI hXn : (CFSG.solvableRadical B).Normal := CFSG.Quasithin.A3.instNormalSolvableRadical B
  haveI hXs : Group.IsSolvable ↥(CFSG.solvableRadical B) :=
    CFSG.Quasithin.A3.solvableRadical_isSolvable
  rw [CFSG.layer.eq_sSup, ← le_bot_iff]
  refine sSup_le fun K hK => ?_
  exfalso
  have hKX : ⁅K, CFSG.solvableRadical B⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hXs hXn.isSubnormal).1 K hK
  have hKle : K ≤ CFSG.solvableRadical B :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKX).trans hcent
  haveI : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKle)
      (Subgroup.inclusion_injective hKle)
  obtain ⟨hperfK, -, a, b, hab⟩ := hK.1
  haveI := hperfK
  haveI : Subsingleton ↥K := by
    by_contra hns
    haveI : Nontrivial ↥K := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  exact hab (Subsingleton.elim _ _)

theorem uc22p20c_exists_noncyclic_pCore {B : Type} [Group B] [Finite B]
    (hperf : Group.IsPerfect B) (hnonab : ∃ a b : B ⧸ CFSG.solvableRadical B, a * b ≠ b * a)
    (h2 : CFSG.pCore 2 B = ⊥)
    (hcent : centralizer ((CFSG.solvableRadical B : Subgroup B) : Set B) ≤
      CFSG.solvableRadical B) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ¬ IsCyclic ↥(CFSG.pCore q B) := by
  by_contra hall
  push Not at hall
  have hq : ∀ q : ℕ, q.Prime → CFSG.pCore q B ≤ center B := by
    intro q hq
    by_cases hq2 : q = 2
    · subst hq2
      rw [h2]
      exact bot_le
    · haveI : (CFSG.pCore q B).Normal := CFSG.pCore_normal
      exact uc22p20c_le_center_of_cyclic_normal hperf _ (hall q hq hq2)
  have hF : CFSG.fittingSubgroup B ≤ center B := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    exact iSup_le fun p => hq p (Nat.prime_of_mem_primeFactors p.2)
  have hE : CFSG.layer B = ⊥ := uc22p20c_layer_eq_bot hcent
  have hFstar : CFSG.generalizedFitting B ≤ center B := by
    rw [CFSG.generalizedFitting.eq_sup, hE, sup_bot_eq]
    exact hF
  have hcentF : centralizer ((CFSG.generalizedFitting B : Subgroup B) : Set B) ≤
      CFSG.generalizedFitting B := by
    rw [← CFSG.Adapters.genFittingFStar_eq_foundations]
    exact CFSG.Adapters.generalized_fitting_self_centralizing B
  have hcomm : ∀ a b : B, a * b = b * a := by
    intro a b
    have hb : b ∈ centralizer ((CFSG.generalizedFitting B : Subgroup B) : Set B) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_center_iff.1 (hFstar hx) b).symm
    have ha : b ∈ center B := hFstar (hcentF hb)
    exact (Subgroup.mem_center_iff.1 ha a)
  obtain ⟨a, b, hab⟩ := hnonab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm a b])

theorem uc22p20c_pRank_comap_eq {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime)
    (hk : ¬ p ∣ Nat.card f.ker) (J : Subgroup Y) :
    CFSG.Open.pRank p (J.comap f) = CFSG.Open.pRank p J := by
  have h1 := CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal p hp f.ker hk
    (J.comap f)
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have h2 : ((J.comap f).map (QuotientGroup.mk' f.ker)).map e.toMonoidHom = J := by
    rw [Subgroup.map_map]
    have h4 : e.toMonoidHom.comp (QuotientGroup.mk' f.ker) = f := by
      ext x
      rfl
    rw [h4, Subgroup.map_comap_eq_self_of_surjective hf]
  have h3 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp e.toMonoidHom
    e.injective ((J.comap f).map (QuotientGroup.mk' f.ker))
  rw [h2] at h3
  rw [← h1, ← h3]

theorem uc22p20c_not_dvd_card_of_isPGroup_two {A : Type} [Group A] {N : Subgroup A} [Finite N]
    (hN : IsPGroup 2 N) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ Nat.card N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hN
  intro hdvd
  rw [hn] at hdvd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))

theorem uc22p20c_applyK318 (hK318 : UCK.K318) {A Y : Type} [Group A] [Finite A] [Group Y]
    [Finite Y] (hY : CFSG.Open.IsKGroup Y) (hY2 : CFSG.pCore 2 Y = ⊥) (f : A →* Y)
    [f.range.Normal] (hker : IsPGroup 2 f.ker) (hperf : Group.IsPerfect A)
    (hsimple : IsSimpleGroup (A ⧸ CFSG.solvableRadical A))
    (hnonab : ∃ a b : A ⧸ CFSG.solvableRadical A, a * b ≠ b * a)
    (hrank1 : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (CFSG.solvableRadical A) ≤ 3)
    (hrank2 : ∀ q : ℕ, q.Prime → q ≠ 2 → 3 < CFSG.Open.pRank q (⊤ : Subgroup A) →
      CFSG.Open.pRank q (CFSG.solvableRadical A) ≤ 1)
    (hnq : ¬ CFSG.IsQuasisimple ↥f.range) :
    ((∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
        (IsL2Odd (A ⧸ CFSG.solvableRadical A) r ∨ IsL3Odd (A ⧸ CFSG.solvableRadical A) r)) ∨
      IsAlt (A ⧸ CFSG.solvableRadical A) 6 ∨ IsAlt (A ⧸ CFSG.solvableRadical A) 7) ∧
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (CFSG.pCore q Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup Y := f.range with hB
  let ρ : A →* ↥B := f.rangeRestrict
  have hρ : Function.Surjective ρ := MonoidHom.rangeRestrict_surjective f
  have hρker : ρ.ker = f.ker := MonoidHom.ker_rangeRestrict f
  have hsolv : Group.IsSolvable ↥ρ.ker := by
    rw [hρker]
    haveI : Group.IsNilpotent ↥f.ker := hker.isNilpotent
    infer_instance
  have hcop : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card ρ.ker := by
    intro q hq hq2
    rw [hρker]
    exact uc22p20c_not_dvd_card_of_isPGroup_two hker hq hq2
  have hBK : CFSG.Open.IsKGroup ↥B := hY.subgroup B
  haveI hBperf : Group.IsPerfect ↥B := Group.IsPerfect.ofSurjective hρ
  let e : A ⧸ CFSG.solvableRadical A ≃* ↥B ⧸ CFSG.solvableRadical ↥B :=
    CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.solQuotEquiv hρ hsolv
  haveI := hsimple
  haveI hsimpleB : IsSimpleGroup (↥B ⧸ CFSG.solvableRadical ↥B) := e.symm.isSimpleGroup
  have hnonabB : ∃ a b : ↥B ⧸ CFSG.solvableRadical ↥B, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e a, e b, fun h => hab (by simpa [map_mul] using congrArg e.symm h)⟩
  have hradB : (CFSG.solvableRadical ↥B).comap ρ = CFSG.solvableRadical A :=
    CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.comap_solvableRadical hρ hsolv
  have hradrank : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (CFSG.solvableRadical ↥B) = CFSG.Open.pRank q (CFSG.solvableRadical A) := by
    intro q hq hq2
    rw [← uc22p20c_pRank_comap_eq ρ hρ hq (hcop q hq hq2), hradB]
  have hB2 : CFSG.pCore 2 ↥B = ⊥ := by
    have hn : (pCoreOf 2 B).Normal :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_of_normal 2 B inferInstance
    have hp : IsPGroup 2 (pCoreOf 2 B) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 B
    have hle : pCoreOf 2 B ≤ CFSG.pCore 2 Y := le_sSup ⟨hn, hp⟩
    rw [hY2, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).1 hle
  have hXB2 : CFSG.Open.pCoreOf 2 (CFSG.solvableRadical ↥B) = ⊥ := by
    have hn : (pCoreOf 2 (CFSG.solvableRadical ↥B)).Normal :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_of_normal 2 _ inferInstance
    have hp : IsPGroup 2 (pCoreOf 2 (CFSG.solvableRadical ↥B)) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 _
    have hle : pCoreOf 2 (CFSG.solvableRadical ↥B) ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hn, hp⟩
    rw [hB2, le_bot_iff] at hle
    exact hle
  have hcentB : centralizer ((CFSG.solvableRadical ↥B : Subgroup ↥B) : Set ↥B) ≤
      CFSG.solvableRadical ↥B := by
    by_contra hc
    exact hnq (uc22p20c_isQuasisimple_of_not_centralizer_le hBperf hsimpleB hnonabB hc)
  obtain ⟨hcl, -⟩ := hK318 ↥B hBK hBperf.commutator_eq_top hXB2 hsimpleB
    (fun q hq hq2 => (hradrank q hq hq2).trans_le (hrank1 q hq hq2)) hcentB
  have hcl' : (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      (CFSG.Blueprint.LieModel (↥B ⧸ CFSG.solvableRadical ↥B) .PSL 2 r 1 ∨
        CFSG.Blueprint.LieModel (↥B ⧸ CFSG.solvableRadical ↥B) .PSL 3 r 1)) ∨
      IsAlt (↥B ⧸ CFSG.solvableRadical ↥B) 6 ∨ IsAlt (↥B ⧸ CFSG.solvableRadical ↥B) 7 := by
    rcases hcl with h | h | h | ⟨-, q, hq, hq2, hq3, hq4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exfalso
      have h1 : CFSG.Open.pRank q (⊤ : Subgroup ↥B) = CFSG.Open.pRank q (⊤ : Subgroup A) := by
        rw [← uc22p20c_pRank_comap_eq ρ hρ hq (hcop q hq hq2) ⊤, Subgroup.comap_top]
      have h2 := hrank2 q hq hq2 (by omega)
      have h3 := hradrank q hq hq2
      omega
  have hfinal : (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
        (IsL2Odd (A ⧸ CFSG.solvableRadical A) r ∨ IsL3Odd (A ⧸ CFSG.solvableRadical A) r)) ∨
      IsAlt (A ⧸ CFSG.solvableRadical A) 6 ∨ IsAlt (A ⧸ CFSG.solvableRadical A) 7 := by
    rcases hcl' with ⟨r, hr, hr2, hL⟩ | h6 | h7
    · refine Or.inl ⟨r, hr, hr2, ?_⟩
      rcases hL with h | h
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)
      · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)
    · exact Or.inr (Or.inl ⟨e.trans h6.some⟩)
    · exact Or.inr (Or.inr ⟨e.trans h7.some⟩)
  refine ⟨hfinal, ?_⟩
  obtain ⟨q, hq, hq2, hqc⟩ := uc22p20c_exists_noncyclic_pCore hBperf hnonabB hB2 hcentB
  refine ⟨q, hq, hq2, ?_⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (IsPGroup q ↥(CFSG.pCore q ↥B)) := ⟨CFSG.pCore_isPGroup⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hq2 hqc
  haveI := hSel
  have hE2 : CFSG.IsElementaryAbelian q ↥((S.map (CFSG.pCore q ↥B).subtype).map B.subtype) := by
    haveI : CFSG.IsElementaryAbelian q ↥(S.map (CFSG.pCore q ↥B).subtype) := CFSG.IsElementaryAbelian.map_subtype
    exact CFSG.IsElementaryAbelian.map_subtype
  have hEcard : Nat.card ↥((S.map (CFSG.pCore q ↥B).subtype).map B.subtype) = q ^ 2 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.card_map_of_injective (CFSG.pCore q ↥B).subtype_injective, hScard]
  have hEle : (S.map (CFSG.pCore q ↥B).subtype).map B.subtype ≤ CFSG.pCore q Y := by
    have h1 : (S.map (CFSG.pCore q ↥B).subtype).map B.subtype ≤ pCoreOf q B :=
      Subgroup.map_mono (Subgroup.map_subtype_le S)
    have hn : (pCoreOf q B).Normal :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_of_normal q B inferInstance
    have hp : IsPGroup q (pCoreOf q B) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup q B
    exact h1.trans (le_sSup ⟨hn, hp⟩)
  exact CFSG.SectionRank.le_pRank hq.one_lt hEle
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q _).mp hE2) hEcard

theorem uc22p20c_cCompSpan_top {Q : Type} [Group Q] [Finite Q] (hperf : Group.IsPerfect Q)
    (hE : CFSG.Quasithin.oInftyE Q = ⊤) : CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q) = ⊤ := by
  have h := CFSG.Quasithin.E1.oInftyE_eq_cCompSpan_sup Q
  rw [hE] at h
  haveI hSn : (CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q)).Normal := CFSG.Quasithin.cCompSpan_normal
  haveI : Group.IsSolvable (Q ⧸ CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q)) := by
    haveI : Group.IsSolvable ↥(CFSG.solvableRadical Q) :=
      CFSG.Quasithin.A3.solvableRadical_isSolvable
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q))).comp
        (CFSG.solvableRadical Q).subtype) ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q)) q
    have hx : x ∈ CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q) ⊔ CFSG.solvableRadical Q := by
      rw [← h]; trivial
    obtain ⟨s, hs, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    refine ⟨⟨r, hr⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have h2 := hSn.conj_mem s hs r⁻¹
    have h3 : r⁻¹ * (s * r) = r⁻¹ * s * r⁻¹⁻¹ := by group
    rw [h3]
    exact h2
  haveI := hperf
  have hsub : Subsingleton (Q ⧸ CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q)) := by
    by_contra hns
    haveI : Nontrivial (Q ⧸ CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q)) :=
      not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (Q ⧸ CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q))
      inferInstance
  rw [eq_top_iff]
  intro b _
  have h1 : (QuotientGroup.mk' (CFSG.Quasithin.cCompSpan (⊤ : Subgroup Q)) b) = 1 :=
    Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff b).1 h1

theorem uc22p20c_oTwoE_eq_top {Q : Type} [Group Q] [Finite Q] (hperf : Group.IsPerfect Q)
    (hE : CFSG.Quasithin.oInftyE Q = ⊤)
    (h : ∀ C ∈ CFSG.Quasithin.cComp (⊤ : Subgroup Q),
      CFSG.IsQuasisimple ↥(C.map (QuotientGroup.mk' (CFSG.pCore 2 Q)))) : OTwoE Q = ⊤ := by
  have hspan := uc22p20c_cCompSpan_top hperf hE
  have hπ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Q)
  have hlayer : CFSG.layer (Q ⧸ CFSG.pCore 2 Q) = ⊤ := by
    rw [eq_top_iff]
    have h1 : (⊤ : Subgroup Q) ≤ (CFSG.layer (Q ⧸ CFSG.pCore 2 Q)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 Q)) := by
      rw [← hspan]
      refine sSup_le fun C hC => ?_
      rw [← Subgroup.map_le_iff_le_comap, CFSG.layer.eq_sSup]
      refine le_sSup ⟨h C hC, ?_⟩
      exact CFSG.Quasithin.A3.subnormal_top_iff.1
        (CFSG.Quasithin.A3.subnormal_top_map hπ (CFSG.Quasithin.subnormal_of_mem_cComp hC))
    intro y _
    obtain ⟨x, rfl⟩ := hπ y
    exact h1 (Subgroup.mem_top x)
  unfold OTwoE
  rw [hlayer, Subgroup.comap_top]

theorem uc22p20c_pCore_quotient_pCore {H : Type*} [Group H] {p : ℕ} :
    CFSG.pCore p (H ⧸ CFSG.pCore p H) = ⊥ := by
  set N : Subgroup H := CFSG.pCore p H with hN
  set K : Subgroup H := (CFSG.pCore p (H ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup p K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := H ⧸ N) (p := p)) ⟨_, hk⟩
    have h1 : k ^ p ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := H) (p := p)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

theorem uc22p20c_normal_of_mem_cComp_top {Q : Type} [Group Q] [Finite Q]
    (hperf : Group.IsPerfect Q) (hE : CFSG.Quasithin.oInftyE Q = ⊤) {C : Subgroup Q}
    (hC : C ∈ CFSG.Quasithin.cComp (⊤ : Subgroup Q)) : C.Normal := by
  have hspan := uc22p20c_cCompSpan_top hperf hE
  obtain ⟨hle, hn⟩ := CFSG.Quasithin.cComp_normal_span hC
  have h1 := (Subgroup.normal_subgroupOf_iff hle).1 hn
  exact ⟨fun n hn' g => h1 n g hn' (by rw [hspan]; trivial)⟩

theorem uc22p20c_barInf_simple {G : Type} [Group G] [Finite G] {X C : Subgroup G}
    (hC : C ∈ CFSG.Quasithin.cComp X) :
    IsSimpleGroup (BarInf C) ∧ ∃ a b : BarInf C, a * b ≠ b * a := by
  have hstruct := (CFSG.Quasithin.cComp_structure hC).2.1
  have heq : (CFSG.Quasithin.solvRad C).subgroupOf C = CFSG.solvableRadical ↥C := by
    rw [CFSG.Quasithin.solvRad_eq_map_solvableRadical, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  let e := QuotientGroup.quotientMulEquivOfEq heq
  haveI := hstruct.1
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hstruct.2
  exact ⟨e a, e b, fun h => hab (by simpa using congrArg e.symm h)⟩

theorem uc22p20c_barInf_equiv_map {G : Type} [Group G] [Finite G] (C : Subgroup G) (g : G) :
    Nonempty (BarInf C ≃* BarInf (C.map (MulAut.conj g).toMonoidHom)) := by
  let e : ↥C ≃* ↥(C.map (MulAut.conj g).toMonoidHom) :=
    C.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hker : Group.IsSolvable ↥e.toMonoidHom.ker := by
    have hbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
    rw [hbot]
    infer_instance
  exact ⟨CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.solQuotEquiv
    (ρ := e.toMonoidHom) e.surjective hker⟩

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G]

theorem uc22p20c_ne_top (D : Data G) {H : Subgroup G} (hH : H ∈ hSet D.T D.M) : H ≠ ⊤ := by
  haveI := D.standing.simple
  obtain ⟨N, hN, hHN⟩ := uc22p20a_exists_mem_calMOf D hH
  have hNtop : N ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1
  exact fun h => hNtop (top_le_iff.mp (h ▸ hHN))

theorem uc22p20c_rank_bounds (D : Data G) (h1930 : H1930 D) (h20_1 : S20_1_124 D)
    {H : Subgroup G} (hH : H ∈ hSet D.T D.M) {C : Subgroup G}
    (hC : C ∈ CFSG.Quasithin.cComp H) :
    (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (CFSG.solvableRadical ↥C) ≤ 3) ∧
    (∀ q : ℕ, q.Prime → q ≠ 2 → 3 < CFSG.Open.pRank q (⊤ : Subgroup ↥C) →
      CFSG.Open.pRank q (CFSG.solvableRadical ↥C) ≤ 1) := by
  obtain ⟨-, h2, h4⟩ := h20_1 h1930 H hH
  have hCH : C ≤ H := CFSG.Quasithin.le_of_mem_cComp hC
  have hsub : CFSG.Open.IsSubnormal (CFSG.Quasithin.solvRad C) H :=
    CFSG.Quasithin.A3.subnormal_trans
      (CFSG.Quasithin.A3.subnormal_of_normal (CFSG.Quasithin.solvRad_le C)
        (CFSG.Quasithin.solvRad_normal C)) (CFSG.Quasithin.subnormal_of_mem_cComp hC)
  have hXH : CFSG.Quasithin.solvRad C ≤ OInf H := by
    have h := CFSG.Quasithin.le_solvRad_of_subnormal hsub (CFSG.Quasithin.solvRad_isSolvable C)
    rw [CFSG.Quasithin.solvRad_eq_map_solvableRadical H] at h
    exact h
  have hOH : OInf H ≤ H := Subgroup.map_subtype_le _
  have hXM : CFSG.Quasithin.solvRad C ≤ H ⊓ D.M := le_inf (hXH.trans hOH) (hXH.trans h4)
  have hrk : ∀ q : ℕ, q.Prime → CFSG.Open.pRank q (CFSG.solvableRadical ↥C) =
      CFSG.Open.pRank q (CFSG.Quasithin.solvRad C) := by
    intro q hq
    rw [CFSG.Quasithin.solvRad_eq_map_solvableRadical C]
    exact (CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective q hq C.subtype
      C.subtype_injective _).symm
  have hmono : ∀ q : ℕ, q.Prime → ∀ {S T : Subgroup G}, S ≤ T →
      CFSG.Open.pRank q S ≤ CFSG.Open.pRank q T := fun q hq S T h =>
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq h
  refine ⟨fun q hq hq2 => ?_, fun q hq hq2 hlt => ?_⟩
  · rw [hrk q hq]
    by_cases h3 : 3 < CFSG.Open.pRank q H
    · exact (hmono q hq hXM).trans ((h2 q hq hq2 h3).trans (by norm_num))
    · have := hmono q hq (hXM.trans inf_le_left)
      omega
  · rw [hrk q hq]
    have hCtop : CFSG.Open.pRank q (⊤ : Subgroup ↥C) = CFSG.Open.pRank q C := by
      have := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective q hq C.subtype
        C.subtype_injective ⊤
      rw [Subgroup.map_top, Subgroup.range_subtype] at this
      exact this.symm
    have h3 : 3 < CFSG.Open.pRank q H := lt_of_lt_of_le (hCtop ▸ hlt) (hmono q hq hCH)
    exact (hmono q hq hXM).trans (h2 q hq hq2 h3)

theorem s20_2_of (D : Data G) (hK318 : UCK.K318) (h20_1 : S20_1_124 D) : S20_2 D := by
  intro h1930 H hH K hKH hKn hKperf hKE hKtrans
  by_cases hOTwoE : OTwoE ↥K = ⊤
  · exact Or.inl hOTwoE
  right
  have hHtop : H ≠ ⊤ := uc22p20c_ne_top D hH
  have hKtop : K ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hKH))
  have hKsub : CFSG.Open.IsSubnormal K H := CFSG.Quasithin.A3.subnormal_of_normal hKH hKn
  haveI hQperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hKperf
  have hKK : CFSG.Open.IsKGroup ↥K :=
    D.standing.kProper.isKGroup K hKtop
  have hYK : CFSG.Open.IsKGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    hKK.quotient _
  have hY2 : CFSG.pCore 2 (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := uc22p20c_pCore_quotient_pCore
  set π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcopπ : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card π.ker := by
    intro q hq hq2
    rw [hπdef, QuotientGroup.ker_mk']
    exact uc22p20c_not_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup hq hq2
  have hex : ∃ C₀ ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥K), ¬ CFSG.IsQuasisimple ↥(C₀.map π) := by
    by_contra hall
    push Not at hall
    exact hOTwoE (uc22p20c_oTwoE_eq_top hQperf hKE hall)
  obtain ⟨C₀, hC₀, hC₀q⟩ := hex
  obtain ⟨C, hC, hCeq⟩ := (CFSG.Quasithin.cComp_subgroupOf_bijOn K).surjOn hC₀
  have hCeq' : C.subgroupOf K = C₀ := hCeq
  have hCK : C ≤ K := CFSG.Quasithin.le_of_mem_cComp hC
  have hCH : C ∈ CFSG.Quasithin.cComp H := CFSG.Quasithin.cComp_mem_of_subnormal hKsub hC
  let f : ↥C →* ↥K ⧸ CFSG.pCore 2 ↥K := π.comp (Subgroup.inclusion hCK)
  have hrange : f.range = C₀.map π := by
    rw [← hCeq']
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Subgroup.inclusion hCK c, Subgroup.mem_subgroupOf.2 c.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  haveI hnormal : f.range.Normal := by
    rw [hrange]
    exact Subgroup.Normal.map (uc22p20c_normal_of_mem_cComp_top hQperf hKE hC₀) π hπ
  have hnq : ¬ CFSG.IsQuasisimple ↥f.range := by
    rw [hrange]
    exact hC₀q
  have hker : IsPGroup 2 f.ker := by
    have h1 : f.ker = (CFSG.pCore 2 ↥K).comap (Subgroup.inclusion hCK) := by
      rw [show f = π.comp (Subgroup.inclusion hCK) from rfl, ← MonoidHom.comap_ker, hπdef,
        QuotientGroup.ker_mk']
    rw [h1]
    exact (CFSG.pCore_isPGroup).comap_of_injective _ (Subgroup.inclusion_injective hCK)
  have hperfC : Group.IsPerfect ↥C := Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfect_of_mem_cComp hC)
  obtain ⟨hsimpleC, hnonabC⟩ := uc22p20c_barInf_simple hC
  obtain ⟨hrank1, hrank2⟩ := uc22p20c_rank_bounds D h1930 h20_1 hH hCH
  obtain ⟨hcl, q, hq, hq2, hqrk⟩ := uc22p20c_applyK318 hK318 hYK hY2 f hker hperfC hsimpleC hnonabC
    hrank1 hrank2 hnq
  refine ⟨?_, q, hq, hq2, ?_⟩
  · rcases hcl with ⟨r, hr, hr2, hL⟩ | h6 | h7
    · refine Or.inl ⟨r, hr, hr2, fun C₂ hC₂ => ?_⟩
      obtain ⟨g, -, rfl⟩ := hKtrans C hC C₂ hC₂
      obtain ⟨e⟩ := uc22p20c_barInf_equiv_map C g
      rcases hL with hL | hL
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL)
      · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hL)
    · refine Or.inr fun C₂ hC₂ => ?_
      obtain ⟨g, -, rfl⟩ := hKtrans C hC C₂ hC₂
      obtain ⟨e⟩ := uc22p20c_barInf_equiv_map C g
      exact Or.inl ⟨e.symm.trans h6.some⟩
    · refine Or.inr fun C₂ hC₂ => ?_
      obtain ⟨g, -, rfl⟩ := hKtrans C hC C₂ hC₂
      obtain ⟨e⟩ := uc22p20c_barInf_equiv_map C g
      exact Or.inr ⟨e.symm.trans h7.some⟩
  · have h1 : CFSG.Open.pRank q (CFSG.Quasithin.E1.oTwoP ↥K q) =
        CFSG.Open.pRank q (CFSG.pCore q (↥K ⧸ CFSG.pCore 2 ↥K)) :=
      uc22p20c_pRank_comap_eq π hπ hq (hcopπ q hq hq2) _
    omega

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.UC22

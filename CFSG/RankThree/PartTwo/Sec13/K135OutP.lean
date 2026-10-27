module

public import CFSG.RankThree.PartTwo.Sec13.F135LastKF135
public import CFSG.RankThree.PartTwo.Sec13.K135OutPCore
public import CFSG.Models.Blueprint
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverSmall
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.MB3.OddOutLinear
public import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
public import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartOne.S11d.PlaneCases

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.Assembly.LowTwoRank CFSG.Models Matrix Subgroup
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.PresentationLocal (sympFour antidiagGram omegaPerm)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem isPerfect_of_simple_nonab {K : Type} [Group K] (hS : IsSimpleGroup K)
    (hnc : ∃ a b : K, a * b ≠ b * a) : Group.IsPerfect K := by
  rw [Group.isPerfect_def]
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator K) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hm : a * b * a⁻¹ * b⁻¹ ∈ commutator K :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      rw [h, Subgroup.mem_bot] at hm
      exact hm
    apply hab
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · exact h

theorem not_simple_of_card_dvd {S X : Type} [Group S] [Finite S] [Group X] {a b : ℕ}
    (hX : Nat.card X ∣ 2 ^ a * 3 ^ b) (hS : IsSimpleGroup S) (hnab : ∃ x y : S, x * y ≠ y * x)
    (e : S ≃* X) : False := by
  have hcard : Nat.card S ∣ 2 ^ a * 3 ^ b := by rwa [Nat.card_congr e.toEquiv]
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := dvd_mul.mp hcard
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd₂
  have := Fintype.ofFinite S
  have hsolv : Group.IsSolvable S :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hd])
  obtain ⟨x, y, hxy⟩ := hnab
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)

theorem not_simple_projSL_two {S : Type} [Group S] [Finite S] (p : ℕ) [Fact p.Prime]
    (hp : p = 2 ∨ p = 3) (hS : IsSimpleGroup S) (hnab : ∃ x y : S, x * y ≠ y * x)
    (e : S ≃* projSL 2 (GaloisField p 1)) : False := by
  rcases hp with rfl | rfl
  · exact not_simple_of_card_dvd (a := 1) (b := 1) (card_projSL_two_dvd 2) hS hnab e
  · exact not_simple_of_card_dvd (a := 4) (b := 1) (card_projSL_two_dvd 3) hS hnab e

theorem not_simple_projSU_three_two {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ x y : S, x * y ≠ y * x) (e : S ≃* projSU 3 2 1) : False := by
  have := Sec13.isSolvable_projSU_two
  have hsolv : Group.IsSolvable S :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨x, y, hxy⟩ := hnab
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)

theorem not_simple_projSp_two_two {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ x y : S, x * y ≠ y * x) (e : S ≃* projSp 2 F2) : False := by
  have : Group.IsPerfect S := isPerfect_of_simple_nonab hS hnab
  let ε := CFSG.RankThree.PartTwo.KFacts.statedSpEquivProjSpOfCharTwo F2
  let χ : S →* ℤˣ := Equiv.Perm.sign.comp (omegaPerm.comp (sp4Hom.comp
    (ε.symm.toMonoidHom.comp e.toMonoidHom)))
  obtain ⟨y, hy⟩ := e.surjective (ε sp4Transvection)
  have hχ : χ y = -1 := by
    change Equiv.Perm.sign (omegaPerm (sp4Hom (ε.symm (e y)))) = -1
    rw [hy, MulEquiv.symm_apply_apply, sp4Hom_transvection, sign_omegaPerm_t03]
  have hker : y ∈ χ.ker :=
    Abelianization.commutator_subset_ker χ (Group.IsPerfect.mem_commutator (g := y))
  rw [MonoidHom.mem_ker, hχ] at hker
  exact absurd hker (by decide)

theorem not_dvd_gcd_of_lt {p n m : ℕ} (hn : 0 < n) (hlt : n < p) : ¬ p ∣ Nat.gcd n m := fun h => by
  have := Nat.le_of_dvd hn (h.trans (Nat.gcd_dvd_left n m))
  omega

theorem outPChain_of_stated {T : Type} [Group T] {t : StatedLieTag} {n ℓ f p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hcl : StatedClassicalModel T t n ℓ f)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hdL : t = .PSL → 3 ≤ n → ¬ p ∣ Nat.gcd n (ℓ ^ f - 1))
    (hdU : t = .PSU → ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (hsp : t = .PSp → n = 2 → ℓ ≠ 2 → OutPChain p T) : OutPChain p T := by
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · by_cases hn2 : n = 2
    · subst hn2
      by_cases hℓ : ℓ = 2
      · subst hℓ
        exact (outPNice_PSL_two hp hcl).toChain
      · exact (outPNice_PSL_two_odd hp hp3 hℓ hcl).toChain
    · have hn3 : 3 ≤ n := by
        have := hcl.1.2.2.1
        omega
      exact (outPNice_PSL_ge_three_odd hp hp2 hn3 hcl (hdL rfl hn3)).toChain
  · exact (outPNice_PSU_odd hp hcl (hdU rfl)).toChain
  · by_cases hn2 : n = 2
    · subst hn2
      by_cases hℓ : ℓ = 2
      · subst hℓ
        exact (outPNice_PSp_two hp hcl).toChain
      · exact hsp rfl rfl hℓ
    · have hn3 : 3 ≤ n := by
        have := hcl.1.2.2.1
        omega
      exact (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl).toChain
  · by_cases hn4 : n = 4
    · subst hn4
      exact outPChain_POmegaPlus_four_gen hp hp5 hcl
    · have hn5 : 5 ≤ n := by
        have := hcl.1.2.2
        omega
      exact (outPNice_POmegaPlus_gen_ge_five hp hp5 hn5 hcl).toChain
  · exact (outPNice_POmegaMinus_gen hp hp5 hcl).toChain

theorem outPChain_psp_two_odd {T : Type} [Group T] [Finite T] {ℓ p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hℓ : ℓ.Prime) (hcl : StatedClassicalModel T .PSp 2 ℓ 1) : OutPChain p T := by
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hcl
  letI : Field K := hF
  haveI : Finite K := hFin
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.outer_card_dvd (K := K)
    (r := 2) hℓ le_rfl hK le_rfl).1
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (StatedProj (StatedSp 2 K))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
  have hle : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) ≤
      2 * 1 * Nat.gcd 2 (ℓ ^ 1 - 1) := by
    rw [hcard]
    exact Nat.le_of_dvd (by
      have : 0 < Nat.gcd 2 (ℓ ^ 1 - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      omega) hdvd
  have hg : Nat.gcd 2 (ℓ ^ 1 - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  refine (CFSG.RankThree.PartOne.PlaneCases.outPNice_of_not_dvd_outer hp fun hd => ?_).toChain
  have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) :=
    Nat.card_pos
  have := Nat.le_of_dvd hpos hd
  omega

theorem stated_of_lieModel {S X : Type} [Group S] [Group X] (e : S ≃* X) {t : StatedLieTag}
    {n ℓ f : ℕ} (hm : LieModel X t n ℓ f) (hn : n ≠ 0) : StatedClassicalModel S t n ℓ f :=
  CFSG.Models.LieModel.statedClassicalModel_of_ne_zero hn (lieModel_of_mulEquiv e hm)

theorem chain_psl {S X : Type} [Group S] [Group X] (e : S ≃* X) {n ℓ f p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hm : LieModel X .PSL n ℓ f) (hn : n ≠ 0)
    (hd : 3 ≤ n → ¬ p ∣ Nat.gcd n (ℓ ^ f - 1)) : OutPChain p S :=
  outPChain_of_stated hp hp7 (stated_of_lieModel e hm hn)
    (Or.inl rfl) (fun _ h3 => hd h3) (fun h => nomatch h) (fun h => nomatch h)

theorem chain_psu {S X : Type} [Group S] [Group X] (e : S ≃* X) {n ℓ f p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hm : LieModel X .PSU n ℓ f) (hn : n ≠ 0)
    (hd : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) : OutPChain p S :=
  outPChain_of_stated hp hp7 (stated_of_lieModel e hm hn)
    (Or.inr (Or.inl rfl)) (fun h => nomatch h) (fun _ => hd) (fun h => nomatch h)

theorem chain_psp {S X : Type} [Group S] [Group X] (e : S ≃* X) {n ℓ f p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hm : LieModel X .PSp n ℓ f) (hn : n ≠ 0) (hexc : n = 2 → ℓ = 2) :
    OutPChain p S :=
  outPChain_of_stated hp hp7 (stated_of_lieModel e hm hn)
    (Or.inr (Or.inr (Or.inl rfl))) (fun h => nomatch h) (fun h => nomatch h)
    (fun _ h2 hℓ => absurd (hexc h2) hℓ)

theorem chain_pomegaPlus {S X : Type} [Group S] [Group X] (e : S ≃* X) {n ℓ f p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hm : LieModel X .POmegaPlus n ℓ f) (hn : n ≠ 0) :
    OutPChain p S :=
  outPChain_of_stated hp hp7 (stated_of_lieModel e hm hn)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun h => nomatch h) (fun h => nomatch h)
    (fun h => nomatch h)

theorem chain_pomegaMinus {S X : Type} [Group S] [Group X] (e : S ≃* X) {n ℓ f p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hm : LieModel X .POmegaMinus n ℓ f) (hn : n ≠ 0) :
    OutPChain p S :=
  outPChain_of_stated hp hp7 (stated_of_lieModel e hm hn)
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (fun h => nomatch h) (fun h => nomatch h)
    (fun h => nomatch h)

theorem two_pow_ne_of_two_le' {n : ℕ} (hn : 2 ≤ n) : 2 ^ n ≠ 2 ∧ 2 ^ n ≠ 3 := by
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

structure OutPInputs : Prop where
  ree : ∀ (hr : (TauCeti.LieTypeIndex.reeG2 1).Valid) {Y : Type} [Group Y],
    Y ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group → IsCyclic (Outer Y)
  g2 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) {p : ℕ}, p.Prime →
    ∀ {Y : Type} [Group Y], Y ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group → OutPNice p Y
  d4 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    ∀ {p : ℕ}, p.Prime → ∀ {Y : Type} [Group Y],
      Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group → OutPNice p Y
  sz : ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {p : ℕ}, p.Prime →
    ∀ {Y : Type} [Group Y], Y ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group → OutPNice p Y
  f4r : ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {p : ℕ}, p.Prime →
    ∀ {Y : Type} [Group Y], Y ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group → OutPNice p Y
  tits : ∀ (hv : TauCeti.LieTypeIndex.tits.Valid) {Y : Type} [Group Y] [Finite Y],
    Y ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group → Nat.card (Outer Y) = 2
  f42 : ∀ {p : ℕ}, p.Prime → ∀ {Y : Type} [Group Y],
    Y ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group → OutPNice p Y
  spor : ∀ (s : TauCeti.SporadicName) {p : ℕ}, p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)

theorem kFactOutP_of_inputs (hI : OutPInputs) : KFactOutP := by
  intro S _ _ hS hnab h42 p hp hp7 P hP
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  refine relIndex_le_of_outPChain hp ?_ P hP
  have hnd : ¬ p ∣ Nat.card (Outer S) → OutPChain p S := fun h =>
    (CFSG.RankThree.PartOne.PlaneCases.outPNice_of_not_dvd_outer hp h).toChain
  have hlt : ∀ {n : ℕ}, 0 < n → n < 7 → ∀ {m : ℕ}, ¬ p ∣ Nat.gcd n m := fun hn hn7 =>
    not_dvd_gcd_of_lt hn (by omega)
  rcases h42 with
    ⟨p0, e, _, hp0, he, hf⟩ | ⟨p0, e, _, hp0, he, -, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p0, _, hp0, ⟨q, hqp, hqe, hG2⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ | ⟨s, hs, hf⟩ |
    hc7 | hc8 | hc9
  ·
    obtain ⟨f⟩ := hf
    have hpp : p0.Prime := Fact.out
    by_cases h3e : p0 ^ e = 3
    · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp h3e
      exact (not_simple_projSL_two 3 (Or.inr rfl) hS hnab f).elim
    · have hodd' : Odd (p0 ^ e) := (hpp.odd_of_ne_two hp0).pow
      have hadm : StatedLieAdmissible .PSL 2 p0 e := by
        refine ⟨hpp, he, le_refl 2, fun h => ?_, fun h => h3e (Prod.mk.inj h).2⟩
        have h2 := (Prod.mk.inj h).2
        rw [h2] at hodd'
        exact (Nat.not_even_iff_odd.mpr hodd') even_two
      exact chain_psl f hp hp7 (lieModel_projSL hadm) (by norm_num) (fun h => absurd h (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    exact chain_psl f hp hp7 (lieModel_projSL (n := 3) (p := p0) (e := e)
      ⟨Fact.out, he, by norm_num, fun h => by simp at h, fun h => by simp at h⟩) (by norm_num)
      (fun _ => hlt (by norm_num) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    have hpp : p0.Prime := Fact.out
    exact chain_psu f hp hp7 (lieModel_projSU (n := 3) (p := p0) (e := e)
      ⟨hpp, he, le_refl 3, fun h => by
        have h2 := (Prod.mk.inj h).2
        have : p0 ≤ p0 ^ e := Nat.le_self_pow (by omega) p0
        omega⟩) (by norm_num) (hlt (by norm_num) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    exact (outPNice_of_isCyclic_outer hp (hI.ree hr f)).toChain
  ·
    obtain ⟨hqv, ⟨g⟩⟩ := hG2
    exact (hI.g2 q hqv hp g).toChain
  ·
    obtain ⟨f⟩ := hf
    have hpp : p0.Prime := Fact.out
    exact outPChain_psp_two_odd hp hp7 hpp (stated_of_lieModel f (lieModel_projSp (n := 2)
      (p := p0) (e := 1) ⟨hpp, le_rfl, le_refl 2, fun h => by
        have h2 := (Prod.mk.inj h).2
        rw [pow_one] at h2
        omega⟩) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    exact chain_psl f hp hp7 (lieModel_projSL (n := 4) (p := p0) (e := 1)
      ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
      (by norm_num) (fun _ => hlt (by norm_num) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    exact chain_psu f hp hp7 (lieModel_projSU (n := 4) (p := p0) (e := 1)
      ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h⟩) (by norm_num)
      (hlt (by norm_num) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    refine hnd fun hd => ?_
    have hle : Nat.card (Outer S) ≤ 4 :=
      (Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv).trans_le
        (CFSG.RankThree.PartOne.card_outer_alternating_le_four hn5)
    have hpos : 0 < Nat.card (Outer S) := Nat.card_pos
    have := Nat.le_of_dvd hpos hd
    omega
  ·
    obtain ⟨f⟩ := hf
    refine hnd fun hd => hI.spor s hp hp2 ?_
    rwa [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv]
  ·
    rcases hc7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hG2⟩ | ⟨q, hqv, hq2, hf⟩ |
      ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact (not_simple_projSL_two 2 (Or.inl rfl) hS hnab f).elim
      · have hne := two_pow_ne_of_two_le' hn2
        exact chain_psl f hp hp7 (lieModel_projSL (n := 2) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2,
            fun h => hne.2 (Prod.mk.inj h).2⟩) (by norm_num) (fun h => absurd h (by norm_num))
    ·
      obtain ⟨f⟩ := hf
      exact chain_psl f hp hp7 (lieModel_projSL (n := 3) (p := 2) (e := n)
        ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
        (by norm_num) (fun _ => hlt (by norm_num) (by norm_num))
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact (not_simple_projSU_three_two hS hnab f).elim
      · have hne := two_pow_ne_of_two_le' hn2
        exact chain_psu f hp hp7 (lieModel_projSU (n := 3) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 3, fun h => hne.1 (Prod.mk.inj h).2⟩) (by norm_num)
          (hlt (by norm_num) (by norm_num))
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact (not_simple_projSp_two_two hS hnab f).elim
      · have hne := two_pow_ne_of_two_le' hn2
        exact chain_psp f hp hp7 (lieModel_projSp (n := 2) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2⟩) (by norm_num)
          (fun _ => rfl)
    ·
      obtain ⟨f⟩ := hf
      exact chain_psu f hp hp7 (lieModel_projSU (n := 4) (p := 2) (e := n)
        ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h⟩) (by norm_num)
        (hlt (by norm_num) (by norm_num))
    ·
      obtain ⟨hqv, ⟨g⟩⟩ := hG2
      exact (hI.g2 q hqv hp g).toChain
    ·
      obtain ⟨f⟩ := hf
      exact (hI.d4 q hqv hq2 hp f).toChain
    ·
      obtain ⟨f⟩ := hf
      exact (hI.sz m hm hp f).toChain
    ·
      obtain ⟨f⟩ := hf
      exact (hI.f4r m hm hp f).toChain
    ·
      obtain ⟨f⟩ := hf
      refine hnd fun hd => ?_
      have h2 := hI.tits ht f
      rw [h2] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
  ·
    rcases hc8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf | hf | hf | hf |
      hf
    all_goals obtain ⟨f⟩ := hf
    ·
      exact chain_psl f hp hp7 (lieModel_projSL (n := 5) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (fun _ => hlt (by norm_num) (by norm_num))
    ·
      exact chain_psu f hp hp7 (lieModel_projSU (n := 5) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (hlt (by norm_num) (by norm_num))
    ·
      exact chain_psl f hp hp7 (lieModel_projSL (n := 6) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (fun _ => hlt (by norm_num) (by norm_num))
    ·
      exact chain_psu f hp hp7 (lieModel_projSU (n := 6) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (hlt (by norm_num) (by norm_num))
    ·
      exact chain_psl f hp hp7 (lieModel_projSL (n := 7) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (fun _ => by
          have h1 : Nat.gcd 7 (2 ^ 1 - 1) = 1 := by norm_num
          rw [h1]
          intro hd
          have := Nat.le_of_dvd one_pos hd
          omega)
    ·
      exact chain_psp f hp hp7 (lieModel_projSp (n := 3) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (fun h => absurd h (by norm_num))
    ·
      exact chain_psp f hp hp7 (lieModel_projSp (n := 4) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (fun h => absurd h (by norm_num))
    ·
      exact chain_pomegaPlus f hp hp7 (lieModel_projOmegaPlus (n := 4) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, le_refl 4⟩) (by norm_num)
    ·
      exact chain_pomegaMinus f hp hp7 (lieModel_projOmegaMinus (n := 4) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, le_refl 4⟩ hbc) (by norm_num)
    ·
      exact chain_psl f hp hp7 (lieModel_projSL (n := 4) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num)
        (fun _ => hlt (by norm_num) (by norm_num))
    ·
      exact chain_psp f hp hp7 (lieModel_projSp (n := 3) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num) (fun h => absurd h (by norm_num))
    ·
      exact chain_psu f hp hp7 (lieModel_projSU (n := 5) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num) (hlt (by norm_num) (by norm_num))
    ·
      exact chain_psu f hp hp7 (lieModel_projSU (n := 5) (p := 2) (e := 3)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num) (hlt (by norm_num) (by norm_num))
    ·
      exact (hI.f42 hp f).toChain
  ·
    rcases hc9 with ⟨e, he1, he3, hf | hf⟩ | hf | hf | hf
    all_goals obtain ⟨f⟩ := hf
    ·
      exact chain_psl f hp hp7 (lieModel_projSL (n := 3) (p := 3) (e := e)
        ⟨Nat.prime_three, he1, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
        (by norm_num) (fun _ => hlt (by norm_num) (by norm_num))
    ·
      exact chain_psu f hp hp7 (lieModel_projSU (n := 3) (p := 3) (e := e)
        ⟨Nat.prime_three, he1, le_refl 3, fun h => by
          have h2 := (Prod.mk.inj h).2
          have := Nat.le_self_pow (by omega : e ≠ 0) 3
          omega⟩) (by norm_num) (hlt (by norm_num) (by norm_num))
    ·
      exact (hI.g2 _ _ hp f).toChain
    ·
      exact chain_psl f hp hp7 (lieModel_projSL (n := 4) (p := 3) (e := 1)
        ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
        (by norm_num) (fun _ => hlt (by norm_num) (by norm_num))
    ·
      exact chain_psu f hp hp7 (lieModel_projSU (n := 4) (p := 3) (e := 1)
        ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by simp at h⟩) (by norm_num)
        (hlt (by norm_num) (by norm_num))

end CFSG.RankThree.PartTwo.Sec13.F135Last

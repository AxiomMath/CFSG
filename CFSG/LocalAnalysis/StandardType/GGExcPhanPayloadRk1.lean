module

public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
public import CFSG.LocalAnalysis.StandardType.ExcPay.RouteE7Three
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724
import CFSG.LocalAnalysis.StandardType.GGResidualRk1SUTwo
import CFSG.LocalAnalysis.StandardType.ExcPay.TwE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg

theorem markTag_exc_aux {lab : LargeEvenLabel} {t : StatedLieTag}
    (ht : t = .twistedE6 ∨ t = .E7 ∨ t = .E8) (h : markTag lab = t) :
    lab.tag ≠ .A ∧ lab.tag ≠ .twD ∧ markDeg lab = lab.n := by
  obtain ⟨tg, rk, m⟩ := lab
  rcases ht with rfl | rfl | rfl <;> cases tg <;> simp_all [markTag, markDeg] <;>
    split_ifs at h <;> simp_all


theorem exists_label_of_isCentralQuotientOf_exc {t : StatedLieTag}
    (ht : t = .twistedE6 ∨ t = .E7 ∨ t = .E8) {f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (h : IsCentralQuotientOf (lieUniversal t 0 2 f Nat.prime_two) X) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (X ⧸ Subgroup.center X) ∧
      markTag lab = t ∧ lab.n = f := by
  obtain ⟨θ, hθ, hker⟩ := h
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    rcases ht with rfl | rfl | rfl <;> trivial
  have hadm : StatedLieAdmissible t 0 2 f := by
    rcases ht with rfl | rfl | rfl <;> exact ⟨Nat.prime_two, hf, rfl⟩
  have h0 := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t 0 2 f Nat.prime_two hfund hadm
  have heq : CFSG.ClassicalInvolution.Generic.modelUniv t 0 2 f Nat.prime_two =
      lieUniversal t 0 2 f Nat.prime_two := by
    rcases ht with rfl | rfl | rfl <;> rfl
  have key : ∀ M : LieUniversal, CFSG.ClassicalInvolution.Generic.modelUniv t 0 2 f
      Nat.prime_two = M → CFSG.Open.IsQuasisimple M.K ∧
        LieModel (M.K ⧸ Subgroup.center M.K) t 0 2 f := by
    rintro M rfl; exact h0
  obtain ⟨hq, hm⟩ := key _ heq
  have hperf : commutator (lieUniversal t 0 2 f Nat.prime_two).K = ⊤ := hq.1
  obtain ⟨e⟩ := nonempty_centerQuotEquiv_aux (Group.isPerfect_def.mpr hperf) θ hθ hker
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ', hP⟩ :=
    largeEvenMarking_exists_hasLabel
      (CFSG.StandardType.largeEvenMarking_of_lieModel_centerQuot hperf hm)
  obtain ⟨h1, -, -, h3⟩ := hP
  obtain ⟨-, -, hdeg⟩ := markTag_exc_aux ht h1
  exact ⟨lab, hlab, ggHasLabel_congr_aux hhas e, h1, by rw [← hdeg]; exact h3⟩

section Payload


theorem GGExcPhanPayloadOf.exists_rk1ConclEx {n : ℕ} {N : CoxeterMatrix (Fin n)} {t : StatedLieTag}
    (ht : t = .twistedE6 ∨ t = .E7 ∨ t = .E8) (hn : n ≠ 0) {p : ℕ} (hp : p.Prime)
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (h : GGExcPhanPayloadOf n N t p Bs X)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)) (hpl : p ∣ 2 ^ lab.n + 1) :
    ∃ r ∈ ggAutomizer X Bs, GGIsReflection p r ∧ GGRk1ConclEx p Bs X r := by
  obtain ⟨f, hf4, hCQ, s, hs, F, _, _, _, hF, hiso, -, -⟩ := h
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h0
    · norm_num at hf4
    · exact h0
  obtain ⟨lab₀, hΛ₀, hlab₀, htag₀, hn₀⟩ := exists_label_of_isCentralQuotientOf_exc ht hf1 hCQ
  obtain ⟨hA₀, hD₀, -⟩ := markTag_exc_aux ht htag₀
  have hfield : ∀ l : LargeEvenLabel, LargeEvenInLambda2 l →
      GGHasLabel l (↥X ⧸ Subgroup.center ↥X) → l.n = f := by
    intro l hl hhl
    rw [← hn₀]
    exact (NSJoin.ggLabelIso_n_eq (ggLabelRigidInput_holds lab₀ l _ hΛ₀ hl hlab₀ hhl) hA₀
      (fun h => absurd h hD₀)).symm
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by have := hΛ.1; omega))).mp hpl
    omega
  have hpf : p ∣ 2 ^ f + 1 := by rw [← hfield lab hΛ hlab]; exact hpl
  have hXns : ¬ GGSplitLie p X := by
    intro hsplit
    obtain ⟨l, hl, hhl, hpl'⟩ := ggSplitLie_label hp hp2 hsplit
    rw [hfield l hl hhl] at hpl'
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpf hpl'
      rwa [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  obtain ⟨hsA, hsR⟩ := hs i
  exact ⟨s i, hsA, hsR, ggRk1ConclEx_of_su_two_rankOne_of_label ggLabelRigidInput_holds hsA hsR hF
    (hiso i) hXns hpf hΛ₀ hlab₀ hA₀ (fun h => absurd h hD₀) hn₀⟩

section Rows


theorem ExcPay.exists_rk1ConclEx_of_marking_E7 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp3 : p ≠ 3) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 2 ≤ lab.n) p Bs X) :
    ∃ r ∈ ggAutomizer X Bs, GGIsReflection p r ∧ GGRk1ConclEx p Bs X r := by
  obtain ⟨lab, hΛ, hhas, -, -, -, -, -, ⟨⟨-, hpl⟩, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hmark
  exact (ExcPay.exists_excPhanPayload_of_marking_E7 hp hp3 hBs hSC hmark).exists_rk1ConclEx
    (Or.inr (Or.inl rfl)) (by norm_num) hp hΛ hhas hpl

theorem ExcPay.exists_rk1ConclEx_of_route_E7_three {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr 3 B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 2 ≤ lab.n) 3 Bs X) :
    ∃ r ∈ ggAutomizer X Bs, GGIsReflection 3 r ∧ GGRk1ConclEx 3 Bs X r := by
  obtain ⟨lab, hΛ, hhas, -, -, -, -, -, ⟨⟨-, hpl⟩, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hmark
  exact (ExcPay.exists_excPhanPayload_of_route_E7_three hcfg hX hmark).exists_rk1ConclEx
    (Or.inr (Or.inl rfl)) (by norm_num) Nat.prime_three hΛ hhas hpl

theorem ExcPay.exists_rk1ConclEx_of_marking_TwE6 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp3 : p ≠ 3) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X) :
    ∃ r ∈ ggAutomizer X Bs, GGIsReflection p r ∧ GGRk1ConclEx p Bs X r := by
  obtain ⟨lab, hΛ, hhas, -, -, -, -, -, ⟨⟨-, hpl⟩, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hmark
  exact (ExcPay.exists_excPhanPayload_of_marking_TwE6 hp hp3 hBs hSC hmark).exists_rk1ConclEx
    (Or.inl rfl) (by norm_num) hp hΛ hhas hpl

end Rows

end Payload

end CFSG.StandardType

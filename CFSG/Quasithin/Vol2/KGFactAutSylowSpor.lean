module

public import CFSG.Quasithin.Vol2.KGFactAutSylowSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.Schreier.PairHSFaithful
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Ru
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.SteinbergBR.OddSylow CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Open (pCoreOf)

theorem exists_selfNormalizing_of_rows {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (mems : List Mem) (hk : 1 ≤ (Nat.card Q).factorization 2)
    (hne : Nat.card Q ≠ 2 ^ (Nat.card Q).factorization 2)
    (hrows : ∀ m ∈ mems, 2 ^ (Nat.card Q).factorization 2 ≤ m.o2 →
      m.order = 2 ^ (Nat.card Q).factorization 2)
    (hover : ∀ T Y : Subgroup Q, IsSylowTwoOf T ⊤ → T ≤ Y →
      Y = ⊤ ∨ ∃ m ∈ mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
        ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2) :
    (∃ P₀ : Sylow 2 Q, Subgroup.normalizer (P₀ : Set Q) = P₀) ∧ Subgroup.center Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ : Sylow 2 Q := default
  have hP₀ : IsSylowTwoOf (P₀ : Subgroup Q) ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨P₀.isPGroup', P₀.not_dvd_index⟩
  have hcard : Nat.card (P₀ : Subgroup Q) = 2 ^ (Nat.card Q).factorization 2 :=
    P₀.card_eq_multiplicity
  have hnn : ¬ (P₀ : Subgroup Q).Normal := by
    intro hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P₀ : Subgroup Q) with h | h
    · rw [h, Subgroup.card_bot] at hcard
      have : 2 ^ 1 ≤ 2 ^ (Nat.card Q).factorization 2 := Nat.pow_le_pow_right (by norm_num) hk
      omega
    · rw [h, Subgroup.card_top] at hcard
      exact hne hcard
  refine ⟨⟨P₀, ?_⟩, ?_⟩
  · set N := Subgroup.normalizer ((P₀ : Subgroup Q) : Set Q) with hN
    have hPN : (P₀ : Subgroup Q) ≤ N := Subgroup.le_normalizer
    rcases hover _ N hP₀ hPN with htop | ⟨m, hm, hmo, hmo2, -⟩
    · exact absurd (Subgroup.normalizer_eq_top_iff.mp htop) hnn
    · have hle : (P₀ : Subgroup Q) ≤ pCoreOf 2 N :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPN le_rfl P₀.isPGroup'
      have h1 : 2 ^ (Nat.card Q).factorization 2 ≤ m.o2 := by
        rw [← hcard, ← hmo2]
        exact Subgroup.card_le_of_le hle
      have h2 := hrows m hm h1
      exact (Subgroup.eq_of_le_of_card_ge hPN (by rw [hmo, h2, hcard])).symm
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      apply hnn
      refine ⟨fun p hp g => ?_⟩
      have hg : g ∈ Subgroup.center Q := h ▸ Subgroup.mem_top g
      rw [(Subgroup.mem_center_iff.mp hg p).symm]
      simpa using hp

theorem autSylowSelfNorm_of_equiv {Q Γ : Type} [Group Q] [Group Γ] [Finite Q] [Finite Γ]
    (e : Q ≃* Γ) (hZ : Subgroup.center Γ = ⊥)
    (hex : ∃ P₀ : Sylow 2 Γ, Subgroup.normalizer (P₀ : Set Γ) = P₀)
    (hout : Nat.card (Outer Γ) ≤ 2) : AutSylowSelfNorm Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hex
  have : Finite (MulAut Γ) :=
    Finite.of_injective (fun f : MulAut Γ => (f : Γ → Γ)) DFunLike.coe_injective
  have h0 : 0 < Nat.card (Outer Γ) := Nat.card_pos
  have hout' : Nat.card (Outer Γ) ∣ 2 := by
    interval_cases (Nat.card (Outer Γ)) <;> norm_num
  refine autSylowSelfNorm_of ?_ (exists_selfNormalizing_of_equiv e P₀ hP₀)
    (isPGroup_outer_of_dvd_two (by rw [card_outer_congr e]; exact hout'))
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [hZ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [h1, map_one])

theorem card_outer_le_two_of_inner {Γ : Type} [Group Γ]
    (h : ∀ α : MulAut Γ, α ∈ inner Γ) : Nat.card (Outer Γ) ≤ 2 := by
  have : Subsingleton (Outer Γ) := by
    refine ⟨fun p q => ?_⟩
    induction p using QuotientGroup.induction_on with
    | H α =>
      induction q using QuotientGroup.induction_on with
      | H β =>
        rw [QuotientGroup.eq]
        exact h _
  rw [Nat.card_unique]
  norm_num

open CFSG.Blueprint.NativeSporadic in
theorem factAutSylowM24_holds :
    FactAutSylowM24 := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  have : Finite (Carrier .M24) := Finite.of_equiv Q e.toEquiv
  have : IsSimpleGroup (Carrier .M24) := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hcard : Nat.card (Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  have hf : (Nat.card (Carrier .M24)).factorization 2 = 10 := by
    rw [hcard, show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 239085)]
    simp
  obtain ⟨hex, hZ⟩ := exists_selfNormalizing_of_rows (Q := Carrier .M24) M24.m24Mems
    (by rw [hf]; norm_num) (by rw [hf, hcard]; norm_num) (by rw [hf]; decide)
    (fun T Y hT hTY => M24.m24_overgroups ⟨MulEquiv.refl _⟩ hT hTY)
  exact autSylowSelfNorm_of_equiv e hZ hex
    (card_outer_le_two_of_inner CFSG.QuasithinUnique.Ch1.m24_all_inner)

open CFSG.Blueprint.NativeSporadic in
theorem factAutSylowHS_holds :
    FactAutSylowHS := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  have : Finite (Carrier .HS) := Finite.of_equiv Q e.toEquiv
  have : IsSimpleGroup (Carrier .HS) := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hcard : Nat.card (Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
  have hf : (Nat.card (Carrier .HS)).factorization 2 = 9 := by
    rw [hcard, show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 86625)]
    simp
  obtain ⟨hex, hZ⟩ := exists_selfNormalizing_of_rows (Q := Carrier .HS) HS.hsMems
    (by rw [hf]; norm_num) (by rw [hf, hcard]; norm_num) (by rw [hf]; decide)
    (fun T Y hT hTY => HS.hs_overgroups ⟨MulEquiv.refl _⟩ hT hTY)
  exact autSylowSelfNorm_of_equiv e hZ hex
    (CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
      CFSG.Sporadic.Schreier.hsPermEquiv)

open CFSG.Blueprint.NativeSporadic in
theorem factAutSylowRu_holds :
    FactAutSylowRu := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  have : Finite (Carrier .Ru) := Finite.of_equiv Q e.toEquiv
  have : IsSimpleGroup (Carrier .Ru) := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hcard : Nat.card (Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
  have hf : (Nat.card (Carrier .Ru)).factorization 2 = 14 := by
    rw [hcard, show (145926144000 : ℕ) = 2 ^ 14 * 8906625 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 8906625)]
    simp
  obtain ⟨hex, hZ⟩ := exists_selfNormalizing_of_rows (Q := Carrier .Ru) Ru.ruMems
    (by rw [hf]; norm_num) (by rw [hf, hcard]; norm_num) (by rw [hf]; decide)
    (fun T Y hT hTY => Ru.ru_overgroups ⟨MulEquiv.refl _⟩ hT hTY)
  have h1 : Nat.card (Outer CFSG.Sporadic.RuSchreier.ruP) ≤ 2 := by
    rw [CFSG.Sporadic.RuSchreier.card_outer_ruP]
    norm_num
  exact autSylowSelfNorm_of_equiv e hZ hex
    (CFSG.Sporadic.Schreier.outer_card_le_of_equiv h1 CFSG.Sporadic.RuSchreier.ruEquivP)

end CFSG.Quasithin.H13.KGAutSyl

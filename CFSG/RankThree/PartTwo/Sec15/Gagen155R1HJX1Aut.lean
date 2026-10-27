module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofJ2
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAction
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1D

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def actionOnQuot {A K : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {S : Type} [Group S]
    (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S) : ↥A →* MulAut S :=
  (MulAut.congr φ).toMonoidHom.comp
    ((CFSG.ComponentClassification.TBLit.quotAutOfChar (CFSG.pPrimeCore 3 ↥K)).comp
      (conjAutK K A hAK))

theorem actionOnQuot_apply {A K : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    {S : Type} [Group S] (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S) (a : ↥A) :
    actionOnQuot hAK φ a = MulAut.congr φ
      (CFSG.ComponentClassification.TBLit.quotAutOfChar (CFSG.pPrimeCore 3 ↥K)
        (conjAutK K A hAK a)) := rfl

theorem commutator_mem_pPrimeCoreOf_of_actionOnQuot_eq_one {A K : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {S : Type} [Group S]
    (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S) (a : ↥A)
    (ha1 : actionOnQuot hAK φ a = 1) :
    ∀ x ∈ K, (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K := by
  intro x hx
  have hq : CFSG.ComponentClassification.TBLit.quotAutOfChar (CFSG.pPrimeCore 3 ↥K)
      (conjAutK K A hAK a) = 1 := by
    apply (MulAut.congr φ).injective
    rw [← actionOnQuot_apply hAK φ a, ha1, map_one]
  let xK : ↥K := ⟨x, hx⟩
  have hfix : CFSG.ComponentClassification.TBLit.quotAutOfChar (CFSG.pPrimeCore 3 ↥K)
      (conjAutK K A hAK a) (xK : ↥K ⧸ CFSG.pPrimeCore 3 ↥K) =
        (xK : ↥K ⧸ CFSG.pPrimeCore 3 ↥K) := by
    rw [hq, MulAut.one_apply]
  rw [CFSG.ComponentClassification.TBLit.quotAutOfChar_mk] at hfix
  have hmem : (conjAutK K A hAK a) xK / xK ∈ CFSG.pPrimeCore 3 ↥K :=
    QuotientGroup.eq_iff_div_mem.mp hfix
  rw [pPrimeCoreOf, Subgroup.mem_map]
  refine ⟨(conjAutK K A hAK a) xK / xK, hmem, ?_⟩
  show (((conjAutK K A hAK a) xK / xK : ↥K) : G) = (a : G) * x * (a : G)⁻¹ * x⁻¹
  rw [Subgroup.coe_div, div_eq_mul_inv, conjAutK_apply_coe]

theorem exists_centralizing_subgroup {A K : Subgroup G} (hA : Late.IsE27 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {S : Type} [Group S]
    (hS : ∀ B : Subgroup (MulAut S), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9)
    (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ A₀ ≠ ⊥ ∧
      ∀ a ∈ A₀, ∀ x ∈ K, a * x * a⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K := by
  classical
  let ρ : ↥A →* MulAut S := actionOnQuot hAK φ
  have hEl : CFSG.Assembly.IsElemAbelian 3 ρ.range := by
    haveI : IsMulCommutative ↥A := hA.1.1
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg ρ (mul_comm' a b)
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
      rw [← ha, ← map_pow]
      have ha3 : a ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hA.1.2 (a : G) a.2
      rw [ha3, map_one]
  have hle : Nat.card ρ.range ≤ 9 := hS ρ.range hEl
  have hcard : Nat.card ρ.ker * Nat.card ρ.range = 27 := by
    rw [Subgroup.card_ker_mul_card_range ρ]
    exact hA.2
  have hker : ρ.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul] at hcard
    omega
  refine ⟨ρ.ker.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro hbot
    have h1 : Nat.card (ρ.ker.map A.subtype) = Nat.card ρ.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [hbot, Subgroup.card_bot] at h1
    rw [← h1, one_mul] at hcard
    omega
  · intro a ha x hx
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha
    have hb1 : actionOnQuot hAK φ b = 1 := MonoidHom.mem_ker.mp hb
    have h := commutator_mem_pPrimeCoreOf_of_actionOnQuot_eq_one hAK φ b hb1 x hx
    have hba' : (b : G) = a := hba
    rwa [hba'] at h

theorem not_surj_j2_projSL_seven [Fact (Nat.Prime 7)]
    (H' : Subgroup CFSG.Blueprint.NativeSporadic.J2)
    (f' : ↥H' →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :
    ¬ Function.Surjective f' := by
  intro hf
  have h1 : Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) ≤
      Nat.card ↥H' :=
    Nat.card_le_card_of_surjective f' hf
  rw [Proof1515.card_projSL_three_seven] at h1
  have hdvd : Nat.card ↥H' ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 :=
    Subgroup.card_subgroup_dvd_card H'
  rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2] at hdvd
  have h2 : Nat.card ↥H' ≤ 604800 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem not_surj_j2_alt7 (h415 : Sec4.Item4_15) (H' : Subgroup CFSG.Blueprint.NativeSporadic.J2)
    (f' : ↥H' →* alternatingGroup (Fin 7)) : ¬ Function.Surjective f' := by
  exact Sec15.ks1515J2NoA7_of h415 CFSG.Blueprint.NativeSporadic.J2 ⟨MulEquiv.refl _⟩ ↥H'
    H'.subtype H'.subtype_injective f'

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

module

public import CFSG.Quasithin.Background.SimsE213MSp4
public import CFSG.Quasithin.Background.SimsE210Parts
public import CFSG.Quasithin.Background.RonanE211Main
public import CFSG.Quasithin.Background.E2KGSz8CoverPf
public import CFSG.Quasithin.Background.E2KGI22OnePf
public import CFSG.Quasithin.Vol2.E2ThirteenMembers
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinRed
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.E2SevenStatement
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E213M

variable {Γ : Type} [Group Γ]

theorem noRoot_of_isInIHTV {H T M V I : Subgroup Γ} (h : IsInIHTV H T M V I) :
    ASInputs.IsInIHTVNoRootAt H T M V I (E1.nParam (⊤ : Subgroup (E2.StarQuot M H))) := by
  obtain ⟨h1, ⟨g, hg, hgen⟩, h3, h4, k, hk, hc⟩ := h
  refine ⟨h1, ⟨g⁻¹, I.inv_mem hg, ?_⟩, h3, h4, k, hk, ?_⟩
  · rw [← SimsE210.conjSubgroup_eq_conjSub]
    exact hgen
  · rcases hc with hc | hc | ⟨a, b, c, d, e, -⟩
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ⟨a, b, c, d, e⟩)

theorem exists_relIndex_eq_two_pow [Finite Γ] {X : Subgroup Γ} (hX : IsPGroup 2 X)
    (U : Subgroup Γ) : ∃ a : ℕ, U.relIndex X = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.mp hX
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hv ▸ Subgroup.relIndex_dvd_card U X)
  exact ⟨a, ha⟩

variable [Finite Γ]

theorem ne_and_rank {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I) (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hcharI : CharTwo I) :
    I ≠ V ∧
      (kerIn (M ⊓ I) I ⊓ V).relIndex V ≤ (V ⊓ B6.conjSub g V).relIndex (kerIn (M ⊓ I) I ⊓ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := E2P.finite_starQuot (M ⊓ I) I
  have hpI : I = V → IsPGroup 2 (E2.StarQuot (M ⊓ I) I) := by
    intro hIV
    have hV2 : IsPGroup 2 ↥V := B6.isPGroup_of_isElemAbelian h.elem
    rw [← hIV] at hV2
    exact hV2.to_quotient _
  obtain ⟨-, -, hsyl, -, k, -, hc⟩ := hI
  have hDih : ASInputs.IsDihL2Sz (E2.StarQuot (M ⊓ I) I) →
      I ≠ V ∧ (kerIn (M ⊓ I) I ⊓ V).relIndex V ≤
        (V ⊓ B6.conjSub g V).relIndex (kerIn (M ⊓ I) I ⊓ V) := fun hD =>
    ⟨fun hIV => E2.not_isPGroup_of_isDihL2Sz hD (hpI hIV), hp.relIndex_le_of_isDihL2Sz hcharI hD⟩
  rcases hc with ⟨-, hY, -⟩ | ⟨-, p, a, hp', hp2, ha, ⟨e⟩⟩ | ⟨-, hk1, hY, -, hcent, -⟩
  · rcases hY with hY | hY
    · exact hDih (Or.inr (Or.inl ⟨k, hY⟩))
    · exact hDih (Or.inr (Or.inr ⟨k, hY⟩))
  · exact hDih (Or.inl ⟨p ^ a, (hp'.odd_of_ne_two hp2).pow, Nat.one_lt_pow (by omega) hp'.one_lt,
      ⟨e⟩⟩)
  · have hdvd := sq_add_one_dvd_card hY
    have hVT : E2.star (M ⊓ I) I V ≤ E2.star (M ⊓ I) I (T ⊓ I) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono I (le_inf h.le_T hp.V_le))
    have hV := card_le_of_le_centralizer hY (E2.isSylowTwoOf_star_inf (M := M) hsyl) hVT hcent
    rw [SimsE210.natCard_star_eq_relIndex hp.V_le] at hV
    refine ⟨fun hIV => ?_, Ch3E213M.relIndex_le_of_sp4 hp hcharI hk1 hdvd hV⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hpI hIV)
    have hq : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
    refine E2.false_of_odd_dvd_two_pow (d := (2 ^ k) ^ 2 + 1) ?_ ?_ (hn ▸ hdvd)
    · rw [hq]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    · have : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega

theorem parts {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g) (hIH : I ≤ H)
    (h4 : B6.conjSub g V ⊓ pCoreOf 2 I = B6.conjSub g V ⊓ Subgroup.normalizer (V : Set Γ))
    (hJ : pCoreOf 2 I = kerIn (M ⊓ I) I)
    (h5c : ∀ x ∈ I, (∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V)) ↔
      x ∈ pCoreOf 2 I)
    (hcharI : CharTwo I) (hIV : I ≠ V)
    (hrank : (kerIn (M ⊓ I) I ⊓ V).relIndex V ≤
      (V ⊓ B6.conjSub g V).relIndex (kerIn (M ⊓ I) I ⊓ V))
    (A : Subgroup Γ) (hA : A = B6.conjSub g V ⊓ pCoreOf 2 I) :
    (A = B6.conjSub g V ⊓ Subgroup.normalizer (V : Set Γ) ∧ ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧
        ⁅V, A⁆ ≠ ⊥ ∧ A ⊓ Subgroup.centralizer (V : Set Γ) = V ⊓ B6.conjSub g V ∧
        E3.mQuot V (V ⊓ Subgroup.centralizer (A : Set Γ)) ≤
          2 * E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set Γ))) ∧
      (V ⊓ B6.conjSub g V = ⊥ → qOf (autI h.elem H) ≤ ((1 : ℚ) : WithTop ℚ)) ∧
      (∀ P : Subgroup Γ, P = (pCoreOf 2 I ⊓ V) ⊔ A →
        (∀ x ∈ I, (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V) → x ∈ pCoreOf 2 I) ∧
        pCoreOf 2 I = kerIn (M ⊓ I) I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hAel, hcub, hnc, hCA⟩ := Ch3n.exists_cubic_of_pair hp hcharI hIV
  have hcount := Ch3n.count_of_pair hp hrank
  have hAeq := hp.conjSub_kerIn_inf_eq
  rw [hAeq, ← hA] at hAel hcub hnc hCA hcount
  set B := V ⊓ pCoreOf 2 I
  have hBk : kerIn (M ⊓ I) I ⊓ V = B := hp.kerIn_inf_eq
  have hAeq' : B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) = A := hAeq.trans hA.symm
  refine ⟨⟨hA.trans h4, hcub, fun hb => hnc (Subgroup.le_centralizer_iff.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hb)), hCA, ?_⟩, ?_, ?_⟩
  ·
    obtain ⟨a, ha⟩ := exists_relIndex_eq_two_pow (B6.isPGroup_of_isElemAbelian h.elem)
      (V ⊓ Subgroup.centralizer (A : Set Γ))
    obtain ⟨b, hb⟩ := exists_relIndex_eq_two_pow (B6.isPGroup_of_isElemAbelian hAel)
      (A ⊓ Subgroup.centralizer (V : Set Γ))
    rw [ha, hb, ← pow_mul] at hcount
    unfold E3.mQuot
    rw [ha, hb, padicValNat.prime_pow, padicValNat.prime_pow]
    rw [mul_comm]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcount
  ·
    intro hZ
    have hss := hrank
    rw [hBk, hZ, Subgroup.relIndex_bot_left] at hss
    have hAN : A ≤ Subgroup.normalizer (V : Set Γ) := by
      rw [hA, h4]
      exact inf_le_right
    have hAH : A ≤ H := by
      rw [hA]
      exact (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)).trans hIH
    have hcardA : Nat.card A = Nat.card B := by
      rw [← hAeq', hBk]
      exact (Nat.card_congr ((MulAut.conj g).subgroupMap B).toEquiv).symm
    have hCA1 : A ⊓ Subgroup.centralizer (V : Set Γ) = ⊥ := hCA.trans hZ
    have hBC : B ≤ V ⊓ Subgroup.centralizer (A : Set Γ) := by
      refine fun b hb => ⟨hb.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
      have hb' : b ∈ kerIn (M ⊓ I) I ⊓ V := by rw [hBk]; exact hb
      have ha' : a ∈ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) := by rw [hAeq']; exact ha
      have hc := hp.commutator_B_A hb' ha'
      rw [hZ, Subgroup.mem_bot] at hc
      have : b * a = a * b := by
        calc b * a = (b * a * b⁻¹ * a⁻¹) * (a * b) := by group
          _ = a * b := by rw [hc, one_mul]
      exact this.symm
    have hFF : IsFFModule (autI h.elem H) := by
      refine ⟨autI h.elem A, autI_mono h.elem hAH, ?_, ?_, ?_⟩
      · exact fun hb => hnc ((autI_eq_bot_iff h.elem hAN).1 hb)
      · exact isElemAbelian2_autI h.elem hAel hAN
      · have h1 := card_autI_mul_card_inf h.elem hAN
        rw [hCA1, Subgroup.card_bot, mul_one] at h1
        rw [card_fixV_autI h.elem hAN, h1, hcardA]
        have h2 := Subgroup.relIndex_mul_card B V
        rw [inf_eq_left.2 (inf_le_left : B ≤ V)] at h2
        calc Nat.card (IntMod V h.elem) = Nat.card V := rfl
          _ = B.relIndex V * Nat.card B := h2.symm
          _ ≤ Nat.card B * Nat.card B := Nat.mul_le_mul_right _ hss
          _ ≤ Nat.card B * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ)) :=
            Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hBC)
    have hq := (B1_4_5 (fun v => IntMod.sq_eq_one v) (autI h.elem H)).out 1 3
    rw [WithTop.coe_one]
    exact hq.mp hFF
  ·
    intro P hP
    rw [inf_comm (pCoreOf 2 I) V] at hP
    subst hP
    refine ⟨?_, hJ⟩
    have hZc : ∀ z ∈ V ⊓ B6.conjSub g V, ∀ i ∈ I, i * z * i⁻¹ = z := fun z hz i hi => by
      rw [← hp.mem_center hz hi]
      group
    have hPeq : (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) = B ⊔ A := by
      rw [hAeq', hBk]
    have hPn : I ≤ Subgroup.normalizer ((B ⊔ A : Subgroup Γ) : Set Γ) := by
      rw [← hPeq]
      exact hp.le_normalizer_P
    have hP2 : IsPGroup 2 ↥(B ⊔ A) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le (by rw [← hPeq]; exact hp.P_le_pCoreOf)
    let Y : Subgroup Γ :=
      { carrier := {x | x ∈ I ∧ ∀ y ∈ B ⊔ A, x * y * x⁻¹ * y⁻¹ ∈ V ⊓ B6.conjSub g V}
        mul_mem' := by
          rintro x x' ⟨hx, hxP⟩ ⟨hx', hx'P⟩
          refine ⟨I.mul_mem hx hx', fun y hy => ?_⟩
          have h1 := hx'P y hy
          have e : x * x' * y * (x * x')⁻¹ * y⁻¹ =
              (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
          rw [e, hZc _ h1 x hx]
          exact Subgroup.mul_mem _ h1 (hxP y hy)
        one_mem' := ⟨I.one_mem, fun y _ => by simp⟩
        inv_mem' := by
          rintro x ⟨hx, hxP⟩
          refine ⟨I.inv_mem hx, fun y hy => ?_⟩
          have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ B ⊔ A :=
            (Subgroup.mem_normalizer_iff.mp (hPn (I.inv_mem hx)) y).mp hy
          have h1 := hxP _ hy'
          have e : x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ * (x⁻¹ * y * x⁻¹⁻¹)⁻¹ =
              (x⁻¹ * y * x⁻¹⁻¹ * y⁻¹)⁻¹ := by group
          rw [e] at h1
          simpa using Subgroup.inv_mem _ h1 }
    have hY2 : ∀ x ∈ Y, ∃ n : ℕ, x ^ 2 ^ n = 1 := by
      rintro x ⟨hx, hxP⟩
      have hx2C : x ^ 2 ∈ Subgroup.centralizer ((B ⊔ A : Subgroup Γ) : Set Γ) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hz := hxP y hy
        have hz2 : (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) = 1 := by
          rw [← pow_two]
          exact h.elem.2 _ hz.1
        have hxy : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
        have key : x ^ 2 * y * (x ^ 2)⁻¹ = y := by
          rw [pow_two]
          calc x * x * y * (x * x)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by group
            _ = x * ((x * y * x⁻¹ * y⁻¹) * y) * x⁻¹ := by rw [← hxy]
            _ = (x * (x * y * x⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹) := by group
            _ = (x * y * x⁻¹ * y⁻¹) * ((x * y * x⁻¹ * y⁻¹) * y) := by
              rw [hZc _ hz x hx, ← hxy]
            _ = y := by rw [← mul_assoc, hz2, one_mul]
        calc y * x ^ 2 = (x ^ 2 * y * (x ^ 2)⁻¹) * x ^ 2 := by rw [key]
          _ = x ^ 2 * y := by group
      have hd : ∀ q ∈ pCoreOf 2 I, x ^ 2 * q * (x ^ 2)⁻¹ * q⁻¹ ∈ B ⊔ A := by
        intro q hq
        have hqI : q ∈ I := CFSG.LieType.BorelTits.pCoreOf_le 2 I hq
        have h1 := (h5c q hqI).mpr hq (x ^ 2) (I.pow_mem hx 2)
        rw [inf_comm (pCoreOf 2 I) V, inf_comm (pCoreOf 2 I) (B6.conjSub g V), ← hA] at h1
        have e : x ^ 2 * q * (x ^ 2)⁻¹ * q⁻¹ = (q * x ^ 2 * q⁻¹ * (x ^ 2)⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ h1
      obtain ⟨n, hn⟩ :=
        E2.exists_pow_two_pow_eq_one_of_stable hPn hP2 hcharI (I.pow_mem hx 2) hx2C hd
      exact ⟨n + 1, by rw [pow_succ', pow_mul]; exact hn⟩
    have hYI : Y ≤ I := fun x hx => hx.1
    have hYp : IsPGroup 2 ↥Y := fun x => by
      obtain ⟨n, hn⟩ := hY2 x x.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    have hYn : I ≤ Subgroup.normalizer (Y : Set Γ) := by
      intro i hi
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hx, hxP⟩
        refine ⟨I.mul_mem (I.mul_mem hi hx) (I.inv_mem hi), fun y hy => ?_⟩
        have hy' : i⁻¹ * y * i⁻¹⁻¹ ∈ B ⊔ A :=
          (Subgroup.mem_normalizer_iff.mp (hPn (I.inv_mem hi)) y).mp hy
        have h1 := hxP _ hy'
        have e : i * x * i⁻¹ * y * (i * x * i⁻¹)⁻¹ * y⁻¹ =
            i * (x * (i⁻¹ * y * i⁻¹⁻¹) * x⁻¹ * (i⁻¹ * y * i⁻¹⁻¹)⁻¹) * i⁻¹ := by group
        rw [e, hZc _ h1 i hi]
        exact h1
      · rintro ⟨hx, hxP⟩
        have hxI : x ∈ I := by
          have := I.mul_mem (I.mul_mem (I.inv_mem hi) hx) hi
          simpa [mul_assoc] using this
        refine ⟨hxI, fun y hy => ?_⟩
        have hy' : i * y * i⁻¹ ∈ B ⊔ A := (Subgroup.mem_normalizer_iff.mp (hPn hi) y).mp hy
        have h1 := hxP _ hy'
        have e : i * x * i⁻¹ * (i * y * i⁻¹) * (i * x * i⁻¹)⁻¹ * (i * y * i⁻¹)⁻¹ =
            i * (x * y * x⁻¹ * y⁻¹) * i⁻¹ := by group
        rw [e] at h1
        have h2 := hZc _ h1 i⁻¹ (I.inv_mem hi)
        have e2 : i⁻¹ * (i * (x * y * x⁻¹ * y⁻¹) * i⁻¹) * i⁻¹⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
        rw [e2] at h2
        rw [h2]
        exact h1
    intro x hxI hxP
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYI hYn hYp ⟨hxI, hxP⟩

end E213M

open E213M

theorem e213_member
    {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (hc : CharTwo H) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hIV : I = V ⊔ conjSubgroup V g) (A : Subgroup Γ) (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I) :
    (A = conjSubgroup V g ⊓ Subgroup.normalizer (V : Set Γ) ∧ ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧
        ⁅V, A⁆ ≠ ⊥ ∧ A ⊓ Subgroup.centralizer (V : Set Γ) = V ⊓ conjSubgroup V g ∧
        E3.mQuot V (V ⊓ Subgroup.centralizer (A : Set Γ)) ≤
          2 * E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set Γ))) ∧
      (V ⊓ conjSubgroup V g = ⊥ → qOf (autI h.elem H) ≤ ((1 : ℚ) : WithTop ℚ)) ∧
      (∀ P : Subgroup Γ, P = (pCoreOf 2 I ⊓ V) ⊔ A →
        (∀ x ∈ I, (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ V ⊓ conjSubgroup V g) → x ∈ pCoreOf 2 I) ∧
        pCoreOf 2 I = kerIn (M ⊓ I) I) := by
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  obtain ⟨hp, -, -, h4, hJ, -, h5c, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (noRoot_of_isInIHTV hI) (I.inv_mem hg) hgen
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 (I.inv_mem hg)) hc
    rwa [← hgen] at this
  obtain ⟨hne, hrank⟩ := ne_and_rank h hI hp hcharI
  rw [e] at hA ⊢
  exact parts h hp hI.1 h4 hJ h5c hcharI hne hrank A hA

end CFSG.Quasithin.SimsE2

module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofList
public import CFSG.RankThree.PartTwo.Sec16.Item1611ResProofConfig
public import CFSG.RankThree.PartTwo.Sec13.Item131a
import CFSG.RankThree.PartTwo.Sec16.Item1611Facts131
import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessConj
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypes
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGen
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofTorus
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTransOut
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec16.Item169General
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Two
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree
public import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1611Res

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

section Model

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem eq_one_of_commute_hessian (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : ProjGenLinGroup (Fin 3) K}
    (hx : x ∈ projImage (slPi π 3 (p ^ f) K))
    (hxd : ProjGenLinGroup.mk (diagTau hτ) * x = x * ProjGenLinGroup.mk (diagTau hτ))
    (hxc : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * x =
      x * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (hx3 : Nat.Coprime 3 (orderOf x)) : x = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨s, hsS, rfl, hsm⟩ := Sec16.ProofHess.exists_lift_pow_eq_one hK hx hx3
  have hm : Nat.Coprime (orderOf (ProjGenLinGroup.mk s)) 3 := hx3.symm
  have h1 := Sec16.ProofHess.commute_of_mk_commute hK hsS (diagTau_mem_slPi hπ hq' hτ) hxd hm hsm
  have h2 := Sec16.ProofHess.commute_of_mk_commute hK hsS (cycThree_mem_slPi hπ) hxc hm hsm
  have h1m : (s : Matrix (Fin 3) (Fin 3) K) * ((diagTau hτ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * s := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simpa only [Units.val_mul] using this
  have h2m : (s : Matrix (Fin 3) (Fin 3) K) * ((cycThree : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * s := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h2
    simpa only [Units.val_mul] using this
  have hM := eq_smul_one_of_commute hτ hτ1 h1m h2m
  refine KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_eq_smul hM ?_)
  intro h0
  have hdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hsS).2
  rw [hM, h0, zero_smul, det_zero] at hdet
  exact zero_ne_one hdet

theorem exists_mem_pCoreOf_hessian (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hp2 : p ≠ 2) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {dM cM : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)) :
    (∃ t ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({dM} : Set _)), t ≠ 1) ∧
      ∃ t ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({cM} : Set _)), t ≠ 1 := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hs : 1 + τ + τ ^ 2 = 0 := by
    have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hτ1
    · exact h
  set F : projImage (slPi π 3 (p ^ f) K) := ⟨ProjGenLinGroup.mk (fourierGL h3 hs),
    ⟨_, fourierGL_mem_slPi hK hq hτ h3 hs, rfl⟩⟩ with hF
  have hFd : F * dM * F⁻¹ = cM⁻¹ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hdM, hcM]
    exact mk_fourier_diagTau hτ h3 hs)
  set ta := Sec17.Proof17Res7.tM hK hp2 _ Sec17.Proof17Res7.isTInv_tOne with hta_def
  have hta : ta ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {dM}) :=
    Sec15.KL3FactsProof.tM_mem_pCoreOf_centralizer hK hp2 hτ hτ1 hdM hcM
  have hta1 : ta ≠ 1 := Sec17.Proof17Res7.tM_ne_one hK hp2 Sec17.Proof17Res7.isTInv_tOne
  refine ⟨⟨ta, hta, hta1⟩, F * ta * F⁻¹, ?_, ?_⟩
  · have h1 := Sec17.Proof17Res7.map_pCoreOf_centralizer_le (MulAut.conj F) dM ⟨ta, hta, rfl⟩
    rw [MulAut.conj_apply, hFd, Sec15.KL3FactsProof.centralizer_inv_singleton] at h1
    exact h1
  · intro h1
    apply hta1
    calc ta = F⁻¹ * (F * ta * F⁻¹) * F := by group
      _ = 1 := by rw [h1]; group

end Model

theorem not_isoLThreePi_of_card_eq_20160 {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hX : Nat.card X = 20160) : ¬ Sec4.IsoLThreePi X p e := by
  have hp : p.Prime := Fact.out
  have hq2 : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hodd : ∀ q, q = p ^ e → q ^ 3 ∣ 20160 → False := by
    intro q hq hdvd
    have h2 : q % 2 = 0 := KFacts.KS14.forall_of_forall_lt (N := 20160) (B := 28) (by norm_num)
      (by norm_num) (P := fun q => q % 2 = 0) (by decide) q (hq ▸ hq2) hdvd
    have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (hq ▸ Nat.dvd_of_mod_eq_zero h2)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  rintro (⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩)
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [← Nat.card_congr φ.toEquiv, hX, GaloisField.card p e (by omega)] at hc
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e - 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      have h1 : Nat.Coprime (p ^ e - 1) (p ^ e - 1 + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      rw [Nat.sub_add_cancel (by omega)] at h1
      exact h1.symm
    exact hodd _ rfl (hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl))
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr φ.toEquiv, hX] at hc
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e + 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    exact hodd _ rfl (hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl))

section Config

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem item142_odd
    (h : Sec14Std G A c L) {hAab : IsMulCommutative A}
    {hcA : c ∈ A} [(ker142 A (lB A) c).Normal] (h142 : Item142 A (lB A) c L hAab hcA)
    {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) :
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c} : Set G)) ∧
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∧
      ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
        img142 A (lB A) c Q ≤ Subgroup.centralizer ({alpha142 A (lB A) c a ha} : Set _) := by
  intro Q hQ
  have hD := h.toSec13Data
  obtain ⟨hQc, hcase⟩ := h142 Q hQ
  rcases hcase with ⟨⟨φ⟩, -, -, -⟩ | ⟨hK, htypes⟩
  · exfalso
    obtain ⟨hS, hZ⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := Sec13.facts_of_prod hD hS hZ φ
    exact not_isoLThreePi_of_card_eq_20160 hp2 he
      (by rw [Nat.card_congr ψ.toEquiv, Sec16.card_projSL_three_four]) hiso
  · refine ⟨hQc, hK, ?_⟩
    obtain ⟨ε⟩ := Item148PtRes2.nonempty_img142_equiv sporadicModels131 h hK
    rcases htypes with ⟨-, a, ha, ha1, hQα⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact ⟨a, ha, ha1, le_centralizer_of_eq_thetaC ha hQα⟩
    · exfalso
      refine KFacts.KS14.not_isoLThreePi_M22 p e ?_
      rcases hiso with ⟨hq, ⟨χ⟩⟩ | ⟨hq, ⟨χ⟩⟩
      · exact Or.inl ⟨hq, ⟨(φ.symm.trans ε).trans χ⟩⟩
      · exact Or.inr ⟨hq, ⟨(φ.symm.trans ε).trans χ⟩⟩
    · exfalso
      refine Item148PtRes2.not_isoLThreePi_J2 p e ?_
      rcases hiso with ⟨hq, ⟨χ⟩⟩ | ⟨hq, ⟨χ⟩⟩
      · exact Or.inl ⟨hq, ⟨(φ.symm.trans ε).trans χ⟩⟩
      · exact Or.inr ⟨hq, ⟨(φ.symm.trans ε).trans χ⟩⟩

end Config

end CFSG.RankThree.PartTwo.Sec16.Proof1611Res

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS Proof1611Res
open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

@[expose] def KS1611OddAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) →
        Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
          Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

theorem ks1611OddAut_of
    (h131a : Item131a) : KS1611OddAut := by
  intro G _ _ A c L h p e _ _ he hiso hprod
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  exact facts131_odd h131a h.toSec13Data hcL ⟨p, e, inferInstance, he, hiso⟩ hprod

theorem ks1611OddNotTrans_of_aut
    (hAut : KS1611OddAut) : KS1611OddNotTrans := by
  intro G _ _ A c L h p e _ hp2 he hiso hprod hAab hcA h142
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (ker142 A (lB A) c).Normal := ker142_normal hAab hcA
  have hD := h.toSec13Data
  have hS14 := h.toSec14Std
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hQ8 := hAut G A c L h p e hp2 he hiso hprod
  obtain ⟨φ⟩ := hprod
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Sec13.card_inf_eq_nine hD (Sec13.isPerfect_lBar hD) φ
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hcAL : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A := sup_le hcAL inf_le_left
    have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
      hD.commute (hcAL hx) hy.1
    have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
      rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three
        hD.orderOf_eq hcL]
      exact fun x hx => ⟨hx.2.2, hx.1⟩
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
    rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9] at hcard
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hD.card_eq])).symm
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩,
      fun x hx => hD.isElemAbelian.2 x hx.1⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set πθ := QuotientGroup.mk' θ with hπθ
  set Eb := ((A ⊓ L).subgroupOf L).map πθ with hEb
  have hE9 : Nat.card Eb = 9 := Res5Gen.card_image_inf hS14 h9
  have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := Subgroup.inf_subgroupOf_right A L
  have hEe : CFSG.Assembly.IsElemAbelian 3 Eb := by
    rw [hEb, hEq]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 πθ (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L hD.isElemAbelian)
  have hpt : ∀ z ∈ Eb, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, πθ ⟨y, hyL⟩ = z := by
    rintro z ⟨y', hy', rfl⟩ hz1
    refine ⟨y', Subgroup.mem_subgroupOf.mp hy', fun hy1 => hz1 ?_, y'.2, rfl⟩
    have : y' = 1 := Subtype.ext hy1
    rw [this, map_one]
  have htrans : ∀ y₀ ∈ Eb, y₀ ≠ 1 → ∀ y₁ ∈ Eb, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (Eb : Set (↥L ⧸ θ)), w * y₀ * w⁻¹ = y₁ := by
    intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
    obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := hpt z₀ hz₀ hz₀1
    obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := hpt z₁ hz₁ hz₁1
    obtain ⟨w, hwL, hwN, hw⟩ :=
      exists_conj_eq_of_autIn hc3 hcL hLc hAc hB h9 hQ8 hy₀ hy₁ hy₀1 hy₁1
    refine ⟨πθ ⟨w, hwL⟩, ?_, ?_⟩
    · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
          (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
      exact Subgroup.le_normalizer_map πθ ⟨_, hwN', rfl⟩
    · rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext hw
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    Res8Hess.exists_hessian_equiv he hiso hEe hE9 htrans
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  obtain ⟨⟨ta, hta, hta1⟩, ⟨tb, htb, htb1⟩⟩ :=
    exists_mem_pCoreOf_hessian hK hq hp2 hτ hτ1 hdM hcM
  have hmain := item142_odd hS14 h142 hp2 he hiso
  obtain ⟨Q₀, -, hQ₀⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)))
    (Item148PtRes2.sup_mem_invariantPiSubgroups hcA fun x hx y hy => hD.commute hx hy)
  have hKeq := (hmain Q₀ hQ₀).2.1
  have hLK : L ≤ k142 A (lB A) c := by
    rw [hKeq]
    exact le_sup_left.trans le_sup_left
  obtain ⟨ι, hι⟩ := exists_lbarEquiv sporadicModels131 hS14 hLK
  set Ψ := Φ.trans ι with hΨ
  have hdE : dM ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)
  have hcE : cM ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)
  have hΦd : Φ dM ∈ Eb := hΦE ▸ ⟨dM, hdE, rfl⟩
  have hΦc : Φ cM ∈ Eb := hΦE ▸ ⟨cM, hcE, rfl⟩
  obtain ⟨a', ha', ha'd⟩ := hΦd
  obtain ⟨b', hb', hb'c⟩ := hΦc
  have haAL : (a' : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp ha'
  have hbAL : (b' : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hb'
  set Γ := ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c with hΓ
  have hΨd : ((Ψ dM : ↥(img142 A (lB A) c L)) : Γ) = alpha142 A (lB A) c (a' : G) haAL.1 := by
    rw [hΨ, MulEquiv.trans_apply, ← ha'd, hι]
    rfl
  have hΨc : ((Ψ cM : ↥(img142 A (lB A) c L)) : Γ) = alpha142 A (lB A) c (b' : G) hbAL.1 := by
    rw [hΨ, MulEquiv.trans_apply, ← hb'c, hι]
    rfl
  set a : G := (a' : G) with ha_def
  set b : G := (b' : G) with hb_def
  have ha : a ∈ A := haAL.1
  have hb : b ∈ A := hbAL.1
  have himgA : img142 A (lB A) c A = img142 A (lB A) c (A ⊓ L) := by
    have hZ : Subgroup.zpowers c ≤ kA142 A (lB A) c :=
      (Subgroup.zpowers_le.mpr hcA).trans le_sup_right
    have hAL : A ⊓ L ≤ kA142 A (lB A) c := inf_le_left.trans le_sup_right
    have h1 : img142 A (lB A) c A = img142 A (lB A) c (Subgroup.zpowers c ⊔ (A ⊓ L)) :=
      congrArg (fun X => img142 A (lB A) c X) hAc
    rw [h1, img142, img142, Subgroup.subgroupOf_sup hZ hAL, Subgroup.map_sup]
    have hbot : ((Subgroup.zpowers c).subgroupOf (kA142 A (lB A) c)).map
        (QuotientGroup.mk' (ker142 A (lB A) c)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro x hx
      rw [ker142, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)
    rw [hbot, bot_sup_eq]
  have hAL : img142 A (lB A) c A ≤ img142 A (lB A) c L := himgA ▸ Res5Types.img_inf_le
  have hA9 : Nat.card (img142 A (lB A) c A) ≤ 9 := by
    rw [himgA]
    exact Nat.le_of_dvd (by norm_num) (h9 ▸ Sec15.Proof1513Res3.card_img142_dvd
      (inf_le_left.trans le_sup_right))
  have hAcomm : ∀ y ∈ img142 A (lB A) c A, ∀ z ∈ img142 A (lB A) c A, y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commute (Subgroup.mem_subgroupOf.mp hy) (Subgroup.mem_subgroupOf.mp hz))
  have hαA : ∀ (x : G) (hx : x ∈ A), alpha142 A (lB A) c x hx ∈ img142 A (lB A) c A :=
    fun x hx => Sec15.Proof1513Res3.mk_mem_img142 (g := ⟨x, Subgroup.mem_sup_right hx⟩) hx
  have hα3 : ∀ (x : G) (hx : x ∈ A), alpha142 A (lB A) c x hx ^ 3 = 1 := by
    intro x hx
    rw [alpha142, ← map_pow]
    have h1 : (⟨x, Subgroup.mem_sup_right hx⟩ : ↥(kA142 A (lB A) c)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hD.isElemAbelian.2 x hx)
    rw [h1, map_one]
  have ha1 : alpha142 A (lB A) c a ha ≠ 1 := by
    rw [← hΨd]
    intro h1
    have h2 : Ψ dM = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    rw [h2, orderOf_one] at hdo
    norm_num at hdo
  have hab : alpha142 A (lB A) c b hb ∉ Subgroup.zpowers (alpha142 A (lB A) c a ha) := by
    rw [← hΨd, ← hΨc]
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hcd
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Ψ.injective (Subtype.ext ?_)⟩
    rw [map_zpow, Subgroup.coe_zpow]
    exact hk
  have hT1 : ∀ x ∈ img142 A (lB A) c L,
      x * alpha142 A (lB A) c a ha = alpha142 A (lB A) c a ha * x →
      x * alpha142 A (lB A) c b hb = alpha142 A (lB A) c b hb * x →
      Nat.Coprime 3 (orderOf x) → x = 1 := by
    intro x hx hxa hxb hx3
    set y := Ψ.symm ⟨x, hx⟩ with hy
    have hΨy : Ψ y = ⟨x, hx⟩ := Ψ.apply_symm_apply _
    have hyd : y * dM = dM * y := by
      apply Ψ.injective
      rw [map_mul, map_mul, hΨy]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hΨd]
      exact hxa
    have hyc : y * cM = cM * y := by
      apply Ψ.injective
      rw [map_mul, map_mul, hΨy]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hΨc]
      exact hxb
    have hyd' : ProjGenLinGroup.mk (diagTau hτ) * (y : ProjGenLinGroup (Fin 3) K) =
        (y : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk (diagTau hτ) := by
      rw [← hdM]
      have h1 := congrArg Subtype.val hyd
      simp only [Subgroup.coe_mul] at h1
      exact h1.symm
    have hyc' : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * (y : ProjGenLinGroup (Fin 3) K) =
        (y : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) := by
      rw [← hcM]
      have h1 := congrArg Subtype.val hyc
      simp only [Subgroup.coe_mul] at h1
      exact h1.symm
    have hyo : Nat.Coprime 3 (orderOf (y : ProjGenLinGroup (Fin 3) K)) := by
      rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq Ψ, hΨy, Subgroup.orderOf_mk]
      exact hx3
    have h1 := eq_one_of_commute_hessian hK hq hτ hτ1 y.2 hyd' hyc' hyo
    have hy1 : y = 1 := Subtype.ext h1
    have h2 : (⟨x, hx⟩ : ↥(img142 A (lB A) c L)) = 1 := by rw [← hΨy, hy1, map_one]
    exact congrArg Subtype.val h2
  have hcent : ∀ (e : G) (he : e ∈ A) (e' : G) (he' : e' ∈ A), alpha142 A (lB A) c e he ≠ 1 →
      alpha142 A (lB A) c e' he' ∉ Subgroup.zpowers (alpha142 A (lB A) c e he) →
      ∀ x ∈ img142 A (lB A) c L,
        x ∈ Subgroup.centralizer ({alpha142 A (lB A) c e he} : Set _) →
        x ∈ Subgroup.centralizer ({alpha142 A (lB A) c e' he'} : Set _) →
        (∃ k : ℕ, x ^ 2 ^ k = 1) → x = 1 := by
    intro e he e' he' he1 hne x hx hxe hxe' hk
    obtain ⟨k, hk⟩ := hk
    have heo : orderOf (alpha142 A (lB A) c e he) = 3 := orderOf_eq_prime (hα3 e he) he1
    have he'1 : alpha142 A (lB A) c e' he' ≠ 1 := fun h1 => hne (h1 ▸ one_mem _)
    have he'o : orderOf (alpha142 A (lB A) c e' he') = 3 := orderOf_eq_prime (hα3 e' he') he'1
    have hjoin : Subgroup.zpowers (alpha142 A (lB A) c e he) ⊔
        Subgroup.zpowers (alpha142 A (lB A) c e' he') = img142 A (lB A) c A := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr (hαA e he))
        (Subgroup.zpowers_le.mpr (hαA e' he'))) ?_
      rw [Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ he'o hne (fun z hz =>
        hAcomm z (Subgroup.zpowers_le.mpr (hαA e he) hz) _ (hαA e' he')), Nat.card_zpowers, heo]
      exact hA9
    have hle : Subgroup.zpowers (alpha142 A (lB A) c e he) ⊔
        Subgroup.zpowers (alpha142 A (lB A) c e' he') ≤ Subgroup.centralizer ({x} : Set _) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff] at hxe ⊢
        exact hxe.symm
      · rw [Subgroup.mem_centralizer_singleton_iff] at hxe' ⊢
        exact hxe'.symm
    have hxA : ∀ z ∈ img142 A (lB A) c A, x * z = z * x := fun z hz => by
      rw [← hjoin] at hz
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hz)).symm
    refine hT1 x hx (hxA _ (hαA a ha)) (hxA _ (hαA b hb)) ?_
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
      (Nat.Coprime.pow_right k (by norm_num))
  have hΘ : ∀ (m t : ↥(projImage (slPi π 3 (p ^ e) K))) (x : G) (hx : x ∈ A),
      ((Ψ m : ↥(img142 A (lB A) c L)) : Γ) = alpha142 A (lB A) c x hx →
      t ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({m} : Set _)) → t ≠ 1 →
      IsPGroup 2 ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer
          ({Ψ m} : Set ↥(img142 A (lB A) c L)))).map (img142 A (lB A) c L).subtype) ∧
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer
          ({Ψ m} : Set ↥(img142 A (lB A) c L)))).map (img142 A (lB A) c L).subtype ≤
            img142 A (lB A) c L ∧
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer
          ({Ψ m} : Set ↥(img142 A (lB A) c L)))).map (img142 A (lB A) c L).subtype ≤
            Subgroup.centralizer ({alpha142 A (lB A) c x hx} : Set _) ∧
        img142 A (lB A) c A ≤ Subgroup.normalizer (((CFSG.Open.pCoreOf 2 (Subgroup.centralizer
          ({Ψ m} : Set ↥(img142 A (lB A) c L)))).map (img142 A (lB A) c L).subtype :
            Subgroup Γ) : Set Γ) ∧
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer
          ({Ψ m} : Set ↥(img142 A (lB A) c L)))).map (img142 A (lB A) c L).subtype ≠ ⊥ := by
    intro m t x hx hΨm ht ht1
    refine ⟨(CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map _, Subgroup.map_subtype_le _,
      ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hzC := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hz
      rw [Subgroup.mem_centralizer_singleton_iff] at hzC ⊢
      rw [← hΨm]
      exact congrArg Subtype.val hzC
    · intro w hw
      have hwL : w ∈ img142 A (lB A) c L := hAL hw
      have hwC : (⟨w, hwL⟩ : ↥(img142 A (lB A) c L)) ∈
          Subgroup.centralizer ({Ψ m} : Set ↥(img142 A (lB A) c L)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hΨm]
        exact hAcomm w hw _ (hαA x hx)
      have hwN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hwC
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨z, hz, rfl⟩ := hn
      exact ⟨⟨w, hwL⟩ * z * (⟨w, hwL⟩)⁻¹, (Subgroup.mem_normalizer_iff.mp hwN z).mp hz, rfl⟩
    · intro hbot
      have hmem : ((Ψ t : ↥(img142 A (lB A) c L)) : Γ) ∈
          (CFSG.Open.pCoreOf 2 (Subgroup.centralizer
            ({Ψ m} : Set ↥(img142 A (lB A) c L)))).map (img142 A (lB A) c L).subtype :=
        ⟨Ψ t, Sec17.Proof17Res7.map_pCoreOf_centralizer_le Ψ m ⟨t, ht, rfl⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      apply ht1
      apply Ψ.injective
      rw [map_one]
      exact Subtype.ext hmem
  exact not_transOn_of_points sporadicModels131 hS14 hLK
    (fun Q hQ => ⟨(hmain Q hQ).1, (hmain Q hQ).2.2⟩) hcent ha hb ha1 hab
    (hΘ dM ta a ha hΨd hta hta1) (hΘ cM tb b hb hΨc htb htb1)

theorem ks1611OddNotTrans_of_item131a
    (h131a : Item131a) :
    KS1611OddNotTrans :=
  ks1611OddNotTrans_of_aut (ks1611OddAut_of h131a)

theorem ks1611OddNotTrans_of
    (h131 : Item131) : KS1611OddNotTrans := by
  refine ks1611OddNotTrans_of_item131a fun G _ _ A c L hD => ?_
  rcases h131 G A c L hD with h | h | h | h | h | h | ⟨h7, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7)))))

theorem step1611List_of'
    (h131 : Item131) (hHJ : KS169HJNotTrans)
    (hA7 : KS1611A7NotTrans) (hM22 : KS1611M22NotTrans) (hM12 : KS1611M12NotTrans) :
    Step1611List :=
  step1611List_of h131 hHJ hA7 hM22 hM12 (ks1611OddNotTrans_of h131)

end CFSG.RankThree.PartTwo.Sec16

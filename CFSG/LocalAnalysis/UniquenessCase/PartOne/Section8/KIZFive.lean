module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZGeneric
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZLocal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ

open Subgroup
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

variable {X : Type} [Group X] [Finite X]

private theorem kizFive_commute_psl2 {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n) {K : Subgroup X}
    (e : ↥K ≃* CFSG.AGLEmbedding.PSL2GF p n) (P : Sylow p X)
    (hPK : (P : Subgroup X) ≤ K) :
    ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a := by
  classical
  let T : Sylow p ↥K := P.subtype hPK
  let U : Sylow p (CFSG.AGLEmbedding.PSL2GF p n) :=
    T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hU : (U : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)) =
      (T : Subgroup ↥K).map e.toMonoidHom := Sylow.coe_mapSurjective e.surjective T
  have hTcoe : (T : Subgroup ↥K) = (P : Subgroup X).subgroupOf K := Sylow.coe_subtype P hPK
  have hUea : CFSG.Open.IsElemAbelian p (U : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)) :=
    (CFSG.AGLEmbedding.psl2GF_sylow p n hn U).1
  have hUea' : IsMulCommutative (U : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)) ∧
      ∀ y ∈ (U : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)), y ^ p = 1 := hUea
  have hcomm : ∀ a b : (U : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)), a * b = b * a :=
    fun a b => hUea'.1.is_comm.comm a b
  intro a ha b hb
  have haT : (⟨a, hPK ha⟩ : ↥K) ∈ (T : Subgroup ↥K) := by
    rw [hTcoe, Subgroup.mem_subgroupOf]
    exact ha
  have hbT : (⟨b, hPK hb⟩ : ↥K) ∈ (T : Subgroup ↥K) := by
    rw [hTcoe, Subgroup.mem_subgroupOf]
    exact hb
  have haU : e ⟨a, hPK ha⟩ ∈ (U : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)) := by
    rw [hU]
    exact Subgroup.mem_map_of_mem e.toMonoidHom haT
  have hbU : e ⟨b, hPK hb⟩ ∈ (U : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)) := by
    rw [hU]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hbT
  have hab : (⟨a, hPK ha⟩ : ↥K) * ⟨b, hPK hb⟩ = ⟨b, hPK hb⟩ * ⟨a, hPK ha⟩ :=
    e.injective (by
      simpa only [map_mul, Subgroup.coe_mul] using congrArg Subtype.val
        (hcomm ⟨e ⟨a, hPK ha⟩, haU⟩ ⟨e ⟨b, hPK hb⟩, hbU⟩))
  simpa using congrArg Subtype.val hab

private theorem kizFive_card_dvd_sq {p : ℕ} [Fact p.Prime] {K : Subgroup X} (P : Sylow p X)
    (hPK : (P : Subgroup X) ≤ K) (h3 : ¬ p ^ 3 ∣ Nat.card ↥K) :
    Nat.card (P : Subgroup X) ∣ p ^ 2 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdvd : Nat.card (P : Subgroup X) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hPK
  have hk3 : k ≤ 2 := by
    by_contra h
    have hpk : p ^ 3 ∣ p ^ k := pow_dvd_pow p (by omega)
    rw [← hk] at hpk
    exact h3 (hpk.trans hdvd)
  rw [hk]
  exact pow_dvd_pow p hk3

private theorem kizFive_unitary {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hU : CFSG.AGLEmbedding.IsUnitaryIndex p d) {K : Subgroup X}
    (e : ↥K ≃* CFSG.AGLEmbedding.CatGroup d) (P : Sylow p X)
    (hPK : (P : Subgroup X) ≤ K) {x : X} (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  classical
  obtain ⟨ψ, hψ, hψr, htor⟩ :=
    CFSG.AGLEmbedding.kFactUnitarySylowCenterTorus ↥K p d hU ⟨e⟩ (P.subtype hPK)
  refine eq_one_of_torus (F := GaloisField p d.1.fieldExponent) (e := 1) P hPK ψ hψ
    hψr ?_ ?_ hxP hx
  · intro μ
    obtain ⟨c, hc, hcψ⟩ := htor μ
    exact ⟨c, hc, fun a => by simpa [pow_one] using hcψ a⟩
  · refine ⟨-1, ?_⟩
    have hchar : ringChar (GaloisField p d.1.fieldExponent) ≠ 2 := by
      rw [ringChar.eq (GaloisField p d.1.fieldExponent) p]
      exact hp2
    simpa using Ring.neg_one_ne_one_of_char_ne_two hchar

theorem eq_one_of_five_le_of_kFacts (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hMcL : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .McL) fun q => q = 5)
    (hJ4 : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .J4) fun q => q = 11)
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      CFSG.AGLEmbeddingD2.D2TransLocalAt (.lie d) fun q => q = 5)
    (hTits : ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal],
      centralizer (K : Set Y) = ⊥ → CFSG.AGLEmbedding.IsTitsGroup ↥K →
        ∀ R : Sylow 5 Y, CFSG.AGLEmbeddingD2.TorusLocal 5 (R : Subgroup Y))
    (hFi : ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → CFSG.AGLEmbedding.IsFi22 L →
      ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) ∧
        ¬ 5 ^ 3 ∣ Nat.card L)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore p X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) (P : Sylow p X) {x : X}
    (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  set K := CFSG.generalizedFitting X with hKdef
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hident :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.identification_of_isStronglyPEmbedded
      hId hLie hCyc hp hp5 hX hO h2 hN
  rcases hident with hsmall | hlie | hsz
  ·
    unfold CFSG.AGLEmbedding.IsSmallStrongP at hsmall
    rcases hsmall with hlin | huni | halt | hthree | hfive | hj4
    ·
      unfold CFSG.AGLEmbedding.IsSmallLinTwo at hlin
      obtain ⟨d, hd, ⟨e₀⟩⟩ := hlin
      obtain ⟨e₁⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (n := 2) hd
      let e : ↥K ≃* CFSG.AGLEmbedding.PSL2GF p 2 := e₀.trans e₁
      have hpe : ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ K := fun z hz hzp =>
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.pElements_psl2GF
          hp2 (by norm_num) hO hN e).2 z hz hzp
      have hPK : (P : Subgroup X) ≤ K := le_of_forall_pElement_mem hN hpe P
      exact eq_one_of_le_of_commute hKnab P hPK
        (kizFive_commute_psl2 (by norm_num) e P hPK) hxP hx
    ·
      unfold CFSG.AGLEmbedding.IsSmallUnitary at huni
      obtain ⟨d, ⟨q, hqp, -, hdq⟩, ⟨e⟩⟩ := huni
      have hU : CFSG.AGLEmbedding.IsUnitaryIndex p d := ⟨q, hqp, hdq⟩
      have hpe : ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ K := fun z hz hzp =>
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.pElements_unitary
          hU hO hN e).2 z hz hzp
      have hPK : (P : Subgroup X) ≤ K := le_of_forall_pElement_mem hN hpe P
      exact kizFive_unitary hp2 hU e P hPK hxP hx
    ·
      unfold CFSG.AGLEmbedding.IsAltTwoP at halt
      obtain ⟨e⟩ := halt
      have hout : ¬ p ∣ Nat.card
          (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (h.trans (outer_card_dvd_two_of_equiv_outside_six (Or.inr (by omega)) e)))
      have hPK : (P : Subgroup X) ≤ K := le_of_not_dvd_card_outer hKC hout P
      have hcard : Nat.card ↥K = Nat.card (alternatingGroup (Fin (2 * p))) :=
        Nat.card_congr e.toEquiv
      have h3 : ¬ p ^ 3 ∣ Nat.card ↥K := by
        rw [hcard]
        exact CFSG.AGLEmbeddingD2.AltSurvivor.not_pow_three_dvd_card_alternatingGroup hp hp2
      exact eq_one_of_le_of_commute hKnab P hPK
        (commute_of_card_dvd_sq P.isPGroup' (kizFive_card_dvd_sq P hPK h3)) hxP hx
    ·
      obtain ⟨h3, -⟩ := hthree
      omega
    ·
      obtain ⟨h5, hT | hMc | hFi22⟩ := hfive
      ·
        subst p
        have hT' : CFSG.AGLEmbeddingD2.TorusLocal 5 (P : Subgroup X) := hTits X K hKC hT P
        exact eq_one_of_torusLocal (by norm_num) (by norm_num) P.isPGroup' hT' hxP hx
      ·
        subst p
        obtain ⟨e⟩ := hMc
        exact eq_one_of_d2HeisLocalAt hMcL hKn hKC ⟨e⟩ hp hp5 rfl P hxP hx
      ·
        subst p
        obtain ⟨hout, h3⟩ := hFi ↥K hKs hFi22
        have hPK : (P : Subgroup X) ≤ K := le_of_not_dvd_card_outer hKC hout P
        exact eq_one_of_le_of_commute hKnab P hPK
          (commute_of_card_dvd_sq P.isPGroup' (kizFive_card_dvd_sq P hPK h3)) hxP hx
    ·
      obtain ⟨h11, hJ⟩ := hj4
      subst p
      obtain ⟨e⟩ := hJ
      exact eq_one_of_d2HeisLocalAt hJ4 hKn hKC ⟨e⟩ hp hp5 rfl P hxP hx
  ·
    obtain ⟨d, hcases, ⟨e⟩⟩ := hlie
    rcases hcases with ⟨n, hn3, hd⟩ | ⟨hU, -⟩ | hree
    ·
      obtain ⟨e₁⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
      let e' : ↥K ≃* CFSG.AGLEmbedding.PSL2GF p n := e.trans e₁
      have hpe : ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ K := fun z hz hzp =>
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.pElements_psl2GF
          hp2 (by omega) hO hN e').2 z hz hzp
      have hPK : (P : Subgroup X) ≤ K := le_of_forall_pElement_mem hN hpe P
      exact eq_one_of_le_of_commute hKnab P hPK
        (kizFive_commute_psl2 (by omega) e' P hPK) hxP hx
    ·
      have hpe : ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ K := fun z hz hzp =>
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.pElements_unitary
          hU hO hN e).2 z hz hzp
      have hPK : (P : Subgroup X) ≤ K := le_of_forall_pElement_mem hN hpe P
      exact kizFive_unitary hp2 hU e P hPK hxP hx
    ·
      obtain ⟨h3, -⟩ := hree
      omega
  ·
    obtain ⟨h5, hiso⟩ := hsz
    obtain ⟨hv, ⟨e⟩⟩ := hiso
    subst p
    let d : TauCeti.ValidLieTypeIndex := ⟨.suzuki 2, hv⟩
    have hd : d.1 = .suzuki 2 := rfl
    exact eq_one_of_d2TransLocalAt (hSz d hd) hKn hKC ⟨e⟩ hp hp2 rfl h2 P hxP hx

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ

module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.ActionTriviality
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.CyclicSylow
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Faithful
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.BaerCore

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

universe v


public lemma CFSG.pPrimeCore_map_le_centralizer_pCore_map {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (H : Subgroup G) :
    let P : Subgroup G := (pCore p (↥H)).map H.subtype
    (pPrimeCore p (↥H)).map H.subtype ≤ Subgroup.centralizer (P : Set G) := by
  intro P
  have hBp : IsPGroup p (pCore p (↥H)) := pCore_isPGroup (G := ↥H) (p := p)
  obtain ⟨n, hcardB⟩ := hBp.exists_card_eq
  have hp_not_dvd_A : ¬ p ∣ Nat.card (pPrimeCore p (↥H)) := by
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (G := ↥H) (p := p))
  have hAcopB : Nat.Coprime (Nat.card (pPrimeCore p (↥H))) (Nat.card (pCore p (↥H))) := by
    rw [hcardB]
    exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd (m := n) hp_not_dvd_A
  have hdisj : Disjoint (pPrimeCore p (↥H)) (pCore p (↥H)) := by
    exact Subgroup.disjoint_of_coprime_natCard hAcopB
  have hcomm_bot : ⁅pPrimeCore p (↥H), pCore p (↥H)⁆ = ⊥ := by
    apply bot_unique
    calc
      ⁅pPrimeCore p (↥H), pCore p (↥H)⁆ ≤ (pPrimeCore p (↥H)) ⊓ pCore p (↥H) := by
        exact Subgroup.commutator_le_inf (H₁ := pPrimeCore p (↥H)) (H₂ := pCore p (↥H))
      _ = ⊥ := hdisj.eq_bot
  have hcentralH :
      pPrimeCore p (↥H) ≤ Subgroup.centralizer (pCore p (↥H) : Set ↥H) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := pPrimeCore p (↥H)) (H₂ := pCore p (↥H))).1 hcomm_bot
  intro x hx
  rcases hx with ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hy with ⟨y, hy, rfl⟩
  exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp (hcentralH hx)) y hy)

lemma CFSG.pPrimeCore_map_subtype_subgroupOf {G : Type*} [Group G] {p : ℕ}
    (H : Subgroup G) :
    (((pPrimeCore p (↥H)).map H.subtype).subgroupOf H) = pPrimeCore p (↥H) := by
  change ((pPrimeCore p (↥H)).map H.subtype).comap H.subtype = pPrimeCore p (↥H)
  exact
    Subgroup.comap_map_eq_self_of_injective
      (H := pPrimeCore p (↥H)) (f := H.subtype) H.subtype_injective

lemma CFSG.inf_pCore_le_pCore_subgroup_map {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (H : Subgroup G) :
    pCore p G ⊓ H ≤ (pCore p (↥H)).map H.subtype := by
  let K : Subgroup H := (pCore p G).subgroupOf H
  have : K.Normal := by
    simpa [K] using
      (Subgroup.Normal.subgroupOf (H := pCore p G) (K := H) (inferInstance : (pCore p G).Normal))
  have hKp_inf : IsPGroup p (↥(pCore p G ⊓ H)) :=
    (pCore_isPGroup (G := G) (p := p)).to_inf_left
  have hKp : IsPGroup p (↥K) := by
    let e :
        ↥((pCore p G ⊓ H).subgroupOf H) ≃* ↥(pCore p G ⊓ H) :=
      Subgroup.subgroupOfEquivOfLe (G := G) (H := pCore p G ⊓ H) (K := H) inf_le_right
    have hKp' : IsPGroup p (↥((pCore p G ⊓ H).subgroupOf H)) := hKp_inf.of_equiv e.symm
    have hEq : K = ((pCore p G ⊓ H).subgroupOf H) := by
      ext x
      simp [K, Subgroup.mem_subgroupOf]
    exact hEq.symm ▸ hKp'
  have hK_le : K ≤ pCore p (↥H) := le_sSup ⟨inferInstance, hKp⟩
  simpa [K, Subgroup.subgroupOf_map_subtype] using (Subgroup.map_mono (f := H.subtype) hK_le)

lemma CFSG.pPrimeCore_map_le_centralizer_inf_pCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (H : Subgroup G) :
    (pPrimeCore p (↥H)).map H.subtype ≤
      Subgroup.centralizer ((pCore p G ⊓ H : Subgroup G) : Set G) := by
  let P : Subgroup G := (pCore p (↥H)).map H.subtype
  have hcentP :
      (pPrimeCore p (↥H)).map H.subtype ≤ Subgroup.centralizer (P : Set G) :=
    pPrimeCore_map_le_centralizer_pCore_map (p := p) H
  have hinf : pCore p G ⊓ H ≤ P := inf_pCore_le_pCore_subgroup_map (p := p) H
  exact hcentP.trans
    (Subgroup.centralizer_le (show ((pCore p G ⊓ H : Subgroup G) : Set G) ⊆ (P : Set G) from hinf))

lemma CFSG.exists_maximal_pSubgroup_centralizedBy {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (R₀ Q : Subgroup G) (hR₀p : IsPGroup p (↥R₀))
    (hQcent : Q ≤ Subgroup.centralizer (R₀ : Set G)) :
    ∃ R : Subgroup G,
      R₀ ≤ R ∧
        IsPGroup p (↥R) ∧
        Q ≤ Subgroup.centralizer (R : Set G) ∧
        ∀ S : Subgroup G,
          R₀ ≤ S →
            IsPGroup p (↥S) →
              Q ≤ Subgroup.centralizer (S : Set G) →
                R ≤ S → S = R := by
  classical
  let s : Set (Subgroup G) :=
    {R | R₀ ≤ R ∧ IsPGroup p (↥R) ∧ Q ≤ Subgroup.centralizer (R : Set G)}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨R₀, le_rfl, hR₀p, hQcent⟩
  obtain ⟨R, hR, hRmax⟩ := hsfin.exists_maximal hsne
  refine ⟨R, hR.1, hR.2.1, hR.2.2, ?_⟩
  intro S hR₀S hSp hQcentS hRS
  exact le_antisymm (hRmax ⟨hR₀S, hSp, hQcentS⟩ hRS) hRS

private lemma CFSG.normalizer_le_normalizer_centralizer {G : Type*} [Group G] (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have hrn : n⁻¹ * r * n ∈ R := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hn) _).1 hr
    have hcomm : (n⁻¹ * r * n) * c = c * (n⁻¹ * r * n) := hc _ hrn
    have hcomm' := congrArg (fun x : G => n * x * n⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have hrn : n * r * n⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hn _).1 hr
    have hcomm :
        (n * r * n⁻¹) * (n * c * n⁻¹) = (n * c * n⁻¹) * (n * r * n⁻¹) :=
      hc _ hrn
    have hcomm' := congrArg (fun x : G => n⁻¹ * x * n) hcomm
    simpa [mul_assoc] using hcomm'

private lemma CFSG.subgroupOf_le_pPrimeCore_map {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K H : Subgroup G} (hKH : K ≤ H) [hKN : (K.subgroupOf H).Normal]
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p (↥H)).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    natCard_subgroupOf_eq K H hKH
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact hcop
  have hsub : K.subgroupOf H ≤ pPrimeCore p (↥H) := le_sSup ⟨hKN, hcop'⟩
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKH] using
    (Subgroup.map_mono (f := H.subtype) hsub)

theorem CFSG.sup_eq_top_of_fixed_quotient
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [H.Normal]
    [MulDistribMulAction A (G ⧸ H)]
    (hquotFix : ∀ g : G, ((g : G) : G ⧸ H) ∈ fixedPointSubgroup A (G ⧸ H))
    (hfixed : fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H)) :
    fixedPointSubgroup A G ⊔ H = ⊤ := by
  apply top_unique
  intro g _
  have hqfix := hquotFix g
  rw [hfixed] at hqfix
  rcases hqfix with ⟨c, hcfix, hcg⟩
  rcases (QuotientGroup.mk'_eq_mk' (N := H)).1 hcg with ⟨z, hz, hcz⟩
  rw [← hcz]
  exact Subgroup.mul_mem_sup hcfix hz

theorem CFSG.pPrimeCore_centralizer_pSubgroup_eq_bot_of_pPrimeCore_eq_bot
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G) {p : ℕ} [Fact p.Prime]
    (hcore : pPrimeCore p G = ⊥) :
    ∀ R : Subgroup G,
      IsPGroup p (↥R) →
        let C : Subgroup G := Subgroup.centralizer (R : Set G)
        (pPrimeCore p (↥C)).map C.subtype = ⊥ := by
  intro R₀ hR₀p
  let C₀ : Subgroup G := Subgroup.centralizer (R₀ : Set G)
  let Q : Subgroup G := (pPrimeCore p (↥C₀)).map C₀.subtype
  by_cases hQbot : Q = ⊥
  · simpa [C₀, Q] using hQbot
  · let P : Subgroup G := pCore p G
    have hfit_eq : fittingSubgroup G = P := Fitting_eq_pcore G p hcore
    have hcentP : Subgroup.centralizer (P : Set G) ≤ P := by
      simpa [P, hfit_eq] using
        (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := G) hsolv)
    have hQleC₀ : Q ≤ C₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact x.2
    have hQcentR₀ : Q ≤ Subgroup.centralizer (R₀ : Set G) := by
      simpa [C₀] using hQleC₀
    obtain ⟨R, hR₀R, hRp, hQcentR, hRmax⟩ :=
      exists_maximal_pSubgroup_centralizedBy (p := p) R₀ Q hR₀p hQcentR₀
    let C : Subgroup G := Subgroup.centralizer (R : Set G)
    have hQleC : Q ≤ C := hQcentR
    have hC_le_C₀ : C ≤ C₀ := by
      exact Subgroup.centralizer_le (show (R₀ : Set G) ⊆ (R : Set G) from hR₀R)
    have : (Q.subgroupOf C₀).Normal := by
      simpa [Q, C₀, pPrimeCore_map_subtype_subgroupOf (p := p) C₀] using
        (inferInstance : (pPrimeCore p (↥C₀)).Normal)
    have hC₀_le_normQ : C₀ ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf (H := Q) (K := C₀) hQleC₀
    have : (Q.subgroupOf C).Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (hC_le_C₀.trans hC₀_le_normQ)
    have hQcop : Nat.Coprime p (Nat.card Q) := by
      have hcard :
          Nat.card Q = Nat.card (pPrimeCore p (↥C₀)) := by
        simpa [Q] using
          (Subgroup.card_map_of_injective (K := pPrimeCore p (↥C₀))
            (f := C₀.subtype) C₀.subtype_injective)
      rw [hcard]
      exact pPrimeCore_coprime_card (G := ↥C₀) (p := p)
    have hQcoreC : Q ≤ (pPrimeCore p (↥C)).map C.subtype :=
      subgroupOf_le_pPrimeCore_map (p := p) hQleC hQcop
    let K : Subgroup G := P ⊓ C
    have hQcentK : Q ≤ Subgroup.centralizer (K : Set G) := by
      simpa [K, P, C] using
        (hQcoreC.trans (pPrimeCore_map_le_centralizer_inf_pCore (p := p) C))
    have hKp : IsPGroup p (↥K) := (pCore_isPGroup (G := G) (p := p)).to_inf_left
    have hR_le_normK : R ≤ Subgroup.normalizer (K : Set G) := by
      have hR_le_normP : R ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      have hR_le_normC : R ≤ Subgroup.normalizer (C : Set G) :=
        R.le_normalizer.trans (normalizer_le_normalizer_centralizer R)
      exact (le_inf hR_le_normP hR_le_normC).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hsup_p : IsPGroup p (↥(R ⊔ K)) :=
      IsPGroup.to_sup_of_normal_right' hRp hKp hR_le_normK
    have hQcent_sup : Q ≤ Subgroup.centralizer ((R ⊔ K : Subgroup G) : Set G) := by
      rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hx with hx | hx
      · exact (Subgroup.mem_centralizer_iff.mp (hQcentR hq)) x hx
      · exact (Subgroup.mem_centralizer_iff.mp (hQcentK hq)) x hx
    have hsup_eq : R ⊔ K = R :=
      hRmax (R ⊔ K) (hR₀R.trans le_sup_left) hsup_p hQcent_sup le_sup_left
    have hK_le_R : K ≤ R := by
      simpa [hsup_eq] using (le_sup_right : K ≤ R ⊔ K)
    have hPinC : P ⊓ C ≤ R := by
      simpa [K] using hK_le_R
    let N : Subgroup G := P ⊓ Subgroup.normalizer (R : Set G)
    have hNp : IsPGroup p (↥N) := by
      simpa [N, P] using (pCore_isPGroup (G := G) (p := p)).to_inf_left
    have hNleP : N ≤ P := inf_le_left
    have hNleNormR : N ≤ Subgroup.normalizer (R : Set G) := inf_le_right
    have hNleNormC : N ≤ Subgroup.normalizer (C : Set G) := by
      exact hNleNormR.trans (normalizer_le_normalizer_centralizer R)
    have hQleNormR : Q ≤ Subgroup.normalizer (R : Set G) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        have hqr : r * (q : G) = (q : G) * r := (Subgroup.mem_centralizer_iff.mp (hQcentR hq)) r hr
        have hconj : (q : G) * r * (q : G)⁻¹ = r := by
          calc
            (q : G) * r * (q : G)⁻¹ = (r * (q : G)) * (q : G)⁻¹ := by rw [hqr]
            _ = r := by simp [mul_assoc]
        simpa [hconj] using hr
      · intro hr
        have hqInvC : (q : G)⁻¹ ∈ C := C.inv_mem (hQleC hq)
        have hqInvr :
            (q : G)⁻¹ * ((q : G) * r * (q : G)⁻¹) = ((q : G) * r * (q : G)⁻¹) * (q : G)⁻¹ :=
          ((Subgroup.mem_centralizer_iff.mp hqInvC) _ hr).symm
        have hconj : r = (q : G) * r * (q : G)⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => t * (q : G)) hqInvr
        exact hconj.symm ▸ hr
    have hQleNormN : Q ≤ Subgroup.normalizer (N : Set G) := by
      have hQleNormP : Q ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      have hQleNormNormR :
          Q ≤ Subgroup.normalizer (Subgroup.normalizer (R : Set G) : Set G) :=
        hQleNormR.trans Subgroup.le_normalizer
      simpa [N] using
        (le_inf hQleNormP hQleNormNormR).trans Subgroup.inf_normalizer_le_normalizer_inf
    have : Subgroup.Normalizes Q N := ⟨hQleNormN⟩
    let KN : Subgroup G := N ⊓ C
    have hKN_le_R : KN ≤ R := by
      exact (inf_le_inf hNleP le_rfl).trans hPinC
    have hNleNormKN : N ≤ Subgroup.normalizer (KN : Set G) := by
      have hNleNormN' : N ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer
      simpa [KN] using
        (le_inf hNleNormN' hNleNormC).trans Subgroup.inf_normalizer_le_normalizer_inf
    have : (KN.subgroupOf N).Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (H := N) (N := KN) hNleNormKN
    have hQleNormKN : Q ≤ Subgroup.normalizer (KN : Set G) := by
      have hQleNormC : Q ≤ Subgroup.normalizer (C : Set G) := hQleC.trans Subgroup.le_normalizer
      simpa [KN] using
        (le_inf hQleNormN hQleNormC).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hKNinv : IsInvariant (↥Q) (↥N) (KN.subgroupOf N) := by
      refine ⟨?_⟩
      intro a x
      constructor
      · intro hx
        apply Subgroup.mem_subgroupOf.mpr
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        exact
          (Subgroup.mem_normalizer_iff.mp (hQleNormKN a.2) (x : G)).1
            (Subgroup.mem_subgroupOf.mp hx)
      · intro hx
        have haInv : ((a : G)⁻¹) ∈ Subgroup.normalizer (KN : Set G) := by
          exact (Subgroup.normalizer (KN : Set G)).inv_mem (hQleNormKN a.2)
        have hx' :
            (a : G)⁻¹ * (((a : G) * (x : G) * (a : G)⁻¹)) * (((a : G)⁻¹)⁻¹) ∈ KN :=
          (Subgroup.mem_normalizer_iff.mp haInv _).1 (by
            rw [← Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
            exact Subgroup.mem_subgroupOf.mp hx)
        apply Subgroup.mem_subgroupOf.mpr
        simpa [mul_assoc] using hx'
    let : IsInvariant (↥Q) (↥N) (KN.subgroupOf N) := hKNinv
    let : MulAction.QuotientAction (↥Q) (KN.subgroupOf N) :=
      quotientAction_of_isInvariant (A := ↥Q) (G := ↥N) (KN.subgroupOf N) hKNinv
    let : MulDistribMulAction (↥Q) (↥N ⧸ KN.subgroupOf N) :=
      quotientMulDistribMulAction (A := ↥Q) (G := ↥N) (KN.subgroupOf N) hKNinv
    have hquotFix :
        ∀ n : N, ((n : N) : ↥N ⧸ KN.subgroupOf N) ∈ fixedPointSubgroup (↥Q) (↥N ⧸ KN.subgroupOf N) := by
      intro n
      rw [FixedPoints.mem_subgroup]
      intro a
      change (((a : ↥Q) • n : N) : ↥N ⧸ KN.subgroupOf N) = ((n : N) : ↥N ⧸ KN.subgroupOf N)
      rw [QuotientGroup.eq_iff_div_mem]
      have hmemN : (((a : G) * (n : G) * (a : G)⁻¹) * (n : G)⁻¹) ∈ N := by
        exact N.mul_mem ((a : ↥Q) • n).2 (N.inv_mem n.2)
      have hmemC : (((a : G) * (n : G) * (a : G)⁻¹) * (n : G)⁻¹) ∈ C := by
        have haC : (a : G) ∈ C := hQleC a.2
        have hnNormC : (n : G) ∈ Subgroup.normalizer (C : Set G) := hNleNormC n.2
        have hconjAinv : (n : G) * (a : G)⁻¹ * (n : G)⁻¹ ∈ C :=
          (Subgroup.mem_normalizer_iff.mp hnNormC _).1 (C.inv_mem haC)
        have : (a : G) * ((n : G) * (a : G)⁻¹ * (n : G)⁻¹) ∈ C := C.mul_mem haC hconjAinv
        simpa [mul_assoc] using this
      change ((((a : ↥Q) • n : N) / n : N) : G) ∈ KN
      simpa [div_eq_mul_inv, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        (show (((a : G) * (n : G) * (a : G)⁻¹) * (n : G)⁻¹) ∈ KN from ⟨hmemN, hmemC⟩)
    have hNsolv : Group.IsSolvable ↥N := by infer_instance
    obtain ⟨nN, hcardN⟩ := hNp.exists_card_eq
    have hpNotDvdQ : ¬ p ∣ Nat.card Q :=
      (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hQcop
    have hQcopN : Nat.Coprime (Nat.card Q) (Nat.card N) := by
      rw [hcardN]
      exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd (m := nN) hpNotDvdQ
    have hfixedN :
        fixedPointSubgroup (↥Q) (↥N ⧸ KN.subgroupOf N) =
          (fixedPointSubgroup (↥Q) ↥N).map (QuotientGroup.mk' (KN.subgroupOf N)) := by
      simpa using
        fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
          (G := ↥N) (A := ↥Q) hNsolv hQcopN (π := ∅) (KN.subgroupOf N) hKNinv
    have hsupN :
        fixedPointSubgroup (↥Q) ↥N ⊔ KN.subgroupOf N = ⊤ := by
      refine sup_eq_top_of_fixed_quotient (A := ↥Q) (H := KN.subgroupOf N) ?_ hfixedN
      intro n
      exact hquotFix ⟨n, n.2⟩
    have hFixN_le_R :
        (fixedPointSubgroup (↥Q) ↥N).map N.subtype ≤ R := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      let X : Subgroup G := Subgroup.zpowers (x : G)
      have hxN : ((x : ↥N) : G) ∈ N := (x : ↥N).2
      have hXleNormR : X ≤ Subgroup.normalizer (R : Set G) := by
        exact Subgroup.zpowers_le.2 (hNleNormR hxN)
      have hXleN : X ≤ N := by
        exact Subgroup.zpowers_le.2 hxN
      have hXpSub : IsPGroup p (X.subgroupOf N) := hNp.to_subgroup (X.subgroupOf N)
      have hXp : IsPGroup p (↥X) := by
        exact hXpSub.of_equiv (Subgroup.subgroupOfEquivOfLe (G := G) (H := X) (K := N) hXleN)
      have hQcentX : Q ≤ Subgroup.centralizer (X : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hxfix : ∀ b : ↥Q, b • x = x := by
          simpa [FixedPoints.mem_subgroup] using hx
        have hconj :
            (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
          simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg Subtype.val (hxfix ⟨a, ha⟩)
        have hcomm : Commute (a : G) (x : G) := by
          rw [commute_iff_eq]
          calc
            (a : G) * (x : G) = ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) := by
              simp [mul_assoc]
            _ = (x : G) * (a : G) := by rw [hconj]
        simpa [Commute] using (hcomm.zpow_right k).eq.symm
      have hQcentRX : Q ≤ Subgroup.centralizer ((R ⊔ X : Subgroup G) : Set G) := by
        rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rcases hz with hz | hz
        · exact (Subgroup.mem_centralizer_iff.mp (hQcentR hq)) z hz
        · exact (Subgroup.mem_centralizer_iff.mp (hQcentX hq)) z hz
      have hRXp : IsPGroup p (↥(R ⊔ X : Subgroup G)) :=
        IsPGroup.to_sup_of_normal_left' hRp hXp hXleNormR
      have hRXeq : R ⊔ X = R :=
        hRmax (R ⊔ X) (hR₀R.trans le_sup_left) hRXp hQcentRX le_sup_left
      have hXleR : X ≤ R := by
        simpa [hRXeq] using (le_sup_right : X ≤ R ⊔ X)
      exact hXleR (Subgroup.mem_zpowers _)
    have hN_eq :
        (fixedPointSubgroup (↥Q) ↥N).map N.subtype ⊔ KN = N := by
      calc
        (fixedPointSubgroup (↥Q) ↥N).map N.subtype ⊔ KN
            =
              (fixedPointSubgroup (↥Q) ↥N).map N.subtype ⊔
                (KN.subgroupOf N).map N.subtype := by
                  simp [Subgroup.subgroupOf_map_subtype, KN, inf_comm]
        _ = (fixedPointSubgroup (↥Q) ↥N ⊔ KN.subgroupOf N).map N.subtype := by
              rw [Subgroup.map_sup]
        _ = (⊤ : Subgroup N).map N.subtype := by rw [hsupN]
        _ = N := by
              rw [← MonoidHom.range_eq_map]
              exact Subgroup.range_subtype N
    have hNleR : N ≤ R := by
      rw [← hN_eq]
      exact sup_le hFixN_le_R hKN_le_R
    let S : Subgroup G := R ⊔ P
    have hSp : IsPGroup p (↥S) := by
      simpa [S] using IsPGroup.to_sup_of_normal_right hRp (pCore_isPGroup (G := G) (p := p))
    have hconjS : ∀ q : G, q ∈ Q → ∀ s : G, s ∈ S → q * s * q⁻¹ ∈ S := by
      intro q hq s hs
      rcases (Subgroup.mem_sup_of_normal_right (s := R) (t := P) (x := s)).1 hs with
        ⟨r, hr, p', hp', hEq⟩
      have hqR : q * r * q⁻¹ = r := by
        have hqr : r * q = q * r := (Subgroup.mem_centralizer_iff.mp (hQcentR hq)) r hr
        calc
          q * r * q⁻¹ = (r * q) * q⁻¹ := by rw [hqr]
          _ = r := by simp [mul_assoc]
      have hqP : q * p' * q⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer_of_normal (H := P) hq) _).1 hp'
      have hEqS : q * s * q⁻¹ = r * (q * p' * q⁻¹) := by
        calc
          q * s * q⁻¹ = q * (r * p') * q⁻¹ := by rw [hEq]
          _ = (q * r * q⁻¹) * (q * p' * q⁻¹) := by simp [mul_assoc]
          _ = r * (q * p' * q⁻¹) := by rw [hqR]
      rw [hEqS]
      exact Subgroup.mul_mem_sup hr hqP
    have hQleNormS : Q ≤ Subgroup.normalizer (S : Set G) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · exact hconjS q hq s
      · intro hs
        simpa [mul_assoc] using hconjS q⁻¹ (Q.inv_mem hq) (q * s * q⁻¹) hs
    have : Subgroup.Normalizes Q S := ⟨hQleNormS⟩
    have hcentRS :
        Subgroup.centralizer ((R.subgroupOf S : Subgroup S) : Set S) ≤ R.subgroupOf S := by
      intro x hx
      change (x : G) ∈ R
      have hxC : (x : G) ∈ C := by
        rw [Subgroup.mem_centralizer_iff] at hx
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        exact congrArg Subtype.val <|
          hx ⟨r, Subgroup.mem_sup_left hr⟩ (by simpa [Subgroup.mem_subgroupOf] using hr)
      rcases (Subgroup.mem_sup_of_normal_right (s := R) (t := P) (x := (x : G))).1 x.2 with
        ⟨r, hr, p', hp', hEq⟩
      have hxNorm : (x : G) ∈ Subgroup.normalizer (R : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro r
        constructor
        · intro hr
          have hxr : r * (x : G) = (x : G) * r := (Subgroup.mem_centralizer_iff.mp hxC) r hr
          have hconj : (x : G) * r * (x : G)⁻¹ = r := by
            calc
              (x : G) * r * (x : G)⁻¹ = (r * (x : G)) * (x : G)⁻¹ := by rw [← hxr]
              _ = r := by simp [mul_assoc]
          simpa [hconj] using hr
        · intro hr
          have hxInvC : (x : G)⁻¹ ∈ C := C.inv_mem hxC
          have hxInvr :
              (x : G)⁻¹ * ((x : G) * r * (x : G)⁻¹) =
                ((x : G) * r * (x : G)⁻¹) * (x : G)⁻¹ :=
            ((Subgroup.mem_centralizer_iff.mp hxInvC) _ hr).symm
          have hconj : r = (x : G) * r * (x : G)⁻¹ := by
            simpa [mul_assoc] using congrArg (fun t : G => t * (x : G)) hxInvr
          exact hconj.symm ▸ hr
      have hrNorm : r ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer hr
      have hpNorm : p' ∈ Subgroup.normalizer (R : Set G) := by
        have : r⁻¹ * (x : G) ∈ Subgroup.normalizer (R : Set G) :=
          (Subgroup.normalizer (R : Set G)).mul_mem
            ((Subgroup.normalizer (R : Set G)).inv_mem hrNorm) hxNorm
        have hpEq : p' = r⁻¹ * (x : G) := by
          rw [← hEq]
          simp
        exact hpEq ▸ this
      have hpN : p' ∈ N := ⟨hp', hpNorm⟩
      have hpR : p' ∈ R := hNleR hpN
      rw [← hEq]
      exact R.mul_mem hr hpR
    let FS : Subgroup G := (fixedPointSubgroup (↥Q) ↥S).map S.subtype
    have hRleFS : R ≤ FS := by
      intro r hr
      refine ⟨⟨r, Subgroup.mem_sup_left hr⟩, ?_, rfl⟩
      change ∀ a : ↥Q, a • (⟨r, Subgroup.mem_sup_left hr⟩ : ↥S) = ⟨r, Subgroup.mem_sup_left hr⟩
      intro a
      apply Subtype.ext
      have hComm := Subgroup.mem_centralizer_iff.mp (hQcentR a.2) r hr
      have hconj : (a : G) * r * (a : G)⁻¹ = r := by
        simpa [mul_assoc] using congrArg (fun t : G => t * (a : G)⁻¹) hComm.symm
      exact hconj
    have hFSpSub : IsPGroup p (fixedPointSubgroup (↥Q) ↥S) :=
      hSp.to_subgroup (fixedPointSubgroup (↥Q) ↥S)
    have hFSp : IsPGroup p (↥FS) := hFSpSub.map S.subtype
    have hQcentFS : Q ≤ Subgroup.centralizer (FS : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hxfix : ∀ b : ↥Q, b • x = x := by
        simpa [FixedPoints.mem_subgroup] using hx
      have hconj :
          (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val (hxfix ⟨a, ha⟩)
      have hComm : (x : G) * (a : G) = (a : G) * (x : G) := by
        simpa [mul_assoc] using (congrArg (fun t : G => t * (a : G)) hconj).symm
      exact hComm
    have hFS_eq : FS = R :=
      hRmax FS (hR₀R.trans hRleFS) hFSp hQcentFS hRleFS
    have hFixS_eq : fixedPointSubgroup (↥Q) ↥S = R.subgroupOf S := by
      ext x
      constructor
      · intro hx
        have hxFS : (x : G) ∈ FS := ⟨x, hx, rfl⟩
        apply Subgroup.mem_subgroupOf.mpr
        rw [← hFS_eq]
        exact hxFS
      · intro hx
        have hxFS : (x : G) ∈ FS := by
          rw [hFS_eq]
          exact Subgroup.mem_subgroupOf.mp hx
        rcases hxFS with ⟨y, hy, hyx⟩
        have hyEq : y = x := by
          apply Subtype.ext
          exact hyx
        simpa [hyEq] using hy
    obtain ⟨nS, hcardS⟩ := hSp.exists_card_eq
    have hQcopS : Nat.Coprime (Nat.card Q) (Nat.card S) := by
      rw [hcardS]
      exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd (m := nS) hpNotDvdQ
    have hnilS : Group.IsNilpotent ↥S := hSp.isNilpotent
    have htrivS : ActsTrivially (A := ↥Q) (G := ↥S) :=
      actsTrivially_of_nilpotent_coprime_and_centralizer_fixedPointSubgroup
        (G := ↥S) (A := ↥Q) hnilS hQcopS (by simpa [hFixS_eq] using hcentRS)
    have hQcentP : Q ≤ Subgroup.centralizer (P : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hfix := htrivS ⟨q, hq⟩ ⟨y, Subgroup.mem_sup_right hy⟩
      have hconj : (q : G) * y * (q : G)⁻¹ = y := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using congrArg Subtype.val hfix
      have hComm : y * (q : G) = (q : G) * y := by
        simpa [mul_assoc] using (congrArg (fun t : G => t * (q : G)) hconj).symm
      exact hComm
    have hQleP : Q ≤ P := by
      intro q hq
      exact hcentP (hQcentP hq)
    have hPp : IsPGroup p (↥P) := pCore_isPGroup (G := G) (p := p)
    obtain ⟨nP, hcardP⟩ := hPp.exists_card_eq
    have hQcopP : Nat.Coprime (Nat.card Q) (Nat.card P) := by
      rw [hcardP]
      exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd (m := nP) hpNotDvdQ
    have hQeqBot : Q = ⊥ := by
      have hInf : Q ⊓ P = ⊥ := (Subgroup.disjoint_of_coprime_natCard hQcopP).eq_bot
      simpa [inf_eq_left.2 hQleP] using hInf
    exact (hQbot hQeqBot).elim

-- Proposition 1.15(b)
set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.pPrimeCore_map_centralizer_le_pPrimeCore_of_solvable
    {G : Type v} [Group G] [Finite G] (hsolv : Group.IsSolvable G) (p : ℕ) [Fact p.Prime] :
    ∀ R : Subgroup G,
      IsPGroup p (↥R) →
        let C : Subgroup G := Subgroup.centralizer (R : Set G)
        (pPrimeCore p (↥C)).map C.subtype ≤ pPrimeCore p G := by
  classical
  intro R hRp
  have hP :
      ∀ n,
        ∀ (H : Type v) [Group H] [Finite H],
          Nat.card H = n →
            Group.IsSolvable H →
              ∀ (p : ℕ) [Fact p.Prime] (R : Subgroup H),
                IsPGroup p (↥R) →
                  let C := Subgroup.centralizer (R : Set H)
                  (pPrimeCore p (↥C)).map C.subtype ≤ pPrimeCore p H := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n IH H _ _ hcard hsolvH p _ R hRp
    let C : Subgroup H := Subgroup.centralizer (R : Set H)
    let K : Subgroup H := (pPrimeCore p (↥C)).map C.subtype
    have hK_coprime : Nat.Coprime p (Nat.card K) := by
      have hCcop : Nat.Coprime p (Nat.card (pPrimeCore p (↥C))) := pPrimeCore_coprime_card (G := (↥C)) (p := p)
      have hKcard : Nat.card K = Nat.card (pPrimeCore p (↥C)) := by
        simpa [K, C] using
          (Subgroup.card_map_of_injective (K := pPrimeCore p (↥C)) (f := C.subtype) C.subtype_injective)
      rw [hKcard]
      exact hCcop
    by_cases hM : pPrimeCore p H = ⊥
    · -- case M trivial
      have hOp_eq : Op_p'p p H = pCore p H := by
        let M : Subgroup H := pPrimeCore p H
        have hM' : M = ⊥ := hM
        let q : H →* H ⧸ M := QuotientGroup.mk' M
        let e : H ⧸ M ≃* H := (QuotientGroup.quotientMulEquivOfEq hM').trans QuotientGroup.quotientBot
        have hqe : ∀ x : H, e (q x) = x := by
          intro x
          have hmk :
              (QuotientGroup.quotientMulEquivOfEq hM') (q x) =
                (QuotientGroup.mk x : H ⧸ (⊥ : Subgroup H)) := by
            simp [q]
          calc
            e (q x) = QuotientGroup.quotientBot ((QuotientGroup.quotientMulEquivOfEq hM') (q x)) := by
              rfl
            _ = QuotientGroup.quotientBot (QuotientGroup.mk x : H ⧸ (⊥ : Subgroup H)) := by
              rw [hmk]
            _ = x := by
              rfl
        have hcomap_eq_map (L : Subgroup (H ⧸ M)) :
            L.comap q = L.map e.toMonoidHom := by
          ext x
          constructor
          · intro hx
            exact Subgroup.mem_map.mpr ⟨q x, hx, hqe x⟩
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
            have hyq : y = q x := by
              apply e.injective
              simpa [hqe x] using hyx
            simpa [hyq] using hy
        have hpCore_map :
            (pCore p (H ⧸ M)).map e.toMonoidHom = pCore p H := by
          simpa using (pCore_map_iso (G := H ⧸ M) (G' := H) (p := p) (f := e))
        simpa [Op_p'p, M, hcomap_eq_map, hpCore_map, q, e]
      have hK_le_op : K ≤ Op_p'p p H := by
        rw [hOp_eq]
        by_cases hRnorm : (R : Subgroup H).Normal
        · let : (R : Subgroup H).Normal := hRnorm
          have hK_normal : K.Normal := by
            simpa [K, C] using
              (inferInstance :
                ((pPrimeCore p (↥(Subgroup.centralizer (R : Set H)))).map
                  (Subgroup.centralizer (R : Set H)).subtype).Normal)
          have hK_bot : K = ⊥ := (pPrimeCore_eq_bot_iff (p := p) (G := H)).1 hM K hK_normal hK_coprime
          simp [hK_bot]
        · -- remaining case: `R` is not normal in `H`
          let N : Subgroup H := Subgroup.normalizer R
          have hN_ne_top : N ≠ ⊤ := by
            intro hNtop
            exact hRnorm (Subgroup.normalizer_eq_top_iff.mp hNtop)
          have hcardN_lt : Nat.card N < Nat.card H := by
            have hx : ∃ x : H, x ∉ N := by
              by_contra hno
              have hall : ∀ x : H, x ∈ N := by
                intro x
                by_contra hx
                exact hno ⟨x, hx⟩
              have hNtop : N = ⊤ := by
                ext x
                constructor
                · intro _; simp
                · intro _; exact hall x
              exact hN_ne_top hNtop
            rcases hx with ⟨x, hx⟩
            simpa [N] using (Finite.card_subtype_lt (p := fun h : H => h ∈ N) hx)
          have hcardN_lt_n : Nat.card N < n := by
            simpa [hcard] using hcardN_lt
          have hsolvN : Group.IsSolvable N := by infer_instance
          have hR_pN : IsPGroup p (↥(R.subgroupOf N)) := by
            have hR_le_N : R ≤ N := by
              simpa [N] using (Subgroup.le_normalizer (H := R))
            simpa [N] using hRp.of_equiv
              (Subgroup.subgroupOfEquivOfLe (H := R) (K := N) hR_le_N).symm
          have hIH_N := IH (Nat.card N) hcardN_lt_n (↥N) rfl hsolvN p (R.subgroupOf N) hR_pN
          have hK_le_coreN_map : K ≤ (pPrimeCore p N).map N.subtype := by
            have hK_eq :
                K =
                  ((pPrimeCore p (↥(C.subgroupOf N))).map (C.subgroupOf N).subtype).map N.subtype := by
              have hC_le_N : C ≤ N := by
                simpa [C, N] using (centralizer_le_normalizer (R := R))
              let eCN : (C.subgroupOf N) ≃* C :=
                Subgroup.subgroupOfEquivOfLe (H := C) (K := N) hC_le_N
              have hmap_core :
                  (pPrimeCore p (↥(C.subgroupOf N))).map eCN.toMonoidHom = pPrimeCore p (↥C) := by
                simpa [eCN] using
                  (pPrimeCore_map_iso (p := p) (G := ↥(C.subgroupOf N)) (G' := ↥C)
                    (f := eCN))
              have hhom :
                  C.subtype.comp eCN.toMonoidHom = N.subtype.comp (C.subgroupOf N).subtype := by
                ext z
                rfl
              calc
                K = (pPrimeCore p (↥C)).map C.subtype := by rfl
                _ = ((pPrimeCore p (↥(C.subgroupOf N))).map eCN.toMonoidHom).map C.subtype := by
                  rw [hmap_core]
                _ = (pPrimeCore p (↥(C.subgroupOf N))).map (C.subtype.comp eCN.toMonoidHom) := by
                  simp [Subgroup.map_map]
                _ = (pPrimeCore p (↥(C.subgroupOf N))).map (N.subtype.comp (C.subgroupOf N).subtype) := by
                  rw [hhom]
                _ = ((pPrimeCore p (↥(C.subgroupOf N))).map (C.subgroupOf N).subtype).map N.subtype := by
                  simp [Subgroup.map_map]
            have hIH_N0 :
                (pPrimeCore p (↥(Subgroup.centralizer ((R.subgroupOf N : Subgroup N) : Set N)))).map
                    (Subgroup.centralizer ((R.subgroupOf N : Subgroup N) : Set N)).subtype ≤
                  pPrimeCore p N := by
              simpa [N] using hIH_N
            have hCn_eq :
                Subgroup.centralizer ((R.subgroupOf N : Subgroup N) : Set N) = C.subgroupOf N := by
              simpa [N, C] using (centralizer_subgroupOf_normalizer_eq (R := R))
            have hKN_le_coreN :
                ((pPrimeCore p (↥(C.subgroupOf N))).map (C.subgroupOf N).subtype) ≤ pPrimeCore p N := by
              convert hIH_N0 using 1
              rw [hCn_eq]
            have hmap :
                ((pPrimeCore p (↥(C.subgroupOf N))).map (C.subgroupOf N).subtype).map N.subtype ≤
                  (pPrimeCore p N).map N.subtype :=
              Subgroup.map_mono hKN_le_coreN
            simpa [hK_eq] using hmap
          have hcoreN_map_le_C : (pPrimeCore p N).map N.subtype ≤ C := by
            have hRnormN : (R.subgroupOf N).Normal := by
              simpa [N] using (Subgroup.normal_in_normalizer (H := R))
            have hcoreN_le_centN :
                pPrimeCore p N ≤
                  Subgroup.centralizer ((R.subgroupOf N : Subgroup N) : Set N) := by
              let : (R.subgroupOf N).Normal := hRnormN
              exact
                pPrimeCore_le_centralizer_of_normal_pgroup
                  (G := N) (p := p) (R := R.subgroupOf N) hR_pN
            have hcent_eq :
                Subgroup.centralizer ((R.subgroupOf N : Subgroup N) : Set N) = C.subgroupOf N := by
              simpa [N, C] using (centralizer_subgroupOf_normalizer_eq (R := R))
            have hmap_cent :
                (pPrimeCore p N).map N.subtype ≤
                  (Subgroup.centralizer ((R.subgroupOf N : Subgroup N) : Set N)).map N.subtype :=
              Subgroup.map_mono hcoreN_le_centN
            have hC_le_N : C ≤ N := by
              simpa [C, N] using (centralizer_le_normalizer (R := R))
            have hCmap : (C.subgroupOf N).map N.subtype = C := by
              calc
                (C.subgroupOf N).map N.subtype = C ⊓ N := Subgroup.subgroupOf_map_subtype (H := C) (K := N)
                _ = C := inf_eq_left.mpr hC_le_N
            have hmap_cent' :
                (pPrimeCore p N).map N.subtype ≤ (C.subgroupOf N).map N.subtype := by
              simpa [hcent_eq] using hmap_cent
            exact hmap_cent'.trans (le_of_eq hCmap)
          have hcoreN_map_le_K : (pPrimeCore p N).map N.subtype ≤ K := by
            let S : Subgroup H := (pPrimeCore p N).map N.subtype
            have hS_le_C : S ≤ C := by
              simpa [S] using hcoreN_map_le_C
            have hC_le_N : C ≤ N := by
              simpa [C, N] using (centralizer_le_normalizer (R := R))
            have hS_le_N : S ≤ N := by
              intro x hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
              exact y.property
            have hconj_memS {c x : H} (hc : c ∈ C) (hx : x ∈ S) :
                c * x * c⁻¹ ∈ S := by
              have hcN : c ∈ N := hC_le_N hc
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
              have hyconj : (⟨c, hcN⟩ : N) * y * (⟨c, hcN⟩ : N)⁻¹ ∈ pPrimeCore p N := by
                exact (pPrimeCore_normal (p := p) (G := N)).conj_mem y hy ⟨c, hcN⟩
              refine Subgroup.mem_map.mpr ?_
              refine ⟨(⟨c, hcN⟩ : N) * y * (⟨c, hcN⟩ : N)⁻¹, hyconj, ?_⟩
              simpa [hyx, mul_assoc]
            have hS_normC : C ≤ Subgroup.normalizer S := by
              intro c hc
              rw [Subgroup.mem_normalizer_iff]
              intro x
              constructor
              · intro hx
                exact hconj_memS hc hx
              · intro hx
                have hcInv : c⁻¹ ∈ C := C.inv_mem hc
                simpa [mul_assoc] using hconj_memS hcInv hx
            have hSsub_norm : (S.subgroupOf C).Normal := by
              exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := S) (K := C) hS_le_C).2 hS_normC
            have hScop : Nat.Coprime p (Nat.card S) := by
              have hcop0 : Nat.Coprime p (Nat.card (pPrimeCore p N)) := pPrimeCore_coprime_card (G := N) (p := p)
              have hcardS : Nat.card S = Nat.card (pPrimeCore p N) := by
                simpa [S] using
                  (Subgroup.card_map_of_injective (K := pPrimeCore p N) (f := N.subtype) N.subtype_injective)
              rw [hcardS]
              exact hcop0
            have hScop_sub : Nat.Coprime p (Nat.card (S.subgroupOf C)) := by
              have hcard_sub : Nat.card (S.subgroupOf C) = Nat.card S := by
                exact natCard_subgroupOf_eq S C hS_le_C
              simpa [hcard_sub] using hScop
            have hSsub_le : S.subgroupOf C ≤ pPrimeCore p (↥C) := le_sSup ⟨hSsub_norm, hScop_sub⟩
            have hmap_le : (S.subgroupOf C).map C.subtype ≤ K := by
              calc
                (S.subgroupOf C).map C.subtype ≤ (pPrimeCore p (↥C)).map C.subtype :=
                  Subgroup.map_mono hSsub_le
                _ = K := by rfl
            have hS_map : (S.subgroupOf C).map C.subtype = S := by
              calc
                (S.subgroupOf C).map C.subtype = S ⊓ C := Subgroup.subgroupOf_map_subtype (H := S) (K := C)
                _ = S := inf_eq_left.mpr hS_le_C
            simpa [S] using (show S ≤ K from hS_map ▸ hmap_le)
          have hK_eq_coreN_map : K = (pPrimeCore p N).map N.subtype := by
            exact le_antisymm hK_le_coreN_map hcoreN_map_le_K
          have hK_le_N : K ≤ N := by
            intro x hx
            rw [hK_eq_coreN_map] at hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            exact y.property
          have hKsub_eq_coreN : K.subgroupOf N = pPrimeCore p N := by
            rw [hK_eq_coreN_map]
            ext x
            constructor
            · intro hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
              have hyx' : y = x := by
                apply Subtype.ext
                simpa using hyx
              simpa [hyx'] using hy
            · intro hx
              exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
          have hKsub_normal : (K.subgroupOf N).Normal := by
            simpa [hKsub_eq_coreN] using (pPrimeCore_normal (p := p) (G := N))
          have hN_le_normK : N ≤ Subgroup.normalizer K := by
            exact
              (Subgroup.normal_subgroupOf_iff_le_normalizer
                (H := K) (K := N) hK_le_N).1 hKsub_normal
          have hNnorm_le_normK : Subgroup.normalizer N ≤ Subgroup.normalizer (K : Set H) := by
            have hKsub_char : (K.subgroupOf N).Characteristic := by
              simpa [hKsub_eq_coreN] using (pPrimeCore_characteristic (p := p) (G := N))
            have hconj_memK :
                ∀ {g y : H}, g ∈ Subgroup.normalizer N → y ∈ K → g * y * g⁻¹ ∈ K := by
              intro g y hg hy
              let gN : Subgroup.normalizer N := ⟨g, hg⟩
              let yN : N := ⟨y, hK_le_N hy⟩
              have hyN : yN ∈ K.subgroupOf N := hy
              have hfix :
                  Subgroup.comap (Subgroup.normalizerMonoidHom N gN).toMonoidHom (K.subgroupOf N) =
                    K.subgroupOf N :=
                hKsub_char.fixed (Subgroup.normalizerMonoidHom N gN)
              have hyComap :
                  yN ∈ Subgroup.comap (Subgroup.normalizerMonoidHom N gN).toMonoidHom (K.subgroupOf N) := by
                rw [hfix]
                exact hyN
              have hyImage : (Subgroup.normalizerMonoidHom N gN) yN ∈ K.subgroupOf N := hyComap
              change (((Subgroup.normalizerMonoidHom N gN) yN : N) : H) ∈ K at hyImage
              simpa [gN, yN, mul_assoc] using hyImage
            intro g hg
            rw [Subgroup.mem_normalizer_iff]
            intro y
            constructor
            · intro hy
              exact hconj_memK hg hy
            · intro hy
              have hgInv : g⁻¹ ∈ Subgroup.normalizer (N : Set H) := by
                simpa using (Subgroup.inv_mem_iff (H := Subgroup.normalizer (N : Set H))).2 hg
              have hy' : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ ∈ K := hconj_memK hgInv hy
              simpa [mul_assoc] using hy'
          have hcoreN_map_le_pcore : (pPrimeCore p N).map N.subtype ≤ pCore p H := by
            have hK_le_pcore : K ≤ pCore p H := by
              by_cases hK_bot : K = ⊥
              · simp [hK_bot]
              · have hcent_pcore_le_pcore :
                    Subgroup.centralizer (pCore p H : Set H) ≤ pCore p H := by
                  have hfit_eq : fittingSubgroup H = pCore p H :=
                    Fitting_eq_pcore (G := H) (p := p) hM
                  have hcent_fit :
                      Subgroup.centralizer (fittingSubgroup H : Set H) ≤ fittingSubgroup H :=
                    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := H) hsolvH
                  simpa [hfit_eq] using hcent_fit
                have hK_le_coreNormK_map :
                    K ≤ (pPrimeCore p (Subgroup.normalizer (K : Set H))).map (Subgroup.normalizer (K : Set H)).subtype := by
                  have hKsub_normalNorm : (K.subgroupOf (Subgroup.normalizer (K : Set H))).Normal := by
                    simpa using (Subgroup.normal_in_normalizer (H := K))
                  have hKsub_coprime : Nat.Coprime p (Nat.card (K.subgroupOf (Subgroup.normalizer (K : Set H)))) := by
                    have hcard_sub : Nat.card (K.subgroupOf (Subgroup.normalizer (K : Set H))) = Nat.card K := by
                      exact natCard_subgroupOf_eq K (Subgroup.normalizer (K : Set H)) Subgroup.le_normalizer
                    simpa [hcard_sub] using hK_coprime
                  have hKsub_le_coreNorm : K.subgroupOf (Subgroup.normalizer (K : Set H)) ≤ pPrimeCore p (Subgroup.normalizer (K : Set H)) :=
                    le_sSup ⟨hKsub_normalNorm, hKsub_coprime⟩
                  have hmap_le :
                      (K.subgroupOf (Subgroup.normalizer (K : Set H))).map (Subgroup.normalizer (K : Set H)).subtype ≤
                        (pPrimeCore p (Subgroup.normalizer (K : Set H))).map (Subgroup.normalizer (K : Set H)).subtype :=
                    Subgroup.map_mono hKsub_le_coreNorm
                  have hmap_eq :
                      (K.subgroupOf (Subgroup.normalizer (K : Set H))).map (Subgroup.normalizer (K : Set H)).subtype = K := by
                    calc
                      (K.subgroupOf (Subgroup.normalizer (K : Set H))).map (Subgroup.normalizer (K : Set H)).subtype = K ⊓ (Subgroup.normalizer (K : Set H)) :=
                        Subgroup.subgroupOf_map_subtype (H := K) (K := (Subgroup.normalizer (K : Set H)))
                      _ = K := inf_eq_left.mpr Subgroup.le_normalizer
                  simpa [hmap_eq] using hmap_le
                have hnormK_ne_top : (Subgroup.normalizer (K : Set H)) ≠ ⊤ := by
                  intro hnormK_top
                  have hK_normal : K.Normal := Subgroup.normalizer_eq_top_iff.mp hnormK_top
                  have hK_eq_bot : K = ⊥ :=
                    (pPrimeCore_eq_bot_iff (p := p) (G := H)).1 hM K hK_normal hK_coprime
                  exact hK_bot hK_eq_bot
                have hcardNormK_lt : Nat.card (Subgroup.normalizer (K : Set H)) < Nat.card H := by
                  have hx : ∃ x : H, x ∉ (Subgroup.normalizer (K : Set H)) := by
                    by_contra hno
                    have hall : ∀ x : H, x ∈ (Subgroup.normalizer (K : Set H)) := by
                      intro x
                      by_contra hx
                      exact hno ⟨x, hx⟩
                    have hnormK_top : (Subgroup.normalizer (K : Set H)) = ⊤ := by
                      ext x
                      constructor
                      · intro _; simp
                      · intro _; exact hall x
                    exact hnormK_ne_top hnormK_top
                  rcases hx with ⟨x, hx⟩
                  simpa using (Finite.card_subtype_lt (p := fun h : H => h ∈ (Subgroup.normalizer (K : Set H))) hx)
                have hK_le_coreNormK_map_rec :
                    K ≤ (pPrimeCore p (Subgroup.normalizer (K : Set H))).map (Subgroup.normalizer (K : Set H)).subtype := by
                  have hR_le_normK : R ≤ (Subgroup.normalizer (K : Set H)) := by
                    exact (Subgroup.le_normalizer (H := R)).trans hN_le_normK
                  have hC_le_normK : C ≤ (Subgroup.normalizer (K : Set H)) := by
                    have hC_le_N : C ≤ N := by
                      simpa [C, N] using (centralizer_le_normalizer (R := R))
                    exact hC_le_N.trans hN_le_normK
                  have hcardNormK_lt_n : Nat.card (Subgroup.normalizer (K : Set H)) < n := by
                    simpa [hcard] using hcardNormK_lt
                  have hsolvNormK : Group.IsSolvable (Subgroup.normalizer (K : Set H)) := by infer_instance
                  have hR_pNormK : IsPGroup p (↥(R.subgroupOf (Subgroup.normalizer (K : Set H)))) := by
                    simpa using hRp.of_equiv
                      (Subgroup.subgroupOfEquivOfLe (H := R) (K := (Subgroup.normalizer (K : Set H))) hR_le_normK).symm
                  have hIH_normK :=
                    IH (Nat.card (Subgroup.normalizer (K : Set H))) hcardNormK_lt_n (↥(Subgroup.normalizer (K : Set H))) rfl hsolvNormK p
                      (R.subgroupOf (Subgroup.normalizer (K : Set H))) hR_pNormK
                  have hCnormK_eq :
                      Subgroup.centralizer ((R.subgroupOf (Subgroup.normalizer (K : Set H)) : Subgroup (Subgroup.normalizer (K : Set H))) : Set (Subgroup.normalizer (K : Set H))) =
                        C.subgroupOf (Subgroup.normalizer (K : Set H)) := by
                    ext x
                    constructor
                    · intro hx
                      change (x : H) ∈ C
                      rw [Subgroup.mem_centralizer_iff]
                      intro y hy
                      let yK : (Subgroup.normalizer (K : Set H)) := ⟨y, hR_le_normK hy⟩
                      have hyK : yK ∈ R.subgroupOf (Subgroup.normalizer (K : Set H)) := hy
                      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) yK hyK)
                    · intro hx
                      change (x : H) ∈ C at hx
                      rw [Subgroup.mem_centralizer_iff] at hx
                      rw [Subgroup.mem_centralizer_iff]
                      intro y hy
                      apply Subtype.ext
                      exact hx (y : H) hy
                  have hIH_normK0 :
                      (pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (K : Set H))))).map (C.subgroupOf (Subgroup.normalizer (K : Set H))).subtype ≤
                        pPrimeCore p (Subgroup.normalizer (K : Set H)) := by
                    convert hIH_normK using 1
                    rw [hCnormK_eq]
                  have hmap_norm :
                      ((pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (K : Set H))))).map (C.subgroupOf (Subgroup.normalizer (K : Set H))).subtype).map
                          (Subgroup.normalizer (K : Set H)).subtype ≤
                        (pPrimeCore p (Subgroup.normalizer (K : Set H))).map (Subgroup.normalizer (K : Set H)).subtype :=
                    Subgroup.map_mono hIH_normK0
                  have hK_eq :
                      K =
                        ((pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (K : Set H))))).map (C.subgroupOf (Subgroup.normalizer (K : Set H))).subtype).map
                          (Subgroup.normalizer (K : Set H)).subtype := by
                    let eC : (C.subgroupOf (Subgroup.normalizer (K : Set H))) ≃* C :=
                      Subgroup.subgroupOfEquivOfLe (H := C) (K := (Subgroup.normalizer (K : Set H))) hC_le_normK
                    have hcore_map :
                        (pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (K : Set H))))).map eC.toMonoidHom =
                          pPrimeCore p (↥C) := by
                      simpa [eC] using
                        (pPrimeCore_map_iso (p := p) (G := ↥(C.subgroupOf (Subgroup.normalizer (K : Set H)))) (G' := ↥C) (f := eC))
                    have hhom :
                        C.subtype.comp eC.toMonoidHom =
                          (Subgroup.normalizer (K : Set H)).subtype.comp (C.subgroupOf (Subgroup.normalizer (K : Set H))).subtype := by
                      ext z
                      rfl
                    calc
                      K = (pPrimeCore p (↥C)).map C.subtype := by rfl
                      _ = ((pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (K : Set H))))).map eC.toMonoidHom).map C.subtype := by
                        rw [hcore_map]
                      _ = (pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (K : Set H))))).map (C.subtype.comp eC.toMonoidHom) := by
                        simp [Subgroup.map_map]
                      _ = (pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (K : Set H))))).map
                          ((Subgroup.normalizer (K : Set H)).subtype.comp (C.subgroupOf (Subgroup.normalizer (K : Set H))).subtype) := by
                        rw [hhom]
                      _ = ((pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (K : Set H))))).map (C.subgroupOf (Subgroup.normalizer (K : Set H))).subtype).map
                          (Subgroup.normalizer (K : Set H)).subtype := by
                        simp [Subgroup.map_map]
                  simpa [hK_eq] using hmap_norm
                have hcoreNormK_map_le_cent :
                    (pPrimeCore p ((Subgroup.normalizer (K : Set H)))).map (Subgroup.normalizer (K : Set H)).subtype ≤
                      Subgroup.centralizer (pCore p H : Set H) := by
                  have pCore_le_of_index_coprime_normalizer {S : Subgroup H}
                      (hS_coprime : Nat.Coprime p S.index) : pCore p H ≤ S := by
                    let P : Subgroup H := pCore p H
                    have hP_rel :
                        P.relIndex (S ⊔ P) = (S ⊓ P).relIndex S := by
                      calc
                        P.relIndex (S ⊔ P) = P.relIndex S := by
                          simp
                        _ = (S ⊓ P).relIndex S := by
                          symm
                          simpa [inf_comm] using (Subgroup.inf_relIndex_left (H := S) (K := P))
                    have hmul :
                        (S ⊓ P).relIndex S * S.relIndex (S ⊔ P) =
                          (S ⊓ P).relIndex P * (S ⊓ P).relIndex S := by
                      calc
                        (S ⊓ P).relIndex S * S.relIndex (S ⊔ P) =
                            (S ⊓ P).relIndex (S ⊔ P) := by
                          exact
                            Subgroup.relIndex_mul_relIndex (H := S ⊓ P) (K := S) (L := S ⊔ P)
                              inf_le_left le_sup_left
                        _ = (S ⊓ P).relIndex P * P.relIndex (S ⊔ P) := by
                          symm
                          exact
                            Subgroup.relIndex_mul_relIndex (H := S ⊓ P) (K := P) (L := S ⊔ P)
                              inf_le_right le_sup_right
                        _ = (S ⊓ P).relIndex P * (S ⊓ P).relIndex S := by
                          rw [hP_rel]
                    have hrel_pos : 0 < (S ⊓ P).relIndex S := by
                      have hrel_ne_zero : (S ⊓ P).relIndex S ≠ 0 := by
                        dsimp [Subgroup.relIndex]
                        exact Subgroup.index_ne_zero_of_finite (H := (S ⊓ P).subgroupOf S)
                      exact Nat.pos_of_ne_zero hrel_ne_zero
                    have hrel_eq :
                        S.relIndex (S ⊔ P) = (S ⊓ P).relIndex P := by
                      have hmul' :
                          (S ⊓ P).relIndex S * S.relIndex (S ⊔ P) =
                            (S ⊓ P).relIndex S * (S ⊓ P).relIndex P := by
                        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
                      exact Nat.eq_of_mul_eq_mul_left hrel_pos hmul'
                    have hrel_dvd_cardP : S.relIndex (S ⊔ P) ∣ Nat.card P := by
                      rw [hrel_eq]
                      exact Subgroup.relIndex_dvd_card (H := S ⊓ P) (K := P)
                    have hrel_dvd_indexS : S.relIndex (S ⊔ P) ∣ S.index :=
                      Subgroup.relIndex_dvd_index_of_le (H := S) (K := S ⊔ P) le_sup_left
                    have hcop_cardP_indexS : Nat.Coprime (Nat.card P) S.index := by
                      rcases (pCore_isPGroup (p := p) (G := H)).exists_card_eq with ⟨n, hn⟩
                      simpa [P, hn] using hS_coprime.pow_left n
                    have hrel_eq_one : S.relIndex (S ⊔ P) = 1 :=
                      Nat.eq_one_of_dvd_coprimes hcop_cardP_indexS hrel_dvd_cardP hrel_dvd_indexS
                    have hsup_le : S ⊔ P ≤ S := (Subgroup.relIndex_eq_one).1 hrel_eq_one
                    exact (show P ≤ S ⊔ P from le_sup_right).trans hsup_le
                  have exists_sylow_le_iff_not_dvd_index (S : Subgroup H) :
                      (∃ P : Sylow p H, (P : Subgroup H) ≤ S) ↔ ¬ p ∣ S.index := by
                    constructor
                    · rintro ⟨P, hP_le_S⟩ hp_dvd
                      exact P.not_dvd_index (hp_dvd.trans (Subgroup.index_dvd_of_le hP_le_S))
                    · intro hS_not_dvd
                      let PS : Sylow p S := Classical.choice Sylow.nonempty
                      let Pmap : Subgroup H := (PS : Subgroup S).map S.subtype
                      have hPmap_p : IsPGroup p (↥Pmap) := by
                        exact
                          IsPGroup.map (p := p) (H := (PS : Subgroup S))
                            PS.isPGroup' S.subtype
                      have hPmap_not_dvd : ¬ p ∣ Pmap.index := by
                        have hPS_not_dvd : ¬ p ∣ (PS : Subgroup S).index := PS.not_dvd_index
                        rw [show Pmap = (PS : Subgroup S).map S.subtype by rfl]
                        rw [Subgroup.index_map_subtype (H := S) (K := (PS : Subgroup S))]
                        exact Nat.Prime.not_dvd_mul (Fact.out : Nat.Prime p) hPS_not_dvd hS_not_dvd
                      refine ⟨hPmap_p.toSylow hPmap_not_dvd, ?_⟩
                      simpa [Pmap] using
                        (Subgroup.map_subtype_le (H := S) (K := (PS : Subgroup S)))
                  have sylow_mem_fixedPoints_R_iff (P : Sylow p H) :
                      P ∈ MulAction.fixedPoints R (Sylow p H) ↔ R ≤ (P : Subgroup H) := by
                    constructor
                    · intro hPfix
                      have hR_le_normP : R ≤ (Subgroup.normalizer (((P : Subgroup H)) : Set H)) :=
                        (Subgroup.sylow_mem_fixedPoints_iff (H := R) (P := P)).1 hPfix
                      have hinf :
                          R ⊓ (Subgroup.normalizer (((P : Subgroup H)) : Set H)) = R ⊓ (P : Subgroup H) :=
                        IsPGroup.inf_normalizer_sylow (p := p) hRp P
                      have hR_eq_inf : R = R ⊓ (P : Subgroup H) := by
                        calc
                          R = R ⊓ (Subgroup.normalizer (((P : Subgroup H)) : Set H)) := (inf_eq_left.mpr hR_le_normP).symm
                          _ = R ⊓ (P : Subgroup H) := hinf
                      exact inf_eq_left.mp hR_eq_inf.symm
                    · intro hR_le_P
                      exact (Subgroup.sylow_mem_fixedPoints_iff (H := R) (P := P)).2
                        (hR_le_P.trans Subgroup.le_normalizer)
                  have exists_sylow_ge_R : ∃ P : Sylow p H, R ≤ (P : Subgroup H) := by
                    have hfix_nonempty : (MulAction.fixedPoints R (Sylow p H)).Nonempty := by
                      exact hRp.nonempty_fixed_point_of_prime_not_dvd_card
                        (α := Sylow p H) (not_dvd_card_sylow (p := p) (G := H))
                    rcases hfix_nonempty with ⟨P, hPfix⟩
                    exact ⟨P, (sylow_mem_fixedPoints_R_iff P).1 hPfix⟩
                  have normalizer_index_not_dvd_of_nontrivial_core_branch :
                      ¬ p ∣ N.index := by
                    have hKsub_char : (K.subgroupOf N).Characteristic := by
                      simpa [hKsub_eq_coreN] using (pPrimeCore_characteristic (p := p) (G := N))
                    have hK_normal_of_hN_normal : N.Normal → K.Normal := by
                      intro hN_normal
                      let : N.Normal := hN_normal
                      let : (K.subgroupOf N).Characteristic := hKsub_char
                      have hmap_normal : ((K.subgroupOf N).map N.subtype).Normal := by infer_instance
                      have hmap_eq : (K.subgroupOf N).map N.subtype = K := by
                        calc
                          (K.subgroupOf N).map N.subtype = K ⊓ N :=
                            Subgroup.subgroupOf_map_subtype (H := K) (K := N)
                          _ = K := inf_eq_left.mpr hK_le_N
                      exact hmap_eq ▸ hmap_normal
                    have hK_le_coreNnorm_map :
                        K ≤ (pPrimeCore p ((Subgroup.normalizer (N : Set H)))).map (Subgroup.normalizer (N : Set H)).subtype := by
                      have hK_le_Nnorm : K ≤ (Subgroup.normalizer (N : Set H)) := hK_le_N.trans Subgroup.le_normalizer
                      have hKsubNnorm_normal : (K.subgroupOf (Subgroup.normalizer (N : Set H))).Normal := by
                        exact
                          (Subgroup.normal_subgroupOf_iff_le_normalizer
                            (H := K) (K := (Subgroup.normalizer (N : Set H))) hK_le_Nnorm).2 hNnorm_le_normK
                      have hKsubNnorm_coprime : Nat.Coprime p (Nat.card (K.subgroupOf (Subgroup.normalizer (N : Set H)))) := by
                        have hcard_sub : Nat.card (K.subgroupOf (Subgroup.normalizer (N : Set H))) = Nat.card K := by
                          exact natCard_subgroupOf_eq K (Subgroup.normalizer (N : Set H)) hK_le_Nnorm
                        simpa [hcard_sub] using hK_coprime
                      have hKsubNnorm_le_core :
                          K.subgroupOf (Subgroup.normalizer (N : Set H)) ≤ pPrimeCore p ((Subgroup.normalizer (N : Set H))) :=
                        le_sSup ⟨hKsubNnorm_normal, hKsubNnorm_coprime⟩
                      have hmap_le :
                          (K.subgroupOf (Subgroup.normalizer (N : Set H))).map (Subgroup.normalizer (N : Set H)).subtype ≤
                            (pPrimeCore p ((Subgroup.normalizer (N : Set H)))).map (Subgroup.normalizer (N : Set H)).subtype :=
                        Subgroup.map_mono hKsubNnorm_le_core
                      have hmap_eq :
                          (K.subgroupOf (Subgroup.normalizer (N : Set H))).map (Subgroup.normalizer (N : Set H)).subtype = K := by
                        calc
                          (K.subgroupOf (Subgroup.normalizer (N : Set H))).map (Subgroup.normalizer (N : Set H)).subtype = K ⊓ (Subgroup.normalizer (N : Set H)) :=
                            Subgroup.subgroupOf_map_subtype (H := K) (K := (Subgroup.normalizer (N : Set H)))
                          _ = K := inf_eq_left.mpr hK_le_Nnorm
                      simpa [hmap_eq] using hmap_le
                    intro hp_dvd
                    by_cases hN_normal : N.Normal
                    · have hK_normal : K.Normal := hK_normal_of_hN_normal hN_normal
                      exact hK_bot ((pPrimeCore_eq_bot_iff (p := p) (G := H)).1 hM K hK_normal hK_coprime)
                    · -- Remaining hard sub-branch: `N = N_H(R)` not normal and `p ∣ [H : N]`.
                      have hcontr_of_not_dvd_Nnorm_index : ¬ p ∣ (Subgroup.normalizer (N : Set H)).index → False := by
                        intro hNnorm_not_dvd
                        have hNnorm_coprime : Nat.Coprime p (Subgroup.normalizer (N : Set H)).index := by
                          exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hNnorm_not_dvd
                        have hpCore_le_normK : pCore p H ≤ (Subgroup.normalizer (K : Set H)) := by
                          refine (le_trans ?_ hNnorm_le_normK)
                          exact pCore_le_of_index_coprime_normalizer (S := (Subgroup.normalizer (N : Set H))) hNnorm_coprime
                        let P0 : Subgroup ((Subgroup.normalizer (K : Set H))) := (pCore p H).subgroupOf (Subgroup.normalizer (K : Set H))
                        have hP0_p : IsPGroup p (↥P0) := by
                          have hpCore_p : IsPGroup p (↥(pCore p H)) := pCore_isPGroup (p := p) (G := H)
                          simpa [P0] using hpCore_p.of_equiv
                            (Subgroup.subgroupOfEquivOfLe (H := pCore p H) (K := (Subgroup.normalizer (K : Set H))) hpCore_le_normK).symm
                        have hcoreNormK_map_le_cent :
                            (pPrimeCore p ((Subgroup.normalizer (K : Set H)))).map (Subgroup.normalizer (K : Set H)).subtype ≤
                              Subgroup.centralizer (pCore p H : Set H) := by
                          have hcoreNormK_le_centP0 :
                              pPrimeCore p ((Subgroup.normalizer (K : Set H))) ≤ Subgroup.centralizer (P0 : Set ((Subgroup.normalizer (K : Set H)))) := by
                            let : P0.Normal := by
                              infer_instance
                            exact
                              pPrimeCore_le_centralizer_of_normal_pgroup
                                (G := (Subgroup.normalizer (K : Set H))) (p := p) (R := P0) hP0_p
                          have hmap_le :
                              (pPrimeCore p ((Subgroup.normalizer (K : Set H)))).map (Subgroup.normalizer (K : Set H)).subtype ≤
                                (Subgroup.centralizer (P0 : Set ((Subgroup.normalizer (K : Set H))))).map (Subgroup.normalizer (K : Set H)).subtype :=
                            Subgroup.map_mono hcoreNormK_le_centP0
                          have hcentP0_map_le :
                              (Subgroup.centralizer (P0 : Set ((Subgroup.normalizer (K : Set H))))).map (Subgroup.normalizer (K : Set H)).subtype ≤
                                Subgroup.centralizer (pCore p H : Set H) := by
                            intro x hx
                            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                            rw [Subgroup.mem_centralizer_iff]
                            intro z hz
                            have hz_normK : z ∈ (Subgroup.normalizer (K : Set H)) := hpCore_le_normK hz
                            have hzP0 : (⟨z, hz_normK⟩ : (Subgroup.normalizer (K : Set H))) ∈ P0 := hz
                            have hy_comm :
                                y * (⟨z, hz_normK⟩ : (Subgroup.normalizer (K : Set H))) =
                                  (⟨z, hz_normK⟩ : (Subgroup.normalizer (K : Set H))) * y :=
                              ((Subgroup.mem_centralizer_iff.mp hy) ⟨z, hz_normK⟩ hzP0).symm
                            simpa using (congrArg Subtype.val hy_comm).symm
                          exact hmap_le.trans hcentP0_map_le
                        have hK_le_pcore' : K ≤ pCore p H :=
                          (hK_le_coreNormK_map_rec.trans hcoreNormK_map_le_cent).trans hcent_pcore_le_pcore
                        have hK_p : IsPGroup p (↥K) := by
                          exact IsPGroup.to_le (hK := pCore_isPGroup (p := p) (G := H)) hK_le_pcore'
                        have hK_card_one : Nat.card K = 1 := by
                          rcases hK_p.card_eq_or_dvd with h1 | hpdvd
                          · exact h1
                          · exfalso
                            exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hK_coprime) hpdvd
                        have hK_eq_bot : K = ⊥ := Subgroup.card_eq_one.mp hK_card_one
                        exact hK_bot hK_eq_bot
                      have hcontr_of_dvd_Nnorm_index : p ∣ (Subgroup.normalizer (N : Set H)).index → False := by
                        intro hNnorm_dvd
                        have hno_sylow_le_Nnorm : ¬ ∃ P : Sylow p H, (P : Subgroup H) ≤ (Subgroup.normalizer (N : Set H)) := by
                          intro hP
                          exact (exists_sylow_le_iff_not_dvd_index (S := (Subgroup.normalizer (N : Set H)))).1 hP hNnorm_dvd
                        have hNnorm_ne_top : (Subgroup.normalizer (N : Set H)) ≠ ⊤ := by
                          intro hNnorm_top
                          have hidx : (Subgroup.normalizer (N : Set H)).index = 1 := by
                            simp [hNnorm_top]
                          exact (Nat.Prime.not_dvd_one (Fact.out : Nat.Prime p)) (hidx ▸ hNnorm_dvd)
                        have hcardNnorm_lt : Nat.card (Subgroup.normalizer (N : Set H)) < Nat.card H := by
                          have hx : ∃ x : H, x ∉ (Subgroup.normalizer (N : Set H)) := by
                            by_contra hno
                            have hall : ∀ x : H, x ∈ (Subgroup.normalizer (N : Set H)) := by
                              intro x
                              by_contra hx
                              exact hno ⟨x, hx⟩
                            have hNnorm_top : (Subgroup.normalizer (N : Set H)) = ⊤ := by
                              ext x
                              constructor
                              · intro _; simp
                              · intro _; exact hall x
                            exact hNnorm_ne_top hNnorm_top
                          rcases hx with ⟨x, hx⟩
                          simpa using (Finite.card_subtype_lt (p := fun h : H => h ∈ (Subgroup.normalizer (N : Set H))) hx)
                        have hcardNnorm_lt_n : Nat.card (Subgroup.normalizer (N : Set H)) < n := by
                          simpa [hcard] using hcardNnorm_lt
                        have hsolvNnorm : Group.IsSolvable (Subgroup.normalizer (N : Set H)) := by infer_instance
                        have hR_le_N : R ≤ N := by
                          simpa [N] using (Subgroup.le_normalizer (H := R))
                        have hR_le_Nnorm : R ≤ (Subgroup.normalizer (N : Set H)) := hR_le_N.trans Subgroup.le_normalizer
                        have hR_pNnorm : IsPGroup p (↥(R.subgroupOf (Subgroup.normalizer (N : Set H)))) := by
                          simpa using hRp.of_equiv
                            (Subgroup.subgroupOfEquivOfLe (H := R) (K := (Subgroup.normalizer (N : Set H))) hR_le_Nnorm).symm
                        have hIH_Nnorm :=
                          IH (Nat.card (Subgroup.normalizer (N : Set H))) hcardNnorm_lt_n (↥(Subgroup.normalizer (N : Set H))) rfl hsolvNnorm p
                            (R.subgroupOf (Subgroup.normalizer (N : Set H))) hR_pNnorm
                        have hC_Nnorm_eq :
                            Subgroup.centralizer ((R.subgroupOf (Subgroup.normalizer (N : Set H)) : Subgroup (Subgroup.normalizer (N : Set H))) : Set (Subgroup.normalizer (N : Set H))) =
                              C.subgroupOf (Subgroup.normalizer (N : Set H)) := by
                          ext x
                          constructor
                          · intro hx
                            change (x : H) ∈ C
                            rw [Subgroup.mem_centralizer_iff]
                            intro y hy
                            let yN : (Subgroup.normalizer (N : Set H)) := ⟨y, hR_le_Nnorm hy⟩
                            have hyN : yN ∈ R.subgroupOf (Subgroup.normalizer (N : Set H)) := hy
                            exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) yN hyN)
                          · intro hx
                            change (x : H) ∈ C at hx
                            rw [Subgroup.mem_centralizer_iff] at hx
                            rw [Subgroup.mem_centralizer_iff]
                            intro y hy
                            apply Subtype.ext
                            exact hx (y : H) hy
                        have hIH_Nnorm0 :
                            (pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (N : Set H))))).map (C.subgroupOf (Subgroup.normalizer (N : Set H))).subtype ≤
                              pPrimeCore p ((Subgroup.normalizer (N : Set H))) := by
                          convert hIH_Nnorm using 1
                          rw [hC_Nnorm_eq]
                        have hC_le_Nnorm : C ≤ (Subgroup.normalizer (N : Set H)) := by
                          exact (centralizer_le_normalizer (R := R)).trans Subgroup.le_normalizer
                        have hK_le_coreNnorm_map_rec :
                            K ≤ (pPrimeCore p ((Subgroup.normalizer (N : Set H)))).map (Subgroup.normalizer (N : Set H)).subtype := by
                          have hmap_norm :
                              ((pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (N : Set H))))).map
                                    (C.subgroupOf (Subgroup.normalizer (N : Set H))).subtype).map (Subgroup.normalizer (N : Set H)).subtype ≤
                                (pPrimeCore p ((Subgroup.normalizer (N : Set H)))).map (Subgroup.normalizer (N : Set H)).subtype :=
                            Subgroup.map_mono hIH_Nnorm0
                          have hK_eq :
                              K =
                                ((pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (N : Set H))))).map
                                      (C.subgroupOf (Subgroup.normalizer (N : Set H))).subtype).map (Subgroup.normalizer (N : Set H)).subtype := by
                            let eC : (C.subgroupOf (Subgroup.normalizer (N : Set H))) ≃* C :=
                              Subgroup.subgroupOfEquivOfLe (H := C) (K := (Subgroup.normalizer (N : Set H))) hC_le_Nnorm
                            have hcore_map :
                                (pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (N : Set H))))).map eC.toMonoidHom =
                                  pPrimeCore p (↥C) := by
                              simpa [eC] using
                                (pPrimeCore_map_iso (p := p) (G := ↥(C.subgroupOf (Subgroup.normalizer (N : Set H)))) (G' := ↥C) (f := eC))
                            have hhom :
                                C.subtype.comp eC.toMonoidHom =
                                  (Subgroup.normalizer (N : Set H)).subtype.comp (C.subgroupOf (Subgroup.normalizer (N : Set H))).subtype := by
                              ext z
                              rfl
                            calc
                              K = (pPrimeCore p (↥C)).map C.subtype := by rfl
                              _ = ((pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (N : Set H))))).map eC.toMonoidHom).map C.subtype := by
                                rw [hcore_map]
                              _ = (pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (N : Set H))))).map
                                  (C.subtype.comp eC.toMonoidHom) := by
                                simp [Subgroup.map_map]
                              _ = (pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (N : Set H))))).map
                                  ((Subgroup.normalizer (N : Set H)).subtype.comp (C.subgroupOf (Subgroup.normalizer (N : Set H))).subtype) := by
                                rw [hhom]
                              _ = ((pPrimeCore p (↥(C.subgroupOf (Subgroup.normalizer (N : Set H))))).map
                                    (C.subgroupOf (Subgroup.normalizer (N : Set H))).subtype).map (Subgroup.normalizer (N : Set H)).subtype := by
                                simp [Subgroup.map_map]
                          simpa [hK_eq] using hmap_norm
                        have hcoreNnorm_ne_bot : pPrimeCore p ((Subgroup.normalizer (N : Set H))) ≠ ⊥ := by
                          intro hcoreNnorm_bot
                          have hmap_bot :
                              (pPrimeCore p ((Subgroup.normalizer (N : Set H)))).map (Subgroup.normalizer (N : Set H)).subtype = ⊥ := by
                            simp [hcoreNnorm_bot]
                          have hK_eq_bot : K = ⊥ := by
                            exact le_bot_iff.mp (hK_le_coreNnorm_map_rec.trans (le_of_eq hmap_bot))
                          exact hK_bot hK_eq_bot
                        have exists_conjR_le_Nnorm_not_mem :
                            ∃ g : H, g ∉ (Subgroup.normalizer (N : Set H)) ∧
                              ∀ r : H, r ∈ R → g⁻¹ * r * g ∈ (Subgroup.normalizer (N : Set H)) := by
                          have hcard_quot_dvd : p ∣ Nat.card (H ⧸ (Subgroup.normalizer (N : Set H))) := by
                            simpa [Subgroup.index_eq_card] using hNnorm_dvd
                          have hone_fix :
                              ((1 : H) : H ⧸ (Subgroup.normalizer (N : Set H))) ∈
                                MulAction.fixedPoints R (H ⧸ (Subgroup.normalizer (N : Set H))) := by
                            rw [MulAction.mem_fixedPoints]
                            intro r
                            rw [MulAction.subgroup_smul_def]
                            have hrNnorm : (r : H) ∈ (Subgroup.normalizer (N : Set H)) := hR_le_Nnorm r.property
                            have hrInvNnorm : ((r : H)⁻¹) ∈ (Subgroup.normalizer (N : Set H)) := by
                              simpa using (Subgroup.inv_mem_iff (H := (Subgroup.normalizer (N : Set H)))).2 hrNnorm
                            have hEq : ((r : H) : H ⧸ (Subgroup.normalizer (N : Set H))) = ((1 : H) : H ⧸ (Subgroup.normalizer (N : Set H))) := by
                              exact (QuotientGroup.eq).2 (by simpa using hrInvNnorm)
                            simpa [smul_eq_mul] using hEq
                          rcases hRp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
                              (α := H ⧸ (Subgroup.normalizer (N : Set H))) hcard_quot_dvd hone_fix with ⟨b, hbfix, hbne⟩
                          rcases QuotientGroup.mk_surjective b with ⟨g, rfl⟩
                          have hg_not_mem : g ∉ (Subgroup.normalizer (N : Set H)) := by
                            intro hgNnorm
                            have hgInvNnorm : g⁻¹ ∈ (Subgroup.normalizer (N : Set H)) := by
                              simpa using (Subgroup.inv_mem_iff (H := (Subgroup.normalizer (N : Set H)))).2 hgNnorm
                            have hEq : ((g : H) : H ⧸ (Subgroup.normalizer (N : Set H))) = ((1 : H) : H ⧸ (Subgroup.normalizer (N : Set H))) := by
                              exact (QuotientGroup.eq).2 (by simpa using hgInvNnorm)
                            exact hbne (hEq.symm)
                          refine ⟨g, hg_not_mem, ?_⟩
                          intro r hrR
                          have hfixg :
                              ((⟨r, hrR⟩ : R) • ((g : H) : H ⧸ (Subgroup.normalizer (N : Set H)))) =
                                ((g : H) : H ⧸ (Subgroup.normalizer (N : Set H))) :=
                            (MulAction.mem_fixedPoints.mp hbfix) ⟨r, hrR⟩
                          have hEq :
                              (((r * g : H)) : H ⧸ (Subgroup.normalizer (N : Set H))) =
                                ((g : H) : H ⧸ (Subgroup.normalizer (N : Set H))) := by
                            simpa [smul_eq_mul] using hfixg
                          have hmemInv : ((r * g : H)⁻¹ * g) ∈ (Subgroup.normalizer (N : Set H)) := (QuotientGroup.eq).1 hEq
                          have hmemInv' : (g⁻¹ * r⁻¹ * g) ∈ (Subgroup.normalizer (N : Set H)) := by
                            simpa [mul_assoc] using hmemInv
                          have hmemInv'' : (g⁻¹ * r * g)⁻¹ ∈ (Subgroup.normalizer (N : Set H)) := by
                            simpa [mul_assoc] using hmemInv'
                          exact (Subgroup.inv_mem_iff (H := (Subgroup.normalizer (N : Set H)))).1 hmemInv''
                        let _ := hcoreNnorm_ne_bot
                        let _ := exists_conjR_le_Nnorm_not_mem
                        let _ := hK_le_coreNnorm_map_rec
                        let _ := hno_sylow_le_Nnorm
                        let _ := hK_le_coreNnorm_map
                        have hexists_sylow_le_Nnorm : ∃ P : Sylow p H, (P : Subgroup H) ≤ (Subgroup.normalizer (N : Set H)) := by
                          have hK_eq_bot : K = ⊥ := by
                            simpa [K, C] using
                              (pPrimeCore_centralizer_pSubgroup_eq_bot_of_pPrimeCore_eq_bot
                                (G := H) hsolvH (p := p) hM R hRp)
                          exact (hK_bot hK_eq_bot).elim
                        exact hno_sylow_le_Nnorm hexists_sylow_le_Nnorm
                      by_cases hNnorm_dvd : p ∣ (Subgroup.normalizer (N : Set H)).index
                      · -- Hard residual case: both `p ∣ N.index` and `p ∣ [H : N_H(N)]`.
                        exact hcontr_of_dvd_Nnorm_index hNnorm_dvd
                      · exact (hcontr_of_not_dvd_Nnorm_index hNnorm_dvd).elim
                  have hpCore_le_normK : pCore p H ≤ (Subgroup.normalizer (K : Set H)) := by
                    refine (le_trans ?_ hNnorm_le_normK)
                    exact pCore_le_of_index_coprime_normalizer (S := (Subgroup.normalizer (N : Set H))) (by
                      have hNnorm_index_dvd_N_index : (Subgroup.normalizer (N : Set H)).index ∣ N.index := by
                        exact Subgroup.index_dvd_of_le (H := N) (K := (Subgroup.normalizer (N : Set H))) Subgroup.le_normalizer
                      have hN_index_not_dvd : ¬ p ∣ N.index := by
                        exact normalizer_index_not_dvd_of_nontrivial_core_branch
                      have hN_index_coprime : Nat.Coprime p N.index := by
                        exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hN_index_not_dvd
                      -- Push coprimality down along the normalizer-index divisibility.
                      have hNnorm_index_coprime : Nat.Coprime p (Subgroup.normalizer (N : Set H)).index := by
                        exact Nat.Coprime.of_dvd_right hNnorm_index_dvd_N_index hN_index_coprime
                      exact hNnorm_index_coprime
                      )
                  let P0 : Subgroup ((Subgroup.normalizer (K : Set H))) := (pCore p H).subgroupOf (Subgroup.normalizer (K : Set H))
                  have hP0_p : IsPGroup p (↥P0) := by
                    have hpCore_p : IsPGroup p (↥(pCore p H)) := pCore_isPGroup (p := p) (G := H)
                    simpa [P0] using hpCore_p.of_equiv
                      (Subgroup.subgroupOfEquivOfLe (H := pCore p H) (K := (Subgroup.normalizer (K : Set H))) hpCore_le_normK).symm
                  have hcoreNormK_le_centP0 :
                      pPrimeCore p ((Subgroup.normalizer (K : Set H))) ≤ Subgroup.centralizer (P0 : Set ((Subgroup.normalizer (K : Set H)))) := by
                    let : P0.Normal := by
                      infer_instance
                    exact
                      pPrimeCore_le_centralizer_of_normal_pgroup
                        (G := (Subgroup.normalizer (K : Set H))) (p := p) (R := P0) hP0_p
                  have hmap_le :
                      (pPrimeCore p ((Subgroup.normalizer (K : Set H)))).map (Subgroup.normalizer (K : Set H)).subtype ≤
                        (Subgroup.centralizer (P0 : Set ((Subgroup.normalizer (K : Set H))))).map (Subgroup.normalizer (K : Set H)).subtype :=
                    Subgroup.map_mono hcoreNormK_le_centP0
                  have hcentP0_map_le :
                      (Subgroup.centralizer (P0 : Set ((Subgroup.normalizer (K : Set H))))).map (Subgroup.normalizer (K : Set H)).subtype ≤
                        Subgroup.centralizer (pCore p H : Set H) := by
                    intro x hx
                    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                    rw [Subgroup.mem_centralizer_iff]
                    intro z hz
                    have hz_normK : z ∈ (Subgroup.normalizer (K : Set H)) := hpCore_le_normK hz
                    have hzP0 : (⟨z, hz_normK⟩ : (Subgroup.normalizer (K : Set H))) ∈ P0 := hz
                    have hy_comm :
                        y * (⟨z, hz_normK⟩ : (Subgroup.normalizer (K : Set H))) =
                          (⟨z, hz_normK⟩ : (Subgroup.normalizer (K : Set H))) * y :=
                      ((Subgroup.mem_centralizer_iff.mp hy) ⟨z, hz_normK⟩ hzP0).symm
                    simpa using (congrArg Subtype.val hy_comm).symm
                  exact hmap_le.trans hcentP0_map_le
                exact (hK_le_coreNormK_map_rec.trans hcoreNormK_map_le_cent).trans hcent_pcore_le_pcore
            simpa [hK_eq_coreN_map] using hK_le_pcore
          exact hK_le_coreN_map.trans hcoreN_map_le_pcore
      exact le_pPrimeCore_of_le_Op_p'p_of_coprime (G := H) (p := p) hK_le_op hK_coprime
    · -- case M nontrivial
      let M : Subgroup H := pPrimeCore p H
      have hM_ne_bot : M ≠ ⊥ := hM
      let q : H →* H ⧸ M := QuotientGroup.mk' M
      let : M.Normal := by
        simpa [M] using (pPrimeCore_normal (p := p) (G := H))
      have hcard_quot_lt : Nat.card (H ⧸ M) < Nat.card H := by
        have hM_one_lt : 1 < Nat.card M :=
          (Subgroup.one_lt_card_iff_ne_bot (H := M)).2 hM_ne_bot
        have hcard : Nat.card H = Nat.card (H ⧸ M) * Nat.card M := by
          simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := H) (s := M))
        have hlt : Nat.card (H ⧸ M) * 1 < Nat.card (H ⧸ M) * Nat.card M :=
          Nat.mul_lt_mul_of_pos_left hM_one_lt (Nat.card_pos (α := H ⧸ M))
        simpa [hcard] using hlt
      have hsolvQ : Group.IsSolvable (H ⧸ M) := by infer_instance
      have hRq_p : IsPGroup p (↥(R.map q)) := IsPGroup.map (p := p) hRp q
      have hcard_quot_lt_n : Nat.card (H ⧸ M) < n := by
        simpa [hcard] using hcard_quot_lt
      have IH_Q := IH (Nat.card (H ⧸ M)) hcard_quot_lt_n (H ⧸ M) rfl hsolvQ p (R.map q) hRq_p
      have hCbar_eq : Subgroup.centralizer ((R.map q : Subgroup (H ⧸ M)) : Set (H ⧸ M)) = C.map q := by
        let : Fact (IsPGroup p (↥R)) := ⟨hRp⟩
        have hM_normal : M.Normal := by infer_instance
        have hMcop : Nat.Coprime p (Nat.card M) := by
          simpa [M] using (pPrimeCore_coprime_card (G := H) (p := p))
        simpa [C, q] using
          (centralizer_map_quotient_eq_map_centralizer (G := H) (p := p) (T := R) (M := M) hM_normal hMcop)
      have h_pcore_bot : pPrimeCore p (H ⧸ M) = ⊥ := by
        simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) (p := p))
      have h_pcore_Cbar_le_bot : (pPrimeCore p (↥(C.map q))).map (C.map q).subtype ≤ ⊥ := by
        have hCbar_eq_set : Subgroup.centralizer (⇑q '' (R : Set H)) = C.map q := by
          simpa [Subgroup.coe_map] using hCbar_eq
        have h_pcore_Cbar_le : (pPrimeCore p (↥(C.map q))).map (C.map q).subtype ≤ pPrimeCore p (H ⧸ M) := by
          have h_IH_Q :
              (pPrimeCore p (↥(Subgroup.centralizer (⇑q '' (R : Set H))))).map
                (Subgroup.centralizer (⇑q '' (R : Set H))).subtype ≤ pPrimeCore p (H ⧸ M) := IH_Q
          rw [hCbar_eq_set] at h_IH_Q
          exact h_IH_Q
        exact h_pcore_Cbar_le.trans (le_of_eq h_pcore_bot)
      have h_pcore_Cbar_bot : pPrimeCore p (↥(C.map q)) = ⊥ := by
        have hmap_bot : (pPrimeCore p (↥(C.map q))).map (C.map q).subtype = ⊥ :=
          le_bot_iff.mp h_pcore_Cbar_le_bot
        exact
          (Subgroup.map_eq_bot_iff_of_injective
            (H := pPrimeCore p (↥(C.map q)))
            (f := (C.map q).subtype)
            (C.map q).subtype_injective).1 hmap_bot
      have hK_le_op : K ≤ Op_p'p p H := by
        intro x hxK
        rcases Subgroup.mem_map.mp hxK with ⟨y, hy, rfl⟩
        change q (C.subtype y : H) ∈ pCore p (H ⧸ M)
        have hyCbar : q (C.subtype y : H) ∈ C.map q := by
          exact Subgroup.mem_map.mpr ⟨(y : C), (y : C).property, rfl⟩
        have hy_pprimeCbar : (⟨q (C.subtype y : H), hyCbar⟩ : C.map q) ∈ pPrimeCore p (↥(C.map q)) := by
          let ψ : C →* C.map q :=
            (q.comp C.subtype).codRestrict (C.map q) (by intro c; exact Subgroup.mem_map.mpr ⟨c, c.property, rfl⟩)
          have hψ_surj : Function.Surjective ψ := by
            intro z
            rcases Subgroup.mem_map.mp z.property with ⟨c, hc, hcz⟩
            refine ⟨⟨c, hc⟩, ?_⟩
            apply Subtype.ext
            simpa [ψ] using hcz
          have hmap_le : (pPrimeCore p (↥C)).map ψ ≤ pPrimeCore p (↥(C.map q)) := by
            have hnorm : ((pPrimeCore p (↥C)).map ψ).Normal :=
              Subgroup.Normal.map (inferInstance : (pPrimeCore p (↥C)).Normal) ψ hψ_surj
            have hcop : Nat.Coprime p (Nat.card ((pPrimeCore p (↥C)).map ψ)) := by
              exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := pPrimeCore p (↥C)) ψ)
                (pPrimeCore_coprime_card (G := (↥C)) (p := p))
            exact le_sSup ⟨hnorm, hcop⟩
          have hy_map : (ψ y : C.map q) ∈ (pPrimeCore p (↥C)).map ψ :=
            Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
          exact hmap_le (by simpa [ψ] using hy_map)
        have hy_bot : (⟨q (C.subtype y : H), hyCbar⟩ : C.map q) ∈ (⊥ : Subgroup (C.map q)) := by
          simpa [h_pcore_Cbar_bot] using hy_pprimeCbar
        have hy_one_sub : (⟨q (C.subtype y : H), hyCbar⟩ : C.map q) = 1 := by
          simpa using hy_bot
        have hy_one : q (C.subtype y : H) = 1 := by
          simpa using congrArg Subtype.val hy_one_sub
        rw [hy_one]
        exact (pCore p (H ⧸ M)).one_mem
      exact le_pPrimeCore_of_le_Op_p'p_of_coprime (G := H) (p := p) hK_le_op hK_coprime
  exact hP (Nat.card G) G rfl hsolv p R hRp

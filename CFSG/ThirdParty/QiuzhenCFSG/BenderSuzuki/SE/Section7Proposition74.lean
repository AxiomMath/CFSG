module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Lemma73
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma311
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 7.4: the source orbit package

This module records the source-facing `Gamma` package and checks the two
routine branches after the Lemma 7.3/Lemma 3.11 source inputs are isolated.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

public abbrev theorem4bSection7Base
    {X : Type u} [Group X] [Finite X] {M : Subgroup X} :
    conjugateCosetSpace M :=
  QuotientGroup.mk 1

public def theorem4bSection7PairCentralizer
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (K : Set X) (beta gamma : conjugateCosetSpace M) : Subgroup X :=
  (Subgroup.centralizer K ⊓ MulAction.stabilizer X beta) ⊓
    MulAction.stabilizer X gamma

/-- Source-facing data of Proposition 7.4.  The pair-centralizer is kept in
the literal set form used by the source; closure conversion is performed only
at the Lemma 7.5/7.6 call sites. -/
public def Theorem4bProposition74Data
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) : Prop :=
  ∃ Gamma : Set (conjugateCosetSpace M),
    Gamma ⊆ d.data.kFixedPoints ∧
    theorem4bSection7Base ∈ Gamma ∧
    1 < Nat.card Gamma ∧
    (∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma ↔ d.data.z • beta ∈ Gamma) ∧
    (∀ {beta gamma : conjugateCosetSpace M},
      beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
        theorem4bSection7PairCentralizer d.data.invertedSet beta gamma ≤ M) ∧
    (∀ {beta : conjugateCosetSpace M},
      beta ∈ Gamma → beta ≠ theorem4bSection7Base →
        ∃ t : X,
          IsInvolution t ∧
          t • theorem4bSection7Base = beta ∧
          rightConjugateSet d.data.invertedSet
              (rightConjugateElem t d.data.z) ⊆
            theorem4bSection7E M d.data.z beta ∧
          theorem4bSection7PairCentralizer
              (rightConjugateSet d.data.invertedSet
                (rightConjugateElem t d.data.z))
              theorem4bSection7Base beta ≤
                theorem4bSection7E M d.data.z beta ∧
          ∃ g : X,
            g • (d.data.z • beta) = theorem4bSection7Base ∧
              g • beta ∈ Gamma)

/-- Exact source-sized output used from Lemma 3.11 in the second branch.
It deliberately contains neither `Gamma ⊆ Omega_K` nor any Proposition 7.4
conclusion; those are checked consequences below. -/
public def Theorem4bLemma311Output
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (H : Subgroup X) : Prop :=
  ∃ R : Subgroup X, ∃ Gamma : Set (conjugateCosetSpace M),
    R ≤ H ∧
    Gamma = MulAction.orbit R theorem4bSection7Base ∧
    (∃ r : ℕ, Nat.Prime r ∧ Odd r ∧ IsPGroup r R ∧
      Nat.card Gamma = r) ∧
    d.data.z ∈ Subgroup.normalizer (R : Set X) ∧
    (∀ beta, beta ∈ Gamma → d.data.z • beta ∈ Gamma) ∧
    (∀ {beta gamma}, beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
      ∀ x, x ∈ H → x • beta = beta → x • gamma = gamma →
        ∀ delta, delta ∈ Gamma → x • delta = delta) ∧
    (∀ beta, beta ∈ Gamma → beta ≠ theorem4bSection7Base →
      ∃ t, IsInvolution t ∧ t ∈ H ∧
        t • theorem4bSection7Base = beta ∧
        t • beta = theorem4bSection7Base)

theorem rightConjugateSet_comp_section7
    {G : Type*} [Group G] (K : Set G) (a b : G) :
    rightConjugateSet (rightConjugateSet K a) b =
      rightConjugateSet K (a * b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, by simp [rightConjugateElem, mul_assoc]⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨rightConjugateElem k a, ⟨k, hk, rfl⟩, ?_⟩
    simp [rightConjugateElem, mul_assoc]

theorem Theorem4bSixA.invertedSet_rightConjugate_z_section7
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) :
    rightConjugateSet d.invertedSet d.z = d.invertedSet := by
  have hconj_mem : ∀ {x : X}, x ∈ d.invertedSet →
      rightConjugateElem x d.z ∈ d.invertedSet := by
    intro x hx
    have hx' := (d.mem_invertedSet_iff x).mp hx
    have hxeq : rightConjugateElem x d.z = x⁻¹ := by
      simpa [rightConjugateElem, d.hz.inv_eq_self] using hx'.2
    apply (d.mem_invertedSet_iff _).mpr
    constructor
    · rw [hxeq]
      exact d.W.inv_mem hx'.1
    · rw [hxeq]
      calc
        d.z * x⁻¹ * d.z⁻¹ = (d.z * x * d.z⁻¹)⁻¹ := by group
        _ = (x⁻¹)⁻¹ := by rw [hx'.2]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hconj_mem hx
  · intro hy
    refine ⟨rightConjugateElem y d.z, hconj_mem hy, ?_⟩
    exact (rightConjugateElem_rightConjugateElem d.hz.inv_eq_self).symm

theorem centralizer_rightConjugateSet_le_stabilizer_section7
    {G Omega : Type*} [Group G] [MulAction G Omega]
    {K : Set G} {u : G} {alpha : Omega}
    (hu : IsInvolution u)
    (hC : Subgroup.centralizer K ≤ MulAction.stabilizer G alpha) :
    Subgroup.centralizer (rightConjugateSet K u) ≤
      MulAction.stabilizer G (u • alpha) := by
  intro c hc
  apply MulAction.mem_stabilizer_iff.mpr
  have huu : u * u = 1 := by simpa [pow_two] using hu.sq_eq_one
  let c0 : G := rightConjugateElem c u
  have hc0 : c0 ∈ Subgroup.centralizer K := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    let ku : G := rightConjugateElem k u
    have hku : ku ∈ rightConjugateSet K u := ⟨k, hk, rfl⟩
    have hcomm : ku * c = c * ku :=
      (Subgroup.mem_centralizer_iff.mp hc) ku hku
    calc
      k * c0 = rightConjugateElem ku u * rightConjugateElem c u := by
        rw [rightConjugateElem_rightConjugateElem hu.inv_eq_self]
      _ = rightConjugateElem (ku * c) u := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (c * ku) u := by rw [hcomm]
      _ = rightConjugateElem c u * rightConjugateElem ku u := by
        simp [rightConjugateElem, mul_assoc]
      _ = c0 * k := by
        rw [rightConjugateElem_rightConjugateElem hu.inv_eq_self]
  have hc0fix : c0 • alpha = alpha :=
    MulAction.mem_stabilizer_iff.mp (hC hc0)
  have hcu : c * u = u * c0 := by
    have hc0eq : c0 = u * c * u := by
      simp [c0, rightConjugateElem, hu.inv_eq_self]
    rw [hc0eq]
    calc
      c * u = 1 * (c * u) := by simp
      _ = (u * u) * (c * u) := by rw [huu]
      _ = u * (u * c * u) := by group
  calc
    c • (u • alpha) = (c * u) • alpha := by rw [smul_smul]
    _ = (u * c0) • alpha := by rw [hcu]
    _ = u • (c0 • alpha) := by rw [smul_smul]
    _ = u • alpha := by rw [hc0fix]

theorem mem_normalizer_of_rightConjugateSet_eq_self_of_involution_section7
    {X : Type u} [Group X] (K : Set X) {z : X}
    (hz : IsInvolution z)
    (hK : rightConjugateSet K z = K) :
    z ∈ Subgroup.normalizer K := by
  change ∀ n : X, n ∈ K ↔ z * n * z⁻¹ ∈ K
  have hforward : ∀ {n : X}, n ∈ K → z * n * z⁻¹ ∈ K := by
    intro n hn
    have hright : rightConjugateElem n z ∈ rightConjugateSet K z :=
      ⟨n, hn, rfl⟩
    rw [hK] at hright
    simpa [rightConjugateElem, hz.inv_eq_self] using hright
  intro n
  constructor
  · exact hforward
  · intro hn
    have hback := hforward hn
    have hsq : z * z = 1 := by
      simpa [pow_two] using hz.sq_eq_one
    have heq : z * (z * n * z⁻¹) * z⁻¹ = n := by
      rw [hz.inv_eq_self]
      calc
        z * (z * n * z) * z = (z * z) * n * (z * z) := by group
        _ = n := by rw [hsq]; simp
    rw [heq] at hback
    exact hback

theorem rightConjugateSet_eq_self_of_mem_normalizer_section7
    {X : Type u} [Group X] (K : Set X) {u : X}
    (hu : u ∈ Subgroup.normalizer K) :
    rightConjugateSet K u = K := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hui : u⁻¹ ∈ Subgroup.normalizer K :=
      (Subgroup.normalizer K).inv_mem hu
    change u⁻¹ * k * u ∈ K
    change ∀ n : X, n ∈ K ↔ u⁻¹ * n * (u⁻¹)⁻¹ ∈ K at hui
    simpa [mul_assoc] using (hui k).mp hk
  · intro hy
    have hforward : u * y * u⁻¹ ∈ K := by
      change ∀ n : X, n ∈ K ↔ u * n * u⁻¹ ∈ K at hu
      exact (hu y).mp hy
    refine ⟨u * y * u⁻¹, hforward, ?_⟩
    simp [rightConjugateElem, mul_assoc]

/-- The `C_X(K) ≤ M` branch of Proposition 7.4, relative only to the exact
normalizing-swap output of Lemma 7.3. -/
public theorem IsStronglyEmbedded.theorem4bProposition74_of_centralizer_le
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixD M)
    (hC : Subgroup.centralizer d.data.invertedSet ≤ M)
    (hswap : ∀ {beta : conjugateCosetSpace M} {P : Subgroup X},
      beta ∈ d.data.kFixedPoints →
      beta ≠ theorem4bSection7Base →
      theorem4bIsSylowSubgroupOf d.data.p P
        (theorem4bSection7E M d.data.z beta) →
      d.data.z ∈ Subgroup.normalizer (P : Set X) →
      ∃ t : X,
        IsInvolution t ∧
        t ∈ Subgroup.normalizer (P : Set X) ∧
        t • theorem4bSection7Base = beta) :
    Theorem4bProposition74Data d := by
  let Gamma : Set (conjugateCosetSpace M) := d.data.kFixedPoints
  have hbase : theorem4bSection7Base ∈ Gamma := by
    apply d.data.fixedPoints_subset_kFixedPoints
    exact theorem4b_baseCoset_mem_fixedPoints d.data.hWM
  have hcard : 1 < Nat.card Gamma := by
    obtain ⟨beta, hbetaW, hbetaNe⟩ := d.data.exists_nonbase_fixedPoint
    have hbetaK : beta ∈ Gamma :=
      d.data.fixedPoints_subset_kFixedPoints hbetaW
    let alphaPoint : Gamma := ⟨theorem4bSection7Base, hbase⟩
    let betaPoint : Gamma := ⟨beta, hbetaK⟩
    let f : Bool → Gamma := fun b => cond b betaPoint alphaPoint
    have hf : Function.Injective f := by
      intro a b hab
      cases a <;> cases b
      · rfl
      · exfalso
        apply hbetaNe
        simpa [f, alphaPoint, betaPoint] using
          (congrArg Subtype.val hab).symm
      · exfalso
        apply hbetaNe
        simpa [f, alphaPoint, betaPoint] using congrArg Subtype.val hab
      · rfl
    have htwo : 2 ≤ Nat.card Gamma := by
      simpa using Nat.card_le_card_of_injective f hf
    omega
  have hzGammaForward : ∀ {beta : conjugateCosetSpace M},
      beta ∈ Gamma → d.data.z • beta ∈ Gamma := by
    intro beta hbeta
    have hbetaW := d.data.kFixedPoints_subset_fixedPoints hbeta
    have hWbeta : d.data.W ≤ MulAction.stabilizer X beta := by
      intro w hw
      exact MulAction.mem_stabilizer_iff.mpr (hbetaW w hw)
    have hWzBeta : d.data.W ≤
        MulAction.stabilizer X (d.data.z • beta) :=
      theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
        d.data.hzNorm hWbeta
    apply d.data.fixedPoints_subset_kFixedPoints
    intro w hw
    exact MulAction.mem_stabilizer_iff.mp (hWzBeta hw)
  have hzGamma : ∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma ↔ d.data.z • beta ∈ Gamma := by
    intro beta
    constructor
    · exact hzGammaForward
    · intro hbeta
      have htwice := hzGammaForward hbeta
      have hzz : d.data.z • (d.data.z • beta) = beta := by
        rw [← mul_smul]
        have hsq : d.data.z * d.data.z = 1 := by
          simpa [pow_two] using d.data.hz.sq_eq_one
        rw [hsq, one_smul]
      simpa [hzz] using htwice
  refine ⟨Gamma, fun _ h => h, hbase, hcard, hzGamma, ?_, ?_⟩
  · intro beta gamma _hbeta _hgamma _hne x hx
    exact hC hx.1.1
  · intro beta hbeta hbetaNe
    let E : Subgroup X := theorem4bSection7E M d.data.z beta
    have hbetaW := d.data.kFixedPoints_subset_fixedPoints hbeta
    have hWbeta : d.data.W ≤ MulAction.stabilizer X beta := by
      intro w hw
      exact MulAction.mem_stabilizer_iff.mpr (hbetaW w hw)
    have hWD : d.data.W ≤ theorem4bSection7D M beta :=
      le_inf d.data.hWM hWbeta
    have hWE : d.data.W ≤ E := by
      simpa [E, theorem4bSection7E, theorem4bSection7D] using
        theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer
          d.data.hzNorm hWD
    have hDodd : Odd (Nat.card (theorem4bSection7D M beta)) := by
      simpa [theorem4bSection7D] using
        hM.base_inf_stabilizer_card_odd hbetaNe
    have hEodd : Odd (Nat.card E) := by
      exact Odd.of_dvd_nat hDodd
        (Subgroup.card_dvd_of_le
          (show E ≤ theorem4bSection7D M beta from inf_le_left))
    have hzE : d.data.z ∈ Subgroup.normalizer (E : Set X) := by
      simpa [E, theorem4bSection7E, theorem4bSection7D] using
        theorem4b_mem_normalizer_tripleStabilizer
          (M := M) (z := d.data.z) (beta := beta)
          d.data.hz d.data.hzM
    obtain ⟨P, hPsyl, hWP, hzP⟩ :=
      theorem4b_exists_invariant_sylow_containing
        hEodd d.data.hz hzE d.data.hp d.data.hWp hWE d.data.hzNorm
    obtain ⟨t, ht, htP, htBase⟩ :=
      hswap hbeta hbetaNe (by simpa [E] using hPsyl) hzP
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    have htBeta : t • beta = theorem4bSection7Base := by
      calc
        t • beta = t • (t • theorem4bSection7Base) := by rw [htBase]
        _ = (t * t) • theorem4bSection7Base := by rw [smul_smul]
        _ = theorem4bSection7Base := by rw [htt, one_smul]
    have hPE : P ≤ E := by
      rcases hPsyl with ⟨Q, rfl⟩
      simpa using Subgroup.map_le_range E.subtype (Q : Subgroup E)
    let u : X := rightConjugateElem t d.data.z
    have hu : IsInvolution u := isInvolution_rightConjugateElem ht
    have huNormP : u ∈ Subgroup.normalizer (P : Set X) := by
      change d.data.z⁻¹ * t * d.data.z ∈
        Subgroup.normalizer (P : Set X)
      exact (Subgroup.normalizer (P : Set X)).mul_mem
        ((Subgroup.normalizer (P : Set X)).mul_mem
          ((Subgroup.normalizer (P : Set X)).inv_mem hzP) htP) hzP
    have hKconjP : rightConjugateSet d.data.invertedSet u ⊆ P := by
      intro x hx
      rcases hx with ⟨k, hk, rfl⟩
      have hkW : k ∈ d.data.W :=
        ((d.data.mem_invertedSet_iff k).mp hk).1
      have hkP : k ∈ P := hWP hkW
      have huInvNorm : u⁻¹ ∈ Subgroup.normalizer (P : Set X) :=
        (Subgroup.normalizer (P : Set X)).inv_mem huNormP
      simpa [rightConjugateElem] using
        ((Subgroup.mem_normalizer_iff.mp huInvNorm k).mp hkP)
    have hKconjE : rightConjugateSet d.data.invertedSet u ⊆ E :=
      fun x hx => hPE (hKconjP hx)
    have hzBase : d.data.z •
        (theorem4bSection7Base (X := X) (M := M)) =
          theorem4bSection7Base (X := X) (M := M) := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [baseCoset_stabilizer]
      exact d.data.hzM
    have huBase : u • theorem4bSection7Base = d.data.z • beta := by
      simp [u, rightConjugateElem, d.data.hz.inv_eq_self,
        mul_smul, hzBase, htBase]
    have hCbase : Subgroup.centralizer d.data.invertedSet ≤
        MulAction.stabilizer X
          (theorem4bSection7Base (X := X) (M := M)) := by
      simpa [theorem4bSection7Base, baseCoset_stabilizer] using hC
    have hCzBeta :
        Subgroup.centralizer (rightConjugateSet d.data.invertedSet u) ≤
          MulAction.stabilizer X (d.data.z • beta) := by
      simpa [huBase] using
        centralizer_rightConjugateSet_le_stabilizer_section7 hu hCbase
    have hpairE : theorem4bSection7PairCentralizer
        (rightConjugateSet d.data.invertedSet u)
          theorem4bSection7Base beta ≤ E := by
      intro x hx
      have hxM : x ∈ M := by
        rw [← baseCoset_stabilizer M]
        exact hx.1.2
      exact ⟨⟨hxM, hx.2⟩, hCzBeta hx.1.1⟩
    let g : X := t * d.data.z
    have hgFirst : g • (d.data.z • beta) = theorem4bSection7Base := by
      have hzz : d.data.z • (d.data.z • beta) = beta := by
        rw [← mul_smul]
        have hsq : d.data.z * d.data.z = 1 := by
          simpa [pow_two] using d.data.hz.sq_eq_one
        rw [hsq, one_smul]
      calc
        g • (d.data.z • beta) =
            t • (d.data.z • (d.data.z • beta)) := by
              rw [show g = t * d.data.z by rfl, mul_smul]
        _ = t • beta := by rw [hzz]
        _ = theorem4bSection7Base := htBeta
    have hKz : rightConjugateSet d.data.invertedSet d.data.z =
        d.data.invertedSet :=
      d.data.invertedSet_rightConjugate_z_section7
    have hKuKg : rightConjugateSet d.data.invertedSet u =
        rightConjugateSet d.data.invertedSet g := by
      calc
        rightConjugateSet d.data.invertedSet u =
            rightConjugateSet d.data.invertedSet
              (d.data.z * (t * d.data.z)) := by
                simp [u, rightConjugateElem, d.data.hz.inv_eq_self,
                  mul_assoc]
        _ = rightConjugateSet
              (rightConjugateSet d.data.invertedSet d.data.z)
              (t * d.data.z) :=
                (rightConjugateSet_comp_section7
                  d.data.invertedSet d.data.z (t * d.data.z)).symm
        _ = rightConjugateSet d.data.invertedSet (t * d.data.z) := by
              rw [hKz]
        _ = rightConjugateSet d.data.invertedSet g := rfl
    have hKconjG : rightConjugateSet d.data.invertedSet g ⊆ E := by
      rw [← hKuKg]
      exact hKconjE
    have hEstabBeta : E ≤ MulAction.stabilizer X beta :=
      inf_le_left.trans inf_le_right
    have hgBeta : g • beta ∈ Gamma := by
      apply (d.data.mem_kFixedPoints_iff (g • beta)).mpr
      intro k hk
      let kg : X := rightConjugateElem k g
      have hkg : kg ∈ rightConjugateSet d.data.invertedSet g :=
        ⟨k, hk, rfl⟩
      have hkgFix : kg • beta = beta :=
        MulAction.mem_stabilizer_iff.mp (hEstabBeta (hKconjG hkg))
      calc
        k • (g • beta) = (k * g) • beta := by rw [smul_smul]
        _ = (g * kg) • beta := by
          simp [kg, rightConjugateElem, mul_assoc]
        _ = g • (kg • beta) := by rw [smul_smul]
        _ = g • beta := by rw [hkgFix]
    refine ⟨t, ht, htBase, ?_, ?_, g, hgFirst, hgBeta⟩
    · simpa [u] using hKconjE
    · simpa [u] using hpairE

private theorem source_apply_centralizer_no_involution
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (C : Subgroup X) (K : Set X) (H : Subgroup X) (z : X)
    (hC : C = Subgroup.centralizer K)
    (hH : H = C ⊔ Subgroup.zpowers z)
    (hzH : z ∈ H)
    (hzM : z ∈ M)
    (hz : IsInvolution z)
    (hHnorm : H ≤ Subgroup.normalizer K)
    (hzNotC : z ∉ C)
    (hCnot : ¬ C ≤ M) :
    ∀ s : X, s ∈ C → IsInvolution s → False := by
  have hCsubH : C ≤ H := by
    rw [hH]
    exact le_sup_left
  have hHnotM : ¬ H ≤ M := by
    intro hHM
    apply hCnot
    exact hCsubH.trans hHM
  let MH : Subgroup H := M.comap H.subtype
  have hMHproper : MH ≠ ⊤ := by
    intro htop
    apply hHnotM
    intro x hx
    let xH : H := ⟨x, hx⟩
    have hxMH : xH ∈ MH := by
      rw [htop]
      trivial
    exact hxMH
  let zH : H := ⟨z, hzH⟩
  have hzMH : zH ∈ MH := by
    change z ∈ M
    exact hzM
  have hzHI : IsInvolution zH := IsInvolution.subtype hz hzH
  have hMHstrong : IsStronglyEmbedded MH :=
    hM.comap_of_injective H.subtype Subtype.val_injective hMHproper
      ⟨zH, hzMH, hzHI⟩
  intro s hsC hsI
  have hsH : s ∈ H := hCsubH hsC
  let sH : H := ⟨s, hsH⟩
  have hsHI : IsInvolution sH := IsInvolution.subtype hsI hsH
  obtain ⟨g, hconj⟩ := hMHstrong.involutions_conjugate
    (x := zH) (y := sH) hzHI hsHI
  have hconjX : rightConjugateElem z (g : X) = s := by
    exact congrArg Subtype.val hconj
  have hgNorm : (g : X) ∈ Subgroup.normalizer K := hHnorm g.property
  have hgInvNorm : (g : X)⁻¹ ∈ Subgroup.normalizer K :=
    (Subgroup.normalizer K).inv_mem hgNorm
  have hzC : z ∈ C := by
    rw [hC]
    apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    have hk' : (g : X)⁻¹ * k * (g : X) ∈ K := by
      change ∀ n : X, n ∈ K ↔
        (g : X)⁻¹ * n * ((g : X)⁻¹)⁻¹ ∈ K at hgInvNorm
      simpa using (hgInvNorm k).mp hk
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hC ▸ hsC))
      ((g : X)⁻¹ * k * (g : X)) hk'
    have hgs : (g : X) * s * (g : X)⁻¹ = z := by
      rw [← hconjX]
      simp [rightConjugateElem, mul_assoc]
    calc
      k * z = k * ((g : X) * s * (g : X)⁻¹) := by rw [hgs]
      _ = (g : X) * (((g : X)⁻¹ * k * (g : X)) * s) *
          (g : X)⁻¹ := by group
      _ = (g : X) * (s * ((g : X)⁻¹ * k * (g : X))) *
          (g : X)⁻¹ := by rw [hcomm]
      _ = ((g : X) * s * (g : X)⁻¹) * k := by group
      _ = z * k := by rw [hgs]
  exact hzNotC hzC

private theorem source_apply_no_two_rank
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (C H : Subgroup X) (K : Set X) (z : X)
    (hC : C = Subgroup.centralizer K)
    (hH : H = C ⊔ Subgroup.zpowers z)
    (hzH : z ∈ H) (hzM : z ∈ M) (hz : IsInvolution z)
    (hHnorm : H ≤ Subgroup.normalizer K)
    (hzNotC : z ∉ C) (hCnot : ¬ C ≤ M) :
    ¬ TwoRankAtLeastTwo H := by
  have hCsubH : C ≤ H := by
    rw [hH]
    exact le_sup_left
  have hno : ∀ s : X, s ∈ C → IsInvolution s → False :=
    source_apply_centralizer_no_involution hM C K H z hC hH hzH hzM hz
      hHnorm hzNotC hCnot
  let CH : Subgroup H := C.subgroupOf H
  have hforwardFor : ∀ a : X, a ∈ H →
      ∀ c : X, c ∈ C → a * c * a⁻¹ ∈ C := by
    intro a ha c hc
    rw [hC]
    apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    have hnormInv : a⁻¹ ∈ Subgroup.normalizer K :=
      (Subgroup.normalizer K).inv_mem (hHnorm ha)
    change ∀ n : X, n ∈ K ↔
      a⁻¹ * n * (a⁻¹)⁻¹ ∈ K at hnormInv
    have hk' : a⁻¹ * k * a ∈ K := by
      simpa using (hnormInv k).mp hk
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hC ▸ hc))
      (a⁻¹ * k * a) hk'
    calc
      k * (a * c * a⁻¹) = a * ((a⁻¹ * k * a) * c) * a⁻¹ := by group
      _ = a * (c * (a⁻¹ * k * a)) * a⁻¹ := by rw [hcomm]
      _ = (a * c * a⁻¹) * k := by group
  have hCHnormalizer : H ≤ Subgroup.normalizer (C : Set X) := by
    intro h hh
    change ∀ c : X, c ∈ C ↔ h * c * h⁻¹ ∈ C
    intro c
    constructor
    · exact hforwardFor h hh c
    · intro hc
      have hback := hforwardFor h⁻¹ (H.inv_mem hh)
        (h * c * h⁻¹) hc
      have heq : h⁻¹ * (h * c * h⁻¹) * (h⁻¹)⁻¹ = c := by group
      rwa [heq] at hback
  have hCHnormal : CH.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCsubH).2 hCHnormalizer
  have hCHodd : Odd (Nat.card CH) := by
    by_contra hodd
    have heven : Even (Nat.card CH) := Nat.not_odd_iff_even.mp hodd
    have htwo : 2 ∣ Nat.card CH := even_iff_two_dvd.mp heven
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, huOrder⟩ := exists_prime_orderOf_dvd_card' (G := CH) 2 htwo
    have huNe : (u : H) ≠ 1 := by
      intro huOne
      have : orderOf u = 1 := by
        have huOneCH : u = 1 := by
          apply Subtype.ext
          exact huOne
        simp [huOneCH]
      omega
    have huSq : (u : H) ^ 2 = 1 := by
      exact congrArg Subtype.val (by
        simpa [huOrder] using pow_orderOf_eq_one u)
    have huI : IsInvolution (u : H) := ⟨huNe, huSq⟩
    have huIX : IsInvolution (u : X) :=
      IsInvolution.map_of_injective huI H.subtype H.subtype_injective
    exact hno (u : X) u.property huIX
  let zH : H := ⟨z, hzH⟩
  let ZH : Subgroup H := Subgroup.zpowers zH
  have hsupMap : (CH ⊔ ZH).map H.subtype = H := by
    rw [Subgroup.map_sup]
    rw [Subgroup.map_subgroupOf_eq_of_le hCsubH]
    rw [MonoidHom.map_zpowers]
    change C ⊔ Subgroup.zpowers z = H
    exact hH.symm
  have hsup : CH ⊔ ZH = (⊤ : Subgroup H) := by
    apply (Subgroup.map_injective H.subtype_injective)
    calc
      (CH ⊔ ZH).map H.subtype = H := hsupMap
      _ = (⊤ : Subgroup H).map H.subtype := by
        symm
        simpa [MonoidHom.range_eq_map] using
          (Subgroup.range_subtype (H := H))
  have hzNormCH : zH ∈ Subgroup.normalizer (CH : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hCHnormal]
    trivial
  have hzHI : IsInvolution zH := IsInvolution.subtype hz hzH
  have hnotSup : ¬ TwoRankAtLeastTwo (↑(CH ⊔ ZH)) := by
    simpa [ZH] using
      (not_twoRankAtLeastTwo_sup_odd_involution CH hCHodd hzHI hzNormCH)
  rw [hsup] at hnotSup
  intro hRank
  let f : H →* (⊤ : Subgroup H) :=
    { toFun := fun x => ⟨x, trivial⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    exact congrArg Subtype.val hxy
  exact hnotSup (hRank.map_of_injective f hf)

/-- The exact operational `Z*` factorization needed to apply Lemma 3.11 to
`H = C_X(K) ⟨z⟩` in the second branch of Proposition 7.4. -/
public theorem theorem4b_lemma311_source_factorization
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (d : Theorem4bSixD M)
    (hCnot : ¬ Subgroup.centralizer d.data.invertedSet ≤ M) :
    let K : Set X := d.data.invertedSet
    let C : Subgroup X := Subgroup.centralizer K
    let H : Subgroup X := C ⊔ Subgroup.zpowers d.data.z
    let zH : H := ⟨d.data.z, by
      exact (show Subgroup.zpowers d.data.z ≤ H from le_sup_right)
        (Subgroup.mem_zpowers d.data.z)⟩
    pPrimeCore 2 H ⊔ Subgroup.centralizer ({zH} : Set H) = ⊤ := by
  classical
  dsimp only
  let K : Set X := d.data.invertedSet
  let C : Subgroup X := Subgroup.centralizer K
  let H : Subgroup X := C ⊔ Subgroup.zpowers d.data.z
  have hzH : d.data.z ∈ H :=
    (show Subgroup.zpowers d.data.z ≤ H from le_sup_right)
      (Subgroup.mem_zpowers d.data.z)
  have hCnorm : C ≤ Subgroup.normalizer K := by
    have hforward : ∀ {a n : X}, a ∈ C → n ∈ K →
        a * n * a⁻¹ ∈ K := by
      intro a n ha hn
      have hcomm : n * a = a * n :=
        (Subgroup.mem_centralizer_iff.mp ha) n hn
      have heq : a * n * a⁻¹ = n := by
        rw [← hcomm]
        simp
      rwa [heq]
    intro a ha
    change ∀ n : X, n ∈ K ↔ a * n * a⁻¹ ∈ K
    intro n
    constructor
    · exact hforward ha
    · intro hn
      have hback := hforward (C.inv_mem ha) hn
      have heq : a⁻¹ * (a * n * a⁻¹) * (a⁻¹)⁻¹ = n := by group
      rwa [heq] at hback
  have hzNormK : d.data.z ∈ Subgroup.normalizer K := by
    have hforward : ∀ {x : X}, x ∈ K →
        d.data.z * x * d.data.z⁻¹ ∈ K := by
      intro x hx
      have hx' := (d.data.mem_invertedSet_iff x).mp hx
      apply (d.data.mem_invertedSet_iff _).mpr
      constructor
      · rw [hx'.2]
        exact d.data.W.inv_mem hx'.1
      · calc
          d.data.z * (d.data.z * x * d.data.z⁻¹) * d.data.z⁻¹ = x := by
            rw [d.data.hz.inv_eq_self]
            have hz2 : d.data.z * d.data.z = 1 := by
              simpa [pow_two] using d.data.hz.sq_eq_one
            calc
              d.data.z * (d.data.z * x * d.data.z) * d.data.z =
                  (d.data.z * d.data.z) * x *
                    (d.data.z * d.data.z) := by group
              _ = x := by rw [hz2]; simp
          _ = (d.data.z * x * d.data.z⁻¹)⁻¹ := by rw [hx'.2]; simp
    change ∀ x : X, x ∈ K ↔
      d.data.z * x * d.data.z⁻¹ ∈ K
    intro x
    constructor
    · exact hforward
    · intro hx
      have hback := hforward hx
      have heq : d.data.z * (d.data.z * x * d.data.z⁻¹) *
          d.data.z⁻¹ = x := by
        rw [d.data.hz.inv_eq_self]
        have hz2 : d.data.z * d.data.z = 1 := by
          simpa [pow_two] using d.data.hz.sq_eq_one
        calc
          d.data.z * (d.data.z * x * d.data.z) * d.data.z =
              (d.data.z * d.data.z) * x *
                (d.data.z * d.data.z) := by group
          _ = x := by rw [hz2]; simp
      rwa [heq] at hback
  have hHnorm : H ≤ Subgroup.normalizer K := by
    apply sup_le hCnorm
    rw [Subgroup.zpowers_le]
    exact hzNormK
  have hzNotC : d.data.z ∉ C := by
    intro hzC
    have hzCentW : d.data.z ∈
        Subgroup.centralizer (d.data.W : Set X) := by
      rw [← d.data.closure_invertedSet_eq]
      rw [Subgroup.centralizer_closure]
      exact hzC
    have hWleCent : d.data.W ≤
        Subgroup.centralizer (Subgroup.zpowers d.data.z : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      intro w hw
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact Subgroup.mem_centralizer_iff.mp hzCentW w hw
    have hbot : ⁅d.data.W, Subgroup.zpowers d.data.z⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWleCent
    exact d.data.hWne (d.data.hcomm.symm.trans hbot)
  have h2rank : ¬ TwoRankAtLeastTwo H :=
    source_apply_no_two_rank hM C H K d.data.z rfl rfl hzH d.data.hzM
      d.data.hz hHnorm hzNotC (by simpa [C, K] using hCnot)
  let zH : H := ⟨d.data.z, hzH⟩
  exact PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
    h2rank (IsInvolution.subtype d.data.hz hzH)

/-- Bridge the checked general Lemma 3.11 output on the `H`-orbit of the
base coset to the exact source-sized Proposition 7.4 package. -/
public theorem theorem4b_lemma311_output_of_source
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (d : Theorem4bSixD M)
    (hCnot : ¬ Subgroup.centralizer d.data.invertedSet ≤ M) :
    Theorem4bLemma311Output d
      (Subgroup.centralizer d.data.invertedSet ⊔
        Subgroup.zpowers d.data.z) := by
  classical
  let K : Set X := d.data.invertedSet
  let C : Subgroup X := Subgroup.centralizer K
  let H : Subgroup X := C ⊔ Subgroup.zpowers d.data.z
  let alpha : conjugateCosetSpace M := theorem4bSection7Base
  let OmegaH := MulAction.orbit H alpha
  let alphaH : OmegaH := ⟨alpha, MulAction.mem_orbit_self alpha⟩
  have hzHmem : d.data.z ∈ H :=
    (show Subgroup.zpowers d.data.z ≤ H from le_sup_right)
      (Subgroup.mem_zpowers d.data.z)
  let zH : H := ⟨d.data.z, hzHmem⟩
  let YH : Subgroup H := M.comap H.subtype
  letI : MulAction H OmegaH := inferInstance
  letI : MulAction.IsPretransitive H OmegaH := inferInstance
  have hYstab : MulAction.stabilizer H alphaH = YH := by
    ext h
    constructor
    · intro hh
      change (h : X) ∈ M
      have hfix : h • alphaH = alphaH :=
        MulAction.mem_stabilizer_iff.mp hh
      have hfixX : (h : X) • alpha = alpha := congrArg Subtype.val hfix
      rw [← baseCoset_stabilizer M]
      exact MulAction.mem_stabilizer_iff.mpr hfixX
    · intro hh
      apply MulAction.mem_stabilizer_iff.mpr
      apply Subtype.ext
      have hmem : (h : X) ∈ MulAction.stabilizer X alpha := by
        dsimp [alpha]
        rw [baseCoset_stabilizer]
        exact hh
      exact MulAction.mem_stabilizer_iff.mp hmem
  have hYproper : YH ≠ ⊤ := by
    intro htop
    apply hCnot
    intro c hc
    have hcH : c ∈ H := (show C ≤ H from le_sup_left) hc
    let cH : H := ⟨c, hcH⟩
    have hcY : cH ∈ YH := by
      rw [htop]
      trivial
    exact hcY
  have hzY : zH ∈ YH := d.data.hzM
  have hzHI : IsInvolution zH := IsInvolution.subtype d.data.hz hzHmem
  have hcentH : Subgroup.centralizer ({zH} : Set H) ≤ YH := by
    intro c hc
    change (c : X) ∈ M
    apply hM.centralizer_le d.data.hzM d.data.hz
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hfactorH : pPrimeCore 2 H ⊔
      Subgroup.centralizer ({zH} : Set H) = ⊤ := by
    simpa [K, C, H, zH] using
      theorem4b_lemma311_source_factorization hM d hCnot
  have hrec :=
    lemma_3_11 YH zH alphaH hYstab hYproper hzY hzHI
      hcentH hfactorH
  rcases hrec with
    ⟨RH, GammaH, hGammaH, hPrimeH, _hcyclicH, _hinvH,
      hzNormH, hzGammaH, hPointH, hSwapH⟩
  obtain ⟨r, hrPrime, hrOdd, hRpH, hGammaHCard⟩ := hPrimeH
  let R : Subgroup X := RH.map H.subtype
  let Gamma : Set (conjugateCosetSpace M) :=
    (fun w : OmegaH => (w : conjugateCosetSpace M)) '' GammaH
  have hRleH : R ≤ H := by
    dsimp [R]
    exact Subgroup.map_subtype_le RH
  have hGammaCard : Nat.card Gamma = Nat.card GammaH := by
    calc
      Nat.card Gamma = Gamma.ncard := Nat.card_coe_set_eq Gamma
      _ = GammaH.ncard :=
        Set.ncard_image_of_injective _ Subtype.val_injective
      _ = Nat.card GammaH := (Nat.card_coe_set_eq GammaH).symm
  have hGammaOrbit : Gamma = MulAction.orbit R alpha := by
    ext beta
    constructor
    · rintro ⟨betaH, hbetaH, rfl⟩
      rw [hGammaH] at hbetaH
      rcases MulAction.mem_orbit_iff.mp hbetaH with ⟨qH, hqH⟩
      let q : R := ⟨(qH : X), ⟨qH, qH.property, rfl⟩⟩
      refine MulAction.mem_orbit_iff.mpr ⟨q, ?_⟩
      exact congrArg Subtype.val hqH
    · intro hbeta
      rcases MulAction.mem_orbit_iff.mp hbeta with ⟨q, hq⟩
      rcases Subgroup.mem_map.mp q.property with ⟨qH, hqHR, hqEq⟩
      have hqEqX : (q : X) = (qH : X) := by simpa using hqEq.symm
      have hqHX : (qH : X) • alpha = beta := by
        have hqX : (q : X) • alpha = beta := hq
        rwa [hqEqX] at hqX
      have hbetaOrbitH : beta ∈ MulAction.orbit H alpha := by
        rw [MulAction.mem_orbit_iff]
        exact ⟨qH, hqHX⟩
      let betaH : OmegaH := ⟨beta, hbetaOrbitH⟩
      have hbetaH : betaH ∈ GammaH := by
        rw [hGammaH]
        let qRH : RH := ⟨qH, hqHR⟩
        exact MulAction.mem_orbit_iff.mpr ⟨qRH, by
          apply Subtype.ext
          exact hqHX⟩
      exact ⟨betaH, hbetaH, rfl⟩
  have hRp : IsPGroup r R := by
    simpa [R] using hRpH.map H.subtype
  have hzNormR : d.data.z ∈ Subgroup.normalizer (R : Set X) := by
    have hzMap : d.data.z ∈
        (Subgroup.normalizer (RH : Set H)).map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hzNormH
    exact (Subgroup.le_normalizer_map (H := RH) H.subtype) hzMap
  have hzGamma : ∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma → d.data.z • beta ∈ Gamma := by
    intro beta hbeta
    rcases hbeta with ⟨betaH, hbetaH, rfl⟩
    have hzbetaH : zH • betaH ∈ GammaH := hzGammaH betaH hbetaH
    exact ⟨zH • betaH, hzbetaH, rfl⟩
  have hPoint : ∀ {beta gamma : conjugateCosetSpace M},
      beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
      ∀ x : X, x ∈ H → x • beta = beta → x • gamma = gamma →
        ∀ delta, delta ∈ Gamma → x • delta = delta := by
    intro beta gamma hbeta hgamma hne x hxH hxbeta hxgamma delta hdelta
    rcases hbeta with ⟨betaH, hbetaH, rfl⟩
    rcases hgamma with ⟨gammaH, hgammaH, rfl⟩
    rcases hdelta with ⟨deltaH, hdeltaH, rfl⟩
    let xH : H := ⟨x, hxH⟩
    have hxbetaH : xH • betaH = betaH := by
      apply Subtype.ext
      exact hxbeta
    have hxgammaH : xH • gammaH = gammaH := by
      apply Subtype.ext
      exact hxgamma
    have hneH : betaH ≠ gammaH := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    exact congrArg Subtype.val
      (hPointH hbetaH hgammaH hneH xH hxbetaH hxgammaH deltaH hdeltaH)
  have hSwap : ∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma → beta ≠ alpha →
      ∃ t : X, IsInvolution t ∧ t ∈ H ∧
        t • alpha = beta ∧ t • beta = alpha := by
    intro beta hbeta hbetaNe
    rcases hbeta with ⟨betaH, hbetaH, rfl⟩
    have hbetaNeH : betaH ≠ alphaH := by
      intro heq
      exact hbetaNe (congrArg Subtype.val heq)
    obtain ⟨tH, htH, htAlphaH, htBetaH⟩ :=
      hSwapH betaH hbetaH hbetaNeH
    have htX : IsInvolution (tH : X) :=
      IsInvolution.map_of_injective htH H.subtype H.subtype_injective
    exact ⟨(tH : X), htX, tH.property,
      congrArg Subtype.val htAlphaH, congrArg Subtype.val htBetaH⟩
  have hGammaCard' : Nat.card Gamma = r := by
    rw [hGammaCard]
    exact hGammaHCard
  refine ⟨R, Gamma, ?_, ?_,
    ⟨r, hrPrime, hrOdd, hRp, hGammaCard'⟩,
    hzNormR, hzGamma, hPoint, ?_⟩
  · simpa [H, C, K] using hRleH
  · simpa [alpha] using hGammaOrbit
  · simpa [alpha] using hSwap


/-- The `C_X(K) not≤ M` branch of Proposition 7.4, with the exact
Lemma 3.11/`Z^*(H)` output isolated as `Theorem4bLemma311Output`. -/
public theorem IsStronglyEmbedded.theorem4bProposition74_of_centralizer_not_le
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (_hM : IsStronglyEmbedded M)
    (d : Theorem4bSixD M)
    (_hCnot : ¬ Subgroup.centralizer d.data.invertedSet ≤ M)
    (h311 : Theorem4bLemma311Output d
      (Subgroup.centralizer d.data.invertedSet ⊔
        Subgroup.zpowers d.data.z)) :
    Theorem4bProposition74Data d := by
  let K : Set X := d.data.invertedSet
  let C : Subgroup X := Subgroup.centralizer K
  let H : Subgroup X := C ⊔ Subgroup.zpowers d.data.z
  have h311H : Theorem4bLemma311Output d H := by
    simpa [H, C, K] using h311
  rcases h311H with
    ⟨R, Gamma, hRH, hGammaOrbit, hGammaPrime, hzR, hzGammaForward,
      hPointwise, hSwap⟩
  obtain ⟨r, hrPrime, hrOdd, hrPGroup, hGammaCard⟩ := hGammaPrime
  have hCnorm : C ≤ Subgroup.normalizer K := by
    have hforward : ∀ {a n : X}, a ∈ C → n ∈ K →
        a * n * a⁻¹ ∈ K := by
      intro a n ha hn
      have hcomm : n * a = a * n :=
        (Subgroup.mem_centralizer_iff.mp ha) n hn
      have heq : a * n * a⁻¹ = n := by
        rw [← hcomm]
        simp
      rw [heq]
      exact hn
    intro a ha
    change ∀ n : X, n ∈ K ↔ a * n * a⁻¹ ∈ K
    intro n
    constructor
    · exact hforward ha
    · intro hn
      have hback := hforward (C.inv_mem ha) hn
      have heq : a⁻¹ * (a * n * a⁻¹) * (a⁻¹)⁻¹ = n := by
        group
      rw [heq] at hback
      exact hback
  have hKz : rightConjugateSet K d.data.z = K := by
    simpa [K] using d.data.invertedSet_rightConjugate_z_section7
  have hzNormK : d.data.z ∈ Subgroup.normalizer K := by
    exact mem_normalizer_of_rightConjugateSet_eq_self_of_involution_section7
      K d.data.hz hKz
  have hHNorm : H ≤ Subgroup.normalizer K := by
    apply sup_le hCnorm
    rw [Subgroup.zpowers_le]
    exact hzNormK
  have hCH : C ≤ H := le_sup_left
  have hzH : d.data.z ∈ H := by
    exact (show Subgroup.zpowers d.data.z ≤ H from le_sup_right)
      (Subgroup.mem_zpowers d.data.z)
  have hbase : theorem4bSection7Base (X := X) (M := M) ∈ Gamma := by
    rw [hGammaOrbit]
    exact MulAction.mem_orbit_self _
  have hcard : 1 < Nat.card Gamma := by
    rw [hGammaCard]
    exact hrPrime.one_lt
  have hGammaK : Gamma ⊆ d.data.kFixedPoints := by
    intro beta hbeta
    rw [hGammaOrbit] at hbeta
    rcases MulAction.mem_orbit_iff.mp hbeta with ⟨q, hq⟩
    apply (d.data.mem_kFixedPoints_iff beta).mpr
    intro k hk
    have hqNorm : (q : X) ∈ Subgroup.normalizer K :=
      hHNorm (hRH q.property)
    have hqInvNorm : (q : X)⁻¹ ∈ Subgroup.normalizer K :=
      (Subgroup.normalizer K).inv_mem hqNorm
    change ∀ n : X, n ∈ K ↔
      (q : X)⁻¹ * n * ((q : X)⁻¹)⁻¹ ∈ K at hqInvNorm
    have hkq : (q : X)⁻¹ * k * (q : X) ∈ K := by
      simpa using (hqInvNorm k).mp hk
    have hKbase : ∀ {a : X}, a ∈ K →
        a • theorem4bSection7Base (X := X) (M := M) =
          theorem4bSection7Base (X := X) (M := M) := by
      intro a ha
      apply MulAction.mem_stabilizer_iff.mp
      rw [baseCoset_stabilizer]
      exact d.data.hWM ((d.data.mem_invertedSet_iff a).mp ha).1
    have hqX : (q : X) • theorem4bSection7Base = beta := hq
    calc
      k • beta = k • ((q : X) • theorem4bSection7Base) := by rw [hqX]
      _ = (k * (q : X)) • theorem4bSection7Base := by rw [smul_smul]
      _ = ((q : X) * ((q : X)⁻¹ * k * (q : X))) •
          theorem4bSection7Base := by congr 1 <;> group
      _ = (q : X) • (((q : X)⁻¹ * k * (q : X)) •
          theorem4bSection7Base) := by rw [smul_smul]
      _ = (q : X) • theorem4bSection7Base := by rw [hKbase hkq]
      _ = beta := hqX
  have hzGamma : ∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma ↔ d.data.z • beta ∈ Gamma := by
    intro beta
    constructor
    · exact hzGammaForward beta
    · intro hbeta
      have htwice := hzGammaForward (d.data.z • beta) hbeta
      have hsq : d.data.z * d.data.z = 1 := by
        simpa [pow_two] using d.data.hz.sq_eq_one
      have hzz : d.data.z • (d.data.z • beta) = beta := by
        rw [← mul_smul, hsq, one_smul]
      simpa [hzz] using htwice
  have hpair : ∀ {beta gamma : conjugateCosetSpace M},
      beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
        theorem4bSection7PairCentralizer K beta gamma ≤ M := by
    intro beta gamma hbeta hgamma hne x hx
    have hxH : x ∈ H := hCH hx.1.1
    have hxbase : x • theorem4bSection7Base =
        theorem4bSection7Base :=
      hPointwise hbeta hgamma hne x hxH
        (MulAction.mem_stabilizer_iff.mp hx.1.2)
        (MulAction.mem_stabilizer_iff.mp hx.2)
        _ hbase
    rw [← baseCoset_stabilizer M]
    exact hxbase
  refine ⟨Gamma, hGammaK, hbase, hcard, hzGamma, ?_, ?_⟩
  · intro beta gamma hbeta hgamma hne
    exact hpair hbeta hgamma hne
  · intro beta hbeta hbetaNe
    obtain ⟨t, ht, htH, htBase, htBeta⟩ :=
      hSwap beta hbeta hbetaNe
    let u : X := rightConjugateElem t d.data.z
    have huH : u ∈ H := by
      exact H.mul_mem (H.mul_mem (H.inv_mem hzH) htH) hzH
    have huNorm : u ∈ Subgroup.normalizer K := hHNorm huH
    have hKu : rightConjugateSet K u = K :=
      rightConjugateSet_eq_self_of_mem_normalizer_section7 K huNorm
    let E : Subgroup X := theorem4bSection7E M d.data.z beta
    have hKleE : K ≤ E := by
      intro k hk
      have hkBeta : k ∈ MulAction.stabilizer X beta :=
        MulAction.mem_stabilizer_iff.mpr
          (((d.data.mem_kFixedPoints_iff beta).mp (hGammaK hbeta)) k hk)
      have hzbetaGamma : d.data.z • beta ∈ Gamma :=
        hzGammaForward beta hbeta
      have hkZbeta : k ∈ MulAction.stabilizer X (d.data.z • beta) :=
        MulAction.mem_stabilizer_iff.mpr
          (((d.data.mem_kFixedPoints_iff (d.data.z • beta)).mp
            (hGammaK hzbetaGamma)) k hk)
      have hkM : k ∈ M := d.data.hWM
        ((d.data.mem_invertedSet_iff k).mp hk).1
      exact ⟨⟨hkM, hkBeta⟩, hkZbeta⟩
    have hpairE : theorem4bSection7PairCentralizer K
        theorem4bSection7Base beta ≤ E := by
      intro x hx
      have hxH : x ∈ H := hCH hx.1.1
      have hbaseNe : theorem4bSection7Base (X := X) (M := M) ≠ beta :=
        hbetaNe.symm
      have hxbase : x • theorem4bSection7Base = theorem4bSection7Base :=
        hPointwise hbase hbeta hbaseNe x hxH
          (MulAction.mem_stabilizer_iff.mp hx.1.2)
          (MulAction.mem_stabilizer_iff.mp hx.2)
          _ hbase
      have hxM : x ∈ M := by
        rw [← baseCoset_stabilizer M]
        exact hxbase
      have hzbetaGamma : d.data.z • beta ∈ Gamma :=
        hzGammaForward beta hbeta
      have hxZbeta : x • (d.data.z • beta) = d.data.z • beta :=
        hPointwise hbase hbeta hbaseNe x hxH
          (MulAction.mem_stabilizer_iff.mp hx.1.2)
          (MulAction.mem_stabilizer_iff.mp hx.2)
          _ hzbetaGamma
      exact ⟨⟨hxM, hx.2⟩, MulAction.mem_stabilizer_iff.mpr hxZbeta⟩
    have hpairU : theorem4bSection7PairCentralizer
        (rightConjugateSet d.data.invertedSet u)
        theorem4bSection7Base beta ≤ E := by
      simpa [K, hKu, E] using hpairE
    have hKsubU : rightConjugateSet d.data.invertedSet u ⊆ E := by
      simpa [K, hKu, E] using hKleE
    have hg : ∃ g : X,
        g • (d.data.z • beta) = theorem4bSection7Base ∧
          g • beta ∈ Gamma := by
      have hzbetaOrbit : d.data.z • beta ∈
          MulAction.orbit R theorem4bSection7Base := by
        rw [← hGammaOrbit]
        exact hzGammaForward beta hbeta
      rcases MulAction.mem_orbit_iff.mp hzbetaOrbit with ⟨q, hq⟩
      have hbetaOrbit : beta ∈ MulAction.orbit R theorem4bSection7Base := by
        rw [← hGammaOrbit]
        exact hbeta
      let g : X := (q⁻¹ : R)
      refine ⟨g, ?_, ?_⟩
      · have hqInv : q⁻¹ • (d.data.z • beta) = theorem4bSection7Base := by
          rw [← hq]
          simp
        change ((q⁻¹ : R) : X) • (d.data.z • beta) = theorem4bSection7Base at hqInv
        simpa [g, Subgroup.coe_inv] using hqInv
      · have hqBetaOrbit := MulAction.mem_orbit_of_mem_orbit q⁻¹ hbetaOrbit
        rw [hGammaOrbit]
        change ((q⁻¹ : R) : X) • beta ∈ MulAction.orbit R theorem4bSection7Base at hqBetaOrbit
        simpa [g, Subgroup.coe_inv] using hqBetaOrbit
    rcases hg with ⟨g, hgFirst, hgBeta⟩
    refine ⟨t, ht, htBase, ?_, ?_, g, hgFirst, hgBeta⟩
    · exact hKsubU
    · exact hpairU

/-- Proposition 7.4 assembled from its two source branches.  The arguments
`hswap` and `h311` are the exact Lemma 7.3 and Lemma 3.11 source outputs; no
Proposition 7.4 or theta conclusion is assumed. -/
public theorem IsStronglyEmbedded.theorem4bProposition74
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixD M)
    (hswap : ∀ {beta : conjugateCosetSpace M} {P : Subgroup X},
      beta ∈ d.data.kFixedPoints →
      beta ≠ theorem4bSection7Base →
      theorem4bIsSylowSubgroupOf d.data.p P
        (theorem4bSection7E M d.data.z beta) →
      d.data.z ∈ Subgroup.normalizer (P : Set X) →
      ∃ t : X,
        IsInvolution t ∧
        t ∈ Subgroup.normalizer (P : Set X) ∧
        t • theorem4bSection7Base = beta)
    (h311 : ¬ Subgroup.centralizer d.data.invertedSet ≤ M →
      Theorem4bLemma311Output d
        (Subgroup.centralizer d.data.invertedSet ⊔
          Subgroup.zpowers d.data.z)) :
    Theorem4bProposition74Data d := by
  by_cases hC : Subgroup.centralizer d.data.invertedSet ≤ M
  · exact hM.theorem4bProposition74_of_centralizer_le d hC hswap
  · exact hM.theorem4bProposition74_of_centralizer_not_le d hC (h311 hC)

/-- Proposition 7.4 with its Lemma 7.3 input discharged.  The only remaining
source input is the exact Lemma 3.11 orbit package in the second branch. -/
public theorem IsStronglyEmbedded.theorem4bProposition74_of_lemma311
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (d : Theorem4bSixD M) :
    Theorem4bProposition74Data d := by
  apply hM.theorem4bProposition74 d ?_
    (theorem4b_lemma311_output_of_source hM d)
  intro beta P hbetaK hbetaNe hPsyl hzP
  obtain ⟨t, ht, htNorm, htBase, _htBeta⟩ :=
    hM.theorem4b_lemma73_exists_swap_normalizing
      hT2 d hbetaK hbetaNe hPsyl hzP
  exact ⟨t, ht, htNorm, htBase⟩

/-- A nonbase point of `Gamma` minimizing the order of its two-point theta
core. -/
public theorem exists_minimal_nonbase_theta
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) (Gamma : Set (conjugateCosetSpace M))
    (hbase : theorem4bSection7Base ∈ Gamma)
    (hcard : 1 < Nat.card Gamma) :
    ∃ beta : conjugateCosetSpace M,
      beta ∈ Gamma ∧ beta ≠ theorem4bSection7Base ∧
      ∀ gamma : conjugateCosetSpace M,
        gamma ∈ Gamma → gamma ≠ theorem4bSection7Base →
        Nat.card (corollary64Theta d.p
          (theorem4bSection7D M beta)) ≤
          Nat.card (corollary64Theta d.p
            (theorem4bSection7D M gamma)) := by
  classical
  have hnonbase : ∃ beta : conjugateCosetSpace M,
      beta ∈ Gamma ∧ beta ≠ theorem4bSection7Base := by
    by_contra h
    push Not at h
    have hcardOne : Nat.card Gamma = 1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨theorem4bSection7Base, hbase⟩, ?_⟩
      intro beta
      apply Subtype.ext
      exact h beta.1 beta.2
    omega
  let S : Set (conjugateCosetSpace M) :=
    {beta | beta ∈ Gamma ∧ beta ≠ theorem4bSection7Base}
  letI : Fintype S := Fintype.ofFinite S
  have hSuniv : (Finset.univ : Finset S).Nonempty := by
    rcases hnonbase with ⟨beta, hbeta, hne⟩
    exact ⟨⟨beta, hbeta, hne⟩, by simp⟩
  rcases Finset.exists_min_image (Finset.univ : Finset S)
      (fun beta : S => Nat.card (corollary64Theta d.p
        (theorem4bSection7D M beta.1))) hSuniv with
    ⟨beta, _hbetaUniv, hbetaMin⟩
  refine ⟨beta.1, beta.2.1, beta.2.2, ?_⟩
  intro gamma hgamma hgammaNe
  exact hbetaMin ⟨gamma, hgamma, hgammaNe⟩ (by simp)

/-- Proposition 7.4 plus the minimal choice supplies exactly the three theta
comparisons used in Proposition 7.2. -/
public theorem IsStronglyEmbedded.theorem4b_proposition72_theta_chain_of_prop74
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (d : Theorem4bSixD M)
    (h74 : Theorem4bProposition74Data d) :
    ∃ beta : conjugateCosetSpace M,
      beta ∈ d.data.kFixedPoints ∧
      beta ≠ theorem4bSection7Base ∧
      corollary64Theta d.data.p (theorem4bSection7F d.data.z beta) ≤
        corollary64Theta d.data.p (theorem4bSection7E M d.data.z beta) ∧
      corollary64Theta d.data.p (theorem4bSection7E M d.data.z beta) ≤
        corollary64Theta d.data.p (theorem4bSection7D M beta) ∧
      Nat.card (corollary64Theta d.data.p
          (theorem4bSection7D M beta)) ≤
        Nat.card (corollary64Theta d.data.p
          (theorem4bSection7F d.data.z beta)) := by
  rcases h74 with ⟨Gamma, hGammaK, hbase, hGammaCard, hzGamma,
    hpair, hlocal⟩
  obtain ⟨beta, hbetaGamma, hbetaNe, hminimal⟩ :=
    exists_minimal_nonbase_theta d.data Gamma hbase hGammaCard
  have hbetaK : beta ∈ d.data.kFixedPoints := hGammaK hbetaGamma
  obtain ⟨t, ht, htBase, hK1E, hpairK1E, g, hgzbeta, hgbetaGamma⟩ :=
    hlocal hbetaGamma hbetaNe
  have hzBase : d.data.z •
      (theorem4bSection7Base (X := X) (M := M)) =
      theorem4bSection7Base (X := X) (M := M) := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact d.data.hzM
  have hzMoves : d.data.z • beta ≠ beta := by
    intro hzBeta
    exact hbetaNe ((hM.involution_fixed_coset_unique d.data.hz).unique
      hzBeta hzBase)
  have hzBetaGamma : d.data.z • beta ∈ Gamma :=
    (hzGamma beta).mp hbetaGamma
  have hpairFB :
      theorem4bSection7PairCentralizer d.data.invertedSet beta
        (d.data.z • beta) ≤ M :=
    hpair hbetaGamma hzBetaGamma (fun h => hzMoves h.symm)
  have hCFW : subgroupCentralizerIn
      (theorem4bSection7F d.data.z beta) d.data.W ≤ M := by
    intro x hx
    have hxCK : x ∈ Subgroup.centralizer d.data.invertedSet := by
      have hxCW : x ∈ Subgroup.centralizer (d.data.W : Set X) := hx.2
      rw [← d.data.closure_invertedSet_eq] at hxCW
      simpa [Subgroup.centralizer_closure] using hxCW
    apply hpairFB
    exact ⟨⟨hxCK, hx.1.1⟩, hx.1.2⟩
  have hFE := hM.theorem4b_lemma75 d.data hbetaK hCFW
  have hcent : theorem4bSection7D M beta ⊓
      Subgroup.centralizer
        (rightConjugateSet d.data.invertedSet
          (rightConjugateElem t d.data.z)) ≤
      theorem4bSection7E M d.data.z beta := by
    intro x hx
    apply hpairK1E
    exact ⟨⟨hx.2, by simpa [theorem4bSection7Base,
      baseCoset_stabilizer] using hx.1.1⟩, hx.1.2⟩
  have hED := hM.theorem4b_lemma76 d.data hbetaNe t hK1E hcent
  let beta1 : conjugateCosetSpace M := g • beta
  have hbeta1Gamma : beta1 ∈ Gamma := by
    simpa [beta1] using hgbetaGamma
  have hbeta1Ne : beta1 ≠ theorem4bSection7Base := by
    intro hbeta1Base
    have hEq : beta = d.data.z • beta := by
      apply smul_left_cancel g
      exact hbeta1Base.trans hgzbeta.symm
    exact hzMoves hEq.symm
  have hcard := theorem4b_lemma77_of_minimal d.data.p Gamma
    hminimal hbeta1Gamma hbeta1Ne (by rfl) hgzbeta
  exact ⟨beta, hbetaK, hbetaNe, hFE, hED, hcard⟩

/-- Proposition 7.2 assembled from the source-facing Proposition 7.4 package
and the checked Lemmas 7.5--7.7. -/
public theorem IsStronglyEmbedded.theorem4b_proposition72_of_prop74
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    (h74 : Theorem4bProposition74Data d) :
    Theorem4bProposition72 d.data := by
  apply hM.theorem4b_proposition72_of_exists_theta_chain
    hX d.data hrank hT2 hinduction
  simpa [theorem4bSection7Base] using
    hM.theorem4b_proposition72_theta_chain_of_prop74 d h74

/-- Proposition 7.2 with Proposition 7.4, Lemma 7.3, and Lemma 3.11 fully
discharged. -/
public theorem IsStronglyEmbedded.theorem4b_proposition72
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    Theorem4bProposition72 d.data := by
  apply hM.theorem4b_proposition72_of_prop74 hX d hrank hT2 hinduction
  exact hM.theorem4bProposition74_of_lemma311 hT2 d

end CFSG.BenderSuzuki

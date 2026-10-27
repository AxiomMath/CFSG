module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary64
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.TBS.TBS
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 7: the Thompson--Bender signalizer step

This file proves the group-theoretic core of Lemma 7.6 in
`docs/cfsg-vol4.tex`.  In the intended application `D` is a two-point
stabilizer of odd order, `E ≤ D`, and `W₁` is a `p`-subgroup satisfying
`W₁ C_D(W₁) ≤ E`.  A Sylow `p`-subgroup of that product supplies the
centralizer hypothesis of the Thompson--Bender signalizer lemma, yielding
`theta(E) ≤ theta(D)`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

universe u

/-- Every finite solvable group is `p`-constrained.  This is the exact
constraint input needed when the Thompson--Bender signalizer lemma is applied
inside the odd-order two-point stabilizer in Lemma 7.6. -/
public theorem theorem4b_pConstrainedGroup_of_solvable
    {G : Type u} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (p : ℕ) [Fact p.Prime] :
    PConstrainedGroup (G := G) p := by
  classical
  intro Q _hQp hQeq
  let M : Subgroup G := pPrimeCore p G
  letI : M.Normal := by
    dsimp [M]
    infer_instance
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hQmap : Q.map q = pCore p (G ⧸ M) := by
    calc
      Q.map q = ⊥ ⊔ Q.map q := by simp
      _ = M.map q ⊔ Q.map q := by simp [M, q]
      _ = (M ⊔ Q).map q := (Subgroup.map_sup M Q q).symm
      _ = (Op_p'p p G).map q := by rw [hQeq]
      _ = pCore p (G ⧸ M) := by
        simpa [Op_p'p, M, q] using
          (Subgroup.map_comap_eq_self_of_surjective
            (f := QuotientGroup.mk' (pPrimeCore p G))
            (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
            (H := pCore p (G ⧸ pPrimeCore p G)))
  intro x hx
  have hqxcent : q x ∈ Subgroup.centralizer (Q.map q : Set (G ⧸ M)) := by
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨a, ha, rfl⟩
    exact congrArg q (hx a ha)
  have hqxcore : q x ∈ pCore p (G ⧸ M) := by
    letI : Group.IsSolvable G := hsolv
    have hcoreQ : pPrimeCore p (G ⧸ M) = ⊥ := by
      simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
    have hsolvQ : Group.IsSolvable (G ⧸ M) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective M)
    have hcent :=
      centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot
        (G := G ⧸ M) hsolvQ (p := p) hcoreQ
    have hqxcent' : q x ∈
        Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M)) := by
      rw [← hQmap]
      exact hqxcent
    simpa [M, q] using hcent hqxcent'
  simpa [Op_p'p, M, q] using hqxcore

/-- An element of order `p` centralizing a Sylow `p`-subgroup belongs to that
Sylow subgroup. -/
public theorem theorem4b_order_p_mem_sylow_of_mem_centralizer
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {x : G}
    (hxcent : x ∈ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hxorder : orderOf x = p) :
    x ∈ (P : Subgroup G) := by
  let Z : Subgroup G := Subgroup.zpowers x
  have hZp : IsPGroup p Z := by
    refine IsPGroup.of_card (p := p) (G := Z) (n := 1) ?_
    simp [Z, Nat.card_zpowers, hxorder]
  have hZnormP : Z ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    simpa [Z] using
      (Subgroup.zpowers_le.mpr
        (centralizer_le_normalizer (P : Subgroup G) hxcent))
  have hsupP : IsPGroup p ((P : Subgroup G) ⊔ Z : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' P.isPGroup' hZp hZnormP
  have hsupEq : (P : Subgroup G) ⊔ Z = (P : Subgroup G) :=
    P.is_maximal' hsupP le_sup_left
  have hxZ : x ∈ Z := by simp [Z]
  have hxSup : x ∈ ((P : Subgroup G) ⊔ Z : Subgroup G) :=
    (show Z ≤ (P : Subgroup G) ⊔ Z from le_sup_right) hxZ
  rwa [hsupEq] at hxSup

/-- Ambient normalization of a subgroup transports to normalization of its
pullback to an ambient subgroup. -/
public theorem theorem4b_subgroupOf_le_normalizer_of_map_le_normalizer
    {X : Type u} [Group X] {D T : Subgroup X} {A : Subgroup D}
    (hA : A.map D.subtype ≤ Subgroup.normalizer (T : Set X)) :
    A ≤ Subgroup.normalizer ((T.subgroupOf D) : Set D) := by
  intro a ha
  have haMap : (a : X) ∈ A.map D.subtype :=
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have haNorm : (a : X) ∈ Subgroup.normalizer (T : Set X) := hA haMap
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxT : (x : X) ∈ T := by
      change (x : X) ∈ T at hx
      exact hx
    have hconjT := (Subgroup.mem_normalizer_iff.mp haNorm (x : X)).mp hxT
    change ((a * x * a⁻¹ : D) : X) ∈ T
    simpa using hconjT
  · intro hx
    have hxConjT : (a : X) * (x : X) * (a : X)⁻¹ ∈ T := by
      change ((a * x * a⁻¹ : D) : X) ∈ T at hx
      exact hx
    have hxT := (Subgroup.mem_normalizer_iff.mp haNorm (x : X)).mpr hxConjT
    change (x : X) ∈ T
    exact hxT

/-- The successive characteristic cores defining `theta(E)` are normalized
by `E`. -/
public theorem theorem4b_section7_theta_le_normalizer
    {X : Type u} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (E : Subgroup X) :
    E ≤ Subgroup.normalizer (corollary64Theta p E : Set X) := by
  let O : Subgroup X := corollary64OddCore E
  let T : Subgroup X := corollary64Theta p E
  haveI : (twoPrimeCore E).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := E))
  have hNormENormO : Subgroup.normalizer (E : Set X) ≤
      Subgroup.normalizer (O : Set X) := by
    simpa [O, corollary64OddCore] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := E) (K := twoPrimeCore E))
  have hNormONormT : Subgroup.normalizer (O : Set X) ≤
      Subgroup.normalizer (T : Set X) := by
    simpa [T, corollary64Theta] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := O) (K := pPrimeCore p O))
  exact Subgroup.le_normalizer.trans (hNormENormO.trans hNormONormT)

/-- If a set and its centralizer lie in `E`, then the subgroup it generates
and the centralizer of that generated subgroup lie in `E`.  This is the
closure step converting `(7C)` into `W₁ C_D(W₁) ≤ E`. -/
public theorem theorem4b_closure_sup_centralizer_le
    {G : Type u} [Group G] {K : Set G} {E : Subgroup G}
    (hKE : K ⊆ E)
    (hcent : Subgroup.centralizer K ≤ E) :
    Subgroup.closure K ⊔
      Subgroup.centralizer (Subgroup.closure K : Set G) ≤ E := by
  apply sup_le
  · rw [Subgroup.closure_le]
    exact hKE
  · simpa [Subgroup.centralizer_closure] using hcent

/-- Lemma 7.6, in the exact subgroup form consumed after `(7C)`.

Here `W` is the subgroup `W₁ ≤ D`, and the last hypothesis is the source
containment `W₁ C_D(W₁) ≤ E`, with a subgroup product represented by `⊔`.
Since `D` has odd order, `O₂'(D) = D`, so the source auxiliary group
`D₁ = W₁ O₂'(D)` is simply `D`.  The proof constructs the required Sylow
subgroup, verifies the Thompson--Bender centralizer and coprimality hypotheses,
and concludes `theta(E) ≤ theta(D)`. -/
public theorem theorem4b_lemma76_of_pgroup_centralizer_le_E
    {X : Type u} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {D E : Subgroup X}
    (hpodd : p ≠ 2)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (W : Subgroup D)
    (hWp : IsPGroup p W)
    (hHE : W ⊔ Subgroup.centralizer (W : Set D) ≤ E.subgroupOf D) :
    corollary64Theta p E ≤ corollary64Theta p D := by
  classical
  let OE : Subgroup X := corollary64OddCore E
  let ThetaE : Subgroup X := corollary64Theta p E
  have hOE : OE ≤ E := by
    simpa [OE, corollary64OddCore] using
      (Subgroup.map_subtype_le (twoPrimeCore E))
  have hThetaEOE : ThetaE ≤ OE := by
    simpa [ThetaE, OE, corollary64Theta] using
      (Subgroup.map_subtype_le (pPrimeCore p OE))
  have hThetaED : ThetaE ≤ D := hThetaEOE.trans (hOE.trans hED)
  let K : Subgroup D := ThetaE.subgroupOf D
  let H : Subgroup D := W ⊔ Subgroup.centralizer (W : Set D)
  have hWH : W ≤ H := by exact le_sup_left
  let WH : Subgroup H := W.subgroupOf H
  have hWHp : IsPGroup p WH :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWH).symm
  obtain ⟨R, hWHR⟩ := hWHp.exists_le_sylow
  let A : Subgroup D := (R : Subgroup H).map H.subtype
  have hWR : W ≤ A := by
    intro w hw
    let wH : H := ⟨w, hWH hw⟩
    apply Subgroup.mem_map.mpr
    refine ⟨wH, ?_, rfl⟩
    exact hWHR (by
      change (w : D) ∈ W
      exact hw)
  have hAp : IsPGroup p A := by
    exact R.isPGroup'.map H.subtype
  have hcentral :
      ∀ x : D,
        x ∈ Subgroup.centralizer (A : Set D) →
          orderOf x = p → x ∈ A := by
    intro x hxcent hxorder
    have hxWcent : x ∈ Subgroup.centralizer (W : Set D) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      apply Subgroup.mem_centralizer_iff.mp hxcent w
      exact hWR hw
    have hxH : x ∈ H := by
      exact (show Subgroup.centralizer (W : Set D) ≤ H from le_sup_right) hxWcent
    let xH : H := ⟨x, hxH⟩
    have hxHcent : xH ∈ Subgroup.centralizer ((R : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      apply Subgroup.mem_centralizer_iff.mp hxcent (y : D)
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hxorderH : orderOf xH = p := by
      simpa [xH, Subgroup.orderOf_coe] using hxorder
    have hxR : xH ∈ (R : Subgroup H) :=
      theorem4b_order_p_mem_sylow_of_mem_centralizer R hxHcent hxorderH
    exact Subgroup.mem_map.mpr ⟨xH, hxR, rfl⟩
  have hHmap : H.map D.subtype ≤
      Subgroup.normalizer (ThetaE : Set X) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyH, rfl⟩
    have hyEsub : y ∈ E.subgroupOf D := hHE (by simpa [H] using hyH)
    have hyE : ((y : D) : X) ∈ E := by
      exact hyEsub
    exact theorem4b_section7_theta_le_normalizer E hyE
  have hHnorm : H ≤ Subgroup.normalizer (K : Set D) := by
    simpa [K, ThetaE] using
      (theorem4b_subgroupOf_le_normalizer_of_map_le_normalizer hHmap)
  have hAnorm : A ≤ Subgroup.normalizer (K : Set D) := by
    exact (Subgroup.map_subtype_le (R : Subgroup H)).trans hHnorm
  have hThetaCard : Nat.card ThetaE = Nat.card (pPrimeCore p OE) := by
    simpa [ThetaE, OE, corollary64Theta] using
      (Subgroup.card_map_of_injective
        (K := pPrimeCore p OE) (f := OE.subtype) OE.subtype_injective)
  have hThetaCop : Nat.Coprime p (Nat.card ThetaE) := by
    rw [hThetaCard]
    exact pPrimeCore_coprime_card (p := p) (G := OE)
  have hKCard : Nat.card K = Nat.card ThetaE := by
    simpa [K] using
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hThetaED).toEquiv)
  obtain ⟨n, hACard⟩ := hAp.exists_card_eq
  have hKACop : Nat.Coprime (Nat.card K) (Nat.card A) := by
    rw [hKCard, hACard]
    exact hThetaCop.symm.pow_right n
  have hKinfA : K ⊓ A = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hKACop)
  have hsolvD : Group.IsSolvable D := odd_order_theorem D hDodd
  have hconstrained : PConstrainedGroup (G := D) p :=
    theorem4b_pConstrainedGroup_of_solvable hsolvD p
  have hKcore : K ≤ pPrimeCore p D :=
    thompson_bender_signalizer_lemma hpodd hconstrained hAp hcentral
      hAnorm hKinfA
  have hmap : K.map D.subtype ≤ (pPrimeCore p D).map D.subtype :=
    Subgroup.map_mono hKcore
  have hKmap : K.map D.subtype = ThetaE := by
    simp [K, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hThetaED]
  have hOtop : twoPrimeCore D = ⊤ := by
    apply top_unique
    change (⊤ : Subgroup D) ≤ pPrimeCore 2 D
    exact le_sSup ⟨inferInstance, by simpa using hDodd.coprime_two_left⟩
  have hOddCoreD : corollary64OddCore D = D := by
    dsimp [corollary64OddCore]
    rw [hOtop]
    simpa [MonoidHom.range_eq_map] using
      (Subgroup.range_subtype (H := D))
  rw [hKmap] at hmap
  change ThetaE ≤ corollary64Theta p D
  rw [corollary64Theta, hOddCoreD]
  exact hmap

end CFSG.BenderSuzuki

module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremA
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.Solvable
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer

namespace CFSG
end CFSG
open CFSG

/-!
# Thompson's minimal-counterexample data for Theorem D

This module pins the exact induction hypothesis and data used in the proof of
Glauberman Theorem D (`refs/glauberman-p-stable.tex` L1972–L1989).  The source
invokes "the method of Thompson, as in [ThompsonNormal] pp. 43--44" to obtain,
in a minimal counterexample `G` with `¬ NormalPComplement p G` and
`NormalPComplement p (N_G(Z(J(S))))`:

* `C_G(O_p(G)) ≤ O_p(G)`;
* `G` is solvable;
* for some prime `q ≠ p`, the Sylow `q`-subgroups of `G` are Abelian and `p`
  and `q` are the only prime divisors of `|G|`.

The weakest reusable induction hypothesis is the ordinary "no smaller
counterexample" clause for the backward direction of Theorem D: every finite
group of strictly smaller cardinality whose `Z(J(Sylow p))`-normalizer has a
normal `p`-complement itself has a normal `p`-complement.  The full implication
from that hypothesis to the data above is Thompson's cited method; no
repository theorem supplies it (see
`/tmp/thompson-method-minimal-report.md`).  This file therefore records the
exact statement, the public data predicate, and the transfer/conversion
helpers that the reduction does and would use.
-/

open scoped Pointwise

namespace CFSG.Glauberman

universe u

/-! ## The explicit data and the minimal-counterexample induction hypothesis -/

/-- The exact data supplied by Thompson's method in a minimal counterexample to
the backward direction of Theorem D ([6], proof of Theorem D, tex
L1974–L1983): `C_G(O_p(G)) ⊆ O_p(G)`, `G` is solvable, and for some prime
`q ≠ p` the Sylow `q`-subgroups are Abelian while `p` and `q` are the only prime
divisors of `|G|`. -/
public def ThompsonMethodData (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [Finite G] : Prop :=
  Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) ≤ pCore p G ∧
    IsSolvable G ∧
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧
      (∀ T : Sylow q G, IsMulCommutative (T : Subgroup G)) ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p ∨ r = q

/-- The normalizer of `Z(J(S))` in `G`, as a subgroup of `G`. -/
public abbrev ZJNormalizer (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] (S : Sylow p G) : Subgroup G :=
  Subgroup.normalizer ((ZJ (G := G) S.toSubgroup : Subgroup G) : Set G)

/-- The normal-`p`-complement condition at `N_G(Z(J(S)))`. -/
public def NormalPComplementZJ (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] (S : Sylow p G) : Prop :=
  NormalPComplement p (↥(ZJNormalizer p S))

/-- The weakest reusable induction hypothesis for Theorem D's backward
direction: every finite group of strictly smaller cardinality that has a
normal `p`-complement in `N_H(Z(J(T)))` for a Sylow `p`-subgroup `T` already
has a normal `p`-complement.  This is the "minimal counterexample" clause used
in the source's induction on `|G|`. -/
public def MinimalCounterexampleHypothesis (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    ∀ T : Sylow p H,
      NormalPComplementZJ p T → NormalPComplement p H

/-- The exact Thompson-method core: from the minimal-counterexample induction
hypothesis, failure of a normal `p`-complement, and a normal `p`-complement in
`N_G(Z(J(S)))`, the Thompson data follow.  This is the precise external step
cited as "[ThompsonNormal] pp. 43--44"; it is not supplied by any in-repository
transfer or normal-complement theorem (see the report). -/
public def ThompsonMethodCore (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [Finite G] : Prop :=
  MinimalCounterexampleHypothesis p G →
    ∀ S : Sylow p G, NormalPComplementZJ p S →
      ¬ NormalPComplement p G → ThompsonMethodData p G

/-! ## Normal-`p`-complement conversions (local copies, avoiding `ZJTheorem`) -/

/-- Convert Glauberman's `O_{p',p}(G) = G` convention to the transfer-API
existential convention. -/
private theorem hasNormalPComplement_of_normalPComplement
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (h : NormalPComplement p G) : HasNormalPComplement p G := by
  classical
  let Q := G ⧸ pPrimeCore p G
  let q : G →* Q := QuotientGroup.mk' (pPrimeCore p G)
  have hOp : Op_p'p p G = ⊤ := normalPComplement_eq_top h
  have hcomap : (pCore p Q).comap q = ⊤ := by
    simpa [Op_p'p, Q, q] using hOp
  have hpcore : pCore p Q = ⊤ := by
    calc
      pCore p Q = ((pCore p Q).comap q).map q := by
        rw [Subgroup.map_comap_eq_self_of_surjective (f := q)
          (QuotientGroup.mk'_surjective (pPrimeCore p G)) (pCore p Q)]
      _ = (⊤ : Subgroup G).map q := by rw [hcomap]
      _ = ⊤ := by
        exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective (pPrimeCore p G))
  have hqtop : IsPGroup p (⊤ : Subgroup Q) := by
    rw [← hpcore]
    exact pCore_isPGroup (G := Q) (p := p)
  have hQp : IsPGroup p Q := hqtop.of_equiv Subgroup.topEquiv
  exact ⟨pPrimeCore p G, inferInstance, pPrimeCore_coprime_card (G := G) (p := p), hQp⟩

/-- Convert the transfer-API existential convention back to Glauberman's
`O_{p',p}(G) = G` convention. -/
private theorem normalPComplement_of_hasNormalPComplement
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (h : HasNormalPComplement p G) : NormalPComplement p G := by
  let Q := G ⧸ pPrimeCore p G
  have hq : IsPGroup p Q :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) G h
  have hqtop : IsPGroup p (⊤ : Subgroup Q) := hq.to_subgroup ⊤
  have hpcore : pCore p Q = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, hqtop⟩
  apply normalPComplement_of_eq_top
  simp [Op_p'p, Q, hpcore]

/-- A normal `p`-complement descends to every subgroup. -/
private theorem normalPComplement_of_subgroup
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (h : NormalPComplement p G) :
    NormalPComplement p (↥H) := by
  have hG : HasNormalPComplement p G := hasNormalPComplement_of_normalPComplement h
  have hTop : HasNormalPComplement p (↥(⊤ : Subgroup G)) :=
    hasNormalPComplement_of_equiv (G := G) (G' := ↥(⊤ : Subgroup G)) p
      (Subgroup.topEquiv (G := G)).symm hG
  have hH : HasNormalPComplement p (↥H) :=
    hasNormalPComplement_of_le (G := G) (p := p) (K := H) (L := ⊤) le_top hTop
  exact normalPComplement_of_hasNormalPComplement hH

/-! ## Minimal-counterexample transfer through `O_{p'}(G)` -/

/-- The quotient map by the `p'`-core is injective on a Sylow `p`-subgroup. -/
private theorem injective_quotient_pPrimeCore_on_sylow
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) :
    Function.Injective
      ((QuotientGroup.mk' (pPrimeCore p G)).comp S.toSubgroup.subtype) := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hS : IsPGroup p (↥(S.toSubgroup : Subgroup G)) := S.isPGroup'
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (↥(S.toSubgroup : Subgroup G))) (Nat.card M) := by
    rw [hn]
    exact ((pPrimeCore_coprime_card (G := G) (p := p)).symm.pow_right n).symm
  have hdisj : Disjoint (S.toSubgroup : Subgroup G) M :=
    Subgroup.disjoint_of_coprime_natCard hcop
  intro a b h
  apply Subtype.ext
  have hq : q (a : G) = q (b : G) := by simpa [q] using h
  have hdiv : (a : G) / (b : G) ∈ M := (QuotientGroup.eq_iff_div_mem (N := M)).mp hq
  have hSmem : (a : G) / (b : G) ∈ (S.toSubgroup : Subgroup G) := by
    exact S.toSubgroup.div_mem a.property b.property
  have hbot : (a : G) / (b : G) ∈ (⊥ : Subgroup G) := by
    have : (a : G) / (b : G) ∈ (S.toSubgroup : Subgroup G) ⊓ M := ⟨hSmem, hdiv⟩
    simpa [hdisj.eq_bot] using this
  have hdiv1 : (a : G) / (b : G) = 1 := Subgroup.mem_bot.mp hbot
  calc
    (a : G) = (a : G) / (b : G) * (b : G) := by rw [div_eq_mul_inv]; group
    _ = (b : G) := by rw [hdiv1]; simp

/-- The characteristic `Z(J(·))` functor commutes with the quotient by the
`p'`-core on a Sylow `p`-subgroup. -/
private theorem ZJ_map_quotient_pPrimeCore
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) :
    let M : Subgroup G := pPrimeCore p G
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    (ZJ (G := G) S.toSubgroup).map q =
      ZJ (G := G ⧸ M)
        ((S.mapSurjective (QuotientGroup.mk'_surjective M)) : Subgroup (G ⧸ M)) := by
  classical
  intro M q
  let Sbar : Sylow p (G ⧸ M) := S.mapSurjective (QuotientGroup.mk'_surjective M)
  let φ : S →* G ⧸ M := q.comp S.toSubgroup.subtype
  have hφinj : Function.Injective φ := by
    change Function.Injective
      ((QuotientGroup.mk' (pPrimeCore p G)).comp S.toSubgroup.subtype)
    exact injective_quotient_pPrimeCore_on_sylow (G := G) (p := p) S
  let e0 : ↥(⊤ : Subgroup S) ≃* ↥((⊤ : Subgroup S).map φ) :=
    Subgroup.equivMapOfInjective (⊤ : Subgroup S) φ hφinj
  have hSbar : (Sbar : Subgroup (G ⧸ M)) = S.toSubgroup.map q :=
    Sylow.coe_mapSurjective (G := G) (G' := G ⧸ M) (f := q)
      (QuotientGroup.mk'_surjective M) S
  have hTopMap : (⊤ : Subgroup S).map φ = S.toSubgroup.map q := by
    ext y
    constructor
    · rintro ⟨x, _hx, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x.1, x.property, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨s, hs⟩, by simp, rfl⟩
  let e1 : ↥((⊤ : Subgroup S).map φ) ≃* ↥(S.toSubgroup.map q) :=
    MulEquiv.subgroupCongr hTopMap
  let e : S ≃* ↥(Sbar : Subgroup (G ⧸ M)) :=
    (Subgroup.topEquiv (G := S)).symm.trans
      (e0.trans (e1.trans (MulEquiv.subgroupCongr hSbar.symm)))
  have hφe : ∀ x : S, φ x = (Sbar : Subgroup (G ⧸ M)).subtype (e x) := by
    intro x
    rfl
  have hcenter :
      (thompsonCenter (G := S) (⊤ : Subgroup S)).map e.toMonoidHom =
        thompsonCenter (G := ↥(Sbar : Subgroup (G ⧸ M)))
          (⊤ : Subgroup (↥(Sbar : Subgroup (G ⧸ M)))) :=
    thompsonCenter_top_map_mulEquiv (G := S) (H := ↥(Sbar : Subgroup (G ⧸ M))) e
  let K : Subgroup S := thompsonCenter (G := S) (⊤ : Subgroup S)
  change (thompsonCenter (G := G) S.toSubgroup).map q =
      ZJ (G := G ⧸ M) (Sbar : Subgroup (G ⧸ M))
  calc
    (thompsonCenter (G := G) S.toSubgroup).map q
        = ((thompsonCenter (G := S) (⊤ : Subgroup S)).map S.toSubgroup.subtype).map q := by
            rw [thompsonCenter_top_map_subtype (G := G) (S := S.toSubgroup)]
    _ = (thompsonCenter (G := S) (⊤ : Subgroup S)).map φ := by
            rw [Subgroup.map_map (K := K) (g := q) (f := S.toSubgroup.subtype)]
    _ = ((thompsonCenter (G := S) (⊤ : Subgroup S)).map e.toMonoidHom).map
          (Sbar : Subgroup (G ⧸ M)).subtype := by
            rw [Subgroup.map_map (K := K) (g := (Sbar : Subgroup (G ⧸ M)).subtype)
              (f := e.toMonoidHom)]
            apply congrArg (fun f : S →* G ⧸ M => K.map f)
            ext x
            exact hφe x
    _ = (thompsonCenter (G := ↥(Sbar : Subgroup (G ⧸ M)))
            (⊤ : Subgroup (↥(Sbar : Subgroup (G ⧸ M))))).map
          (Sbar : Subgroup (G ⧸ M)).subtype := by rw [hcenter]
    _ = ZJ (G := G ⧸ M) (Sbar : Subgroup (G ⧸ M)) := by
            simpa [ZJ] using
              (thompsonCenter_top_map_subtype (G := G ⧸ M) (S := (Sbar : Subgroup (G ⧸ M))))

/-- A normal `p`-complement of `N_G(Z(J(S)))` descends to the `Z(J(·))`
normalizer of the image Sylow subgroup in the `O_{p'}(G)`-quotient. -/
private theorem normalPComplementZJ_of_quotient_pPrimeCore
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hN : NormalPComplementZJ p S) :
    let M : Subgroup G := pPrimeCore p G
    let Sbar : Sylow p (G ⧸ M) :=
      S.mapSurjective (QuotientGroup.mk'_surjective M)
    NormalPComplementZJ p Sbar := by
  classical
  intro M Sbar
  let Q := G ⧸ M
  let q : G →* Q := QuotientGroup.mk' M
  let Z : Subgroup G := ZJ (G := G) S.toSubgroup
  let N : Subgroup G := Subgroup.normalizer (Z : Set G)
  let Zbar : Subgroup Q := ZJ (G := Q) (Sbar : Subgroup Q)
  let Nbar : Subgroup Q := Subgroup.normalizer (Zbar : Set Q)
  have hZmap' : Z.map q = Zbar := by
    simpa [Z, Zbar, Sbar] using ZJ_map_quotient_pPrimeCore (G := G) (p := p) S
  haveI : Fact (IsPGroup p (↥Z)) :=
    ⟨IsPGroup.to_le S.isPGroup' (thompsonCenter_le S.toSubgroup)⟩
  have hMnormal : M.Normal := by
    simpa [M] using (pPrimeCore_normal (p := p) (G := G))
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hnorm :
      Subgroup.normalizer (Z.map q) = (Subgroup.normalizer (Z : Set G)).map q :=
    normalizer_map_quotient_eq_map_normalizer (G := G) p Z M hMnormal hMcop
  have hNbar_eq : Nbar = N.map q := by
    change Subgroup.normalizer (Zbar : Set Q) = N.map q
    rw [← hZmap']
    exact hnorm
  have hNhas : HasNormalPComplement p (↥N) :=
    hasNormalPComplement_of_normalPComplement hN
  let K : Subgroup N := M.subgroupOf N
  haveI : K.Normal := by
    dsimp [K]
    infer_instance
  have hquotN : HasNormalPComplement p (N ⧸ K) :=
    BenderSuzuki.External.hkt_hasNormalPComplement_to_quotient (H := N) (N := K) hNhas
  let qN : N →* Nbar :=
    (q.comp N.subtype).codRestrict Nbar (by
      intro x
      rw [hNbar_eq]
      exact Subgroup.mem_map_of_mem q x.property)
  have hqNsurj : Function.Surjective qN := by
    intro y
    have hy : (y : Q) ∈ Nbar := y.property
    have hy' : (y : Q) ∈ N.map q := by
      rw [← hNbar_eq]
      exact hy
    rcases Subgroup.mem_map.mp hy' with ⟨n, hn, hEq⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    apply Subtype.ext
    exact hEq
  have hker : qN.ker = K := by
    ext x
    simp [qN, K]
    change QuotientGroup.mk (x : G) = 1 ↔ (x : G) ∈ M
    rw [QuotientGroup.eq_one_iff]
  have hRangetop : qN.range = ⊤ := MonoidHom.range_eq_top.mpr hqNsurj
  let e : N ⧸ K ≃* Nbar :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange qN).trans
        ((MulEquiv.subgroupCongr hRangetop).trans (Subgroup.topEquiv (G := Nbar))))
  have hNbarHas : HasNormalPComplement p Nbar :=
    hasNormalPComplement_of_equiv (G := N ⧸ K) (G' := Nbar) p e hquotN
  exact normalPComplement_of_hasNormalPComplement hNbarHas

/-- In a minimal counterexample to the backward direction of Theorem D, the
`p'`-core is trivial: if `O_{p'}(G)` were nontrivial, the quotient would be a
smaller group whose `Z(J(·))`-normalizer has a normal `p`-complement, so the
minimality hypothesis would make the quotient (and hence `G`) `p`-nilpotent. -/
private theorem pPrimeCore_eq_bot_of_minimalCounterexample
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hmin : MinimalCounterexampleHypothesis p G)
    (hnot : ¬ NormalPComplement p G) (hN : NormalPComplementZJ p S) :
    pPrimeCore p G = ⊥ := by
  classical
  by_contra hMne
  let M : Subgroup G := pPrimeCore p G
  let Q := G ⧸ M
  let Sbar : Sylow p Q := S.mapSurjective (QuotientGroup.mk'_surjective M)
  have hNbar : NormalPComplementZJ p Sbar :=
    normalPComplementZJ_of_quotient_pPrimeCore (G := G) (p := p) S hN
  have hMnormal : M.Normal := by
    simpa [M] using (pPrimeCore_normal (p := p) (G := G))
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hMne_top : M ≠ ⊤ := by
    intro htop
    have hGp' : Nat.Coprime p (Nat.card G) := by
      have hcardM : Nat.card M = Nat.card G := by simp [htop]
      rw [← hcardM]
      exact pPrimeCore_coprime_card (G := G) (p := p)
    have hsub : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
      QuotientGroup.subsingleton_quotient_top
    have hP : IsPGroup p (G ⧸ (⊤ : Subgroup G)) := by
      intro x
      exact ⟨0, Subsingleton.elim _ _⟩
    have hcomp : HasNormalPComplement p G :=
      ⟨⊤, inferInstance, by simpa [htop] using hGp', by simpa using hP⟩
    exact hnot (normalPComplement_of_hasNormalPComplement hcomp)
  have hindex_pos : 0 < M.index := by
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := M))
  have hindex_dvd : M.index ∣ Nat.card G := M.index_dvd_card
  have hindex_ne_card : M.index ≠ Nat.card G := by
    intro hEq
    have hprod : M.index * Nat.card M = Nat.card G := M.index_mul_card
    have h : M.index * Nat.card M = M.index * 1 := by simpa [hEq] using hprod
    have hcardM : Nat.card M = 1 := Nat.mul_left_cancel hindex_pos h
    exact hMne (Subgroup.card_eq_one.mp hcardM)
  have hindex_lt : M.index < Nat.card G :=
    Nat.lt_of_le_of_ne (Nat.le_of_dvd (Nat.card_pos (α := G)) hindex_dvd) hindex_ne_card
  have hcardlt : Nat.card Q < Nat.card G := by
    rw [← Subgroup.index_eq_card]
    exact hindex_lt
  have hQcomp : NormalPComplement p Q :=
    hmin Q hcardlt Sbar hNbar
  have hcompG : HasNormalPComplement p G :=
    hasNormalPComplement_of_quotient (G := G) (p := p) (N := M) hMcop
      (hasNormalPComplement_of_normalPComplement hQcomp)
  exact hnot (normalPComplement_of_hasNormalPComplement hcompG)

/-- The public bridge statement: in a minimal counterexample to the backward
direction of Theorem D, the explicit `ThompsonMethodData` conclusion follows
from the exact Thompson-method core.  The reducible `O_{p'}(G) = 1` transfer is
proved here; the remaining core is recorded verbatim in
`ThompsonMethodCore` and in `/tmp/thompson-method-minimal-report.md`. -/
public theorem thompsonMethod_minimalCounterexample_data
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {G : Type u} [Group G] [Finite G] (S : Sylow p G)
    (hmin : MinimalCounterexampleHypothesis p G)
    (hnot : ¬ NormalPComplement p G) (hN : NormalPComplementZJ p S)
    (hcore : ThompsonMethodCore p G) :
    ThompsonMethodData p G := by
  have _hOdd : p ≠ 2 := hpodd
  have _hOp' : pPrimeCore p G = ⊥ :=
    pPrimeCore_eq_bot_of_minimalCounterexample S hmin hnot hN
  exact hcore hmin S hN hnot

end CFSG.Glauberman

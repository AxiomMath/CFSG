module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970) Statement 1.7 — shared `F*(A)`-subnormal helpers

This module contains the structural F*-absorption and residual facts used by
`Bender1970_17i.lean`, `Bender1970_17ii.lean`, and `Bender1970_17iii.lean`.
Every reusable declaration is `public` so later Section-1/2 files can import
this module without importing the wrapper `GorensteinWalter.Section2.Bender1970`.

The route follows the source proof of [1, Satz 1.7] (`refs/bender-abelian-sylow2.tex`
lines 244--293):

1. `E(A) ≤ S` and `Z(F(A)) ≤ S` for a subnormal self-centralizing `S ≤ F*(A)`;
2. for `p ∈ π(F(A))`, a nontrivial central p-subgroup of `F(A)` lies in
   `O_p(S)`, so `C_G(O_p(S)) ≤ N_G(Z_p) = A`;
3. the p-residual machinery needed to apply the Thompson lemma 1.1.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## p-residual helpers (mirrored from `Bender1970_18`)

`Bender1970_18.lean` currently does not build, so the two residual facts
needed below are re-provided here under `fstar_`-prefixed names to avoid a
later name clash with that module's public API. -/

/-- If `H / N` is a `p`-group and `N` is normal in `H`, then `O^p(H) ≤ N`. -/
public theorem fstar_pResidualOf_le_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G]
    (H N : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hNle : N ≤ H)
    (hN : (N.subgroupOf H).Normal)
    (hQ : IsPGroup p (H ⧸ N.subgroupOf H)) :
    pResidualOf H p ≤ N := by
  let : Fact p.Prime := ⟨hp⟩
  rcases (IsPGroup.iff_card.mp hQ) with ⟨n, hn⟩
  have hidx : ∃ n : ℕ, (N.subgroupOf H).index = p ^ n := ⟨n, by
    rw [← hn]
    exact (Subgroup.index_eq_card (N.subgroupOf H)).symm⟩
  have hle := pResidualOf_le_of_normal_index H p (N.subgroupOf H) hN hidx
  simpa [Subgroup.map_subgroupOf_eq_of_le hNle] using hle

/-- `O^p(H)` is characteristic in `H`. -/
public theorem fstar_pResidualOf_subgroupOf_characteristic
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) :
    ((pResidualOf H p).subgroupOf H).Characteristic := by
  classical
  let family : Set (Subgroup H) :=
    {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}
  have hNres : (pResidualOf H p).subgroupOf H = sInf family := by
    unfold pResidualOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective (sInf family)
  rw [hNres]
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  exact pResidual_map_iso (G := H) (H := H) p e

/-- `O^p(H)` is normal in `H`. -/
public instance fstar_pResidualOf_subgroupOf_normal
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) :
    ((pResidualOf H p).subgroupOf H).Normal := by
  have : ((pResidualOf H p).subgroupOf H).Characteristic :=
    fstar_pResidualOf_subgroupOf_characteristic H p
  infer_instance

/-- `H / O^p(H)` is a `p`-group. -/
public theorem fstar_isPGroup_quotient_pResidualOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) :
    IsPGroup p (H ⧸ (pResidualOf H p).subgroupOf H) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have : ((pResidualOf H p).subgroupOf H).Normal := fstar_pResidualOf_subgroupOf_normal H p
  let family : Set (Subgroup H) :=
    {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}
  let N : Subgroup H := sInf family
  have hNres : (pResidualOf H p).subgroupOf H = N := by
    unfold pResidualOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  let ι : Type u := {M : Subgroup H // M ∈ family}
  have : Finite ι := Finite.of_injective (fun M : ι => (M : Subgroup H)) (by
    intro M N h
    exact Subtype.ext h)
  let : Fintype ι := Fintype.ofFinite ι
  have : ∀ M : ι, (M : Subgroup H).Normal := fun M => M.2.1
  let n : ι → ℕ := fun M => Classical.choose M.2.2
  have hn : ∀ M : ι, (M : Subgroup H).index = p ^ n M := fun M =>
    Classical.choose_spec M.2.2
  have hQcard : ∀ M : ι, Nat.card (H ⧸ (M : Subgroup H)) = p ^ n M := by
    intro M
    rw [← hn M, Subgroup.index_eq_card]
  let T : Type u := ∀ M : ι, H ⧸ (M : Subgroup H)
  have hTcard : Nat.card T = p ^ (∑ M, n M) := by
    rw [Nat.card_pi]
    rw [← Finset.prod_pow_eq_pow_sum (s := Finset.univ) (f := n) (a := p)]
    exact Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (by intro M _; exact hQcard M)
  have hT : IsPGroup p T := IsPGroup.of_card hTcard
  let f : H →* T :=
    { toFun := fun h M => QuotientGroup.mk' (M : Subgroup H) h
      map_one' := by
        funext M
        exact rfl
      map_mul' := by intro x y; ext M; rfl }
  have hfker : f.ker = N := by
    ext h
    constructor
    · intro hh
      rw [Subgroup.mem_sInf]
      intro M hM
      have : M.Normal := hM.1
      have hcomp : QuotientGroup.mk' M h = (1 : H ⧸ M) := congrFun hh ⟨M, hM⟩
      exact (QuotientGroup.eq_one_iff (N := M) h).1 hcomp
    · intro hh
      ext M
      have : (M : Subgroup H).Normal := M.2.1
      rw [Subgroup.mem_sInf] at hh
      have hhM : h ∈ (M : Subgroup H) := hh (M : Subgroup H) M.2
      exact (QuotientGroup.eq_one_iff (N := (M : Subgroup H)) h).2
        hhM
  have hNnormal : N.Normal := by
    refine ⟨?_⟩
    intro n hn g
    rw [Subgroup.mem_sInf] at hn ⊢
    intro M hM
    exact hM.1.conj_mem n (hn M hM) g
  have : N.Normal := hNnormal
  let e : H ⧸ N ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq (M := N) (N := f.ker) hfker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hRange : IsPGroup p (f.range : Subgroup T) :=
    hT.to_subgroup (f.range : Subgroup T)
  have hNquot : IsPGroup p (H ⧸ N) := hRange.of_equiv e.symm
  have eRes : (H ⧸ (pResidualOf H p).subgroupOf H) ≃* (H ⧸ N) :=
    QuotientGroup.quotientMulEquivOfEq
      (M := (pResidualOf H p).subgroupOf H) (N := N) hNres
  exact hNquot.of_equiv eRes.symm

/-- Characteristicity is preserved by group isomorphisms. -/
public theorem fstar_characteristic_map_of_mulEquiv
    {G H : Type u} [Group G] [Group H] (e : G ≃* H)
    {K : Subgroup G} (hK : K.Characteristic) :
    (K.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  let α : G ≃* G := (e.trans φ).trans e.symm
  have hα : K.map α.toMonoidHom = K :=
    Subgroup.characteristic_iff_map_eq.mp hK α
  have hα' := congrArg (Subgroup.map e.toMonoidHom) hα
  have htrans : α.trans e = e.trans φ := by
    apply MulEquiv.ext
    intro x
    simp [α]
  have hα'' : K.map (α.trans e).toMonoidHom = K.map e.toMonoidHom := by
    simpa [Subgroup.map_map] using hα'
  simpa [Subgroup.map_map, htrans] using hα''

/-- The `p`-residual of a `p`-residual is itself. -/
public theorem fstar_pResidualOf_idempotent
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) :
    pResidualOf (pResidualOf H p) p = pResidualOf H p := by
  classical
  let R : Subgroup G := pResidualOf H p
  let Q : Subgroup G := pResidualOf R p
  have hRleH : R ≤ H := pResidualOf_le H p
  have hQleR : Q ≤ R := pResidualOf_le R p
  have hQleH : Q ≤ H := hQleR.trans hRleH
  have hQnormH : (Q.subgroupOf H).Normal := by
    let RH : Subgroup (↥H) := R.subgroupOf H
    let K' : Subgroup RH := (Q.subgroupOf H).subgroupOf RH
    let QR : Subgroup (↥R) := Q.subgroupOf R
    let e : RH ≃* R := Subgroup.subgroupOfEquivOfLe hRleH
    have hQRchar : QR.Characteristic := fstar_pResidualOf_subgroupOf_characteristic R p
    have hK'eq : K' = QR.map e.symm.toMonoidHom := by
      ext q
      constructor
      · intro hq
        have hq1 : (q : ↥H) ∈ Q.subgroupOf H := Subgroup.mem_subgroupOf.mp hq
        have hq2 : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq1
        let x : ↥R := ⟨(q : G), hQleR hq2⟩
        refine Subgroup.mem_map.mpr ⟨x, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact hq2
        · ext
          rfl
      · intro hq
        rcases (Subgroup.mem_map).1 hq with ⟨x, hx, rfl⟩
        have hxQ : (x : G) ∈ Q := (Subgroup.mem_subgroupOf).1 hx
        rw [Subgroup.mem_subgroupOf]
        rw [Subgroup.mem_subgroupOf]
        exact hxQ
    have hK'char : K'.Characteristic := hK'eq ▸
      fstar_characteristic_map_of_mulEquiv e.symm hQRchar
    have : K'.Characteristic := hK'char
    have hK'norm : (K'.map RH.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal (H := RH) (K := K')
    have hmap : K'.map RH.subtype = Q.subgroupOf H := by
      have hQRHle : Q.subgroupOf H ≤ RH := Subgroup.subgroupOf_mono H hQleR
      simpa [K'] using (Subgroup.map_subgroupOf_eq_of_le (G := H)
        (H := Q.subgroupOf H) (K := RH) hQRHle)
    exact hmap ▸ hK'norm
  have hQHR : IsPGroup p (H ⧸ R.subgroupOf H) :=
    fstar_isPGroup_quotient_pResidualOf H p hp
  have hQRp : IsPGroup p (R ⧸ Q.subgroupOf R) :=
    fstar_isPGroup_quotient_pResidualOf R p hp
  have hQquot : IsPGroup p (H ⧸ Q.subgroupOf H) := by
    classical
    let : Fact p.Prime := ⟨hp⟩
    rcases (IsPGroup.iff_card.mp hQHR) with ⟨a, ha⟩
    rcases (IsPGroup.iff_card.mp hQRp) with ⟨b, hb⟩
    have hQindex : (Q.subgroupOf H).index =
        (Q.subgroupOf R).index * (R.subgroupOf H).index := by
      have hQHRle : Q.subgroupOf H ≤ R.subgroupOf H := Subgroup.subgroupOf_mono H hQleR
      have hrel := Subgroup.relIndex_mul_index (G := ↥H)
        (H := Q.subgroupOf H) (K := R.subgroupOf H) hQHRle
      have hrel2 : (Q.subgroupOf H).relIndex (R.subgroupOf H) = (Q.subgroupOf R).index := by
        have h := Subgroup.relIndex_subgroupOf (G := G) (H := Q) (K := R) (L := H) hRleH
        simpa [Subgroup.relIndex] using h
      simpa [hrel2, Subgroup.index_eq_card] using hrel.symm
    have hcard : Nat.card (H ⧸ Q.subgroupOf H) = p ^ (a + b) := by
      calc
        Nat.card (H ⧸ Q.subgroupOf H) = (Q.subgroupOf H).index :=
          (Subgroup.index_eq_card (Q.subgroupOf H)).symm
        _ = (Q.subgroupOf R).index * (R.subgroupOf H).index := hQindex
        _ = Nat.card (R ⧸ Q.subgroupOf R) * Nat.card (H ⧸ R.subgroupOf H) := by
          rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
        _ = p ^ b * p ^ a := by rw [hb, ha]
        _ = p ^ (b + a) := by rw [pow_add]
        _ = p ^ (a + b) := by rw [add_comm]
    exact IsPGroup.of_card hcard
  have hResleQ : pResidualOf H p ≤ Q :=
    fstar_pResidualOf_le_of_quotient_isPGroup H Q p hp hQleH hQnormH hQquot
  exact le_antisymm hQleR hResleQ

/-! ## `O_p(F(A))` centralizers -/

/-- `O_p(A) ≤ F(A)`. -/
public theorem fstar_qCoreOf_le_fittingSubgroupOf {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) : qCoreOf A p ≤ fittingSubgroupOf A := by
  let : Fact p.Prime := ⟨hp⟩
  have hle : pCore p (↥A) ≤ fittingSubgroup (↥A) := pCore_le_fitting (G := ↥A) p
  exact Subgroup.map_mono (f := A.subtype) hle

/-- `F(A)` is the join of its `O_q(A)`. -/
public theorem fstar_fittingSubgroupOf_eq_iSup_qCoreOf {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) :
    fittingSubgroupOf A =
      ⨆ q : (Nat.card (↥A)).primeFactors.attach, qCoreOf A q.1.1 := by
  unfold fittingSubgroupOf qCoreOf
  rw [fitting_eq_sup_pCore, Subgroup.map_iSup]

/-- For distinct primes, `O_q(A)` centralizes `O_p(A)`. -/
public theorem fstar_qCoreOf_centralizer_of_ne {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    qCoreOf A q ≤ Subgroup.centralizer ((qCoreOf A p : Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases (Subgroup.mem_map).1 hx with ⟨x₀, hx₀, rfl⟩
  rcases (Subgroup.mem_map).1 hy with ⟨y₀, hy₀, rfl⟩
  have hdisj : Disjoint (pCore q (↥A)) (pCore p (↥A)) :=
    IsPGroup.disjoint_of_ne q p (hne.symm)
      (pCore q (↥A)) (pCore p (↥A))
      (pCore_isPGroup (p := q) (G := ↥A)) (pCore_isPGroup (p := p) (G := ↥A))
  have hcomm₀ : ⁅x₀, y₀⁆ = (1 : ↥A) := by
    have hmem : ⁅x₀, y₀⁆ ∈ ⁅pCore q (↥A), pCore p (↥A)⁆ :=
      Subgroup.commutator_mem_commutator hx₀ hy₀
    have hle : ⁅pCore q (↥A), pCore p (↥A)⁆ ≤
        pCore q (↥A) ⊓ pCore p (↥A) :=
      Subgroup.commutator_le_inf (H₁ := pCore q (↥A)) (H₂ := pCore p (↥A))
    have hinf : (pCore q (↥A) ⊓ pCore p (↥A) : Subgroup (↥A)) = ⊥ := by
      exact hdisj.eq_bot
    have : ⁅x₀, y₀⁆ ∈ (⊥ : Subgroup (↥A)) := by
      rw [← hinf]
      exact hle hmem
    simpa using this
  exact congrArg Subtype.val ((commutatorElement_eq_one_iff_mul_comm.mp hcomm₀).symm)

/-- `O_q(A) ≤ O_q(F(A))`. -/
public theorem fstar_qCoreOf_le_qCoreOf_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (q : ℕ) (hq : q.Prime) :
    qCoreOf A q ≤ qCoreOf (fittingSubgroupOf A) q := by
  let : Fact q.Prime := ⟨hq⟩
  let F : Subgroup G := fittingSubgroupOf A
  let Q : Subgroup G := qCoreOf A q
  have hQF : Q ≤ F := fstar_qCoreOf_le_fittingSubgroupOf A q hq
  have hFleA : F ≤ A := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hQnormF : IsNormalIn Q F := by
    refine ⟨hQF, ?_⟩
    intro f hf x hx
    exact (qCoreOf_normal_in A q).2 f (hFleA hf) x hx
  have hQp : IsPGroup q (Q.subgroupOf F) :=
    (qCoreOf_isPGroup A q).of_equiv (Subgroup.subgroupOfEquivOfLe hQF).symm
  have hQsub : Q.subgroupOf F ≤ pCore q (↥F) := le_sSup ⟨by
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := F) (N := Q)
      (by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          exact hQnormF.2 x hx y hy
        · intro hy
          have hxinv : x⁻¹ ∈ F := F.inv_mem hx
          have h := hQnormF.2 x⁻¹ hxinv (x * y * x⁻¹) hy
          simpa [mul_assoc] using h), hQp⟩
  have hmap := Subgroup.map_mono (f := F.subtype) hQsub
  have hQmap : (Q.subgroupOf F).map F.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQF
  change qCoreOf A q ≤ (pCore q (↥F)).map F.subtype
  simpa [hQmap, Q] using hmap

/-- The center of `O_p(F(A))` centralizes `F(A)`. -/
public theorem fstar_center_qCoreOf_fitting_centralizes_fitting
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    (Subgroup.center (↥(qCoreOf (fittingSubgroupOf A) p))).map
      (qCoreOf (fittingSubgroupOf A) p).subtype ≤
    Subgroup.centralizer ((fittingSubgroupOf A : Subgroup G) : Set G) := by
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  intro z hz
  rcases (Subgroup.mem_map).1 hz with ⟨c, hc, hzc⟩
  have hzP : z ∈ P := by
    rw [← hzc]
    exact (c : ↥P).2
  have hzCentP : z ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcomm : (⟨y, hy⟩ : ↥P) * c = c * (⟨y, hy⟩ : ↥P) :=
      (Subgroup.mem_center_iff.mp hc) ⟨y, hy⟩
    have hz : (c : G) = z := by simpa using hzc
    simpa [hz] using congrArg Subtype.val hcomm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [fstar_fittingSubgroupOf_eq_iSup_qCoreOf A] at hx
  rw [Subgroup.iSup_eq_closure] at hx
  have hgen : ∀ y : G,
      y ∈ ⋃ q : (Nat.card (↥A)).primeFactors.attach, (qCoreOf A q.1.1 : Set G) →
        y * z = z * y := by
    intro y hy
    rcases (Set.mem_iUnion).1 hy with ⟨q, hq⟩
    have hqprime : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hqp : q.1.1 = p
    · have hq' : y ∈ qCoreOf A p := by simpa [hqp] using hq
      have hyP : y ∈ P := (fstar_qCoreOf_le_qCoreOf_fittingSubgroupOf A p hp) hq'
      exact (Subgroup.mem_centralizer_iff.mp hzCentP) y hyP
    · have hqCoreF : qCoreOf A q.1.1 ≤ qCoreOf F q.1.1 :=
        fstar_qCoreOf_le_qCoreOf_fittingSubgroupOf A q.1.1 hqprime
      have hC : qCoreOf F q.1.1 ≤ Subgroup.centralizer (P : Set G) :=
        fstar_qCoreOf_centralizer_of_ne F hp hqprime (by
          intro hpq
          exact hqp hpq.symm)
      have hzY : z * y = y * z :=
        (Subgroup.mem_centralizer_iff.mp (hC (hqCoreF hq))) z hzP
      exact hzY.symm
  refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hx
  · intro y hy
    have hcomm : y * z = z * y := hgen y hy
    calc
      y⁻¹ * z = y⁻¹ * (z * y * y⁻¹) := by group
      _ = y⁻¹ * (y * z * y⁻¹) := by rw [hcomm]
      _ = z * y⁻¹ := by group
  · simpa using (show 1 * z = z * 1 by simp)
  · intro y w _ _ hy' hw'
    calc
      (y * w) * z = y * (w * z) := by group
      _ = y * (z * w) := by rw [hw']
      _ = (y * z) * w := by group
      _ = (z * y) * w := by rw [hy']
      _ = z * (y * w) := by group

/-- If `p` divides `|F(A)|`, then `O_p(F(A))` is nontrivial. -/
public theorem fstar_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    qCoreOf (fittingSubgroupOf A) p ≠ ⊥ := by
  let F : Subgroup G := fittingSubgroupOf A
  let : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent (↥F) := by
    let e : fittingSubgroup (↥A) ≃* ↥F :=
      Subgroup.equivMapOfInjective (fittingSubgroup (↥A)) A.subtype A.subtype_injective
    exact Group.nilpotent_of_mulEquiv e
  let P : Sylow p (↥F) := Classical.choice Sylow.nonempty
  have hPnormal : (P : Subgroup (↥F)).Normal :=
    Group.IsNilpotent.sylow_normal (G := ↥F) inferInstance p P
  have hPp : IsPGroup p (P : Subgroup (↥F)) := P.isPGroup'
  have hPle : (P : Subgroup (↥F)) ≤ pCore p (↥F) := le_sSup ⟨hPnormal, hPp⟩
  have hpdiv : p ∣ Nat.card (↥F) := by
    have hpf : p ∈ (Nat.card (↥F)).primeFactors := by simpa [primesOfOrder] using hpF
    exact Nat.dvd_of_mem_primeFactors hpf
  have hPne : (P : Subgroup (↥F)) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hpdiv
  have hCoreNe : pCore p (↥F) ≠ ⊥ := by
    intro hbot
    exact hPne (le_bot_iff.mp (hPle.trans (le_of_eq hbot)))
  have hmapne : (pCore p (↥F)).map F.subtype ≠ ⊥ := by
    intro hmap
    have hbot : pCore p (↥F) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := pCore p (↥F))
        (f := F.subtype) (hf := F.subtype_injective)).1 hmap
    exact hCoreNe hbot
  simpa [qCoreOf, F] using hmapne

/-- A nontrivial central subgroup of `O_p(F(A))` lies in `O_p(S)`. -/
public theorem fstar_center_qCoreOf_fitting_le_qCoreOf_S
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    (Subgroup.center (↥(qCoreOf (fittingSubgroupOf A) p))).map
      (qCoreOf (fittingSubgroupOf A) p).subtype ≤ qCoreOf S p := by
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let X : Subgroup G := generalizedFittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hZF : Z ≤ Subgroup.centralizer (F : Set G) := by
    simpa [Z, P] using (fstar_center_qCoreOf_fitting_centralizes_fitting A p hp)
  have hZE : Z ≤ Subgroup.centralizer (E : Set G) := by
    have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := F)).1
        (layer_centralizes_fitting A)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hzF : z ∈ F := by
      rcases (Subgroup.mem_map).1 hz with ⟨c, _hc, rfl⟩
      exact (qCoreOf_le F p) (c : ↥P).2
    exact ((Subgroup.mem_centralizer_iff.mp (hEF he)) z hzF).symm
  have hZX : Z ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    change x ∈ F ⊔ E at hx
    rw [Subgroup.sup_eq_closure] at hx
    have hgen : ∀ y : G,
        y ∈ ((F : Set G) ∪ (E : Set G)) → y * z = z * y := by
      intro y hy
      rcases hy with hyF | hyE
      · exact (Subgroup.mem_centralizer_iff.mp (hZF hz)) y hyF
      · exact (Subgroup.mem_centralizer_iff.mp (hZE hz)) y hyE
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hx
    · intro y hy
      have hcomm : y * z = z * y := hgen y hy
      calc
        y⁻¹ * z = y⁻¹ * (z * y * y⁻¹) := by group
        _ = y⁻¹ * (y * z * y⁻¹) := by rw [hcomm]
        _ = z * y⁻¹ := by group
    · simp
    · intro y w _ _ hy' hw'
      calc
        (y * w) * z = y * (w * z) := by group
        _ = y * (z * w) := by rw [hw']
        _ = (y * z) * w := by group
        _ = (z * y) * w := by rw [hy']
        _ = z * (y * w) := by group
  have hZXle : Z ≤ X := by
    intro z hz
    exact (le_sup_left : F ≤ X) (by
      rcases (Subgroup.mem_map).1 hz with ⟨c, _hc, rfl⟩
      exact (qCoreOf_le F p) (c : ↥P).2)
  have hZS : Z ≤ S := by
    intro z hz
    have hzS : z ∈ Subgroup.centralizer (S : Set G) :=
      (Subgroup.centralizer_le (show (S : Set G) ⊆ (X : Set G) from hSF)) (hZX hz)
    exact hCS ⟨hZXle hz, hzS⟩
  have hZcentS : Z ≤ Subgroup.centralizer (S : Set G) :=
    fun z hz => (Subgroup.centralizer_le (show (S : Set G) ⊆ (X : Set G) from hSF)) (hZX hz)
  have hZnormS : IsNormalIn Z S := by
    refine ⟨hZS, ?_⟩
    intro s hs z hz
    have hcomm : s * z = z * s := (Subgroup.mem_centralizer_iff.mp (hZcentS hz)) s hs
    have heq : s * z * s⁻¹ = z := by
      calc
        s * z * s⁻¹ = z * s * s⁻¹ := by rw [hcomm]
        _ = z := by group
    simpa [heq] using hz
  have hZp : IsPGroup p Z := by
    have hPp : IsPGroup p (↥P) := by simpa [P] using (qCoreOf_isPGroup F p)
    have hPtop : IsPGroup p ↥(⊤ : Subgroup (↥P)) :=
      hPp.of_equiv (Subgroup.topEquiv).symm
    have hcP : IsPGroup p (Subgroup.center (↥P)) :=
      IsPGroup.to_le (G := ↥P) (K := (⊤ : Subgroup (↥P))) hPtop le_top
    simpa [Z] using IsPGroup.map hcP P.subtype
  have hZsub : Z.subgroupOf S ≤ pCore p (↥S) := le_sSup ⟨by
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := S) (N := Z)
      (by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          exact hZnormS.2 x hx y hy
        · intro hy
          have hxinv : x⁻¹ ∈ S := S.inv_mem hx
          have h := hZnormS.2 x⁻¹ hxinv (x * y * x⁻¹) hy
          simpa [mul_assoc] using h), by
    exact hZp.of_equiv (Subgroup.subgroupOfEquivOfLe hZS).symm⟩
  have hmap := Subgroup.map_mono (f := S.subtype) hZsub
  have hZmap : (Z.subgroupOf S).map S.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZS
  change Z ≤ qCoreOf S p
  simpa [hZmap, qCoreOf] using hmap

/-- Every element of `H` whose order is coprime to `p` lies in `O^p(H)`. -/
public theorem fstar_mem_pResidualOf_of_order_coprime
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) {x : G} (hx : x ∈ H)
    (hcop : Nat.Coprime p (orderOf x)) : x ∈ pResidualOf H p := by
  rw [pResidualOf]
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_sInf]
  intro N hN
  rcases hN with ⟨hNnormal, n, hn⟩
  let : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (H ⧸ N) := IsPGroup.of_card (n := n) (by
    rw [← hn]
    exact (Subgroup.index_eq_card N).symm)
  let q : H ⧸ N := QuotientGroup.mk' N ⟨x, hx⟩
  have hcopH : Nat.Coprime p (orderOf (⟨x, hx⟩ : H)) := by
    have hord : orderOf (⟨x, hx⟩ : H) = orderOf x :=
      (orderOf_injective H.subtype H.subtype_injective (⟨x, hx⟩ : H)).symm
    rwa [hord]
  have hqcop : (orderOf q).Coprime (orderOf (⟨x, hx⟩ : H)) :=
    hQ.orderOf_coprime hcopH q
  have hqdiv : orderOf q ∣ orderOf (⟨x, hx⟩ : H) :=
    orderOf_map_dvd (QuotientGroup.mk' N) (⟨x, hx⟩)
  have hq1 : q = 1 :=
    (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hqcop dvd_rfl hqdiv))
  exact (QuotientGroup.eq_one_iff (N := N) (x := (⟨x, hx⟩ : H))).1 hq1

/-! ## Component normality and subnormal transport -/

/-- The image of the center under a group isomorphism is the center. -/
private theorem fstar_map_center_eq_center_of_mulEquiv {G H : Type u}
    [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, ?_⟩
    · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
    · exact e.apply_symm_apply x

/-- Quasisimplicity is invariant under a group isomorphism. -/
private theorem fstar_isQuasisimple_mulEquiv
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsQuasisimple G) :
    IsQuasisimple H := by
  have hNontriv : Nontrivial H := by
    let : Nontrivial G := hG.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect H := by
    let : Group.IsPerfect G := (Group.isPerfect_def).2 hG.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.toEquiv.surjective
  have hSimple : IsSimpleGroup (H ⧸ Subgroup.center H) := by
    have he : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
      fstar_map_center_eq_center_of_mulEquiv e
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he)).mp hG.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

/-- Conjugation by an ambient element transports quasisimplicity. -/
public theorem fstar_isQuasisimple_conjugateSubgroup
    {G : Type u} [Group G]
    (E : Subgroup G) (g : G) (hE : IsQuasisimple E) :
    IsQuasisimple (conjugateSubgroup E g) :=
  fstar_isQuasisimple_mulEquiv ((MulAut.conj g).subgroupMap E) hE

/-- Conjugation by an ambient element transports subnormality. -/
public theorem fstar_isSubnormal_conjugateSubgroup
    {G : Type u} [Group G]
    (E : Subgroup G) (g : G) (hE : E.IsSubnormal) :
    (conjugateSubgroup E g).IsSubnormal := by
  simpa [conjugateSubgroup] using hE.map (MulAut.conj g).surjective

/-- A conjugate (by an element of `A`) of a component of `A` is again a
component of `A`. -/
public theorem fstar_isComponentOf_conjugateSubgroup_of_mem
    {G : Type u} [Group G]
    {E A : Subgroup G} (hE : IsComponentOf E A) (a : G) (ha : a ∈ A) :
    IsComponentOf (conjugateSubgroup E a) A := by
  refine ⟨?_, ?_, fstar_isQuasisimple_conjugateSubgroup E a hE.2.2⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨e, he, rfl⟩
    exact A.mul_mem (A.mul_mem ha (hE.1 he)) (A.inv_mem ha)
  · have hsnA : (E.subgroupOf A).IsSubnormal := hE.2.1
    have hconjA : (conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A)).IsSubnormal :=
      fstar_isSubnormal_conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A) hsnA
    have hEq : conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A) =
        (conjugateSubgroup E a).subgroupOf A := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        rcases (Subgroup.mem_map).1 hx with ⟨k, hk, hkx⟩
        exact Subgroup.mem_map.mpr ⟨(k : G), (Subgroup.mem_subgroupOf).1 hk,
          by simpa [conjugateSubgroup] using congrArg Subtype.val hkx⟩
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
        let v : ↥A := ⟨y, hE.1 hy⟩
        refine Subgroup.mem_map.mpr ⟨v, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact hy
        · ext
          simpa [v, conjugateSubgroup] using hxy
    simpa [hEq] using hconjA

/-- The layer `E(A)` is normal in `A`. -/
public theorem fstar_componentLayerOf_isNormalIn {G : Type u} [Group G]
    (A : Subgroup G) : IsNormalIn (componentLayerOf A) A := by
  refine ⟨?_, ?_⟩
  · rw [componentLayerOf]
    exact sSup_le (fun E hE => hE.1)
  · intro a ha e he
    rw [componentLayerOf, sSup_eq_iSup', Subgroup.iSup_eq_closure] at he
    have hgen : ∀ y : G,
        y ∈ ⋃ E : {E : Subgroup G // IsComponentOf E A}, (E.1 : Set G) →
          a * y * a⁻¹ ∈ componentLayerOf A := by
      intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨E, hyE⟩
      exact Subgroup.mem_sSup_of_mem
        (fstar_isComponentOf_conjugateSubgroup_of_mem E.2 a ha)
        (by
          exact Subgroup.mem_map.mpr ⟨y, hyE, by simp [conjugateSubgroup]⟩)
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ he
    · intro x hx
      simpa [mul_assoc] using (componentLayerOf A).inv_mem (hgen x hx)
    · simpa using (componentLayerOf A).one_mem
    · intro x y _hx _hy hx' hy'
      simpa [mul_assoc, mul_left_comm, mul_right_comm] using
        (componentLayerOf A).mul_mem hx' hy'

/-- The generalized Fitting subgroup `F*(A)` is normal in `A`. -/
public theorem fstar_generalizedFittingSubgroupOf_isNormalIn
    {G : Type u} [Group G] (A : Subgroup G) :
    IsNormalIn (generalizedFittingSubgroupOf A) A := by
  have hF : IsNormalIn (fittingSubgroupOf A) A := fittingSubgroupOf_isNormalIn A
  have hE : IsNormalIn (componentLayerOf A) A := fstar_componentLayerOf_isNormalIn A
  refine ⟨?_, ?_⟩
  · exact sup_le hF.1 hE.1
  · intro a ha x hx
    change x ∈ fittingSubgroupOf A ⊔ componentLayerOf A at hx
    rw [Subgroup.sup_eq_closure] at hx
    have hgen : ∀ y : G,
        y ∈ ((fittingSubgroupOf A : Set G) ∪ (componentLayerOf A : Set G)) →
          a * y * a⁻¹ ∈ generalizedFittingSubgroupOf A := by
      intro y hy
      rcases hy with hyF | hyE
      · exact Subgroup.mem_sup_left (hF.2 a ha y hyF)
      · exact Subgroup.mem_sup_right (hE.2 a ha y hyE)
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hx
    · intro y hy
      simpa [mul_assoc] using (generalizedFittingSubgroupOf A).inv_mem (hgen y hy)
    · simpa using (generalizedFittingSubgroupOf A).one_mem
    · intro y z _ _ hy' hz'
      simpa [mul_assoc, mul_left_comm, mul_right_comm] using
        (generalizedFittingSubgroupOf A).mul_mem hy' hz'

/-- Subnormality in `X` plus normality of `X` in `A` gives subnormality in `A`. -/
public theorem fstar_isSubnormal_subgroupOf_of_subnormal_subgroupOf_normal
    {G : Type u} [Group G]
    {S X A : Subgroup G} (hSX : S ≤ X) (hS : (S.subgroupOf X).IsSubnormal)
    (hXA : X ≤ A) (hX : IsNormalIn X A) :
    (S.subgroupOf A).IsSubnormal := by
  let XA : Subgroup (↥A) := X.subgroupOf A
  let SA : Subgroup (↥A) := S.subgroupOf A
  have hXAn : XA.Normal := by
    refine ⟨?_⟩
    intro n hn g
    rw [Subgroup.mem_subgroupOf]
    exact hX.2 (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.mp hn)
  have hXAsn : XA.IsSubnormal := hXAn.isSubnormal
  let e : ↥X ≃* ↥XA := (Subgroup.subgroupOfEquivOfLe hXA).symm
  have hSXmap : ((S.subgroupOf X).map e.toMonoidHom).IsSubnormal :=
    hS.map e.surjective
  have hEqS : (S.subgroupOf X).map e.toMonoidHom = SA.subgroupOf XA := by
    ext x
    constructor
    · intro hx
      rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
      have hyS : (y : G) ∈ S := (Subgroup.mem_subgroupOf).1 hy
      have hxS : (x : G) ∈ S := by
        have hxyA : (e.toMonoidHom y : ↥A) = (x : ↥A) := congrArg Subtype.val hxy
        have hxy' : (e.toMonoidHom y : G) = (x : G) :=
          congrArg (fun z : ↥A => (z : G)) hxyA
        simpa [e] using hxy' ▸ hyS
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf]
      exact hxS
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_subgroupOf] at hx
      refine Subgroup.mem_map.mpr ⟨⟨(x : G), hSX hx⟩, ?_, ?_⟩
      rw [Subgroup.mem_subgroupOf]
      exact hx
      ext
      rfl
  have hSXAsn : (SA.subgroupOf XA).IsSubnormal := by
    exact hEqS ▸ hSXmap
  have hSAmap : (SA.subgroupOf XA).map XA.subtype = SA :=
    Subgroup.map_subgroupOf_eq_of_le (by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_subgroupOf]
      exact hSX hx)
  have hsn := Subgroup.IsSubnormal.trans' (H := SA.subgroupOf XA) (K := XA)
    hSXAsn hXAsn
  simpa [SA, hSAmap] using hsn

/-! ## Self-centralizing subnormal subgroups of `F*(A)` -/

/-- Transport of commutator triviality through `subgroupOf`. -/
public theorem fstar_commutator_subgroupOf_eq_bot_iff_of_le
    {G : Type u} [Group G] {A B H : Subgroup G}
    (hAH : A ≤ H) (hBH : B ≤ H) :
    ⁅A.subgroupOf H, B.subgroupOf H⁆ = ⊥ ↔ ⁅A, B⁆ = ⊥ := by
  constructor
  · intro hbot
    have hmap : (⁅A.subgroupOf H, B.subgroupOf H⁆).map H.subtype = ⊥ := by
      rw [hbot]
      exact Subgroup.map_bot H.subtype
    have hm : ⁅(A.subgroupOf H).map H.subtype, (B.subgroupOf H).map H.subtype⁆ = ⊥ := by
      rw [← Subgroup.map_commutator (H₁ := A.subgroupOf H) (H₂ := B.subgroupOf H)
        (f := H.subtype)]
      exact hmap
    have hA : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
    have hB : (B.subgroupOf H).map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
    simpa [hA, hB] using hm
  · intro hbot
    have hm : (⁅A.subgroupOf H, B.subgroupOf H⁆).map H.subtype = ⊥ := by
      rw [Subgroup.map_commutator (H₁ := A.subgroupOf H) (H₂ := B.subgroupOf H)
        (f := H.subtype)]
      rw [Subgroup.map_subgroupOf_eq_of_le hAH, Subgroup.map_subgroupOf_eq_of_le hBH]
      exact hbot
    exact (Subgroup.map_eq_bot_iff_of_injective (H := ⁅A.subgroupOf H, B.subgroupOf H⁆)
      (f := H.subtype) (hf := H.subtype_injective)).mp hm

/-- A component of `A` is a component of the ambient group `↥A`. -/
public theorem fstar_isComponentOf_subgroupOf_top
    {G : Type u} [Group G]
    {A E : Subgroup G} (hE : IsComponentOf E A) :
    IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) := by
  refine ⟨le_top, ?_, ?_⟩
  · exact Subgroup.IsSubnormal.subgroupOf (K := (⊤ : Subgroup (↥A))) hE.2.1
  · exact fstar_isQuasisimple_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.2

/-- `F*(A) ≤ A`. -/
public theorem fstar_generalizedFittingSubgroupOf_le {G : Type u} [Group G]
    (A : Subgroup G) : generalizedFittingSubgroupOf A ≤ A := by
  rw [generalizedFittingSubgroupOf]
  refine sup_le ?_ ?_
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  · rw [componentLayerOf]
    refine sSup_le ?_
    intro E hE
    exact hE.1

/-- Dichotomy for a component of `A` against a subnormal subgroup of `A`. -/
public theorem fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {A S E : Subgroup G}
    (hSA : S ≤ A) (hS : (S.subgroupOf A).IsSubnormal) (hE : IsComponentOf E A) :
    E ≤ S ∨ ⁅E, S⁆ = ⊥ := by
  let K : Subgroup (↥A) := E.subgroupOf A
  let U : Subgroup (↥A) := S.subgroupOf A
  have hK : IsComponentOf K (⊤ : Subgroup (↥A)) := fstar_isComponentOf_subgroupOf_top hE
  have hU : U.IsSubnormal := hS
  rcases component_le_or_commutator_eq_bot hK hU with hKU | hcomm
  · left
    intro x hx
    have hxK : (⟨x, hE.1 hx⟩ : ↥A) ∈ K := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hxU : (⟨x, hE.1 hx⟩ : ↥A) ∈ U := hKU hxK
    exact (Subgroup.mem_subgroupOf).1 hxU
  · right
    exact (fstar_commutator_subgroupOf_eq_bot_iff_of_le (A := E) (B := S) (H := A)
      hE.1 hSA).1 hcomm

/-- The layer `E(A)` lies in every subnormal self-centralizing `S ≤ F*(A)`. -/
public theorem fstar_componentLayer_le_selfCentralizingSubnormal
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S) :
    componentLayerOf A ≤ S := by
  let X : Subgroup G := generalizedFittingSubgroupOf A
  have hXleA : X ≤ A := fstar_generalizedFittingSubgroupOf_le A
  have hSleA : S ≤ A := hSF.trans hXleA
  have hSsubA : (S.subgroupOf A).IsSubnormal :=
    fstar_isSubnormal_subgroupOf_of_subnormal_subgroupOf_normal hSF hSsub hXleA
      (fstar_generalizedFittingSubgroupOf_isNormalIn A)
  apply sSup_le
  intro E hE
  rcases fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf
    hSleA hSsubA hE with hES | hcomm
  · exact hES
  · have hEX : E ≤ X := by
      exact (le_sSup (s := {E' : Subgroup G | IsComponentOf E' A}) (a := E) hE).trans
        (le_sup_right : componentLayerOf A ≤ generalizedFittingSubgroupOf A)
    have hEC : E ≤ Subgroup.centralizer (S : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := S)).1 hcomm
    intro x hx
    exact hCS ⟨hEX hx, hEC hx⟩

/-- If `z` centralizes two subgroups, it centralizes their join. -/
public theorem fstar_centralizer_of_centralizes_join
    {G : Type u} [Group G] {F E : Subgroup G} {z : G}
    (hzF : z ∈ Subgroup.centralizer (F : Set G))
    (hzE : z ∈ Subgroup.centralizer (E : Set G)) :
    z ∈ Subgroup.centralizer ((F ⊔ E : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyF | hyE
    · exact (Subgroup.mem_centralizer_iff.mp hzF) y hyF
    · exact (Subgroup.mem_centralizer_iff.mp hzE) y hyE
  · intro y hy
    have hcomm : y * z = z * y := by
      rcases hy with hyF | hyE
      · exact (Subgroup.mem_centralizer_iff.mp hzF) y hyF
      · exact (Subgroup.mem_centralizer_iff.mp hzE) y hyE
    calc
      y⁻¹ * z = y⁻¹ * (z * y * y⁻¹) := by group
      _ = y⁻¹ * (y * z * y⁻¹) := by rw [hcomm]
      _ = z * y⁻¹ := by group
  · simp
  · intro x y _hx _hy hx' hy'
    calc
      (x * y) * z = x * (y * z) := by group
      _ = x * (z * y) := by rw [hy']
      _ = (x * z) * y := by group
      _ = (z * x) * y := by rw [hx']
      _ = z * (x * y) := by group

/-- `Z(F(A))` lies in every subnormal self-centralizing `S ≤ F*(A)`. -/
public theorem fstar_centerFitting_le_selfCentralizingSubnormal
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S) :
    (Subgroup.center (↥(fittingSubgroupOf A))).map (fittingSubgroupOf A).subtype ≤ S := by
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let X : Subgroup G := generalizedFittingSubgroupOf A
  intro z hz
  rcases (Subgroup.mem_map).1 hz with ⟨c, hc, hzc⟩
  have hzFmem : z ∈ F := by
    rw [← hzc]
    exact (c : ↥F).2
  have hzX : z ∈ X := (le_sup_left : F ≤ X) hzFmem
  have hzFcent : z ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hcomm : (⟨f, hf⟩ : ↥F) * c = c * (⟨f, hf⟩ : ↥F) :=
      (Subgroup.mem_center_iff.mp hc) ⟨f, hf⟩
    have hz : (c : G) = z := by simpa using hzc
    simpa [hz] using congrArg Subtype.val hcomm
  have hEcentF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := F)).1
      (layer_centralizes_fitting A)
  have hzEcent : z ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.mp (hEcentF he) z hzFmem).symm)
  have hzXcent : z ∈ Subgroup.centralizer (X : Set G) :=
    fstar_centralizer_of_centralizes_join (F := F) (E := E) hzFcent hzEcent
  have hzScent : z ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.centralizer_le (show (S : Set G) ⊆ (X : Set G) from hSF)) hzXcent
  exact hCS ⟨hzX, hzScent⟩

end CFSG.GorensteinWalter

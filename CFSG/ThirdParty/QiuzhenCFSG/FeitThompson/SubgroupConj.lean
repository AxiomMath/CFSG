module

public import Mathlib.Algebra.Group.Subgroup.Actions

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

/-!
# Subgroup conjugation algebra

This file collects algebraic identities for `Subgroup.conjBy` (conjugation of a subgroup by
a group element).  These lemmas are generic — they need only `[Group G]` — and are extracted
from local reproofs in the BG‑section files.

The main identities are:

* `conjBy_mul` / `conjBy_conjBy` – how `conjBy` interacts with multiplication of the conjugating
  element (it is a group anti‑homomorphism);
* `conjBy_one` – conjugation by the identity is trivial;
* `conjBy_inv` – conjugation by `a` and by `a⁻¹` are mutual inverses.
-/

namespace Subgroup

section ConjByAlgebra

variable {G : Type*} [Group G]

/-- Conjugation by `a * b` is the same as conjugation by `b` followed by conjugation by `a`. -/
public theorem conjBy_mul (H : Subgroup G) (a b : G) :
    H.conjBy (a * b) = (H.conjBy b).conjBy a := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨b * y * b⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
    · simp [MulAut.conj_apply, mul_assoc]
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    exact ⟨z, hz, by simp [MulAut.conj_apply, mul_assoc]⟩

/-- Conjugation by `1` is the identity. -/
public theorem conjBy_one (H : Subgroup G) : H.conjBy (1 : G) = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp⟩

/-- Conjugation by `h` then by `g` is conjugation by `h * g`.  (An anti‑homomorphism.) -/
public theorem conjBy_conjBy (H : Subgroup G) (g h : G) :
    (H.conjBy g).conjBy h = H.conjBy (h * g) :=
  (conjBy_mul H h g).symm

/-- Conjugation by `a` is inverted by conjugation by `a⁻¹`. -/
public theorem conjBy_inv (H : Subgroup G) (a : G) : (H.conjBy a).conjBy a⁻¹ = H := by
  rw [conjBy_conjBy, inv_mul_cancel, conjBy_one]

/-- Conjugation by `a` and by `a⁻¹` are mutually inverse;
  this is `conjBy_inv` expressed as cancellation on the other side. -/
public theorem conjBy_inv' (H : Subgroup G) (a : G) : (H.conjBy a⁻¹).conjBy a = H := by
  rw [conjBy_conjBy, mul_inv_cancel, conjBy_one]

/-- If conjugating by `a` gives the same result as conjugating by `b`, then conjugating
  by `a⁻¹ * b` is the identity. -/
public theorem conjBy_inv_mul_cancel (H : Subgroup G) {a b : G}
    (h : H.conjBy a = H.conjBy b) : H.conjBy (a⁻¹ * b) = H := by
  rw [conjBy_mul, ← h, conjBy_inv]

end ConjByAlgebra

end Subgroup

section NormalizerLemmas

variable {G : Type*} [Group G]

/-- If `R` fixes `H` under conjugation (elementwise), then `R` is contained in the
normalizer of `H`.  This is in `Subgroup.conjBy` language. -/
public theorem CFSG.subgroup_le_normalizer_of_conj_mem {G : Type*} [Group G]
    (H R : Subgroup G)
    (hRinv : ∀ r : R, ∀ h ∈ H, (r : G) * h * (r : G)⁻¹ ∈ H) :
    R ≤ Subgroup.normalizer (H : Set G) := by
  intro r hrR
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hRinv ⟨r, hrR⟩ x hx
  · intro hx
    have hx' :
        ((r : G)⁻¹ * ((r : G) * x * (r : G)⁻¹) * (((r : G)⁻¹)⁻¹)) ∈ H :=
      hRinv ⟨r⁻¹, R.inv_mem hrR⟩ ((r : G) * x * (r : G)⁻¹) hx
    simpa [mul_assoc] using hx'

/-- `normal_subgroupOf_sup_of_conj_mem` gives a sufficient condition for the subgroup
  `H.subgroupOf (H ⊔ R)` to be normal in `H ⊔ R`. -/
public theorem CFSG.normal_subgroupOf_sup_of_conj_mem {G : Type*} [Group G]
    (H R : Subgroup G) [H.Normal]
    (hRinv : ∀ r : R, ∀ h ∈ H, (r : G) * h * (r : G)⁻¹ ∈ H) :
    (H.subgroupOf (H ⊔ R)).Normal := by
  let S : Subgroup G := H ⊔ R
  refine ⟨?_⟩
  intro x hx y
  rcases (Subgroup.mem_sup_of_normal_left (x := (y : G)) (s := H) (t := R)).1 y.2 with
    ⟨h, hhH, r, hrR, hy⟩
  have hrxH : (r : G) * x * (r : G)⁻¹ ∈ H := hRinv ⟨r, hrR⟩ x hx
  have hhxH : h * ((r : G) * x * (r : G)⁻¹) * h⁻¹ ∈ H :=
    Subgroup.Normal.conj_mem inferInstance _ hrxH h
  change ((y : G) * x * (y : G)⁻¹) ∈ H
  rw [← hy]
  simpa [mul_assoc] using hhxH

end NormalizerLemmas

section ComplementLemmas

variable {G : Type*} [Group G]

/-- If `H` is normal and `Disjoint H R`, then `H.subgroupOf (H ⊔ R)` and `R.subgroupOf (H ⊔ R)`
  are complementary subgroups of `H ⊔ R`. -/
public theorem CFSG.isComplement'_subgroupOf_sup_of_disjoint {G : Type*} [Group G]
    (H R : Subgroup G) [H.Normal] (hdisj : Disjoint H R) :
    (H.subgroupOf (H ⊔ R)).IsComplement' (R.subgroupOf (H ⊔ R)) := by
  let S : Subgroup G := H ⊔ R
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxH hxR
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisj hxH hxR
  · rw [Set.eq_univ_iff_forall]
    intro x
    rcases (Subgroup.mem_sup_of_normal_left (x := (x : G)) (s := H) (t := R)).1 x.2 with
      ⟨h, hhH, r, hrR, hmul⟩
    let hS : H.subgroupOf S := ⟨⟨h, Subgroup.mem_sup_left hhH⟩, hhH⟩
    let rS : R.subgroupOf S := ⟨⟨r, Subgroup.mem_sup_right hrR⟩, hrR⟩
    refine ⟨(hS : S), hS.2, (rS : S), rS.2, ?_⟩
    apply Subtype.ext
    simpa using hmul

end ComplementLemmas

section IsComplementQuotient

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The quotient equivalence attached to a complement sends the quotient
class of a complement element back to that element. -/
public theorem CFSG.quotientMulEquiv_mk_apply_of_isComplement'
    {K N : Subgroup G} [N.Normal]
    (hcomp : K.IsComplement' N) (x : K) :
    hcomp.QuotientMulEquiv (QuotientGroup.mk' N (x : G)) = x := by
  have hinjective :
      ∀ {x y : K},
        (QuotientGroup.mk' N (x : G) : G ⧸ N) =
            QuotientGroup.mk' N (y : G) →
          x = y := by
    intro x y hxy
    have hdiv : (x : G) * (y : G)⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      simpa [map_mul, map_inv] using
        congrArg (fun q => q * (QuotientGroup.mk' N (y : G))⁻¹) hxy
    have hxyK : (x : G) * (y : G)⁻¹ ∈ K :=
      K.mul_mem x.property (K.inv_mem y.property)
    have htop : ((x : G) * (y : G)⁻¹ : G) = 1 :=
      Subgroup.disjoint_def.mp hcomp.disjoint hxyK hdiv
    exact Subtype.ext (mul_inv_eq_one.mp htop)
  apply hinjective
  rw [Subgroup.IsComplement'.QuotientMulEquiv_apply]
  exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hcomp _

omit [Finite G] in
/-- Under the quotient equivalence supplied by a complement `K` to `N`,
the image of `N ⊔ W` is the transported copy of every subgroup `W ≤ K`. -/
public theorem CFSG.quotient_sup_image_eq_complement_map
    {S N K W : Subgroup G}
    (hNS : N ≤ S) (hKS : K ≤ S) (hWK : W ≤ K)
    [(N.subgroupOf S).Normal]
    (hcomp :
      (N.subgroupOf S).IsComplement' (K.subgroupOf S)) :
    let e : S ⧸ N.subgroupOf S ≃* K :=
      hcomp.symm.QuotientMulEquiv.trans
        (Subgroup.subgroupOfEquivOfLe hKS)
    ((N ⊔ W).subgroupOf S).map
        (QuotientGroup.mk' (N.subgroupOf S)) =
      (W.subgroupOf K).map e.symm.toMonoidHom := by
  classical
  let q : S →* S ⧸ N.subgroupOf S :=
    QuotientGroup.mk' (N.subgroupOf S)
  let e0 : S ⧸ N.subgroupOf S ≃* K.subgroupOf S :=
    hcomp.symm.QuotientMulEquiv
  let e : S ⧸ N.subgroupOf S ≃* K :=
    e0.trans (Subgroup.subgroupOfEquivOfLe hKS)
  have hWS : W ≤ S := hWK.trans hKS
  have hImage :
      ((N ⊔ W).subgroupOf S).map q =
        (W.subgroupOf S).map q := by
    have hsubsup :
        (N ⊔ W).subgroupOf S =
          N.subgroupOf S ⊔ W.subgroupOf S :=
      Subgroup.subgroupOf_sup (A := N) (A' := W) (B := S) hNS hWS
    rw [hsubsup, Subgroup.map_sup, QuotientGroup.map_mk'_self]
    simp
  rw [hImage]
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨wS, hwW, hwy⟩
    let wK : K := ⟨((wS : S) : G), hWK (by
      simpa [Subgroup.mem_subgroupOf] using hwW)⟩
    have hwKsub : wK ∈ W.subgroupOf K := by
      simpa [wK, Subgroup.mem_subgroupOf] using hwW
    refine Subgroup.mem_map.mpr ⟨wK, hwKsub, ?_⟩
    change e.symm wK = y
    apply e.injective
    have heval :
        e (q wS) = wK := by
      let wKS : K.subgroupOf S := ⟨wS, wK.property⟩
      have he0 :
          e0 (q wS) = wKS := by
        simpa [q, e0, wKS] using
          quotientMulEquiv_mk_apply_of_isComplement' hcomp.symm wKS
      change (Subgroup.subgroupOfEquivOfLe hKS) (e0 (q wS)) = wK
      rw [he0]
      rfl
    have hey : e y = wK := by
      rw [← hwy]
      exact heval
    exact (e.apply_symm_apply wK).trans hey.symm
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨wK, hwW, hwy⟩
    let wS : S := ⟨(wK : G), hKS wK.property⟩
    have hwWS : wS ∈ W.subgroupOf S := by
      change (wK : G) ∈ W
      exact hwW
    refine Subgroup.mem_map.mpr ⟨wS, hwWS, ?_⟩
    apply e.injective
    have heval :
        e (q wS) = wK := by
      let wKS : K.subgroupOf S := ⟨wS, wK.property⟩
      have he0 :
          e0 (q wS) = wKS := by
        simpa [q, e0, wKS] using
          quotientMulEquiv_mk_apply_of_isComplement' hcomp.symm wKS
      change (Subgroup.subgroupOfEquivOfLe hKS) (e0 (q wS)) = wK
      rw [he0]
      rfl
    have hey : e y = wK := by
      rw [← hwy]
      exact e.apply_symm_apply wK
    exact heval.trans hey.symm

omit [Finite G] in
/-- If `K.IsComplement' R` and `N ≤ K`, then the images under `G → G/N` are complementary. -/
public theorem CFSG.isComplement'_map_mk'_of_le_isComplement' (K R N : Subgroup G) [N.Normal]
    (hN_le_K : N ≤ K) (hKR : K.IsComplement' R) :
    (K.map (QuotientGroup.mk' N)).IsComplement' (R.map (QuotientGroup.mk' N)) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxK hxR
    rw [Subgroup.mem_map] at hxK hxR
    rcases hxK with ⟨k, hkK, hkx⟩
    rcases hxR with ⟨r, hrR, hrx⟩
    have hrk_eq : (r : G)⁻¹ * k ∈ N := QuotientGroup.eq.mp (hrx.trans hkx.symm)
    have hr_inv_mem_K : (r : G)⁻¹ ∈ K := by
      have hmemK : (r : G)⁻¹ * k ∈ K := hN_le_K hrk_eq
      have : ((r : G)⁻¹ * k) * k⁻¹ ∈ K := K.mul_mem hmemK (K.inv_mem hkK)
      simpa [mul_assoc] using this
    have hr_mem_K : (r : G) ∈ K := by
      simpa using K.inv_mem hr_inv_mem_K
    have hr_eq_one : (r : G) = 1 := by
      have hr_bot : (r : G) ∈ (⊥ : Subgroup G) :=
        (Subgroup.disjoint_def.mp hKR.disjoint) hr_mem_K hrR
      simpa using hr_bot
    calc
      x = q r := hrx.symm
      _ = 1 := by simp [q, hr_eq_one]
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := N) x
    rcases hKR.2 g with ⟨⟨⟨k, hkK⟩, ⟨r, hrR⟩⟩, hgr⟩
    have hgr' : (k : G) * r = g := by
      simpa using hgr
    refine ⟨q k, ?_, q r, ?_, ?_⟩
    · exact ⟨k, hkK, rfl⟩
    · exact ⟨r, hrR, rfl⟩
    · change q (k * r) = q g
      simpa using congrArg q hgr'

end IsComplementQuotient

section CommutatorActionLemmas

variable {G : Type*} [Group G]

/-- Relate the image of the commutator action inside `H ⋊ R` to the commutator subgroup
  `⁅H, R⁆`. -/
public theorem CFSG.commutatorAction_subgroup_conj_map_eq_commutator {G : Type*} [Group G]
    (H R : Subgroup G) (hRnormH : R ≤ Subgroup.normalizer H) :
    haveI : Subgroup.Normalizes R H := ⟨hRnormH⟩
    (commutatorAction (A := ↥R) (G := ↥H)).map H.subtype = ⁅H, R⁆ := by
  haveI : Subgroup.Normalizes R H := ⟨hRnormH⟩
  let SH : Set H := {x : H | ∃ a : R, ∃ h : H, x = h⁻¹ * (a • h)}
  let SG : Set G := {x : G | ∃ a : R, ∃ h : H, x = ⁅(h : G)⁻¹, (a : G)⁆}
  let SC : Set G := {x : G | ∃ h ∈ H, ∃ a ∈ R, ⁅h, a⁆ = x}
  have himage : H.subtype '' SH = SG := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨a, h, rfl⟩
      refine ⟨a, h, ?_⟩
      simp [commutatorElement_def,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
    · rintro ⟨a, h, rfl⟩
      refine ⟨h⁻¹ * (a • h), ⟨a, h, rfl⟩, ?_⟩
      simp [commutatorElement_def,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
  have hsets : SG = SC := by
    ext x
    constructor
    · rintro ⟨a, h, rfl⟩
      exact ⟨(h : G)⁻¹, H.inv_mem h.2, (a : G), a.2, rfl⟩
    · rintro ⟨h, hhH, a, haR, rfl⟩
      exact ⟨⟨a, haR⟩, ⟨h⁻¹, H.inv_mem hhH⟩, by simp⟩
  calc
    (commutatorAction (A := ↥R) (G := ↥H)).map H.subtype
        = (Subgroup.closure SH).map H.subtype := by
            simpa [SH] using
              congrArg (fun K : Subgroup H => K.map H.subtype)
                (commutatorAction_eq_closure (G := ↥H) (A := ↥R))
    _ = Subgroup.closure (H.subtype '' SH) := by
          simpa using (MonoidHom.map_closure (f := H.subtype) SH)
    _ = Subgroup.closure SG := by
          simpa using congrArg Subgroup.closure himage
    _ = Subgroup.closure SC := by rw [hsets]
    _ = ⁅H, R⁆ := by
          simp [SC, Subgroup.commutator_def]

end CommutatorActionLemmas

section SubgroupOfCommutator

variable {G : Type*} [Group G]

/-- The commutator of two subgroups, when both are restricted to a containing subgroup `S`, maps
  to the full commutator via `S.subtype`. -/
public theorem CFSG.commutator_subgroupOf_map_eq {G : Type*} [Group G]
    (S H R : Subgroup G) (hH_le : H ≤ S) (hR_le : R ≤ S) :
    (⁅R.subgroupOf S, H.subgroupOf S⁆).map S.subtype = ⁅R, H⁆ := by
  rw [Subgroup.map_commutator]
  rw [Subgroup.map_subgroupOf_eq_of_le hR_le, Subgroup.map_subgroupOf_eq_of_le hH_le]

/-- If the commutator of the `S`-restricted subgroups is trivial, then the full commutator is
  trivial. -/
public theorem CFSG.commutator_eq_bot_of_subgroupOf_commutator_le_bot {G : Type*} [Group G]
    (S H R : Subgroup G) (hH_le : H ≤ S) (hR_le : R ≤ S)
    (hsub : ⁅R.subgroupOf S, H.subgroupOf S⁆ ≤ ⊥) :
    ⁅H, R⁆ = ⊥ := by
  apply bot_unique
  intro x hx
  have hxmap : x ∈ (⁅R.subgroupOf S, H.subgroupOf S⁆).map S.subtype := by
    rw [commutator_subgroupOf_map_eq S H R hH_le hR_le]
    simpa [Subgroup.commutator_comm] using hx
  rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, rfl⟩
  have hy1 : y = 1 := by
    exact hsub hy
  simpa using congrArg Subtype.val hy1

/-- A version of `commutator_eq_bot_of_subgroupOf_commutator_le_bot` where the containing
  subgroup is `H ⊔ R`. -/
public theorem CFSG.commutator_eq_bot_of_sup_subgroupOf_commutator_le_bot {G : Type*} [Group G]
    (H R : Subgroup G) (hsub : ⁅R.subgroupOf (H ⊔ R), H.subgroupOf (H ⊔ R)⁆ ≤ ⊥) :
    ⁅H, R⁆ = ⊥ := by
  exact
    commutator_eq_bot_of_subgroupOf_commutator_le_bot (G := G) (S := H ⊔ R) (H := H) (R := R)
      le_sup_left le_sup_right hsub

/-- Relate `subgroupCentralizerIn` in a supergroup `S` to the one in the full group. -/
public theorem CFSG.subgroupCentralizerIn_subgroupOf_eq {G : Type*} [Group G]
    (S H R : Subgroup G) (hR_le : R ≤ S) :
    subgroupCentralizerIn (H.subgroupOf S) (R.subgroupOf S) =
      (subgroupCentralizerIn H R).subgroupOf S := by
  ext x
  constructor
  · rintro ⟨hxH, hxC⟩
    change (x : G) ∈ H ∧ (x : G) ∈ Subgroup.centralizer (R : Set G)
    refine ⟨hxH, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hrR
    have hrsub : (⟨r, hR_le hrR⟩ : S) ∈ R.subgroupOf S := by
      simpa [Subgroup.mem_subgroupOf] using hrR
    exact congrArg Subtype.val (hxC ⟨r, hR_le hrR⟩ hrsub)
  · intro hx
    change (x : G) ∈ H ∧ (x : G) ∈ Subgroup.centralizer (R : Set G) at hx
    rcases hx with ⟨hxH, hxC⟩
    refine ⟨hxH, ?_⟩
    change x ∈ Subgroup.centralizer ((R.subgroupOf S) : Set S)
    rw [Subgroup.mem_centralizer_iff]
    intro r hrR
    apply Subtype.ext
    exact hxC (r : G) (by simpa [Subgroup.mem_subgroupOf] using hrR)


section ZGroupLemmas

variable {G : Type*} [Group G]

/-- If `subgroupCentralizerIn H R` is a Z-group, then `subgroupCentralizerIn N R` is also
  a Z-group for any `N ≤ H`. -/
public theorem CFSG.isZGroup_subgroupCentralizerIn_of_le (H N R : Subgroup G) (hN_le_H : N ≤ H)
    [IsZGroup ↥(subgroupCentralizerIn H R)] :
    IsZGroup ↥(subgroupCentralizerIn N R) := by
  have hleCZ : subgroupCentralizerIn N R ≤ subgroupCentralizerIn H R := by
    intro x hx
    exact ⟨hN_le_H hx.1, hx.2⟩
  let f : subgroupCentralizerIn N R →* subgroupCentralizerIn H R := Subgroup.inclusion hleCZ
  have hf : Function.Injective f := Subgroup.inclusion_injective hleCZ
  exact IsZGroup.of_injective (f := f) hf

/-- If `subgroupCentralizerIn N R` is a Z-group, then its restriction to `S` is also. -/
public theorem CFSG.isZGroup_subgroupCentralizerIn_subgroupOf (S N R : Subgroup G) (hR_le : R ≤ S)
    [IsZGroup ↥(subgroupCentralizerIn N R)] :
    IsZGroup ↥(subgroupCentralizerIn (N.subgroupOf S) (R.subgroupOf S)) := by
  have hEq :
      subgroupCentralizerIn (N.subgroupOf S) (R.subgroupOf S) =
        (subgroupCentralizerIn N R).subgroupOf S :=
    subgroupCentralizerIn_subgroupOf_eq S N R hR_le
  let fsub : ((subgroupCentralizerIn N R).subgroupOf S) →* subgroupCentralizerIn N R :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := rfl
      map_mul' := by intro a b; rfl }
  have hfsub : Function.Injective fsub := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    simpa [fsub] using congrArg Subtype.val hab
  have hZsub : IsZGroup ↥((subgroupCentralizerIn N R).subgroupOf S) :=
    IsZGroup.of_injective (f := fsub) hfsub
  rw [hEq]
  exact hZsub

end ZGroupLemmas

section FixedPointLemmas

variable {G : Type*} [Group G]

open FixedPoints

/-- The fixed-point subgroup of the action of `R` on `H` (by conjugation) equals the
  subgroup-centralizer `subgroupCentralizerIn H R` intersected with `H`. -/
public theorem CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
    (H R : Subgroup G) (hRnormH : R ≤ Subgroup.normalizer H) :
    haveI : Subgroup.Normalizes R H := ⟨hRnormH⟩
    fixedPointSubgroup (↥R) (↥H) = (subgroupCentralizerIn H R).subgroupOf H := by
  haveI : Subgroup.Normalizes R H := ⟨hRnormH⟩
  ext x
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    change (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hrR
    have hxfix : (⟨r, hrR⟩ : R) • x = x := hx ⟨r, hrR⟩
    have hxconj : (r : G) * (x : G) * (r : G)⁻¹ = x := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using
        congrArg Subtype.val hxfix
    have := congrArg (fun t : G => t * r) hxconj
    simpa [mul_assoc] using this
  · intro hx
    rcases hx with ⟨-, hxC⟩
    rw [FixedPoints.mem_subgroup]
    intro r
    apply Subtype.ext
    have hcomm : (r : G) * (x : G) = (x : G) * (r : G) :=
      Subgroup.mem_centralizer_iff.mp hxC (r : G) r.2
    have hxconj : (r : G) * (x : G) * (r : G)⁻¹ = x := by
      calc
        (r : G) * (x : G) * (r : G)⁻¹ = ((x : G) * (r : G)) * (r : G)⁻¹ := by
          rw [hcomm]
        _ = x := by simp [mul_assoc]
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using hxconj

/-- Relate the fixed-point subgroup of the action of `⟨r⟩` on `K` to the element centralizer
  of `r` in `K`. -/
public theorem CFSG.fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
    {G : Type*} [Group G] (K R : Subgroup G) (hRK : R ≤ Subgroup.normalizer K) (r : R) :
    haveI : Subgroup.Normalizes R K := ⟨hRK⟩
    fixedPointSubgroup (↥(Subgroup.zpowers r)) (↥K) =
      (elementCentralizerIn K (r : G)).subgroupOf K := by
  haveI : Subgroup.Normalizes R K := ⟨hRK⟩
  ext x
  constructor
  · intro hx
    refine ⟨x.property, ?_⟩
    have hxfix : r • x = x := by
      exact hx ⟨r, Subgroup.mem_zpowers r⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hxconj : (r : G) * (x : G) * (r : G)⁻¹ = x := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using
        congrArg Subtype.val hxfix
    have := congrArg (fun t : G => t * (r : G)) hxconj
    simpa [mul_assoc] using this.symm
  · intro hx
    rcases hx with ⟨hxK, hxcent⟩
    rw [FixedPoints.mem_subgroup]
    intro a
    have hxr : r • x = x := by
      apply Subtype.ext
      have hxconj : (r : G) * (x : G) * (r : G)⁻¹ = x := by
        have hmul : (r : G) * (x : G) = (x : G) * (r : G) :=
          (Subgroup.mem_centralizer_singleton_iff.mp hxcent).symm
        calc
          (r : G) * (x : G) * (r : G)⁻¹ = ((x : G) * (r : G)) * (r : G)⁻¹ := by
            rw [hmul]
          _ = x := by simp [mul_assoc]
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hxconj
    have ha_mem :
        a ∈ Subgroup.zpowers (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) := by
      rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
        apply Subtype.ext
        simpa using hn⟩
    exact
      smul_eq_self_of_mem_zpowers (y := (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r))
        ha_mem hxr

/-- If the action of `R` on `K` (by conjugation) is trivial, then the commutator is trivial. -/
public theorem CFSG.commutator_eq_bot_of_actsTrivially_subgroup_conj {G : Type*} [Group G]
    (K R : Subgroup G) (hRK : R ≤ Subgroup.normalizer K) :
    haveI : Subgroup.Normalizes R K := ⟨hRK⟩
    ActsTrivially (A := ↥R) (G := ↥K) → ⁅R, K⁆ = ⊥ := by
  haveI : Subgroup.Normalizes R K := ⟨hRK⟩
  intro htriv
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hfix : ((⟨r, hr⟩ : R) • (⟨k, hk⟩ : K) : K) = ⟨k, hk⟩ := htriv ⟨r, hr⟩ ⟨k, hk⟩
  have hfix' : (r : G) * k * (r : G)⁻¹ = k := by
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using
      congrArg Subtype.val hfix
  have := congrArg (fun t : G => t * r) hfix'
  simpa [mul_assoc] using this.symm

/-- The converse direction: if the commutator is trivial, the action is trivial. -/
public theorem CFSG.actsTrivially_subgroup_conj_of_commutator_eq_bot {G : Type*} [Group G]
    (K R : Subgroup G) (hRK : R ≤ Subgroup.normalizer K) :
    haveI : Subgroup.Normalizes R K := ⟨hRK⟩
    ⁅R, K⁆ = ⊥ → ActsTrivially (A := ↥R) (G := ↥K) := by
  haveI : Subgroup.Normalizes R K := ⟨hRK⟩
  intro hcomm r k
  have hcomm_le : R ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
  have hr_cent : (r : G) ∈ Subgroup.centralizer (K : Set G) := hcomm_le r.2
  have hmul : (r : G) * (k : G) = (k : G) * (r : G) :=
    (Subgroup.mem_centralizer_iff.mp hr_cent) k k.2 |>.symm
  have hfix' : (r : G) * (k : G) * (r : G)⁻¹ = (k : G) := by
    calc
      (r : G) * (k : G) * (r : G)⁻¹ = ((k : G) * (r : G)) * (r : G)⁻¹ := by rw [hmul]
      _ = (k : G) := by simp [mul_assoc]
  apply Subtype.ext
  simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hfix'

end FixedPointLemmas

end SubgroupOfCommutator

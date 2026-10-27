module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonExceptionalF9SL3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma3_4
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_1
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3Step7
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma63Step8
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma63MinimalBadEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PStableIso
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.pStability
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.QdSLPCore
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.QdMulEquivOfComplement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.InvolvedQuotient

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

open Matrix
open GorensteinWalter
open scoped Pointwise commutatorElement

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — Lemma 6.3

Statement (paper `refs/glauberman-p-stable.tex` L1656–L1793): let `p` be an odd prime and
`G` a finite group.  The following are equivalent:

(a) `Qd(p)` is not involved in `G`;
(b) every subquotient of `G` is `p`-stable.

Formal statement (`lemma6_3`, matching the pinned wrapper statement
`Glauberman.ZJTheorem.lemma_6_3`):

    (¬ Involved (Qd p) G) ↔ ∀ (K : Subgroup G) (N : Subgroup K) [hN : N.Normal], pStable p (K ⧸ N)

## Proof route (paper L1664–L1793)

* **(b) ⟹ (a)** ([6], §2, p. 1104–1105; tex L278–L300): `Qd(p) = V₂ ⋊ SL(2,p)` is not
  `p`-stable: the transvection `x = [[1,1],[0,1]]` satisfies `[V₂,x,x] = 1` (computed from
  `(y-1)² = 0`), but its coset modulo `C(V₂) = V₂` is a non-trivial element of
  `N(V₂)/C(V₂) ≅ SL(2,p)`, whose `p`-core is trivial for odd `p` (`O_p(SL(2,p)) = 1`).
  This is proved as `qd_not_pStable` below.  Since `pStable` is invariant under group
  isomorphism (`pStable_iso`, proved here), (b) applied to the witnessing subquotient
  `K ⧸ N ≃ Qd(p)` of an involvement contradicts it.
* **(a) ⟹ (b)** — choose a least-cardinality non-`p`-stable subquotient, identify it
  with `Qd(p)` by `minimal_bad_group_equiv_qd`, and transport involvement back through
  the quotient and subgroup witnesses.
* The `Involved` plumbing (`Involved_iff_of_mulEquiv`, `involved_self`,
  `involved_of_involved_subgroup`) and the isomorphism invariance of `pStable` /
  `pStableLocal` (`pStableLocal_iso`, `pStable_iso`) are proved in full in this file.

## Axiom audit

All exported endpoints in this module are proved without `sorry`; the audits at the
end of the file report only `{propext, Classical.choice, Quot.sound}`.
-/

namespace CFSG.Glauberman

/-! ## `Qd(p)` is not `p`-stable (the `(b) ⟹ (a)` input) -/

/-- The normal `p`-subgroup `V₂ = inl.range` of `Qd(p)`. -/
private def qdV (p : ℕ) [Fact p.Prime] : Subgroup (Qd p) :=
  (SemidirectProduct.inl : Multiplicative (qdSpace p) →* Qd p).range

private theorem qdV_normal (p : ℕ) [Fact p.Prime] : (qdV p).Normal := by
  rw [qdV, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

private theorem qdV_card (p : ℕ) [Fact p.Prime] : Nat.card (qdV p) = p ^ 2 := by
  let e : Multiplicative (qdSpace p) ≃* qdV p :=
    MulEquiv.ofBijective (SemidirectProduct.inl.rangeRestrict)
      ⟨(MonoidHom.rangeRestrict_injective_iff (f := (SemidirectProduct.inl : Multiplicative (qdSpace p) →* Qd p))).2 SemidirectProduct.inl_injective,
        MonoidHom.rangeRestrict_surjective _⟩
  calc
    Nat.card (qdV p) = Nat.card (Multiplicative (qdSpace p)) := Nat.card_congr e.symm.toEquiv
    _ = p ^ 2 := by simp [qdSpace]

private theorem qdV_isPGroup (p : ℕ) [Fact p.Prime] : IsPGroup p (qdV p) :=
  IsPGroup.of_card (qdV_card p)

private theorem qdV_le_pCore (p : ℕ) [Fact p.Prime] : qdV p ≤ pCore p (Qd p) := by
  rw [pCore]
  exact le_sSup ⟨qdV_normal p, qdV_isPGroup p⟩

private theorem qdV_rightHom_ker (p : ℕ) [Fact p.Prime] :
    (SemidirectProduct.rightHom : Qd p →* qdSL p).ker = qdV p := by
  rw [qdV, SemidirectProduct.range_inl_eq_ker_rightHom]

private theorem normalPSubgroup_le_qdV (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    {K : Subgroup (Qd p)} (hK : K.Normal) (hKp : IsPGroup p K) :
    K ≤ qdV p := by
  let ρ : Qd p →* qdSL p := SemidirectProduct.rightHom
  have him : K.map ρ = ⊥ := by
    have hmap_normal : (K.map ρ).Normal := Subgroup.Normal.map hK ρ SemidirectProduct.rightHom_surjective
    have hmap_p : IsPGroup p (K.map ρ) := IsPGroup.map hKp ρ
    have hle : K.map ρ ≤ pCore p (qdSL p) := le_sSup ⟨hmap_normal, hmap_p⟩
    rw [qdSL_pCore_eq_bot p hpodd] at hle
    exact le_bot_iff.mp hle
  intro x hx
  have hxρ : ρ x ∈ K.map ρ := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [him] at hxρ
  have hker : x ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    simpa using hxρ
  simpa [ρ, qdV_rightHom_ker p] using hker

private theorem pCore_le_qdV (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    pCore p (Qd p) ≤ qdV p := by
  rw [pCore]
  exact sSup_le (by
    intro K hK
    exact normalPSubgroup_le_qdV p hpodd hK.1 hK.2)

private theorem qdV_eq_pCore (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    qdV p = pCore p (Qd p) :=
  le_antisymm (qdV_le_pCore p) (pCore_le_qdV p hpodd)

private theorem qdSL_eq_one_of_fixes_basis (p : ℕ) [Fact p.Prime] {A : qdSL p}
    (h0 : A • (![1, 0] : qdSpace p) = ![1, 0])
    (h1 : A • (![0, 1] : qdSpace p) = ![0, 1]) : A = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i
  · fin_cases j
    · have hc := congrFun h0 0
      simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two] using hc
    · have hc := congrFun h1 0
      simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two] using hc
  · fin_cases j
    · have hc := congrFun h0 1
      simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two] using hc
    · have hc := congrFun h1 1
      simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two] using hc

private lemma qdAction_apply_smul (p : ℕ) [Fact p.Prime] (A : qdSL p) (v : qdSpace p) :
    Multiplicative.toAdd (qdAction p A (Multiplicative.ofAdd v)) = A • v := by
  simp [qdAction, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.SpecialLinearGroup.smul_def]

private theorem qdV_centralizer_eq (p : ℕ) [Fact p.Prime] :
    Subgroup.centralizer ((qdV p : Subgroup (Qd p)) : Set (Qd p)) = qdV p := by
  apply le_antisymm
  · intro y hy
    have hy' : ∀ v ∈ qdV p, y * v = v * y := by
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp hy v hv).symm
    let n : Multiplicative (qdSpace p) := y.left
    let A : qdSL p := y.right
    have hy0 : n * qdAction p A (Multiplicative.ofAdd (![1, 0] : qdSpace p)) =
        Multiplicative.ofAdd (![1, 0] : qdSpace p) * n := by
      have hv : SemidirectProduct.inl (Multiplicative.ofAdd (![1, 0] : qdSpace p)) ∈ qdV p := by
        rw [qdV]
        exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (![1, 0] : qdSpace p), rfl⟩
      have h := hy' (SemidirectProduct.inl (Multiplicative.ofAdd (![1, 0] : qdSpace p))) hv
      have hleft := congrArg SemidirectProduct.left h
      simpa [n, A, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.left_inr] using hleft
    have he0 : qdAction p A (Multiplicative.ofAdd (![1, 0] : qdSpace p)) =
        Multiplicative.ofAdd (![1, 0] : qdSpace p) := by
      have h' := congrArg (fun z : Multiplicative (qdSpace p) => z * n⁻¹) hy0
      simpa [mul_assoc] using h'
    have hA0 : A • (![1, 0] : qdSpace p) = ![1, 0] := by
      have h := congrArg Multiplicative.toAdd he0
      rw [qdAction_apply_smul p A ![1,0]] at h
      exact h
    have hy1 : n * qdAction p A (Multiplicative.ofAdd (![0, 1] : qdSpace p)) =
        Multiplicative.ofAdd (![0, 1] : qdSpace p) * n := by
      have hv : SemidirectProduct.inl (Multiplicative.ofAdd (![0, 1] : qdSpace p)) ∈ qdV p := by
        rw [qdV]
        exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (![0, 1] : qdSpace p), rfl⟩
      have h := hy' (SemidirectProduct.inl (Multiplicative.ofAdd (![0, 1] : qdSpace p))) hv
      have hleft := congrArg SemidirectProduct.left h
      simpa [n, A, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.left_inr] using hleft
    have he1 : qdAction p A (Multiplicative.ofAdd (![0, 1] : qdSpace p)) =
        Multiplicative.ofAdd (![0, 1] : qdSpace p) := by
      have h' := congrArg (fun z : Multiplicative (qdSpace p) => z * n⁻¹) hy1
      simpa [mul_assoc] using h'
    have hA1 : A • (![0, 1] : qdSpace p) = ![0, 1] := by
      have h := congrArg Multiplicative.toAdd he1
      rw [qdAction_apply_smul p A ![0,1]] at h
      exact h
    have hA : A = 1 := qdSL_eq_one_of_fixes_basis p hA0 hA1
    have hker : y ∈ (SemidirectProduct.rightHom : Qd p →* qdSL p).ker := by
      rw [MonoidHom.mem_ker]
      simp [A, hA]
    simpa [qdV_rightHom_ker p] using hker
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have : IsMulCommutative (qdV p) :=
      Subgroup.range_isMulCommutative (f := (SemidirectProduct.inl : Multiplicative (qdSpace p) →* Qd p))
    have hyc : y ∈ Subgroup.centralizer ((qdV p : Subgroup (Qd p)) : Set (Qd p)) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (G := Qd p) (K := qdV p)).mpr inferInstance hy
    exact (Subgroup.mem_centralizer_iff.mp hyc) z hz

/-- The transvection `x = (0, [[1,1],[0,1]])` and its powers. -/
private def qdT (p : ℕ) [Fact p.Prime] : qdSL p :=
  GorensteinWalter.sl2UpperUnipotent (1 : ZMod p)

private def qdX (p : ℕ) [Fact p.Prime] : Qd p :=
  SemidirectProduct.inr (qdT p)

private theorem qdT_pow (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (qdT p) ^ k = GorensteinWalter.sl2UpperUnipotent (k : ZMod p) := by
  induction k with
  | zero => simp [qdT]
  | succ k ih =>
      rw [pow_succ, ih]
      simp [qdT, GorensteinWalter.sl2UpperUnipotent_mul, Nat.cast_add]

private theorem qdT_zpow (p : ℕ) [Fact p.Prime] (k : ℤ) :
    (qdT p) ^ k = GorensteinWalter.sl2UpperUnipotent (k : ZMod p) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa [zpow_natCast] using qdT_pow p n
  · rw [zpow_neg, zpow_natCast, qdT_pow p n, GorensteinWalter.sl2UpperUnipotent_inv]
    simp

private theorem qdX_pow (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (qdX p) ^ k = SemidirectProduct.inr (GorensteinWalter.sl2UpperUnipotent (k : ZMod p)) := by
  rw [show (qdX p) ^ k = SemidirectProduct.inr ((qdT p) ^ k) by
    exact (map_pow (SemidirectProduct.inr : qdSL p →* Qd p) (qdT p) k).symm, qdT_pow]

private theorem qdX_zpow (p : ℕ) [Fact p.Prime] (k : ℤ) :
    (qdX p) ^ k = SemidirectProduct.inr (GorensteinWalter.sl2UpperUnipotent (k : ZMod p)) := by
  rw [show (qdX p) ^ k = SemidirectProduct.inr ((qdT p) ^ k) by
    exact (map_zpow (SemidirectProduct.inr : qdSL p →* Qd p) (qdT p) k).symm, qdT_zpow]

private theorem qd_commutator_inl_inr (p : ℕ) [Fact p.Prime] (a : qdSpace p) (A : qdSL p) :
    (⁅(SemidirectProduct.inl (Multiplicative.ofAdd a) : Qd p),
       (SemidirectProduct.inr A : Qd p)⁆ : Qd p) =
      SemidirectProduct.inl (Multiplicative.ofAdd (a - A • a)) := by
  change (SemidirectProduct.inl (Multiplicative.ofAdd a) * SemidirectProduct.inr A *
    (SemidirectProduct.inl (Multiplicative.ofAdd a))⁻¹ * (SemidirectProduct.inr A)⁻¹) = _
  apply SemidirectProduct.ext
  · apply Multiplicative.ext
    simp [qdAction_apply_smul p, sub_eq_add_neg]
  · simp [div_eq_mul_inv]

private theorem sl2UpperUnipotent_fixed_of_square_zero (p : ℕ) [Fact p.Prime]
    (m n : ZMod p) (a : qdSpace p) :
    GorensteinWalter.sl2UpperUnipotent m • (a - GorensteinWalter.sl2UpperUnipotent n • a) =
      a - GorensteinWalter.sl2UpperUnipotent n • a := by
  simp_rw [Matrix.SpecialLinearGroup.smul_def]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail,
      GorensteinWalter.sl2UpperUnipotent]

private theorem qd_commutator_triple_eq_one (p : ℕ) [Fact p.Prime] (a : qdSpace p) (m n : ℤ) :
    (⁅⁅(SemidirectProduct.inl (Multiplicative.ofAdd a) : Qd p),
         (qdX p) ^ m⁆, (qdX p) ^ n⁆ : Qd p) = 1 := by
  rw [qdX_zpow, qdX_zpow]
  have h1 : (⁅(SemidirectProduct.inl (Multiplicative.ofAdd a) : Qd p),
      (SemidirectProduct.inr (GorensteinWalter.sl2UpperUnipotent (m : ZMod p)) : Qd p)⁆ : Qd p) =
      SemidirectProduct.inl (Multiplicative.ofAdd (a - GorensteinWalter.sl2UpperUnipotent (m : ZMod p) • a)) :=
    qd_commutator_inl_inr p a (GorensteinWalter.sl2UpperUnipotent (m : ZMod p))
  rw [h1]
  have h2 : (⁅(SemidirectProduct.inl (Multiplicative.ofAdd (a - GorensteinWalter.sl2UpperUnipotent (m : ZMod p) • a)) : Qd p),
      (SemidirectProduct.inr (GorensteinWalter.sl2UpperUnipotent (n : ZMod p)) : Qd p)⁆ : Qd p) =
      SemidirectProduct.inl (Multiplicative.ofAdd ((a - GorensteinWalter.sl2UpperUnipotent (m : ZMod p) • a) -
        GorensteinWalter.sl2UpperUnipotent (n : ZMod p) • (a - GorensteinWalter.sl2UpperUnipotent (m : ZMod p) • a))) :=
    qd_commutator_inl_inr p (a - GorensteinWalter.sl2UpperUnipotent (m : ZMod p) • a)
      (GorensteinWalter.sl2UpperUnipotent (n : ZMod p))
  rw [h2]
  have hvec : (a - GorensteinWalter.sl2UpperUnipotent (m : ZMod p) • a) -
      GorensteinWalter.sl2UpperUnipotent (n : ZMod p) •
        (a - GorensteinWalter.sl2UpperUnipotent (m : ZMod p) • a) = 0 := by
    have hfix := sl2UpperUnipotent_fixed_of_square_zero p (n : ZMod p) (m : ZMod p) a
    rw [hfix]
    abel
  rw [hvec]
  simp

private theorem qd_commutator_x_eq_bot (p : ℕ) [Fact p.Prime] :
    ⁅⁅qdV p, Subgroup.zpowers (qdX p)⁆, Subgroup.zpowers (qdX p)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [Subgroup.commutator_le]
  intro v hv y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases (Subgroup.mem_zpowers_iff.mp hy) with ⟨m, hm⟩
  rcases (Subgroup.mem_zpowers_iff.mp hz) with ⟨n, hn⟩
  rw [← hm, ← hn]
  rcases MonoidHom.mem_range.mp hv with ⟨b, rfl⟩
  have hb : b = Multiplicative.ofAdd (Multiplicative.toAdd b) := by simp
  rw [hb]
  have htriple := qd_commutator_triple_eq_one p (Multiplicative.toAdd b) m n
  exact (commutatorElement_eq_one_iff_mul_comm.mp htriple).symm

private theorem qdT_ne_one (p : ℕ) [Fact p.Prime] : qdT p ≠ 1 := by
  intro h
  have h01 := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  simp [qdT, GorensteinWalter.sl2UpperUnipotent] at h01

/-- For an odd prime `p`, the quadratic group `Qd(p)` is not `p`-stable
(`refs/glauberman-p-stable.tex` L278–L300).  The proof follows the §2 computation:
`V₂ = O_p(Qd(p))` is the normal `p`-subgroup `inl.range`, its centralizer is itself,
and the transvection `x = (0, [[1,1],[0,1]])` satisfies `[V₂,x,x] = 1` while its coset
modulo `C(V₂)` is not contained in `O_p(Qd(p)/C(V₂))` (the latter is trivial because
`O_p(SL(2,p)) = 1`). -/
public theorem qd_not_pStable {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) : ¬ pStable p (Qd p) := by
  classical
  have : Finite (Qd p) := by
    dsimp [Qd, qdSL, qdSpace]
    exact Finite.of_equiv (Multiplicative (qdSpace p) × qdSL p) SemidirectProduct.equivProd.symm
  intro hstab
  have hPne : pCore p (Qd p) ≠ ⊥ := by
    have hVne : qdV p ≠ ⊥ := by
      have hcard : Nat.card (qdV p) = p ^ 2 := qdV_card p
      have hp0 : 0 < p := (Fact.out : p.Prime).pos
      intro h
      have hc := hcard
      rw [h] at hc
      simp at hc
      have hsq : 1 < p ^ 2 := by
        have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
        nlinarith [sq_pos_of_pos hp0, hp1]
      omega
    intro hbot
    have hle := qdV_le_pCore p
    have hVbot : qdV p = ⊥ := le_bot_iff.mp (by simpa [hbot] using hle)
    exact hVne hVbot
  have hcentralizer :
      Subgroup.centralizer ((pCore p (Qd p) : Subgroup (Qd p)) : Set (Qd p)) ≤ pCore p (Qd p) := by
    rw [← qdV_eq_pCore p hpodd, qdV_centralizer_eq p]
  have hcomm : ⁅⁅pCore p (Qd p), Subgroup.zpowers (qdX p)⁆, Subgroup.zpowers (qdX p)⁆ = ⊥ := by
    rw [← qdV_eq_pCore p hpodd]
    exact qd_commutator_x_eq_bot p
  have hcore_mem :=
    Glauberman.pStableLocal_apply_of_core_normal (G := Qd p) p hstab hPne (qdX p) hcomm
  have hleCore :=
    Glauberman.pCore_quotient_centralizer_le_of_centralizer_le_core (G := Qd p) p hcentralizer
  have hxmap : QuotientGroup.mk' (Subgroup.centralizer ((pCore p (Qd p) : Subgroup (Qd p)) : Set (Qd p))) (qdX p) ∈
      (pCore p (Qd p)).map (QuotientGroup.mk' (Subgroup.centralizer ((pCore p (Qd p) : Subgroup (Qd p)) : Set (Qd p)))) :=
    hleCore hcore_mem
  rcases Subgroup.mem_map.mp hxmap with ⟨v, hv, hvx⟩
  have hvc : v⁻¹ * qdX p ∈ Subgroup.centralizer ((pCore p (Qd p) : Subgroup (Qd p)) : Set (Qd p)) :=
    QuotientGroup.eq.mp hvx
  have hvcP : v⁻¹ * qdX p ∈ pCore p (Qd p) := hcentralizer hvc
  have hxP : qdX p ∈ pCore p (Qd p) := by
    have hxeq : qdX p = v * (v⁻¹ * qdX p) := by group
    rw [hxeq]
    exact (pCore p (Qd p)).mul_mem hv hvcP
  have hxV : qdX p ∈ qdV p := by
    rw [← qdV_eq_pCore p hpodd] at hxP
    exact hxP
  have hxker : qdX p ∈ (SemidirectProduct.rightHom : Qd p →* qdSL p).ker := by
    rw [← qdV_rightHom_ker p] at hxV
    exact hxV
  have hxright : qdT p = 1 := by
    rw [MonoidHom.mem_ker] at hxker
    change (SemidirectProduct.rightHom : Qd p →* qdSL p) (SemidirectProduct.inr (qdT p)) = 1 at hxker
    simpa using hxker
  exact qdT_ne_one p hxright

/-- **The application of Lemma 6.2 in step 6 of the proof of Lemma 6.3**
(`refs/glauberman-p-stable.tex` L1743–L1755).

**Statement.**  Let `p` be an odd prime, `F = GF(p)`, `V` a finite-dimensional `F`-vector
space and `H` a group of linear transformations acting faithfully and irreducibly on `V`,
generated by two elements each with minimal polynomial `(X-1)²`.  Then there exists a field
`K` of endomorphisms of `V` such that (a) `F ⊆ K`; (b) `V` is two-dimensional over `K`;
(c) either `H` is the special linear group of `V` over `K`, or `|K| = 9` and `H ≅ SL(2,5)`.
This is exactly the statement of `Glauberman.lemma6_2` in the imported module
`Glauberman.Lemma6_2`.

**Why it is needed.**  Step 6 of the minimal-counterexample argument (tex L1743–L1755)
applies Lemma 6.2 to the following data: the elementary Abelian `p`-group `H` considered
as a vector space `V := Additive ↥H` over `GF(p)`, and the automorphisms `conjAut x`,
`conjAut y` of `H` induced by conjugation by the generators `x`, `y` of the acting group
(both in `N_G(H)`), with `(conjAut x - 1)² = 0 = (conjAut y - 1)²` following from
`[H,x,x] = [H,y,y] = 1` and `conjAut x - 1 ≠ 0 ≠ conjAut y - 1` from `x, y ∉ C_G(H)`.
The body bundles the four inputs into `Lemma62Data` and unwraps the conclusion through
the exposed `Lemma62Data.lin` definition. -/
public theorem lemma6_2_application {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] {H : Type*}
    [Group H] (ρ : H →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hfaith : Function.Injective ρ)
    (hirr : ∀ W : Submodule (ZMod p) V,
      (∀ h : H, ∀ v : V, v ∈ W →
        ((ρ h : LinearMap.GeneralLinearGroup (ZMod p) V) : V →ₗ[ZMod p] V) v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hgen : ∃ x y : H,
      Subgroup.closure ({x, y} : Set H) = ⊤ ∧
        ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 ∧ (ρ x : V →ₗ[ZMod p] V) - 1 ≠ 0 ∧
        ((ρ y : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 ∧ (ρ y : V →ₗ[ZMod p] V) - 1 ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K),
      ∃ φ : K →ₐ[ZMod p] Module.End (ZMod p) V,
        Function.Injective φ ∧
          (∀ h : H, ∀ k : K,
            ((ρ h : V →ₗ[ZMod p] V) : Module.End (ZMod p) V) * φ k =
              φ k * ((ρ h : V →ₗ[ZMod p] V) : Module.End (ZMod p) V)) ∧
          letI : Module K V := Glauberman.moduleOfAlgHom φ
          Module.finrank K V = 2 ∧
            (Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∨
              (Nat.card K = 9 ∧ Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))) := by
  let D : Lemma62Data p hpodd V H :=
    { ρ := ρ
      faithful := hfaith
      irreducible := hirr
      two_generators := hgen }
  simpa only [Lemma62Data.lin] using (lemma6_2_part_c hpodd D)

/- **Proof transcription for the minimal-counterexample half of Lemma 6.3**
(the `(a) ⟹ (b)` contrapositive).

**Statement.**  For an odd prime `p` and a finite group `G`: if some subquotient of `G`
is not `p`-stable, then `Qd(p)` is involved in `G`.

**Why it is needed.**  This is the entire converse direction of Lemma 6.3
(`refs/glauberman-p-stable.tex` L1667–L1793), the long minimal-counterexample argument.
The eight steps of the paper's proof are transcribed below; their formal implementation
is split across `Lemma6_3Steps1To5`, `Lemma63Step6Aligned`, `Lemma6_3Step7`,
`Lemma63Step8`, and `Lemma63MinimalBadEquiv`.

**Proof (paper L1667–L1793).**  Assume some subquotient `Q` of `G` is not `p`-stable and
take `Q` of minimal order (well-founded on `Nat.card`); we show `Q ≅ Qd(p)`.

1. *Reduction to `Q = G`* (L1671–L1693).  Unfolding `pStable`, `¬ pStable p Q` gives
   `M ∈ M_p(Q)` with `¬ pStableLocal p M`; if `M ≠ Q`, `M` is a proper subquotient of
   `Q`, hence `p`-stable by minimality — contradiction.  So `Q ∈ M_p(Q)`, i.e.
   `O_p(Q) ≠ 1`, and `¬ pStableLocal p Q`.  Choose a `p`-subgroup `H` of `Q` of least
   order subject to: (i) `O_{p'}(Q)H ⊴ Q`, and (ii) `N(H)` contains `x` with
   `[H,x,x] = 1` and the coset of `C(H)` containing `x` outside
   `O_p(N(H)/C(H))` (the unpacked `¬ pStableLocal` failure; least order via
   well-founded selection).
2. *`O_{p'}(Q) = 1`, `C = C(H)`, `H ⊴ Q`* (L1693–L1712).  Let `M = O_{p'}(Q)`,
   `C = C_Q(MH/M)`.  Frattini: `Q = MHN(H) = MN(H)` (6.1); hence
   `C = M(N(H) ∩ C) = MC(H)` (6.2).  Barring by `M`: `N(H)/C(H) ≅ N_{Q̄}(H̄)/C_{Q̄}(H̄)`,
   so `Q̄` is not `p`-stable; since `|Q̄| < |Q|` unless `M = 1`, minimality gives
   `M = 1`; then `C = C(H)` and `H ⊴ Q`.
3. *`C` is a `p`-group* (L1712–L1721).  For any prime `r`, take `R ∈ Syl_r(C)`;
   Frattini: `Q = C·N(R)` (6.1 applied inside).  Write `x = cy` (`c ∈ C`, `y ∈ N(R)`);
   then `[H,y,y] = 1`, and `y` maps onto the coset of `x` in `Q/C`, while `N(R)` maps
   onto `Q/C`; also `H ≤ C(R) ≤ N(R)`.  Hence `N(R)` is not `p`-stable, so
   `Q = N(R)` (minimality: `N(R) < Q` would be `p`-stable).  As `r` is arbitrary and
   `O_{p'}(Q) = 1`, `C` is a `p`-group (a prime `r ≠ p` dividing `|C|` gives a
   non-trivial `R`, and then `Q = N(R)` forces `R ⊴ Q`, so `R ≤ O_{p'}(Q) = 1` by the
   coprime-normal-subgroup lemma — contradiction).
4. *`H` is elementary Abelian, `Q` irreducible on `H`* (L1721–L1737).  If `Q` has a
   normal subgroup `1 < K < H`, take `K` minimal normal; `K` is elementary Abelian and
   `Q` irreducible on it.  Lemma 3.4
   (`Glauberman.Lemma3_4.fixedPoints_eq_bot_of_irreducible_of_normal_pSubgroup` on the
   faithful irreducible action `Q/C(K)` on `K`) gives `O_p(Q/C(K)) = 1` (6.3).
   `[K,x,x] ≤ [H,x,x] = 1` gives `x ∈ C(K)` by (6.3) and the choice of `H`.  Take
   `N ≤ Q` with `C_Q(H/K) ≤ N` and `N/C_Q(H/K) = O_p(Q/C_Q(H/K))`; since `Q/K` is
   `p`-stable (minimality, `K ≠ 1`) and `[H,x,x] = 1 ≤ K`, we get `x ∈ N`, hence
   `x ∈ C_N(K)`.  With `D = C_Q(H/K)`: `N/D` is a `p`-group, so `C_N(K)D/D` and
   `C_N(K)/(C_N(K) ∩ D)` are `p`-groups; and
   `(C_N(K) ∩ D)/C(H) = (C_Q(K) ∩ C_Q(H/K))/C_Q(H)` is a `p`-group by **Lemma 5.3
   applied with `S := H`, `P := K`** (`Glauberman.Lemma5_3.lemma5_3`: automorphisms of
   the `p`-group `H` fixing `K` pointwise and inducing the identity on `H/K` form a
   `p`-group, via `mem_lemma5_3Centralizer`; the group in question embeds into
   `lemma5_3Centralizer K` under the natural map `N_Q(H) → Aut H`).  Since `C` is a
   `p`-group (step 3), `C_N(K) ∩ D` and hence `C_N(K)` are `p`-groups, so
   `x ∈ C_N(K) ≤ O_p(Q)` — impossible because `O_p(Q)C/C ≤ O_p(Q/C)` and the coset of
   `x` lies outside `O_p(N(H)/C(H)) = O_p(Q/C)`.  (Note: the file header of
   `Glauberman/Lemma5_3.lean` names `C_N(K)/(C_N(K) ∩ D)` as the Lemma-5.3 application;
   that is a docstring inaccuracy — the Lemma-5.3 application is the
   `(C_N(K) ∩ D)/C(H)` quotient, with `S := H`, `P := K`; the `C_N(K)/(C_N(K) ∩ D)`
   part is a `p`-group because `N/D` is.)
   Hence no such `K` exists; a minimal normal subgroup of `Q` inside `H` must be `H`
   itself, so `H` is elementary Abelian and `Q` is irreducible on `H` (6.4).
5. *`Q = ⟨x, x^w, C⟩` for a suitable `w`* (L1737–L1743).  Since `xC ∉ O_p(Q/C)`, the
   contrapositive of Lemma 6.1 (`Glauberman.Lemma6_1.baer_contrapositive`) gives
   `w ∈ Q` with `G* = ⟨x, x^w, C⟩` such that `G*/C` is not a `p`-group.  Then
   `[H,x,x] = 1` and `[H,x^w,x^w] = [H^w,x^w,x^w] = [H,x,x]^w = 1` show `G*` is not
   `p`-stable, so `Q = G*` by minimality (6.5).
6. *The structure of `Q/C`* (L1743–L1755).  View `H` as a vector space over `GF(p)`;
   let `y` be conjugation by `x` on `H`.  For each `h ∈ H`, `h^{(y-1)²} = [h,x,x] = 1`,
   so `(y-1)² = 0` and `y^p - 1 = (y-1)^p = (y-1)²(y-1)^{p-2} = 0` (Frobenius in
   characteristic `p`); the same holds for the automorphism of `x^w`.  By (6.4), (6.5)
   and Lemma 6.2 (`lemma6_2_application` above), there is a finite field
   `K₀` such that `H` is two-dimensional over `K₀` and `Q/C ≅ SL(2,K₀)` (or, if
   `|K₀| = 9`, `Q/C ≅ SL(2,5)`); `y` lies in a subgroup `L ≤ Q/C` isomorphic to
   `SL(2,p)`.  Since `y ∉ O_p(L)` (a non-trivial transvection, and `O_p(SL(2,p)) = 1`),
   and every proper subgroup of `Q` is `p`-stable (minimality), `L = Q/C`, hence
   `K₀ = GF(p)`.
7. *`C = H`* (L1755–L1775).  `Q/C ≅ SL(2,p)` has a unique subgroup `T/C` of order 2
   (the centre `{±I}`), whose non-identity element acts on `H` as `h ↦ h⁻¹`.  Let
   `T₂ ∈ Syl₂(T)`; Frattini: `Q = T·N(T₂) = C·T₂·N(T₂) = C·N(T₂)`, so `N(T₂)H` is not
   `p`-stable and `Q = N(T₂)H` (6.6).  Let `E = C ∩ N(T₂)`: `E ⊴ Q` (normalized by
   `N(T₂)`, centralized by `H`), `[E,T₂] ≤ C ∩ T₂ ≤ O_p(Q) ∩ T₂ = 1`, and
   `E ∩ H ≤ C(T₂) ∩ H = 1`; by (6.6), `C = E·H`, so `C = E × H`; `Q/E` is not
   `p`-stable, so `E = 1` (minimality) and `C = H`.
8. *`Q ≅ Qd(p)`* (L1775–L1793).  `Q = H ⋊ (Q/C)` with `H` elementary Abelian
   (a vector space over `GF(p)`, two-dimensional by step 6) and `Q/C ≅ SL(2,p)` acting
   naturally; this is exactly `Qd(p) = (Multiplicative (Fin 2 → ZMod p)) ⋊ SL(2,p)`,
   assembled via the isomorphism `H ≃ (Fin 2 → ZMod p)` (from the two-dimensional
   structure) and `Q/C ≅ SL(2,p)`.  Hence `Involved (Qd p) G` (with the witnessing
   subquotient `Q` of `G`).

The formal proof follows these steps through the split modules listed above; Step 6
uses Lemma 6.2 and the exceptional-case cardinality argument, while Step 8 reconstructs
the semidirect product explicitly. -/
/-! ## Centralizer transport (local copy)

`Glauberman.pStability` (which proves `map_centralizer_eq_of_equiv`) was mid-edit and
unbuildable when this file was written (its `le_normalizer_of_normal_subgroupOf_of_le`
did not elaborate), so it is not imported; the lemma is re-proved here under a distinct
name, keeping this file self-contained.  (The dependency has since been reported fixed;
the copy is kept to avoid coupling this file to its import graph.) -/

/-- The centralizer of a subgroup is transported along a group isomorphism: for
`e : G ≃* G'` and `P ≤ G`, one has `C_G(P)ᵉ = C_{G'}(Pᵉ)`. -/
private theorem centralizer_map_eq_of_equiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (P : Subgroup G) :
    (Subgroup.centralizer (P : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
  refine le_antisymm ?_ ?_
  · simpa [Subgroup.coe_map] using
      (Subgroup.map_centralizer_le_centralizer_image (s := (P : Set G)) (f := e.toMonoidHom))
  · intro y hy
    refine ⟨e.symm y, ?_, ?_⟩
    · intro h hh
      have hy' := hy (e h) (by exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
      apply e.injective
      rw [map_mul, map_mul]
      simp [hy']
    · simp

/-! ## `Involved` plumbing -/

/-- If `H` and `H'` are isomorphic, then `H` is involved in `G` iff `H'` is involved in
`G` (an involvement witness for one transports along the isomorphism). -/
public theorem Involved_iff_of_mulEquiv {H H' G : Type*} [Group H] [Group H'] [Group G]
    (e : H ≃* H') : Involved H G ↔ Involved H' G := by
  constructor
  · intro h
    rcases h with ⟨K, N, hN, hq⟩
    let : N.Normal := hN
    rcases hq with ⟨f⟩
    exact ⟨K, N, hN, ⟨f.trans e⟩⟩
  · intro h
    rcases h with ⟨K, N, hN, hq⟩
    let : N.Normal := hN
    rcases hq with ⟨f⟩
    exact ⟨K, N, hN, ⟨f.trans e.symm⟩⟩

/-- Every finite group is involved in itself: `H ≅ H/1` is a subquotient of `H`. -/
public theorem involved_self (H : Type*) [Group H] : Involved H H := by
  refine ⟨(⊤ : Subgroup H), ⊥, inferInstance,
    ⟨QuotientGroup.quotientBot.trans (Subgroup.topEquiv (G := H))⟩⟩

/-- Every subgroup of a group is involved in it: `K = K/1`. -/
public theorem involved_of_subgroup {G : Type*} [Group G] (K : Subgroup G) :
    Involved (↥K) G := by
  refine ⟨K, ⊥, inferInstance, ⟨QuotientGroup.quotientBot (G := ↥K)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Monotonicity of `Involved`.**  If `H` is involved in the subgroup `K` of `G`, then
`H` is involved in `G`: a subquotient `A ⧸ B` of `K` maps isomorphically onto the
subquotient `A₀ ⧸ B₀` of `G`, where `A₀ = A.map K.subtype` and `B₀` is the image of `B`
under the same map (the map of subgroups under an injective homomorphism preserves
subquotients). -/
public theorem involved_of_involved_subgroup {H G : Type*} [Group H] [Group G]
    {K : Subgroup G} (h : Involved H (↥K)) : Involved H G := by
  rcases h with ⟨A, B, hB, hq⟩
  let : B.Normal := hB
  rcases hq with ⟨e⟩
  -- `A₀ = A.map K.subtype` is a subgroup of `G`; `B₀ = B.map f'` (with
  -- `f' : ↥A →* ↥A₀` the corestriction of `K.subtype.comp A.subtype`) is a normal
  -- subgroup of `A₀` (the image of the normal subgroup `B` under the surjective
  -- homomorphism `f'`), and `A ⧸ B ≃ A₀ ⧸ B₀` via the induced isomorphism.
  let A₀ : Subgroup G := A.map K.subtype
  let f : ↥A →* G := K.subtype.comp A.subtype
  have hmem_f : ∀ a : ↥A, f a ∈ A₀ := by
    intro a
    exact Subgroup.mem_map.mpr ⟨a, by simp, rfl⟩
  let f' : ↥A →* ↥A₀ := f.codRestrict A₀ hmem_f
  let B₀ : Subgroup A₀ := B.map f'
  have hf'_inj : Function.Injective f' := by
    intro a b hab
    apply Subtype.ext
    apply K.subtype_injective
    simpa [f, f'] using (congrArg Subtype.val hab)
  have hf'_surj : Function.Surjective f' := by
    intro y
    rcases (Subgroup.mem_map.mp y.2) with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change f ⟨x, hx⟩ = y.1
    simpa [f] using hxy
  have hB₀_normal : B₀.Normal :=
    Subgroup.Normal.map hB f' hf'_surj
  let eA : ↥A ≃* ↥A₀ := MulEquiv.ofBijective f' ⟨hf'_inj, hf'_surj⟩
  have heA : B.map eA.toMonoidHom = B₀ := by
    -- `eA` agrees with `f'` on elements
    dsimp [B₀]
    apply congrArg (fun g : ↥A →* ↥A₀ => B.map g)
    ext a
    simp [eA]
  let Φ : ↥A ⧸ B ≃* ↥A₀ ⧸ B₀ :=
    QuotientGroup.congr (G := ↥A) (H := ↥A₀) (G' := B) (H' := B₀) eA heA
  -- `A₀ ⧸ B₀ ≃* H`
  have hq' : Nonempty (A₀ ⧸ B₀ ≃* H) := ⟨Φ.symm.trans e⟩
  exact ⟨A₀, B₀, hB₀_normal, hq'⟩

/-! ## `pStable`/`pStableLocal` are invariant under isomorphism -/

/-- The normalizer of a subgroup is transported along a group isomorphism. -/
private theorem normalizer_map_eq_of_equiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (P : Subgroup G) :
    (Subgroup.normalizer (P : Set G)).map e.toMonoidHom =
      Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
  simpa using (Subgroup.map_equiv_normalizer_eq P e)

/-- The image of a subgroup under a group isomorphism is again normal when the original
is normal (transport of normality along an isomorphism). -/
private theorem map_normal_of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {P : Subgroup G} [P.Normal] : (P.map e.toMonoidHom : Subgroup G').Normal := by
  exact Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective

set_option backward.isDefEq.respectTransparency false in
/-- Forward direction of `pStableLocal_iso`: `pStableLocal p G` implies
`pStableLocal p G'` along a group isomorphism `e : G ≃* G'`.  Every hypothesis of the
definition is transported: the subgroup `P = P'.map e.symm`, the element
`x = e.symm x'`, the normalizer/centralizer quotients, and the `pCore` conclusion. -/
private theorem pStableLocal_iso_forward {p : ℕ} [Fact p.Prime] {G G' : Type*}
    [Group G] [Group G'] (e : G ≃* G') :
    pStableLocal p G → pStableLocal p G' := by
  intro hloc P' hP'p hP'n x' hx' hcomm'
  let P : Subgroup G := P'.map e.symm.toMonoidHom
  have hPp : IsPGroup p P := by
    dsimp [P]
    exact IsPGroup.map hP'p e.symm.toMonoidHom
  have hPn : (pPrimeCore p G ⊔ P).Normal := by
    have hpc : pPrimeCore p G = (pPrimeCore p G').map e.symm.toMonoidHom := by
      exact (pPrimeCore_map_iso (G := G') (G' := G) (p := p) (f := e.symm)).symm
    have hmap : ((pPrimeCore p G' ⊔ P').map e.symm.toMonoidHom).Normal :=
      Subgroup.Normal.map hP'n e.symm.toMonoidHom e.symm.surjective
    rw [Subgroup.map_sup, ← hpc] at hmap
    simpa [P] using hmap
  let x : G := e.symm x'
  have hNmap : (Subgroup.normalizer (P' : Set G')).map e.symm.toMonoidHom =
      Subgroup.normalizer (P : Set G) := by
    simpa [P] using (normalizer_map_eq_of_equiv (e := e.symm) P')
  have hx : x ∈ Subgroup.normalizer (P : Set G) := by
    dsimp [x]
    rw [← hNmap]
    exact Subgroup.mem_map.mpr ⟨x', hx', rfl⟩
  have hcomm : ⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ := by
    have hzx : Subgroup.zpowers x = (Subgroup.zpowers x').map e.symm.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    calc
      ⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆
          = ⁅⁅P'.map e.symm.toMonoidHom, (Subgroup.zpowers x').map e.symm.toMonoidHom⁆,
              (Subgroup.zpowers x').map e.symm.toMonoidHom⁆ := by
        simp [P, hzx]
      _ = (⁅⁅P', Subgroup.zpowers x'⁆, Subgroup.zpowers x'⁆).map e.symm.toMonoidHom := by
        rw [Subgroup.map_commutator, Subgroup.map_commutator]
      _ = ⊥ := by
        rw [hcomm', Subgroup.map_bot]
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have hconcl : QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩ ∈
      pCore p (N ⧸ C.subgroupOf N) := by
    simpa [N, C] using (hloc P hPp hPn x hx hcomm)
  -- transport the conclusion to `G'`
  let N' : Subgroup G' := Subgroup.normalizer (P' : Set G')
  let C' : Subgroup G' := Subgroup.centralizer (P' : Set G')
  have hPmap : P.map e.toMonoidHom = P' := by
    dsimp [P]
    rw [Subgroup.map_map]
    have hcomp : (e.toMonoidHom.comp e.symm.toMonoidHom : G' →* G') = MonoidHom.id G' := by
      ext y
      simp
    simp
  have hNmap' : N.map e.toMonoidHom = N' := by
    calc
      N.map e.toMonoidHom =
          Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
        simpa [N] using (normalizer_map_eq_of_equiv (e := e) P)
      _ = N' := by
        rw [hPmap]
  have hCmap : C.map e.toMonoidHom = C' := by
    calc
      C.map e.toMonoidHom =
          Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
        simpa [C] using (centralizer_map_eq_of_equiv (e := e) P)
      _ = C' := by
        rw [hPmap]
  -- the induced isomorphism `↥N ≃* ↥N'`
  let fN : ↥N →* ↥N' := (e.toMonoidHom.comp N.subtype).codRestrict N' (by
    intro y
    rw [← hNmap']
    exact Subgroup.mem_map.mpr ⟨y.1, y.2, rfl⟩)
  have hfN_inj : Function.Injective fN := by
    intro a b hab
    apply Subtype.ext
    apply e.injective
    have hv := congrArg Subtype.val hab
    simpa [fN] using hv
  have hfN_surj : Function.Surjective fN := by
    intro y
    have hyN : y.1 ∈ N.map e.toMonoidHom := by
      rw [hNmap']
      exact y.2
    rcases (Subgroup.mem_map.mp hyN) with ⟨n, hn, hn_eq⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    apply Subtype.ext
    simpa [fN] using hn_eq
  let eN : ↥N ≃* ↥N' := MulEquiv.ofBijective fN ⟨hfN_inj, hfN_surj⟩
  have he : (C.subgroupOf N).map eN.toMonoidHom = C'.subgroupOf N' := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      -- `eN z ∈ C'.subgroupOf N'` iff `(eN z : G') ∈ C'`
      apply Subgroup.mem_subgroupOf.mpr
      have hzC : (z.1 : G) ∈ C := (Subgroup.mem_subgroupOf.mp hz)
      have hmem : e z.1 ∈ C.map e.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨z.1, hzC, rfl⟩
      have hmem' : e z.1 ∈ C' := by
        rw [hCmap] at hmem
        exact hmem
      -- `(eN z : G') = e z.1`
      simpa [eN, fN] using hmem'
    · intro hy
      have hyC : y.1 ∈ C.map e.toMonoidHom := by
        have hyC' : y.1 ∈ C' := (Subgroup.mem_subgroupOf.mp hy)
        rw [hCmap]
        exact hyC'
      rcases (Subgroup.mem_map.mp hyC) with ⟨c, hc, hc_eq⟩
      have hyN : y.1 ∈ N.map e.toMonoidHom := by
        rw [hNmap']
        exact y.2
      rcases (Subgroup.mem_map.mp hyN) with ⟨n, hn, hn_eq⟩
      have hnc : n = c := by
        apply e.injective
        change e.toMonoidHom n = e.toMonoidHom c
        rw [hn_eq, ← hc_eq]
      have hcN : c ∈ N := by
        simpa [hnc] using hn
      refine ⟨⟨c, hcN⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
      apply Subtype.ext
      simpa [eN, fN] using hc_eq
  let Φ : ↥N ⧸ C.subgroupOf N ≃* ↥N' ⧸ C'.subgroupOf N' :=
    QuotientGroup.congr (G := ↥N) (H := ↥N') (G' := C.subgroupOf N) (H' := C'.subgroupOf N')
      eN he
  have hcore : (pCore p (N ⧸ C.subgroupOf N)).map Φ.toMonoidHom =
      pCore p (N' ⧸ C'.subgroupOf N') :=
    pCore_map_iso (G := ↥N ⧸ C.subgroupOf N) (G' := ↥N' ⧸ C'.subgroupOf N') (p := p)
      (f := Φ)
  have hmem : Φ (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) ∈
      pCore p (N' ⧸ C'.subgroupOf N') := by
    rw [← hcore]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩, hconcl, rfl⟩
  have happly : Φ (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) =
      QuotientGroup.mk' (C'.subgroupOf N') ⟨x', hx'⟩ := by
    dsimp [Φ]
    congr 1
    apply Subtype.ext
    dsimp [eN, fN, x]
    exact (e.apply_symm_apply x')
  rw [happly] at hmem
  simpa [N', C'] using hmem

/-- `pStableLocal` is invariant under group isomorphism. -/
public theorem pStableLocal_iso {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') : pStableLocal p G ↔ pStableLocal p G' := by
  constructor
  · exact pStableLocal_iso_forward e
  · exact pStableLocal_iso_forward e.symm

/-- Choose a non-`p`-stable subquotient of least cardinality.  Every strictly
smaller subquotient of the chosen group is then `p`-stable. -/
private theorem exists_minimal_bad_subquotient {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G]
    (hbad : ∃ (K : Subgroup G) (N : Subgroup K) (hN : N.Normal),
      letI : N.Normal := hN
      ¬ pStable p (K ⧸ N)) :
    ∃ (K : Subgroup G) (N : Subgroup K) (hN : N.Normal),
      letI : N.Normal := hN
      ¬ pStable p (K ⧸ N) ∧
        ∀ (A : Subgroup (K ⧸ N)) (B : Subgroup A) [B.Normal],
          Nat.card (A ⧸ B) < Nat.card (K ⧸ N) → pStable p (A ⧸ B) := by
  classical
  let Bad : ℕ → Prop := fun n =>
    ∃ (K : Subgroup G) (N : Subgroup K) (hN : N.Normal),
      let : N.Normal := hN
      Nat.card (K ⧸ N) = n ∧ ¬ pStable p (K ⧸ N)
  have hBad : ∃ n, Bad n := by
    rcases hbad with ⟨K, N, hN, hunstable⟩
    let : N.Normal := hN
    exact ⟨Nat.card (K ⧸ N), K, N, hN, rfl, hunstable⟩
  rcases Nat.find_spec hBad with ⟨K, N, hN, hcard, hunstable⟩
  let : N.Normal := hN
  refine ⟨K, N, hN, hunstable, ?_⟩
  intro A B hB hlt
  let : B.Normal := hB
  by_contra hAB
  have hInvABQ : Involved (A ⧸ B) (K ⧸ N) :=
    ⟨A, B, hB, ⟨MulEquiv.refl (A ⧸ B)⟩⟩
  have hInvABK : Involved (A ⧸ B) K :=
    involved_of_involved_quotient N hInvABQ
  have hInvABG : Involved (A ⧸ B) G :=
    involved_of_involved_subgroup hInvABK
  rcases hInvABG with ⟨K', N', hN', ⟨e⟩⟩
  let : N'.Normal := hN'
  have hunstable' : ¬ pStable p (K' ⧸ N') := by
    intro hstable'
    exact hAB ((pStable_iso e).mp hstable')
  have hcard' : Nat.card (K' ⧸ N') = Nat.card (A ⧸ B) :=
    Nat.card_congr e.toEquiv
  have hBad' : Bad (Nat.card (A ⧸ B)) :=
    ⟨K', N', hN', hcard', hunstable'⟩
  have hmin : Nat.find hBad ≤ Nat.card (A ⧸ B) :=
    Nat.find_min' hBad hBad'
  have hfindCard : Nat.find hBad = Nat.card (K ⧸ N) := hcard.symm
  rw [hfindCard] at hmin
  exact (not_le_of_gt hlt) hmin

/-! ## The minimal-counterexample implication -/

/-- If an odd-prime subquotient of `G` is not `p`-stable, then `Qd(p)` is involved in
`G`.  Choose a bad subquotient of least cardinality, apply the completed eight-step
classification to identify it with `Qd(p)`, and lift involvement through its quotient
and subgroup witnesses. -/
public theorem qd_involved_of_not_pStable_subquotient {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) {G : Type*} [Group G] [Finite G] :
    (∃ (K : Subgroup G) (N : Subgroup K) (hN : N.Normal),
        letI : N.Normal := hN
        ¬ pStable p (K ⧸ N)) →
      Involved (Qd p) G := by
  intro hbad
  obtain ⟨K, N, hN, hQbad, hmin⟩ :=
    exists_minimal_bad_subquotient hbad
  let : N.Normal := hN
  obtain ⟨e⟩ := minimal_bad_group_equiv_qd hpodd hQbad hmin
  have hInvQ : Involved (Qd p) (K ⧸ N) :=
    (Involved_iff_of_mulEquiv e).mp (involved_self (K ⧸ N))
  have hInvK : Involved (Qd p) K :=
    involved_of_involved_quotient N hInvQ
  exact involved_of_involved_subgroup hInvK

/-! ## Lemma 6.3 -/

/-- **Lemma 6.3** ([6], §6, p. 1122; `refs/glauberman-p-stable.tex` L1656–L1793): let `p`
be an odd prime and `G` a finite group.  Then `Qd(p)` is not involved in `G` if and only
if every subquotient of `G` is `p`-stable:

    (¬ Involved (Qd p) G) ↔ ∀ (K : Subgroup G) (N : Subgroup K) [hN : N.Normal], pStable p (K ⧸ N)

The forward direction is the completed minimal-counterexample argument
`qd_involved_of_not_pStable_subquotient`; the backward direction uses that
`Qd(p)` is not `p`-stable (`qd_not_pStable`) and that `pStable` is
invariant under isomorphism (`pStable_iso`, proved above). -/
public theorem lemma6_3 {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] :
    (¬ Involved (Qd p) G) ↔
      ∀ (K : Subgroup G) (N : Subgroup K) [_hN : N.Normal], pStable p (K ⧸ N) := by
  constructor
  · intro hInv K N hN
    let : N.Normal := inferInstance
    by_contra h
    exact hInv (qd_involved_of_not_pStable_subquotient hpodd ⟨K, N, hN, h⟩)
  · intro hb hInv
    rcases hInv with ⟨K, N, hN, hq⟩
    let : N.Normal := hN
    rcases hq with ⟨e⟩
    have hstab : pStable p (K ⧸ N) := hb K N
    have hqd : pStable p (Qd p) := (pStable_iso (G := K ⧸ N) (G' := Qd p) e).1 hstab
    exact qd_not_pStable hpodd hqd

-- Axiom audit: the minimal-counterexample implication, Lemma 6.2 application,
-- `qd_not_pStable`, and the isomorphism/involvement plumbing are all sorry-free.
-- The exported theorem chain uses only `propext`, `Classical.choice`, and `Quot.sound`.
#print axioms qd_not_pStable
#print axioms lemma6_2_application
#print axioms qd_involved_of_not_pStable_subquotient
#print axioms lemma6_3
#print axioms pStable_iso
#print axioms pStableLocal_iso
#print axioms Involved_iff_of_mulEquiv
#print axioms involved_self
#print axioms involved_of_subgroup
#print axioms involved_of_involved_subgroup

end CFSG.Glauberman

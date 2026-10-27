module

public import CFSG.RankThree.PartOne.D4RC.ParaLang
public import Mathlib.FieldTheory.Finite.Basic
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.D4RC

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.SeitzReduction

open scoped CFSG.ConvolutionPoints

local notation "D4T" => TwistTag.D4.tag

variable {L : Type} [Field L] [CharP L 2]


private abbrev rcdNode (i : Fin 4) : Fin (Tag.rank D4T) := i

theorem rcd_exists_smul_highRoot_single (j : Fin (Tag.rank D4T)) :
    ∃ v : WeylGroup D4T, v • highRoot D4T = Pi.single j 1 := by
  have h2 : (simple D4T (rcdNode 3) * simple D4T (rcdNode 1) * simple D4T (rcdNode 0) *
      simple D4T (rcdNode 2)) • highRoot D4T = Pi.single (rcdNode 2) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  have h0 : (simple D4T (rcdNode 2) * simple D4T (rcdNode 0)) •
      (Pi.single (rcdNode 2) 1 : Fin (Tag.rank D4T) → ℤ) = Pi.single (rcdNode 0) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  have h1 : (simple D4T (rcdNode 2) * simple D4T (rcdNode 1)) •
      (Pi.single (rcdNode 2) 1 : Fin (Tag.rank D4T) → ℤ) = Pi.single (rcdNode 1) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  have h3 : (simple D4T (rcdNode 2) * simple D4T (rcdNode 3)) •
      (Pi.single (rcdNode 2) 1 : Fin (Tag.rank D4T) → ℤ) = Pi.single (rcdNode 3) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  have hj : ∀ i : Fin (Tag.rank D4T),
      i = rcdNode 0 ∨ i = rcdNode 1 ∨ i = rcdNode 2 ∨ i = rcdNode 3 := by decide
  rcases hj j with rfl | rfl | rfl | rfl
  · exact ⟨_, by rw [mul_smul, h2, h0]⟩
  · exact ⟨_, by rw [mul_smul, h2, h1]⟩
  · exact ⟨_, h2⟩
  · exact ⟨_, by rw [mul_smul, h2, h3]⟩

theorem rcd_exists_smul_highRoot {β : Fin (Tag.rank D4T) → ℤ} (hβ : IsRoot D4T β) :
    ∃ w : WeylGroup D4T, w • highRoot D4T = β := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨v, hv⟩ := rcd_exists_smul_highRoot_single j
  exact ⟨w * v, by rw [mul_smul, hv]⟩

theorem rcd_F_conj_of_fixed {F : ModGL D4T L →* ModGL D4T L} {n g₀ z : ModGL D4T L}
    (hFg₀ : F g₀ = g₀ * n) (hz : n * F z * n⁻¹ = z) : F (g₀ * z * g₀⁻¹) = g₀ * z * g₀⁻¹ := by
  have hFz : F z = n⁻¹ * z * n :=
    calc F z = n⁻¹ * (n * F z * n⁻¹) * n := by group
      _ = n⁻¹ * z * n := by rw [hz]
  rw [map_mul, map_mul, map_inv, hFg₀, hFz]
  group

theorem rcd_exists_fixed_conj [IsAlgClosed L] {f : ℕ} (hf : 1 ≤ f) {n g₀ h : ModGL D4T L}
    (hg₀ : g₀ ∈ adjointGroup D4T L)
    (hFg₀ : twistHom TwistTag.D4 L (iterateFrobenius L 2 f) g₀ = g₀ * n)
    (hh : h ∈ adjointGroup D4T L) {β : Fin (Tag.rank D4T) → ℤ} (hβ : IsRoot D4T β) {e : L}
    (he : e ≠ 0)
    (hz : n * twistHom TwistTag.D4 L (iterateFrobenius L 2 f)
        (h * pinnedX D4T L β e * h⁻¹) * n⁻¹ = h * pinnedX D4T L β e * h⁻¹) :
    ∃ k ∈ adjointGroup D4T L, twistHom TwistTag.D4 L (iterateFrobenius L 2 f) k = k ∧
      (rootSubgroup D4T L β).map (MulAut.conj (g₀ * h)).toMonoidHom =
        (rootSubgroup D4T L (highRoot D4T)).map (MulAut.conj k).toMonoidHom := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  set F := twistHom TwistTag.D4 L (iterateFrobenius L 2 f) with hF
  obtain ⟨w, hw⟩ := rcd_exists_smul_highRoot hβ
  have hnw : canonicalRep (coxeterSystem D4T) L w ∈ adjointGroup D4T L :=
    monomialSubgroup_le_adjointGroup' (canonicalRep_mem_monomialSubgroup L w)
  have hconj : ∀ c, canonicalRep (coxeterSystem D4T) L w * pinnedX D4T L (highRoot D4T) c *
      (canonicalRep (coxeterSystem D4T) L w)⁻¹ = pinnedX D4T L β c := fun c => by
    rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_highRoot D4T) c, hw]
  set d := g₀ * h * canonicalRep (coxeterSystem D4T) L w with hd
  have hdG : d ∈ adjointGroup D4T L := mul_mem (mul_mem hg₀ hh) hnw
  have hdx : d * pinnedX D4T L (highRoot D4T) e * d⁻¹ =
      g₀ * (h * pinnedX D4T L β e * h⁻¹) * g₀⁻¹ := by
    calc d * pinnedX D4T L (highRoot D4T) e * d⁻¹
        = g₀ * h * (canonicalRep (coxeterSystem D4T) L w * pinnedX D4T L (highRoot D4T) e *
            (canonicalRep (coxeterSystem D4T) L w)⁻¹) * h⁻¹ * g₀⁻¹ := by
          rw [hd]
          group
      _ = g₀ * (h * pinnedX D4T L β e * h⁻¹) * g₀⁻¹ := by
          rw [hconj]
          group
  have hst : F (d * pinnedX D4T L (highRoot D4T) e * d⁻¹) =
      d * pinnedX D4T L (highRoot D4T) e * d⁻¹ := by
    rw [hdx]
    exact rcd_F_conj_of_fixed hFg₀ hz
  obtain ⟨k, hk, hFk, hkU⟩ := rcp_exists_fixed_conj hf hdG he hst
  refine ⟨k, hk, hFk, ?_⟩
  rw [hkU]
  have hcomp : (MulAut.conj d).toMonoidHom =
      (MulAut.conj (g₀ * h)).toMonoidHom.comp
        (MulAut.conj (canonicalRep (coxeterSystem D4T) L w)).toMonoidHom :=
    MonoidHom.ext fun x => by simp [hd, mul_assoc]
  rw [hcomp, ← Subgroup.map_map,
    (canonical_weyl_root_transport D4T L).2.1 w _ (isRoot_highRoot D4T), hw]

theorem rcd_fixed_set_finite {q : ℕ} (hq : 1 < q) :
    {c : L | c ^ q = c}.Finite ∧ {c : L | c ^ q = c}.ncard ≤ q := by
  classical
  have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hsub : {c : L | c ^ q = c} ⊆
      (((Polynomial.X ^ q - Polynomial.X : Polynomial L).roots.toFinset : Finset L) : Set L) := by
    intro c hc
    have hc' : c ^ q = c := hc
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    exact sub_eq_zero.2 hc'
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc {c : L | c ^ q = c}.ncard
      ≤ (((Polynomial.X ^ q - Polynomial.X : Polynomial L).roots.toFinset : Finset L) :
          Set L).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Polynomial.X ^ q - Polynomial.X : Polynomial L).roots.toFinset.card :=
        Set.ncard_coe_finset _
    _ ≤ Multiset.card (Polynomial.X ^ q - Polynomial.X : Polynomial L).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial L).natDegree := Polynomial.card_roots' _
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq L hq

theorem rcd_mem_fixed_iff [IsAlgClosed L] {f : ℕ} (hf : 1 ≤ f) {n g₀ h : ModGL D4T L}
    (hg₀ : g₀ ∈ adjointGroup D4T L)
    (hFg₀ : twistHom TwistTag.D4 L (iterateFrobenius L 2 f) g₀ = g₀ * n)
    (hh : h ∈ adjointGroup D4T L) {β : Fin (Tag.rank D4T) → ℤ} (hβ : IsRoot D4T β) {e : L}
    (he : e ≠ 0) {κ : Type} [Field κ] [Algebra κ L] (hκ : Nat.card κ = 2 ^ f)
    (hz : ∀ t : κ, n * twistHom TwistTag.D4 L (iterateFrobenius L 2 f)
        (h * pinnedX D4T L β (e * algebraMap κ L t) * h⁻¹) * n⁻¹ =
          h * pinnedX D4T L β (e * algebraMap κ L t) * h⁻¹) :
    ∃ k ∈ adjointGroup D4T L, twistHom TwistTag.D4 L (iterateFrobenius L 2 f) k = k ∧
      ∀ v : ModGL D4T L,
        (∃ t : κ, v = g₀ * (h * pinnedX D4T L β (e * algebraMap κ L t) * h⁻¹) * g₀⁻¹) ↔
          ∃ c : L, c ^ (2 ^ f) = c ∧ v = k * pinnedX D4T L (highRoot D4T) c * k⁻¹ := by
  set F := twistHom TwistTag.D4 L (iterateFrobenius L 2 f) with hF
  have hz1 := hz 1
  rw [map_one, mul_one] at hz1
  obtain ⟨k, hk, hFk, hkU⟩ := rcd_exists_fixed_conj hf hg₀ hFg₀ hh hβ he hz1
  refine ⟨k, hk, hFk, fun v => ?_⟩
  have hFθ : ∀ c : L, F (k * pinnedX D4T L (highRoot D4T) c * k⁻¹) =
      k * pinnedX D4T L (highRoot D4T) (c ^ (2 ^ f)) * k⁻¹ := fun c => by
    rw [map_mul, map_mul, map_inv, hFk, hF, rcp_twistHom_pinnedX_highRoot, iterateFrobenius_def]
  have hmem : ∀ t : κ, ∃ c : L, c ^ (2 ^ f) = c ∧
      g₀ * (h * pinnedX D4T L β (e * algebraMap κ L t) * h⁻¹) * g₀⁻¹ =
        k * pinnedX D4T L (highRoot D4T) c * k⁻¹ := fun t => by
    have hmemU : (g₀ * h) * pinnedX D4T L β (e * algebraMap κ L t) * (g₀ * h)⁻¹ ∈
        (rootSubgroup D4T L (highRoot D4T)).map (MulAut.conj k).toMonoidHom := by
      rw [← hkU]
      exact ⟨_, mem_rootSubgroup.2 ⟨_, rfl⟩, rfl⟩
    obtain ⟨y, hy, hyv⟩ := hmemU
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
    have hv : g₀ * (h * pinnedX D4T L β (e * algebraMap κ L t) * h⁻¹) * g₀⁻¹ =
        k * pinnedX D4T L (highRoot D4T) c * k⁻¹ := by
      rw [← show (MulAut.conj k).toMonoidHom (pinnedX D4T L (highRoot D4T) c) =
        k * pinnedX D4T L (highRoot D4T) c * k⁻¹ from rfl, hyv]
      group
    refine ⟨c, ?_, hv⟩
    have hfix := rcd_F_conj_of_fixed hFg₀ (hz t)
    rw [hv, hFθ] at hfix
    have := pinnedX_injective D4T L (highRoot D4T) (mul_left_cancel (mul_right_cancel hfix))
    exact this
  choose c hcfix hcv using hmem
  have hinj : Function.Injective c := by
    intro t t' htt'
    have h1 : g₀ * (h * pinnedX D4T L β (e * algebraMap κ L t) * h⁻¹) * g₀⁻¹ =
        g₀ * (h * pinnedX D4T L β (e * algebraMap κ L t') * h⁻¹) * g₀⁻¹ := by
      rw [hcv, hcv, htt']
    have h2 : pinnedX D4T L β (e * algebraMap κ L t) = pinnedX D4T L β (e * algebraMap κ L t') :=
      calc pinnedX D4T L β (e * algebraMap κ L t)
          = h⁻¹ * (g₀⁻¹ * (g₀ * (h * pinnedX D4T L β (e * algebraMap κ L t) * h⁻¹) * g₀⁻¹) *
              g₀) * h := by group
        _ = h⁻¹ * (g₀⁻¹ * (g₀ * (h * pinnedX D4T L β (e * algebraMap κ L t') * h⁻¹) * g₀⁻¹) *
              g₀) * h := by rw [h1]
        _ = pinnedX D4T L β (e * algebraMap κ L t') := by group
    exact (algebraMap κ L).injective (mul_left_cancel₀ he (pinnedX_injective D4T L β h2))
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  obtain ⟨hfin, hcard⟩ := rcd_fixed_set_finite (L := L) hq
  have hfin' : Finite ↥{x : L | x ^ (2 ^ f) = x} := hfin.to_subtype
  let φ : κ → ↥{x : L | x ^ (2 ^ f) = x} := fun t => ⟨c t, hcfix t⟩
  have hφ : Function.Bijective φ := by
    refine Function.Injective.bijective_of_nat_card_le
      (fun t t' h => hinj (congrArg Subtype.val h)) ?_
    rw [hκ, Nat.card_coe_set_eq]
    exact hcard
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨c t, hcfix t, hcv t⟩
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨t, ht⟩ := hφ.2 ⟨c', hc'⟩
    refine ⟨t, ?_⟩
    rw [hcv t, show c t = c' from congrArg Subtype.val ht]

end CFSG.RankThree.PartOne.D4RC

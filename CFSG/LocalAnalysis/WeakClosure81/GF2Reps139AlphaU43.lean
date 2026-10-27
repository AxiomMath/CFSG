module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaE
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107TripleDefs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107TripleCost
import CFSG.Goldschmidt.Steps.G3b35Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private lemma w1369_mulAut_congr_conj {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (a : A) : MulAut.congr φ (MulAut.conj a) = MulAut.conj (φ a) := by
  ext b
  simp [MulAut.congr_apply, MulAut.conj_apply]

private lemma w1369_commutator_eq_top_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : commutator B = ⊤) : commutator A = ⊤ := by
  have hmap : (commutator A).map (e : A →* B) = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_equiv_top e]
    exact h
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : e x ∈ (commutator A).map (e : A →* B) := by rw [hmap]; trivial
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [e.injective hyx] at hy

theorem Std139.u43_not_mem (hgen : U43TripleGen) (hw2 : ∀ w : W, w ^ 2 = 1)
    (S : Std139 G X D s Y n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K)
    (hHat : ∃ (S' : Type) (_ : Group S'), LieModel S' .PSU 4 3 1 ∧ IsHat ↥K S')
    {d : MulAut W} (hd : d ∈ D) (hd1 : d ≠ 1) : d ∉ K := by
  intro hdK
  obtain ⟨S', hgrp, hLieS', hHat'⟩ := hHat
  letI : Group S' := hgrp
  obtain ⟨φ⟩ := hHat'.2.2
  have hLieK : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 4 3 1 :=
    LieModel.of_mulEquiv φ.symm hLieS'
  have hdOrd : orderOf d = 2 := orderOf_eq_prime (S.elem.2 d hd) hd1
  have hcost : E3.mQuot ⊤ (fixV (Subgroup.zpowers d)) ≤ 2 := by
    have h1 : E3.mQuot ⊤ Y = rkIdx Y := by
      rw [E3.mQuot, rkIdx, Subgroup.relIndex_top_right]
    rw [Std139.fixV_eq_axis hw2 S hd hd1, h1, S.Yrk]
  exact w107_false_of_involution_cost_two hw2 hgen hHat'.1 hHat'.2.1 hLieK hK.top hdK hdOrd hcost

theorem Std139.u43_embed (hgen : U43TripleGen) (hw2 : ∀ w : W, w ^ 2 = 1)
    (S : Std139 G X D s Y n) (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K)
    (hirr : IsIrrOn K ⊤ ⊥) (hHat : ∃ (S' : Type) (_ : Group S'), LieModel S' .PSU 4 3 1 ∧
      IsHat ↥K S') :
    ∃ (S' : Type) (_ : Group S') (_ : Finite S') (_ : LieModel S' .PSU 4 3 1)
      (E : Subgroup (MulAut S')), (∀ a ∈ E, a ^ 2 = 1) ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ∈ (MulAut.conj : S' →* MulAut S').range → a = 1) ∧
      Nat.card D ≤ Nat.card E := by
  have hHat0 := hHat
  obtain ⟨S', hgrp, hLieS', hHat'⟩ := hHat0
  letI : Group S' := hgrp
  obtain ⟨φ⟩ := hHat'.2.2
  haveI : Finite S' :=
    Finite.of_injective (φ.symm : S' → ↥K ⧸ Subgroup.center ↥K) φ.symm.injective
  let N : Subgroup (MulAut W) := Subgroup.normalizer (K : Set (MulAut W))
  have hDN : D ≤ N := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hK.normal d (S.DG hd)
  let L : Subgroup ↥N := K.subgroupOf N
  haveI : L.Normal := Subgroup.normal_in_normalizer
  let eL : L ≃* ↥K := Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := K))
  have hperfL : commutator L = ⊤ :=
    w1369_commutator_eq_top_of_mulEquiv eL hHat'.1.1.commutator_eq_top
  let qiso : L ⧸ Subgroup.center L ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.congr (Subgroup.center L) (Subgroup.center ↥K) eL (Subgroup.map_center_eq eL)
  let ψ : L ⧸ Subgroup.center L ≃* S' := qiso.trans φ
  let Ψ : ↥D →* MulAut (L ⧸ Subgroup.center L) :=
    (CFSG.Goldschmidt.G3b.conjQuot L).comp (Subgroup.inclusion hDN)
  let Φ : ↥D →* MulAut S' := (MulAut.congr ψ).toMonoidHom.comp Ψ
  have hker : ∀ d : ↥D, Φ d = 1 → d = 1 := by
    intro d hd1
    have hΨ : Ψ d = 1 := by
      apply (MulAut.congr ψ).injective
      rw [map_one]
      exact hd1
    have hcq : CFSG.Goldschmidt.G3b.conjQuot L (Subgroup.inclusion hDN d) = 1 := hΨ
    have hcentN :=
      (CFSG.Goldschmidt.G3b.conjQuot_eq_one_iff L hperfL (Subgroup.inclusion hDN d)).mp hcq
    have hcentK : (d : MulAut W) ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff] at hcentN ⊢
      intro k hk
      have hkL : (⟨k, Subgroup.le_normalizer hk⟩ : ↥N) ∈ L := hk
      have h := hcentN ⟨k, Subgroup.le_normalizer hk⟩ hkL
      simpa [Subgroup.coe_inclusion] using congrArg Subtype.val h
    have hX : (d : MulAut W) ∈ X := by
      rw [← Std139.alpha_centralizer hw2 S hn hK hirr]
      exact hcentK
    have hd2 : (d : MulAut W) ^ 2 = 1 := S.elem.2 d d.2
    have hd3 : (d : MulAut W) ^ 3 = 1 := by
      have hdvd : orderOf (d : MulAut W) ∣ 3 := by
        have h : orderOf (d : MulAut W) = orderOf (⟨(d : MulAut W), hX⟩ : X) :=
          Subgroup.orderOf_coe (⟨(d : MulAut W), hX⟩ : X)
        rw [h, ← S.Xcard]
        exact orderOf_dvd_natCard _
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hval : (d : MulAut W) = 1 := by
      have h : (d : MulAut W) ^ 3 = (d : MulAut W) := by rw [pow_succ, hd2, one_mul]
      rw [← h, hd3]
    exact Subtype.ext hval
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h1 : Φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : a * b⁻¹ = 1 := hker (a * b⁻¹) h1
    have h3 : (a : MulAut W) * (b : MulAut W)⁻¹ = 1 := congrArg Subtype.val h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hinner : ∀ a ∈ Φ.range, a ∈ (MulAut.conj : S' →* MulAut S').range → a = 1 := by
    intro a haE haInn
    rw [MonoidHom.mem_range] at haE
    obtain ⟨d, rfl⟩ := haE
    rw [MonoidHom.mem_range] at haInn
    obtain ⟨σ, hσ⟩ := haInn
    by_cases hd1 : d = 1
    · rw [hd1, map_one]
    · exfalso
      have hdW : (d : MulAut W) ≠ 1 := fun h => hd1 (Subtype.ext h)
      have hnat := w1369_mulAut_congr_conj ψ (ψ.symm σ)
      rw [MulEquiv.apply_symm_apply] at hnat
      have hΦ : Φ d = MulAut.congr ψ (Ψ d) := rfl
      have hconj : Ψ d = MulAut.conj (ψ.symm σ) := by
        apply (MulAut.congr ψ).injective
        rw [hnat]
        exact hΦ.symm.trans hσ.symm
      have hcq : CFSG.Goldschmidt.G3b.conjQuot L (Subgroup.inclusion hDN d) =
          MulAut.conj (ψ.symm σ) := hconj
      obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) (ψ.symm σ)
      have hconj2 : CFSG.Goldschmidt.G3b.conjQuot L (Subgroup.inclusion hDN d) =
          MulAut.conj (l : L ⧸ Subgroup.center L) :=
        hcq.trans (congrArg MulAut.conj hl.symm)
      have hlmem : CFSG.Goldschmidt.G3b.conjQuot L l =
          MulAut.conj (l : L ⧸ Subgroup.center L) :=
        CFSG.Goldschmidt.G3b.conjQuot_of_mem L l.2
      set c : ↥N := Subgroup.inclusion hDN d * (l : ↥N)⁻¹ with hc_def
      have hprod : CFSG.Goldschmidt.G3b.conjQuot L c = 1 := by
        rw [hc_def, map_mul, map_inv, hconj2, hlmem, mul_inv_cancel]
      have hcC : c ∈ Subgroup.centralizer (L : Set ↥N) :=
        (CFSG.Goldschmidt.G3b.conjQuot_eq_one_iff L hperfL c).mp hprod
      have hd_eq : (c : MulAut W) * (l : MulAut W) = d := by
        have h : (c * l : ↥N) = Subgroup.inclusion hDN d := by rw [hc_def]; group
        simpa [Subgroup.coe_inclusion] using congrArg (fun w : ↥N => (w : MulAut W)) h
      have hcK : (c : MulAut W) ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hkL : (⟨k, Subgroup.le_normalizer hk⟩ : ↥N) ∈ L := hk
        have h := hcC ⟨k, Subgroup.le_normalizer hk⟩ hkL
        simpa using congrArg Subtype.val h
      have hcX : (c : MulAut W) ∈ X := by
        rw [← Std139.alpha_centralizer hw2 S hn hK hirr]
        exact hcK
      have hk : (l : MulAut W) ∈ K := l.2
      have hcomm : Commute (c : MulAut W) (l : MulAut W) :=
        (Subgroup.mem_centralizer_iff.mp hcK (l : MulAut W) hk).symm
      have hc3 : (c : MulAut W) ^ 3 = 1 := by
        have hdvd : orderOf (c : MulAut W) ∣ 3 := by
          have h : orderOf (c : MulAut W) = orderOf (⟨(c : MulAut W), hcX⟩ : X) :=
            Subgroup.orderOf_coe (⟨(c : MulAut W), hcX⟩ : X)
          rw [h, ← S.Xcard]
          exact orderOf_dvd_natCard _
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hc2 : (c : MulAut W) = (l : MulAut W) ^ 2 := by
        have h1 : (c : MulAut W) ^ 2 * (l : MulAut W) ^ 2 = 1 := by
          rw [← hcomm.mul_pow 2, hd_eq]
          exact S.elem.2 d d.2
        have h2 : (c : MulAut W) ^ 2 = ((l : MulAut W) ^ 2)⁻¹ :=
          mul_eq_one_iff_eq_inv.mp h1
        have h3 : (c : MulAut W) ^ 2 = (c : MulAut W)⁻¹ :=
          mul_eq_one_iff_eq_inv.mp (by rw [← pow_succ]; exact hc3)
        rw [h3] at h2
        exact inv_injective h2
      have hcK' : (c : MulAut W) ∈ K := by
        rw [hc2]
        exact K.pow_mem hk 2
      have hdK : (d : MulAut W) ∈ K := by
        rw [← hd_eq]
        exact K.mul_mem hcK' hk
      exact (Std139.u43_not_mem (d := (d : MulAut W)) hgen hw2 S hK hHat d.2 hdW) hdK
  have hcard : Nat.card D ≤ Nat.card Φ.range := by
    have hbij : Function.Bijective Φ.rangeRestrict :=
      ⟨fun x y h => hinj (Subtype.ext_iff.mp h), Φ.rangeRestrict_surjective⟩
    have h := Nat.card_congr (Equiv.ofBijective Φ.rangeRestrict hbij)
    exact le_of_eq h
  refine ⟨S', hgrp, inferInstance, hLieS', Φ.range, ?_, ?_, hinner, hcard⟩
  · intro a ha
    rw [MonoidHom.mem_range] at ha
    obtain ⟨d, rfl⟩ := ha
    have hd2 : d ^ 2 = 1 := Subtype.ext (S.elem.2 (d : MulAut W) d.2)
    rw [← map_pow, hd2, map_one]
  · intro a ha b hb
    rw [MonoidHom.mem_range] at ha hb
    obtain ⟨d, rfl⟩ := ha
    obtain ⟨e, rfl⟩ := hb
    have hde : d * e = e * d :=
      Subtype.ext (S.elem.1 (d : MulAut W) d.2 (e : MulAut W) e.2)
    simpa only [map_mul] using congrArg Φ hde

theorem Std139.alpha_row_U43 (hgen : U43TripleGen) (gOut : GapOutU43)
    (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    (hHat : ∃ (S' : Type) (_ : Group S'), LieModel S' .PSU 4 3 1 ∧ IsHat ↥K S')
    (hcard : Nat.card W = 2 ^ 12) : False := by
  obtain ⟨S', _, _, hLie, E, hE2, hEc, hEinn, hDE⟩ := Std139.u43_embed hgen hw2 S hn hK hirr hHat
  have h4 := gOut S' hLie E hE2 hEc hEinn
  have hn6 : n = 6 := by
    have h : (2 : ℕ) ^ (2 * n) = 2 ^ 12 := by rw [pow_mul]; norm_num; rw [← S.card]; exact hcard
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  have hD := S.Dcard
  rw [hn6] at hD
  omega

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

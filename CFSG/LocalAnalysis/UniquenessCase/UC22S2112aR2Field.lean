module

public import CFSG.Blueprint.Catalog
import CFSG.RankThree.PartOne.CTP.SeitzL2
import CFSG.RankThree.PartTwo.KFacts.AutKinds
import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson
import CFSG.GH74.GLS.IVK.L2.BorelStd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem uc22s2112r2_exists_rootParam {X : Type} [Group X] {p f r : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hX : LieModel X .PSL 2 p f) (hr : r.Prime) (hr2 : r ≠ 2) {θ : MulAut X}
    (hθr : orderOf θ = r) (hθ : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ (w : Multiplicative (GaloisField p f) →* X) (τ : GaloisField p f ≃+* GaloisField p f),
      Function.Injective w ∧ orderOf τ = r ∧ r ∣ f ∧
      Nat.card {t : GaloisField p f // τ t = t} = p ^ (f / r) ∧
      ∀ t : GaloisField p f, θ (w (Multiplicative.ofAdd t)) = w (Multiplicative.ofAdd (τ t)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  set σ : MulAut (CFSG.GorensteinWalter.PSL2 (GaloisField p f)) := MulAut.congr e θ with hσ
  have hσr : orderOf σ = r := by rw [hσ, MulEquiv.orderOf_eq]; exact hθr
  have hσout : ∀ g, σ ≠ MulAut.conj g := by
    intro g hg
    exact hθ ((CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e θ).1 ⟨g, hg.symm⟩)
  obtain ⟨τ, β, hτ, hστ⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_conj_fieldAut hr (hr.odd_of_ne_two hr2) ⟨hσr, hσout⟩
  obtain ⟨hrf, hcard⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield hp hf1 hF τ
  rw [hτ] at hrf hcard
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField p f) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p f) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  let u : Multiplicative (GaloisField p f) →* PSL(2, GaloisField p f) :=
    MonoidHom.mk' (fun t => CFSG.PSL2Table.mk (CFSG.PSL2Table.unip (Multiplicative.toAdd t)))
      (fun s t => by rw [toAdd_mul, CFSG.PSL2Table.unip_add, map_mul])
  refine ⟨(e.symm.toMonoidHom.comp β.toMonoidHom).comp u, τ, ?_, hτ, hrf, ?_, fun t => ?_⟩
  · intro s t hst
    have h1 : u s = u t := β.injective (e.symm.injective hst)
    exact Multiplicative.toAdd.injective
      ((CFSG.PSL2Table.mk_unip_eq_mk_unip_iff h2 _ _).1 h1)
  · rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (CFSG.ComponentClassification.CatalogueBLinearTwoDescent.mem_fixedSubfield _ τ x).symm)
  · have hθx : ∀ x : X, θ x = e.symm (σ (e x)) := fun x => by
      rw [hσ, MulAut.congr_apply]
      simp
    change θ (e.symm (β (u (Multiplicative.ofAdd t)))) =
      e.symm (β (u (Multiplicative.ofAdd (τ t))))
    rw [hθx, MulEquiv.apply_symm_apply, hστ, MulAut.mul_apply, MulAut.mul_apply,
      MulAut.inv_apply_self]
    congr 2
    exact CFSG.GH74.GLS.IVK.L2Borel.psl2FieldAut_mk_unip τ t

theorem uc22s2112r2_sub_one_onto {F : Type} [Field F] [Finite F] {r : ℕ} (τ : F ≃+* F)
    (hτr : τ ^ r = 1) (hr : (r : F) ≠ 0) {v : F} (hv : ∃ t, τ t - t = v) :
    ∃ u, (∃ t, τ t - t = u) ∧ τ u - u = v := by
  classical
  have hpow : ∀ (k : ℕ) (x : F), (τ ^ (k + 1)) x = (τ ^ k) (τ x) := fun k x => by
    rw [pow_succ]
    rfl
  have hfix : ∀ y : F, τ (τ y - y) = τ y - y → τ y - y = 0 := by
    intro y hy
    have hk : ∀ k : ℕ, (τ ^ k) (τ y - y) = τ y - y := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [hpow, hy, ih]
    have hsum : ∑ i ∈ Finset.range r, ((τ ^ (i + 1)) y - (τ ^ i) y) = (τ ^ r) y - (τ ^ 0) y :=
      Finset.sum_range_sub (fun i => (τ ^ i) y) r
    have hsum' : ∑ i ∈ Finset.range r, ((τ ^ (i + 1)) y - (τ ^ i) y) = (r : F) * (τ y - y) := by
      rw [Finset.sum_congr rfl fun i _ => (show (τ ^ (i + 1)) y - (τ ^ i) y = τ y - y by
        rw [hpow, ← map_sub, hk]), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum', hτr, pow_zero] at hsum
    exact (mul_eq_zero.1 (hsum.trans (sub_self y))).resolve_left hr
  let V := {x : F // ∃ t, τ t - t = x}
  let g : V → V := fun x => ⟨τ x.1 - x.1, x.1, rfl⟩
  have hg : Function.Injective g := by
    rintro ⟨x, s, rfl⟩ ⟨y, t, rfl⟩ hxy
    have h1 : τ (τ s - s) - (τ s - s) = τ (τ t - t) - (τ t - t) := congrArg Subtype.val hxy
    have h2 : τ (s - t) - (s - t) = (τ s - s) - (τ t - t) := by
      rw [map_sub]
      ring
    have h3 := hfix (s - t) (by
      rw [h2, map_sub]
      linear_combination h1)
    apply Subtype.ext
    change τ s - s = τ t - t
    rw [h2] at h3
    exact sub_eq_zero.1 h3
  obtain ⟨⟨u, hu⟩, huv⟩ := (Finite.injective_iff_surjective.1 hg) ⟨v, hv⟩
  exact ⟨u, hu, congrArg Subtype.val huv⟩

theorem uc22s2112r2_exists_sub_one_sq {p : ℕ} [Fact p.Prime] {F : Type} [Field F]
    [Algebra (ZMod p) F] (τ : F ≃+* F) (hτp : τ ^ p = 1) (hτ : τ ≠ 1) :
    ∃ t, τ t ≠ t ∧ τ (τ t - t) = τ t - t := by
  classical
  have hp : p.Prime := Fact.out
  let T : Module.End (ZMod p) F := AddMonoidHom.toZModLinearMap p τ.toAddMonoidHom
  let N : Module.End (ZMod p) F := T - 1
  have hNt : ∀ t, N t = τ t - t := fun t => rfl
  have : CharP (Module.End (ZMod p) F) p := Module.charP_end
    ⟨1, (Ideal.torsionOf_eq_bot_iff_of_noZeroSMulDivisors (ZMod p) (1 : F)).2 one_ne_zero⟩
  have hT : T ^ p = 1 := by
    ext t
    rw [Module.End.pow_apply, Module.End.one_apply]
    have h1 : ∀ k : ℕ, T^[k] t = (τ ^ k) t := by
      intro k
      induction k generalizing t with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply, ih, pow_succ]
        rfl
    rw [h1, hτp]
    rfl
  have hN : N ^ p = 0 := by
    rw [sub_pow_char_of_commute (R := Module.End (ZMod p) F) (p := p) (Commute.one_right T), hT,
      one_pow, sub_self]
  by_contra hcon
  have key : ∀ t, N (N t) = 0 → N t = 0 := by
    intro t ht
    rw [hNt, hNt] at ht
    by_contra h0
    rw [hNt] at h0
    exact hcon ⟨t, fun h => h0 (by rw [h, sub_self]), sub_eq_zero.1 ht⟩
  have hk : ∀ k : ℕ, ∀ t, (N ^ (k + 1)) t = 0 → N t = 0 := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih =>
      intro t ht
      apply key
      apply ih
      rw [pow_succ, Module.End.mul_apply] at ht
      exact ht
  apply hτ
  ext t
  have h1 := hk (p - 1) t (by rw [Nat.sub_add_cancel hp.one_le, hN, LinearMap.zero_apply])
  rw [hNt] at h1
  exact sub_eq_zero.1 h1

end CFSG.LocalAnalysis.UniquenessCase.UC22

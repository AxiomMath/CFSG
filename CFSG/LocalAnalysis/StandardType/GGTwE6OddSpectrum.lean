module

public import CFSG.LocalAnalysis.StandardType.GGTwE6PrimeCentralizers
public import CFSG.LocalAnalysis.StandardType.GGTwE6Retoralize
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusOrders
public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusMeetGamma
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.StandardType.TwE6Tori
open scoped Matrix

theorem twE6_card_torus {L : Type}
    [Field L] [IsAlgClosed L] [CharP L 2] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2)
    (D : LangDatum TwistTag.E6.tag L) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) :
    ∃ (v : WeylGroup TwistTag.E6.tag)
      (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ),
      (∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) ∧
        Nat.card D.torus = (M.charpoly.eval (2 : ℤ)).natAbs := by
  classical
  obtain ⟨w, hw⟩ := D.n_weyl
  set g : WeylGroup TwistTag.E6.tag := w * twE6W0 with hg
  set M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    -(weylMatrix g) with hM
  have hv : ∀ x, w • x = M *ᵥ permLattice TwistTag.E6.perm x := by
    intro x
    rw [hM, Matrix.neg_mulVec, weylMatrix_mulVec, hg, mul_smul, twE6W0_smul_permLattice,
      smul_neg, neg_neg]
  have hn0 : 2 * orderOf g ≠ 0 := by
    have := orderOf_pos g
    omega
  have hpow : M ^ (2 * orderOf g) = 1 := by
    rw [hM, (even_two_mul _).neg_pow, ← weylMatrix_pow, pow_mul', pow_orderOf_eq_one, one_pow,
      weylMatrix_one]
  have hcop := not_dvd_natAbs_det_sub (ℓ := 2) (q := 2) Nat.prime_two (dvd_refl 2) M hn0 hpow
  have hBne : (M - ((2 : ℕ) : ℤ) • (1 : Matrix (Fin TwistTag.E6.tag.rank)
      (Fin TwistTag.E6.tag.rank) ℤ)).det ≠ 0 := fun h => hcop (by rw [h]; exact dvd_zero 2)
  refine ⟨w, M, hv, ?_⟩
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr w M hv
  have hcard := natCard_fixedCharTuples M Fr (q := 2) (ℓ := 2) hFr hBne hcop
  show Nat.card (twistedTorusOf D.n D.Φ) = _
  rw [hw, hΦ, hT0, Subgroup.card_map_of_injective CFSG.LieType.Chevalley.rootDiagUnit_injective,
    hcard, natAbs_eval_charpoly]
  rfl

theorem twE6OddSpectrum_holds
    : TwE6OddSpectrum := by
  classical
  intro L _ _ _ p₀ Fr S hal hq hFr hΦ x hx
  obtain ⟨D', hq', hΦ', hfin', hΓ', htor, hΓ⟩ :=
    twE6_oddOrder_retoralize S hq hal Fr hFr hΦ x hx
  have hΦD : D'.Φ = twistHom TwistTag.E6 L Fr := hΦ'.trans hΦ
  have halg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c := fun c => by
    simpa [hq] using hal c
  have hdvd := twE6_torus_meet_gamma_dvd Fr halg D' hFr hΦD
  obtain ⟨v, M, hv, hcard⟩ := twE6_card_torus Fr hFr D' hΦD
  obtain ⟨h13, h19⟩ := twE6_charpoly_two_spec v M hv
  set c : ModGL TwistTag.E6.tag L := D'.g0⁻¹ * S.D.g0 with hc
  set y : ModGL TwistTag.E6.tag L := c * (x : ModGL TwistTag.E6.tag L) * c⁻¹ with hy
  have hord : orderOf y = orderOf x := by
    have h1 : orderOf y = orderOf ((MulAut.conj c).toMonoidHom (x : ModGL TwistTag.E6.tag L)) := rfl
    rw [h1, orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective]
    exact Subgroup.orderOf_coe x
  have hyT : y ∈ D'.torus ⊓ D'.Γ := ⟨htor, hΓ⟩
  have h1 : orderOf y ∣ Nat.card ↥(D'.torus ⊓ D'.Γ) := by
    have := orderOf_dvd_natCard (⟨y, hyT⟩ : ↥(D'.torus ⊓ D'.Γ))
    rwa [Subgroup.orderOf_mk] at this
  have hsub : Nat.card (D'.torus.subgroupOf D'.Γ) = Nat.card ↥(D'.torus ⊓ D'.Γ) := by
    rw [← Subgroup.card_map_of_injective D'.Γ.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  rw [hsub, hcard] at hdvd
  have h3 : 3 * orderOf x ∣ (M.charpoly.eval (2 : ℤ)).natAbs := by
    rw [← hord]
    exact (Nat.mul_dvd_mul_left 3 h1).trans (by rw [mul_comm]; exact hdvd)
  have key : ∀ {p : ℕ}, 0 < p → p ∣ orderOf x → 3 * orderOf x ∣ 3 * p → orderOf x = p := by
    intro p hp ⟨k, hk⟩ h
    rw [hk] at h ⊢
    have h' : p * k ∣ p * 1 := by
      have := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) h
      simpa using this
    have := Nat.dvd_of_mul_dvd_mul_left hp h'
    rw [Nat.dvd_one.1 this, mul_one]
  refine ⟨fun h13x => ?_, fun h19x => ?_⟩
  · have hd : (M.charpoly.eval (2 : ℤ)).natAbs = 39 :=
      h13 (dvd_trans (dvd_trans h13x (Dvd.intro_left 3 rfl)) h3)
    rw [hd] at h3
    exact key (by norm_num) h13x (by simpa using h3)
  · have hd : (M.charpoly.eval (2 : ℤ)).natAbs = 57 :=
      h19 (dvd_trans (dvd_trans h19x (Dvd.intro_left 3 rfl)) h3)
    rw [hd] at h3
    exact key (by norm_num) h19x (by simpa using h3)

theorem twE6q2OrderThreeCentralizers_holds
    : TwE6q2OrderThreeCentralizers :=
  twE6q2OrderThreeCentralizers_of_oddSpectrum twE6OddSpectrum_holds

end CFSG.StandardType.TableCRes

end

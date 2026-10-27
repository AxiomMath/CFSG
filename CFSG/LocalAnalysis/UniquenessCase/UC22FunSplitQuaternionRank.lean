module

public import CFSG.ClassicalInvolution.Generic.Frame
import CFSG.ClassicalGroups.SpecialLinear.TvModLinAlg
import CFSG.ClassicalInvolution.TwoGroupCase.Q8
import CFSG.LocalAnalysis.SteinbergBVPrimeTorsionHomocyclic
import CFSG.LocalAnalysis.LargeEvenClassification.ElementaryLinear
import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Quasithin.EmptyFaithful.SzN31FactRA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.SteinbergBV

open QuaternionGroup

private theorem q8_center_eq_one_of_commuting_image {M : Type*} [Group M]
    (f : QuaternionGroup 2 →* M) (hcomm : ∀ x y, Commute (f x) (f y)) : f (a 2) = 1 := by
  apply CFSG.ClassicalInvolution.q8_center_mem_ker f
  intro hf
  have h := hcomm (a 1) (xa 0)
  have hc : (a 1 : QuaternionGroup 2) * xa 0 = xa 0 * a 1 :=
    hf (by rw [map_mul, map_mul]; exact h.eq)
  have hn : (a 1 : QuaternionGroup 2) * xa 0 ≠ xa 0 * a 1 := by decide +kernel
  exact hn hc

theorem quaternion_center_eq_one_of_commuting_linear_actions
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hF : (2 : F) ≠ 0) (hV : Module.finrank F V ≤ 2)
    (ρQ ρR : QuaternionGroup 2 →* (V ≃ₗ[F] V))
    (hQR : ∀ q r, Commute (ρQ q) (ρR r))
    (hQz : ∀ v, ρQ (a 2) v = -v) : ρR (a 2) = 1 := by
  classical
  let ι := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)
  have hι : Function.Injective ι := LinearEquiv.toLinearMap_injective
  by_cases h0 : Module.finrank F V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact Subsingleton.elim _ _
  have hQzne : ρQ (a 2) ≠ 1 := by
    intro hz
    have hzero : ∀ v : V, v = 0 := by
      intro v
      have h : v = -v := by simpa [hz] using hQz v
      have h2 : (2 : F) • v = 0 := by rw [two_smul]; nth_rw 1 [h]; exact neg_add_cancel v
      exact (smul_eq_zero.mp h2).resolve_left hF
    have : Subsingleton V := ⟨fun v w => by rw [hzero v, hzero w]⟩
    exact h0 Module.finrank_zero_of_subsingleton
  have hRcomm : ∀ r s, Commute (ρR r) (ρR s) := by
    by_cases h1 : Module.finrank F V = 1
    · intro r s
      obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1 (ι (ρR r))
      apply Commute.of_map hι
      rw [hc]
      exact (Commute.one_left (ι (ρR s))).smul_left c
    · have hdim : Module.finrank F V = 2 := by omega
      obtain ⟨q, hq⟩ : ∃ q : QuaternionGroup 2, ∀ c : F, ι (ρQ q) ≠ c • 1 := by
        by_contra h
        push Not at h
        apply hQzne
        apply q8_center_eq_one_of_commuting_image ρQ
        intro q r
        obtain ⟨c, hc⟩ := h q
        obtain ⟨d, hd⟩ := h r
        apply Commute.of_map hι
        rw [hc, hd]
        exact ((Commute.one_left (1 : Module.End F V)).smul_left c).smul_right d
      intro r s
      apply Commute.of_map hι
      exact CFSG.ClassicalGroups.SpecialLinear.TvMod.commute_of_commute_of_finrank_eq_two
        hdim hq ((hQR q r).map ι) ((hQR q s).map ι)
  exact q8_center_eq_one_of_commuting_image ρR hRcomm

private theorem q8_involution_eq {G : Type*} [Group G] (Q : Subgroup G)
    (e : Q ≃* QuaternionGroup 2) {z : G} (hz : IsUniqueInvolution Q z) :
    ((e.symm (QuaternionGroup.a 2) : Q) : G) = z := by
  have hsq : (e.symm (QuaternionGroup.a 2) : Q) * e.symm (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul]
    have h : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide +kernel
    rw [h, map_one]
  have hne : (e.symm (QuaternionGroup.a 2) : Q) ≠ 1 := by
    intro h
    have h' := congrArg e h
    have h2 : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide +kernel
    exact h2 (by simpa using h')
  exact (hz.unique _ (e.symm (QuaternionGroup.a 2)).2
    (congrArg (fun q : Q => (q : G)) hsq)).resolve_left (fun h => hne (Subtype.ext h))

theorem quaternion_commuting_center_fixes_rank_two
    {G : Type*} [Group G] [Finite G] (E Q R : Subgroup G)
    (hEab : IsMulCommutative E) (hEodd : Odd (Nat.card E))
    (hrank : ∀ p : ℕ, p.Prime → p ∣ Nat.card E → CFSG.Open.pRank p E ≤ 2)
    (eQ : Q ≃* QuaternionGroup 2) (eR : R ≃* QuaternionGroup 2)
    {zQ zR : G} (hzQ : IsUniqueInvolution Q zQ) (hzR : IsUniqueInvolution R zR)
    (hQR : ∀ q ∈ Q, ∀ r ∈ R, q * r = r * q)
    (hQE : Q ≤ normalizer (E : Set G)) (hRE : R ≤ normalizer (E : Set G))
    (hinv : ∀ x ∈ E, zQ * x * zQ⁻¹ = x⁻¹) :
    ∀ x ∈ E, zR * x * zR⁻¹ = x := by
  classical
  let _ : CommGroup E := { E.toGroup with mul_comm := hEab.is_comm.comm }
  have hzQmap := q8_involution_eq Q eQ hzQ
  have hzRmap := q8_involution_eq R eR hzR
  let νQ : QuaternionGroup 2 →* MulAut E := E.normalizerMonoidHom.comp
    ((Subgroup.inclusion hQE).comp eQ.symm.toMonoidHom)
  let νR : QuaternionGroup 2 →* MulAut E := E.normalizerMonoidHom.comp
    ((Subgroup.inclusion hRE).comp eR.symm.toMonoidHom)
  have hν : ∀ q r, Commute (νQ q) (νR r) := by
    intro q r
    have hc : Commute ((Subgroup.inclusion hQE) (eQ.symm q))
        ((Subgroup.inclusion hRE) (eR.symm r)) :=
      show _ * _ = _ * _ from Subtype.ext (hQR _ (eQ.symm q).2 _ (eR.symm r).2)
    exact hc.map E.normalizerMonoidHom
  let α : MulAut E := E.normalizerMonoidHom ⟨zR, hRE hzR.mem⟩
  have hα : α * α = 1 := by
    rw [show α = E.normalizerMonoidHom ⟨zR, hRE hzR.mem⟩ from rfl, ← map_mul]
    have hsq : (⟨zR, hRE hzR.mem⟩ : normalizer (E : Set G)) * ⟨zR, hRE hzR.mem⟩ = 1 :=
      Subtype.ext hzR.sq
    rw [hsq, map_one]
  have hfixp : ∀ p : ℕ, p.Prime → p ∣ Nat.card E → ∀ x : E, x ^ p = 1 → α x = x := by
    intro p hp hpd x hxp
    have : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := fun h => hEodd.not_two_dvd_nat (h ▸ hpd)
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro h
      have hpd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
      exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hpd2 |>.resolve_left hp.ne_one)
    have hchar : (primeTorsion E p).Characteristic := by
      rw [Subgroup.characteristic_iff_map_le]
      intro a
      rintro _ ⟨y, hy, rfl⟩
      change y ∈ primeTorsion E p at hy
      rw [mem_primeTorsion] at hy ⊢
      rw [← map_pow, hy, map_one]
    let V := Additive (primeTorsion E p)
    let κ : MulAut E →* (V ≃ₗ[ZMod p] V) :=
      (CFSG.LargeEvenClassification.Helpers.elementaryAutLinear p).comp
        (CFSG.FiveTransitive.CharacteristicAutomorphism.restrict (primeTorsion E p))
    let ρQ := κ.comp νQ
    let ρR := κ.comp νR
    have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
    have hcard : Nat.card (primeTorsion E p) = p ^ Module.finrank (ZMod p) V := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rw [Nat.card_zmod] at hc
      exact hc
    have ht : IsElemAbelian p (primeTorsion E p) :=
      ⟨inferInstance, fun y hy => mem_primeTorsion.mp hy⟩
    have hdim : Module.finrank (ZMod p) V ≤ 2 := by
      apply le_trans (CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_subtype_le
        (primeTorsion E p)) (CFSG.SectionRank.isElemAbelian_map ht E.subtype) ?_) (hrank p hp hpd)
      rw [Subgroup.card_map_of_injective E.subtype_injective, hcard]
    have hρQ : ∀ v : V, ρQ (QuaternionGroup.a 2) v = -v := by
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change ((eQ.symm (QuaternionGroup.a 2) : Q) : G) *
        (((v.toMul : primeTorsion E p) : E) : G) *
        ((eQ.symm (QuaternionGroup.a 2) : Q) : G)⁻¹ =
        ((((v.toMul : primeTorsion E p) : E) : G))⁻¹
      rw [hzQmap]
      exact hinv _ (v.toMul : E).2
    have hρR := quaternion_center_eq_one_of_commuting_linear_actions htwo hdim ρQ ρR (fun q r => (hν q r).map κ) hρQ
    have hxT : x ∈ primeTorsion E p := mem_primeTorsion.mpr hxp
    have hxfix := congrArg
      (fun f : V ≃ₗ[ZMod p] V => (((f (Additive.ofMul ⟨x, hxT⟩)).toMul : primeTorsion E p) : E)) hρR
    apply Subtype.ext
    change zR * (x : G) * zR⁻¹ = x
    have hh := congrArg (fun y : E => (y : G)) hxfix
    change ((eR.symm (QuaternionGroup.a 2) : R) : G) * (x : G) *
      ((eR.symm (QuaternionGroup.a 2) : R) : G)⁻¹ = x at hh
    rwa [hzRmap] at hh
  have hαfix : ∀ x : E, α x = x := by
    intro x
    by_contra hx
    let w : E := x⁻¹ * α x
    have hw1 : w ≠ 1 := fun h => hx (inv_mul_eq_one.mp h).symm
    have hwInv : α w = w⁻¹ := by
      have hαα : α (α x) = x := congrArg (fun f : MulAut E => f x) hα
      simp only [w, map_mul, map_inv, hαα, mul_inv_rev, inv_inv]
    have horder : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd horder
    have hpdE : p ∣ Nat.card E := hpd.trans (orderOf_dvd_natCard w)
    let v := w ^ (orderOf w / p)
    have hvord : orderOf v = p := orderOf_pow_orderOf_div
      (isOfFinOrder_of_finite w).orderOf_pos.ne' hpd
    have hvp : v ^ p = 1 := hvord ▸ pow_orderOf_eq_one v
    have hvInv : α v = v⁻¹ := by rw [map_pow, hwInv, inv_pow]
    have hvFix := hfixp p hp hpdE v hvp
    have hp2 : p ≠ 2 := fun h => hEodd.not_two_dvd_nat (h ▸ hpdE)
    have heqInv : v = v⁻¹ := hvFix.symm.trans hvInv
    have hv1 : v = 1 := CFSG.Quasithin.SzN31.eq_one_of_sq_eq_one_of_pow_eq_one hp hp2
      (by nth_rw 1 [heqInv]; exact inv_mul_cancel v) hvp
    exact hp.ne_one (by simpa [hv1] using hvord.symm)
  intro x hx
  exact congrArg (fun y : E => (y : G)) (hαfix ⟨x, hx⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22

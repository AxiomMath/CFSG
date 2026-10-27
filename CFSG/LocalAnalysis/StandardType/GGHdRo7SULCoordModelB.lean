module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordTorus
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly
open CFSG.StandardType.UCoord
open Multiplicative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def hdRo7SULCoordAux_decomp (m p : ℕ) [Fact p.Prime] (hm : (m : ZMod p) ≠ 0) :
    (Fin m → Multiplicative (ZMod p)) ≃* ↥(sumZero m p) × Multiplicative (ZMod p) where
  toFun f :=
    (⟨fun i => Multiplicative.ofAdd (Multiplicative.toAdd (f i) -
        (m : ZMod p)⁻¹ * ∑ j, Multiplicative.toAdd (f j)), by
        rw [mem_sumZero]
        simp only [toAdd_ofAdd]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul, sub_self]⟩,
     Multiplicative.ofAdd ((m : ZMod p)⁻¹ * ∑ j, Multiplicative.toAdd (f j)))
  invFun q := fun i =>
    Multiplicative.ofAdd (Multiplicative.toAdd ((q.1 : Fin m → Multiplicative (ZMod p)) i) +
      Multiplicative.toAdd q.2)
  left_inv f := by
    funext i
    simp only [toAdd_ofAdd]
    rw [show Multiplicative.toAdd (f i) - (m : ZMod p)⁻¹ * (∑ j, Multiplicative.toAdd (f j)) +
        (m : ZMod p)⁻¹ * (∑ j, Multiplicative.toAdd (f j)) =
        Multiplicative.toAdd (f i) by ring]
    simp
  right_inv q := by
    have hS : (∑ j, (Multiplicative.toAdd ((q.1 : Fin m → Multiplicative (ZMod p)) j) +
        Multiplicative.toAdd q.2)) = (m : ZMod p) * Multiplicative.toAdd q.2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [show (∑ j, Multiplicative.toAdd ((q.1 : Fin m → Multiplicative (ZMod p)) j)) = 0
          from q.1.2, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp only [toAdd_ofAdd, hS]
      rw [show Multiplicative.toAdd ((q.1 : Fin m → Multiplicative (ZMod p)) i) +
          Multiplicative.toAdd q.2 -
          (m : ZMod p)⁻¹ * ((m : ZMod p) * Multiplicative.toAdd q.2) =
          Multiplicative.toAdd ((q.1 : Fin m → Multiplicative (ZMod p)) i) by
        rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]
        ring]
      simp
    · show Multiplicative.ofAdd ((m : ZMod p)⁻¹ *
          (∑ j, (Multiplicative.toAdd ((q.1 : Fin m → Multiplicative (ZMod p)) j) +
            Multiplicative.toAdd q.2))) = q.2
      rw [hS, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]
      simp
  map_mul' f g := by
    have hS : (∑ j, Multiplicative.toAdd ((f * g) j)) =
        (∑ j, Multiplicative.toAdd (f j)) + (∑ j, Multiplicative.toAdd (g j)) := by
      simp [Pi.mul_apply, Finset.sum_add_distrib]
    apply Prod.ext
    · apply Subtype.ext
      funext i
      change ofAdd (toAdd ((f * g) i) - (m : ZMod p)⁻¹ * ∑ j, toAdd ((f * g) j)) =
        ofAdd (toAdd (f i) - (m : ZMod p)⁻¹ * ∑ j, toAdd (f j)) *
        ofAdd (toAdd (g i) - (m : ZMod p)⁻¹ * ∑ j, toAdd (g j))
      have hfg : Multiplicative.toAdd ((f * g) i) =
          Multiplicative.toAdd (f i) + Multiplicative.toAdd (g i) := by simp
      rw [hS, hfg, ← ofAdd_add]
      congr 1
      ring
    · change ofAdd ((m : ZMod p)⁻¹ * ∑ j, toAdd ((f * g) j)) =
        ofAdd ((m : ZMod p)⁻¹ * ∑ j, toAdd (f j)) *
        ofAdd ((m : ZMod p)⁻¹ * ∑ j, toAdd (g j))
      rw [hS, ← ofAdd_add]
      congr 1
      ring

theorem hdRo7SULCoordAux_decomp_fst_apply (m p : ℕ) [Fact p.Prime] (hm : (m : ZMod p) ≠ 0)
    (f : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    (((hdRo7SULCoordAux_decomp m p hm f).1 : ↥(sumZero m p)) :
      Fin m → Multiplicative (ZMod p)) i =
      Multiplicative.ofAdd (Multiplicative.toAdd (f i) -
        (m : ZMod p)⁻¹ * ∑ j, Multiplicative.toAdd (f j)) := rfl

theorem hdRo7SULCoordAux_decomp_snd_apply (m p : ℕ) [Fact p.Prime] (hm : (m : ZMod p) ≠ 0)
    (f : Fin m → Multiplicative (ZMod p)) :
    (hdRo7SULCoordAux_decomp m p hm f).2 =
      Multiplicative.ofAdd ((m : ZMod p)⁻¹ * ∑ j, Multiplicative.toAdd (f j)) := rfl

theorem hdRo7SULCoordAux_decomp_crd (m p : ℕ) [Fact p.Prime] (hm : (m : ZMod p) ≠ 0)
    (f : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    crd (hdRo7SULCoordAux_decomp m p hm f).1 i =
      Multiplicative.toAdd (f i) - (m : ZMod p)⁻¹ * ∑ j, Multiplicative.toAdd (f j) := by
  rw [crd, hdRo7SULCoordAux_decomp_fst_apply, toAdd_ofAdd]

theorem hdRo7SULCoordAux_decomp_ones (m p : ℕ) [Fact p.Prime] (hm : (m : ZMod p) ≠ 0) :
    hdRo7SULCoordAux_decomp m p hm (fun _ => Multiplicative.ofAdd (1 : ZMod p)) =
      ((1 : ↥(sumZero m p)), Multiplicative.ofAdd (1 : ZMod p)) := by
  have hS : (∑ j : Fin m, Multiplicative.toAdd
      ((fun _ => Multiplicative.ofAdd (1 : ZMod p)) j)) = (m : ZMod p) := by
    simp only [toAdd_ofAdd]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  apply Prod.ext
  · apply Subtype.ext
    funext i
    change Multiplicative.ofAdd (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p)) -
      (m : ZMod p)⁻¹ * (∑ j : Fin m, Multiplicative.toAdd
        ((fun _ => Multiplicative.ofAdd (1 : ZMod p)) j))) = (1 : Multiplicative (ZMod p))
    rw [hS, inv_mul_cancel₀ hm]
    simp
  · change Multiplicative.ofAdd ((m : ZMod p)⁻¹ * (∑ j : Fin m, Multiplicative.toAdd
      ((fun _ => Multiplicative.ofAdd (1 : ZMod p)) j))) = Multiplicative.ofAdd (1 : ZMod p)
    rw [hS, inv_mul_cancel₀ hm]

section Axis

@[expose] noncomputable def hdRo7SULCoordAux_axisEquivCfg {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hx : x ∈ Bs) (hp3 : p = 3) :
    Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := by
  have hp : Nat.Prime p := by rw [hp3]; exact Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, -, -, hSStar, -⟩ := hH.1.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  have hxp : x ^ p = 1 := hH.1.2.1.2.1.2 x hx
  have hCeq := hdRo7SULCoordAux_centralizerCfg hH hp3
  let g : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    ⟨x, by rw [hCeq]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩⟩
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hgpG : (g : G) ^ p = 1 := congrArg Subtype.val hgp
  have hgne : g ≠ 1 := fun h => hxne (Subtype.ext_iff.mp h)
  have hordg : orderOf g = p := orderOf_eq_prime hgp hgne
  let f : Multiplicative (ZMod p) →* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    MonoidHom.mk' (fun a => g ^ (Multiplicative.toAdd a).val) (by
      intro a b
      apply Subtype.ext
      show (g : G) ^ (Multiplicative.toAdd a + Multiplicative.toAdd b).val =
        (g : G) ^ (Multiplicative.toAdd a).val * (g : G) ^ (Multiplicative.toAdd b).val
      rw [ZMod.val_add, ← pow_eq_pow_mod (n := p) (a := (g : G))
        ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) hgpG, ← pow_add])
  have hfa : ∀ a : Multiplicative (ZMod p), f a = g ^ (Multiplicative.toAdd a).val := fun _ => rfl
  have hf1 : f (Multiplicative.ofAdd (1 : ZMod p)) = g := by
    rw [hfa]
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    have : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = 1 := by
      simp [ZMod.val_one p]
    rw [this, pow_one]
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : f (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : g ^ (Multiplicative.toAdd (a * b⁻¹)).val = 1 := h1
    have h3 : (Multiplicative.toAdd (a * b⁻¹)).val = 0 := by
      have hdvd : orderOf g ∣ (Multiplicative.toAdd (a * b⁻¹)).val :=
        orderOf_dvd_iff_pow_eq_one.mpr h2
      rw [hordg] at hdvd
      exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have h4 : Multiplicative.toAdd (a * b⁻¹) = 0 := (ZMod.val_eq_zero _).mp h3
    have h5 : Multiplicative.toAdd a + -Multiplicative.toAdd b = 0 := by simpa using h4
    have h6 : Multiplicative.toAdd a = Multiplicative.toAdd b := by
      have := add_eq_zero_iff_eq_neg.mp h5
      simpa using this
    exact Multiplicative.toAdd.injective h6
  have hcard_dom : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]
  have hcard_cod : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hCeq, Nat.card_zpowers, orderOf_eq_prime hxp hxne]
  exact MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [hcard_cod, hcard_dom]⟩)

theorem hdRo7SULCoordAux_axisEquiv_apply_oneCfg {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hx : x ∈ Bs) (hp3 : p = 3) :
    (hdRo7SULCoordAux_axisEquivCfg hH hx hp3) (Multiplicative.ofAdd (1 : ZMod p)) =
      (⟨x, by
        rw [hdRo7SULCoordAux_centralizerCfg hH hp3]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩⟩ :
        ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) := by
  unfold hdRo7SULCoordAux_axisEquivCfg
  simp only [MulEquiv.ofBijective_apply, MonoidHom.mk'_apply]
  rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = 1 by
    haveI : Fact (1 < p) := ⟨by rw [hp3]; norm_num⟩
    simp [ZMod.val_one p]]
  rw [pow_one]

@[expose] noncomputable def hdRo7SULCoordAux_prodEquivCfg {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs := by
  let f : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) →* ↥Bs :=
    MonoidHom.mk' (fun q => ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩) (by
      intro q r
      apply Subtype.ext
      show ((q.1 : G) * (r.1 : G)) * ((q.2 : G) * (r.2 : G)) =
        ((q.1 : G) * (q.2 : G)) * ((r.1 : G) * (r.2 : G))
      have h : (r.1 : G) * (q.2 : G) = (q.2 : G) * (r.1 : G) :=
        Subgroup.mem_centralizer_iff.mp q.2.2.2 (r.1 : G) r.1.2.2
      calc ((q.1 : G) * (r.1 : G)) * ((q.2 : G) * (r.2 : G))
          = (q.1 : G) * ((r.1 : G) * (q.2 : G)) * (r.2 : G) := by group
        _ = (q.1 : G) * ((q.2 : G) * (r.1 : G)) * (r.2 : G) := by rw [h]
        _ = ((q.1 : G) * (q.2 : G)) * ((r.1 : G) * (r.2 : G)) := by group)
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨q1, q2⟩ ⟨r1, r2⟩ h
    have h' : (q1 : G) * (q2 : G) = (r1 : G) * (r2 : G) := congrArg Subtype.val h
    have hmemT : (r1 : G)⁻¹ * (q1 : G) ∈ Bs ⊓ L :=
      ⟨Bs.mul_mem (Bs.inv_mem r1.2.1) q1.2.1, L.mul_mem (L.inv_mem r1.2.2) q1.2.2⟩
    have hmemC : (r1 : G)⁻¹ * (q1 : G) ∈ Subgroup.centralizer (L : Set G) := by
      have h2 : (r1 : G)⁻¹ * (q1 : G) = (r2 : G) * (q2 : G)⁻¹ := by
        have h3 : (q1 : G) * (q2 : G) * (q2 : G)⁻¹ = (r1 : G) * (r2 : G) * (q2 : G)⁻¹ := by
          rw [h']
        rw [mul_inv_cancel_right] at h3
        rw [h3]
        group
      rw [h2]
      exact (Subgroup.centralizer (L : Set G)).mul_mem r2.2.2
        ((Subgroup.centralizer (L : Set G)).inv_mem q2.2.2)
    have hz1 : (r1 : G)⁻¹ * (q1 : G) = 1 :=
      hdRo7SULCoordAux_inf_center_eq_botCfg hH hRig hrow _ hmemT.1 hmemT.2 hmemC
    have hq1 : q1 = r1 := by
      have h4 : (r1 : G) * ((r1 : G)⁻¹ * (q1 : G)) = (r1 : G) * 1 := by rw [hz1]
      rw [mul_inv_cancel_left, mul_one] at h4
      exact Subtype.ext h4
    have hq2 : q2 = r2 := by
      have h5 : (q1 : G) * (q2 : G) = (q1 : G) * (r2 : G) := by rw [h', ← hq1]
      exact Subtype.ext (mul_left_cancel h5)
    exact Prod.ext hq1 hq2
  · intro b
    obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SULCoordAux_splitCfg hH hRig hrow b b.2
    exact ⟨(⟨t, ht⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩

end Axis

end CFSG.StandardType.HdRo7SU

end

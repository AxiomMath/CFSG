module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OTs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LieType.Universal.Spin
open QuadraticMap

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_small_orbit_omegaMinus (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {A : Subgroup (MulAut (StdMod (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F))}
    (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hlin : ∀ a ∈ A, IsSemilinear a (RingEquiv.refl F))
    (hiso : ∀ a ∈ A, ∀ v, StatedQuadMinus 3 F b c (toAddMap a v) =
      StatedQuadMinus 3 F b c v) :
    ∃ w ∉ fixV A, ∃ U : Subgroup (StdMod (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F),
      Nat.card U ≤ Nat.card F ^ 2 ∧ ∀ a ∈ A, a w * w⁻¹ ∈ U := by
  classical
  let Q : QuadraticForm F (OW F) := quadMinus 3 F b c
  let B : LinearMap.BilinForm F (OW F) := polarBilin Q
  have hQn : (polarBilin (quadMinus 3 F b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hQnd : B.Nondegenerate := hQn
  let D : Submodule F (OW F) :=
    { toAddSubmonoid :=
        ({ carrier := {v | Multiplicative.ofAdd v ∈ fixV A}
           zero_mem' := by
             change Multiplicative.ofAdd (0 : OW F) ∈ fixV A
             rw [ofAdd_zero]
             exact Subgroup.one_mem _
           add_mem' := by
             intro x y hx hy
             change Multiplicative.ofAdd (x + y) ∈ fixV A
             change Multiplicative.ofAdd x ∈ fixV A at hx
             change Multiplicative.ofAdd y ∈ fixV A at hy
             rw [ofAdd_add]
             exact Subgroup.mul_mem _ hx hy } : AddSubmonoid (OW F))
      smul_mem' := by
        intro r x hx
        change Multiplicative.ofAdd (r • x) ∈ fixV A
        change Multiplicative.ofAdd x ∈ fixV A at hx
        rw [mem_fixV] at hx ⊢
        intro a ha
        have h1 : toAddMap a (r • x) = r • toAddMap a x := by
          simpa using hlin a ha r x
        have h2 : toAddMap a x = x := Multiplicative.ofAdd.injective (hx a ha)
        have h3 : toAddMap a (r • x) = r • x := by rw [h1, h2]
        rw [← ofAdd_toAdd (a (Multiplicative.ofAdd (r • x)))]
        simpa [toAddMap] using congrArg Multiplicative.ofAdd h3 }
  have hDmem : ∀ {v : OW F}, v ∈ D ↔ Multiplicative.ofAdd v ∈ fixV A := by
    intro v
    change Multiplicative.ofAdd v ∈ fixV A ↔ Multiplicative.ofAdd v ∈ fixV A
    rfl
  have hDfix : ∀ {d : OW F}, d ∈ D → ∀ a ∈ A, toAddMap a d = d := by
    intro d hd a ha
    exact Multiplicative.ofAdd.injective (mem_fixV.1 (hDmem.mp hd) a ha)
  let T : Submodule F (OW F) := D ⊓ B.orthogonal D
  have hTfinite : Module.Finite F ↥T := Module.Finite.of_finite
  have hTmem : ∀ {v : OW F}, v ∈ T ↔ v ∈ D ∧ ∀ d ∈ D, polar Q d v = 0 := by
    intro v
    rw [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨hv, h⟩
      refine ⟨hv, fun d hd => ?_⟩
      simpa [B, polarBilin_apply_apply] using h d hd
    · rintro ⟨hv, h⟩
      refine ⟨hv, fun d hd => ?_⟩
      simpa [B, polarBilin_apply_apply] using h d hd
  have hTorth : ∀ x ∈ T, ∀ y ∈ T, polar Q x y = 0 := by
    intro x hx y hy
    rw [hTmem] at hx hy
    exact hy.2 x hx.1
  have hBpres : ∀ a ∈ A, ∀ x y : OW F,
      polar Q (toAddMap a x) (toAddMap a y) = polar Q x y := by
    intro a ha x y
    have hQx : Q (toAddMap a x) = Q x := by
      change quadMinus 3 F b c (toAddMap a x) = quadMinus 3 F b c x
      rw [quadMinus_eq_stated, quadMinus_eq_stated]
      exact hiso a ha x
    have hQy : Q (toAddMap a y) = Q y := by
      change quadMinus 3 F b c (toAddMap a y) = quadMinus 3 F b c y
      rw [quadMinus_eq_stated, quadMinus_eq_stated]
      exact hiso a ha y
    have hQxy : Q (toAddMap a x + toAddMap a y) = Q (x + y) := by
      rw [← toAddMap_add]
      change quadMinus 3 F b c (toAddMap a (x + y)) =
        quadMinus 3 F b c (x + y)
      rw [quadMinus_eq_stated, quadMinus_eq_stated]
      exact hiso a ha (x + y)
    simp only [QuadraticMap.polar, hQxy, hQx, hQy]
  have hV6 : Module.finrank F (OW F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    norm_num [Fintype.card_sum]
  have hTfin : Module.finrank F T ≤ 3 := by
    have h1 : Module.finrank F T ≤ Module.finrank F D :=
      Submodule.finrank_mono inf_le_left
    have h2 : Module.finrank F T ≤ Module.finrank F (B.orthogonal D) :=
      Submodule.finrank_mono inf_le_right
    rw [LinearMap.BilinForm.finrank_orthogonal hQnd, hV6] at h2
    omega
  by_cases hsmall : Module.finrank F T ≤ 2
  ·
    have hW : ∀ w : StdMod (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F, w ^ 2 = 1 := by
      intro w
      have hw : w = Multiplicative.ofAdd (Multiplicative.toAdd w) :=
        (ofAdd_toAdd w).symm
      rw [hw, pow_two, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]
    obtain ⟨w, hwF, hdisp⟩ := exists_mem_secondLayer hW hA (le_refl (fixV A))
      (fixV_ne_top hA1)
    let wvec : OW F := Multiplicative.toAdd w
    have hwD : wvec ∉ D := by
      intro h
      exact hwF (by simpa [wvec] using hDmem.mp h)
    have hconv : ∀ a ∈ A,
        Multiplicative.ofAdd (toAddMap a wvec - wvec) = a w * w⁻¹ := by
      intro a ha
      rw [sub_eq_add_neg, ofAdd_add, ofAdd_neg]
      simp [toAddMap, wvec]
    have hdispT : ∀ a ∈ A, toAddMap a wvec - wvec ∈ T := by
      intro a ha
      rw [hTmem]
      refine ⟨?_, fun d hd => ?_⟩
      · rw [hDmem]
        rw [hconv a ha]
        exact hdisp a ha
      · rw [polar_comm Q d (toAddMap a wvec - wvec), polar_sub_left]
        have h1 : polar Q (toAddMap a wvec) (toAddMap a d) = polar Q wvec d :=
          hBpres a ha wvec d
        rw [hDfix hd a ha] at h1
        rw [h1, sub_self]
    refine ⟨w, hwF, AddSubgroup.toSubgroup T.toAddSubgroup, ?_, ?_⟩
    · have hcard : Nat.card ↥(AddSubgroup.toSubgroup T.toAddSubgroup) = Nat.card ↥T := by
        have h1 : Nat.card ↥(AddSubgroup.toSubgroup T.toAddSubgroup) =
            Nat.card ↥T.toAddSubgroup := by
          refine Nat.card_congr ?_
          exact
          { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (OW F)), x.2⟩
            invFun := fun x => ⟨Multiplicative.ofAdd (x : OW F), by simpa using x.2⟩
            left_inv := fun x => by ext; simp
            right_inv := fun x => by ext; simp }
        have h2 : Nat.card ↥T.toAddSubgroup = Nat.card ↥T := by
          refine Nat.card_congr ?_
          exact
          { toFun := fun x => ⟨x.1, (Submodule.mem_toAddSubgroup T).mp x.2⟩
            invFun := fun x => ⟨x.1, (Submodule.mem_toAddSubgroup T).mpr x.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun x => by ext; rfl }
        rw [h1, h2]
      rw [hcard]
      calc Nat.card ↥T = Nat.card F ^ Module.finrank F T :=
              @Module.natCard_eq_pow_finrank F ↥T _ _ _ hTfinite
        _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_right Nat.card_pos hsmall
    · intro a ha
      have htoAdd : Multiplicative.toAdd (a w * w⁻¹) = toAddMap a wvec - wvec := by
        rw [toAdd_mul, toAdd_inv, sub_eq_add_neg]
        simp [toAddMap, wvec]
      show Multiplicative.toAdd (a w * w⁻¹) ∈ T
      rw [htoAdd]
      exact hdispT a ha
  ·
    have hT3 : Module.finrank F T = 3 := by omega
    have hTcard3 : Nat.card ↥T = Nat.card F ^ 3 := by
      have hcard := @Module.natCard_eq_pow_finrank F ↥T _ _ _ hTfinite
      rw [hcard, hT3]
    have hDfin : Module.finrank F D = 3 := by
      have h1 : Module.finrank F T ≤ Module.finrank F D :=
        Submodule.finrank_mono inf_le_left
      have h2 : Module.finrank F T ≤ Module.finrank F (B.orthogonal D) :=
        Submodule.finrank_mono inf_le_right
      rw [LinearMap.BilinForm.finrank_orthogonal hQnd, hV6] at h2
      omega
    have hDperpFin : Module.finrank F (B.orthogonal D) = 3 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hQnd, hV6, hDfin]
    have hTD : T = D :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hT3, hDfin])
    have hDperpT : B.orthogonal D = T :=
      (Submodule.eq_of_le_of_finrank_eq inf_le_right
        (by rw [hT3, hDperpFin])).symm
    let T0 : AddSubgroup (OW F) :=
      { carrier := {v | v ∈ T ∧ Q v = 0}
        zero_mem' := by
          change (0 : OW F) ∈ T ∧ Q 0 = 0
          exact ⟨T.zero_mem, map_zero _⟩
        add_mem' := by
          intro x y hx hy
          change x ∈ T ∧ Q x = 0 at hx
          change y ∈ T ∧ Q y = 0 at hy
          change x + y ∈ T ∧ Q (x + y) = 0
          refine ⟨T.add_mem hx.1 hy.1, ?_⟩
          rw [QuadraticMap.map_add Q x y, hx.2, hy.2, hTorth x hx.1 y hy.1]
          simp
        neg_mem' := by
          intro x hx
          change x ∈ T ∧ Q x = 0 at hx
          change -x ∈ T ∧ Q (-x) = 0
          refine ⟨T.neg_mem hx.1, ?_⟩
          rw [QuadraticMap.map_neg Q x, hx.2] }
    have hT0mem : ∀ {v : OW F}, v ∈ T0 ↔ v ∈ T ∧ Q v = 0 := by
      intro v
      change (v ∈ T ∧ Q v = 0) ↔ (v ∈ T ∧ Q v = 0)
      rfl
    let φ : ↥T →+ F := AddMonoidHom.mk' (fun t => Q t.1) (fun t t' => by
      change Q ((t : OW F) + (t' : OW F)) = Q t.1 + Q t'.1
      rw [QuadraticMap.map_add Q (t : OW F) (t' : OW F),
        hTorth t.1 t.2 t'.1 t'.2]
      simp)
    have hkerφT0 : Nat.card ↥φ.ker = Nat.card ↥T0 := by
      refine Nat.card_congr ?_
      exact
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, (hT0mem.mp y.2).1⟩, (hT0mem.mp y.2).2⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun y => by ext; rfl }
    have hT0ts : Nat.card ↥T0 ≤ Nat.card F ^ 2 := by
      refine ts_card_le hirr T0 (fun x hx => ?_)
      have hx' : x ∈ T ∧ Q x = 0 := hT0mem.mp hx
      rw [← quadMinus_eq_stated]
      exact hx'.2
    have hrangeφ : Nat.card ↥φ.range ≤ Nat.card F :=
      Nat.card_le_card_of_injective (fun x : ↥φ.range => (x : F))
        (fun x y h => Subtype.ext h)
    have hT0ge : Nat.card F ^ 2 ≤ Nat.card ↥T0 := by
      have h1 : Nat.card F ^ 3 ≤ Nat.card ↥φ.ker * Nat.card F := by
        calc Nat.card F ^ 3 = Nat.card ↥T := hTcard3.symm
          _ = Nat.card ↥φ.ker * Nat.card ↥φ.range :=
              AddSubgroup.card_ker_mul_card_range φ |>.symm
          _ ≤ Nat.card ↥φ.ker * Nat.card F := Nat.mul_le_mul_left _ hrangeφ
      rw [hkerφT0] at h1
      rw [show Nat.card F ^ 3 = Nat.card F ^ 2 * Nat.card F by ring] at h1
      exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
    have hT0card : Nat.card ↥T0 = Nat.card F ^ 2 := le_antisymm hT0ts hT0ge
    have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
    have hT0gt : 1 < Nat.card ↥T0 := by
      rw [hT0card]
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq2 2
    have hT0ncard : 1 < (T0 : Set (OW F)).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact hT0gt
    obtain ⟨t₀, ht₀T0, ht₀ne⟩ := Set.exists_ne_of_one_lt_ncard hT0ncard (0 : OW F)
    have ht₀T : t₀ ∈ T := (hT0mem.mp ht₀T0).1
    have ht₀Q : Q t₀ = 0 := (hT0mem.mp ht₀T0).2
    have hnotall : ¬ ∀ x : OW F, (polarBilin Q x) t₀ = 0 := by
      intro h
      exact ht₀ne (hQnd.2 t₀ h)
    push Not at hnotall
    obtain ⟨w, hw⟩ := hnotall
    have hw' : polar Q w t₀ ≠ 0 := by
      simpa [polarBilin_apply_apply] using hw
    have hwD : w ∉ D := by
      intro hwDmem
      have h0 : ∀ t : OW F, t ∈ T0 → polar Q w t = 0 := by
        intro t ht
        have htT : t ∈ T := (hT0mem.mp ht).1
        rw [hTmem] at htT
        exact htT.2 w hwDmem
      exact hw' (h0 t₀ ht₀T0)
    have hdispPerp : ∀ a ∈ A, toAddMap a w - w ∈ B.orthogonal D := by
      intro a ha
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro d hd
      change polar Q d (toAddMap a w - w) = 0
      rw [polar_comm Q d (toAddMap a w - w), polar_sub_left]
      have h1 : polar Q (toAddMap a w) (toAddMap a d) = polar Q w d :=
        hBpres a ha w d
      rw [hDfix hd a ha] at h1
      rw [h1, sub_self]
    have hdispT : ∀ a ∈ A, toAddMap a w - w ∈ T := by
      intro a ha
      rw [← hDperpT]
      exact hdispPerp a ha
    let ψ : ↥T →+ F := AddMonoidHom.mk' (fun t => Q t.1 + polar Q w t.1)
      (fun t t' => by
        change Q ((t : OW F) + (t' : OW F)) +
          polar Q w ((t : OW F) + (t' : OW F)) =
          (Q t.1 + polar Q w t.1) + (Q t'.1 + polar Q w t'.1)
        rw [QuadraticMap.map_add Q (t : OW F) (t' : OW F), polar_add_right,
          hTorth t.1 t.2 t'.1 t'.2]
        abel)
    have hψsurj : Function.Surjective ψ := by
      intro d
      let bb : F := polar Q w t₀
      have hbb : bb ≠ 0 := hw'
      have hmem : (d / bb) • t₀ ∈ T := T.smul_mem (d / bb) ht₀T
      refine ⟨⟨(d / bb) • t₀, hmem⟩, ?_⟩
      change Q ((d / bb) • t₀) + polar Q w ((d / bb) • t₀) = d
      rw [QuadraticMap.map_smul, ht₀Q, polar_smul_right]
      simp only [smul_eq_mul, mul_zero, zero_add]
      exact div_mul_cancel₀ d hbb
    have hrangeψ : Nat.card ↥ψ.range = Nat.card F := by
      have hbij : Function.Bijective (fun x : ↥ψ.range => (x : F)) :=
        ⟨fun x y h => Subtype.ext h, fun d => by
          obtain ⟨t, ht⟩ := hψsurj d
          exact ⟨⟨ψ t, ⟨t, rfl⟩⟩, ht⟩⟩
      exact Nat.card_congr (Equiv.ofBijective _ hbij)
    have hkerψ : Nat.card ↥ψ.ker = Nat.card F ^ 2 := by
      have hkm := AddSubgroup.card_ker_mul_card_range ψ
      rw [hTcard3, hrangeψ] at hkm
      rw [show Nat.card F ^ 3 = Nat.card F ^ 2 * Nat.card F by ring] at hkm
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hkm
    let K' : AddSubgroup (OW F) := ψ.ker.map T.subtype
    have hK'card : Nat.card ↥K' ≤ Nat.card F ^ 2 := by
      have hsurj : Function.Surjective (fun x : ↥ψ.ker =>
          (⟨T.subtype x.1, AddSubgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩ : ↥K')) := by
        intro y
        obtain ⟨k, hk, hky⟩ := AddSubgroup.mem_map.mp y.2
        refine ⟨⟨k, hk⟩, ?_⟩
        exact Subtype.ext hky
      calc Nat.card ↥K' ≤ Nat.card ↥ψ.ker := Nat.card_le_card_of_surjective _ hsurj
        _ = Nat.card F ^ 2 := hkerψ
    refine ⟨Multiplicative.ofAdd w, ?_, AddSubgroup.toSubgroup K', ?_, ?_⟩
    · intro h
      exact hwD h
    · have hcard : Nat.card ↥(AddSubgroup.toSubgroup K') = Nat.card ↥K' := by
        refine Nat.card_congr ?_
        exact
        { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (OW F)), x.2⟩
          invFun := fun x => ⟨Multiplicative.ofAdd (x : OW F), by simpa using x.2⟩
          left_inv := fun x => by ext; simp
          right_inv := fun x => by ext; simp }
      rw [hcard]
      exact hK'card
    · intro a ha
      have htoAdd : Multiplicative.toAdd (a (Multiplicative.ofAdd w) *
          (Multiplicative.ofAdd w)⁻¹) = toAddMap a w - w := by
        rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg]
      show Multiplicative.toAdd (a (Multiplicative.ofAdd w) *
        (Multiplicative.ofAdd w)⁻¹) ∈ K'
      rw [htoAdd]
      refine AddSubgroup.mem_map.mpr ⟨⟨toAddMap a w - w, hdispT a ha⟩, ?_, rfl⟩
      show ψ ⟨toAddMap a w - w, hdispT a ha⟩ = 0
      change Q (toAddMap a w - w) + polar Q w (toAddMap a w - w) = 0
      have hQaw : Q (toAddMap a w) = Q w := by
        change quadMinus 3 F b c (toAddMap a w) = quadMinus 3 F b c w
        rw [quadMinus_eq_stated, quadMinus_eq_stated]
        exact hiso a ha w
      have hdispEq : toAddMap a w = w + (toAddMap a w - w) := by abel
      have h1 : Q (w + (toAddMap a w - w)) = Q w := by
        rw [← hdispEq, hQaw]
      rw [QuadraticMap.map_add Q w (toAddMap a w - w)] at h1
      have h2 : Q w + (Q (toAddMap a w - w) + polar Q w (toAddMap a w - w)) =
          Q w + 0 := by
        rw [add_zero]
        simpa [add_assoc] using h1
      exact add_left_cancel h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

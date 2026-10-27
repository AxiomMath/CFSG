module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.Quasithin.Vol2.Ch6SL2Fix

import CFSG.Quasithin.Recognition.St84.Sec6BaumannS3
import CFSG.Quasithin.Vol2.Ch3n317A5
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1Rad
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement MatrixGroups

namespace SL2Nat

variable {F : Type} [Field F] [Finite F] [CharP F 2]

def e1 : Fin 2 → F := ![1, 0]

def e2 : Fin 2 → F := ![0, 1]

def lin (A : SL(2, F)) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  Matrix.SpecialLinearGroup.toLin' A

theorem lin_apply (A : SL(2, F)) (v : Fin 2 → F) :
    lin A v = (A : Matrix (Fin 2) (Fin 2) F).mulVec v := by
  show Matrix.SpecialLinearGroup.toLin' A v = _
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]

def fixedSub (R : Subgroup SL(2, F)) : Submodule F (Fin 2 → F) where
  carrier := {v | ∀ r ∈ R, lin r v = v}
  zero_mem' := by intro r _; exact map_zero _
  add_mem' := by
    intro v w hv hw r hr
    rw [map_add, hv r hr, hw r hr]
  smul_mem' := by
    intro c v hv r hr
    rw [LinearEquiv.map_smul, hv r hr]

theorem mem_fixedSub {R : Subgroup SL(2, F)} {v : Fin 2 → F} :
    v ∈ fixedSub R ↔ ∀ r ∈ R, lin r v = v := Iff.rfl

@[expose] def commSub (R : Subgroup SL(2, F)) : Submodule F (Fin 2 → F) :=
  Submodule.span F {w | ∃ r ∈ R, ∃ v : Fin 2 → F, w = lin r v - v}

theorem sub_mem_commSub {R : Subgroup SL(2, F)} {r : SL(2, F)} (hr : r ∈ R)
    (v : Fin 2 → F) : lin r v - v ∈ commSub R :=
  Submodule.subset_span ⟨r, hr, v, rfl⟩

theorem conj_lin (B r : SL(2, F)) (v : Fin 2 → F) :
    lin (B * r * B⁻¹) v = lin B (lin r (lin B⁻¹ v)) := by
  show Matrix.SpecialLinearGroup.toLin' (B * r * B⁻¹) v =
    Matrix.SpecialLinearGroup.toLin' B (Matrix.SpecialLinearGroup.toLin' r
      (Matrix.SpecialLinearGroup.toLin' B⁻¹ v))
  rw [map_mul, map_mul, map_inv]
  exact LinearEquiv.mul_apply _ _ _

theorem fixedSub_sl2Stab_eq_span {v : Fin 2 → F} (hv : v ≠ 0) :
    fixedSub (sl2Stab v) = Submodule.span F {v} := by
  have hne : sl2Stab v ≠ ⊥ := by
    intro hbot
    have hcard := card_sl2Stab hv
    rw [hbot, Subgroup.card_bot] at hcard
    have h2 : 2 ≤ Nat.card F := by
      haveI : Nontrivial F := inferInstance
      exact Finite.one_lt_card
    omega
  refine le_antisymm ?_ ?_
  · intro w hw
    have hw' : ∀ A ∈ sl2Stab v, (A : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
      intro A hA
      rw [← lin_apply]
      exact hw A hA
    obtain ⟨c, hc⟩ := fixed_eq_line (sl2Stab v) hne hv (fun A hA => hA) hw'
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · rw [Submodule.span_le]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact fun A hA => by rw [lin_apply]; exact hA

theorem commSub_sl2Stab_le_fixedSub {v : Fin 2 → F} (hv : v ≠ 0) :
    commSub (sl2Stab v) ≤ fixedSub (sl2Stab v) := by
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
  have hB' : lin B e1 = v := by
    rw [lin_apply, e1]; exact hB
  rw [commSub, Submodule.span_le]
  rintro w ⟨r, hr, u, rfl⟩
  obtain ⟨b, rfl⟩ := (mem_sl2Stab_iff hB r).mp hr
  refine (mem_fixedSub).mpr ?_
  intro A hA
  have hBu : lin B (lin B⁻¹ u) = u := by
    show Matrix.SpecialLinearGroup.toLin' B (Matrix.SpecialLinearGroup.toLin' B⁻¹ u) = u
    rw [map_inv]
    exact LinearEquiv.apply_symm_apply _ _
  have hx : lin (sl2X (b : F)) (lin B⁻¹ u) - lin B⁻¹ u =
      (b * (lin B⁻¹ u) 1) • e1 := by
    rw [lin_apply, sl2X_mulVec]
    ext i
    fin_cases i <;> simp [e1]
  have hsub : lin (B * sl2X (b : F) * B⁻¹) u - u =
      (b * (lin B⁻¹ u) 1) • v := by
    rw [conj_lin]
    have h1 : lin B (lin (sl2X (b : F)) (lin B⁻¹ u)) - u =
        lin B (lin (sl2X (b : F)) (lin B⁻¹ u)) - lin B (lin B⁻¹ u) := by rw [hBu]
    rw [h1, ← map_sub, hx, LinearEquiv.map_smul, hB']
  rw [hsub, LinearEquiv.map_smul]
  rw [show lin A v = v from by rw [lin_apply]; exact hA]

theorem commSub_sl2Stab_ne_bot {v : Fin 2 → F} (hv : v ≠ 0) :
    commSub (sl2Stab v) ≠ ⊥ := by
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
  have hB' : lin B e1 = v := by
    rw [lin_apply, e1]; exact hB
  intro hbot
  have hr : B * sl2X (1 : F) * B⁻¹ ∈ sl2Stab v := (mem_sl2Stab_iff hB _).mpr ⟨1, rfl⟩
  have hmem : lin (B * sl2X (1 : F) * B⁻¹) (lin B e2) - lin B e2 ∈ commSub (sl2Stab v) :=
    sub_mem_commSub hr _
  rw [hbot, Submodule.mem_bot] at hmem
  apply hv
  have hBinv : lin B⁻¹ (lin B e2) = e2 := by
    show Matrix.SpecialLinearGroup.toLin' B⁻¹ (Matrix.SpecialLinearGroup.toLin' B e2) = e2
    rw [map_inv]
    exact LinearEquiv.symm_apply_apply _ _
  have hx : lin (sl2X (1 : F)) e2 - e2 = e1 := by
    rw [lin_apply, sl2X_mulVec]
    ext i
    fin_cases i <;> simp [e1, e2]
  have hBBinv : lin B (lin B⁻¹ (lin B e2)) = lin B e2 := by
    show Matrix.SpecialLinearGroup.toLin' B (Matrix.SpecialLinearGroup.toLin' B⁻¹
      (Matrix.SpecialLinearGroup.toLin' B e2)) = Matrix.SpecialLinearGroup.toLin' B e2
    rw [map_inv]
    exact LinearEquiv.apply_symm_apply _ _
  have hx' : lin (sl2X (1 : F)) (lin B⁻¹ (lin B e2)) - lin B⁻¹ (lin B e2) = e1 := by
    rw [hBinv, hx]
  have h1 : lin (B * sl2X (1 : F) * B⁻¹) (lin B e2) - lin B e2 = v := by
    rw [conj_lin]
    have h2 : lin B (lin (sl2X (1 : F)) (lin B⁻¹ (lin B e2))) - lin B e2 =
        lin B (lin (sl2X (1 : F)) (lin B⁻¹ (lin B e2))) - lin B (lin B⁻¹ (lin B e2)) := by
      rw [hBBinv]
    rw [h2, ← map_sub, hx', hB']
  rw [← h1, hmem]

theorem commSub_sl2Stab_eq {v : Fin 2 → F} (hv : v ≠ 0) :
    commSub (sl2Stab v) = fixedSub (sl2Stab v) := by
  have hle := commSub_sl2Stab_le_fixedSub hv
  have hne := commSub_sl2Stab_ne_bot hv
  rw [fixedSub_sl2Stab_eq_span hv] at hle
  rw [fixedSub_sl2Stab_eq_span hv]
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle hw)
  have hc0 : c ≠ 0 := by
    intro h0
    apply hw0
    rw [← hc, h0, zero_smul]
  have hvmem : v ∈ commSub (sl2Stab v) := by
    have := (commSub (sl2Stab v)).smul_mem c⁻¹ hw
    rwa [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  refine le_antisymm hle ?_
  rw [Submodule.span_le]
  exact Set.singleton_subset_iff.mpr hvmem

theorem fixedSub_eq_span_of_card {R : Subgroup SL(2, F)} (hR : IsPGroup 2 R)
    (hcard : Nat.card R = Nat.card F) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ fixedSub R = Submodule.span F {v} := by
  haveI : Fintype F := Fintype.ofFinite F
  have hRne : R ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    have h2 : 2 ≤ Nat.card F := by
      haveI : Nontrivial F := inferInstance
      exact Finite.one_lt_card
    omega
  have hF : 2 ∣ Nat.card F := by
    obtain ⟨m, hp, hm⟩ := FiniteField.card F 2
    have hm0 : 0 < (m : ℕ) := m.pos
    rw [Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self 2 hm0.ne'
  obtain ⟨v, hv, hfix⟩ := exists_fixed_vector hF R hR
  refine ⟨v, hv, ?_⟩
  refine le_antisymm ?_ ?_
  · intro w hw
    have hw' : ∀ A ∈ R, (A : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
      intro A hA
      rw [← lin_apply]
      exact hw A hA
    obtain ⟨c, hc⟩ := fixed_eq_line R hRne hv hfix hw'
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · rw [Submodule.span_le]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hfix

theorem finrank_fixedSub_of_card {R : Subgroup SL(2, F)} (hR : IsPGroup 2 R)
    (hcard : Nat.card R = Nat.card F) : Module.finrank F ↥(fixedSub R) = 1 := by
  obtain ⟨v, hv, hW⟩ := fixedSub_eq_span_of_card hR hcard
  rw [hW]
  exact finrank_span_singleton hv

theorem eq_one_of_odd_order_of_fixed {A : SL(2, F)} {v : Fin 2 → F}
    (hv : v ≠ 0) (hodd : Odd (orderOf A))
    (hfix : (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : A = 1 := by
  have hsq : A ^ 2 = 1 := CFSG.RankThree.PartTwo.Sec16.ProofKS1624KP1.sq_eq_one_of_fix hv hfix
  have hdvd : orderOf A ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hodd
    exact (by norm_num : ¬ Odd 2) hodd

theorem natCard_fixedSub_of_card {R : Subgroup SL(2, F)} (hR : IsPGroup 2 R)
    (hcard : Nat.card R = Nat.card F) : Nat.card ↥(fixedSub R) = Nat.card F := by
  haveI : Fintype F := Fintype.ofFinite F
  have h2 : 2 ≤ Nat.card F := by
    haveI : Nontrivial F := inferInstance
    exact Finite.one_lt_card
  have hRne : R ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hF : 2 ∣ Nat.card F := by
    obtain ⟨m, hp, hm⟩ := FiniteField.card F 2
    have hm0 : 0 < (m : ℕ) := m.pos
    rw [Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self 2 hm0.ne'
  obtain ⟨v, hv, hfix⟩ := exists_fixed_vector hF R hR
  have hfixed : fixedSub R = Submodule.span F {v} := by
    refine le_antisymm ?_ ?_
    · intro w hw
      obtain ⟨c, hc⟩ := fixed_eq_line R hRne hv hfix hw
      rw [hc]
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    · rw [Submodule.span_le]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hfix
  rw [hfixed]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => Classical.choose (Submodule.mem_span_singleton.mp x.2)
      invFun := fun c => (⟨c • v, Submodule.smul_mem _ c (Submodule.subset_span rfl)⟩ :
        ↥(Submodule.span F {v}))
      left_inv := fun x => ?_
      right_inv := fun c => ?_ }
  · apply Subtype.ext
    exact Classical.choose_spec (Submodule.mem_span_singleton.mp x.2)
  · have h := Classical.choose_spec (Submodule.mem_span_singleton.mp
      (Submodule.smul_mem (Submodule.span F {v}) c (Submodule.subset_span rfl)))
    exact smul_left_injective F hv h

theorem commSub_eq_fixedSub_of_card {R : Subgroup SL(2, F)} (hR : IsPGroup 2 R)
    (hcard : Nat.card R = Nat.card F) : commSub R = fixedSub R := by
  have h2 : 2 ≤ Nat.card F := by
    haveI : Nontrivial F := inferInstance
    exact Finite.one_lt_card
  have hRne : R ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  haveI : Fintype F := Fintype.ofFinite F
  have hF : 2 ∣ Nat.card F := by
    obtain ⟨m, hp, hm⟩ := FiniteField.card F 2
    have hm0 : 0 < (m : ℕ) := m.pos
    rw [Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self 2 hm0.ne'
  obtain ⟨v, hv, hfix⟩ := exists_fixed_vector hF R hR
  have hfixed : fixedSub R = Submodule.span F {v} := by
    refine le_antisymm ?_ ?_
    · intro w hw
      have hw' : ∀ A ∈ R, (A : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
        intro A hA
        rw [← lin_apply]
        exact hw A hA
      obtain ⟨c, hc⟩ := fixed_eq_line R hRne hv hfix hw'
      rw [hc]
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    · rw [Submodule.span_le]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact fun r hr => by rw [lin_apply]; exact hfix r hr
  have hRsub : R ≤ sl2Stab v := fun r hr => hfix r hr
  have hReq : R = sl2Stab v := by
    refine Subgroup.eq_of_le_of_card_ge hRsub ?_
    rw [card_sl2Stab hv, hcard]
  rw [hReq, commSub_sl2Stab_eq hv]

theorem fixedSub_inf_sup_of_ne {R R' : Subgroup SL(2, F)}
    (hR : IsPGroup 2 R) (hRcard : Nat.card R = Nat.card F)
    (hR' : IsPGroup 2 R') (hR'card : Nat.card R' = Nat.card F)
    (hne : R ≠ R') :
    fixedSub R ⊓ fixedSub R' = ⊥ ∧ fixedSub R ⊔ fixedSub R' = ⊤ := by
  obtain ⟨v, hv, hWv⟩ := fixedSub_eq_span_of_card hR hRcard
  obtain ⟨v', hv', hW'v⟩ := fixedSub_eq_span_of_card hR' hR'card
  let W : Submodule F (Fin 2 → F) := fixedSub R
  let W' : Submodule F (Fin 2 → F) := fixedSub R'
  have hWv' : W = Submodule.span F {v} := hWv
  have hW'v' : W' = Submodule.span F {v'} := hW'v
  have hfinW : Module.finrank F ↥W = 1 := by
    change Module.finrank F ↥(fixedSub R) = 1
    exact finrank_fixedSub_of_card hR hRcard
  have hfinW' : Module.finrank F ↥W' = 1 := by
    change Module.finrank F ↥(fixedSub R') = 1
    exact finrank_fixedSub_of_card hR' hR'card
  have hfinV : Module.finrank F (Fin 2 → F) = 2 := by
    simpa using (Module.finrank_fin_fun F (n := 2))
  have hWne : W ≠ W' := by
    intro hEq
    have hvW : v ∈ W := by
      rw [hWv']
      exact Submodule.subset_span rfl
    have hvW' : v ∈ W' := by rwa [hEq] at hvW
    have hRsub : R ≤ sl2Stab v := by
      intro r hr
      rw [mem_sl2Stab, ← lin_apply]
      exact (mem_fixedSub).mp (by change v ∈ W; exact hvW) r hr
    have hR'sub : R' ≤ sl2Stab v := by
      intro r hr
      rw [mem_sl2Stab, ← lin_apply]
      exact (mem_fixedSub).mp (by change v ∈ W'; exact hvW') r hr
    have hReq : R = sl2Stab v := by
      refine Subgroup.eq_of_le_of_card_ge hRsub ?_
      rw [card_sl2Stab hv, hRcard]
    have hR'eq : R' = sl2Stab v := by
      refine Subgroup.eq_of_le_of_card_ge hR'sub ?_
      rw [card_sl2Stab hv, hR'card]
    exact hne (hReq.trans hR'eq.symm)
  have hinf : W ⊓ W' = ⊥ := by
    have hlt : W ⊓ W' < W := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro hEq
      have hle : W ≤ W' := by rw [← hEq]; exact inf_le_right
      exact hWne (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinW, hfinW']))
    have hzero : Module.finrank F ↥(W ⊓ W') = 0 := by
      have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    exact (Submodule.finrank_eq_zero).mp hzero
  have hsup : W ⊔ W' = ⊤ := by
    have hlt : W < W ⊔ W' := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro hEq
      have hle : W' ≤ W := by
        calc W' ≤ W ⊔ W' := le_sup_right
          _ = W := hEq.symm
      exact hWne (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinW', hfinW])).symm
    have hge : 2 ≤ Module.finrank F ↥(W ⊔ W') := by
      have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hle : Module.finrank F ↥(W ⊔ W') ≤ 2 := by
      have hmono := Submodule.finrank_mono (le_top : W ⊔ W' ≤ ⊤)
      rw [finrank_top, hfinV] at hmono
      exact hmono
    have heq : Module.finrank F ↥(W ⊔ W') = 2 := le_antisymm hle hge
    exact Submodule.eq_top_of_finrank_eq (by rw [heq, hfinV])
  exact ⟨by simpa [W, W'] using hinf, by simpa [W, W'] using hsup⟩

end SL2Nat
section BetaTop

variable {X : Type} [Group X] [Finite X]
variable {E Z : Subgroup X} [E.Normal] [Z.Normal]
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {α : X →* SL(2, F)}
variable {β : ↥E →* Multiplicative (Fin 2 → F)}
variable {n : ℕ}

private def IsBetaEquiv (α : X →* SL(2, F)) (β : ↥E →* Multiplicative (Fin 2 → F)) : Prop :=
  ∀ ℓ : X, ∀ u v : ↥E, (v : X) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

private theorem card_map_sylow_eq_card (hF : Fintype.card F = 2 ^ n)
    (hα : Function.Surjective α) (hK : IsPGroup 2 α.ker) {A : Subgroup X}
    (hA : IsSylowTwoOf A ⊤) : Nat.card ↥(A.map α) = Nat.card F := by
  have hFcard : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hnorm : (⊤ : Subgroup X) ≤ Subgroup.normalizer (α.ker : Set X) :=
    le_of_eq (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm
  have hker_le : α.ker ≤ A := hA.le_of_normalizes le_top hnorm hK
  have hidx : ¬ 2 ∣ (A.map α).index := by
    rw [Subgroup.index_map_eq A hα hker_le]
    have h := hA.2.2
    rwa [show (A.subgroupOf ⊤).index = A.index from Subgroup.relIndex_top_right A] at h
  have hSyl : IsSylowTwoOf (A.map α) ⊤ := by
    refine ⟨le_top, hA.2.1.map α, ?_⟩
    rwa [show ((A.map α).subgroupOf ⊤).index = (A.map α).index from
      Subgroup.relIndex_top_right (A.map α)]
  have hSL : Nat.card (SL(2, F)) = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.Ch3n317A5.card_SL_two_pow hFcard
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at hFcard
      exact absurd hFcard (Finite.one_lt_card (α := F)).ne'
    · exact hpos
  have hodd : Odd (4 ^ n - 1) := by
    have h4 : Even (4 ^ n) := Even.pow_of_ne_zero (by norm_num : Even 4) (by omega)
    exact Nat.Even.sub_odd (Nat.one_le_pow n 4 (by norm_num)) h4 (by norm_num : Odd 1)
  have hm : ¬ 2 ∣ 4 ^ n - 1 := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  have hres := CFSG.Quasithin.H13.FiveNorm.card_eq_of_isSylowTwoOf_top
    (k := n) (m := 4 ^ n - 1) hSyl hSL hm
  exact hres.trans hFcard.symm

private theorem mem_relCent_iff_fixed (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) {A : Subgroup X} (e : ↥E) :
    (e : X) ∈ relCent E Z A ↔
      Multiplicative.toAdd (β e) ∈ SL2Nat.fixedSub (A.map α) := by
  have hEZ : E ≤ Subgroup.normalizer (Z : Set X) := Subgroup.le_normalizer_of_normal
  rw [mem_relCent hEZ, SL2Nat.mem_fixedSub]
  constructor
  · rintro ⟨-, hcomm⟩
    intro r hr
    rw [SL2Nat.lin_apply]
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
    have haA : a ∈ A := ha
    let v : ↥E := ⟨a * (e : X) * a⁻¹, (inferInstance : E.Normal).conj_mem (e : X) e.2 a⟩
    have hv : (v : X) = a * (e : X) * a⁻¹ := rfl
    have hact := hβe a e v hv
    have hβve : β v = β e := by
      have hmem : v * e⁻¹ ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        have hcoe : ((v * e⁻¹ : ↥E) : X) = ⁅a, (e : X)⁆ := by
          simp [v, commutatorElement_def]
        rw [hcoe, ← commutatorElement_inv (e : X) a]
        exact Z.inv_mem (hcomm a haA)
      have h1 : β (v * e⁻¹) = 1 := MonoidHom.mem_ker.mp hmem
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    rw [← hact, hβve]
  · rintro hfix
    refine ⟨e.2, fun a ha => ?_⟩
    have hfix' : (α a : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (β e)) = Multiplicative.toAdd (β e) := by
      have h := hfix (α a) (Subgroup.mem_map_of_mem α ha)
      rwa [SL2Nat.lin_apply] at h
    let v : ↥E := ⟨a * (e : X) * a⁻¹, (inferInstance : E.Normal).conj_mem (e : X) e.2 a⟩
    have hv : (v : X) = a * (e : X) * a⁻¹ := rfl
    have hβv : β v = β e := by
      apply Multiplicative.toAdd.injective
      rw [hβe a e v hv, hfix']
    have hmem : v * e⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβv, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at hmem
    have hcoe : ((v * e⁻¹ : ↥E) : X) = ⁅a, (e : X)⁆ := by
      simp [v, commutatorElement_def]
    rw [hcoe] at hmem
    rw [← commutatorElement_inv a (e : X)]
    exact Z.inv_mem hmem

private theorem mem_map_relCent_iff_fixed (hβk : β.ker = Z.subgroupOf E)
    (hβ : Function.Surjective β) (hβe : IsBetaEquiv α β) {A : Subgroup X}
    {v : Multiplicative (Fin 2 → F)} :
    v ∈ ((relCent E Z A).subgroupOf E).map β ↔
      Multiplicative.toAdd v ∈ SL2Nat.fixedSub (A.map α) := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (mem_relCent_iff_fixed hβk hβe e).mp (Subgroup.mem_subgroupOf.mp he)
  · intro hv
    obtain ⟨e, he⟩ := hβ v
    refine ⟨e, Subgroup.mem_subgroupOf.mpr ((mem_relCent_iff_fixed hβk hβe e).mpr ?_), he⟩
    rwa [he]

private def relCentMapEquivFixed (hβk : β.ker = Z.subgroupOf E)
    (hβ : Function.Surjective β) (hβe : IsBetaEquiv α β) {A : Subgroup X} :
    ↥(((relCent E Z A).subgroupOf E).map β) ≃ ↥(SL2Nat.fixedSub (A.map α)) where
  toFun v := ⟨Multiplicative.toAdd v.1,
    (mem_map_relCent_iff_fixed hβk hβ hβe).mp v.2⟩
  invFun v := ⟨Multiplicative.ofAdd v.1,
    (mem_map_relCent_iff_fixed hβk hβ hβe).mpr (by simpa using v.2)⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

private theorem natCard_map_eq_relIndex (hβk : β.ker = Z.subgroupOf E) {K : Subgroup X}
    (hKE : K ≤ E) : Nat.card ↥((K.subgroupOf E).map β) = Z.relIndex K := by
  let K' : Subgroup ↥E := K.subgroupOf E
  let f : ↥K' →* Multiplicative (Fin 2 → F) := β.comp K'.subtype
  have hker : f.ker = (Z.subgroupOf E).subgroupOf K' := by
    ext x
    show β (x : ↥E) = 1 ↔ ((x : ↥E) : X) ∈ Z
    rw [← MonoidHom.mem_ker (f := β), hβk, Subgroup.mem_subgroupOf]
  have hrange : f.range = K'.map β := by
    rw [show f = β.comp K'.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  calc
    Nat.card ↥((K.subgroupOf E).map β) = Nat.card ↥f.range := by rw [hrange]
    _ = f.ker.index := (Subgroup.index_ker f).symm
    _ = Z.relIndex K := by
      rw [hker]
      exact Subgroup.relIndex_subgroupOf hKE

private theorem line_beta (hF : Fintype.card F = 2 ^ n)
    (hα : Function.Surjective α) (hK : IsPGroup 2 α.ker)
    (hβ : Function.Surjective β) (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) (hZE : Z ≤ E) {A : Subgroup X}
    (hA : IsSylowTwoOf A ⊤) : Z.relIndex (relCent E Z A) = 2 ^ n := by
  have hR2 : IsPGroup 2 (A.map α) := hA.2.1.map α
  have hRcard : Nat.card ↥(A.map α) = Nat.card F :=
    card_map_sylow_eq_card hF hα hK hA
  have hZle : Z ≤ relCent E Z A := by
    intro z hz
    rw [mem_relCent (Subgroup.le_normalizer_of_normal (H := Z) (K := E))]
    refine ⟨hZE hz, fun a _ => ?_⟩
    rw [commutatorElement_def]
    have h := Z.mul_mem hz ((inferInstance : Z.Normal).conj_mem z⁻¹ (Z.inv_mem hz) a)
    simpa [mul_assoc] using h
  have hrelE : relCent E Z A ≤ E := fun x hx => hx.1
  calc
    Z.relIndex (relCent E Z A) =
        Nat.card ↥(((relCent E Z A).subgroupOf E).map β) :=
      (natCard_map_eq_relIndex hβk hrelE).symm
    _ = Nat.card ↥(SL2Nat.fixedSub (A.map α)) :=
      Nat.card_congr (relCentMapEquivFixed hβk hβ hβe)
    _ = Nat.card F := SL2Nat.natCard_fixedSub_of_card hR2 hRcard
    _ = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]

private theorem index_beta (hF : Fintype.card F = 2 ^ n)
    (hβ : Function.Surjective β) (hβk : β.ker = Z.subgroupOf E) :
    Z.relIndex E = 2 ^ (2 * n) := by
  have hmap : (E.subgroupOf E).map β = ⊤ := by
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hβ]
  calc
    Z.relIndex E = Nat.card ↥((E.subgroupOf E).map β) :=
      (natCard_map_eq_relIndex hβk le_rfl).symm
    _ = Nat.card (Multiplicative (Fin 2 → F)) := by rw [hmap, Subgroup.card_top]
    _ = Nat.card (Fin 2 → F) := Nat.card_congr Multiplicative.toAdd
    _ = Nat.card F ^ Nat.card (Fin 2) := Nat.card_fun
    _ = Nat.card F ^ 2 := by
      rw [Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    _ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hF, pow_two, ← pow_add, two_mul]

private theorem comm_le_relCent (hF : Fintype.card F = 2 ^ n)
    (hα : Function.Surjective α) (hK : IsPGroup 2 α.ker)
    (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) (hZE : Z ≤ E) {A : Subgroup X}
    (hA : IsSylowTwoOf A ⊤) : ⁅E, A⁆ ⊔ Z ≤ relCent E Z A := by
  let R : Subgroup SL(2, F) := A.map α
  have hR2 : IsPGroup 2 R := hA.2.1.map α
  have hRcard : Nat.card R = Nat.card F := card_map_sylow_eq_card hF hα hK hA
  have hcommSub : SL2Nat.commSub R = SL2Nat.fixedSub R :=
    SL2Nat.commSub_eq_fixedSub_of_card hR2 hRcard
  have hEA : ⁅E, A⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he a ha
    have hconj : a * e * a⁻¹ ∈ E := (inferInstance : E.Normal).conj_mem e he a
    have hcomm : ⁅a, e⁆ ∈ E := by
      rw [commutatorElement_def]
      exact E.mul_mem hconj (E.inv_mem he)
    rw [← commutatorElement_inv a e]
    exact E.inv_mem hcomm
  let C : Subgroup (Multiplicative (Fin 2 → F)) :=
    AddSubgroup.toSubgroup (SL2Nat.commSub R).toAddSubgroup
  have hcomm_le_X : ⁅E, A⁆ ≤ (C.comap β).map E.subtype := by
    rw [Subgroup.commutator_le]
    intro e he a ha
    let v0 : Fin 2 → F := Multiplicative.toAdd (β ⟨e, he⟩)
    let vE : ↥E := ⟨a * e * a⁻¹, (inferInstance : E.Normal).conj_mem e he a⟩
    have hvE : (vE : X) = a * e * a⁻¹ := rfl
    have hβgen : β (vE * ⟨e, he⟩⁻¹) =
        Multiplicative.ofAdd ((α a : Matrix (Fin 2) (Fin 2) F).mulVec v0 - v0) := by
      apply Multiplicative.toAdd.injective
      have h2 : Multiplicative.toAdd (β (vE * ⟨e, he⟩⁻¹)) =
          Multiplicative.toAdd (β vE) - Multiplicative.toAdd (β ⟨e, he⟩) := by
        rw [map_mul, map_inv]
        simp [sub_eq_add_neg]
      rw [h2, hβe a ⟨e, he⟩ vE hvE]
      rfl
    have hgenComm : (α a : Matrix (Fin 2) (Fin 2) F).mulVec v0 - v0 ∈
        SL2Nat.commSub R := by
      have h := SL2Nat.sub_mem_commSub (R := R) (Subgroup.mem_map_of_mem α ha) v0
      rwa [SL2Nat.lin_apply] at h
    have hgenC : β (vE * ⟨e, he⟩⁻¹) ∈ C := by
      rw [hβgen]
      simpa [C] using hgenComm
    let w : ↥E := ⟨⁅e, a⁆, hEA (Subgroup.commutator_mem_commutator he ha)⟩
    have hw : w = (vE * ⟨e, he⟩⁻¹)⁻¹ := by
      apply Subtype.ext
      change (⁅e, a⁆ : X) = ((vE * ⟨e, he⟩⁻¹ : ↥E) : X)⁻¹
      rw [commutatorElement_def]
      change e * a * e⁻¹ * a⁻¹ = (a * e * a⁻¹ * e⁻¹)⁻¹
      group
    have hwC : β w ∈ C := by
      rw [hw, map_inv]
      exact C.inv_mem hgenC
    refine Subgroup.mem_map.mpr ⟨w, ?_, rfl⟩
    exact Subgroup.mem_comap.mpr hwC
  have hcomm_le_rel : ⁅E, A⁆ ≤ relCent E Z A := by
    intro x hx
    have hxE : x ∈ E := hEA hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hcomm_le_X hx)
    have hyC : β y ∈ C := Subgroup.mem_comap.mp hy
    have hyComm : Multiplicative.toAdd (β y) ∈ SL2Nat.commSub R := by
      simpa [C] using hyC
    have hyFix : Multiplicative.toAdd (β y) ∈ SL2Nat.fixedSub R := by
      rwa [hcommSub] at hyComm
    have hxy : β ⟨x, hxE⟩ = β y := by
      apply congrArg β
      apply Subtype.ext
      exact hyx.symm
    have hxfix : Multiplicative.toAdd (β ⟨x, hxE⟩) ∈ SL2Nat.fixedSub R := by
      rw [hxy]
      exact hyFix
    exact (mem_relCent_iff_fixed hβk hβe ⟨x, hxE⟩).mpr hxfix
  have hZle : Z ≤ relCent E Z A := by
    intro z hz
    rw [mem_relCent (Subgroup.le_normalizer_of_normal (H := Z) (K := E))]
    refine ⟨hZE hz, fun a _ => ?_⟩
    rw [commutatorElement_def]
    have h := Z.mul_mem hz ((inferInstance : Z.Normal).conj_mem z⁻¹ (Z.inv_mem hz) a)
    simpa [mul_assoc] using h
  exact sup_le hcomm_le_rel hZle

private theorem relCent_le_sup (hF : Fintype.card F = 2 ^ n)
    (hα : Function.Surjective α) (hK : IsPGroup 2 α.ker)
    (hβ : Function.Surjective β) (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) {A : Subgroup X}
    (hA : IsSylowTwoOf A ⊤) : relCent E Z A ≤ ⁅E, A⁆ ⊔ Z := by
  let R : Subgroup SL(2, F) := A.map α
  have hR2 : IsPGroup 2 R := hA.2.1.map α
  have hRcard : Nat.card R = Nat.card F := card_map_sylow_eq_card hF hα hK hA
  have hcommSub : SL2Nat.commSub R = SL2Nat.fixedSub R :=
    SL2Nat.commSub_eq_fixedSub_of_card hR2 hRcard
  let P : (Fin 2 → F) → Prop := fun w =>
    ∀ c : F, ∃ y : ↥E, ((y : X) ∈ ⁅E, A⁆ ⊔ Z) ∧
      Multiplicative.toAdd (β y) = c • w
  have hP : ∀ w, w ∈ SL2Nat.commSub R → P w := by
    intro w hw
    rw [show SL2Nat.commSub R = Submodule.span F {w | ∃ r ∈ R, ∃ v : Fin 2 → F,
      w = SL2Nat.lin r v - v} from rfl] at hw
    refine Submodule.span_induction ?mem ?zero ?add ?smul hw
    · rintro w ⟨r, hr, v, rfl⟩ c
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
      obtain ⟨e, heβ⟩ := hβ (Multiplicative.ofAdd (c • v))
      let vE : ↥E := ⟨a * e * a⁻¹, (inferInstance : E.Normal).conj_mem e e.2 a⟩
      have hvE : (vE : X) = a * e * a⁻¹ := rfl
      have hβgen : Multiplicative.toAdd (β (vE * e⁻¹)) =
          c • (SL2Nat.lin (α a) v - v) := by
        have h2 : Multiplicative.toAdd (β (vE * e⁻¹)) =
            Multiplicative.toAdd (β vE) - Multiplicative.toAdd (β e) := by
          rw [map_mul, map_inv]
          simp [sub_eq_add_neg]
        rw [h2, hβe a e vE hvE, heβ]
        simp only [toAdd_ofAdd]
        rw [Matrix.mulVec_smul, SL2Nat.lin_apply, smul_sub]
      have hmemAE : ⁅a, (e : X)⁆ ∈ ⁅E, A⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator ha e.2
      have hy_comm : ((vE * e⁻¹ : ↥E) : X) = ⁅a, (e : X)⁆ := by
        rw [commutatorElement_def]
        change a * e * a⁻¹ * e⁻¹ = ⁅a, (e : X)⁆
        rw [commutatorElement_def]
        rfl
      have hysup : ((vE * e⁻¹ : ↥E) : X) ∈ ⁅E, A⁆ ⊔ Z :=
        Subgroup.mem_sup_left (by rw [hy_comm]; exact hmemAE)
      exact ⟨vE * e⁻¹, hysup, hβgen⟩
    · intro c
      refine ⟨1, Subgroup.mem_sup_right Z.one_mem, ?_⟩
      rw [map_one]
      simp
    · intro w₁ w₂ _ _ ih₁ ih₂ c
      obtain ⟨y₁, hy₁, hy₁β⟩ := ih₁ c
      obtain ⟨y₂, hy₂, hy₂β⟩ := ih₂ c
      refine ⟨y₁ * y₂, (⁅E, A⁆ ⊔ Z).mul_mem hy₁ hy₂, ?_⟩
      rw [map_mul]
      simp [hy₁β, hy₂β, smul_add]
    · intro c w _ ih
      intro d
      obtain ⟨y, hy, hyβ⟩ := ih (d * c)
      refine ⟨y, hy, ?_⟩
      rw [hyβ, smul_smul]
  intro x hx
  have hxE : x ∈ E := hx.1
  let xE : ↥E := ⟨x, hxE⟩
  have hxfix : Multiplicative.toAdd (β xE) ∈ SL2Nat.fixedSub R :=
    (mem_relCent_iff_fixed hβk hβe xE).mp hx
  have hxcomm : Multiplicative.toAdd (β xE) ∈ SL2Nat.commSub R := by
    rw [hcommSub]
    exact hxfix
  obtain ⟨y, hysup, hyβ⟩ := hP _ hxcomm 1
  rw [one_smul] at hyβ
  have hxy : β xE = β y := by
    apply Multiplicative.toAdd.injective
    rw [hyβ]
  have hmem : xE * y⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at hmem
  have hdiff : x * (y : X)⁻¹ ∈ Z := by simpa using hmem
  have hx_eq : x = (x * (y : X)⁻¹) * (y : X) := by group
  rw [hx_eq]
  exact (⁅E, A⁆ ⊔ Z).mul_mem (Subgroup.mem_sup_right hdiff) hysup

private theorem comm_eq_beta (hF : Fintype.card F = 2 ^ n)
    (hα : Function.Surjective α) (hK : IsPGroup 2 α.ker)
    (hβ : Function.Surjective β) (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) (hZE : Z ≤ E) {A : Subgroup X}
    (hA : IsSylowTwoOf A ⊤) : ⁅E, A⁆ ⊔ Z = relCent E Z A :=
  le_antisymm (comm_le_relCent hF hα hK hβk hβe hZE hA)
    (relCent_le_sup hF hα hK hβ hβk hβe hA)

private theorem lines_inf_beta (hF : Fintype.card F = 2 ^ n)
    (hα : Function.Surjective α) (hK : IsPGroup 2 α.ker)
    (hβ : Function.Surjective β) (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) (hZE : Z ≤ E) {A A' : Subgroup X}
    (hA : IsSylowTwoOf A ⊤) (hA' : IsSylowTwoOf A' ⊤) (hnot : ¬ A ≤ A' ⊔ E) :
    relCent E Z A ⊓ relCent E Z A' = Z ∧
      relCent E Z A ⊔ relCent E Z A' = E := by
  let R : Subgroup SL(2, F) := A.map α
  let R' : Subgroup SL(2, F) := A'.map α
  have hR2 : IsPGroup 2 R := hA.2.1.map α
  have hRcard : Nat.card R = Nat.card F := card_map_sylow_eq_card hF hα hK hA
  have hR'2 : IsPGroup 2 R' := hA'.2.1.map α
  have hR'card : Nat.card R' = Nat.card F := card_map_sylow_eq_card hF hα hK hA'
  have hnorm : (⊤ : Subgroup X) ≤ Subgroup.normalizer (α.ker : Set X) :=
    le_of_eq (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm
  have hker_le : α.ker ≤ A' := hA'.le_of_normalizes le_top hnorm hK
  have hne : R ≠ R' := by
    intro hEq
    apply hnot
    intro a ha
    have haR : α a ∈ R := Subgroup.mem_map_of_mem α ha
    rw [hEq] at haR
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp haR
    have hker : a'⁻¹ * a ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, haeq, inv_mul_cancel]
    have hmem : a'⁻¹ * a ∈ A' := hker_le hker
    have haA' : a ∈ A' := by
      have h := A'.mul_mem ha' hmem
      simpa [mul_assoc] using h
    exact Subgroup.mem_sup_left haA'
  have hlines := SL2Nat.fixedSub_inf_sup_of_ne hR2 hRcard hR'2 hR'card hne
  have hZle : ∀ B : Subgroup X, Z ≤ relCent E Z B := by
    intro B z hz
    rw [mem_relCent (Subgroup.le_normalizer_of_normal (H := Z) (K := E))]
    refine ⟨hZE hz, fun a _ => ?_⟩
    rw [commutatorElement_def]
    have h := Z.mul_mem hz ((inferInstance : Z.Normal).conj_mem z⁻¹ (Z.inv_mem hz) a)
    simpa [mul_assoc] using h
  refine ⟨?_, ?_⟩
  · refine le_antisymm ?_ (le_inf (hZle A) (hZle A'))
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxE : x ∈ E := hx.1.1
    let xE : ↥E := ⟨x, hxE⟩
    have hxW : Multiplicative.toAdd (β xE) ∈ SL2Nat.fixedSub R :=
      (mem_relCent_iff_fixed hβk hβe xE).mp hx.1
    have hxW' : Multiplicative.toAdd (β xE) ∈ SL2Nat.fixedSub R' :=
      (mem_relCent_iff_fixed hβk hβe xE).mp hx.2
    have hxbot : Multiplicative.toAdd (β xE) ∈ (⊥ : Submodule F (Fin 2 → F)) := by
      rw [← hlines.1]
      exact Submodule.mem_inf.mpr ⟨hxW, hxW'⟩
    have hzero : Multiplicative.toAdd (β xE) = 0 := (Submodule.mem_bot F).mp hxbot
    have hβ1 : β xE = 1 := Multiplicative.toAdd.injective (by simpa using hzero)
    have hker : xE ∈ β.ker := MonoidHom.mem_ker.mpr hβ1
    rw [hβk, Subgroup.mem_subgroupOf] at hker
    simpa using hker
  · refine le_antisymm ?_ ?_
    · exact sup_le (fun x hx => hx.1) (fun x hx => hx.1)
    · intro x hx
      let xE : ↥E := ⟨x, hx⟩
      have hxW : Multiplicative.toAdd (β xE) ∈
          SL2Nat.fixedSub R ⊔ SL2Nat.fixedSub R' := by
        rw [hlines.2]
        exact Submodule.mem_top
      obtain ⟨w1, hw1, w2, hw2, hw_eq⟩ := Submodule.mem_sup.mp hxW
      obtain ⟨y1, hy1β⟩ := hβ (Multiplicative.ofAdd w1)
      obtain ⟨y2, hy2β⟩ := hβ (Multiplicative.ofAdd w2)
      have hy1 : (y1 : X) ∈ relCent E Z A := by
        refine (mem_relCent_iff_fixed hβk hβe y1).mpr ?_
        rw [hy1β]
        simpa using hw1
      have hy2 : (y2 : X) ∈ relCent E Z A' := by
        refine (mem_relCent_iff_fixed hβk hβe y2).mpr ?_
        rw [hy2β]
        simpa using hw2
      have hβxy : β (y1 * y2) = β xE := by
        apply Multiplicative.toAdd.injective
        rw [map_mul, hy1β, hy2β, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
        rw [hw_eq]
      have hmem : (y1 * y2 : ↥E) * xE⁻¹ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hβxy, mul_inv_cancel]
      rw [hβk, Subgroup.mem_subgroupOf] at hmem
      have hdiff : ((y1 * y2 : ↥E) : X) * x⁻¹ ∈ Z := by simpa using hmem
      have hdiff' : x * (((y1 * y2 : ↥E) : X))⁻¹ ∈ Z := by
        simpa [mul_inv_rev] using Z.inv_mem hdiff
      have hprod : ((y1 * y2 : ↥E) : X) ∈
          relCent E Z A ⊔ relCent E Z A' :=
        (relCent E Z A ⊔ relCent E Z A').mul_mem
          (Subgroup.mem_sup_left hy1) (Subgroup.mem_sup_right hy2)
      have hx_eq : x = (x * (((y1 * y2 : ↥E) : X))⁻¹) * (((y1 * y2 : ↥E) : X)) := by
        group
      rw [hx_eq]
      exact (relCent E Z A ⊔ relCent E Z A').mul_mem
        (Subgroup.mem_sup_right (hZle A' hdiff')) hprod

private theorem mem_of_map_mem (hβk : β.ker = Z.subgroupOf E) {K : Subgroup X}
    (hZK : Z ≤ K) {e : ↥E} :
    (e : X) ∈ K ↔ β e ∈ (K.subgroupOf E).map β := by
  constructor
  · intro he
    exact Subgroup.mem_map_of_mem β (Subgroup.mem_subgroupOf.mpr he)
  · intro he
    obtain ⟨y, hy, hyβ⟩ := Subgroup.mem_map.mp he
    have hmem : e * y⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyβ, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at hmem
    have hdiff : (e : X) * (y : X)⁻¹ ∈ Z := by simpa using hmem
    have h_eq : (e : X) = ((e : X) * (y : X)⁻¹) * (y : X) := by group
    rw [h_eq]
    exact K.mul_mem (hZK hdiff) (Subgroup.mem_subgroupOf.mp hy)

private theorem fpf_beta (hK : IsPGroup 2 α.ker) (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) {g : X} (hodd : Odd (orderOf g)) (hgE : g ∉ E)
    {e : X} (he : e ∈ E) (hcomm : ⁅e, g⁆ ∈ Z) : e ∈ Z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let vE : ↥E := ⟨g * e * g⁻¹, (inferInstance : E.Normal).conj_mem e he g⟩
  have hvE : (vE : X) = g * e * g⁻¹ := rfl
  have hβv : β vE = β ⟨e, he⟩ := by
    have hmem : vE * ⟨e, he⟩⁻¹ ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      change g * e * g⁻¹ * e⁻¹ ∈ Z
      have hinv : g * e * g⁻¹ * e⁻¹ = ⁅e, g⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [hinv]
      exact Z.inv_mem hcomm
    have h1 : β (vE * ⟨e, he⟩⁻¹) = 1 := MonoidHom.mem_ker.mp hmem
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hfix : (α g : Matrix (Fin 2) (Fin 2) F).mulVec
      (Multiplicative.toAdd (β ⟨e, he⟩)) = Multiplicative.toAdd (β ⟨e, he⟩) := by
    have h := hβe g ⟨e, he⟩ vE hvE
    rw [hβv] at h
    exact h.symm
  have hαg : α g ≠ 1 := by
    intro h
    have hmem : g ∈ α.ker := MonoidHom.mem_ker.mpr h
    have hgone : g = 1 := by
      by_contra hg1
      have hne : (⟨g, hmem⟩ : ↥α.ker) ≠ 1 := by
        intro hsub
        exact hg1 (Subtype.ext_iff.mp hsub)
      have hdiv : 2 ∣ orderOf (⟨g, hmem⟩ : ↥α.ker) := hK.dvd_orderOf hne
      rw [Subgroup.orderOf_mk] at hdiv
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
    exact hgE (by rw [hgone]; exact E.one_mem)
  have hoddα : Odd (orderOf (α g)) := hodd.of_dvd_nat (orderOf_map_dvd α g)
  by_contra heZ
  have hv : Multiplicative.toAdd (β ⟨e, he⟩) ≠ 0 := by
    intro hzero
    apply heZ
    have hβ1 : β ⟨e, he⟩ = 1 := Multiplicative.toAdd.injective (by simpa using hzero)
    have hker : ⟨e, he⟩ ∈ β.ker := MonoidHom.mem_ker.mpr hβ1
    rw [hβk, Subgroup.mem_subgroupOf] at hker
    exact hker
  exact hαg (SL2Nat.eq_one_of_odd_order_of_fixed hv hoddα hfix)

private theorem irred_beta (hα : Function.Surjective α) (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) {W : Subgroup X} (hZW : Z ≤ W) (hWE : W ≤ E)
    (hWn : (⊤ : Subgroup X) ≤ Subgroup.normalizer (W : Set X)) :
    W = Z ∨ W = E := by
  let W' : Subgroup ↥E := W.subgroupOf E
  by_cases hbot : W'.map β = ⊥
  · left
    refine le_antisymm ?_ hZW
    intro w hw
    have hwE : w ∈ E := hWE hw
    have hwW : (⟨w, hwE⟩ : ↥E) ∈ W' := Subgroup.mem_subgroupOf.mpr hw
    have himg : β ⟨w, hwE⟩ ∈ W'.map β := Subgroup.mem_map_of_mem β hwW
    rw [hbot] at himg
    have hβ1 : β ⟨w, hwE⟩ = 1 := Subgroup.mem_bot.mp himg
    have hker : ⟨w, hwE⟩ ∈ β.ker := MonoidHom.mem_ker.mpr hβ1
    rw [hβk, Subgroup.mem_subgroupOf] at hker
    exact hker
  · right
    refine le_antisymm hWE ?_
    obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hv0 : Multiplicative.toAdd v.1 ≠ 0 := by
      intro hzero
      apply hvne
      apply Subtype.ext
      exact Multiplicative.toAdd.injective (by simpa using hzero)
    obtain ⟨a, ha', haβ⟩ := Subgroup.mem_map.mp v.2
    have haW : (a : X) ∈ W := Subgroup.mem_subgroupOf.mp ha'
    intro e he
    let eE : ↥E := ⟨e, he⟩
    have himg : β eE ∈ W'.map β := by
      by_cases h1 : β eE = 1
      · rw [h1]
        exact (W'.map β).one_mem
      · have he0 : Multiplicative.toAdd (β eE) ≠ 0 := by
          intro hzero
          exact h1 (Multiplicative.toAdd.injective (by simpa using hzero))
        obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.exists_sl2_mulVec_eq
          (Multiplicative.toAdd v.1) (Multiplicative.toAdd (β eE)) hv0 he0
        obtain ⟨x, hx⟩ := hα g
        let a' : ↥E := ⟨x * (a : X) * x⁻¹, (inferInstance : E.Normal).conj_mem a a.2 x⟩
        have ha'W : (a' : X) ∈ W := by
          have hxN : x ∈ Subgroup.normalizer (W : Set X) := hWn (Subgroup.mem_top x)
          exact (Subgroup.mem_normalizer_iff.mp hxN (a : X)).mp haW
        have hβa' : β a' = β eE := by
          apply Multiplicative.toAdd.injective
          rw [hβe x a a' rfl, haβ, hx, hg]
        have himg' : β a' ∈ W'.map β :=
          Subgroup.mem_map_of_mem β (Subgroup.mem_subgroupOf.mpr ha'W)
        rwa [hβa'] at himg'
    exact (mem_of_map_mem hβk hZW).mpr himg

private theorem natQuot_of_beta_top (hF : Fintype.card F = 2 ^ n)
    (hα : Function.Surjective α) (hK : IsPGroup 2 α.ker)
    (hβ : Function.Surjective β) (hβk : β.ker = Z.subgroupOf E)
    (hβe : IsBetaEquiv α β) (hZE : Z ≤ E) :
    NatQuot (⊤ : Subgroup X) E Z n where
  Z_le := hZE
  E_le := le_top
  normal := by
    refine le_inf ?_ ?_
    · exact le_of_eq (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm
    · exact le_of_eq (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm
  index := index_beta hF hβ hβk
  line := fun A hA => line_beta hF hα hK hβ hβk hβe hZE hA
  comm_eq := fun A hA => comm_eq_beta hF hα hK hβ hβk hβe hZE hA
  lines_inf := fun A A' hA hA' hnot =>
    lines_inf_beta hF hα hK hβ hβk hβe hZE hA hA' hnot
  fpf := fun g hg hodd hgE e he hcomm => fpf_beta hK hβk hβe hodd hgE he hcomm
  irred := fun A hZA hAE hAn => irred_beta hα hβk hβe hZA hAE hAn

end BetaTop

theorem natQuot_of_isNatSecOf {G : Type} [Group G] {L E Z : Subgroup G} [Finite ↥L]
    {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L)
    (hZE : Z ≤ E) (hEL : E ≤ L)
    (hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (h : CFSG.Quasithin.F112R.St84.IsNatSecOf L E Z α) :
    NatQuot L E Z n := by
  classical
  obtain ⟨β, hβ, hβk, hβe⟩ := h
  let X := ↥L
  let E' : Subgroup X := E.subgroupOf L
  let Z' : Subgroup X := Z.subgroupOf L
  have hNE : L ≤ Subgroup.normalizer (E : Set G) := fun x hx => (hL hx).1
  have hNZ : L ≤ Subgroup.normalizer (Z : Set G) := fun x hx => (hL hx).2
  haveI hEn : E'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNE
  haveI hZn : Z'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNZ
  have hZE' : Z' ≤ E' := Subgroup.subgroupOf_mono L hZE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : IsPGroup 2 α.ker := by
    rw [hker]
    have hpc : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 X := by
      change ((CFSG.pCore 2 X).map L.subtype).subgroupOf L = CFSG.pCore 2 X
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [hpc]
    exact CFSG.LieType.BorelTits.pCore_isPGroup (G := X) (r := 2)
  let eE : ↥E' ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEL
  let β' : ↥E' →* Multiplicative (Fin 2 → F) := β.comp eE.toMonoidHom
  have hβ' : Function.Surjective β' := hβ.comp eE.surjective
  have hβk' : β'.ker = Z'.subgroupOf E' := by
    ext x
    show β (eE x) = 1 ↔ ((x : X) : G) ∈ Z
    rw [← MonoidHom.mem_ker (f := β), hβk, Subgroup.mem_subgroupOf]
    rfl
  have hβe' : IsBetaEquiv α β' := by
    intro ℓ u v huv
    have hG : (eE v : G) = (ℓ : G) * (eE u : G) * (ℓ : G)⁻¹ := by
      change (v : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹
      simpa using congrArg (fun z : X => (z : G)) huv
    have h := hβe ℓ (eE u) (eE v) hG
    simpa [β'] using h
  have htop : NatQuot (⊤ : Subgroup X) E' Z' n :=
    natQuot_of_beta_top hF hα hK hβ' hβk' hβe' hZE'
  exact natQuot_subgroupOf hEL (hZE.trans hEL) htop

end CFSG.Quasithin.St84

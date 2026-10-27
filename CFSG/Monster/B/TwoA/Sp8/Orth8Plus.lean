module

public import CFSG.Monster.B.TwoA.Sp8.SubgeomVec
public import CFSG.Monster.B.TwoA.Sp8.Orth8FormsBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Image

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def vPlus : V8 := bvec 8 64

theorem qN_64 : qN 64 = true := by decide

theorem qPoly_vPlus : qPoly vPlus = 1 := by
  rw [vPlus, qPoly_bvec 64 (by norm_num), qN_64, ite_eq_left rfl]

@[expose] def t2D :
    Dfull := cQ * Psi vPlus

theorem t2D_mem_T9 :
    t2D ∈ T9 := T9.mul_mem cQ_mem_T9 (A8_le_T9 (Psi_mem_A8 _))

theorem t2D_not_mem_A8 :
    t2D ∉ A8 := fun h => cQ_not_mem_A8 (by
  have := A8.mul_mem h (A8.inv_mem (Psi_mem_A8 vPlus))
  rwa [t2D, mul_inv_cancel_right] at this)

theorem t2D_mem_Shat :
    t2D ∈ Shat := T9_le_Shat t2D_mem_T9

theorem t2D_mul_self :
    t2D * t2D = 1 := by
  calc t2D * t2D = cQ * cQ * (Psi vPlus * Psi vPlus) := by
        rw [t2D, mul_assoc, ← mul_assoc (Psi vPlus), ← cQ_comm_Psi, mul_assoc, mul_assoc]
    _ = 1 := by rw [cQ_mul_self, one_mul, ← Psi_add, ZModModule.add_self, Psi_zero']

theorem cPsi_mul_cPsi
    (v w : V8) : cQ * Psi v * (cQ * Psi w) = Psi (v + w) := by
  calc cQ * Psi v * (cQ * Psi w) = cQ * cQ * (Psi v * Psi w) := by
        rw [mul_assoc, ← mul_assoc (Psi v), ← cQ_comm_Psi, mul_assoc, mul_assoc]
    _ = Psi (v + w) := by rw [cQ_mul_self, one_mul, Psi_add]

@[expose] def qPlus : QuadraticForm (ZMod 2) V8 := qv vPlus

theorem qPlus_apply (w : V8) : qPlus w = qPoly (w + vPlus) + 1 := by
  rw [qPlus, qv_apply', qPoly_vPlus]

theorem polarBilin_qPlus : QuadraticMap.polarBilin qPlus = b0 := polarBilin_qv vPlus

@[expose] def P4p :
    Subgroup Dfull := Xgrp ⊓ Subgroup.centralizer {t2D}

theorem P4p_le_Xgrp :
    P4p ≤ Xgrp := inf_le_left

theorem qv_affine
    (x : Xgrp) {t : V8} (ht : (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ * Psi t)
    (v w : V8) : qv (t + rhoX x v) (rhoX x w) = qv v w := by
  rw [qv_apply', qv_apply', show rhoX x w + (t + rhoX x v) = t + rhoX x (w + v) by
    rw [map_add]; abel, qPoly_affine x ht, qPoly_affine x ht]

theorem conj_t2D
    (x : Xgrp) {t : V8} (ht : (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ * Psi t) :
    (x : Dfull) * t2D * (x : Dfull)⁻¹ = cQ * Psi (t + rhoX x vPlus) :=
  conj_cPsi_rhoX x ht vPlus

theorem mem_P4p_iff_eq
    (x : Xgrp) {t : V8} (ht : (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ * Psi t) :
    (x : Dfull) ∈ P4p ↔ t + rhoX x vPlus = vPlus := by
  constructor
  · intro hx
    have hc : (x : Dfull) * t2D * (x : Dfull)⁻¹ = t2D := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hx.2, mul_inv_cancel_right]
    rw [conj_t2D x ht] at hc
    exact Psi_inj (mul_left_cancel hc)
  · intro h
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hc := conj_t2D x ht
    rw [h] at hc
    calc (x : Dfull) * t2D = (x : Dfull) * t2D * (x : Dfull)⁻¹ * x := by group
      _ = t2D * x := by rw [hc]; rfl

theorem mem_P4p_iff
    (x : Xgrp) :
    (x : Dfull) ∈ P4p ↔ rhoX x ∈ TauCeti.QuadraticMap.orthogonalGroup qPlus := by
  obtain ⟨t, ht⟩ := exists_conj_cQ x
  rw [mem_P4p_iff_eq x ht, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro h w
    have e := qv_affine x ht vPlus w
    rw [h] at e
    exact e
  · intro h
    apply qv_injective
    apply QuadraticMap.ext
    intro w
    obtain ⟨u, rfl⟩ := (rhoX x).surjective w
    rw [qv_affine x ht vPlus u]
    exact (h u).symm

theorem orthogonalGroup_qPlus_le_isometryGroup :
    TauCeti.QuadraticMap.orthogonalGroup qPlus ≤ TauCeti.BilinForm.isometryGroup b0 := by
  intro M hM
  have hM' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hM
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  rw [← polarBilin_qPlus, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.polar, ← map_add,
    hM' (x + y), hM' x, hM' y]

theorem map_P4p :
    (P4p.subgroupOf Xgrp).map rhoX = TauCeti.QuadraticMap.orthogonalGroup qPlus := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_P4p_iff x).1 hx
  · intro M hM
    obtain ⟨x, hx⟩ := rhoXSp_surjective ⟨M, orthogonalGroup_qPlus_le_isometryGroup hM⟩
    have hxM : rhoX x = M := congrArg Subtype.val hx
    refine ⟨x, ?_, hxM⟩
    show (x : Dfull) ∈ P4p
    rw [mem_P4p_iff, hxM]
    exact hM

theorem Lgrp_le_P4p :
    Lgrp ≤ P4p := fun _ hl =>
  ⟨Lgrp_le_Xgrp hl, Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 (Lgrp_le_centralizer_T9 hl)) t2D t2D_mem_T9).symm⟩

@[expose] def p4pProj :
    P4p →* TauCeti.QuadraticMap.orthogonalGroup qPlus :=
  (rhoX.comp (Subgroup.inclusion P4p_le_Xgrp)).codRestrict _
    fun x => (mem_P4p_iff (Subgroup.inclusion P4p_le_Xgrp x)).1 x.2

theorem coe_p4pProj
    (x : P4p) :
    (p4pProj x : V8 ≃ₗ[ZMod 2] V8) = rhoX (Subgroup.inclusion P4p_le_Xgrp x) := rfl

theorem p4pProj_surjective :
    Function.Surjective p4pProj := by
  rintro ⟨M, hM⟩
  rw [← map_P4p] at hM
  obtain ⟨x, hx, rfl⟩ := hM
  exact ⟨⟨(x : Dfull), hx⟩, Subtype.ext rfl⟩

theorem ker_p4pProj :
    p4pProj.ker = Lgrp.subgroupOf P4p := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : rhoX ⟨x, P4p_le_Xgrp x.2⟩ = 1 := congrArg Subtype.val h
    exact (rhoX_eq_one_iff _).1 h1
  · intro h
    exact Subtype.ext ((rhoX_eq_one_iff ⟨x, P4p_le_Xgrp x.2⟩).2 h)

instance Lgrp_subgroupOf_P4p_normal :
    (Lgrp.subgroupOf P4p).Normal :=
  ker_p4pProj ▸ p4pProj.normal_ker

@[expose] def p4pQuotEquiv :
    P4p ⧸ Lgrp.subgroupOf P4p ≃* TauCeti.QuadraticMap.orthogonalGroup qPlus :=
  (QuotientGroup.quotientMulEquivOfEq ker_p4pProj.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective p4pProj p4pProj_surjective)

@[expose] def affWordM (ws : List ℕ) (v : V8) : V8 := ws.foldl (fun u k => affM k u) v

@[expose] def affWordN (ws : List ℕ) (n : ℕ) : ℕ := ws.foldl (fun m k => affN k m) n

theorem affWordN_spec :
    ∀ ws : List ℕ, (∀ k ∈ ws, k < 45) → ∀ n < 256,
    bvec 8 (affWordN ws n) = affWordM ws (bvec 8 n) ∧ affWordN ws n < 256
  | [], _, n, hn => ⟨rfl, hn⟩
  | k :: ws, hws, n, hn => by
    obtain ⟨h1, h2⟩ := affN_spec k (hws k (List.mem_cons_self ..)) n hn
    have ih := affWordN_spec ws (fun k' h => hws k' (List.mem_cons_of_mem _ h)) _ h2
    refine ⟨?_, ih.2⟩
    show bvec 8 (affWordN ws (affN k n)) = affWordM ws (affM k (bvec 8 n))
    rw [ih.1, h1]

theorem conj_affWord :
    ∀ ws : List ℕ, (∀ k ∈ ws, k < 45) →
    ∃ g ∈ Xgrp, ∀ w : V8, g * (cQ * Psi w) * g⁻¹ = cQ * Psi (affWordM ws w)
  | [], _ => ⟨1, Xgrp.one_mem, fun w => by rw [one_mul, inv_one, mul_one]; rfl⟩
  | k :: ws, hws => by
    obtain ⟨g, hg, hgw⟩ := conj_affM (hws k (List.mem_cons_self ..))
    obtain ⟨g', hg', hg'w⟩ := conj_affWord ws fun k' h => hws k' (List.mem_cons_of_mem _ h)
    refine ⟨g' * g, Xgrp.mul_mem hg' hg, fun w => ?_⟩
    rw [show g' * g * (cQ * Psi w) * (g' * g)⁻¹ = g' * (g * (cQ * Psi w) * g⁻¹) * g'⁻¹ by group,
      hgw, hg'w]
    rfl

@[expose] def plusWords : List (List ℕ) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [30, 38, 43], [33, 38, 43], [38, 43],
   [1, 38, 43], [], [], [], [], [1, 38, 39, 43], [38, 39, 43], [38, 43, 28], [38, 28, 43],
   [1, 38, 39, 43, 29], [38, 39, 43, 29], [38, 43, 28, 29], [38, 28, 43, 29],
   [1, 38, 39, 43, 29, 30], [38, 39, 43, 29, 30], [38, 28, 43, 29, 43], [38, 28, 43, 29, 30], [],
   [], [], [], [1, 38, 40, 43], [38, 40, 43], [33, 38, 40, 43], [30, 38, 40, 43],
   [30, 40, 29, 43, 29], [33, 40, 29, 43, 29], [38, 28, 40, 43, 29], [38, 28, 43, 29, 27],
   [1, 38, 40, 43, 29, 30], [38, 40, 43, 29, 30], [33, 38, 40, 43, 29, 30],
   [30, 38, 40, 43, 29, 30], [1, 38, 40, 43, 29, 28], [38, 40, 43, 29, 28],
   [30, 38, 40, 43, 29, 43], [30, 38, 40, 43, 29, 28], [1, 38, 40, 43, 29], [38, 40, 43, 29],
   [33, 38, 40, 43, 29], [30, 38, 40, 43, 29], [30, 40, 29, 43], [33, 40, 29, 43],
   [38, 28, 40, 43], [40, 30, 38, 43], [], [], [], [], [], [1], [], [], [30], [33], [], [],
   [1, 38], [38], [], [], [], [], [30, 38], [33, 38], [38, 28], [1, 38, 28], [], [], [], [],
   [1, 38, 39], [38, 39], [], [], [30, 39], [33, 39], [], [], [39], [1, 39], [30, 38, 40],
   [33, 38, 40], [], [], [], [], [1, 38, 40], [38, 40], [], [], [30, 40], [33, 40], [], [], [40],
   [1, 40], [], [], [40, 27], [39, 40], [], [], [40, 30], [1, 40, 30], [], [], [30, 40, 29],
   [33, 40, 29], [40, 30, 38], [38, 28, 40], [], [], [44], [], [], [1, 44], [30, 44], [], [],
   [33, 44], [44, 6], [], [], [38, 44], [], [30, 38, 44], [33, 38, 44], [], [38, 28, 44], [], [],
   [44, 6, 28], [], [39, 44, 6], [38, 39, 44], [], [], [30, 39, 44], [33, 39, 44], [], [],
   [39, 44], [1, 39, 44], [], [30, 38, 40, 44], [], [], [33, 38, 40, 44], [], [40, 44, 6],
   [38, 40, 44], [], [], [30, 40, 44], [33, 40, 44], [], [], [40, 44], [1, 40, 44], [], [],
   [39, 44, 8], [39, 40, 44], [], [], [40, 30, 44], [1, 40, 30, 44], [], [], [30, 40, 29, 44],
   [33, 40, 29, 44], [], [38, 28, 44, 8], [], [], [38, 28, 40, 44], [44, 13], [], [44, 11], [],
   [1, 44, 43], [], [30, 44, 11], [], [38, 44, 11], [], [38, 44, 13], [], [], [1, 44, 43, 6], [],
   [30, 38, 44, 11], [38, 28, 44, 13], [], [38, 28, 44, 11], [], [], [38, 39, 44, 11], [],
   [38, 39, 44, 13], [], [1, 39, 44, 43], [], [30, 39, 44, 11], [], [39, 44, 13], [],
   [39, 44, 11], [1, 40, 44, 43, 6], [], [30, 38, 40, 44, 11], [], [], [38, 40, 44, 11], [],
   [38, 40, 44, 13], [], [1, 40, 44, 43], [], [30, 40, 44, 11], [], [40, 44, 13], [],
   [40, 44, 11], [], [39, 40, 44, 11], [], [39, 40, 44, 13], [], [39, 40, 44, 43], [],
   [40, 30, 44, 11], [], [1, 40, 44, 43, 29], [], [30, 40, 29, 44, 11], [38, 28, 40, 44, 11], [],
   [38, 28, 40, 44, 13], []]

theorem plusWords_spec : ∀ n < 256, qN n = true →
    affWordN (plusWords.getD n []) 64 = n ∧ ∀ k ∈ plusWords.getD n [], k < 45 := by
  decide +kernel

theorem mem_orbit_t2D
    {v : V8} (hv : qPoly v = 1) : ∃ x ∈ Xgrp, x * t2D * x⁻¹ = cQ * Psi v := by
  obtain ⟨n, hn, rfl⟩ := exists_bvec8 v
  have hq : qN n = true := by
    rw [qPoly_bvec n hn] at hv
    cases h : qN n
    · rw [h, ite_eq_right (by decide)] at hv
      exact absurd hv (by decide)
    · rfl
  obtain ⟨hw, hk⟩ := plusWords_spec n hn hq
  obtain ⟨g, hg, hgw⟩ := conj_affWord _ hk
  refine ⟨g, hg, ?_⟩
  rw [t2D, hgw, vPlus, ← (affWordN_spec _ hk 64 (by norm_num)).1, hw]

theorem orbit_t2D :
    {y : Dfull | ∃ x ∈ Xgrp, x * t2D * x⁻¹ = y} =
    (fun v => cQ * Psi v) '' {v : V8 | qPoly v = 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := exists_conj_cQ ⟨x, hx⟩
    refine ⟨t + rhoX ⟨x, hx⟩ vPlus, ?_, (conj_t2D ⟨x, hx⟩ ht).symm⟩
    show qPoly (t + rhoX ⟨x, hx⟩ vPlus) = 1
    rw [qPoly_affine ⟨x, hx⟩ ht, qPoly_vPlus]
  · rintro ⟨v, hv, rfl⟩
    exact mem_orbit_t2D hv

theorem card_qPoly_one :
    (Finset.univ.filter fun v : Fin 8 → ZMod 2 => qPoly v = 1).card = 136 := by
  decide +kernel

theorem ncard_orbit_t2D :
    {y : Dfull | ∃ x ∈ Xgrp, x * t2D * x⁻¹ = y}.ncard = 136 := by
  rw [orbit_t2D, Set.ncard_image_of_injective _ cPsi_injective, ← card_qPoly_one,
    ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem index_P4p :
    (P4p.subgroupOf Xgrp).index = 136 := by
  let _ := xConj
  have hset : {y : Dfull | ∃ x ∈ Xgrp, x * t2D * x⁻¹ = y} = MulAction.orbit Xgrp t2D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  have hstab : MulAction.stabilizer Xgrp t2D = P4p.subgroupOf Xgrp := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, P4p, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    change (x : Dfull) * t2D * (x : Dfull)⁻¹ = t2D ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [← hstab, MulAction.index_stabilizer, ← hset, ncard_orbit_t2D]

theorem natCard_P4p :
    Nat.card P4p = 11689182992793600 := by
  have h := Subgroup.card_mul_index (P4p.subgroupOf Xgrp)
  rw [index_P4p, natCard_Xgrp, Nat.card_congr (Subgroup.subgroupOfEquivOfLe P4p_le_Xgrp).toEquiv]
    at h
  omega

theorem natCard_orthogonalGroup_qPlus :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup qPlus) = 348364800 := by
  rw [← Nat.card_congr p4pQuotEquiv.toEquiv]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Lgrp.subgroupOf P4p)
  rw [natCard_P4p, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lgrp_le_P4p).toEquiv,
    natCard_Lgrp] at h
  omega

theorem Psi_not_mem_Ehat
    {v : V8} (hv : v 7 = 1) : Psi v ∉ Ehat := by
  intro h
  apply ghat8_not_mem_Ehat
  have hP : Psi v = PhiD v * ghat8 := by
    rw [Psi, hv, show (1 : ZMod 2).val = 1 from rfl, pow_one]
  have e : ghat8 = (PhiD v)⁻¹ * Psi v := by rw [hP, inv_mul_cancel_left]
  rw [e]
  exact Ehat.mul_mem (Ehat.inv_mem (B7_le_Ehat (PhiD_mem_B7 v))) h

theorem affWordN_xhatWord : affWordN [33, 38, 43, 29, 43, 44] 0 = 143 ∧
    affWordN [33, 38, 43, 29, 43, 44] 64 = 142 := by
  decide +kernel

theorem exists_conj_vPlus_xhat :
    ∃ g ∈ Xgrp, g * Psi vPlus * g⁻¹ = xhat ∧ g * cQ * g⁻¹ ∉ Ehat := by
  have hk : ∀ k ∈ [33, 38, 43, 29, 43, 44], k < 45 := by decide
  obtain ⟨g, hg, hgw⟩ := conj_affWord _ hk
  obtain ⟨h0, h64⟩ := affWordN_xhatWord
  have e0 := (affWordN_spec _ hk 0 (by norm_num)).1
  have e64 := (affWordN_spec _ hk 64 (by norm_num)).1
  rw [h0] at e0
  rw [h64] at e64
  have hc : g * cQ * g⁻¹ = cQ * Psi (bvec 8 143) := by
    have h := hgw (bvec 8 0)
    rw [show bvec 8 0 = (0 : V8) by decide, Psi_zero', mul_one] at h
    rw [h, e0]
    rfl
  have ht : g * (cQ * Psi vPlus) * g⁻¹ = cQ * Psi (bvec 8 142) := by
    rw [hgw, vPlus, e64]
  refine ⟨g, hg, ?_, ?_⟩
  · have e : Psi vPlus = cQ * (cQ * Psi vPlus) := by rw [← mul_assoc, cQ_mul_self, one_mul]
    rw [e, show g * (cQ * (cQ * Psi vPlus)) * g⁻¹ =
        g * cQ * g⁻¹ * (g * (cQ * Psi vPlus) * g⁻¹) by group, hc, ht, cPsi_mul_cPsi,
      show bvec 8 143 + bvec 8 142 = bvec 8 1 by decide, Psi_bvec_one]
  · rw [hc]
    intro h
    have h7 : bvec 8 143 7 = 1 := by decide
    exact Psi_not_mem_Ehat h7 (by
      have := Ehat.mul_mem (Ehat.inv_mem cQ_mem_Ehat) h
      rwa [inv_mul_cancel_left] at this)

end CFSG.Monster.B.TwoA.Sp8

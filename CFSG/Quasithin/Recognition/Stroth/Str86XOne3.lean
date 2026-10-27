module

public import CFSG.Quasithin.Recognition.Stroth.Str86XOne2
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneUpper

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

attribute [instance] u3M_normal

theorem u3LS_eq_sup_q1 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hU3 : VU3Big L1) :
    u3LS L1 L2 S = L1 ⊔ Q1 L1 L2 S := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl hU3))
  calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
        conv_lhs => rw [hS1]
    _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
    _ = L1 ⊔ Q1 L1 L2 S := by
        rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]

noncomputable def u3QEquiv {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hU3 : VU3Big L1) :
    oTwoQuot (u3LS L1 L2 S) ≃* oTwoQuot ↥L1 := by
  rw [u3LS_eq_sup_q1 hF hSB hU3]
  exact oTwoQuotSupEquiv hF.1

theorem u3HQU3 {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (h1 : VU3Big L1) :
    Nonempty (oTwoQuot (u3LS L1 L2 S) ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot (u3LS L1 L2 S) ≃* StatedProj (StatedSU 3 (2 ^ k) F)) := by
  rcases hU3 with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨(u3QEquiv hF hSB h1).trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨(u3QEquiv hF hSB h1).trans e⟩

theorem u3S_not_normal_in_u3LS {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) :
    ¬ u3LS L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
  intro hN
  obtain ⟨g, hgL1, hgN⟩ := u3_exists_mem_L1_not_normalizer hF hSB
  exact hgN (hN ((le_sup_left : L1 ≤ u3LS L1 L2 S) hgL1))

theorem u3T0_not_normal {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1) :
    ¬ (u3T0 (k := k) (F := F) hF hSB hU3 :
      Subgroup (oTwoQuot (u3LS L1 L2 S))).Normal := by
  intro hT
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hpre : (u3T0 (k := k) (F := F) hF hSB hU3 :
      Subgroup (oTwoQuot (u3LS L1 L2 S))).comap
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(u3LS L1 L2 S))) =
      S.subgroupOf (u3LS L1 L2 S) := by
    rw [u3T0_coe (k := k) (F := F), imageOTwoQuot, QuotientGroup.comap_map_mk']
    rw [u3LS_pCore_subgroupOf (k := k) (F := F) hF hSB hU3]
    exact sup_eq_right.mpr (Subgroup.subgroupOf_mono _ hQ1S)
  have hSnorm : (S.subgroupOf (u3LS L1 L2 S)).Normal := by
    rw [← hpre]
    exact hT.comap _
  exact u3S_not_normal_in_u3LS hF hSB
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_right : S ≤ u3LS L1 L2 S)).mp hSnorm)

theorem u3_exists_sylow_ne_T0 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1) :
    ∃ T1 : Sylow 2 (oTwoQuot (u3LS L1 L2 S)),
      T1 ≠ u3T0 (k := k) (F := F) hF hSB hU3 := by
  let Q := oTwoQuot (u3LS L1 L2 S)
  let T0 : Sylow 2 Q := u3T0 (k := k) (F := F) hF hSB hU3
  have hnot : ¬ (T0 : Subgroup Q).Normal :=
    u3T0_not_normal (k := k) (F := F) hF hSB hU3
  rw [Subgroup.normal_iff_map_conj_eq] at hnot
  push Not at hnot
  obtain ⟨q, hq⟩ := hnot
  refine ⟨q • T0, ?_⟩
  intro h
  refine hq ?_
  have hcoe : ((q • T0 : Sylow 2 Q) : Subgroup Q) =
      Subgroup.map (MulAut.conj q).toMonoidHom (T0 : Subgroup Q) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  show Subgroup.map (MulAut.conj q).toMonoidHom (T0 : Subgroup Q) = (T0 : Subgroup Q)
  exact hcoe.symm.trans
    (congrArg (fun T : Sylow 2 Q => (T : Subgroup Q)) h)

theorem u3_exists_mul_mem_L1_S {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h : ↥(u3LS L1 L2 S)) :
    ∃ l ∈ L1, ∃ s ∈ S, (h : G) = l * s := by
  have hS : S ≤ Subgroup.normalizer (L1 : Set G) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (bigB_le_normalizer_of_hyp111 hF.1)
  exact (F1.mem_sup_iff_exists_mul_of_normalizes hS).mp h.2

theorem u3MQuotAct_mk_apply {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (h : ↥(u3LS L1 L2 S)) (u : ↥(u3X1 L1 L2 S)) :
    u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1 (QuotientGroup.mk h)
        (QuotientGroup.mk u) =
      QuotientGroup.mk (⟨(h : G) * u * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_u3X1_sup hF h.2) (u : G)).mp u.2⟩ :
        ↥(u3X1 L1 L2 S)) := by
  rw [u3MQuotAct, QuotientGroup.lift_mk, u3MActLS]
  exact CFSG.Quasithin.Vol2.Ch11.SecD.quotAct_mk _ _ h u

theorem u3MQuotAct_mul_mk_apply {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (h1 h2 : ↥(u3LS L1 L2 S)) (u : ↥(u3X1 L1 L2 S)) :
    u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
        (QuotientGroup.mk h1 * QuotientGroup.mk h2) (QuotientGroup.mk u) =
      QuotientGroup.mk (⟨(h1 : G) * ((h2 : G) * u * (h2 : G)⁻¹) * (h1 : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_u3X1_sup hF h1.2)
          ((h2 : G) * u * (h2 : G)⁻¹)).mp
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_u3X1_sup hF h2.2) (u : G)).mp u.2)⟩ :
        ↥(u3X1 L1 L2 S)) := by
  rw [map_mul, MulAut.mul_apply]
  rw [u3MQuotAct_mk_apply (L1 := L1) (L2 := L2) (S := S) hF hSB hU3 hX1Q1 h2 u]
  rw [u3MQuotAct_mk_apply (L1 := L1) (L2 := L2) (S := S) hF hSB hU3 hX1Q1 h1]

theorem u3MQuotAct_conj_mk_apply_exists {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (h1 h2 : ↥(u3LS L1 L2 S)) (u : ↥(u3X1 L1 L2 S)) :
    ∃ u' : ↥(u3X1 L1 L2 S),
      (u' : G) = (h1 : G) * (h2 : G) * (h1 : G)⁻¹ * u *
        ((h1 : G) * (h2 : G) * (h1 : G)⁻¹)⁻¹ ∧
      u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
        (QuotientGroup.mk h1 * QuotientGroup.mk h2 * (QuotientGroup.mk h1)⁻¹)
        (QuotientGroup.mk u) = QuotientGroup.mk u' := by
  have hN1 : (h1 : G) ∈ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    le_normalizer_u3X1_sup hF h1.2
  have hN2 : (h2 : G) ∈ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    le_normalizer_u3X1_sup hF h2.2
  have hN1i : (h1 : G)⁻¹ ∈ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    (Subgroup.normalizer _).inv_mem hN1
  let u1 : ↥(u3X1 L1 L2 S) :=
    ⟨(h1 : G)⁻¹ * u * ((h1 : G)⁻¹)⁻¹, by
      exact (Subgroup.mem_normalizer_iff.mp hN1i (u : G)).mp u.2⟩
  let u2 : ↥(u3X1 L1 L2 S) :=
    ⟨(h2 : G) * u1 * (h2 : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hN2 (u1 : G)).mp u1.2⟩
  let u3 : ↥(u3X1 L1 L2 S) :=
    ⟨(h1 : G) * u2 * (h1 : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hN1 (u2 : G)).mp u2.2⟩
  refine ⟨u3, ?_, ?_⟩
  · change (h1 : G) * u2 * (h1 : G)⁻¹ =
      (h1 : G) * (h2 : G) * (h1 : G)⁻¹ * u *
        ((h1 : G) * (h2 : G) * (h1 : G)⁻¹)⁻¹
    change (h1 : G) * ((h2 : G) * ((h1 : G)⁻¹ * u * ((h1 : G)⁻¹)⁻¹) * (h2 : G)⁻¹) *
        (h1 : G)⁻¹ =
      (h1 : G) * (h2 : G) * (h1 : G)⁻¹ * u *
        ((h1 : G) * (h2 : G) * (h1 : G)⁻¹)⁻¹
    group
  · rw [map_mul, map_inv, MulAut.mul_apply]
    have hcomp : u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
        (QuotientGroup.mk h1) * u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
        ((QuotientGroup.mk h1)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hinv : (u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
        (QuotientGroup.mk h1))⁻¹ =
        u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1 ((QuotientGroup.mk h1)⁻¹) :=
      inv_eq_of_mul_eq_one_right hcomp
    rw [hinv]
    rw [show (QuotientGroup.mk h1 : oTwoQuot (u3LS L1 L2 S))⁻¹ =
      QuotientGroup.mk h1⁻¹ by simp]
    rw [u3MQuotAct_mk_apply (L1 := L1) (L2 := L2) (S := S) hF hSB hU3 hX1Q1 h1⁻¹ u]
    change u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
      (QuotientGroup.mk h1 * QuotientGroup.mk h2) (QuotientGroup.mk u1) =
        QuotientGroup.mk u3
    rw [u3MQuotAct_mul_mk_apply (L1 := L1) (L2 := L2) (S := S) hF hSB hU3 hX1Q1 h1 h2 u1]

theorem u3MQuotAct_conj_commutator_mem {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    {l z : G} (hl : l ∈ L1) (hz : z ∈ Z2 L1 L2 S) (u : ↥(u3X1 L1 L2 S)) :
    ∃ y : ↥(u3X1 L1 L2 S), (y : G) ∈ conjSub l (u3Y L1 L2 S) ∧
      ((QuotientGroup.mk u : u3M L1 L2 S))⁻¹ *
        u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
          (QuotientGroup.mk ⟨l, (le_sup_left : L1 ≤ u3LS L1 L2 S) hl⟩ *
            QuotientGroup.mk ⟨z, (le_sup_right : S ≤ u3LS L1 L2 S)
              ((omegaOneCenterOf_le (Q2 L1 L2 S)).trans
                (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
                  (f112_isSylowTwoOf_P2 hF.toW)) hz)⟩ *
            (QuotientGroup.mk ⟨l, (le_sup_left : L1 ≤ u3LS L1 L2 S) hl⟩)⁻¹)
          (QuotientGroup.mk u) = QuotientGroup.mk y := by
  let lH : ↥(u3LS L1 L2 S) := ⟨l, (le_sup_left : L1 ≤ u3LS L1 L2 S) hl⟩
  let zH : ↥(u3LS L1 L2 S) :=
    ⟨z, (le_sup_right : S ≤ u3LS L1 L2 S)
      ((omegaOneCenterOf_le (Q2 L1 L2 S)).trans
        (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)) hz)⟩
  obtain ⟨u3, hu3val, hu3act⟩ :=
    u3MQuotAct_conj_mk_apply_exists (L1 := L1) (L2 := L2) (S := S) (k := k) (F := F)
      hF hSB hU3 hX1Q1 lH zH u
  have hg : l * z * l⁻¹ ∈ conjSub l (Z2 L1 L2 S) := by
    rw [mem_conjSub]
    have hz' : l⁻¹ * (l * z * l⁻¹) * l = z := by group
    rwa [hz']
  have hcomm : u⁻¹ * (l * z * l⁻¹) * u * (l * z * l⁻¹)⁻¹ ∈
      conjSub l (u3Y L1 L2 S) := by
    have hmem := Subgroup.commutator_mem_commutator
      (Subgroup.inv_mem (u3X1 L1 L2 S) u.2) hg
    have hmem' : u⁻¹ * (l * z * l⁻¹) * u * (l * z * l⁻¹)⁻¹ ∈
        ⁅u3X1 L1 L2 S, conjSub l (Z2 L1 L2 S)⁆ := by
      simpa only [commutatorElement_def, inv_inv, Subgroup.coe_inv] using hmem
    exact u3_commutator_u3X1_conj_z2_le_u3Y hF hl hmem'
  have hYX : conjSub l (u3Y L1 L2 S) ≤ u3X1 L1 L2 S := by
    have hYle : u3Y L1 L2 S ≤ u3X1 L1 L2 S := by
      rw [u3X1]
      exact le_conjClosure _ _
    calc conjSub l (u3Y L1 L2 S) ≤ conjSub l (u3X1 L1 L2 S) := conjSub_mono l hYle
      _ = u3X1 L1 L2 S :=
          F1.conjSub_eq_of_mem_normalizer
            (le_normalizer_u3X1_sup hF ((le_sup_left : L1 ≤ u3LS L1 L2 S) hl))
  have hmemY : ((u⁻¹ * u3 : ↥(u3X1 L1 L2 S)) : G) ∈ conjSub l (u3Y L1 L2 S) := by
    change ((u⁻¹ : ↥(u3X1 L1 L2 S)) : G) * (u3 : G) ∈ conjSub l (u3Y L1 L2 S)
    rw [hu3val]
    dsimp [lH, zH]
    simpa only [Subgroup.coe_inv, inv_inv, mul_assoc] using hcomm
  refine ⟨⟨u⁻¹ * u3, hYX hmemY⟩, hmemY, ?_⟩
  rw [show (QuotientGroup.mk u : u3M L1 L2 S)⁻¹ =
    QuotientGroup.mk (u⁻¹ : ↥(u3X1 L1 L2 S)) by simp]
  rw [hu3act]
  change QuotientGroup.mk (u⁻¹ : ↥(u3X1 L1 L2 S)) * QuotientGroup.mk u3 =
    QuotientGroup.mk ((u⁻¹ * u3 : ↥(u3X1 L1 L2 S)) : ↥(u3X1 L1 L2 S))
  rfl

end CFSG.Quasithin.Stroth

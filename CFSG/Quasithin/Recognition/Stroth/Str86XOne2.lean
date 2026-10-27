module

public import CFSG.Quasithin.Recognition.Stroth.Str86XOne
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev u3LS (L1 L2 S : Subgroup G) : Subgroup G := L1 ⊔ S

theorem u3LS_pCoreOf {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1) :
    pCoreOf 2 (u3LS L1 L2 S) = Q1 L1 L2 S := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl hU3))
  have hLhatQ : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  rw [u3LS, hLhatQ]
  exact pCoreOf_sup_pCoreOf hF.1

@[expose] noncomputable def u3MActLS {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    [((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal] :
    ↥(u3LS L1 L2 S) →* MulAut (u3M L1 L2 S) := by
  have hX : u3LS L1 L2 S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    le_normalizer_u3X1_sup hF
  have hZ : u3LS L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    refine (sup_le (le_sup_left : L1 ≤ P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans ?_
    exact (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  exact CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hX hZ

theorem u3LS_pCore_subgroupOf {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1) :
    CFSG.Open.pCore 2 ↥(u3LS L1 L2 S) = (Q1 L1 L2 S).subgroupOf (u3LS L1 L2 S) := by
  ext x : 1
  rw [Subgroup.mem_subgroupOf (H := Q1 L1 L2 S) (K := u3LS L1 L2 S),
    CFSG.Quasithin.F1.mem_pCore_iff_coe (H := u3LS L1 L2 S) x,
    u3LS_pCoreOf (k := k) (F := F) hF hSB hU3]

theorem u3M_pCore_le_ker {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    [((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal]
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S) :
    CFSG.Open.pCore 2 ↥(u3LS L1 L2 S) ≤
      (u3MActLS (L1 := L1) (L2 := L2) (S := S) hF).ker := by
  intro q hq
  rw [MonoidHom.mem_ker]
  have hqG : ((q : ↥(u3LS L1 L2 S)) : G) ∈ Q1 L1 L2 S := by
    have hq' : q ∈ (Q1 L1 L2 S).subgroupOf (u3LS L1 L2 S) := by
      rw [← u3LS_pCore_subgroupOf (k := k) (F := F) hF hSB hU3]
      exact hq
    exact Subgroup.mem_subgroupOf.mp hq'
  have hUZ : u3X1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans
      (Subgroup.le_normalizer.trans
        (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  rw [u3MActLS, CFSG.Quasithin.Vol2.Ch11.SecD.quotAct_eq_one_iff (hUZ := hUZ)]
  intro x hx
  have hmem : (↑q * x * (↑q)⁻¹ * x⁻¹) ∈ ⁅Q1 L1 L2 S, u3X1 L1 L2 S⁆ :=
    Subgroup.commutator_mem_commutator hqG hx
  rw [Subgroup.commutator_comm] at hmem
  exact hX1Q1 hmem

@[expose] noncomputable def u3MQuotAct {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    [((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal]
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S) :
    oTwoQuot (u3LS L1 L2 S) →* MulAut (u3M L1 L2 S) :=
  QuotientGroup.lift (CFSG.Open.pCore 2 ↥(u3LS L1 L2 S))
    (u3MActLS (L1 := L1) (L2 := L2) (S := S) hF)
    (u3M_pCore_le_ker (k := k) (F := F) hF hSB hU3 hX1Q1)

theorem u3LS_isSylowTwoOf {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1) :
    IsSylowTwoOf S (u3LS L1 L2 S) := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl hU3))
  have hLhatQ : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  rw [u3LS, hLhatQ]
  exact isSylowTwoOf_sup_pCoreOf hF.1 hS1

noncomputable def u3T0 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1) :
    Sylow 2 (oTwoQuot (u3LS L1 L2 S)) :=
  (isPGroup_imageOTwoQuot_of_isSylow (u3LS_isSylowTwoOf (k := k) (F := F) hF hSB hU3)).toSylow
    (not_two_dvd_index_imageOTwoQuot (u3LS_isSylowTwoOf (k := k) (F := F) hF hSB hU3))

theorem u3T0_coe {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F] (hU3 : VU3Big L1) :
    (u3T0 (k := k) (F := F) hF hSB hU3 : Subgroup (oTwoQuot (u3LS L1 L2 S))) =
      imageOTwoQuot (u3LS L1 L2 S) S :=
  IsPGroup.toSylow_coe _ _

theorem u3A0_eq_omegaOne {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    imageOTwoQuot (u3LS L1 L2 S) (Z2 L1 L2 S) =
      omegaOneOf (imageOTwoQuot (u3LS L1 L2 S) S) := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  obtain ⟨X0, hX0mem, hQ1X0, -, hX0eq, -⟩ :=
    str86_z2_sup_q1_eq_X0 (L1 := L1) (L2 := L2) (S := S) hF hSB hk hFc hU3 hZQ
  let H : Subgroup G := u3LS L1 L2 S
  have hcoreOf : pCoreOf 2 H = Q1 L1 L2 S := u3LS_pCoreOf (k := k) (F := F) hF hSB h1
  have hQ1core : CFSG.Open.pCore 2 ↥H = (Q1 L1 L2 S).subgroupOf H := by
    ext x : 1
    rw [Subgroup.mem_subgroupOf (H := Q1 L1 L2 S) (K := H),
      CFSG.Quasithin.F1.mem_pCore_iff_coe (H := H) x, hcoreOf]
  have hQ1img : imageOTwoQuot H (Q1 L1 L2 S) = ⊥ := by
    rw [imageOTwoQuot, ← hQ1core, QuotientGroup.map_mk'_self]
  have hZ2H : Z2 L1 L2 S ≤ H :=
    ((omegaOneCenterOf_le (Q2 L1 L2 S)).trans
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW))).trans
      (le_sup_right : S ≤ H)
  have hQ1H : Q1 L1 L2 S ≤ H :=
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)).trans
      (le_sup_right : S ≤ H)
  have hX0img : imageOTwoQuot H X0 = imageOTwoQuot H (Z2 L1 L2 S) := by
    rw [imageOTwoQuot, imageOTwoQuot, ← hX0eq,
      Subgroup.subgroupOf_sup hZ2H hQ1H, Subgroup.map_sup]
    change imageOTwoQuot H (Z2 L1 L2 S) ⊔ imageOTwoQuot H (Q1 L1 L2 S) =
      imageOTwoQuot H (Z2 L1 L2 S)
    rw [hQ1img, sup_bot_eq]
  rw [← hX0img]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxS : ((x : G)) ∈ S := (hX0mem (x : G)).mp (Subgroup.mem_subgroupOf.mp hx) |>.1
    have hx2 : ((x : G)) ^ 2 ∈ Q1 L1 L2 S :=
      (hX0mem (x : G)).mp (Subgroup.mem_subgroupOf.mp hx) |>.2
    refine Subgroup.subset_closure
      ⟨Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hxS, rfl⟩, ?_⟩
    have hsq : ((x : ↥H) ^ 2) ∈ CFSG.Open.pCore 2 ↥H := by
      rw [hQ1core]
      exact Subgroup.mem_subgroupOf.mpr hx2
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (x ^ 2)).mpr hsq
  · rw [omegaOneOf, Subgroup.closure_le]
    rintro y ⟨⟨s, hs, rfl⟩, hy2⟩
    have hsG : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hsqcore : (s ^ 2 : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by
      have h : ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) (s ^ 2)) = 1 := by
        simpa [map_pow] using hy2
      exact (QuotientGroup.eq_one_iff (s ^ 2)).mp h
    have hsqG : ((s : G) ^ 2) ∈ Q1 L1 L2 S := by
      have hsub : (s ^ 2 : ↥H) ∈ (Q1 L1 L2 S).subgroupOf H := by
        rw [← hQ1core]
        exact hsqcore
      simpa using Subgroup.mem_subgroupOf.mp hsub
    have hsX0 : (s : G) ∈ X0 := (hX0mem (s : G)).mpr ⟨hsG, hsqG⟩
    refine Subgroup.mem_map.mpr ⟨⟨(s : G), ?_⟩, ?_, ?_⟩
    · exact s.2
    · exact Subgroup.mem_subgroupOf.mpr hsX0
    · rfl

theorem u3A0_eq_omegaOne_T0 {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (h1 : VU3Big L1) :
    imageOTwoQuot (u3LS L1 L2 S) (Z2 L1 L2 S) =
      omegaOneOf (u3T0 (k := k) (F := F) hF hSB h1 : Subgroup _) := by
  rw [u3T0_coe (k := k) (F := F)]
  exact u3A0_eq_omegaOne hF hSB hk hFc hU3 hZQ

end CFSG.Quasithin.Stroth

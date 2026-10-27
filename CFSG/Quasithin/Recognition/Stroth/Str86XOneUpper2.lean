module

public import CFSG.Quasithin.Recognition.Stroth.Str86XOne3
public import CFSG.ClassicalGroups.UnitaryFlag.ThreeOmegaOne

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private noncomputable def u3YM (L1 L2 S : Subgroup G) (l : G) : Subgroup (u3M L1 L2 S) :=
  ((QuotientGroup.mk' ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S))).comp
    ((conjSub l (u3Y L1 L2 S)).subgroupOf (u3X1 L1 L2 S)).subtype).range

private theorem mem_u3YM {L1 L2 S : Subgroup G} {l : G}
    (hYX : conjSub l (u3Y L1 L2 S) ≤ u3X1 L1 L2 S) {x : u3M L1 L2 S} :
    x ∈ u3YM L1 L2 S l ↔
      ∃ y : ↥(u3X1 L1 L2 S), (y : G) ∈ conjSub l (u3Y L1 L2 S) ∧
        QuotientGroup.mk y = x := by
  rw [u3YM, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨⟨y, hYX hy⟩, hy⟩, rfl⟩

private theorem card_conjSub_eq (l : G) (A : Subgroup G) :
    Nat.card (conjSub l A) = Nat.card A := by
  rw [conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj l).injective

private theorem u3_omegaOneOf_smul {X : Type} [Group X] [Finite X]
    (q : X) (T : Sylow 2 X) :
    omegaOneOf ((q • T : Sylow 2 X) : Subgroup X) =
      (omegaOneOf (T : Subgroup X)).map (MulAut.conj q).toMonoidHom := by
  have hcoe : ((q • T : Sylow 2 X) : Subgroup X) =
      (T : Subgroup X).map (MulAut.conj q).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hcoe, ← CFSG.Quasithin.omegaOneOf_map_mulEquiv (MulAut.conj q)]

private theorem u3_conjSub_le_u3X1 {L1 L2 S : Subgroup G} {l : G} (hl : l ∈ L1) :
    conjSub l (u3Y L1 L2 S) ≤ u3X1 L1 L2 S := by
  have hlN : l ∈ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    le_normalizer_u3X1_left (L1 := L1) (L2 := L2) (S := S) hl
  have hX : conjSub l (u3X1 L1 L2 S) = u3X1 L1 L2 S := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hlN
  calc conjSub l (u3Y L1 L2 S) ≤ conjSub l (u3X1 L1 L2 S) :=
        conjSub_mono l u3Y_le_u3X1
    _ = u3X1 L1 L2 S := hX

private theorem u3YM_card_le {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hY : Nat.card (u3Y L1 L2 S) = (2 ^ k) ^ 3)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k) {l : G} (hl : l ∈ L1) :
    Nat.card (u3YM L1 L2 S l) ≤ (2 ^ k) ^ 2 := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hZY : Z1 L1 L2 S ≤ u3Y L1 L2 S := u3Z1_le_u3Y hF hSB h1 hB2 h2 hZI
  have hZ1X : Z1 L1 L2 S ≤ u3X1 L1 L2 S := hZY.trans u3Y_le_u3X1
  have hYX : conjSub l (u3Y L1 L2 S) ≤ u3X1 L1 L2 S :=
    u3_conjSub_le_u3X1 (L1 := L1) (L2 := L2) (S := S) hl
  have hZl : conjSub l (Z1 L1 L2 S) = Z1 L1 L2 S := by
    have hlC : l ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      hZI ((le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S) hl)
    have hlN : l ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
      Subgroup.centralizer_le_normalizer _ hlC
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hlN
  have hZYl : Z1 L1 L2 S ≤ conjSub l (u3Y L1 L2 S) := by
    calc Z1 L1 L2 S = conjSub l (Z1 L1 L2 S) := hZl.symm
      _ ≤ conjSub l (u3Y L1 L2 S) := conjSub_mono l hZY
  let Yl : Subgroup G := conjSub l (u3Y L1 L2 S)
  let φ : ↥(Yl.subgroupOf (u3X1 L1 L2 S)) →* u3M L1 L2 S :=
    (QuotientGroup.mk' ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S))).comp
      (Yl.subgroupOf (u3X1 L1 L2 S)).subtype
  let K : Subgroup ↥(Yl.subgroupOf (u3X1 L1 L2 S)) :=
    ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).subgroupOf
      (Yl.subgroupOf (u3X1 L1 L2 S))
  have hKY : (Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S) ≤
      Yl.subgroupOf (u3X1 L1 L2 S) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hZYl hx
  have hKcard : Nat.card K = 2 ^ k := by
    calc Nat.card K = Nat.card ↥((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv
      _ = Nat.card (Z1 L1 L2 S) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ1X).toEquiv
      _ = 2 ^ k := hZ1
  have hKle : K ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxZ : ((x.1 : ↥(u3X1 L1 L2 S)) : G) ∈ Z1 L1 L2 S :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
    show (QuotientGroup.mk' ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S))) x.1 = 1
    exact (QuotientGroup.eq_one_iff x.1).mpr (Subgroup.mem_subgroupOf.mpr hxZ)
  have hdom : Nat.card ↥(Yl.subgroupOf (u3X1 L1 L2 S)) = (2 ^ k) ^ 3 := by
    calc Nat.card ↥(Yl.subgroupOf (u3X1 L1 L2 S)) = Nat.card Yl :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
      _ = Nat.card (u3Y L1 L2 S) := card_conjSub_eq l (u3Y L1 L2 S)
      _ = (2 ^ k) ^ 3 := hY
  have hYM : u3YM L1 L2 S l = φ.range := rfl
  have hker_ge : 2 ^ k ≤ Nat.card φ.ker := by
    calc 2 ^ k = Nat.card K := hKcard.symm
      _ ≤ Nat.card φ.ker := Subgroup.card_le_of_le hKle
  have hcardφ := Subgroup.card_ker_mul_card_range φ
  have hmul : 2 ^ k * Nat.card (u3YM L1 L2 S l) ≤ (2 ^ k) ^ 3 := by
    calc 2 ^ k * Nat.card (u3YM L1 L2 S l) = 2 ^ k * Nat.card φ.range := by rw [hYM]
      _ ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul_right _ hker_ge
      _ = Nat.card ↥(Yl.subgroupOf (u3X1 L1 L2 S)) := hcardφ
      _ = (2 ^ k) ^ 3 := hdom
  have hqpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  refine Nat.le_of_mul_le_mul_left ?_ hqpos
  calc 2 ^ k * Nat.card (u3YM L1 L2 S l) ≤ (2 ^ k) ^ 3 := hmul
    _ = 2 ^ k * (2 ^ k) ^ 2 := by ring

private theorem u3_act_u3YM_le {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hU3 : VU3Big L1)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    {q : oTwoQuot (u3LS L1 L2 S)} {h : ↥(u3LS L1 L2 S)} {l s : G}
    (hq : QuotientGroup.mk h = q) (hl : l ∈ L1) (hs : s ∈ S) (hh : (h : G) = l * s)
    {Aq : Subgroup (oTwoQuot (u3LS L1 L2 S))}
    (hAq : Aq = (imageOTwoQuot (u3LS L1 L2 S) (Z2 L1 L2 S)).map
      (MulAut.conj q).toMonoidHom)
    {a : oTwoQuot (u3LS L1 L2 S)} (ha : a ∈ Aq)
    {lj : G} (hlj : lj ∈ L1) :
    (u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1 a) • u3YM L1 L2 S lj ≤
      u3YM L1 L2 S l ⊔ u3YM L1 L2 S lj := by
  classical
  intro x hx
  rw [Subgroup.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨u0, hu0, rfl⟩ := hx
  have hYXj : conjSub lj (u3Y L1 L2 S) ≤ u3X1 L1 L2 S :=
    u3_conjSub_le_u3X1 (L1 := L1) (L2 := L2) (S := S) hlj
  rw [mem_u3YM hYXj] at hu0
  obtain ⟨u, huYj, rfl⟩ := hu0
  have hAq' : a ∈ (imageOTwoQuot (u3LS L1 L2 S) (Z2 L1 L2 S)).map
      (MulAut.conj q).toMonoidHom := hAq ▸ ha
  obtain ⟨z, hzA0, hza⟩ := Subgroup.mem_map.mp hAq'
  rw [imageOTwoQuot] at hzA0
  obtain ⟨z', hz'Z2, hz'eq⟩ := Subgroup.mem_map.mp hzA0
  let lH : ↥(u3LS L1 L2 S) :=
    ⟨l, (le_sup_left : L1 ≤ u3LS L1 L2 S) hl⟩
  let z'' : G := s * (z' : G) * s⁻¹
  have hz''Z2 : z'' ∈ Z2 L1 L2 S := by
    have hz'Z2' : (z' : G) ∈ Z2 L1 L2 S := Subgroup.mem_subgroupOf.mp hz'Z2
    simpa [z''] using (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S) hs)
      (z' : G)).mp hz'Z2'
  let z''H : ↥(u3LS L1 L2 S) :=
    ⟨z'', (le_sup_right : S ≤ u3LS L1 L2 S)
      ((omegaOneCenterOf_le (Q2 L1 L2 S)).trans
        (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
          (f112_isSylowTwoOf_P2 hF.toW)) hz''Z2)⟩
  have hH_eq : h * z' * h⁻¹ = lH * z''H * lH⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, lH, z''H, z'', hh]
    group
  have ha_eq : a = QuotientGroup.mk lH * QuotientGroup.mk z''H *
      (QuotientGroup.mk lH)⁻¹ := by
    rw [← hza, ← hz'eq, ← hq]
    change (MulAut.conj (QuotientGroup.mk h)) (QuotientGroup.mk z') =
      QuotientGroup.mk lH * QuotientGroup.mk z''H * (QuotientGroup.mk lH)⁻¹
    rw [MulAut.conj_apply]
    calc QuotientGroup.mk h * QuotientGroup.mk z' * (QuotientGroup.mk h)⁻¹
        = QuotientGroup.mk (h * z' * h⁻¹) := by
            simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = QuotientGroup.mk (lH * z''H * lH⁻¹) := by rw [hH_eq]
      _ = QuotientGroup.mk lH * QuotientGroup.mk z''H *
            (QuotientGroup.mk lH)⁻¹ := by
            simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  obtain ⟨y, hyY, hyact⟩ :=
    u3MQuotAct_conj_commutator_mem (L1 := L1) (L2 := L2) (S := S)
      (k := k) (F := F) hF hSB hU3 hX1Q1 hl hz''Z2 u
  have hu_inv_act : (QuotientGroup.mk u)⁻¹ *
      (u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
        (QuotientGroup.mk lH * QuotientGroup.mk z''H *
          (QuotientGroup.mk lH)⁻¹)) (QuotientGroup.mk u) =
      QuotientGroup.mk y := by
    simpa [lH, z''H] using hyact
  have hact : (u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1 a)
      (QuotientGroup.mk u) = QuotientGroup.mk u * QuotientGroup.mk y := by
    rw [ha_eq]
    calc (u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
          (QuotientGroup.mk lH * QuotientGroup.mk z''H *
            (QuotientGroup.mk lH)⁻¹)) (QuotientGroup.mk u)
        = QuotientGroup.mk u *
          ((QuotientGroup.mk u)⁻¹ *
            (u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1
              (QuotientGroup.mk lH * QuotientGroup.mk z''H *
                (QuotientGroup.mk lH)⁻¹)) (QuotientGroup.mk u)) := by group
      _ = QuotientGroup.mk u * QuotientGroup.mk y := by rw [hu_inv_act]
  have hYXl : conjSub l (u3Y L1 L2 S) ≤ u3X1 L1 L2 S :=
    u3_conjSub_le_u3X1 (L1 := L1) (L2 := L2) (S := S) hl
  have hmemu : QuotientGroup.mk u ∈ u3YM L1 L2 S lj :=
    (mem_u3YM hYXj).mpr ⟨u, huYj, rfl⟩
  have hmemy : QuotientGroup.mk y ∈ u3YM L1 L2 S l :=
    (mem_u3YM hYXl).mpr ⟨y, hyY, rfl⟩
  have hprod : QuotientGroup.mk u * QuotientGroup.mk y ∈
      u3YM L1 L2 S lj ⊔ u3YM L1 L2 S l :=
    (u3YM L1 L2 S lj ⊔ u3YM L1 L2 S l).mul_mem
      (Subgroup.mem_sup_left hmemu) (Subgroup.mem_sup_right hmemy)
  change (u3MQuotAct (k := k) (F := F) hF hSB hU3 hX1Q1 a)
      (QuotientGroup.mk u) ∈ u3YM L1 L2 S l ⊔ u3YM L1 L2 S lj
  rw [hact]
  simpa [sup_comm] using hprod

theorem str86_X1_upper_bound
    {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S) :
    Nat.card (u3M L1 L2 S) ≤ (2 ^ k) ^ 6 := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hY' : Nat.card (u3Y L1 L2 S) = (2 ^ k) ^ 3 := by
    simpa [u3Y] using hY
  let H : Subgroup G := u3LS L1 L2 S
  let Q := oTwoQuot H
  let M := u3M L1 L2 S
  let mkM : ↥(u3X1 L1 L2 S) →* M :=
    QuotientGroup.mk' ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S))
  let T0 : Sylow 2 Q := u3T0 (k := k) (F := F) hF hSB h1
  let A0 : Subgroup Q := imageOTwoQuot H (Z2 L1 L2 S)
  have hA0 : A0 = omegaOneOf (T0 : Subgroup Q) := by
    simpa [A0, T0, H, Q] using
      u3A0_eq_omegaOne_T0 (k := k) (F := F) hF hSB hk hFc hU3 hZQ h1
  obtain ⟨T1, hT1ne⟩ := u3_exists_sylow_ne_T0 (k := k) (F := F) hF hSB h1
  obtain ⟨T2, hT2⟩ := exists_sup_three_omegaOne_eq_top hk hFc
    (u3HQU3 (k := k) (F := F) hF hSB hU3 h1) T0 T1 (fun h => hT1ne h.symm)
  obtain ⟨q1, hq1⟩ := MulAction.exists_smul_eq (M := Q) T0 T1
  obtain ⟨q2, hq2⟩ := MulAction.exists_smul_eq (M := Q) T0 T2
  obtain ⟨h1H, hq1'⟩ := QuotientGroup.mk_surjective q1
  obtain ⟨h2H, hq2'⟩ := QuotientGroup.mk_surjective q2
  obtain ⟨l1, hl1, s1, hs1, hh1⟩ := u3_exists_mul_mem_L1_S (L1 := L1) (L2 := L2) (S := S) hF h1H
  obtain ⟨l2, hl2, s2, hs2, hh2⟩ := u3_exists_mul_mem_L1_S (L1 := L1) (L2 := L2) (S := S) hF h2H
  let YM0 : Subgroup M := u3YM L1 L2 S 1
  let YM1 : Subgroup M := u3YM L1 L2 S l1
  let YM2 : Subgroup M := u3YM L1 L2 S l2
  let Ssub : Subgroup M := YM0 ⊔ YM1 ⊔ YM2
  have hYM0 : Nat.card YM0 ≤ (2 ^ k) ^ 2 := by
    simpa [YM0] using u3YM_card_le (L1 := L1) (L2 := L2) (S := S) (k := k) (F := F)
      hF hSB hk hFc hU3 hB2 h2 hZI hY' hZ1 (l := (1 : G)) L1.one_mem
  have hYM1 : Nat.card YM1 ≤ (2 ^ k) ^ 2 := by
    simpa [YM1] using u3YM_card_le (L1 := L1) (L2 := L2) (S := S) (k := k) (F := F)
      hF hSB hk hFc hU3 hB2 h2 hZI hY' hZ1 (l := l1) hl1
  have hYM2 : Nat.card YM2 ≤ (2 ^ k) ^ 2 := by
    simpa [YM2] using u3YM_card_le (L1 := L1) (L2 := L2) (S := S) (k := k) (F := F)
      hF hSB hk hFc hU3 hB2 h2 hZI hY' hZ1 (l := l2) hl2
  let A1 : Subgroup Q := (omegaOneOf (T0 : Subgroup Q)).map (MulAut.conj q1).toMonoidHom
  let A2 : Subgroup Q := (omegaOneOf (T0 : Subgroup Q)).map (MulAut.conj q2).toMonoidHom
  have hA1_omega : A1 = omegaOneOf (T1 : Subgroup Q) := by
    have h := u3_omegaOneOf_smul q1 T0
    rw [hq1] at h
    simpa [A1] using h.symm
  have hA2_omega : A2 = omegaOneOf (T2 : Subgroup Q) := by
    have h := u3_omegaOneOf_smul q2 T0
    rw [hq2] at h
    simpa [A2] using h.symm
  have hAsup : A0 ⊔ A1 ⊔ A2 = ⊤ := by
    rw [hA0, hA1_omega, hA2_omega]
    exact hT2
  have hAq0 : A0 = A0.map (MulAut.conj (1 : Q)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  have hAq1 : A1 = A0.map (MulAut.conj q1).toMonoidHom := by
    simpa [A1] using
      (congrArg (fun S => S.map (MulAut.conj q1).toMonoidHom) hA0).symm
  have hAq2 : A2 = A0.map (MulAut.conj q2).toMonoidHom := by
    simpa [A2] using
      (congrArg (fun S => S.map (MulAut.conj q2).toMonoidHom) hA0).symm
  let act : Q →* MulAut M := u3MQuotAct (k := k) (F := F) hF hSB h1 hX1Q1
  have hYM0S : YM0 ≤ Ssub := by
    dsimp [Ssub]
    exact le_sup_left.trans le_sup_left
  have hYM1S : YM1 ≤ Ssub := by
    dsimp [Ssub]
    exact le_sup_right.trans le_sup_left
  have hYM2S : YM2 ≤ Ssub := by
    dsimp [Ssub]
    exact le_sup_right
  have hsmul_le_of_mem {q : Q} {h : H} {l s : G}
      (hq : QuotientGroup.mk h = q) (hl : l ∈ L1) (hs : s ∈ S) (hh : (h : G) = l * s)
      {Aq : Subgroup Q} (hAq : Aq = A0.map (MulAut.conj q).toMonoidHom)
      (hYlS : u3YM L1 L2 S l ≤ Ssub) :
      ∀ b ∈ Aq, (act b) • Ssub ≤ Ssub := by
    intro b hb
    have h0 := u3_act_u3YM_le (L1 := L1) (L2 := L2) (S := S) (k := k) (F := F)
      hF hSB h1 hX1Q1 hq hl hs hh hAq hb (lj := (1 : G)) L1.one_mem
    have h1' := u3_act_u3YM_le (L1 := L1) (L2 := L2) (S := S) (k := k) (F := F)
      hF hSB h1 hX1Q1 hq hl hs hh hAq hb (lj := l1) hl1
    have h2' := u3_act_u3YM_le (L1 := L1) (L2 := L2) (S := S) (k := k) (F := F)
      hF hSB h1 hX1Q1 hq hl hs hh hAq hb (lj := l2) hl2
    have h0S : (act b) • YM0 ≤ Ssub := by
      have hle : u3YM L1 L2 S l ⊔ u3YM L1 L2 S 1 ≤ Ssub :=
        sup_le hYlS hYM0S
      have h0' : (act b) • YM0 ≤
          u3YM L1 L2 S l ⊔ u3YM L1 L2 S 1 := by
        simpa [act, YM0] using h0
      exact h0'.trans hle
    have h1S : (act b) • YM1 ≤ Ssub := by
      have hle : u3YM L1 L2 S l ⊔ u3YM L1 L2 S l1 ≤ Ssub :=
        sup_le hYlS hYM1S
      have h1'' : (act b) • YM1 ≤
          u3YM L1 L2 S l ⊔ u3YM L1 L2 S l1 := by
        simpa [act, YM1] using h1'
      exact h1''.trans hle
    have h2S : (act b) • YM2 ≤ Ssub := by
      have hle : u3YM L1 L2 S l ⊔ u3YM L1 L2 S l2 ≤ Ssub :=
        sup_le hYlS hYM2S
      have h2'' : (act b) • YM2 ≤
          u3YM L1 L2 S l ⊔ u3YM L1 L2 S l2 := by
        simpa [act, YM2] using h2'
      exact h2''.trans hle
    calc (act b) • Ssub = (act b) • YM0 ⊔ (act b) • YM1 ⊔ (act b) • YM2 := by
          dsimp [Ssub]
          rw [Subgroup.smul_sup, Subgroup.smul_sup]
      _ ≤ Ssub := sup_le (sup_le h0S h1S) h2S
  have hsmul_eq_of_mem {q : Q} {h : H} {l s : G}
      (hq : QuotientGroup.mk h = q) (hl : l ∈ L1) (hs : s ∈ S) (hh : (h : G) = l * s)
      {Aq : Subgroup Q} (hAq : Aq = A0.map (MulAut.conj q).toMonoidHom)
      (hYlS : u3YM L1 L2 S l ≤ Ssub) :
      ∀ b ∈ Aq, (act b) • Ssub = Ssub := by
    intro b hb
    apply le_antisymm (hsmul_le_of_mem hq hl hs hh hAq hYlS b hb)
    have hle_inv : (act b⁻¹) • Ssub ≤ Ssub :=
      hsmul_le_of_mem hq hl hs hh hAq hYlS b⁻¹ (Aq.inv_mem hb)
    calc Ssub = (act (b * b⁻¹)) • Ssub := by simp
      _ = (act b * act b⁻¹) • Ssub := by rw [map_mul]
      _ = (act b) • ((act b⁻¹) • Ssub) := by rw [mul_smul]
      _ ≤ (act b) • Ssub :=
          (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hle_inv
  have hA0_eq : ∀ b ∈ A0, (act b) • Ssub = Ssub :=
    hsmul_eq_of_mem (q := 1) (h := 1) (l := 1) (s := 1) (by simp) L1.one_mem S.one_mem
      (by simp) hAq0 hYM0S
  have hA1_eq : ∀ b ∈ A1, (act b) • Ssub = Ssub :=
    hsmul_eq_of_mem (q := q1) (h := h1H) (l := l1) (s := s1) hq1' hl1 hs1 hh1 hAq1
      hYM1S
  have hA2_eq : ∀ b ∈ A2, (act b) • Ssub = Ssub :=
    hsmul_eq_of_mem (q := q2) (h := h2H) (l := l2) (s := s2) hq2' hl2 hs2 hh2 hAq2
      hYM2S
  let N : Subgroup Q :=
    { carrier := {q | (act q) • Ssub = Ssub}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change (act (a * b)) • Ssub = Ssub
        rw [map_mul, mul_smul, hb, ha]
      inv_mem' := by
        intro a ha
        have h := congrArg (fun T => (act a)⁻¹ • T) ha
        simpa [← mul_smul, map_inv] using h.symm }
  have hA0N : A0 ≤ N := hA0_eq
  have hA1N : A1 ≤ N := hA1_eq
  have hA2N : A2 ≤ N := hA2_eq
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = A0 ⊔ A1 ⊔ A2 := hAsup.symm
      _ ≤ N := sup_le (sup_le hA0N hA1N) hA2N
  have hInv : ∀ q : Q, (act q) • Ssub = Ssub := by
    intro q
    have hq : q ∈ N := by
      rw [hNtop]
      exact Subgroup.mem_top q
    exact hq
  have hSsub_top : Ssub = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)) m
    let Gens : Set G := {g | ∃ l ∈ L1, ∃ y ∈ u3Y L1 L2 S, l * y * l⁻¹ = g}
    have hXeq : u3X1 L1 L2 S = Subgroup.closure Gens := rfl
    have hxmem : (x : G) ∈ Subgroup.closure Gens := hXeq ▸ x.2
    have hmain : ∀ g (hg : g ∈ Subgroup.closure Gens),
        mkM ⟨g, hXeq ▸ hg⟩ ∈ Ssub := by
      intro g hg
      refine Subgroup.closure_induction
        (p := fun g hg => mkM ⟨g, hXeq ▸ hg⟩ ∈ Ssub) ?_ ?_ ?_ ?_ hg
      · rintro x ⟨l, hl, y, hy, rfl⟩
        have hyX : y ∈ u3X1 L1 L2 S := u3Y_le_u3X1 hy
        let lH : H := ⟨l, (le_sup_left : L1 ≤ H) hl⟩
        have hqN : (QuotientGroup.mk lH : Q) ∈ N := hNtop ▸ Subgroup.mem_top _
        have hInvL : (act (QuotientGroup.mk lH)) • Ssub = Ssub := hqN
        have hyYM : mkM ⟨y, hyX⟩ ∈ YM0 := by
          have hYX1 : conjSub (1 : G) (u3Y L1 L2 S) ≤ u3X1 L1 L2 S :=
            u3_conjSub_le_u3X1 (L1 := L1) (L2 := L2) (S := S) L1.one_mem
          have hmem : mkM ⟨y, hyX⟩ ∈ u3YM L1 L2 S 1 := by
            rw [mem_u3YM hYX1]
            exact ⟨⟨y, hyX⟩, by simpa [conjSub, MulAut.conj_apply] using hy, rfl⟩
          simpa [YM0] using hmem
        have hsm : (act (QuotientGroup.mk lH)) (mkM ⟨y, hyX⟩) ∈ Ssub := by
          have hyS : mkM ⟨y, hyX⟩ ∈ Ssub := hYM0S hyYM
          have h := Subgroup.smul_mem_pointwise_smul (mkM ⟨y, hyX⟩)
            (act (QuotientGroup.mk lH)) Ssub hyS
          rwa [hInvL] at h
        have heq : mkM ⟨l * y * l⁻¹, hXeq ▸ Subgroup.subset_closure ⟨l, hl, y, hy, rfl⟩⟩ =
            (act (QuotientGroup.mk lH)) (mkM ⟨y, hyX⟩) := by
          dsimp only [act, mkM]
          change QuotientGroup.mk (⟨l * y * l⁻¹,
            hXeq ▸ Subgroup.subset_closure ⟨l, hl, y, hy, rfl⟩⟩ : ↥(u3X1 L1 L2 S)) =
            u3MQuotAct (k := k) (F := F) hF hSB h1 hX1Q1
              (QuotientGroup.mk lH) (QuotientGroup.mk ⟨y, hyX⟩)
          rw [u3MQuotAct_mk_apply]
        rw [heq]
        exact hsm
      · change mkM (1 : ↥(u3X1 L1 L2 S)) ∈ Ssub
        rw [map_one]
        exact Ssub.one_mem
      · intro x y hx hy ihx ihy
        have heq : mkM ⟨x * y, hXeq ▸ (Subgroup.closure Gens).mul_mem hx hy⟩ =
            mkM ⟨x, hXeq ▸ hx⟩ * mkM ⟨y, hXeq ▸ hy⟩ := by
          dsimp only [mkM]
          rw [← map_mul]
          rfl
        rw [heq]
        exact Ssub.mul_mem ihx ihy
      · intro x hx ih
        have heq : mkM ⟨x⁻¹, hXeq ▸ (Subgroup.closure Gens).inv_mem hx⟩ =
            (mkM ⟨x, hXeq ▸ hx⟩)⁻¹ := by
          dsimp only [mkM]
          rw [← map_inv]
          rfl
        rw [heq]
        exact Ssub.inv_mem ih
    exact hmain (x : G) hxmem
  letI : CommGroup M := u3MCommGroup hX1'
  have hMcard : Nat.card M = Nat.card Ssub := by
    rw [hSsub_top, Subgroup.card_top]
  calc Nat.card M = Nat.card Ssub := hMcard
    _ ≤ Nat.card ↥(YM0 ⊔ YM1) * Nat.card YM2 :=
        CFSG.Quasithin.FFC.card_sup_le_mul _ _
    _ ≤ (Nat.card YM0 * Nat.card YM1) * Nat.card YM2 :=
        Nat.mul_le_mul_right _ (CFSG.Quasithin.FFC.card_sup_le_mul _ _)
    _ ≤ ((2 ^ k) ^ 2 * (2 ^ k) ^ 2) * (2 ^ k) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul hYM0 hYM1) hYM2
    _ = (2 ^ k) ^ 6 := by ring

end CFSG.Quasithin.Stroth

module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LSRQ
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2WedgeP2

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative Pointwise

theorem mem_liftPre_of_mem {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* L3321.SL4}
    {P : Subgroup L3321.SL4} {x : G} (hx : x ∈ L) :
    x ∈ L3316.liftPre α P ↔ α ⟨x, hx⟩ ∈ P :=
  mem_liftPre_iff' (⟨x, hx⟩ : ↥L)

theorem liftPre_U2_le_P2 {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* L3321.SL4} :
    L3316.liftPre α U2 ≤ L3316.liftPre α L3321.P2 := by
  intro x hx
  have hxL : x ∈ L := L3316.liftPre_le α _ hx
  exact (mem_liftPre_of_mem hxL).2 (U2_le_P2 ((mem_liftPre_of_mem hxL).1 hx))

theorem conj_mem_liftPre_U2 {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* L3321.SL4}
    {c x : G} (hc : c ∈ L3316.liftPre α L3321.P2) (hx : x ∈ L3316.liftPre α U2) :
    c * x * c⁻¹ ∈ L3316.liftPre α U2 := by
  have hcL : c ∈ L := L3316.liftPre_le α _ hc
  have hxL : x ∈ L := L3316.liftPre_le α _ hx
  have hcx : c * x * c⁻¹ ∈ L := L.mul_mem (L.mul_mem hcL hxL) (L.inv_mem hcL)
  have hc2 : α ⟨c, hcL⟩ ∈ L3321.P2 := (mem_liftPre_of_mem hcL).1 hc
  have hx2 : α ⟨x, hxL⟩ ∈ U2 := (mem_liftPre_of_mem hxL).1 hx
  have hn : (⟨α ⟨x, hxL⟩, U2_le_P2 hx2⟩ : ↥L3321.P2) ∈ U2.subgroupOf L3321.P2 :=
    Subgroup.mem_subgroupOf.2 hx2
  have hconj := Subgroup.mem_subgroupOf.1
    (U2_normal_in_P2.conj_mem _ hn ⟨α ⟨c, hcL⟩, hc2⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hconj
  refine (mem_liftPre_of_mem hcx).2 ?_
  have e : (⟨c * x * c⁻¹, hcx⟩ : ↥L) = ⟨c, hcL⟩ * ⟨x, hxL⟩ * ⟨c, hcL⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact hconj

theorem le_normalizer_liftPre_U2 {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* L3321.SL4} :
    L3316.liftPre α L3321.P2 ≤ Subgroup.normalizer (L3316.liftPre α U2 : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_liftPre_U2 hc hx
  · intro hx
    have hc' : c⁻¹ ∈ L3316.liftPre α L3321.P2 := (L3316.liftPre α L3321.P2).inv_mem hc
    have h := conj_mem_liftPre_U2 hc' hx
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rw [e] at h
    exact h

theorem isPGroup_liftPre_U2 {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* L3321.SL4}
    (hker : IsPGroup 2 α.ker) : IsPGroup 2 (L3316.liftPre α U2) :=
  IsPGroup.map (IsPGroup.comap_of_ker_isPGroup U2_isPGroup α hker) L.subtype

theorem pCoreOf_liftPre_P2_le {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* L3321.SL4}
    (hαs : Function.Surjective α) :
    pCoreOf 2 (L3316.liftPre α L3321.P2) ≤ L3316.liftPre α U2 := by
  have hCL : L3316.liftPre α L3321.P2 ≤ L := L3316.liftPre_le α _
  let f : ↥(L3316.liftPre α L3321.P2) →* ↥L3321.P2 :=
    (α.comp (Subgroup.inclusion hCL)).codRestrict L3321.P2
      (fun w => (mem_liftPre_of_mem (hCL w.2)).1 w.2)
  have hf : Function.Surjective f := by
    rintro ⟨p, hp⟩
    obtain ⟨l, rfl⟩ := hαs p
    have hlC : (l : G) ∈ L3316.liftPre α L3321.P2 := (mem_liftPre_of_mem l.2).2 hp
    exact ⟨⟨(l : G), hlC⟩, rfl⟩
  have hmap := CFSG.LieType.BorelTits.map_pCore_le 2 f hf
  rw [← U2_eq_pCore] at hmap
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  have hfw : f w ∈ U2.subgroupOf L3321.P2 := hmap (Subgroup.mem_map_of_mem f hw)
  exact (mem_liftPre_of_mem (hCL w.2)).2 (Subgroup.mem_subgroupOf.1 hfw)

theorem liftPre_U2_eq_pCoreOf {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* L3321.SL4}
    (hαs : Function.Surjective α) (hker : IsPGroup 2 α.ker) :
    L3316.liftPre α U2 = pCoreOf 2 (L3316.liftPre α L3321.P2) := by
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 liftPre_U2_le_P2
      le_normalizer_liftPre_U2 (isPGroup_liftPre_U2 hker)
  · exact pCoreOf_liftPre_P2_le hαs

theorem index_ker_inclusion_liftPre_U2 {G : Type} [Group G] {L : Subgroup G}
    {α : ↥L →* L3321.SL4} (hαs : Function.Surjective α) (hP1L : L3316.liftPre α U2 ≤ L) :
    (α.comp (Subgroup.inclusion hP1L)).ker.index = 16 := by
  rw [Subgroup.index_ker]
  have hr : (α.comp (Subgroup.inclusion hP1L)).range = U2 := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
      exact (mem_liftPre_of_mem (hP1L x.2)).1 x.2
    · intro hy
      obtain ⟨l, rfl⟩ := hαs y
      have hlP : (l : G) ∈ L3316.liftPre α U2 := (mem_liftPre_of_mem l.2).2 hy
      exact MonoidHom.mem_range.2 ⟨⟨(l : G), hlP⟩, rfl⟩
  rw [hr, card_U2]

theorem index_le_relIndex_sup_of_mem {G : Type} [Group G] [Finite G] {N Q : Subgroup G}
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G)) (K : Subgroup ↥N)
    (hK : ∀ x : ↥N, (x : G) ∈ Q → x ∈ K) :
    K.index ≤ Q.relIndex (N ⊔ Q) := by
  have hN' : N ⊔ Q ≤ Subgroup.normalizer (Q : Set G) := sup_le hNQ Subgroup.le_normalizer
  haveI : (Q.subgroupOf (N ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hN'
  let φ : ↥N →* ↥(N ⊔ Q) ⧸ Q.subgroupOf (N ⊔ Q) :=
    (QuotientGroup.mk' (Q.subgroupOf (N ⊔ Q))).comp
      (Subgroup.inclusion (le_sup_left : N ≤ N ⊔ Q))
  have hφs : Function.Surjective φ := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : (y : G) ∈ (N : Set G) * (Q : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right N Q hNQ]; exact y.2
    obtain ⟨l, hl, q, hq, hlq⟩ := hy
    refine ⟨⟨l, hl⟩, ?_⟩
    show (QuotientGroup.mk _ : ↥(N ⊔ Q) ⧸ Q.subgroupOf (N ⊔ Q)) = QuotientGroup.mk y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (l : G)⁻¹ * (y : G) ∈ Q
    rw [← hlq]
    simpa using hq
  have hφk : φ.ker.index = Q.relIndex (N ⊔ Q) := by
    have h1 := Subgroup.index_comap_of_surjective
      (H := (⊥ : Subgroup (↥(N ⊔ Q) ⧸ Q.subgroupOf (N ⊔ Q)))) hφs
    rw [Subgroup.index_bot, ← Subgroup.index_eq_card] at h1
    exact h1
  have hle : φ.ker ≤ K := by
    intro l hl
    have h1 : (QuotientGroup.mk (Subgroup.inclusion (le_sup_left : N ≤ N ⊔ Q) l) :
        ↥(N ⊔ Q) ⧸ Q.subgroupOf (N ⊔ Q)) = 1 := MonoidHom.mem_ker.1 hl
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact hK l h1
  rw [← hφk]
  exact Subgroup.index_antitone hle

section Main

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.R_le_liftU2_mul_Q (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (c : A2Cfg G T M L D H K q) {α : ↥L →* L3321.SL4} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hCZ : L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
      L3316.liftPre α L3321.P2) :
    ∀ r ∈ pCoreOf 2 H, ∃ l : ↥L, α l ∈ U2 ∧ ∃ q ∈ pCoreOf 2 (L ⊔ T), r = (l : G) * q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP1L : L3316.liftPre α U2 ≤ L := L3316.liftPre_le α U2
  have hker : IsPGroup 2 α.ker := by
    rw [hαk]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hP1eq : L3316.liftPre α U2 = pCoreOf 2 (L3316.liftPre α L3321.P2) :=
    liftPre_U2_eq_pCoreOf hαs hker
  have hHC : H = L3316.liftPre α L3321.P2 ⊔ T := by
    rw [c.hH, hCZ]
  have hTC : T ≤ Subgroup.normalizer (L3316.liftPre α L3321.P2 : Set G) := by
    have h1 : T ≤ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) : Subgroup G) : Set G) :=
      CFSG.Quasithin.F7.le_normalizer_inf c.TL
        ((CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T).trans
          Subgroup.le_normalizer)
    rw [hCZ] at h1
    exact h1
  have hHN : H ≤ Subgroup.normalizer (L3316.liftPre α U2 : Set G) := by
    rw [hHC]
    refine sup_le le_normalizer_liftPre_U2 ?_
    rw [hP1eq]
    exact hTC.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hP1H : L3316.liftPre α U2 ≤ H := by
    rw [hHC]
    exact (liftPre_U2_le_P2 (α := α)).trans le_sup_left
  have hP1R : L3316.liftPre α U2 ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP1H hHN (isPGroup_liftPre_U2 hker)
  have hQN : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := le_sup_left.trans hQN
  have hP1N : L3316.liftPre α U2 ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    hP1L.trans hLQ
  have hQL : pCoreOf 2 (L ⊔ T) ⊓ L ≤ pCoreOf 2 L := by
    have hp : IsPGroup 2 (pCoreOf 2 (L ⊔ T) ⊓ L : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_left
    have hn : L ≤ Subgroup.normalizer ((pCoreOf 2 (L ⊔ T) ⊓ L : Subgroup G) : Set G) :=
      CFSG.Quasithin.F7.le_normalizer_inf hLQ Subgroup.le_normalizer
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hn hp
  obtain ⟨K₁, hK₁def⟩ : ∃ K : Subgroup ↥(L3316.liftPre α U2),
      K = (α.comp (Subgroup.inclusion hP1L)).ker := ⟨_, rfl⟩
  have hK₁ : ∀ x : ↥(L3316.liftPre α U2), (x : G) ∈ pCoreOf 2 (L ⊔ T) → x ∈ K₁ := by
    rw [hK₁def]
    intro x hxQ
    have hxL : (x : G) ∈ L := hP1L x.2
    have hxpc : (x : G) ∈ pCoreOf 2 L := hQL (Subgroup.mem_inf.2 ⟨hxQ, hxL⟩)
    have hxker : (⟨(x : G), hxL⟩ : ↥L) ∈ α.ker := by
      rw [hαk]
      exact (Lem3328.mem_pCore_iff (⟨(x : G), hxL⟩ : ↥L)).2 hxpc
    exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hxker)
  have hK₁idx : K₁.index = 16 := by
    rw [hK₁def]
    exact index_ker_inclusion_liftPre_U2 hαs hP1L
  have hS16 : 16 ≤ (pCoreOf 2 (L ⊔ T)).relIndex (L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)) := by
    have h := index_le_relIndex_sup_of_mem hP1N K₁ hK₁
    rw [hK₁idx] at h
    exact h
  have hR2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hm : CFSG.Quasithin.mIdx (pCoreOf 2 H) (pCoreOf 2 (L ⊔ T)) ≤ 4 :=
    leaf_LSRQ_of h9 hGA G T M L D H K q c
  have hpow := CFSG.Quasithin.HypF98.relIndex_eq_two_pow_mIdx
    (X := pCoreOf 2 H) (Y := pCoreOf 2 (L ⊔ T)) hR2
  have hR16 : (pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) ≤ 16 := by
    rw [hpow]
    calc 2 ^ CFSG.Quasithin.mIdx (pCoreOf 2 H) (pCoreOf 2 (L ⊔ T))
        ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hm
      _ = 16 := by norm_num
  have hRpos : 0 < (pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) := by
    rw [hpow]
    positivity
  have hS_R : L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 H :=
    sup_le hP1R c.Q_le_R
  have hmul : (pCoreOf 2 (L ⊔ T)).relIndex (L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)) *
      (L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) =
      (pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) :=
    Subgroup.relIndex_mul_relIndex (H := pCoreOf 2 (L ⊔ T))
      (K := L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)) (L := pCoreOf 2 H) le_sup_right hS_R
  have hS1 : (L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) = 1 := by
    have hle1 : (L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) ≤ 1 := by
      by_contra hcon
      have h2 : 2 ≤ (L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) := by
        omega
      have h3 := Nat.mul_le_mul hS16 h2
      rw [hmul] at h3
      omega
    have hpos1 : 0 < (L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) := by
      rcases Nat.eq_zero_or_pos
        ((L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H)) with h0 | h0
      · rw [h0, mul_zero] at hmul
        omega
      · exact h0
    omega
  have hSR : L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T) = pCoreOf 2 H :=
    le_antisymm hS_R (Subgroup.relIndex_eq_one.1 hS1)
  intro r hr
  have hrS : r ∈ L3316.liftPre α U2 ⊔ pCoreOf 2 (L ⊔ T) := by
    rw [hSR]
    exact hr
  have hrS' : r ∈ (L3316.liftPre α U2 : Set G) * (pCoreOf 2 (L ⊔ T) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hP1N]
    exact hrS
  obtain ⟨p, hp, q', hq', hpq⟩ := hrS'
  have hpL : p ∈ L := hP1L hp
  exact ⟨⟨p, hpL⟩, (mem_liftPre_of_mem hpL).1 hp, q', hq', hpq.symm⟩

end Main

end CFSG.Quasithin.H13.NFa2

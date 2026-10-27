module

public import CFSG.Milestones.ASVolI.C121.Red1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

theorem burnsideC121_noTwoQuotient_oTwoUpper {Ω : Type} [Group Ω] [Finite Ω] (X : Subgroup Ω) :
    CFSG.CGT.PushingUpLit.SubTwo.NoTwoQuotient (oTwoUpper X) := by
  intro N hN _ h2
  refine le_antisymm hN (oTwoUpper_le_of_pow_mem fun x hx => ?_)
  obtain ⟨k₁, hk₁⟩ := exists_pow_mem_oTwoUpper X hx
  obtain ⟨k₂, hk₂⟩ := h2 _ hk₁
  exact ⟨k₁ + k₂, by rw [pow_add, pow_mul]; exact hk₂⟩

theorem burnsideC121_le_normalizer_of_conj {Ω : Type} [Group Ω] {L K : Subgroup Ω}
    (h : ∀ m ∈ L, ∀ x ∈ K, m * x * m⁻¹ ∈ K) : L ≤ Subgroup.normalizer (K : Set Ω) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h m hm x, fun hx => ?_⟩
  have := h m⁻¹ (L.inv_mem hm) _ hx
  simpa [mul_assoc] using this

theorem burnsideC121_commutator_le_of_gen {Ω : Type} [Group Ω] {L Q V Y : Subgroup Ω}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set Ω)) (hLV : L ≤ Subgroup.normalizer (V : Set Ω))
    (hgen : ∀ N : Subgroup Ω, N ≤ L → L ≤ Subgroup.normalizer (N : Set Ω) → Y ≤ N → N = L)
    (hYL : Y ≤ L) (hQY : ⁅Q, Y⁆ ≤ V) : ⁅Q, L⁆ ≤ V := by
  have hV : ∀ m ∈ L, ∀ v ∈ V, m * v * m⁻¹ ∈ V := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hLV hm) v).1 hv
  let K : Subgroup Ω :=
    { carrier := {l | l ∈ L ∧ ∀ q ∈ Q, ⁅q, l⁆ ∈ V}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨L.mul_mem ha hb, fun q hq => ?_⟩
        have e : ⁅q, a * b⁆ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact V.mul_mem (ha' q hq) (hV a ha _ (hb' q hq))
      one_mem' := ⟨L.one_mem, fun q _ => by rw [commutatorElement_one_right]; exact V.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨L.inv_mem ha, fun q hq => ?_⟩
        have e : ⁅q, a⁻¹⁆ = a⁻¹ * ⁅q, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hV a⁻¹ (L.inv_mem ha) _ (V.inv_mem (ha' q hq)) }
  have hmemK : ∀ l, l ∈ K ↔ l ∈ L ∧ ∀ q ∈ Q, ⁅q, l⁆ ∈ V := fun l => Iff.rfl
  have hKL : K ≤ L := fun l hl => ((hmemK l).1 hl).1
  have hLK : L ≤ Subgroup.normalizer (K : Set Ω) := by
    refine burnsideC121_le_normalizer_of_conj fun m hm l hl => ?_
    obtain ⟨hlL, hlQ⟩ := (hmemK l).1 hl
    refine (hmemK _).2 ⟨L.mul_mem (L.mul_mem hm hlL) (L.inv_mem hm), fun q hq => ?_⟩
    have hq' : m⁻¹ * q * m⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 (hLQ (L.inv_mem hm)) q).1 hq
    have e : ⁅q, m * l * m⁻¹⁆ = m * ⁅m⁻¹ * q * m⁻¹⁻¹, l⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hV m hm _ (hlQ _ hq')
  have hYK : Y ≤ K := fun y hy =>
    (hmemK y).2 ⟨hYL hy, fun q hq => hQY (Subgroup.commutator_mem_commutator hq hy)⟩
  have hKeq := hgen K hKL hLK hYK
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have hlK : l ∈ K := by rw [hKeq]; exact hl
  exact ((hmemK l).1 hlK).2 q hq

theorem burnsideC121_e12_e21_ne {F : Type} [Field F] :
    SL2Model.e12 (1 : F) * SL2Model.e21 1 ≠ SL2Model.e21 1 * SL2Model.e12 1 := by
  intro h
  have h3 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h3

theorem burnsideC121_L_le_X {Ω : Type} [Group Ω] {X L : Subgroup Ω} (hLX : L = oTwoUpper X) :
    L ≤ X := by
  rw [hLX]; exact oTwoUpper_le X

theorem burnsideC121_X_le_normalizer_L {Ω : Type} [Group Ω] [Finite Ω] {X L : Subgroup Ω}
    (hLX : L = oTwoUpper X) : X ≤ Subgroup.normalizer (L : Set Ω) := by
  rw [hLX]; exact le_normalizer_oTwoUpper X

theorem burnsideC121_pCore_L_le {Ω : Type} [Group Ω] [Finite Ω] {X L : Subgroup Ω}
    (hLX : L = oTwoUpper X) : pCoreOf 2 L ≤ pCoreOf 2 X :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans (burnsideC121_L_le_X hLX))
    ((burnsideC121_X_le_normalizer_L hLX).trans (normalizer_le_normalizer_pCoreOf 2 L))
    (pCoreOf_isPGroup 2 L)

theorem burnsideC121_Q_inf_L_le {Ω : Type} [Group Ω] [Finite Ω] {X L : Subgroup Ω}
    (hLX : L = oTwoUpper X) : pCoreOf 2 X ⊓ L ≤ pCoreOf 2 L :=
  C1.le_pCoreOf_of_normalized inf_le_right
    (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨((burnsideC121_L_le_X hLX).trans (le_normalizer_pCoreOf 2 X)) hl, Subgroup.le_normalizer hl⟩)
    ((pCoreOf_isPGroup 2 X).to_le inf_le_left)

theorem burnsideC121_eq_of_block {Ω : Type} [Group Ω] [Finite Ω] {X L Y : Subgroup Ω}
    (hLX : L = oTwoUpper X) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hperf : ⁅L, L⁆ = L) (hYL : Y ≤ L)
    (hOY : pCoreOf 2 L ≤ Subgroup.normalizer (Y : Set Ω)) (hYperf : Y = oTwoUpper Y)
    (hblk : IsL2OrA3Block Y Y) {N : Subgroup Ω} (hNL : N ≤ L)
    (hLN : L ≤ Subgroup.normalizer (N : Set Ω)) (hYN : Y ≤ N) : N = L := by
  classical
  have hN0 : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hNm : ((N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    hN0.map _ (QuotientGroup.mk'_surjective _)
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set Ω) := le_normalizer_pCoreOf 2 L
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hNm with h | h
  ·
    have hntL : CFSG.CGT.PushingUpLit.SubTwo.NoTwoQuotient L := by
      rw [hLX]; exact burnsideC121_noTwoQuotient_oTwoUpper X
    refine hntL N hNL hLN fun l hl => ?_
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨l, hl⟩ ∈
        (N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [h]; exact Subgroup.mem_top _
    obtain ⟨m, hm, hml⟩ := hmem
    have hml' : ((m : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) =
        ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) := hml
    have ho : ((m⁻¹ * ⟨l, hl⟩ : ↥L) : Ω) ∈ pCoreOf 2 L :=
      (CFSG.mem_openPCoreOf_iff _).2 (QuotientGroup.eq.1 hml')
    exact C124.exists_pow_mem_of_prod hNL hLN (pCoreOf_le 2 L) (pCoreOf_isPGroup 2 L) hl
      ⟨m, hm, _, ho, by simp⟩
  ·
    have hc : ∀ y ∈ Y, ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
      intro y hy l hl
      have hyc : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨y, hYL hy⟩ ∈
          Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
        h ⟨⟨y, hYL hy⟩, hYN hy, rfl⟩
      have hcomm : ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) *
          ((⟨y, hYL hy⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) =
          ((⟨y, hYL hy⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) *
            ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) :=
        Subgroup.mem_center_iff.1 hyc _
      have h1 : ((⟨l, hl⟩ * ⟨y, hYL hy⟩ * (⟨l, hl⟩ : ↥L)⁻¹ * (⟨y, hYL hy⟩ : ↥L)⁻¹ : ↥L) :
          ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
      exact (CFSG.mem_openPCoreOf_iff _).2 ((QuotientGroup.eq_one_iff _).1 h1)
    have hOYY : pCoreOf 2 L ⊓ Y ≤ pCoreOf 2 Y :=
      C1.le_pCoreOf_of_normalized inf_le_right
        (fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hLO (hYL hy), Subgroup.le_normalizer hy⟩)
        ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
    have hYs : IsShort2 Y := hblk.1.1
    exfalso
    rcases hblk.2 with ⟨n, -, F, _, _, -, α, hαs, hαk, -⟩ | ⟨α, hαs, hαk, β, hβs, hβk, -⟩
    ·
      obtain ⟨y₁, hy₁⟩ := hαs (SL2Model.e12 1)
      obtain ⟨y₂, hy₂⟩ := hαs (SL2Model.e21 1)
      have hk : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ α.ker := by
        rw [hαk, ← CFSG.mem_openPCoreOf_iff]
        exact hOYY ⟨hc y₂ y₂.2 y₁ (hYL y₁.2), (y₁ * y₂ * y₁⁻¹ * y₂⁻¹).2⟩
      have h1 : α (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) = 1 := hk
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy₁, hy₂, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact burnsideC121_e12_e21_ne h1
    ·
      have hMY : Y ⊔ pCoreOf 2 L ≤ Subgroup.normalizer (Y : Set Ω) :=
        sup_le Subgroup.le_normalizer hOY
      have hYM : Y = oTwoUpper (Y ⊔ pCoreOf 2 L) := by
        refine eq_oTwoUpper_of_pow_mem le_sup_left (fun x hx => ?_) hYperf
        have hx' : x ∈ ((Y ⊔ pCoreOf 2 L : Subgroup Ω) : Set Ω) := hx
        rw [Subgroup.coe_mul_of_right_le_normalizer_left Y _ hOY] at hx'
        obtain ⟨y, hy, o, ho, rfl⟩ := hx'
        exact C124.exists_pow_mem_of_prod le_sup_left hMY le_sup_right (pCoreOf_isPGroup 2 L) hx
          ⟨y, hy, o, ho, rfl⟩
      have hLM : L ≤ Subgroup.normalizer ((Y ⊔ pCoreOf 2 L : Subgroup Ω) : Set Ω) := by
        refine burnsideC121_le_normalizer_of_conj fun l hl x hx => ?_
        have hx' : x ∈ ((Y ⊔ pCoreOf 2 L : Subgroup Ω) : Set Ω) := hx
        rw [Subgroup.coe_mul_of_right_le_normalizer_left Y _ hOY] at hx'
        obtain ⟨y, hy, o, ho, rfl⟩ := hx'
        have e : l * (y * o) * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y * (l * o * l⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (hc y hy l hl))
          (Subgroup.mem_sup_left hy)) (Subgroup.mem_sup_right
            ((Subgroup.mem_normalizer_iff.1 (hLO hl) o).1 ho))
      have hLY : L ≤ Subgroup.normalizer (Y : Set Ω) := by
        have := hLM.trans (normalizer_le_normalizer_oTwoUpper _)
        rwa [← hYM] at this
      have hU : IsElemAbelian 2 (blockU Y) :=
        ⟨⟨⟨fun a b => Subtype.ext (C1.blockU_comm hYs _ a.2 _ (C1.blockU_le_blockQ hYs b.2))⟩⟩,
          fun x hx => hYs.2.2.1.2 x hx⟩
      have hZU : blockZ Y ≤ blockU Y := inf_le_left
      have hcard : Nat.card (blockU Y) ≤ 4 * Nat.card (blockZ Y) := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv,
          C126.A5.card_evenWeight_three, hβk,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h1
        exact h1.le
      have hsec := burnsideC121_perfect_centralizes_section hU hZU
        (fun l hl => C1.mem_normalizer_blockU (hLY hl))
        (fun l hl => C1.mem_normalizer_blockZ (hLY hl)) hperf hcard
      have hle : blockU Y ≤ blockZ Y := by
        rw [← C1.commutator_blockU hYs, Subgroup.commutator_le]
        intro u hu y hy
        have h1 := Subgroup.inv_mem _ (hsec y (hYL hy) u hu)
        have e : u * y * u⁻¹ * y⁻¹ = (y * u * y⁻¹ * u⁻¹)⁻¹ := by group
        rw [commutatorElement_def, e]
        exact h1
      exact hYs.2.2.2.2.1.ne' (le_antisymm hle hYs.2.2.2.2.1.le)

namespace burnsideC121_YCtx

variable {Ω : Type} [Group Ω] [Finite Ω] {X R T Y W L : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W)

include c

theorem Y_le_L (hLX : L = oTwoUpper X) : Y ≤ L :=
  calc Y = oTwoUpper Y := c.hY.perf
    _ ≤ oTwoUpper X := oTwoUpper_mono c.hY.le
    _ = L := hLX.symm

theorem pow_mem_Y : ∀ g ∈ burnsideC121_H X T Y, ∃ k : ℕ, g ^ 2 ^ k ∈ Y := by
  intro g hg
  obtain ⟨y, hy, p, hp, rfl⟩ := c.H_prod g hg
  exact C124.exists_pow_mem_of_prod c.Y_le_H c.H_le_normalizer c.P_le_H c.P_pGroup hg
    ⟨y, hy, p, hp, rfl⟩

theorem Q_le_pCore_H : pCoreOf 2 X ≤ pCoreOf 2 (burnsideC121_H X T Y) :=
  C1.le_pCoreOf_of_normalized (c.Q_le_P.trans c.P_le_H)
    (c.H_le_X.trans (le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)

theorem blockU_le_omega (hYs : IsShort2 Y) : blockU Y ≤ omegaOneCenterOf (pCoreOf 2 X) := by
  have hC := C1.inf_centralizer_blockU_eq hYs c.Y_le_H c.H_le_normalizer c.pow_mem_Y
  have hQC : pCoreOf 2 X ≤ Subgroup.centralizer (blockU Y : Set Ω) := by
    have := c.Q_le_pCore_H
    rw [← hC] at this
    exact fun q hq => (this hq).2
  have hX := c.charTwo
  unfold CharTwo at hX
  intro u hu
  have huY : u ∈ Y := ((C1.blockU_le_blockQ hYs).trans (C1.blockQ_le Y)) hu
  have huC : u ∈ Subgroup.centralizer (pCoreOf 2 X : Set Ω) :=
    Subgroup.mem_centralizer_iff.2 fun q hq => (Subgroup.mem_centralizer_iff.1 (hQC hq) u hu).symm
  have huQ : u ∈ pCoreOf 2 X := hX ⟨c.hY.le huY, huC⟩
  exact Subgroup.subset_closure ⟨⟨huQ, huC⟩, C1.blockU_sq hYs u hu⟩

theorem commutator_Q_le_blockU : ⁅pCoreOf 2 X, Y⁆ ≤ blockU Y := by
  have hYQ : Y ≤ Subgroup.normalizer (pCoreOf 2 X : Set Ω) :=
    c.hY.le.trans (le_normalizer_pCoreOf 2 X)
  have h1 : ⁅pCoreOf 2 X, Y⁆ ≤ pCoreOf 2 Y :=
    C1.le_pCoreOf_of_normalized
      (Subgroup.le_normalizer_iff_commutator_le_right.mp c.Q_le_normalizer)
      (Subgroup.normalizer_commutator_ge_right _ Y)
      ((pCoreOf_isPGroup 2 X).to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hYQ))
  rw [← CFSG.CGT.PushingUpLit.SixThree.commutator_commutator_eq c.noTwoQuotient
    (pCoreOf_isPGroup 2 X) hYQ]
  exact Subgroup.commutator_mono h1 le_rfl

theorem reduction (hLX : L = oTwoUpper X) (hLc : L ∈ cComp X)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hblk : IsL2OrA3Block Y Y)
    (hJ : ⁅Y, thompsonJ R⁆ = Y) :
    IsShort2 L ∧ ∃ hU : IsElemAbelian 2 (blockU L), IsFFInt (L ⊔ baum T) (blockU L) hU := by
  have hYs : IsShort2 Y := hblk.1.1
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  have hYL : Y ≤ L := c.Y_le_L hLX
  have hLXle : L ≤ X := burnsideC121_L_le_X hLX
  have hXNL : X ≤ Subgroup.normalizer (L : Set Ω) := burnsideC121_X_le_normalizer_L hLX
  have hOLQ : pCoreOf 2 L ≤ pCoreOf 2 X := burnsideC121_pCore_L_le hLX
  have hQLO : pCoreOf 2 X ⊓ L ≤ pCoreOf 2 L := burnsideC121_Q_inf_L_le hLX
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 X : Set Ω) :=
    hLXle.trans (le_normalizer_pCoreOf 2 X)
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set Ω) := le_normalizer_pCoreOf 2 L
  have hgen : ∀ N : Subgroup Ω, N ≤ L → L ≤ Subgroup.normalizer (N : Set Ω) → Y ≤ N → N = L :=
    fun N h1 h2 h3 => burnsideC121_eq_of_block hLX hLq hperf hYL (hOLQ.trans c.Q_le_normalizer)
      c.hY.perf hblk h1 h2 h3
  have hWQel : IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 X)) :=
    B2F.isElemAbelian_omegaOneCenterOf _
  have hWQQ : omegaOneCenterOf (pCoreOf 2 X) ≤ pCoreOf 2 X := C1GN.omegaOneCenterOf_le_self _
  have hWQC : omegaOneCenterOf (pCoreOf 2 X) ≤ Subgroup.centralizer (pCoreOf 2 X : Set Ω) :=
    (C1GN.omegaOneCenterOf_le_centerOf _).trans inf_le_right
  have hLWQ : L ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 X) : Set Ω) :=
    fun l hl => normalizer_le_normalizer_omegaOneCenterOf _ (hLQ hl)
  have hUYW : blockU Y ≤ omegaOneCenterOf (pCoreOf 2 X) := c.blockU_le_omega hYs
  have hQY : ⁅pCoreOf 2 X, Y⁆ ≤ blockU Y := c.commutator_Q_le_blockU
  have hQL : ⁅pCoreOf 2 X, L⁆ ≤ omegaOneCenterOf (pCoreOf 2 X) :=
    burnsideC121_commutator_le_of_gen hLQ hLWQ hgen hYL (hQY.trans hUYW)
  have hULO : blockU L ≤ pCoreOf 2 L := Subgroup.le_normalizer_iff_commutator_le_left.mp hLO
  have hULW : blockU L ≤ omegaOneCenterOf (pCoreOf 2 X) :=
    (Subgroup.commutator_mono hOLQ le_rfl).trans hQL
  have hUL : IsElemAbelian 2 (blockU L) := B2F.isElemAbelian_mono hULW hWQel
  have hUYO : blockU Y ≤ pCoreOf 2 L := fun u hu => hQLO ⟨hWQQ (hUYW hu),
    hYL (((C1.blockU_le_blockQ hYs).trans (C1.blockQ_le Y)) hu)⟩
  have hUYUL : blockU Y ≤ blockU L := by
    rw [← C1.commutator_blockU hYs]
    exact Subgroup.commutator_mono hUYO hYL
  have hUYne : blockU Y ≠ ⊥ := fun h => by
    have := hYs.2.2.2.2.1
    rw [h] at this
    exact not_lt_bot this
  have hYnc : ∀ V : Subgroup Ω, blockU Y ≤ V → ¬ Y ≤ Subgroup.centralizer (V : Set Ω) := by
    intro V hV hYV
    apply hUYne
    rw [← C1.commutator_blockU hYs, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.1 (hYV.trans (Subgroup.centralizer_le hV))
  have hshort : IsShort2 L := by
    refine ⟨?_, A4.charTwo_of_normal hLXle hXNL c.charTwo,
      ⟨fun u hu => ⟨hULO hu, Subgroup.centralizer_le hOLQ (hWQC (hULW hu))⟩,
        fun x hx => hWQel.2 x (hULW hx)⟩, Or.inl hLq, ?_, ?_⟩
    · intro N _ h2
      haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
      haveI : Group.IsNilpotent (↥L ⧸ N) := h2.isNilpotent
      rw [eq_top_iff]
      intro a _
      exact (QuotientGroup.eq_one_iff a).1
        (burnsideC121_hom_trivial_of_perfect (QuotientGroup.mk' N) a)
    ·
      have hZL : blockZ L ≤ blockU L := inf_le_left
      refine lt_of_le_of_ne hZL fun h => ?_
      have hUC : blockU L ≤ Subgroup.centralizer (L : Set Ω) := by
        rw [← h]; exact inf_le_right
      exact hYnc (blockU L) hUYUL (hYL.trans (Subgroup.le_centralizer_iff.1 hUC))
    ·
      intro W' hZW hWU hLW
      have hYW : Y ≤ Subgroup.normalizer (W' : Set Ω) := hYL.trans hLW
      have hW'Q : W' ≤ pCoreOf 2 X := (hWU.trans hULW).trans hWQQ
      have hW'el : IsElemAbelian 2 W' := B2F.isElemAbelian_mono (hWU.trans hULW) hWQel
      have hUYel : IsElemAbelian 2 (blockU Y) := B2F.isElemAbelian_mono hUYW hWQel
      have hZYU : blockZ Y ≤ blockU Y := inf_le_left
      have hYUY : Y ≤ Subgroup.normalizer (blockU Y : Set Ω) := C1.le_normalizer_blockU Y
      have hYZY : Y ≤ Subgroup.normalizer (blockZ Y : Set Ω) := fun y hy =>
        C1.mem_normalizer_blockZ (Subgroup.le_normalizer hy)
      have hZN : blockZ Y ≤ Subgroup.normalizer ((W' ⊓ blockU Y : Subgroup Ω) : Set Ω) := by
        intro z hz
        refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => ?_)
        exact B2F.isElemAbelian_comm hUYel hg.2 hz.1
      have hYW'' : Y ≤ Subgroup.normalizer
          (((W' ⊓ blockU Y) ⊔ blockZ Y : Subgroup Ω) : Set Ω) := fun y hy =>
        C1.mem_normalizer_sup (Subgroup.inf_normalizer_le_normalizer_inf ⟨hYW hy, hYUY hy⟩)
          (hYZY hy)
      rcases hYs.2.2.2.2.2 ((W' ⊓ blockU Y) ⊔ blockZ Y) le_sup_right
          (sup_le inf_le_right hZYU) hYW'' with h | h
      ·
        left
        have hW'Y : ⁅W', Y⁆ ≤ blockZ Y := by
          have h1 : ⁅W', Y⁆ ≤ W' ⊓ blockU Y :=
            le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hYW)
              ((Subgroup.commutator_mono hW'Q le_rfl).trans hQY)
          rw [← h]
          exact h1.trans le_sup_left
        have hbot : ⁅⁅W', Y⁆, Y⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          exact hW'Y.trans inf_le_right
        rw [CFSG.CGT.PushingUpLit.SixThree.commutator_commutator_eq c.noTwoQuotient
          (B2F.isPGroup_of_isElemAbelian hW'el) hYW] at hbot
        have hYC : Y ≤ Subgroup.centralizer (W' : Set Ω) :=
          Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot)
        have hLC := hgen (L ⊓ Subgroup.centralizer (W' : Set Ω)) inf_le_left
          (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf
            ⟨Subgroup.le_normalizer hl, B2F.normalizer_le_normalizer_centralizer W' (hLW hl)⟩)
          (le_inf hYL hYC)
        have hLC' : L ≤ Subgroup.centralizer (W' : Set Ω) := by
          rw [← hLC]; exact inf_le_right
        exact le_antisymm (le_inf hWU (Subgroup.le_centralizer_iff.1 hLC')) hZW
      ·
        right
        have hUYW' : blockU Y ≤ W' := by
          rw [← C1.commutator_blockU hYs, Subgroup.commutator_le]
          intro u hu y hy
          have hu' : u ∈ (((W' ⊓ blockU Y) ⊔ blockZ Y : Subgroup Ω) : Set Ω) := by
            rw [h]; exact hu
          rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN] at hu'
          obtain ⟨w, hw, z, hz, rfl⟩ := hu'
          have hzy : z * y * z⁻¹ = y := by
            rw [← Subgroup.mem_centralizer_iff.1 hz.2 y hy, mul_inv_cancel_right]
          have e1 : ⁅w * z, y⁆ = w * (y * w⁻¹ * y⁻¹) := by
            rw [commutatorElement_def]
            calc w * z * y * (w * z)⁻¹ * y⁻¹ = w * (z * y * z⁻¹) * w⁻¹ * y⁻¹ := by group
              _ = w * (y * w⁻¹ * y⁻¹) := by rw [hzy]; group
          rw [e1]
          exact W'.mul_mem hw.1 ((Subgroup.mem_normalizer_iff.1 (hYW hy) w⁻¹).1 (W'.inv_mem hw.1))
        have hQW' : ⁅pCoreOf 2 X, L⁆ ≤ W' :=
          burnsideC121_commutator_le_of_gen hLQ hLW hgen hYL (hQY.trans hUYW')
        exact le_antisymm hWU ((Subgroup.commutator_mono hOLQ le_rfl).trans hQW')
  refine ⟨hshort, hUL, ?_⟩
  have hex : ∃ A : Subgroup Ω, IsMaxElemAbelian R A ∧
      ¬ A ≤ Subgroup.centralizer (blockU L : Set Ω) := by
    by_contra hcon
    push Not at hcon
    have hJC : thompsonJ R ≤ Subgroup.centralizer (blockU L : Set Ω) := by
      unfold thompsonJ
      exact iSup₂_le fun A hA => hcon A hA
    have hJY : thompsonJ R ≤ Subgroup.centralizer (blockU Y : Set Ω) :=
      hJC.trans (Subgroup.centralizer_le hUYUL)
    apply hUYne
    have h1 : ⁅⁅thompsonJ R, blockU Y⁆, Y⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2 hJY, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅blockU Y, Y⁆, thompsonJ R⁆ = ⊥ := by
      rw [C1.commutator_blockU hYs, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.1 hJY
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hJ, Subgroup.commutator_comm, C1.commutator_blockU hYs] at h3
    exact h3
  obtain ⟨A, hA, hA1⟩ := hex
  have hAJ : A ≤ thompsonJ R := by
    unfold thompsonJ
    exact le_iSup₂ (f := fun (B : Subgroup Ω) (_ : IsMaxElemAbelian R B) => B) A hA
  exact isFFModule_autOn hUL (hULW.trans (hWQQ.trans c.QR))
    (sup_le (C1.le_normalizer_blockU L) fun s hs =>
      C1.mem_normalizer_blockU (hXNL (c.RX (c.SR hs))))
    (hAJ.trans (c.thompsonJ_R_le_S.trans le_sup_right)) hA hA1

end burnsideC121_YCtx

end CFSG.ASVolI

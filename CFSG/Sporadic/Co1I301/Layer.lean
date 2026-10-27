module

public import CFSG.Sporadic.Co1I301.RZero
public import CFSG.Sporadic.Co1I301.Orbit
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301LayerQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301U42

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1I301

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1I301.Native
  CFSG.Sporadic.Co1.Module CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301 CFSG.LocalAnalysis.GLTheoremA.H301B
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.HardMathSupport.Dickson.I271.U42Presentation CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint (NativeSporadic.Co1)
open scoped commutatorElement

section Words

theorem nrep_relRows {x y : NativeSporadic.Co1}
    {X Y Xi Yi : Native.Rows} (hx : NRep X x) (hy : NRep Y y) (hxi : NRep Xi x⁻¹)
    (hyi : NRep Yi y⁻¹) (w : List (Fin 2 × Bool)) :
    NRep (relRows X Y Xi Yi w) (evalW ![x, y] w) := by
  have key : ∀ (w : List (Fin 2 × Bool)) (acc : Native.Rows) (a : NativeSporadic.Co1),
      NRep acc a → NRep (w.foldl (fun acc l => Native.mul acc (if l.1 = 0 then
        (if l.2 then X else Xi) else (if l.2 then Y else Yi))) acc) (a * evalW ![x, y] w) := by
    intro w
    induction w with
    | nil => intro acc a h; simpa [evalW_nil] using h
    | cons l w ih =>
      intro acc a h
      rw [List.foldl_cons, evalW_cons, ← mul_assoc]
      refine ih _ _ (h.mul ?_)
      obtain ⟨i, b⟩ := l
      fin_cases i <;> cases b <;> simpa
  simpa [relRows] using key w Native.one 1 NRep.one'

theorem evalW_map {G H : Type*} [Group G] [Group H] (f : G →* H) {m : ℕ} (g : Fin m → G)
    (w : List (Fin m × Bool)) : evalW (fun i => f (g i)) w = f (evalW g w) := by
  induction w with
  | nil => simp [evalW_nil]
  | cons l w ih =>
    rw [evalW_cons, evalW_cons, ih, map_mul]
    cases l.2 <;> simp

end Words


noncomputable abbrev XC : Subgroup NativeSporadic.Co1 :=
  centralizer ({dC} : Set NativeSporadic.Co1) ⊓ centralizer ({aNC} : Set NativeSporadic.Co1)

theorem mem_XC_iff {x : NativeSporadic.Co1} : x ∈ XC ↔ x * dC = dC * x ∧ x * aNC = aNC * x := by
  rw [Subgroup.mem_inf, @mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance dC x,
    @mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC x]

theorem dC_mem_XC : dC ∈ XC := mem_XC_iff.2 ⟨rfl, dC_comm_aNC⟩

theorem k1C_mem_XC : k1C ∈ XC := mem_XC_iff.2 ⟨k_comm.1, k_comm.2.1⟩

theorem k2C_mem_XC : k2C ∈ XC := mem_XC_iff.2 ⟨k_comm.2.2.1, k_comm.2.2.2⟩

theorem co1R_le_centralizer : co1R ≤ centralizer ({aNC} : Set NativeSporadic.Co1) :=
  Subgroup.map_subtype_le _

theorem rowR0_le_XC : rowR0Of dC co1R ≤ XC := fun _ hx =>
  Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, co1R_le_centralizer (Subgroup.mem_inf.1 hx).1⟩

theorem conj_mem_rowR0 {g n : NativeSporadic.Co1} (hg : g ∈ XC) (hn : n ∈ rowR0Of dC co1R) :
    g * n * g⁻¹ ∈ rowR0Of dC co1R := by
  obtain ⟨hnR, hnd⟩ := Subgroup.mem_inf.1 hn
  obtain ⟨hgd, hga⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hgd hnd)
    (Subgroup.inv_mem _ hgd)⟩
  obtain ⟨m, hm, rfl⟩ := hnR
  have h := twoAQC_normal.conj_mem m hm ⟨g, hga⟩
  exact ⟨_, h, rfl⟩

noncomputable abbrev NX : Subgroup ↥XC := (rowR0Of dC co1R).subgroupOf XC

instance NX_normal : NX.Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_rowR0 g.2 hn
    simpa using this⟩

theorem card_NX : Nat.card NX = 2 ^ 7 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe rowR0_le_XC).toEquiv, card_rowR0]

noncomputable abbrev piX : ↥XC →* ↥XC ⧸ NX := QuotientGroup.mk' NX

noncomputable abbrev dX : ↥XC := ⟨dC, dC_mem_XC⟩

noncomputable abbrev k1X : ↥XC := ⟨k1C, k1C_mem_XC⟩

noncomputable abbrev k2X : ↥XC := ⟨k2C, k2C_mem_XC⟩

theorem piX_eq_one_iff (y : ↥XC) : piX y = 1 ↔ (y : NativeSporadic.Co1) ∈ rowR0Of dC co1R := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem chkK_parts :
    (∀ w ∈ u42Words, CFSG.Sporadic.Co1.InvNative.validRows
        (relRows (k1Rw ()) (k2Rw ()) (Native.inv (k1Rw ())) (Native.inv (k2Rw ())) w) = true ∧
      (r0Set ()).contains
        (relRows (k1Rw ()) (k2Rw ()) (Native.inv (k1Rw ())) (Native.inv (k2Rw ())) w) = true) ∧
    (r0Set ()).contains (k1Rw ()) = false ∧
    Native.mul (k1Rw ()) (Native.inv (k1Rw ())) = Native.one ∧
    Native.mul (k2Rw ()) (Native.inv (k2Rw ())) = Native.one := by
  have h := co1RowCheck_parts.2.2.2.2.2.1
  simp only [chkK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨fun w hw => h5 w hw, h6, h7, h8⟩

theorem rels_piX : ∀ w ∈ u42Words, evalW ![piX k1X, piX k2X] w = 1 := by
  intro w hw
  obtain ⟨hrel, -, hi1, hi2⟩ := chkK_parts
  have hg : (![piX k1X, piX k2X] : Fin 2 → ↥XC ⧸ NX) = fun i => piX (![k1X, k2X] i) := by
    funext i
    fin_cases i <;> rfl
  rw [hg, evalW_map, piX_eq_one_iff]
  have hcoe : ((evalW ![k1X, k2X] w : ↥XC) : NativeSporadic.Co1) = evalW ![k1C, k2C] w := by
    have h := evalW_map XC.subtype ![k1X, k2X] w
    have hg' : (fun i => XC.subtype (![k1X, k2X] i)) =
        (![k1C, k2C] : Fin 2 → NativeSporadic.Co1) := by
      funext i
      fin_cases i <;> rfl
    rw [hg'] at h
    exact h.symm
  rw [hcoe]
  have hrep := nrep_relRows nrep_k1C nrep_k2C (nrep_k1C.inv hi1) (nrep_k2C.inv hi2) w
  exact (mem_rowR0_iff hrep (hrel w hw).1).2 (hrel w hw).2

theorem piX_k1_ne_one : piX k1X ≠ 1 := by
  rw [Ne, piX_eq_one_iff]
  intro h
  have h1 := (mem_rowR0_iff nrep_k1C (cEl_valid (by norm_num) (by norm_num))).1 h
  rw [chkK_parts.2.1] at h1
  exact Bool.false_ne_true h1

noncomputable abbrev SX : Subgroup (↥XC ⧸ NX) := closure (Set.range ![piX k1X, piX k2X])

theorem nonempty_SX_equiv :
    Nonempty (↥SX ≃* ↥CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup) :=
  nonempty_mulEquiv_QP45_of_rels_ne_one ![piX k1X, piX k2X] rels_piX piX_k1_ne_one

theorem piX_dX_central (x : ↥XC ⧸ NX) : x * piX dX = piX dX * x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective NX x
  have h : y * dX = dX * y := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (mem_XC_iff.1 y.2).1)
  have h' := congrArg piX h
  rw [map_mul, map_mul] at h'
  exact h'

theorem piX_dX_pow_conj (m : ℕ) (x : ↥XC ⧸ NX) : piX dX ^ m * x * (piX dX ^ m)⁻¹ = x := by
  rw [← ((Commute.pow_right (piX_dX_central x) m).eq), mul_inv_cancel_right]

theorem piX_dX_pow_three : piX dX ^ 3 = 1 := by
  rw [← map_pow]
  have : dX ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact dC_pow_three)
  rw [this, map_one]

theorem piX_dX_ne_one : piX dX ≠ 1 := by
  rw [Ne, piX_eq_one_iff]
  intro h
  have h128 : (⟨dC, h⟩ : ↥(rowR0Of dC co1R)) ^ 128 = 1 := by
    rw [show (128 : ℕ) = Nat.card (rowR0Of dC co1R) by rw [card_rowR0]; norm_num]
    exact pow_card_eq_one'
  have h1 : dC ^ 128 = 1 := by
    have := congrArg Subtype.val h128
    simpa using this
  have h2 : dC ^ 128 = dC ^ 2 := by
    rw [show (128 : ℕ) = 3 * 42 + 2 by norm_num, pow_add, pow_mul, dC_pow_three, one_pow, one_mul]
  rw [h2] at h1
  have h3 := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_dC] at h3
  norm_num at h3

theorem orderOf_piX_dX : orderOf (piX dX) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime piX_dX_pow_three piX_dX_ne_one

theorem center_SX : Subgroup.center ↥SX = ⊥ := by
  obtain ⟨e⟩ := nonempty_SX_equiv
  haveI := CFSG.HardMathSupport.Dickson.I271.isSimpleGroup_of_equiv_QP45 e
  obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Dickson.I271.nonabelian_of_equiv_QP45 e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥SX) with h | h
  · exact h
  · exfalso
    have ha : a ∈ Subgroup.center ↥SX := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem pow_piX_dX_mem_SX {k : ℕ} (hk : piX dX ^ k ∈ SX) : piX dX ^ k = 1 := by
  have hc : (⟨piX dX ^ k, hk⟩ : ↥SX) ∈ Subgroup.center ↥SX := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact ((Commute.pow_right (show Commute (s : ↥XC ⧸ NX) (piX dX) from
      piX_dX_central s) k)).eq
  rw [center_SX, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

noncomputable def prodMap (p : Fin 3 × ↥SX) : ↥XC ⧸ NX := piX dX ^ (p.1 : ℕ) * (p.2 : ↥XC ⧸ NX)

theorem prodMap_injective : Function.Injective prodMap := by
  rintro ⟨k, s⟩ ⟨k', s'⟩ h
  simp only [prodMap] at h
  have key : ∀ (k k' : Fin 3) (s s' : ↥SX), (k : ℕ) ≤ k' →
      piX dX ^ (k : ℕ) * (s : ↥XC ⧸ NX) = piX dX ^ (k' : ℕ) * (s' : ↥XC ⧸ NX) →
        k = k' ∧ s = s' := by
    intro k k' s s' hkk h
    have hpow : piX dX ^ ((k' : ℕ) - k) = (s : ↥XC ⧸ NX) * (s' : ↥XC ⧸ NX)⁻¹ := by
      have e1 : piX dX ^ (k' : ℕ) = piX dX ^ (k : ℕ) * piX dX ^ ((k' : ℕ) - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hkk]
      rw [e1, mul_assoc] at h
      have h2 := mul_left_cancel h
      rw [h2, mul_inv_cancel_right]
    have hmem : piX dX ^ ((k' : ℕ) - k) ∈ SX := by
      rw [hpow]
      exact Subgroup.mul_mem _ s.2 (Subgroup.inv_mem _ s'.2)
    have h1 := pow_piX_dX_mem_SX hmem
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_piX_dX] at h3
    have hkk' : k = k' := by
      apply Fin.ext
      have hlt : (k' : ℕ) - k < 3 := by omega
      have := Nat.eq_zero_of_dvd_of_lt h3 hlt
      omega
    subst hkk'
    refine ⟨rfl, Subtype.ext (mul_left_cancel h)⟩
  rcases le_total (k : ℕ) k' with hle | hle
  · obtain ⟨h1, h2⟩ := key k k' s s' hle h
    rw [h1, h2]
  · obtain ⟨h1, h2⟩ := key k' k s' s hle h.symm
    rw [h1, h2]

theorem card_quot_le : Nat.card (↥XC ⧸ NX) ≤ 77760 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup NX
  rw [card_NX] at h1
  have h2 := card_centralizer_dC_inf_le
  have h3 : Nat.card ↥XC ≤ 9953280 := h2
  omega

theorem prodMap_surjective : Function.Surjective prodMap := by
  obtain ⟨e⟩ := nonempty_SX_equiv
  have hS : Nat.card ↥SX = 25920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.HardMathSupport.Dickson.I271.card_QP45_eq
  haveI : Finite (↥XC ⧸ NX) := Nat.finite_of_card_ne_zero (by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup NX
    intro h0
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this)
  refine (prodMap_injective.bijective_of_nat_card_le ?_).2
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hS]
  exact card_quot_le

theorem SX_conj_mem (g : ↥XC ⧸ NX) {s : ↥XC ⧸ NX} (hs : s ∈ SX) : g * s * g⁻¹ ∈ SX := by
  obtain ⟨⟨k, t⟩, rfl⟩ := prodMap_surjective g
  simp only [prodMap]
  have e : piX dX ^ (k : ℕ) * (t : ↥XC ⧸ NX) * s * (piX dX ^ (k : ℕ) * (t : ↥XC ⧸ NX))⁻¹ =
      piX dX ^ (k : ℕ) * ((t : ↥XC ⧸ NX) * s * (t : ↥XC ⧸ NX)⁻¹) * (piX dX ^ (k : ℕ))⁻¹ := by
    group
  rw [e, piX_dX_pow_conj]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ t.2 hs) (Subgroup.inv_mem _ t.2)

theorem commutator_le_SX : ⁅(⊤ : Subgroup (↥XC ⧸ NX)), (⊤ : Subgroup (↥XC ⧸ NX))⁆ ≤ SX := by
  rw [Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨⟨k, t⟩, rfl⟩ := prodMap_surjective g₁
  obtain ⟨⟨k', t'⟩, rfl⟩ := prodMap_surjective g₂
  simp only [prodMap]
  set z₁ := piX dX ^ (k : ℕ)
  set z₂ := piX dX ^ (k' : ℕ)
  set a : ↥XC ⧸ NX := (t : ↥XC ⧸ NX)
  set b : ↥XC ⧸ NX := (t' : ↥XC ⧸ NX)
  have hab : ⁅z₁ * a, z₂ * b⁆ = ⁅a, b⁆ := by
    have h2a : a * z₂ = z₂ * a := (Commute.pow_right (piX_dX_central a) (k' : ℕ)).eq
    calc ⁅z₁ * a, z₂ * b⁆ = z₁ * (a * (z₂ * b) * a⁻¹) * z₁⁻¹ * (z₂ * b)⁻¹ := by
          rw [commutatorElement_def]; group
      _ = a * (z₂ * b) * a⁻¹ * (z₂ * b)⁻¹ := by rw [piX_dX_pow_conj]
      _ = (a * z₂) * (b * a⁻¹ * b⁻¹) * z₂⁻¹ := by group
      _ = (z₂ * a) * (b * a⁻¹ * b⁻¹) * z₂⁻¹ := by rw [h2a]
      _ = z₂ * (a * b * a⁻¹ * b⁻¹) * z₂⁻¹ := by group
      _ = ⁅a, b⁆ := by rw [piX_dX_pow_conj, commutatorElement_def]
  rw [hab, commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ t.2 t'.2)
    (Subgroup.inv_mem _ t.2)) (Subgroup.inv_mem _ t'.2)

theorem nonempty_pQuot_layer_XC :
    Nonempty (PQuot 3 (GLAPLayer 3 XC) ≃*
      ↥CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup) := by
  obtain ⟨e⟩ := nonempty_SX_equiv
  haveI := CFSG.HardMathSupport.Dickson.I271.isSimpleGroup_of_equiv_QP45 e
  obtain ⟨e₁⟩ := nonempty_pQuot_glaPLayer_of_quotient Nat.prime_three NX
    (by rw [card_NX]; norm_num) SX inferInstance
    (CFSG.HardMathSupport.Dickson.I271.nonabelian_of_equiv_QP45 e)
    (CFSG.HardMathSupport.Dickson.I271.three_dvd_card_of_equiv_QP45 e) SX_conj_mem
    commutator_le_SX
  obtain ⟨e₂⟩ := nonempty_pQuot_glaPLayer_subtype Nat.prime_three XC
  exact ⟨(e₂.trans e₁).trans e⟩

theorem isTypeWithCenter_layer_XC : IsTypeWithCenter 3 (GLAPLayer 3 XC) isPSp43 1 := by
  obtain ⟨e⟩ := nonempty_pQuot_layer_XC
  haveI := CFSG.HardMathSupport.Dickson.I271.isSimpleGroup_of_equiv_QP45 e
  obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Dickson.I271.nonabelian_of_equiv_QP45 e
  have hZ : Subgroup.center (PQuot 3 (GLAPLayer 3 XC)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (PQuot 3 (GLAPLayer 3 XC))) with h | h
    · exact h
    · exfalso
      have ha : a ∈ Subgroup.center (PQuot 3 (GLAPLayer 3 XC)) := by rw [h]; trivial
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  let e' : PSimple 3 (GLAPLayer 3 XC) ≃*
      ↥CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  exact ⟨catalogIs_isPSp43_of_equiv_QP45 e', by rw [hZ, Subgroup.card_bot]⟩

end CFSG.Sporadic.Co1I301

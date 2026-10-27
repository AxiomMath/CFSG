module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318H
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318G

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T M L D : Subgroup G} {n k : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)}
  {Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)}

theorem card_Q_ge (hD : Data G T M L D n k α Φ) :
    8 ^ k * 8 ^ (n - 3) ≤ Nat.card ↥(c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) := by
  rw [← hD.card_inf_mul, ← hD.card_W₃]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le (le_inf hD.W₃_le_Q hD.W₃_le_pCoreOf))

theorem exists_modO2Surj_three (hD : Data G T M L D n k α Φ) :
    ∃ α₂ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})) →* ↥(StatedSL 3 (ZMod 2)),
      IsModO2Surj (liftCore α (flagStabilizer n (ZMod 2) {3})) α₂ := by
  obtain ⟨ψ, hψs, hψk, -⟩ := hD.exists_levi_three
  refine ⟨(specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom.comp ψ, ?_, ?_⟩
  · rw [MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hψs
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hψk]

theorem not_case1 (hD : Data G T M L D n k α Φ)
    (h1 : IsC134Case1 (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T) T
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) : False := by
  obtain ⟨-, nF, F, _, _, hFc, -, α', hα's, hα'k, β, hβs, hβk, -⟩ := h1
  obtain ⟨α₂, hα₂⟩ := hD.exists_modO2Surj_three
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ ⟨hα's, hα'k⟩)
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hcard : Nat.card ↥(c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) = 8 := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_eq_fintype_card, hF]
    simp
  have h := hD.card_Q_ge
  rw [hcard] at h
  have hk := hD.k1
  have hn := hD.n4
  have h1 : 8 ≤ 8 ^ k := Nat.le_self_pow (by omega) 8
  have h2 : 8 ≤ 8 ^ (n - 3) := Nat.le_self_pow (by omega) 8
  nlinarith

omit [Finite G] in
theorem mem_W₃_of {c : Fin k → Multiplicative (Fin n → ZMod 2)} (hn : 3 ≤ n)
    (hc : ∀ i (j : Fin n), 3 ≤ (j : ℕ) → Multiplicative.toAdd (c i) j = 0) :
    (Φ c : G) ∈ W₃ Φ := by
  obtain ⟨x, rfl⟩ := exists_ext3 hn hc
  exact ⟨x, rfl⟩

theorem mulVec_apply_of_rows {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hA : ∀ j t : Fin n, 3 ≤ (j : ℕ) → A j t = if j = t then 1 else 0) (v : Fin n → ZMod 2)
    {j : Fin n} (hj : 3 ≤ (j : ℕ)) : (A *ᵥ v) j = v j := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · rw [hA j j hj, ite_eq_left rfl, one_mul]
  · intro t _ htj
    rw [hA j t hj, ite_eq_right (Ne.symm htj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem comm_eq (hD : Data G T M L D n k α Φ) (l : ↥L)
    (c : Fin k → Multiplicative (Fin n → ZMod 2)) :
    (l : G) * (Φ c : G) * (l : G)⁻¹ * (Φ c : G)⁻¹ =
      (Φ (vecAct k ((α l : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) c * c⁻¹) : G) := by
  rw [hD.equiv, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem rows_of_mem (hD : Data G T M L D n k α Φ) {y : G}
    (hy : y ∈ liftCore α (flagStabilizer n (ZMod 2) {3})) (j t : Fin n) (hj : 3 ≤ (j : ℕ)) :
    ((α ⟨y, liftCore_le α _ hy⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) j t = if j = t then 1 else 0 := by
  have hP := mem_perfectCore_of_mem_liftCore hD.surj hy
  by_cases ht : 3 ≤ (t : ℕ)
  · exact br_eq_ite (Nat.card_zmod 2) hD.n4 hD.n5 hP hj ht
  · rw [bl_eq_zero (perfectCore_le _ hP) hj (by omega)]
    have : j ≠ t := fun e => by subst e; omega
    simp [this]

theorem comm_mem_W₃ (hD : Data G T M L D n k α Φ) (l : ↥L)
    (hl : ∀ j t : Fin n, 3 ≤ (j : ℕ) → ((α l : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) j t = if j = t then 1 else 0)
    (c : Fin k → Multiplicative (Fin n → ZMod 2)) :
    (l : G) * (Φ c : G) * (l : G)⁻¹ * (Φ c : G)⁻¹ ∈ W₃ Φ := by
  rw [hD.comm_eq]
  refine mem_W₃_of (by have := hD.n4; omega) fun i j hj => ?_
  have h := mulVec_apply_of_rows hl (Multiplicative.toAdd (c i)) hj
  rw [Pi.mul_apply, Pi.inv_apply, toAdd_mul, toAdd_inv, vecAct_apply, toAdd_ofAdd,
    Pi.add_apply, Pi.neg_apply, h, add_neg_cancel]

theorem exists_mem_Q (hD : Data G T M L D n k α Φ) {a b : Fin n} (ha : (a : ℕ) < 3)
    (hb : 3 ≤ (b : ℕ)) (hab : a ≠ b) :
    ∃ (q : G) (hqL : q ∈ L), q ∈ c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3})) ∧
      α ⟨q, hqL⟩ = SpecialLinearGroup.transvection hab (1 : ZMod 2) := by
  have hn := hD.n4
  obtain ⟨ψ, -, hψk, hψe⟩ := hD.exists_levi_three
  obtain ⟨c, hc3, hca⟩ : ∃ c : Fin n, (c : ℕ) < 3 ∧ c ≠ a := by
    by_cases ha0 : (a : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, by simp, fun e => by
        have := congrArg Fin.val e
        simp at this
        omega⟩
    · exact ⟨⟨0, by omega⟩, by simp, fun e => by
        have := congrArg Fin.val e
        simp at this
        omega⟩
  have hac : a ≠ c := hca.symm
  have hcb : c ≠ b := fun e => by
    have := congrArg Fin.val e
    omega
  obtain ⟨x, hxY, hxO, hxe⟩ := hD.exists_rad hψk hψe hc3 hb hcb
  have h3 : 0 + 3 ≤ n := by omega
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  have hmem : SpecialLinearGroup.transvection hac (1 : ZMod 2) ∈
      perfectCore (flagStabilizer n (ZMod 2) {3}) := by
    rw [transvection_eq_liftT h3 ha hc3 hac]
    exact Ln2.liftT_mem_perfectCore h3 le_rfl hno _
  obtain ⟨y, hyY, hye⟩ := exists_mem_liftCore hD.surj hmem
  have hq : ⁅y, x⁆ ∈ c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3})) := by
    rw [c134Q, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hyY hxO
  have hqL : ⁅y, x⁆ ∈ L := L.mul_mem (L.mul_mem (L.mul_mem (liftCore_le α _ hyY)
    (liftCore_le α _ hxY)) (L.inv_mem (liftCore_le α _ hyY))) (L.inv_mem (liftCore_le α _ hxY))
  refine ⟨⁅y, x⁆, hqL, hq, ?_⟩
  have : (⟨⁅y, x⁆, hqL⟩ : ↥L) = ⁅(⟨y, liftCore_le α _ hyY⟩ : ↥L), ⟨x, liftCore_le α _ hxY⟩⁆ :=
    rfl
  rw [this, map_commutatorElement, hye, hxe,
    Matrix.SpecialLinearGroup.commutatorElement_transvection hac hcb hab, mul_one]

theorem case2 (hD : Data G T M L D n k α Φ)
    (h2 : IsC134Case2 (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T) T
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) :
    k = 1 ∧ n = 4 ∧ c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3})) ⊓ pCoreOf 2 L = W₃ Φ := by
  obtain ⟨⟨nF, F, _, _, α', hFc, hα', -, -, β, hβs, hβk, -⟩, -⟩ := h2
  obtain ⟨α₂, hα₂⟩ := hD.exists_modO2Surj_three
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα')
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hcard : Nat.card ↥(c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) = 64 := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have h1 := hD.card_inf_mul
  rw [hcard] at h1
  have hW := Subgroup.card_le_of_le (le_inf hD.W₃_le_Q hD.W₃_le_pCoreOf)
  rw [hD.card_W₃] at hW
  have hk := hD.k1
  have hn4 := hD.n4
  have hn5 := hD.n5
  have h8 : 8 ≤ 8 ^ k := Nat.le_self_pow (by omega) 8
  have hn : n = 4 := by
    rcases (by omega : n = 4 ∨ n = 5) with h | h
    · exact h
    · exfalso
      subst h
      have e : (8 : ℕ) ^ (5 - 3) = 64 := by norm_num
      rw [e] at h1
      omega
  subst hn
  have e : (8 : ℕ) ^ (4 - 3) = 8 := by norm_num
  rw [e] at h1
  have hk1 : k = 1 := by
    by_contra hk1
    have h64 : 64 ≤ 8 ^ k := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ 8 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hk1
  refine ⟨rfl, rfl, (Subgroup.eq_of_le_of_card_ge (le_inf hD.W₃_le_Q hD.W₃_le_pCoreOf) ?_).symm⟩
  rw [hD.card_W₃]
  omega

theorem not_case3 (hD : Data G T M L D n k α Φ)
    (h3 : IsC134Case3 (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T) T
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) : False := by
  classical
  have hn := hD.n4
  have hk := hD.k1
  have hZ8 : Nat.card ↥(centerOf (c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3})))) = 8 := by
    obtain ⟨⟨nF, F, _, _, α', hFc, hα', ⟨-, -, β, hβs, hβk, -⟩, -⟩, -⟩ := h3
    obtain ⟨α₂, hα₂⟩ := hD.exists_modO2Surj_three
    have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα')
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have hWZ : W₃ Φ = centerOf (c134Q (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) := by
    refine Subgroup.eq_of_le_of_card_ge hD.W₃_le_centerOf ?_
    rw [hZ8, hD.card_W₃]
    exact Nat.le_self_pow (by omega) 8
  set e₃ : Fin n → ZMod 2 := Pi.single ⟨3, by omega⟩ 1 with he₃
  set c₃ : Fin k → Multiplicative (Fin n → ZMod 2) :=
    Pi.mulSingle ⟨0, hk⟩ (Multiplicative.ofAdd e₃) with hc₃
  set v : G := (Φ c₃ : G) with hv
  have hab := (Hyp331.vPlus_reduced hD.hyp.toSetup331).2.1
  have hcommV : ∀ a ∈ vPlus L T, ∀ b ∈ vPlus L T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWV : W₃ Φ ≤ vPlus L T := by
    rintro _ ⟨x, rfl⟩
    exact (Φ _).2
  have hcomm := MSY.comm_eq_one_of_case3 h3 (v := v)
    (fun q hq => by
      rw [← hWZ]
      have hqY : q ∈ liftCore α (flagStabilizer n (ZMod 2) {3}) :=
        CFSG.LieType.BorelTits.pCoreOf_le 2 _ (hD.Q_le_pCoreOf hq)
      exact hD.comm_mem_W₃ ⟨q, liftCore_le α _ hqY⟩ (hD.rows_of_mem hqY) c₃)
    (fun z hz => by
      rw [← hWZ] at hz
      exact hcommV z (hWV hz) v (Φ c₃).2)
    (fun y hy q hq => by
      have hy' : y⁻¹ ∈ liftCore α (flagStabilizer n (ZMod 2) {3}) :=
        (liftCore α _).inv_mem hy
      have h1 := hD.comm_mem_W₃ ⟨y⁻¹, liftCore_le α _ hy'⟩ (hD.rows_of_mem hy') c₃
      simp only [inv_inv] at h1
      have hw : y⁻¹ * v * y * v⁻¹ ∈ W₃ Φ := h1
      have hwv : (y⁻¹ * v * y * v⁻¹) * v = v * (y⁻¹ * v * y * v⁻¹) :=
        hcommV _ (hWV hw) v (Φ c₃).2
      have hu : v⁻¹ * y⁻¹ * v * y ∈ W₃ Φ := by
        have : v⁻¹ * y⁻¹ * v * y = v⁻¹ * ((y⁻¹ * v * y * v⁻¹) * v) := by group
        rw [this, hwv, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hw
      rw [hWZ] at hu
      exact (Subgroup.mem_centralizer_iff.mp hu.2 q hq).symm)
  obtain ⟨q, hqL, hq, hqe⟩ := hD.exists_mem_Q (a := ⟨0, by omega⟩) (b := ⟨3, by omega⟩)
    (by simp) (by simp) (fun e => by
      have := congrArg Fin.val e
      simp at this)
  have h1 : q * v * q⁻¹ = v := by rw [hcomm q hq, mul_inv_cancel_right]
  have h2 := (hD.comm_iff ⟨q, hqL⟩ c₃).mp h1 ⟨0, hk⟩
  rw [hqe, hc₃, Pi.mulSingle_eq_same, toAdd_ofAdd] at h2
  have h3 := SpecialLinearGroup.transvection_smul_single_snd (F := ZMod 2)
    (i := (⟨0, by omega⟩ : Fin n)) (j := ⟨3, by omega⟩) (fun e => by
      have := congrArg Fin.val e
      simp at this) 1
  rw [Matrix.SpecialLinearGroup.smul_def, one_smul] at h3
  have h3' : ((SpecialLinearGroup.transvection (i := (⟨0, by omega⟩ : Fin n))
      (j := ⟨3, by omega⟩) (fun e => by
        have := congrArg Fin.val e
        simp at this) (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e₃ = e₃ + Pi.single ⟨0, by omega⟩ 1 := h3
  rw [h3'] at h2
  have h4 := congrFun h2 ⟨0, by omega⟩
  simp at h4

theorem not_case5
    (hD : Data G T M L D n k α Φ) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h5 : IsC134Case5 (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T) T
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) : False := by
  have hT : IsSylowTwoOf T (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hD.hyp.sylow le_sup_right
  have hY₂ := MSY.le_centralizer_of_case5 h5 hT
  have hLT : L ⊔ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [hD.sup_eq]
    exact sup_le (sup_le hD.le_centralizer hY₂)
      (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T)
  refine MS3323.false_of_le_center hD.hyp h38 h39 hD.TL ?_
  rw [omegaOneCenterOf_eq]
  refine le_inf ((B2F.omegaOneCenter_le_inf_centralizer T).trans (inf_le_left.trans
    le_sup_right)) ?_
  rw [← Subgroup.le_centralizer_iff]
  exact hLT

end Data

end CFSG.Quasithin.H13.L3318

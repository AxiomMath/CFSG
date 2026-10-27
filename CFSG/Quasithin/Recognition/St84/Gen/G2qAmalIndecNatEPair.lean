module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecNatECoord

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

namespace G2qNatEConf

variable {L1 L2 S Q1 Q2 Z1 Z2 W E : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {α₁ : ↥L1 →* SL(2, F₁)} {α₂ : ↥L2 →* SL(2, F₂)} {vE : G → Fin 2 → F₁}
  {nv zv : G → Fin 2 → F₂}

theorem nv_apply_one_of_mem_E (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    (hEQ : E ≤ Q2) {e : G} (he : e ∈ E) : nv e 1 = 0 :=
  hC.split.natW.apply_one_eq_zero_of_commutator_mem hC.split.surj hC.memS_right (hEQ he)
    fun s hs => hC.split.center_le ((hC.mem_center_right_iff
      (hC.natE.commutator_left_mem ⟨(s : G), hC.le_left hs⟩ he)).mpr
      (hC.natE.map_commutator_left_apply_one ((hC.memS_left ⟨(s : G), hC.le_left hs⟩).mp hs) he))

theorem nv_apply_one_of_mem_Y (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    {y : G} (hy : y ∈ ⁅Q2, L2⁆ ⊓ Q1) : nv y 1 = 0 :=
  hC.split.natW.apply_one_eq_zero_of_commutator_mem hC.split.surj hC.memS_right
    (hC.split.commutator_le_Q (Subgroup.mem_inf.mp hy).1)
    fun s hs => hC.split.center_le (hC.le_center (hC.YS s hs y hy))

theorem mem_center_of_mem_E_of_mem_R (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    {e : G} (he : e ∈ E) (heR : e ∈ ⁅Q2, L2⁆) : e ∈ Z2 :=
  (hC.mem_center_right_iff he).mpr (hC.natE.apply_one_eq_zero_of_commutator_mem hC.surj_left
    hC.memS_left he fun s hs => hC.YS s hs e (Subgroup.mem_inf.mpr ⟨heR, hC.E_le he⟩))

theorem exists_mem_Y_inv_mul_mem_W (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    {x : G} (hxQ : x ∈ Q2) (hx1 : x ∈ Q1) : ∃ r ∈ ⁅Q2, L2⁆ ⊓ Q1, r⁻¹ * x ∈ W := by
  obtain ⟨r, hrR, hrQ, hrv⟩ := hC.split.natW.exists_mem_commutator hC.split.surj (nv x)
  have hw : r⁻¹ * x ∈ W := hC.split.natW.inv_mul_mem hrQ hxQ hrv
  refine ⟨r, Subgroup.mem_inf.mpr ⟨hrR, ?_⟩, hw⟩
  rw [show r = x * (r⁻¹ * x)⁻¹ by group]
  exact mul_mem hx1 (inv_mem (hC.W_le_left hw))

theorem exists_mem_Y_nv_eq (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    {y₀ : G} (hy₀ : y₀ ∈ ⁅Q2, L2⁆ ⊓ Q1) (h0 : nv y₀ 0 ≠ 0) (t : F₂) :
    ∃ y ∈ ⁅Q2, L2⁆ ⊓ Q1, nv y = ![t, 0] := by
  by_cases ht : t = 0
  · refine ⟨1, one_mem _, ?_⟩
    rw [hC.split.natW.map_one, ht]
    funext i
    fin_cases i <;> rfl
  have hy₀R := (Subgroup.mem_inf.mp hy₀).1
  have hy₀Q := hC.split.commutator_le_Q hy₀R
  obtain ⟨l, hl⟩ := hC.split.surj (torusElt (Units.mk0 (t / nv y₀ 0) (div_ne_zero ht h0)))
  have hlB : α₂ l ∈ borel F₂ := by rw [hl]; exact torusElt_mem_borel _
  refine ⟨(l : G) * y₀ * (l : G)⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact G2qSplitData.conj_mem_commutator_of_conj_mem (fun a ha => hC.split.conj_mem_Q l.2 ha)
      (fun m hm => mul_mem (mul_mem l.2 hm) (inv_mem l.2)) hy₀R
  · exact (Subgroup.mem_normalizer_iff.mp (hC.borel_right l hlB) y₀).mp
      (Subgroup.mem_inf.mp hy₀).2
  · rw [hC.split.natW.conj l y₀ hy₀Q, hl]
    funext i
    fin_cases i
    · simp [natE_torusElt_mulVec_zero, h0]
    · simp [natE_torusElt_mulVec_one, hC.nv_apply_one_of_mem_Y hy₀]

theorem exists_mem_Y_of_mem_E (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    (hEQ : E ≤ Q2) {e₀ : G} (he₀ : e₀ ∈ E) (h0 : nv e₀ 0 ≠ 0) (t : F₂) :
    ∃ y ∈ ⁅Q2, L2⁆ ⊓ Q1, nv y = ![t, 0] := by
  obtain ⟨r, hr, hw⟩ := hC.exists_mem_Y_inv_mul_mem_W (hEQ he₀) (hC.E_le he₀)
  have hrQ := hC.split.commutator_le_Q (Subgroup.mem_inf.mp hr).1
  have hrv : nv r = nv e₀ := by
    have h := hC.split.natW.map_inv_mul hrQ (hEQ he₀)
    rw [(hC.split.natW.eq_zero_iff _ (mul_mem (inv_mem hrQ) (hEQ he₀))).mpr hw] at h
    exact (sub_eq_zero.mp h.symm).symm
  exact hC.exists_mem_Y_nv_eq hr (by rw [hrv]; exact h0) t

theorem exists_pair_E (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    (hEQ : E ≤ Q2) {e : G} (he : e ∈ E) :
    ∃ s : F₂, (∀ y ∈ ⁅Q2, L2⁆ ⊓ Q1, zv ⁅e, y⁆ = s • nv y) ∧ (s = 0 → e ∈ Z2) := by
  obtain ⟨r, hr, hw⟩ := hC.exists_mem_Y_inv_mul_mem_W (hEQ he) (hC.E_le he)
  have hrR := (Subgroup.mem_inf.mp hr).1
  have hrQ := hC.split.commutator_le_Q hrR
  obtain ⟨s, hs⟩ := hC.split.exists_pair hw
  refine ⟨s, fun y hy => ?_, fun hs0 => ?_⟩
  · have hyR := (Subgroup.mem_inf.mp hy).1
    have hyQ := hC.split.commutator_le_Q hyR
    have hwy : ⁅r⁻¹ * e, y⁆ ∈ Z2 := hC.split.commutator_W _ hw y (hC.split.le hyQ)
    have hcomm := hC.split.comm _ hwy r hrQ
    have hry := hC.R_comm r hrR y hyR
    have key : ⁅e, y⁆ = ⁅r⁻¹ * e, y⁆ := by
      calc ⁅e, y⁆ = r * ⁅r⁻¹ * e, y⁆ * (y * r⁻¹ * y⁻¹) := by
            simp only [commutatorElement_def]
            group
        _ = ⁅r⁻¹ * e, y⁆ * (r * y * r⁻¹ * y⁻¹) := by
            rw [hcomm]
            group
        _ = ⁅r⁻¹ * e, y⁆ := by
            rw [hry]
            group
    rw [key, hs y hyQ]
  · have hwZ := (hC.split.pair_eq_zero_iff hw hs).mp hs0
    refine hC.mem_center_of_mem_E_of_mem_R he ?_
    rw [show e = r * (r⁻¹ * e) by group]
    exact mul_mem hrR (hC.split.center_le_commutator hwZ)

variable {a₁ : G}

theorem pair_formula (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    (hEQ : E ≤ Q2) (ha₁ : a₁ ∈ ⁅Q2, L2⁆ ⊓ Q1) (ha₁v : nv a₁ = ![1, 0]) {e : G} (he : e ∈ E)
    {y : G} (hy : y ∈ ⁅Q2, L2⁆ ⊓ Q1) : zv ⁅e, y⁆ 0 = zv ⁅e, a₁⁆ 0 * nv y 0 := by
  obtain ⟨s, hs, -⟩ := hC.exists_pair_E hEQ he
  rw [hs y hy, hs a₁ ha₁, ha₁v]
  simp

theorem mem_center_of_pair_eq_zero (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    (hEQ : E ≤ Q2) (ha₁ : a₁ ∈ ⁅Q2, L2⁆ ⊓ Q1) (ha₁v : nv a₁ = ![1, 0]) {e : G} (he : e ∈ E)
    (h : zv ⁅e, a₁⁆ 0 = 0) : e ∈ Z2 := by
  obtain ⟨s, hs, hs0⟩ := hC.exists_pair_E hEQ he
  have k : zv ⁅e, a₁⁆ 0 = s := by simpa [ha₁v] using congrFun (hs a₁ ha₁) 0
  exact hs0 (k.symm.trans h)

theorem pair_mul (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) (hEQ : E ≤ Q2)
    (ha₁Q : a₁ ∈ Q2) {e e' : G} (he : e ∈ E) (he' : e' ∈ E) :
    zv ⁅e * e', a₁⁆ = zv ⁅e, a₁⁆ + zv ⁅e', a₁⁆ := by
  have hc : ⁅e', a₁⁆ ∈ Z2 := hC.split.commutator_mem e' (hEQ he') a₁ ha₁Q
  have hc' : ⁅e, a₁⁆ ∈ Z2 := hC.split.commutator_mem e (hEQ he) a₁ ha₁Q
  rw [show ⁅e * e', a₁⁆ = e * ⁅e', a₁⁆ * e⁻¹ * ⁅e, a₁⁆ by simp only [commutatorElement_def]; group,
    hC.split.conj_eq_of_mem (hEQ he) hc, hC.split.nat.map_mul _ hc _ hc', add_comm]

theorem borel_pair (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) (hEQ : E ≤ Q2)
    (ha₁ : a₁ ∈ ⁅Q2, L2⁆ ⊓ Q1) (ha₁v : nv a₁ = ![1, 0]) {b : ↥L1} (hb : α₁ b ∈ borel F₁)
    {e : G} (he : e ∈ E) {y : G} (hy : y ∈ ⁅Q2, L2⁆ ⊓ Q1) :
    zv ⁅(b : G) * e * (b : G)⁻¹, a₁⁆ 0 * nv ((b : G) * y * (b : G)⁻¹) 0 =
      zv ⁅e, a₁⁆ 0 * nv y 0 := by
  obtain ⟨hbL, hbQ⟩ := hC.borel_left b hb
  have hy1 := (Subgroup.mem_inf.mp hy).2
  have hby : (b : G) * y * (b : G)⁻¹ ∈ ⁅Q2, L2⁆ ⊓ Q1 := Subgroup.mem_inf.mpr
    ⟨G2qSplitData.conj_mem_commutator_of_conj_mem
      (fun a ha => (Subgroup.mem_normalizer_iff.mp hbQ a).mp ha)
      (fun m hm => (Subgroup.mem_normalizer_iff.mp hbL m).mp hm) (Subgroup.mem_inf.mp hy).1,
      hC.conj_left b b.2 y hy1⟩
  have hc : ⁅e, y⁆ ∈ Z1 := hC.comm_left e (hC.E_le he) y hy1
  have key : ⁅(b : G) * e * (b : G)⁻¹, (b : G) * y * (b : G)⁻¹⁆ = ⁅e, y⁆ := by
    rw [← conjugate_commutatorElement, hC.center_left _ hc b b.2, mul_inv_cancel_right]
  rw [← hC.pair_formula hEQ ha₁ ha₁v (hC.natE.conj_mem b e he) hby, key,
    hC.pair_formula hEQ ha₁ ha₁v he hy]

theorem borel_nv (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) (hEQ : E ≤ Q2)
    (ha₁ : a₁ ∈ ⁅Q2, L2⁆ ⊓ Q1) (ha₁v : nv a₁ = ![1, 0]) {e' : G} (he' : e' ∈ E)
    (hX : zv ⁅e', a₁⁆ 0 ≠ 0) {b : ↥L1} (hb : α₁ b ∈ borel F₁) {e : G} (he : e ∈ E) :
    nv ((b : G) * e * (b : G)⁻¹) 0 = nv ((b : G) * a₁ * (b : G)⁻¹) 0 * nv e 0 := by
  obtain ⟨hbL, hbQ⟩ := hC.borel_left b hb
  obtain ⟨y, hy, hyv⟩ := hC.exists_mem_Y_nv_eq ha₁ (by rw [ha₁v]; simp) (nv e 0)
  have hyQ := hC.split.commutator_le_Q (Subgroup.mem_inf.mp hy).1
  have hev : nv y = nv e := by
    rw [hyv]
    funext i
    fin_cases i
    · rfl
    · exact (hC.nv_apply_one_of_mem_E hEQ he).symm
  have hw : y⁻¹ * e ∈ W := hC.split.natW.inv_mul_mem hyQ (hEQ he) hev
  have hbw : (b : G) * (y⁻¹ * e) * (b : G)⁻¹ ∈ W := hC.split.torus_conj_mem_W hbL hbQ hw
  have hby : (b : G) * y * (b : G)⁻¹ ∈ Q2 := (Subgroup.mem_normalizer_iff.mp hbQ y).mp hyQ
  have h1 : nv ((b : G) * e * (b : G)⁻¹) = nv ((b : G) * y * (b : G)⁻¹) := by
    rw [show (b : G) * e * (b : G)⁻¹ =
        ((b : G) * y * (b : G)⁻¹) * ((b : G) * (y⁻¹ * e) * (b : G)⁻¹) by group,
      hC.split.natW.map_mul _ hby _ (hC.split.le_Q hbw),
      (hC.split.natW.eq_zero_iff _ (hC.split.le_Q hbw)).mpr hbw, add_zero]
  have k1 := hC.borel_pair hEQ ha₁ ha₁v hb he' hy
  have k2 := hC.borel_pair hEQ ha₁ ha₁v hb he' ha₁
  rw [ha₁v] at k2
  simp only [Matrix.cons_val_zero, mul_one] at k2
  have hA : zv ⁅(b : G) * e' * (b : G)⁻¹, a₁⁆ 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at k2
    exact hX k2.symm
  rw [h1, ← congrFun hev 0]
  exact mul_left_cancel₀ hA (by linear_combination k1 - nv y 0 * k2)

theorem exists_borel_conj (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) {e e' : G}
    (he : e ∈ E) (he' : e' ∈ E) (h1 : vE e 1 ≠ 0) (h1' : vE e' 1 ≠ 0) :
    ∃ b : ↥L1, α₁ b ∈ borel F₁ ∧ ((b : G) * e * (b : G)⁻¹)⁻¹ * e' ∈ Z2 := by
  obtain ⟨b, hb⟩ := hC.surj_left (torusElt (Units.mk0 (vE e 1 / vE e' 1) (div_ne_zero h1 h1')))
  have hbB : α₁ b ∈ borel F₁ := by rw [hb]; exact torusElt_mem_borel _
  have hbe := hC.natE.conj_mem b e he
  refine ⟨b, hbB, (hC.mem_center_right_iff (mul_mem (inv_mem hbe) he')).mpr ?_⟩
  rw [hC.natE.map_inv_mul hbe he', Pi.sub_apply, hC.natE.conj b e he, hb,
    natE_torusElt_mulVec_one, Units.val_inv_eq_inv_val, Units.val_mk0, inv_div,
    div_mul_cancel₀ _ h1, sub_self]

private theorem pair_center_eq_zero (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    (ha₁Q : a₁ ∈ Q2) {z : G} (hz : z ∈ Z2) : zv ⁅z, a₁⁆ 0 = 0 := by
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hC.split.comm z hz a₁ ha₁Q).symm,
    hC.split.nat.map_one, Pi.zero_apply]

private theorem pair_inv (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    (hEQ : E ≤ Q2) (ha₁Q : a₁ ∈ Q2) {e : G} (he : e ∈ E) : zv ⁅e⁻¹, a₁⁆ = -zv ⁅e, a₁⁆ := by
  have k := hC.pair_mul hEQ ha₁Q (inv_mem he) he
  rw [inv_mul_cancel, commutatorElement_one_left, hC.split.nat.map_one] at k
  exact eq_neg_iff_add_eq_zero.mpr k.symm

private theorem pair_nv_eq_of_inv_mul_mem
    (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) (hEQ : E ≤ Q2) (ha₁Q : a₁ ∈ Q2)
    {e e' : G} (he : e ∈ E) (he' : e' ∈ E) (hz : e⁻¹ * e' ∈ Z2) :
    zv ⁅e', a₁⁆ 0 = zv ⁅e, a₁⁆ 0 ∧ nv e' 0 = nv e 0 := by
  have hm := mul_mem (inv_mem he) he'
  refine ⟨?_, ?_⟩
  · have k := congrFun (hC.pair_mul hEQ ha₁Q he hm) 0
    rw [mul_inv_cancel_left, Pi.add_apply, hC.pair_center_eq_zero ha₁Q hz, add_zero] at k
    exact k
  · have k := (hC.split.natW.eq_zero_iff _ (hEQ hm)).mpr (hC.split.center_le hz)
    rw [hC.split.natW.map_inv_mul (hEQ he) (hEQ he')] at k
    exact congrFun (sub_eq_zero.mp k) 0

private theorem exists_X_surj (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    [Finite F₂] (hEQ : E ≤ Q2) (ha₁ : a₁ ∈ ⁅Q2, L2⁆ ⊓ Q1) (ha₁v : nv a₁ = ![1, 0])
    (x : F₂) : ∃ e ∈ E, zv ⁅e, a₁⁆ 0 = x := by
  have ha₁Q := hC.split.commutator_le_Q (Subgroup.mem_inf.mp ha₁).1
  choose et hetE hetv using fun t : F₁ => hC.natE.surj ![0, t]
  have hinj : Function.Injective fun t => zv ⁅et t, a₁⁆ 0 := by
    intro t t' h
    have hmem := mul_mem (inv_mem (hetE t)) (hetE t')
    have hX0 : zv ⁅(et t)⁻¹ * et t', a₁⁆ 0 = 0 := by
      rw [hC.pair_mul hEQ ha₁Q (inv_mem (hetE t)) (hetE t'), Pi.add_apply,
        hC.pair_inv hEQ ha₁Q (hetE t), Pi.neg_apply]
      simp only at h
      rw [h, neg_add_cancel]
    have hZ := (hC.mem_center_right_iff hmem).mp
      (hC.mem_center_of_pair_eq_zero hEQ ha₁ ha₁v hmem hX0)
    rw [hC.natE.map_inv_mul (hetE t) (hetE t'), Pi.sub_apply, hetv, hetv] at hZ
    have h' : t' - t = 0 := by simpa using hZ
    exact (sub_eq_zero.mp h').symm
  obtain ⟨t, ht⟩ := (hinj.bijective_of_nat_card_le hC.card_eq.symm.le).2 x
  exact ⟨et t, hetE t, ht⟩

private theorem exists_psi (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    [Finite F₂] (hEQ : E ≤ Q2) (ha₁ : a₁ ∈ ⁅Q2, L2⁆ ⊓ Q1) (ha₁v : nv a₁ = ![1, 0]) :
    ∃ ψ : F₂ → F₂, (∀ e ∈ E, ψ (zv ⁅e, a₁⁆ 0) = nv e 0) ∧ ∀ x y, ψ (x + y) = ψ x + ψ y := by
  have ha₁Q := hC.split.commutator_le_Q (Subgroup.mem_inf.mp ha₁).1
  choose ex hexE hexX using hC.exists_X_surj hEQ ha₁ ha₁v
  have hψ : ∀ e ∈ E, nv (ex (zv ⁅e, a₁⁆ 0)) 0 = nv e 0 := by
    intro e he
    refine (hC.pair_nv_eq_of_inv_mul_mem hEQ ha₁Q (hexE _) he ?_).2.symm
    refine hC.mem_center_of_pair_eq_zero hEQ ha₁ ha₁v (mul_mem (inv_mem (hexE _)) he) ?_
    rw [hC.pair_mul hEQ ha₁Q (inv_mem (hexE _)) he, Pi.add_apply, hC.pair_inv hEQ ha₁Q (hexE _),
      Pi.neg_apply, hexX, neg_add_cancel]
  refine ⟨fun x => nv (ex x) 0, hψ, fun x y => ?_⟩
  have h := hψ _ (mul_mem (hexE x) (hexE y))
  rw [hC.pair_mul hEQ ha₁Q (hexE x) (hexE y), Pi.add_apply, hexX, hexX,
    hC.split.natW.map_mul _ (hEQ (hexE x)) _ (hEQ (hexE y)), Pi.add_apply] at h
  exact h

private theorem psi_mul (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv)
    [Finite F₂] (hEQ : E ≤ Q2) (ha₁ : a₁ ∈ ⁅Q2, L2⁆ ⊓ Q1) (ha₁v : nv a₁ = ![1, 0])
    {ψ : F₂ → F₂} (hψ : ∀ e ∈ E, ψ (zv ⁅e, a₁⁆ 0) = nv e 0)
    (hψadd : ∀ x y, ψ (x + y) = ψ x + ψ y) {c : F₂} (hc : c ≠ 0) (x : F₂) :
    ψ (c * x) = c⁻¹ * ψ x := by
  have ha₁Q := hC.split.commutator_le_Q (Subgroup.mem_inf.mp ha₁).1
  by_cases hx : x = 0
  · have h := hψadd 0 0
    rw [add_zero] at h
    rw [hx, mul_zero, add_left_cancel (h.symm.trans (add_zero _).symm), mul_zero]
  have hsnd : ∀ e ∈ E, zv ⁅e, a₁⁆ 0 ≠ 0 → vE e 1 ≠ 0 := fun e he hX h =>
    hX (hC.pair_center_eq_zero ha₁Q ((hC.mem_center_right_iff he).mpr h))
  obtain ⟨e, he, hex⟩ := hC.exists_X_surj hEQ ha₁ ha₁v x
  obtain ⟨e', he', he'x⟩ := hC.exists_X_surj hEQ ha₁ ha₁v (c * x)
  obtain ⟨e₁, he₁, he₁X⟩ := hC.exists_X_surj hEQ ha₁ ha₁v 1
  obtain ⟨b, hb, hbZ⟩ := hC.exists_borel_conj he he' (hsnd e he (by rw [hex]; exact hx))
    (hsnd e' he' (by rw [he'x]; exact mul_ne_zero hc hx))
  obtain ⟨hXb, hηb⟩ :=
    hC.pair_nv_eq_of_inv_mul_mem hEQ ha₁Q (hC.natE.conj_mem b e he) he' hbZ
  have k2 := hC.borel_pair hEQ ha₁ ha₁v hb he ha₁
  rw [ha₁v, ← hXb, he'x, hex] at k2
  simp only [Matrix.cons_val_zero, mul_one] at k2
  have hμ : nv ((b : G) * a₁ * (b : G)⁻¹) 0 = c⁻¹ :=
    eq_inv_of_mul_eq_one_right (mul_left_cancel₀ hx (by linear_combination k2))
  rw [← he'x, hψ e' he', ← hex, hψ e he, hηb,
    hC.borel_nv hEQ ha₁ ha₁v he₁ (by rw [he₁X]; exact one_ne_zero) hb he, hμ]

theorem E_le_W (hC : G2qNatEConf L1 L2 S Q1 Q2 Z1 Z2 W E α₁ α₂ vE nv zv) [Finite F₂]
    [CharP F₂ 2] (hEQ : E ≤ Q2) : E ≤ W := by
  by_contra hEW
  obtain ⟨e₀, he₀E, he₀W⟩ := SetLike.not_le_iff_exists.mp hEW
  have he₀0 : nv e₀ 0 ≠ 0 := by
    intro h0
    refine he₀W ((hC.split.natW.eq_zero_iff _ (hEQ he₀E)).mp ?_)
    funext i
    fin_cases i
    · exact h0
    · exact hC.nv_apply_one_of_mem_E hEQ he₀E
  obtain ⟨a₁, ha₁, ha₁v⟩ := hC.exists_mem_Y_of_mem_E hEQ he₀E he₀0 1
  obtain ⟨ψ, hψ, hψadd⟩ := hC.exists_psi hEQ ha₁ ha₁v
  have h := natE_eq_zero_of_map_mul_inv hC.five_le hψadd
    (fun c hc x => hC.psi_mul hEQ ha₁ ha₁v hψ hψadd hc x) (zv ⁅e₀, a₁⁆ 0)
  exact he₀0 ((hψ e₀ he₀E).symm.trans h)

end G2qNatEConf

end CFSG.Quasithin.F112R.St84

end

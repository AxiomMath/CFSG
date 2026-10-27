module

public import CFSG.Sporadic.SuzRecog.Cover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore

local notation "ψ" => Coord.psi (t := suzInv 1) (q := qVec)

section Pointwise

variable {n : ℕ}

theorem rep_get3 {ta tb tc : Array ℕ} {A B C : Equiv.Perm (Fin n)} (ha : Rep n ta A)
    (hb : Rep n tb B) (hc : Rep n tc C) (y : Fin n) :
    ta[tb[tc[(y : ℕ)]!]!]! = ((A * B * C) y : ℕ) := by
  rw [hc y, hb (C y), ha (B (C y))]
  rfl

theorem rep_get4 {ta tb tc td : Array ℕ} {A B C D : Equiv.Perm (Fin n)} (ha : Rep n ta A)
    (hb : Rep n tb B) (hc : Rep n tc C) (hd : Rep n td D) (y : Fin n) :
    ta[tb[tc[td[(y : ℕ)]!]!]!]! = ((A * B * C * D) y : ℕ) := by
  rw [hd y, hc (D y), hb (C (D y)), ha (B (C (D y)))]
  rfl

theorem allLt_eq_iff {f g : Equiv.Perm (Fin n)} {p : ℕ → Bool}
    (hp : ∀ y : Fin n, p y = true ↔ (f y : ℕ) = g y) : allLt n p = true ↔ f = g := by
  rw [allLt_iff]
  constructor
  · intro h
    exact Equiv.ext fun y => Fin.ext ((hp y).1 (h y y.2))
  · rintro rfl i hi
    exact (hp ⟨i, hi⟩).2 rfl

end Pointwise

@[expose] noncomputable def w0P : Equiv.Perm (Fin 1782) := qVec 1

@[expose] noncomputable def qE (j : ℕ) : Equiv.Perm (Fin 1782) := qVec (j / 2) * suzInv 1 ^ (j % 2)

section Cert


theorem rep_w0P : Rep 1782 w0Tab w0P := rep_qProds (by norm_num)

theorem rep_w0tP : Rep 1782 w0tTab (w0P * suzInv 1) := rep_compA rep_w0P rep_tTab

theorem rep_qE {j : ℕ} (hj : j < 128) : Rep 1782 qElts[j]! (qE j) := by
  rw [qElts_get hj]
  exact rep_compA (rep_qProds (by omega)) (rep_tPow (Nat.mod_lt _ (by norm_num)))

theorem commTest_iff {x q : Array ℕ} {X P : Equiv.Perm (Fin 1782)} (hx : Rep 1782 x X)
    (hq : Rep 1782 q P) : commTest x q = true ↔ X * P * w0P = w0P * (X * P) := by
  rw [commTest]
  refine allLt_eq_iff fun y => ?_
  rw [beq_iff_eq, rep_get3 hx hq rep_w0P y, rep_get3 rep_w0P hx hq y, mul_assoc w0P]

theorem sqTest_iff {x q s : Array ℕ} {X P T : Equiv.Perm (Fin 1782)} (hx : Rep 1782 x X)
    (hq : Rep 1782 q P) (hs : Rep 1782 s T) : sqTest x q s = true ↔ X * P * (X * P) = T := by
  rw [sqTest]
  refine allLt_eq_iff fun y => ?_
  rw [beq_iff_eq, rep_get4 hx hq hx hq y, hs y, ← mul_assoc]

theorem invTest_iff {x q : Array ℕ} {X P : Equiv.Perm (Fin 1782)} (hx : Rep 1782 x X)
    (hq : Rep 1782 q P) : invTest x q = true ↔ X * P * (X * P) = 1 := by
  rw [invTest]
  refine allLt_eq_iff fun y => ?_
  rw [beq_iff_eq, rep_get4 hx hq hx hq y, ← mul_assoc]
  rfl

theorem kind_eq_one_iff {x : Array ℕ} {X : Equiv.Perm (Fin 1782)} (hx : Rep 1782 x X)
    {j : ℕ} (hj : j < 128) :
    kind x j = 1 ↔ X * qE j * w0P = w0P * (X * qE j) ∧
      (X * qE j * (X * qE j) = w0P ∨ X * qE j * (X * qE j) = w0P * suzInv 1) := by
  have hq := rep_qE hj
  rw [← commTest_iff hx hq, ← sqTest_iff hx hq rep_w0P, ← sqTest_iff hx hq rep_w0tP]
  unfold kind
  split_ifs with h1 h2 h3 <;> simp_all

theorem of_kind_eq_two {x : Array ℕ} {X : Equiv.Perm (Fin 1782)} (hx : Rep 1782 x X)
    {j : ℕ} (hj : j < 128) (h : kind x j = 2) :
    X * qE j * w0P = w0P * (X * qE j) ∧ X * qE j * (X * qE j) = 1 := by
  have hq := rep_qE hj
  rw [← commTest_iff hx hq, ← invTest_iff hx hq]
  unfold kind at h
  split_ifs at h with h1 h2 h3 <;> simp_all


theorem qE_mem {j : ℕ} (hj : j < 128) : qE j ∈ coord_qVec.Q :=
  coord_qVec.mem_Q_iff.mpr ⟨j / 2, by omega, j % 2, Nat.mod_lt _ (by norm_num), rfl⟩

theorem w0P_mem : w0P ∈ coord_qVec.Q := coord_qVec.q_mem (by norm_num)

theorem conjTest_iff {r g s : Tab} {R G T : Equiv.Perm (Fin 64)} (hr : TabRep r R)
    (hg : TabRep g G) (hs : TabRep s T) : conjTest r g s = true ↔ R * G = G * T := by
  rw [conjTest]
  refine allLt_eq_iff fun y => ?_
  rw [beq_iff_eq, hg.apply y, hr.apply (G y), hs.apply y, hg.apply (T y)]
  rfl

end Cert

theorem fibreCheck_parts :
    (∀ i ∈ invPos, matWord (enumWord i) = matEnum.tabs[i]! ∧ ∀ k ∈ enumWord i, k < 10) ∧
      countW = 480 ∧ countZ = 1200 := by
  have h := twistFibre_check
  simp only [fibreCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    at h
  exact ⟨fun i hi => h.1.1 i hi, h.1.2, h.2⟩

@[expose] noncomputable def xElt (i : ℕ) (hi : i ∈ invPos) : ↥(invE 1) :=
  wElt (enumWord i) (fibreCheck_parts.1 i hi).2

theorem rep_xElt {i : ℕ} (hi : i ∈ invPos) :
    Rep 1782 (liftTab i) ((xElt i hi : ↥(invE 1)) : Equiv.Perm (Fin 1782)) :=
  rep_cWord (fibreCheck_parts.1 i hi).2

theorem tabRep_xElt {i : ℕ} (hi : i ∈ invPos) :
    TabRep matEnum.tabs[i]! (kapL (phi0 (xElt i hi))) := by
  rw [← (fibreCheck_parts.1 i hi).1]
  exact tabRep_matWord _

theorem matEnum_size : matEnum.tabs.size = 25920 := b0_parts.2.2.2.2.2.1

theorem exists_mem_invPos {l : Lm} (hl1 : l.1 (bitVec 1) = bitVec 1)
    (hl2 : l * l = 1) : ∃ i, ∃ hi : i ∈ invPos, phi0 (xElt i hi) = l := by
  have hmem : kapL l ∈ rho1.range.map kappa := by
    refine ⟨(l : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)), ?_, rfl⟩
    rw [range_rho1]
    exact l.2
  obtain ⟨t, ht, hrep⟩ := kappa_rho1_enumerates.complete _ hmem
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  have hfix : fixInv matEnum.tabs[i]! = true := by
    rw [fixInv, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    refine ⟨?_, ?_⟩
    · rw [hrep.apply ⟨1, by norm_num⟩]
      change ((bitEquiv.symm (l.1 (bitVec 1)) : Fin 64) : ℕ) = 1
      rw [hl1]
      exact bitEquiv_symm_bitVec (by norm_num)
    · have h2 := hrep.comp hrep
      rw [← map_mul, hl2, map_one] at h2
      exact h2.tab_eq TabRep.idTab
  have hiP : i ∈ invPos := by
    rw [invPos, List.mem_filter, List.mem_range]
    exact ⟨by rw [← matEnum_size]; exact hi, hfix⟩
  exact ⟨i, hiP, kapL_injective ((tabRep_xElt hiP).perm_eq hrep)⟩

@[expose] noncomputable def w0C : ↥(invE 1) := ⟨w0P, Q_le_invE w0P_mem⟩

theorem psi_w0P : ψ w0P = bitVec 1 := coord_qVec.psi_q (by norm_num)

theorem exists_eq_xElt_mul {h : ↥(invE 1)} (hc : h * w0C = w0C * h)
    (hq : ((h * h : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ coord_qVec.Q) :
    ∃ i, ∃ hi : i ∈ invPos, ∃ j < 128,
      (h : Equiv.Perm (Fin 1782)) = (xElt i hi : Equiv.Perm (Fin 1782)) * qE j := by
  have hl1 : (phi0 h).1 (bitVec 1) = bitVec 1 := by
    rw [coe_phi0, ← psi_w0P, ← psi_conj h w0P_mem]
    congr 1
    have h1 := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at h1
    rw [show (w0C : Equiv.Perm (Fin 1782)) = w0P from rfl] at h1
    rw [h1, mul_inv_cancel_right]
  have hl2 : phi0 h * phi0 h = 1 := by
    rw [← map_mul]
    exact (phi0_eq_one_iff _).2 hq
  obtain ⟨i, hi, hx⟩ := exists_mem_invPos hl1 hl2
  have hk : phi0 ((xElt i hi)⁻¹ * h) = 1 := by rw [map_mul, map_inv, hx, inv_mul_cancel]
  obtain ⟨v, hv, a, ha, he⟩ := coord_qVec.mem_Q_iff.mp ((phi0_eq_one_iff _).1 hk)
  refine ⟨i, hi, 2 * v + a, by omega, ?_⟩
  have e1 : qE (2 * v + a) = qVec v * suzInv 1 ^ a := by
    rw [qE, show (2 * v + a) / 2 = v by omega, show (2 * v + a) % 2 = a by omega]
  rw [e1, ← he]
  simp

theorem invPos_nodup : invPos.Nodup := by
  unfold invPos
  exact List.Nodup.filter _ List.nodup_range

theorem countBelow_kind (x : Array ℕ) (c : ℕ) :
    countBelow 128 (fun j => kind x j == c) =
      ((Finset.range 128).filter fun j => kind x j = c).card := by
  rw [countBelow_eq]
  simp only [beq_iff_eq]

theorem coe_w0C : ((w0C : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = w0P := rfl

theorem coe_t1C : ((t1C : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = suzInv 1 := rfl

@[expose] noncomputable def fibreSet (c : ℕ) (i : ℕ) : Finset (Equiv.Perm (Fin 1782)) :=
  ((Finset.range 128).filter fun j => kind (liftTab i) j = c).image fun j =>
    wPerm (enumWord i) * qE j

theorem mem_fibreSet {c i : ℕ} {x : Equiv.Perm (Fin 1782)} :
    x ∈ fibreSet c i ↔ ∃ j < 128, kind (liftTab i) j = c ∧ wPerm (enumWord i) * qE j = x := by
  rw [fibreSet, Finset.mem_image]
  simp only [Finset.mem_filter, Finset.mem_range, and_assoc]

theorem card_fibreSet_le (c i : ℕ) :
    (fibreSet c i).card ≤ countBelow 128 (fun j => kind (liftTab i) j == c) := by
  rw [countBelow_kind]
  exact Finset.card_image_le

theorem card_sq_w_le :
    Nat.card {h : ↥(invE 1) // h * w0C = w0C * h ∧ (h * h = w0C ∨ h * h = w0C * t1C)} ≤ 480 := by
  classical
  obtain ⟨FW, hFW⟩ : ∃ s : Finset (Equiv.Perm (Fin 1782)),
      s = invPos.toFinset.biUnion (fibreSet 1) := ⟨_, rfl⟩
  have hsub : ∀ h : {h : ↥(invE 1) // h * w0C = w0C * h ∧ (h * h = w0C ∨ h * h = w0C * t1C)},
      ((h : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ FW := by
    rintro ⟨h, hc, hs⟩
    have hq : ((h * h : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ coord_qVec.Q := by
      rcases hs with hs | hs
      · rw [hs, coe_w0C]
        exact w0P_mem
      · rw [hs, Subgroup.coe_mul, coe_w0C, coe_t1C]
        exact coord_qVec.Q.mul_mem w0P_mem coord_qVec.t_mem
    obtain ⟨i, hi, j, hj, he⟩ := exists_eq_xElt_mul hc hq
    have hcomm : (h : Equiv.Perm (Fin 1782)) * w0P = w0P * h := by
      have := congrArg Subtype.val hc
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_w0C] at this
    have hsq : (h : Equiv.Perm (Fin 1782)) * h = w0P ∨
        (h : Equiv.Perm (Fin 1782)) * h = w0P * suzInv 1 := by
      rcases hs with hs | hs
      · left
        have := congrArg Subtype.val hs
        rwa [Subgroup.coe_mul, coe_w0C] at this
      · right
        have := congrArg Subtype.val hs
        rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_w0C, coe_t1C] at this
    rw [hFW, Finset.mem_biUnion]
    refine ⟨i, List.mem_toFinset.mpr hi, mem_fibreSet.mpr ⟨j, hj, ?_, he.symm⟩⟩
    have hx : (xElt i hi : Equiv.Perm (Fin 1782)) = wPerm (enumWord i) := rfl
    rw [hx] at he
    refine (kind_eq_one_iff (rep_xElt hi) hj).2 ⟨?_, ?_⟩
    · rw [hx, ← he]
      exact hcomm
    · rw [hx, ← he]
      exact hsq
  have hcard : FW.card ≤ 480 := by
    rw [hFW]
    refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_sum fun i _ => card_fibreSet_le 1 i).trans ?_
    rw [List.sum_toFinset _ invPos_nodup, ← fibreCheck_parts.2.1, countW]
  calc Nat.card {h : ↥(invE 1) // h * w0C = w0C * h ∧ (h * h = w0C ∨ h * h = w0C * t1C)}
      ≤ Nat.card FW := Nat.card_le_card_of_injective
        (fun h => ⟨((h : ↥(invE 1)) : Equiv.Perm (Fin 1782)), hsub h⟩)
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    _ = FW.card := Nat.card_eq_finsetCard FW
    _ ≤ 480 := hcard

theorem exists_conj_of_conjOK {i : ℕ} (hi : i ∈ invPos) (hc : conjOK i = true) :
    ∃ γ : Lm, phi0 (xElt i hi) * γ = γ * lB := by
  rw [conjOK, anyBelow_eq_true] at hc
  obtain ⟨c, hc25920, hct⟩ := hc
  obtain ⟨g, ⟨g', hg', rfl⟩, hrep⟩ := kappa_rho1_enumerates.sound _
    (getElem!_mem (by rw [matEnum_size]; exact hc25920))
  have hγ : g' ∈ Lm := by rw [Lm, ← range_rho1]; exact hg'
  refine ⟨⟨g', hγ⟩, kapL_injective ?_⟩
  rw [map_mul, map_mul]
  exact (conjTest_iff (tabRep_xElt hi) hrep tabRep_lB).1 hct

@[expose] noncomputable def fibreElt (i : ℕ) (hi : i ∈ invPos) (j : ℕ) (hj : j < 128) :
    ↥(invE 1) :=
  xElt i hi * ⟨qE j, Q_le_invE (qE_mem hj)⟩

theorem coe_fibreElt {i : ℕ} (hi : i ∈ invPos) {j : ℕ} (hj : j < 128) :
    ((fibreElt i hi j hj : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = wPerm (enumWord i) * qE j :=
  rfl

theorem phi0_fibreElt {i : ℕ} (hi : i ∈ invPos) {j : ℕ} (hj : j < 128) :
    phi0 (fibreElt i hi j hj) = phi0 (xElt i hi) := by
  rw [fibreElt, map_mul, (phi0_eq_one_iff ⟨qE j, Q_le_invE (qE_mem hj)⟩).2 (qE_mem hj),
    mul_one]

theorem fibreElt_ne {i i' : ℕ} (hi : i ∈ invPos) (hi' : i' ∈ invPos) (hne : i ≠ i')
    {j j' : ℕ} (hj : j < 128) (hj' : j' < 128) : fibreElt i hi j hj ≠ fibreElt i' hi' j' hj' := by
  intro he
  have e := congrArg phi0 he
  rw [phi0_fibreElt, phi0_fibreElt] at e
  have ht := (tabRep_xElt hi).tab_eq (e ▸ tabRep_xElt hi')
  have hlt : i < matEnum.tabs.size := by
    rw [matEnum_size]
    rw [invPos] at hi
    exact List.mem_range.mp (List.mem_filter.mp hi).1
  have hlt' : i' < matEnum.tabs.size := by
    rw [matEnum_size]
    rw [invPos] at hi'
    exact List.mem_range.mp (List.mem_filter.mp hi').1
  have hnd := kappa_rho1_enumerates.nodup
  rw [List.nodup_iff_injective_getElem] at hnd
  have := @hnd ⟨i, by simpa using hlt⟩ ⟨i', by simpa using hlt'⟩ (by
    simp only [Array.getElem_toList]
    rw [← getElem!_pos _ i hlt, ← getElem!_pos _ i' hlt']
    exact ht)
  exact hne (congrArg Fin.val this)

theorem qE_injOn {j j' : ℕ} (hj : j < 128) (hj' : j' < 128) (he : qE j = qE j') : j = j' := by
  have := coord_qVec.inj (j / 2) (by omega) (j' / 2) (by omega) (j % 2)
    (Nat.mod_lt _ (by norm_num)) (j' % 2) (Nat.mod_lt _ (by norm_num)) he
  omega

@[expose] noncomputable def invSet (i : ℕ) : Finset ℕ :=
  if conjOK i then (Finset.range 128).filter fun j => kind (liftTab i) j = 2 else ∅

theorem mem_invSet {i j : ℕ} : j ∈ invSet i ↔ conjOK i = true ∧ j < 128 ∧
    kind (liftTab i) j = 2 := by
  rw [invSet]
  split_ifs with h
  · rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hj => ⟨h, hj⟩, fun hj => hj.2⟩
  · simp [h]

theorem card_sq_one_ge :
    1200 ≤ Nat.card {h : ↥(invE 1) // h * w0C = w0C * h ∧ h * h = 1 ∧
      ∃ γ : Lm, phi0 h * γ = γ * lB} := by
  classical
  obtain ⟨IZ, hIZ⟩ : ∃ s : Finset (Σ _ : ℕ, ℕ), s = invPos.toFinset.sigma invSet := ⟨_, rfl⟩
  have hmemIZ : ∀ p ∈ IZ, p.1 ∈ invPos ∧ conjOK p.1 = true ∧ p.2 < 128 ∧
      kind (liftTab p.1) p.2 = 2 := by
    intro p hp
    rw [hIZ, Finset.mem_sigma, List.mem_toFinset, mem_invSet] at hp
    exact ⟨hp.1, hp.2⟩
  have hcardIZ : IZ.card = 1200 := by
    rw [hIZ, Finset.card_sigma, List.sum_toFinset _ invPos_nodup, ← fibreCheck_parts.2.2,
      countZ]
    refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
    rw [invSet]
    split_ifs with hc
    · exact (countBelow_kind (liftTab i) 2).symm
    · rfl
  have hprop : ∀ p : IZ, ∃ h : {h : ↥(invE 1) // h * w0C = w0C * h ∧ h * h = 1 ∧
      ∃ γ : Lm, phi0 h * γ = γ * lB}, (h : ↥(invE 1)) =
        fibreElt p.1.1 (hmemIZ p.1 p.2).1 p.1.2 (hmemIZ p.1 p.2).2.2.1 := by
    rintro ⟨⟨i, j⟩, hp⟩
    obtain ⟨hi, hc, hj, hk⟩ := hmemIZ _ hp
    obtain ⟨hcomm, hsq⟩ := of_kind_eq_two (rep_xElt hi) hj hk
    obtain ⟨γ, hγ⟩ := exists_conj_of_conjOK hi hc
    refine ⟨⟨fibreElt i hi j hj, ?_, ?_, γ, ?_⟩, rfl⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_fibreElt, coe_w0C]
      exact hcomm
    · apply Subtype.ext
      rw [Subgroup.coe_mul, coe_fibreElt, OneMemClass.coe_one]
      exact hsq
    · rw [phi0_fibreElt]
      exact hγ
  rw [← hcardIZ, ← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective (fun p => Classical.choose (hprop p)) ?_
  rintro ⟨⟨i, j⟩, hp⟩ ⟨⟨i', j'⟩, hp'⟩ hpp
  have e1 := Classical.choose_spec (hprop ⟨⟨i, j⟩, hp⟩)
  have e2 := Classical.choose_spec (hprop ⟨⟨i', j'⟩, hp'⟩)
  have he := congrArg (fun h : {h : ↥(invE 1) // h * w0C = w0C * h ∧ h * h = 1 ∧
      ∃ γ : Lm, phi0 h * γ = γ * lB} => (h : ↥(invE 1))) hpp
  simp only at he
  rw [e1, e2] at he
  obtain ⟨hi, -, hj, -⟩ := hmemIZ _ hp
  obtain ⟨hi', -, hj', -⟩ := hmemIZ _ hp'
  have hii : i = i' := by
    by_contra hne
    exact fibreElt_ne hi hi' hne hj hj' he
  subst hii
  have hq : qE j = qE j' := by
    have := congrArg Subtype.val he
    rw [coe_fibreElt, coe_fibreElt] at this
    exact mul_left_cancel this
  have hjj := qE_injOn hj hj' hq
  subst hjj
  rfl

end CFSG.Sporadic.SuzRecog

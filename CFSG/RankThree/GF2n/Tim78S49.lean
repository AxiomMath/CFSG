module

public import CFSG.RankThree.GF2n.Tim78S48Defs
public import CFSG.RankThree.GF2n.Tim78S4Conj
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.RankThree.GF2n.Tim78S46

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_conj_inv_mul_iff {g h x : G} {U : Subgroup G} :
    x ∈ conjSubgroup (g⁻¹ * h) U ↔ g * x * g⁻¹ ∈ conjSubgroup h U := by
  rw [mem_conjSubgroup, mem_conjSubgroup]
  rw [show (g⁻¹ * h)⁻¹ * x * (g⁻¹ * h) = h⁻¹ * (g * x * g⁻¹) * h by group]

theorem card_sup_of_comm [Finite G] {X Y : Subgroup G} (hXY : X ⊓ Y = ⊥)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    Nat.card (X ⊔ Y : Subgroup G) = Nat.card X * Nat.card Y := by
  have := PartTwo.Sec6.card_sup_mul_card_inf (X := X) (N := Y) (le_normalizer_of_comm hcomm)
  rwa [hXY, Subgroup.card_bot, mul_one] at this

theorem comm_sup_of_comm {X Y : Subgroup G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hY : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ a ∈ X ⊔ Y, ∀ b ∈ X ⊔ Y, a * b = b * a := by
  intro a ha b hb
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_comm fun y hy x hx => (hXY x hx y hy).symm
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hYX ha
  obtain ⟨x', hx', y', hy', rfl⟩ := exists_mul_of_mem_sup hYX hb
  calc x * y * (x' * y') = x * (y * x') * y' := by group
    _ = x * (x' * y) * y' := by rw [hXY x' hx' y hy]
    _ = (x * x') * (y * y') := by group
    _ = (x' * x) * (y' * y) := by rw [hX x hx x' hx', hY y hy y' hy']
    _ = x' * (x * y') * y := by group
    _ = x' * (y' * x) * y := by rw [hXY x hx y' hy']
    _ = x' * y' * (x * y) := by group

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

omit [Finite G] in
theorem conj_ne_bot (g : G) : conjSubgroup g B ≠ ⊥ := by
  intro h
  apply H.B_ne_bot
  apply Subgroup.eq_bot_of_card_eq
  have := card_conjSubgroup g B
  rw [h, Subgroup.card_bot] at this
  exact this.symm

omit [Finite G] in
theorem exists_ne_one_mem_conj (g : G) : ∃ a ∈ conjSubgroup g B, a ≠ 1 := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (H.conj_ne_bot g)
  exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩

omit [Finite G] in
theorem conj_inf_Q_ne_bot {g : G} (hg : conjSubgroup g B ≤ Q) : conjSubgroup g B ⊓ Q ≠ ⊥ := by
  rw [inf_of_le_left hg]
  exact H.conj_ne_bot g

theorem inf_eq_bot_of_conj_ne {e f : G} (h : conjSubgroup e B ≠ conjSubgroup f B) :
    conjSubgroup e B ⊓ conjSubgroup f B = ⊥ := by
  have e1 : conjSubgroup f B = conjSubgroup (f * e⁻¹) (conjSubgroup e B) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  rw [e1] at h ⊢
  exact inf_conjSubgroup_eq_bot_of_isTI (isTI_conjSubgroup H.ti e) fun h' => h h'.symm

omit [Finite G] in
theorem conj_comm {g a b : G} (ha : a ∈ conjSubgroup g B) (hb : b ∈ conjSubgroup g B) :
    a * b = b * a :=
  comm_of_isElemAbelian (isElemAbelian_conjSubgroup H.elemAb g) ha hb

omit [Finite G] in
theorem conj_sq {g a : G} (ha : a ∈ conjSubgroup g B) : a * a = 1 := by
  rw [← sq]
  exact (isElemAbelian_conjSubgroup H.elemAb g).2 a ha

section Certified


theorem commutator_mul_left_of_mem_Q {u u' a : G} (hu : u ∈ Q) (hu' : u' ∈ Q) (ha : a ∈ Q) :
    ⁅u * u', a⁆ = ⁅u', a⁆ * ⁅u, a⁆ := by
  have e : ⁅u * u', a⁆ = u * ⁅u', a⁆ * u⁻¹ * ⁅u, a⁆ := by
    simp only [commutatorElement_def]; group
  have hc : ⁅u', a⁆ * u = u * ⁅u', a⁆ := H.center_Q (H.commutator_mem hu' ha) hu
  rw [e, mul_assoc u, ← mul_assoc, ← hc]
  group

theorem comm_of_comm_conj {e y u : G} (hEP : conjSubgroup e B ≤ P)
    (hEB : conjSubgroup e B ≠ B) (hy : y ∈ P) (hu : u ∈ conjSubgroup e B) (hu1 : u ≠ 1)
    (hyu : y * u = u * y) : ∀ v ∈ conjSubgroup e B, y * v = v * y := by
  intro v hv
  have hyM : y ∈ conjSubgroup e M :=
    H.centralizer_le_conj hu hu1 (Subgroup.mem_centralizer_singleton_iff.mpr hyu)
  have hyN : y ∈ Subgroup.normalizer (conjSubgroup e B : Set G) := by
    rw [H.normalizer_conj_eq]
    exact hyM
  have h1 : ⁅y, v⁆ ∈ conjSubgroup e B := by
    rw [commutatorElement_def]
    exact (conjSubgroup e B).mul_mem ((Subgroup.mem_normalizer_iff.mp hyN v).mp hv)
      ((conjSubgroup e B).inv_mem hv)
  have h2 : ⁅y, v⁆ ∈ B := H.commutator_mem (H.P_le_Q hy) (H.P_le_Q (hEP hv))
  have h3 : ⁅y, v⁆ ∈ B ⊓ conjSubgroup e B := ⟨h2, h1⟩
  rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hEB, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3

theorem comm_of_comm_pair {e f x u : G} (hEP : conjSubgroup e B ≤ P)
    (hEB : conjSubgroup e B ≠ B) (hFP : conjSubgroup f B ≤ P) (hFB : conjSubgroup f B ≠ B)
    (hx : x ∈ conjSubgroup f B) (hx1 : x ≠ 1) (hu : u ∈ conjSubgroup e B) (hu1 : u ≠ 1)
    (hxu : x * u = u * x) :
    ∀ a ∈ conjSubgroup f B, ∀ b ∈ conjSubgroup e B, a * b = b * a := by
  intro a ha b hb
  have hxb : x * b = b * x := H.comm_of_comm_conj hEP hEB (hFP hx) hu hu1 hxu b hb
  exact (H.comm_of_comm_conj hFP hFB (hEP hb) hx hx1 hxb.symm a ha).symm

theorem partition_of_le_P {g : G} (hg : conjSubgroup g B ≤ P) (hgB : conjSubgroup g B ≠ B) :
    ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
      ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U :=
  (tim78_2_18 (M := M) (V := B) (Q := Q) (P := Q ⊓ Subgroup.centralizer (B : Set G))
    (W := B ⊔ conjSubgroup g B)
    (H := (Q ⊓ Subgroup.centralizer (B : Set G)) ⊔
      conjSubgroup g (Q ⊓ Subgroup.centralizer (B : Set G))) (g := g)
    H.maxLocal H.fitting H.maxAb H.sq_eq_one H.ti H.hQ hgB (hg.trans H.P_le_Q) H.q4 rfl rfl
    rfl).2.1.1

theorem exists_member_not_comm {g : G} (hg : conjSubgroup g B ≤ P)
    (hgB : conjSubgroup g B ≠ B) :
    ∃ x : G, conjSubgroup x B ≤ P ∧ ∃ a ∈ conjSubgroup x B, ∃ e ∈ conjSubgroup g B,
      a * e ≠ e * a := by
  by_contra hnot
  push Not at hnot
  obtain ⟨e, he, he1⟩ := H.exists_ne_one_mem_conj g
  have hcomm : ∀ p ∈ P, p * e = e * p := by
    refine H.comm_P_of_comm_gens fun x hx a ha => ?_
    exact hnot x (H.conj_le_P hx) a ha e he
  have heB : e ∈ B := by
    have : e ∈ P ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hg he, Subgroup.mem_centralizer_iff.mpr fun p hp => hcomm p hp⟩
    rwa [H.inf_centralizer_P] at this
  have : e ∈ B ⊓ conjSubgroup g B := ⟨heB, he⟩
  rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hgB, Subgroup.mem_bot] at this
  exact he1 this

end Certified

section Root


theorem comm_conj_T_le_conj_B (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {g h : G} (hg : conjSubgroup g B ≤ P) (hh : conjSubgroup h B ≤ P)
    (hgB : conjSubgroup g B ≠ B)
    (hcomm : ∀ a ∈ conjSubgroup g B, ∀ b ∈ conjSubgroup h B, a * b = b * a) :
    ∀ a ∈ conjSubgroup h B, ∀ t ∈ conjSubgroup g T, ⁅a, t⁆ ∈ conjSubgroup g B := by
  intro a ha t ht
  have hgM : g ∉ M := fun h' => hgB (H.conj_eq_iff.mpr h')
  have hβ := H.tim78_4_6_beta hCen hU hgM (H.conj_inf_Q_ne_bot (hg.trans H.P_le_Q))
  obtain ⟨-, hTgM⟩ := H.T_le_conj_M_of_conj_B_le_P hg
  obtain ⟨a0, ha0, ha01⟩ := H.exists_ne_one_mem_conj g
  have haM : a ∈ conjSubgroup g M :=
    H.centralizer_le_conj ha0 ha01
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a0 ha0 a ha).symm)
  have haN : a ∈ Subgroup.normalizer (conjSubgroup g T : Set G) :=
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_T haM
  have h1 : ⁅a, t⁆ ∈ conjSubgroup g T := by
    rw [commutatorElement_def]
    exact (conjSubgroup g T).mul_mem ((Subgroup.mem_normalizer_iff.mp haN t).mp ht)
      ((conjSubgroup g T).inv_mem ht)
  have h2 : ⁅a, t⁆ ∈ P := by
    have hNP := H.M_le_normalizer_P (hTgM ht)
    have e : ⁅a, t⁆ = a * (t * a⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem (hh ha) ((Subgroup.mem_normalizer_iff.mp hNP a⁻¹).mp (P.inv_mem (hh ha)))
  rw [← hβ]
  exact ⟨h2, h1⟩

theorem conj_le_conj_P (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Step48 M B P T) {g h : G} (hg : conjSubgroup g B ≤ P) (hh : conjSubgroup h B ≤ P)
    (hgB : conjSubgroup g B ≠ B) (hhB : conjSubgroup h B ≠ B)
    (hcomm : ∀ a ∈ conjSubgroup g B, ∀ b ∈ conjSubgroup h B, a * b = b * a) :
    conjSubgroup h B ≤ conjSubgroup g P := by
  have hcomm' : ∀ a ∈ conjSubgroup h B, ∀ b ∈ conjSubgroup g B, a * b = b * a :=
    fun a ha b hb => (hcomm b hb a ha).symm
  have hF1 := H.comm_conj_T_le_conj_B hCen hU hg hh hgB hcomm
  have hF2 := H.comm_conj_T_le_conj_B hCen hU hh hg hhB hcomm'
  obtain ⟨a0, ha0, ha01⟩ := H.exists_ne_one_mem_conj g
  have hhM : conjSubgroup h B ≤ conjSubgroup g M := fun a ha =>
    H.centralizer_le_conj ha0 ha01
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a0 ha0 a ha).symm)
  have hyp : Hyp48 M B T (g⁻¹ * h) := by
    refine ⟨fun x hx => ?_, fun a ha t ht => ?_, fun b hb t ht => ?_⟩
    · have := hhM (mem_conj_inv_mul_iff.mp hx)
      rw [mem_conjSubgroup] at this
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
    · have ha' : g * a * g⁻¹ ∈ conjSubgroup h B := mem_conj_inv_mul_iff.mp ha
      have ht' : g * t * g⁻¹ ∈ conjSubgroup g T := by
        rw [mem_conjSubgroup]
        simpa [mul_assoc] using ht
      have h3 := hF1 _ ha' _ ht'
      rw [mem_conjSubgroup] at h3
      have e : g⁻¹ * ⁅g * a * g⁻¹, g * t * g⁻¹⁆ * g = ⁅a, t⁆ := by
        simp only [commutatorElement_def]; group
      rwa [e] at h3
    · have hb' : g * b * g⁻¹ ∈ conjSubgroup g B := by
        rw [mem_conjSubgroup]
        simpa [mul_assoc] using hb
      have ht' : g * t * g⁻¹ ∈ conjSubgroup h T := mem_conj_inv_mul_iff.mp ht
      have h3 := hF2 _ hb' _ ht'
      refine mem_conj_inv_mul_iff.mpr ?_
      have e : g * ⁅b, t⁆ * g⁻¹ = ⁅g * b * g⁻¹, g * t * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rwa [e]
  have := h48 (g⁻¹ * h) hyp
  intro x hx
  have hx' : g⁻¹ * x * g ∈ conjSubgroup (g⁻¹ * h) B := by
    refine mem_conj_inv_mul_iff.mpr ?_
    simpa [mul_assoc] using hx
  have := this hx'
  rw [mem_conjSubgroup]
  exact this

theorem tim78_4_9 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Step48 M B P T) :
    ∀ g h : G, conjSubgroup g B ≤ P → conjSubgroup h B ≤ P →
      conjSubgroup g B ≠ B → conjSubgroup h B ≠ B →
      (∀ a ∈ conjSubgroup g B, ∀ b ∈ conjSubgroup h B, a * b = b * a) →
      conjSubgroup h B ≤ B ⊔ conjSubgroup g B := by
  intro g h hg hh hgB hhB hcomm
  by_contra hnot
  have hE12 : conjSubgroup g B ≠ conjSubgroup h B := fun h' =>
    hnot (by rw [← h']; exact le_sup_right)
  have hinf : conjSubgroup g B ⊓ conjSubgroup h B = ⊥ := H.inf_eq_bot_of_conj_ne hE12
  have hBE1 : B ⊓ conjSubgroup g B = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hgB
  have hU12 : ∀ a ∈ conjSubgroup g B ⊔ conjSubgroup h B, ∀ b ∈ conjSubgroup g B ⊔ conjSubgroup h B,
      a * b = b * a :=
    comm_sup_of_comm (fun a ha b hb => H.conj_comm ha hb) (fun a ha b hb => H.conj_comm ha hb)
      hcomm
  have hcardU : Nat.card (conjSubgroup g B ⊔ conjSubgroup h B : Subgroup G) =
      Nat.card B * Nat.card B := by
    rw [card_sup_of_comm hinf hcomm, card_conjSubgroup, card_conjSubgroup]
  have hcardBE : Nat.card (B ⊔ conjSubgroup g B : Subgroup G) = Nat.card B * Nat.card B := by
    rw [card_sup_of_comm hBE1 (fun b hb e he => H.center_Q hb (H.P_le_Q (hg he))),
      card_conjSubgroup]
  have hE2P : conjSubgroup h B ≤ conjSubgroup g P :=
    H.conj_le_conj_P hCen hU h48 hg hh hgB hhB hcomm
  obtain ⟨x, hxP, a, ha, e, he, hae⟩ := H.exists_member_not_comm hg hgB
  have hxB : conjSubgroup x B ≠ B := by
    intro hxB
    rw [hxB] at ha
    exact hae (H.center_Q ha (H.P_le_Q (hg he)))
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hae (by simp)
  have haP : a ∈ P := hxP ha
  have hC1 : ∀ u ∈ conjSubgroup g B, a * u = u * a → u = 1 := by
    intro u hu hau
    by_contra hu1
    exact hae (H.comm_of_comm_conj hg hgB haP hu hu1 hau e he)
  let θ : conjSubgroup g B → B := fun u =>
    ⟨⁅(u : G), a⁆, H.commutator_mem (H.P_le_Q (hg u.2)) (H.P_le_Q haP)⟩
  have hθinj : Function.Injective θ := by
    intro u u' huu
    have hc : ⁅(u : G), a⁆ = ⁅(u' : G), a⁆ := congrArg Subtype.val huu
    have h1 : ⁅(u : G) * (u' : G), a⁆ = 1 := by
      rw [H.commutator_mul_left_of_mem_Q (H.P_le_Q (hg u.2)) (H.P_le_Q (hg u'.2))
        (H.P_le_Q haP), ← hc]
      have := H.sq_eq_one _ (H.commutator_mem (H.P_le_Q (hg u.2)) (H.P_le_Q haP))
      rwa [sq] at this
    have h2 : (u : G) * (u' : G) = 1 :=
      hC1 _ ((conjSubgroup g B).mul_mem u.2 u'.2)
        (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    exact Subtype.ext (mul_left_cancel (h2.trans (H.conj_sq u.2).symm)).symm
  have hθsurj : Function.Surjective θ :=
    (hθinj.bijective_of_nat_card_le (by rw [card_conjSubgroup])).2
  obtain ⟨u0, hu0, hu01⟩ := H.exists_ne_one_mem_conj h
  obtain ⟨e1, he1⟩ := hθsurj ⟨⁅u0, a⁆, H.commutator_mem (H.P_le_Q (hh hu0)) (H.P_le_Q haP)⟩
  have he1' : ⁅(e1 : G), a⁆ = ⁅u0, a⁆ := congrArg Subtype.val he1
  set w : G := u0 * (e1 : G) with hw
  have hwU : w ∈ conjSubgroup g B ⊔ conjSubgroup h B :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right hu0) (Subgroup.mem_sup_left e1.2)
  have hwa : a * w = w * a := by
    have h1 : ⁅w, a⁆ = 1 := by
      rw [hw, H.commutator_mul_left_of_mem_Q (H.P_le_Q (hh hu0)) (H.P_le_Q (hg e1.2))
        (H.P_le_Q haP), he1']
      have := H.sq_eq_one _ (H.commutator_mem (H.P_le_Q (hh hu0)) (H.P_le_Q haP))
      rwa [sq] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hwE1 : w ∉ conjSubgroup g B := by
    intro hwE
    have hu0E : u0 ∈ conjSubgroup g B := by
      have := (conjSubgroup g B).mul_mem hwE ((conjSubgroup g B).inv_mem e1.2)
      rwa [hw, mul_inv_cancel_right] at this
    have : u0 ∈ conjSubgroup g B ⊓ conjSubgroup h B := ⟨hu0E, hu0⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hu01 this
  have hw1 : w ≠ 1 := fun h' => hwE1 (h' ▸ (conjSubgroup g B).one_mem)
  have e2 : conjSubgroup (h * g⁻¹) (conjSubgroup g B) = conjSubgroup h B := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hpart := (H.conj g).partition_of_le_P (g := h * g⁻¹) (by rw [e2]; exact hE2P)
    (by rw [e2]; exact fun h' => hE12 h'.symm)
  rw [e2] at hpart
  obtain ⟨F, ⟨⟨k, hk⟩, hFU⟩, hwF⟩ := (hpart w hwU hw1).exists
  have hFk : F = conjSubgroup (k * g) B := by rw [hk, conjSubgroup_mul]
  rw [hFk] at hFU hwF
  have hFP : conjSubgroup (k * g) B ≤ P := hFU.trans (sup_le hg hh)
  have hFB : conjSubgroup (k * g) B ≠ B := by
    intro hF
    have hBU : B ≤ conjSubgroup g B ⊔ conjSubgroup h B := by
      rw [hF] at hFU
      exact hFU
    have hle : B ⊔ conjSubgroup g B ≤ conjSubgroup g B ⊔ conjSubgroup h B :=
      sup_le hBU le_sup_left
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardU, hcardBE])
    exact hnot (by rw [heq]; exact le_sup_right)
  have hFX : ∀ b' ∈ conjSubgroup (k * g) B, ∀ x' ∈ conjSubgroup x B, b' * x' = x' * b' :=
    H.comm_of_comm_pair hxP hxB hFP hFB hwF hw1 ha ha1 hwa.symm
  have hXP' : conjSubgroup x B ≤ conjSubgroup (k * g) P :=
    H.conj_le_conj_P hCen hU h48 hFP hxP hFB hxB hFX
  have hE1P' : conjSubgroup g B ≤ conjSubgroup (k * g) P :=
    H.conj_le_conj_P hCen hU h48 hFP hg hFB hgB
      (fun b' hb' c hc => hU12 b' (hFU hb') c (Subgroup.mem_sup_left hc))
  have h1 : ⁅a, e⁆ ∈ B := H.commutator_mem (H.P_le_Q haP) (H.P_le_Q (hg he))
  have h2 : ⁅a, e⁆ ∈ conjSubgroup (k * g) B := by
    have ha' := hXP' ha
    have he' := hE1P' he
    rw [mem_conjSubgroup] at ha' he' ⊢
    have hconj : (k * g)⁻¹ * ⁅a, e⁆ * (k * g) =
        ⁅(k * g)⁻¹ * a * (k * g), (k * g)⁻¹ * e * (k * g)⁆ := by
      simp only [commutatorElement_def]; group
    rw [hconj]
    exact H.commutator_mem (H.P_le_Q ha') (H.P_le_Q he')
  have h3 : ⁅a, e⁆ ∈ B ⊓ conjSubgroup (k * g) B := ⟨h1, h2⟩
  rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hFB, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h3
  exact hae h3

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

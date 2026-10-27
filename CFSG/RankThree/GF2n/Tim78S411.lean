module

public import CFSG.RankThree.GF2n.Tim78S410

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mul_conj_eq_commutator_of_mul_self_eq_one {x : G} (hx : x * x = 1) (y : G) :
    x * (y * x * y⁻¹) = ⁅x, y⁆ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  simp only [commutatorElement_def, hxi, mul_assoc]

theorem commute_conj_of_commutator_sq {x y : G} (hx : x * x = 1) (h : ⁅x, y⁆ * ⁅x, y⁆ = 1) :
    x * (y * x * y⁻¹) = (y * x * y⁻¹) * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have e2 : (y * x * y⁻¹) * x = ⁅x, y⁆⁻¹ := by
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, hxi, mul_assoc]
  rw [mul_conj_eq_commutator_of_mul_self_eq_one hx y, e2]
  exact eq_inv_of_mul_eq_one_left h

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Certified


theorem exists_member_comm_not_mem_B {x p : G} (hp : p ∈ P) (hpB : ⁅x, p⁆ ∉ B) :
    ∃ g : G, conjSubgroup g B ≤ P ∧ ∃ e ∈ conjSubgroup g B, ⁅x, e⁆ ∉ B := by
  by_contra hcon
  push Not at hcon
  have hcen : ∀ c ∈ B, ∀ y ∈ P, y * c * y⁻¹ = c := fun c hc y hy => by
    rw [← H.center_Q hc (H.P_le_Q hy)]
    group
  let K : Subgroup G :=
    { carrier := {y | y ∈ P ∧ ⁅x, y⁆ ∈ B}
      one_mem' := ⟨P.one_mem, by simp [B.one_mem]⟩
      mul_mem' := by
        rintro y y' ⟨hy, hyB⟩ ⟨hy', hy'B⟩
        refine ⟨P.mul_mem hy hy', ?_⟩
        have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e, hcen _ hy'B y hy]
        exact B.mul_mem hyB hy'B
      inv_mem' := by
        rintro y ⟨hy, hyB⟩
        refine ⟨P.inv_mem hy, ?_⟩
        have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
          simp only [commutatorElement_def]; group
        have h1 : y⁻¹ * ⁅x, y⁆⁻¹ * y = ⁅x, y⁆⁻¹ := by
          have := hcen _ (B.inv_mem hyB) y⁻¹ (P.inv_mem hy)
          simpa using this
        rw [e, h1]
        exact B.inv_mem hyB }
  have hPK : P ≤ K := by
    rw [H.hP]
    refine iSup₂_le fun g hg y hy => ?_
    exact ⟨H.conj_le_P hg hy, hcon g (H.conj_le_P hg) y hy⟩
  exact hpB (hPK hp).2

end Certified

section Root


theorem tim78_4_11 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) :
    ∀ x ∈ classD B, x ∈ M → x ∉ Q → (∀ p ∈ P, ⁅x, p⁆ ∈ B) ∨ (∀ t ∈ T, ⁅x, t⁆ ∈ B) := by
  intro x hx hxM hxQ
  by_contra hnot
  push Not at hnot
  obtain ⟨⟨p0, hp0, hp0B⟩, ⟨h, hh, hhB⟩⟩ := hnot
  obtain ⟨k, b0, hb0, hb01, hxk⟩ := hx
  have hxD : x ∈ classD B := ⟨k, b0, hb0, hb01, hxk⟩
  have hxK : x ∈ conjSubgroup k B := by
    rw [mem_conjSubgroup, hxk, show k⁻¹ * (k * b0 * k⁻¹) * k = b0 by group]
    exact hb0
  have hx1 : x ≠ 1 := by
    intro h1
    apply hb01
    calc b0 = k⁻¹ * x * k := by rw [hxk]; group
      _ = 1 := by rw [h1]; group
  have hKM : conjSubgroup k B ≤ M := hRT k b0 hb0 hb01 (hxk ▸ hxM)
  have hxC : ∀ b ∈ B, x * b = b * x := fun b hb =>
    (H.commute_of_conj_le_M hKM b hb x hxK).symm
  have hx2 : x * x = 1 := H.conj_sq hxK
  have hfirst := H.tim78_4_10_first hCen hU hRT h48
  have hsecond := H.tim78_4_10_second hCen hU hfirst
  obtain ⟨g, hgP, e0, he0, he0B⟩ := H.exists_member_comm_not_mem_B hp0 hp0B
  have hcomm1 : ∀ y : G, x * y = y * x → ⁅x, y⁆ ∈ B := fun y hy => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hy]
    exact B.one_mem
  have hgB : conjSubgroup g B ≠ B := by
    intro h'
    rw [h'] at he0
    exact he0B (hcomm1 e0 (hxC e0 he0))
  have hnc : ¬ ∀ a ∈ conjSubgroup g B, ∀ b' ∈ conjSubgroup (x * g) B, a * b' = b' * a := by
    intro hc
    have hax : ∃ a ∈ conjSubgroup g B, a * x ≠ x * a :=
      ⟨e0, he0, fun h' => he0B (hcomm1 e0 h'.symm)⟩
    have h1 := H.commutator_mem_B_of_comm hCen hU h48 hxM hx2 hx1 hxC hgP hgB hax hc e0 he0
    exact he0B (by rw [← commutatorElement_inv]; exact B.inv_mem (by simpa using h1))
  have hzT : ⁅x, h⁆ ∈ T := by
    have h1 : x * h * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_T hxM) h).mp hh
    rw [commutatorElement_def]
    exact T.mul_mem h1 (T.inv_mem hh)
  have hz2 : ⁅x, h⁆ * ⁅x, h⁆ ∈ B := by
    have := H.sq_mem (H.T_le_Q hzT)
    rwa [sq] at this
  obtain ⟨e, he, hse⟩ := H.exists_sq_eq_of_noncomm hxM hx2 hxC hgP hgB hnc _ hz2
  have heP : e ∈ P := hgP he
  have hsP : ⁅x, e⁆ ∈ P := by
    have h1 : x * e * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P hxM) e).mp heP
    rw [commutatorElement_def]
    exact P.mul_mem h1 (P.inv_mem heP)
  have hPT : ∀ y ∈ P, ∀ t ∈ T, y * t = t * y := fun y hy t ht =>
    (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) y hy)
  have hw : ⁅x, e * h⁆ = ⁅x, e⁆ * ⁅x, h⁆ := by
    have e1 : ⁅x, e * h⁆ = ⁅x, e⁆ * (e * ⁅x, h⁆ * e⁻¹) := by
      simp only [commutatorElement_def]; group
    have e2 : e * ⁅x, h⁆ * e⁻¹ = ⁅x, h⁆ := by
      rw [hPT e heP _ hzT]
      group
    rw [e1, e2]
  have hww : ⁅x, e * h⁆ * ⁅x, e * h⁆ = 1 := by
    have hcz : ⁅x, h⁆ * ⁅x, e⁆ = ⁅x, e⁆ * ⁅x, h⁆ := (hPT _ hsP _ hzT).symm
    have hbb : (⁅x, h⁆ * ⁅x, h⁆) * (⁅x, h⁆ * ⁅x, h⁆) = 1 := by
      have := H.sq_eq_one _ hz2
      rwa [sq] at this
    calc ⁅x, e * h⁆ * ⁅x, e * h⁆
        = ⁅x, e⁆ * (⁅x, h⁆ * ⁅x, e⁆) * ⁅x, h⁆ := by rw [hw]; group
      _ = (⁅x, e⁆ * ⁅x, e⁆) * (⁅x, h⁆ * ⁅x, h⁆) := by rw [hcz]; group
      _ = 1 := by rw [hse]; exact hbb
  have hw1 : ⁅x, e * h⁆ ≠ 1 := by
    intro h1
    apply hhB
    have h2 : ⁅x, h⁆ = ⁅x, e⁆⁻¹ := by
      rw [hw] at h1
      exact eq_inv_of_mul_eq_one_right h1
    have hzP : ⁅x, h⁆ ∈ P := by rw [h2]; exact P.inv_mem hsP
    have : ⁅x, h⁆ ∈ P ⊓ T := ⟨hzP, hzT⟩
    rwa [H.P_inf_T] at this
  set y : G := e * h with hy
  have hx'D : y * x * y⁻¹ ∈ classD B := mem_classD_conj hxD y
  have hcomm : x * (y * x * y⁻¹) = (y * x * y⁻¹) * x :=
    commute_conj_of_commutator_sq hx2 hww
  have hne : x ≠ y * x * y⁻¹ := by
    intro h1
    apply hw1
    rw [← mul_conj_eq_commutator_of_mul_self_eq_one hx2 y, ← h1]
    exact hx2
  have hwD : ⁅x, y⁆ ∈ classD B := by
    have := hsecond x hxD _ hx'D hcomm hne
    rwa [mul_conj_eq_commutator_of_mul_self_eq_one hx2 y] at this
  obtain ⟨j, b1, hb1, hb11, hwj⟩ := hwD
  have hwQ : ⁅x, y⁆ ∈ Q := by
    rw [hy, hw]
    exact Q.mul_mem (H.P_le_Q hsP) (H.T_le_Q hzT)
  have hwjB : ⁅x, y⁆ ∈ conjSubgroup j B := by
    rw [mem_conjSubgroup, hwj, show j⁻¹ * (j * b1 * j⁻¹) * j = b1 by group]
    exact hb1
  have hne' : conjSubgroup j B ⊓ Q ≠ ⊥ := by
    intro hbot
    have hmem : ⁅x, y⁆ ∈ conjSubgroup j B ⊓ Q := ⟨hwjB, hwQ⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  have hjP := H.tim78_4_5 hCen hU j hne'
  have hwP : ⁅x, y⁆ ∈ P := hjP hwjB
  have hzP : ⁅x, h⁆ ∈ P := by
    have h1 : ⁅x, h⁆ = ⁅x, e⁆⁻¹ * ⁅x, y⁆ := by rw [hy, hw]; group
    rw [h1]
    exact P.mul_mem (P.inv_mem hsP) hwP
  have : ⁅x, h⁆ ∈ P ⊓ T := ⟨hzP, hzT⟩
  rw [H.P_inf_T] at this
  exact hhB this

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

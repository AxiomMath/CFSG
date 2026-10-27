module

public import CFSG.RankThree.GF2n.Tim78S49
import CFSG.RankThree.GF2n.Tim78Critical
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_classD_conj {B : Subgroup G} {x : G} (hx : x ∈ classD B) (g : G) :
    g * x * g⁻¹ ∈ classD B := by
  obtain ⟨k, b, hb, hb1, rfl⟩ := hx
  exact ⟨g * k, b, hb, hb1, by group⟩

theorem conj_conj_self_of_mul_self_eq_one {x : G} (hx : x * x = 1) (y : G) :
    x * (x * y * x⁻¹) * x⁻¹ = y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rw [hxi]
  calc x * (x * y * x) * x = (x * x) * y * (x * x) := by group
    _ = y := by rw [hx]; group

theorem conj_comm_inv_of_mul_self_eq_one {x : G} (hx : x * x = 1) (e : G) :
    x * ⁅x, e⁆ * x⁻¹ = ⁅x, e⁆⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  simp only [commutatorElement_def, hxi, mul_inv_rev, inv_inv, mul_assoc]
  calc x * (x * (e * (x * (e⁻¹ * x)))) = (x * x) * (e * (x * (e⁻¹ * x))) := by group
    _ = e * (x * (e⁻¹ * x)) := by rw [hx, one_mul]

theorem comm_mul_conj_of_mul_self_eq_one {x : G} (hx : x * x = 1) (e : G) :
    ⁅x, e⁆ * x * ⁅x, e⁆⁻¹ = x * (⁅x, e⁆ * ⁅x, e⁆)⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h1 := conj_comm_inv_of_mul_self_eq_one hx e
  rw [hxi] at h1
  calc ⁅x, e⁆ * x * ⁅x, e⁆⁻¹ = (x * x) * ⁅x, e⁆ * x * ⁅x, e⁆⁻¹ := by rw [hx, one_mul]
    _ = x * (x * ⁅x, e⁆ * x) * ⁅x, e⁆⁻¹ := by group
    _ = x * ⁅x, e⁆⁻¹ * ⁅x, e⁆⁻¹ := by rw [h1]
    _ = x * (⁅x, e⁆ * ⁅x, e⁆)⁻¹ := by rw [mul_inv_rev, mul_assoc]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Certified


theorem commutator_mul_right_of_mem_Q {a s t : G} (ha : a ∈ Q) (hs : s ∈ Q) (ht : t ∈ Q) :
    ⁅a, s * t⁆ = ⁅a, s⁆ * ⁅a, t⁆ := by
  have e : ⁅a, s * t⁆ = ⁅a, s⁆ * (s * ⁅a, t⁆ * s⁻¹) := by
    simp only [commutatorElement_def]; group
  have hc : ⁅a, t⁆ * s = s * ⁅a, t⁆ := H.center_Q (H.commutator_mem ha ht) hs
  have h3 : s * ⁅a, t⁆ * s⁻¹ = ⁅a, t⁆ := by rw [← hc]; group
  rw [e, h3]

theorem commutator_conj_mul {x e f : G} (hxC : ∀ b ∈ B, x * b = b * x) (hx2 : x * x = 1)
    (he : e ∈ Q) (hf : f ∈ Q) (he' : x * e * x⁻¹ ∈ Q) (hf' : x * f * x⁻¹ ∈ Q) :
    ⁅x * (e * f) * x⁻¹, e * f⁆ = ⁅x * e * x⁻¹, e⁆ * ⁅x * f * x⁻¹, f⁆ := by
  set a1 := x * e * x⁻¹ with ha1
  set a2 := x * f * x⁻¹ with ha2
  have hxef : x * (e * f) * x⁻¹ = a1 * a2 := by rw [ha1, ha2]; group
  have hB : ∀ {c d : G}, c ∈ Q → d ∈ Q → ⁅c, d⁆ ∈ B := fun hc hd => H.commutator_mem hc hd
  have hp : ⁅a2, e⁆ ∈ B := hB hf' he
  have hq : ⁅a1, e⁆ ∈ B := hB he' he
  have hr : ⁅a2, f⁆ ∈ B := hB hf' hf
  have hs : ⁅a1, f⁆ ∈ B := hB he' hf
  have hps : ⁅a2, e⁆ * ⁅a1, f⁆ = 1 := by
    have h1 : x * ⁅a2, e⁆ * x⁻¹ = ⁅a2, e⁆ := by rw [hxC _ hp, mul_inv_cancel_right]
    have h2 : x * ⁅a2, e⁆ * x⁻¹ = ⁅a1, f⁆⁻¹ := by
      have : x * ⁅a2, e⁆ * x⁻¹ = ⁅x * a2 * x⁻¹, x * e * x⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [this, ha2, conj_conj_self_of_mul_self_eq_one hx2, ← ha1, commutatorElement_inv]
    rw [← h1, h2]
    exact inv_mul_cancel _
  rw [hxef, H.commutator_mul_right_of_mem_Q (Q.mul_mem he' hf') he hf,
    H.commutator_mul_left_of_mem_Q he' hf' he, H.commutator_mul_left_of_mem_Q he' hf' hf]
  calc ⁅a2, e⁆ * ⁅a1, e⁆ * (⁅a2, f⁆ * ⁅a1, f⁆)
      = ⁅a1, e⁆ * (⁅a2, e⁆ * ⁅a2, f⁆) * ⁅a1, f⁆ := by
        rw [H.B_comm hp hq]; group
    _ = ⁅a1, e⁆ * (⁅a2, f⁆ * ⁅a2, e⁆) * ⁅a1, f⁆ := by rw [H.B_comm hp hr]
    _ = ⁅a1, e⁆ * ⁅a2, f⁆ * (⁅a2, e⁆ * ⁅a1, f⁆) := by group
    _ = ⁅a1, e⁆ * ⁅a2, f⁆ := by rw [hps, mul_one]

theorem conj_mul_member {x g : G} (hxM : x ∈ M) (hg : conjSubgroup g B ≤ P)
    (hgB : conjSubgroup g B ≠ B) : conjSubgroup (x * g) B ≤ P ∧ conjSubgroup (x * g) B ≠ B := by
  refine ⟨?_, fun h => hgB (H.conj_eq_iff.mpr (by
    have hxg := H.conj_eq_iff.mp h
    have := M.mul_mem (M.inv_mem hxM) hxg
    simpa using this))⟩
  rw [conjSubgroup_mul]
  have h1 : conjSubgroup x (conjSubgroup g B) ≤ conjSubgroup x P := Subgroup.map_mono hg
  rwa [conjSubgroup_eq_self_iff.mpr (H.M_le_normalizer_P hxM)] at h1

theorem exists_sq_eq_of_noncomm {x : G} (hxM : x ∈ M) (hx2 : x * x = 1)
    (hxC : ∀ b ∈ B, x * b = b * x) {g : G} (hg : conjSubgroup g B ≤ P)
    (hgB : conjSubgroup g B ≠ B)
    (hnc : ¬ ∀ a ∈ conjSubgroup g B, ∀ b ∈ conjSubgroup (x * g) B, a * b = b * a) :
    ∀ b ∈ B, ∃ e ∈ conjSubgroup g B, ⁅x, e⁆ * ⁅x, e⁆ = b := by
  obtain ⟨hE'P, hE'B⟩ := H.conj_mul_member hxM hg hgB
  have hmem : ∀ e ∈ conjSubgroup g B, x * e * x⁻¹ ∈ conjSubgroup (x * g) B := by
    intro e he
    rw [mem_conjSubgroup] at he ⊢
    rw [show (x * g)⁻¹ * (x * e * x⁻¹) * (x * g) = g⁻¹ * e * g by group]
    exact he
  have hθQ : ∀ e ∈ conjSubgroup g B, ⁅x * e * x⁻¹, e⁆ ∈ B := fun e he =>
    H.commutator_mem (H.P_le_Q (hE'P (hmem e he))) (H.P_le_Q (hg he))
  let θ : conjSubgroup g B → B := fun e => ⟨⁅x * (e : G) * x⁻¹, (e : G)⁆, hθQ e e.2⟩
  have hθmul : ∀ e f : conjSubgroup g B, θ (e * f) = θ e * θ f := by
    intro e f
    refine Subtype.ext ?_
    exact H.commutator_conj_mul hxC hx2 (H.P_le_Q (hg e.2)) (H.P_le_Q (hg f.2))
      (H.P_le_Q (hE'P (hmem e e.2))) (H.P_le_Q (hE'P (hmem f f.2)))
  have hθinj : Function.Injective θ := by
    intro e f hef
    have hker : ⁅x * ((e : G) * (f : G)) * x⁻¹, (e : G) * (f : G)⁆ = 1 := by
      have h1 : θ (e * f) = θ e * θ e := by rw [hθmul, ← hef]
      have h2 := congrArg Subtype.val h1
      have h3 : (θ e : G) * (θ e : G) = 1 := by
        have := H.sq_eq_one _ (θ e).2
        rwa [sq] at this
      exact h2.trans h3
    have hef1 : (e : G) * (f : G) = 1 := by
      by_contra hne1
      have hmemef : (e : G) * (f : G) ∈ conjSubgroup g B := (conjSubgroup g B).mul_mem e.2 f.2
      have hne1' : x * ((e : G) * (f : G)) * x⁻¹ ≠ 1 := by
        intro h
        apply hne1
        calc (e : G) * (f : G) = x⁻¹ * (x * ((e : G) * (f : G)) * x⁻¹) * x := by group
          _ = 1 := by rw [h]; group
      have hall := H.comm_of_comm_pair hg hgB hE'P hE'B (hmem _ hmemef) hne1' hmemef hne1
        (commutatorElement_eq_one_iff_mul_comm.mp hker)
      exact hnc fun a ha b hb => (hall b hb a ha).symm
    exact Subtype.ext (mul_left_cancel (hef1.trans (H.conj_sq e.2).symm)).symm
  have hθsurj : Function.Surjective θ :=
    (hθinj.bijective_of_nat_card_le (by rw [card_conjSubgroup])).2
  intro b hb
  obtain ⟨e, he⟩ := hθsurj ⟨b, hb⟩
  refine ⟨e, e.2, ?_⟩
  have he' : ⁅x * (e : G) * x⁻¹, (e : G)⁆ = b := congrArg Subtype.val he
  rw [← he']
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hei : (e : G)⁻¹ = e := inv_eq_of_mul_eq_one_right (H.conj_sq e.2)
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, hxi, hei, mul_assoc]

end Certified

section Root


theorem le_conj_Q_of_centralizes_P (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {g u : G} (hu : u ∈ conjSubgroup g B) (hu1 : u ≠ 1) (huC : ∀ p ∈ P, p * u = u * p) :
    B ≤ conjSubgroup g Q := by
  by_contra hα
  have hPMg : P ≤ conjSubgroup g M := fun p hp =>
    H.centralizer_le_conj hu hu1 (Subgroup.mem_centralizer_singleton_iff.mpr (huC p hp))
  have hBMg : B ≤ conjSubgroup g M := H.B_le_P.trans hPMg
  have hMgQg : ∀ m ∈ conjSubgroup g M, ∀ z ∈ conjSubgroup g Q, m * z * m⁻¹ ∈ conjSubgroup g Q := by
    intro m hm z hz
    have : m ∈ Subgroup.normalizer (conjSubgroup g Q : Set G) := by
      rw [normalizer_conjSubgroup]
      exact Subgroup.map_mono H.M_le_normalizer_Q hm
    exact (Subgroup.mem_normalizer_iff.mp this z).mp hz
  set Qg := conjSubgroup g Q with hQg
  set E := B ⊓ Qg with hE
  have hEB : E ≤ B := inf_le_left
  have hEne : E ≠ B := fun h => hα (h ▸ inf_le_right)
  obtain ⟨Hh, hEHh, hHhB, hHh2⟩ := H.exists_hyperplane_ge hEB hEne
  have hPQg : ∀ p ∈ P, ∀ z ∈ Qg, p * z * p⁻¹ ∈ Qg := fun p hp z hz => hMgQg p (hPMg hp) z hz
  have hNle : ∀ y ∈ P, y ∈ Qg → y ∈ B := by
    intro y hyP hyQg
    refine H.center_quotient hHhB hHh2 hyP fun p hp => ?_
    have h2 : ⁅y, p⁆ ∈ Qg := by
      have e : ⁅y, p⁆ = y * (p * y⁻¹ * p⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Qg.mul_mem hyQg (hPQg p hp y⁻¹ (Qg.inv_mem hyQg))
    have h3 : ⁅y, p⁆ ∈ B := H.commutator_mem (H.P_le_Q hyP) (H.P_le_Q hp)
    exact hEHh ⟨h3, h2⟩
  have hNE : ∀ y ∈ P, y ∈ Qg → y ∈ E := fun y hy hyQg => ⟨hNle y hy hyQg, hyQg⟩
  by_cases hE0 : E = ⊥
  ·
    have hPQgbot : ∀ y ∈ P, y ∈ Qg → y = 1 := fun y hy hyQ => by
      have := hNE y hy hyQ
      rw [hE0, Subgroup.mem_bot] at this
      exact this
    have hsq : ∀ p ∈ P, p ^ 2 ∈ Qg := by
      intro p hp
      by_cases hp2 : p ^ 2 = 1
      · rw [hp2]
        exact Qg.one_mem
      have hyB : p ^ 2 ∈ B := H.sq_mem (H.P_le_Q hp)
      have hconjpow : ∀ n : ℕ, (g⁻¹ * p * g) ^ n = g⁻¹ * p ^ n * g := fun n => by
        have := conj_pow (a := g⁻¹) (b := p) (i := n)
        simpa using this
      have hy₀M : g⁻¹ * p * g ∈ M := by
        have := hPMg hp
        rwa [mem_conjSubgroup] at this
      have hy₀2 : ∃ k : ℕ, (g⁻¹ * p * g) ^ 2 ^ k = 1 := by
        obtain ⟨k, hk⟩ := H.isPGroup_P ⟨p, hp⟩
        refine ⟨k, ?_⟩
        have hk' : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
        rw [hconjpow, hk']
        group
      have hC : Q ⊓ Subgroup.centralizer ({g⁻¹ * p * g} : Set G) =
          Q ⊓ Subgroup.centralizer ({(g⁻¹ * p * g) ^ 2} : Set G) := by
        refine le_antisymm (fun c hc => ?_) (fun c hc => ?_)
        · refine ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          have h0 : Commute c (g⁻¹ * p * g) := Subgroup.mem_centralizer_singleton_iff.mp hc.2
          exact h0.pow_right 2
        · obtain ⟨hcQ, hcC⟩ := hc
          have hcC' := Subgroup.mem_centralizer_singleton_iff.mp hcC
          rw [hconjpow] at hcC'
          have hc0Q : g * c * g⁻¹ ∈ Qg := by
            rw [mem_conjSubgroup, show g⁻¹ * (g * c * g⁻¹) * g = c by group]
            exact hcQ
          have hc0C : g * c * g⁻¹ * p ^ 2 = p ^ 2 * (g * c * g⁻¹) := by
            calc g * c * g⁻¹ * p ^ 2
                = g * (c * (g⁻¹ * p ^ 2 * g)) * g⁻¹ := by group
              _ = g * ((g⁻¹ * p ^ 2 * g) * c) * g⁻¹ := by rw [hcC']
              _ = p ^ 2 * (g * c * g⁻¹) := by group
          have hc0M : g * c * g⁻¹ ∈ M :=
            (H.normalizer_eq_and_centralizer_le.2 _ hyB hp2)
              (Subgroup.mem_centralizer_singleton_iff.mpr hc0C)
          have hc0P : ∀ p' ∈ P, g * c * g⁻¹ * p' = p' * (g * c * g⁻¹) := by
            intro p' hp'
            have h1 : ⁅g * c * g⁻¹, p'⁆ ∈ P := by
              have e : ⁅g * c * g⁻¹, p'⁆ = (g * c * g⁻¹ * p' * (g * c * g⁻¹)⁻¹) * p'⁻¹ := by
                rw [commutatorElement_def]
              rw [e]
              exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp
                (H.M_le_normalizer_P hc0M) p').mp hp') (P.inv_mem hp')
            have h2 : ⁅g * c * g⁻¹, p'⁆ ∈ Qg := by
              have e : ⁅g * c * g⁻¹, p'⁆ = (g * c * g⁻¹) * (p' * (g * c * g⁻¹)⁻¹ * p'⁻¹) := by
                rw [commutatorElement_def]; group
              rw [e]
              exact Qg.mul_mem hc0Q (hPQg p' hp' _ (Qg.inv_mem hc0Q))
            have h3 := hPQgbot _ h1 h2
            rwa [commutatorElement_eq_one_iff_mul_comm] at h3
          refine ⟨hcQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          have := hc0P p hp
          calc c * (g⁻¹ * p * g) = g⁻¹ * ((g * c * g⁻¹) * p) * g := by group
            _ = g⁻¹ * (p * (g * c * g⁻¹)) * g := by rw [this]
            _ = g⁻¹ * p * g * c := by group
      have h23 := tim78_2_3 H.fitting hy₀M hy₀2 (by rw [← H.hQ]; exact hC)
      rw [← H.hQ, hconjpow] at h23
      rw [hQg, mem_conjSubgroup]
      exact h23
    refine absurd ?_ hα
    rw [← H.mho_eq_B_of_ne H.B_le_P H.P_le_Q H.M_le_normalizer_P H.B_lt_P.ne]
    exact CFSG.GroupTheory.HuppertProduct.mho_le_of_forall hsq
  ·
    refine absurd (H.le_conj_Q_of_normalizer_eq hCen hU hBMg hEB inf_le_right hE0 ?_) hα
    intro c hcQg hcN b hb
    have hcM : c ∈ M := H.mem_M_of_normalizes hEB hE0 hcN
    refine H.comm_B_of_commutator_mem (c := c) (fun y hy => ?_) b hb
    have h1 : ⁅c, y⁆ ∈ P := by
      have e : ⁅c, y⁆ = (c * y * c⁻¹) * y⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P hcM) y).mp hy)
        (P.inv_mem hy)
    have h2 : ⁅c, y⁆ ∈ Qg := by
      have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Qg.mul_mem hcQg (hPQg y hy c⁻¹ (Qg.inv_mem hcQg))
    exact hNle _ h1 h2

theorem commutator_mem_B_of_comm (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Step48 M B P T) {x : G} (hxM : x ∈ M) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxC : ∀ b ∈ B, x * b = b * x) {g : G} (hg : conjSubgroup g B ≤ P)
    (hgB : conjSubgroup g B ≠ B) (hax : ∃ a ∈ conjSubgroup g B, a * x ≠ x * a)
    (hc : ∀ a ∈ conjSubgroup g B, ∀ b ∈ conjSubgroup (x * g) B, a * b = b * a) :
    ∀ e ∈ conjSubgroup g B, ⁅e, x⁆ ∈ B := by
  obtain ⟨hE'P, hE'B⟩ := H.conj_mul_member hxM hg hgB
  have h49 := H.tim78_4_9 hCen hU h48 g (x * g) hg hE'P hgB hE'B hc
  have hBE : B ⊓ conjSubgroup g B = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hgB
  have hBEc : ∀ b ∈ B, ∀ e ∈ conjSubgroup g B, b * e = e * b := fun b hb e he =>
    H.center_Q hb (H.P_le_Q (hg he))
  have hUel : Assembly.IsElemAbelian 2 (B ⊔ conjSubgroup g B) :=
    CFSG.Open.IsElemAbelian.sup_of_commute H.elemAb (isElemAbelian_conjSubgroup H.elemAb g) hBEc
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp H.isPGroup_B
  have hcardU : Nat.card (B ⊔ conjSubgroup g B : Subgroup G) = 2 ^ (2 * n) := by
    rw [card_sup_of_comm hBE hBEc, card_conjSubgroup, hn, ← pow_add, ← two_mul]
  have hxU : x ∈ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
    have hsup : conjSubgroup x (B ⊔ conjSubgroup g B) =
        conjSubgroup x B ⊔ conjSubgroup x (conjSubgroup g B) := Subgroup.map_sup _ _ _
    have hle : conjSubgroup x (B ⊔ conjSubgroup g B) ≤ B ⊔ conjSubgroup g B := by
      rw [hsup, H.conj_eq_iff.mpr hxM, ← conjSubgroup_mul]
      exact sup_le le_sup_left h49
    have heq : conjSubgroup x (B ⊔ conjSubgroup g B) = B ⊔ conjSubgroup g B :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
    exact conjSubgroup_eq_self_iff.mp heq
  obtain ⟨⟨b1, hb1⟩, hb11⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp H.B_ne_bot
  have hb11' : b1 ≠ 1 := fun h => hb11 (Subtype.ext h)
  obtain ⟨e1, he1, he11⟩ := H.exists_ne_one_mem_conj g
  have hwU : b1 * e1 ∈ B ⊔ conjSubgroup g B :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hb1) (Subgroup.mem_sup_right he1)
  have hw1 : b1 * e1 ≠ 1 := by
    intro h
    have : e1 ∈ B ⊓ conjSubgroup g B := ⟨by
      have := B.mul_mem (B.inv_mem hb1) (show b1 * e1 ∈ B from by rw [h]; exact B.one_mem)
      simpa using this, he1⟩
    rw [hBE, Subgroup.mem_bot] at this
    exact he11 this
  obtain ⟨F, ⟨⟨k, hk⟩, hFU⟩, hwF⟩ := (H.partition_of_le_P hg hgB _ hwU hw1).exists
  have hFB : F ≠ B := by
    intro hFB'
    rw [hFB'] at hwF
    have : e1 ∈ B ⊓ conjSubgroup g B := ⟨by
      have := B.mul_mem (B.inv_mem hb1) hwF
      simpa using this, he1⟩
    rw [hBE, Subgroup.mem_bot] at this
    exact he11 this
  have hFE : F ≠ conjSubgroup g B := by
    intro h
    rw [h] at hwF
    have : b1 ∈ B ⊓ conjSubgroup g B := ⟨hb1, by
      have := (conjSubgroup g B).mul_mem hwF ((conjSubgroup g B).inv_mem he1)
      simpa using this⟩
    rw [hBE, Subgroup.mem_bot] at this
    exact hb11' this
  have hcls : 3 ≤ (classIn B (B ⊔ conjSubgroup g B)).ncard := by
    have h3 : 2 < (classIn B (B ⊔ conjSubgroup g B)).ncard :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).mpr ⟨B, conjSubgroup g B, F,
        ⟨⟨1, (conjSubgroup_one B).symm⟩, le_sup_left⟩, ⟨⟨g, rfl⟩, le_sup_right⟩,
        ⟨⟨k, hk⟩, hFU⟩, fun h => hgB h.symm, fun h => hFB h.symm, fun h => hFE h.symm⟩
    exact h3
  have hxCB : B ≤ Subgroup.centralizer ({x} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hxC b hb).symm
  have hxord : orderOf x = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have h217 := tim78_2_17 hUel hcardU hn H.ti le_sup_left hcls hxU hxCB hxord
  rcases h217 with h0 | hB
  · exfalso
    obtain ⟨a, ha, hax⟩ := hax
    have haU : a ∈ B ⊔ conjSubgroup g B := Subgroup.mem_sup_right ha
    have := Subgroup.commutator_mem_commutator haU (Subgroup.mem_zpowers x)
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hax this
  · intro e he
    have heU : e ∈ B ⊔ conjSubgroup g B := Subgroup.mem_sup_right he
    have := Subgroup.commutator_mem_commutator heU (Subgroup.mem_zpowers x)
    rwa [hB] at this

theorem exists_conj_eq_mul_of_comm (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (h48 : Step48 M B P T) {x : G} (hxM : x ∈ M)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxC : ∀ b ∈ B, x * b = b * x) {g : G}
    (hg : conjSubgroup g B ≤ P) (hgB : conjSubgroup g B ≠ B)
    (hax : ∃ a ∈ conjSubgroup g B, a * x ≠ x * a)
    (hc : ∀ a ∈ conjSubgroup g B, ∀ b ∈ conjSubgroup (x * g) B, a * b = b * a) :
    ∀ b ∈ B, ∃ z : G, z * x * z⁻¹ = x * b := by
  have hcB := H.commutator_mem_B_of_comm hCen hU h48 hxM hx2 hx1 hxC hg hgB hax hc
  have hC1 : ∀ u ∈ conjSubgroup g B, u ≠ 1 → x * u = u * x → False := by
    intro u hu hu1 hxu
    have hxM' : x ∈ conjSubgroup g M :=
      H.centralizer_le_conj hu hu1 (Subgroup.mem_centralizer_singleton_iff.mpr hxu)
    have hxN : x ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
      rw [H.normalizer_conj_eq]
      exact hxM'
    obtain ⟨a, ha, hax⟩ := hax
    have h1 : ⁅a, x⁆ ∈ conjSubgroup g B := by
      have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (conjSubgroup g B).mul_mem ha
        ((Subgroup.mem_normalizer_iff.mp hxN a⁻¹).mp ((conjSubgroup g B).inv_mem ha))
    have h2 : ⁅a, x⁆ ∈ B ⊓ conjSubgroup g B := ⟨hcB a ha, h1⟩
    rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hgB, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h2
    exact hax h2
  let θ : conjSubgroup g B → B := fun e => ⟨⁅(e : G), x⁆, hcB e e.2⟩
  have hθinj : Function.Injective θ := by
    intro e f hef
    have hc1 : ⁅(e : G), x⁆ = ⁅(f : G), x⁆ := congrArg Subtype.val hef
    have hsq : ⁅(e : G), x⁆ * ⁅(e : G), x⁆ = 1 := by
      have := H.sq_eq_one _ (hcB e e.2)
      rwa [sq] at this
    have h1 : ⁅(e : G) * (f : G), x⁆ = 1 := by
      have hform : ⁅(e : G) * (f : G), x⁆ = (e : G) * ⁅(f : G), x⁆ * (e : G)⁻¹ * ⁅(e : G), x⁆ := by
        simp only [commutatorElement_def]; group
      have hcen : (e : G) * ⁅(f : G), x⁆ * (e : G)⁻¹ = ⁅(f : G), x⁆ := by
        rw [← H.center_Q (hcB f f.2) (H.P_le_Q (hg e.2))]
        group
      rw [hform, hcen, ← hc1, hsq]
    have hef1 : (e : G) * (f : G) = 1 := by
      by_contra hne1
      exact hC1 _ ((conjSubgroup g B).mul_mem e.2 f.2) hne1
        (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    exact Subtype.ext (mul_left_cancel (hef1.trans (H.conj_sq e.2).symm)).symm
  have hθsurj : Function.Surjective θ :=
    (hθinj.bijective_of_nat_card_le (by rw [card_conjSubgroup])).2
  intro b hb
  obtain ⟨e, he⟩ := hθsurj ⟨b, hb⟩
  refine ⟨e, ?_⟩
  have he' : ⁅(e : G), x⁆ = b := congrArg Subtype.val he
  have : (e : G) * x * (e : G)⁻¹ = ⁅(e : G), x⁆ * x := by
    simp only [commutatorElement_def]; group
  rw [this, he', hxC b hb]

theorem not_centralizes_P (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {k x : G} (hx : x ∈ conjSubgroup k B) (hx1 : x ≠ 1) (hxQ : x ∉ Q) :
    ¬ ∀ p ∈ P, p * x = x * p := by
  intro hC
  have hα := H.le_conj_Q_of_centralizes_P hCen hU hx hx1 hC
  have h1 : conjSubgroup k⁻¹ B ≤ Q := by
    intro z hz
    rw [mem_conjSubgroup, inv_inv] at hz
    have := hα hz
    rwa [mem_conjSubgroup, show k⁻¹ * (k * z * k⁻¹) * k = z by group] at this
  have h2 : conjSubgroup k B ≤ Q := by
    have := H.conj_inv_le_Q h1
    rwa [inv_inv] at this
  exact hxQ (h2 hx)

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

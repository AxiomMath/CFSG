module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA2
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.HardMathSupport.U4FF.SmallGL
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Linear
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309 (eSum eSum_apply eSum_apply_of_mem_fixSub
  eSum_apply_sub_one odd_nsmul_eq_self)

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem isCompl_commOn_fixSub_of_odd {X : Subgroup G} [Finite ↥X] (hX : Odd (Nat.card ↥X)) :
    IsCompl (commOn ρ X ⊤) (fixSub ρ X) := by
  classical
  haveI : Fintype ↥X := Fintype.ofFinite _
  have hodd : Odd (Fintype.card ↥X) := Nat.card_eq_fintype_card (α := ↥X) ▸ hX
  have hfix : ∀ v ∈ fixSub ρ X, eSum ρ X v = v := fun v hv =>
    eSum_apply_of_mem_fixSub hodd (RankFourTheoremC.PEmpty.KD309.mem_fixSub.2 (mem_fixSub.1 hv))
  have hker : ∀ v ∈ commOn ρ X ⊤, eSum ρ X v = 0 := by
    have hle : commOn ρ X ⊤ ≤ LinearMap.ker (eSum ρ X) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, u, -, rfl⟩
      have h := eSum_apply_sub_one (ρ := ρ) hx u
      rw [LinearMap.sub_apply, Module.End.one_apply] at h
      exact h
    exact fun v hv => hle hv
  have himg : ∀ v, eSum ρ X v ∈ fixSub ρ X := fun v => by
    rw [mem_fixSub]
    intro y hy
    rw [eSum_apply, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨y, hy⟩ : ↥X)) _ _ fun h => by
      rw [Equiv.coe_mulLeft, Subgroup.coe_mul, Subgroup.coe_mk, map_mul, Module.End.mul_apply]
  have hsub : ∀ v, v - eSum ρ X v ∈ commOn ρ X ⊤ := fun v => by
    have hmem : ∑ x : ↥X, (ρ x v - v) ∈ commOn ρ X ⊤ :=
      Submodule.sum_mem _ fun x _ => sub_mem_commOn x.2 Submodule.mem_top
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      odd_nsmul_eq_self hodd,
      ← eSum_apply] at hmem
    simpa only [neg_sub] using neg_mem hmem
  refine ⟨Submodule.disjoint_def.2 fun v h₁ h₂ => ?_, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
  · rw [← hfix v h₂]
    exact hker v h₁
  · intro v _
    exact Submodule.mem_sup.2 ⟨_, hsub v, _, himg v, sub_add_cancel _ _⟩

theorem cenOn_commOn_eq_bot_of_odd (hρ : Function.Injective ρ) {X : Subgroup G}
    (hodd : ∀ x ∈ X, Odd (orderOf x)) : cenOn ρ X (commOn ρ X ⊤) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun x hx => eq_one_of_fixes_commOn hρ hx.1 (hodd x hx.1) hx.2

private theorem odd_orderOf_of_card_three {Q : Subgroup G} (hQ3 : Nat.card ↥Q = 3) :
    ∀ x ∈ Q, Odd (orderOf x) := fun x hx =>
  Odd.of_dvd_nat (by rw [hQ3]; decide) (Subgroup.orderOf_dvd_natCard Q hx)

theorem not_forall_apply_eq_of_inverts (hρ : Function.Injective ρ) {Q : Subgroup G} {b q : G}
    (hQ3 : Nat.card ↥Q = 3) (hb : ∀ x ∈ Q, b * x * b⁻¹ = x⁻¹) (hq : q ∈ Q) :
    ¬ ∀ u ∈ commOn ρ Q ⊤, ρ b u = ρ q u := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQ3]; norm_num)
  have hQinv := (invariant_commOn_top (ρ := ρ) (A := Q) (L := Q) Subgroup.le_normalizer).1
  obtain hbot | ⟨x, hxQ, hx1⟩ := Subgroup.bot_or_exists_ne_one Q
  · rw [hbot, Subgroup.card_bot] at hQ3
    omega
  have hcyc : IsCyclic ↥Q := isCyclic_of_prime_card hQ3
  have hxq : q * x = x * q := congrArg Subtype.val (hcyc.commGroup.mul_comm ⟨q, hq⟩ ⟨x, hxQ⟩)
  have hbinv : ∀ u ∈ commOn ρ Q ⊤, ρ b⁻¹ u = ρ q⁻¹ u := fun u hu => by
    have h1 := h _ (hQinv _ (Q.inv_mem hq) u hu)
    rw [glRep_apply_inv] at h1
    calc ρ b⁻¹ u = ρ b⁻¹ (ρ b (ρ q⁻¹ u)) := by rw [h1]
      _ = ρ q⁻¹ u := glRep_inv_apply ρ b _
  have hxx : ∀ u ∈ commOn ρ Q ⊤, ρ x⁻¹ u = ρ x u := fun u hu => by
    have e1 : ρ x⁻¹ u = ρ b (ρ x (ρ b⁻¹ u)) := by
      rw [← hb x hxQ, glRep_mul_apply, glRep_mul_apply]
    have e2 : q * x * q⁻¹ = x := by rw [hxq, mul_inv_cancel_right]
    rw [e1, hbinv u hu, h _ (hQinv _ hxQ _ (hQinv _ (Q.inv_mem hq) u hu)), ← glRep_mul_apply,
      ← glRep_mul_apply, e2]
  have hsq : x * x = 1 := eq_one_of_fixes_commOn hρ (Q.mul_mem hxQ hxQ)
    (odd_orderOf_of_card_three hQ3 _ (Q.mul_mem hxQ hxQ)) fun u hu => by
      rw [glRep_mul_apply, ← hxx u hu, glRep_apply_inv]
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have h3 : orderOf x ∣ 3 := hQ3 ▸ Subgroup.orderOf_dvd_natCard Q hxQ
  have h1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_one ((by decide : Nat.gcd 2 3 = 1) ▸ Nat.dvd_gcd h2 h3)
  exact hx1 (orderOf_eq_one_iff.1 h1)

private theorem eq_six_of_dvd {n : ℕ} (h3 : 3 ∣ n) (h6 : n ∣ 6) (hne : n ≠ 3) : n = 6 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases n <;> omega

theorem exists_eq_apply_of_card_three [Finite V] (hρ : Function.Injective ρ) {Q : Subgroup G}
    {b g : G} (hQ3 : Nat.card ↥Q = 3) (hQV : Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) = 2)
    (hb : ∀ x ∈ Q, b * x * b⁻¹ = x⁻¹) (hbN : b ∈ Subgroup.normalizer (Q : Set G))
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    ∃ h ∈ Q ⊔ Subgroup.zpowers b, ∀ u ∈ commOn ρ Q ⊤, ρ g u = ρ h u := by
  have hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (Subgroup.normalizer (Q : Set G)) (commOn ρ Q ⊤) :=
    (invariant_commOn_top (ρ := ρ) (A := Subgroup.normalizer (Q : Set G)) (L := Q) le_rfl).2
  have hQN : Q ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer
  have hBN : Q ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hQN (Subgroup.zpowers_le.2 hbN)
  have hGL : Nat.card (↥(commOn ρ Q ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ Q ⊤)) = 6 := by
    rw [CFSG.HardMathSupport.U4FF.card_linearEquiv_eq_prod hQV, Fin.prod_univ_two]
    norm_num
  haveI : Finite (↥(commOn ρ Q ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ Q ⊤)) :=
    Nat.finite_of_card_ne_zero (by rw [hGL]; norm_num)
  have hIQ : Nat.card ↥(imgGL ρ _ _ hU Q) = 3 := by
    have h := card_imgGL_mul_card_cenOn (hU := hU) hQN
    rwa [cenOn_commOn_eq_bot_of_odd hρ (odd_orderOf_of_card_three hQ3), Subgroup.card_bot,
      mul_one, hQ3] at h
  have hle : imgGL ρ _ _ hU Q ≤ imgGL ρ _ _ hU (Q ⊔ Subgroup.zpowers b) := imgGL_mono le_sup_left
  have hbI : resGL ρ _ _ hU ⟨b, hbN⟩ ∈ imgGL ρ _ _ hU (Q ⊔ Subgroup.zpowers b) :=
    resGL_mem_imgGL (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) hbN
  have hbQ : resGL ρ _ _ hU ⟨b, hbN⟩ ∉ imgGL ρ _ _ hU Q := by
    intro hx
    obtain ⟨q, hqQ, hqb⟩ := mem_imgGL.1 hx
    refine not_forall_apply_eq_of_inverts hρ hQ3 hb hqQ fun u hu => ?_
    exact (congrArg (fun f : ↥(commOn ρ Q ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ Q ⊤) =>
      ((f ⟨u, hu⟩ : ↥(commOn ρ Q ⊤)) : V)) hqb).symm
  have htop : imgGL ρ _ _ hU (Q ⊔ Subgroup.zpowers b) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hGL]
    refine eq_six_of_dvd (hIQ ▸ Subgroup.card_dvd_of_le hle)
      (hGL ▸ Subgroup.card_subgroup_dvd_card _) fun h3 => hbQ ?_
    rwa [Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hIQ])]
  obtain ⟨h, hhB, hh⟩ := mem_imgGL.1 (htop ▸ Subgroup.mem_top (resGL ρ _ _ hU ⟨g, hg⟩))
  refine ⟨h, hhB, fun u hu => ?_⟩
  exact (congrArg (fun f : ↥(commOn ρ Q ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ Q ⊤) =>
    ((f ⟨u, hu⟩ : ↥(commOn ρ Q ⊤)) : V)) hh).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148

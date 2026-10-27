module

public import CFSG.RankThree.GF2n.Tim78S4RootCase2
public import CFSG.RankThree.GF2n.Tim78S43
public import CFSG.RankThree.GF2n.Tim78S4RootReduce

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

theorem mem_T_of_commutator_le_hyperplane {Hh : Subgroup G} (hHB : Hh ≤ B)
    (hH2 : Nat.card Hh * 2 = Nat.card B) {x : G} (hx : x ∈ Q) (h : ∀ p ∈ P, ⁅x, p⁆ ∈ Hh) :
    x ∈ T := by
  have hcomm := H.comm_P_of_comm_gens (y := x) fun g hg a ha => by
    have h1 := H.commute_of_commutator_le_hyperplane hHB hH2 hx (H.conj_le_P hg)
      (fun a ha => h a (H.conj_le_P hg ha)) a ha
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  rw [H.hT]
  exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr fun p hp => hcomm p hp⟩

theorem rootTypeStep_direct : RootTypeStep M B := by
  classical
  intro g b hb hb1 hgb
  by_contra hgM
  set A := conjSubgroup g B with hA
  set A₀ := A ⊓ M with hA₀
  have h1 : RootStep1 M B Q g := H.rootStep1_of_not_le_M hgM
  have hE := isElemAbelian_conjSubgroup H.elemAb g
  set a₀ : G := g * b * g⁻¹ with ha₀def
  have ha₀A : a₀ ∈ A := by
    rw [hA, mem_conjSubgroup, ha₀def, show g⁻¹ * (g * b * g⁻¹) * g = b by group]
    exact hb
  have ha₀ : a₀ ∈ A₀ := Subgroup.mem_inf.mpr ⟨ha₀A, hgb⟩
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    apply hb1
    calc b = g⁻¹ * a₀ * g := by rw [ha₀def]; group
      _ = 1 := by rw [h]; group
  have ha₀2 : a₀ * a₀ = 1 := by rw [← sq]; exact hE.2 a₀ ha₀A
  have ha₀inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀2
  set L : Subgroup G := ⨆ (y : G) (_ : y ∈ Q), conjSubgroup y A₀ with hL
  have hA₀L : A₀ ≤ L := by
    have := le_iSup₂_of_le (f := fun (y : G) (_ : y ∈ Q) => conjSubgroup y A₀) 1 (one_mem Q)
      le_rfl
    rwa [conjSubgroup_one] at this
  have hconjL : ∀ a ∈ A₀, ∀ y ∈ Q, y⁻¹ * a * y ∈ L := by
    intro a ha y hy
    refine Subgroup.mem_iSup_of_mem y⁻¹ (Subgroup.mem_iSup_of_mem (inv_mem hy) ?_)
    rw [mem_conjSubgroup, show y⁻¹⁻¹ * (y⁻¹ * a * y) * y⁻¹ = a by group]
    exact ha
  have hQL : ∀ q ∈ Q, ∀ s ∈ L, q * s * q⁻¹ ∈ L := by
    intro q hq s hs
    have hq' : ∀ y ∈ Q, conjSubgroup q (conjSubgroup y A₀) ≤ L := by
      intro y hy
      rw [← conjSubgroup_mul]
      exact le_iSup₂_of_le (f := fun (y : G) (_ : y ∈ Q) => conjSubgroup y A₀) (q * y)
        (mul_mem hq hy) le_rfl
    have key : conjSubgroup q L ≤ L := by
      rw [hL]
      unfold conjSubgroup
      rw [Subgroup.map_iSup]
      refine iSup_le fun y => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hy => hq' y hy
    exact key (mem_conjSubgroup.mpr (by rw [show q⁻¹ * (q * s * q⁻¹) * q = s by group]; exact hs))
  have hLc : ∀ a ∈ A₀, L ≤ Subgroup.centralizer ({a} : Set G) := by
    intro a ha
    refine iSup₂_le fun y hy s hs => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (H.comm_of_mem_conj_of_rootStep1 hgM h1 ha hy hs).symm
  have hfin : (∀ b' ∈ B, a₀ * b' = b' * a₀) → False := by
    intro hc
    apply hgM
    refine H.conj_le_M_of_le_conj fun b' hb' => ?_
    exact H.toRootCore.centralizer_le_conj ha₀A ha₀1
      (Subgroup.mem_centralizer_singleton_iff.mpr (hc b' hb').symm)
  by_cases hBL : B ≤ L
  · exact hfin fun b' hb' =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hLc a₀ ha₀ (hBL hb'))).symm
  ·
    obtain ⟨Hh, hDH, hHB, hH2⟩ := H.exists_hyperplane_ge (E := L ⊓ B) inf_le_right
      (fun h => hBL (h ▸ inf_le_left))
    have hLT : ∀ x ∈ L, x ∈ Q → x ∈ T := by
      intro x hxL hxQ
      refine H.mem_T_of_commutator_le_hyperplane hHB hH2 hxQ fun p hp => ?_
      have h1' : ⁅x, p⁆ ∈ L := by
        rw [show ⁅x, p⁆ = x * (p * x⁻¹ * p⁻¹) by rw [commutatorElement_def]; group]
        exact L.mul_mem hxL (hQL p (H.P_le_Q hp) x⁻¹ (L.inv_mem hxL))
      exact hDH ⟨h1', H.commutator_mem hxQ (H.P_le_Q hp)⟩
    have ha₀M : a₀ ∈ M := hgb
    have hcy : ∀ y ∈ P, a₀ * (y⁻¹ * a₀ * y) ∈ B := by
      intro y hy
      have hcL : a₀ * (y⁻¹ * a₀ * y) ∈ L :=
        L.mul_mem (hA₀L ha₀) (hconjL a₀ ha₀ y (H.P_le_Q hy))
      have hsplit : a₀ * (y⁻¹ * a₀ * y) = (a₀ * y⁻¹ * a₀⁻¹) * y := by
        rw [ha₀inv]; group
      have hP' : (a₀ * y⁻¹ * a₀⁻¹) ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P ha₀M) y⁻¹).mp (inv_mem hy)
      have hcP : a₀ * (y⁻¹ * a₀ * y) ∈ P := by rw [hsplit]; exact P.mul_mem hP' hy
      have hcQ : a₀ * (y⁻¹ * a₀ * y) ∈ Q := H.P_le_Q hcP
      have hcT := hLT _ hcL hcQ
      have : a₀ * (y⁻¹ * a₀ * y) ∈ P ⊓ T := Subgroup.mem_inf.mpr ⟨hcP, hcT⟩
      rwa [H.P_inf_T] at this
    refine hfin (H.comm_B_of_commutator_mem fun y hy => ?_)
    have := hcy y⁻¹ (inv_mem hy)
    rwa [show a₀ * (y⁻¹⁻¹ * a₀ * y⁻¹) = ⁅a₀, y⁆ by
      rw [commutatorElement_def, ha₀inv]; group] at this

end Hyp4

end CFSG.RankThree.GF2n.Tim78

module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveH
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveI
public import CFSG.RankThree.GF2n.DecompSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n (DecompSetup QuotPair)
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def imgN (M V : Subgroup G) (g : G)
    [((NOf M V g).subgroupOf (LOf V g)).Normal] (A : Subgroup G) :
    Subgroup (↥(LOf V g) ⧸ (NOf M V g).subgroupOf (LOf V g)) :=
  (A.subgroupOf (LOf V g)).map (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)))

section Bookkeeping

variable (M V : Subgroup G) (g : G) [((NOf M V g).subgroupOf (LOf V g)).Normal]

theorem mk_eq_one_iff_mem_N (y : ↥(LOf V g)) :
    QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y = 1 ↔ (y : G) ∈ NOf M V g := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem s65_SixFiveQuot_mem_N_of_comm {y y' : ↥(LOf V g)}
    (hc : QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y' =
      QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y' *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y) :
    (y : G) * y' * y⁻¹ * y'⁻¹ ∈ NOf M V g := by
  have h : QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⁅y, y'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hc]
  have hmem := (mk_eq_one_iff_mem_N M V g ⁅y, y'⁆).1 h
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hmem

private theorem s65_SixFiveQuot_comm_of_mem_N {y y' : ↥(LOf V g)}
    (h : (y : G) * y' * y⁻¹ * y'⁻¹ ∈ NOf M V g) :
    QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y' =
      QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y' *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  exact (mk_eq_one_iff_mem_N M V g ⁅y, y'⁆).2 (by
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h)

private theorem s65_SixFiveQuot_comm_of_mem_abelian {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {y y' : ↥(LOf V g)} (hy : (y : G) ∈ A) (hy' : (y' : G) ∈ A) :
    QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y' =
      QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y' *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) y := by
  have h : (y : ↥(LOf V g)) * y' = y' * y := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hA.comm hy hy')
  rw [← map_mul, ← map_mul, h]

private theorem s65_SixFiveQuot_pi_eq_mul {k b u : G} (hk : k = b * u)
    (hbL : b ∈ LOf V g) (huL : u ∈ LOf V g) (hkL : k ∈ LOf V g) :
    QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨k, hkL⟩ =
      QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b, hbL⟩ *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u, huL⟩ := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext (by rw [Subgroup.coe_mul]; exact hk)

end Bookkeeping

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem N_normal (h : Hyp65 n M V₀ V g) : ((NOf M V g).subgroupOf (LOf V g)).Normal := by
  have hNL : NOf M V g ≤ LOf V g := by
    rw [NOf, UOf, LOf]
    exact inf_le_left.trans (inf_le_left.trans le_sup_left)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2 ?_
  intro x hx
  exact conjSubgroup_eq_iff_mem_normalizer.mp (conjSubgroup_N_eq h hx)

theorem commutator_K_K_mem_N (h : Hyp65 n M V₀ V g) :
    ∀ k ∈ KOf M V g, ∀ k' ∈ KOf M V g, k * k' * k⁻¹ * k'⁻¹ ∈ NOf M V g := by
  haveI := N_normal h
  intro k hk k' hk'
  have hkL : k ∈ LOf V g := KOf_le_LOf M V g hk
  have hkL' : k' ∈ LOf V g := KOf_le_LOf M V g hk'
  change k ∈ (KOf M V g : Set G) at hk
  change k' ∈ (KOf M V g : Set G) at hk'
  rw [K_coe_eq_mul h, Set.mem_mul] at hk hk'
  obtain ⟨b, hbB, u, huU, hk_eq⟩ := hk
  obtain ⟨b', hbB', u', huU', hk_eq'⟩ := hk'
  have hbL : b ∈ LOf V g := by
    rw [LOf]
    exact (le_sup_right : conjSubgroup V g ≤ V ⊔ conjSubgroup V g) hbB.1
  have huL : u ∈ LOf V g := by
    rw [LOf]
    exact (le_sup_left : V ≤ V ⊔ conjSubgroup V g) huU.1
  have hbL' : b' ∈ LOf V g := by
    rw [LOf]
    exact (le_sup_right : conjSubgroup V g ≤ V ⊔ conjSubgroup V g) hbB'.1
  have huL' : u' ∈ LOf V g := by
    rw [LOf]
    exact (le_sup_left : V ≤ V ⊔ conjSubgroup V g) huU'.1
  have hkLprod : b * u ∈ LOf V g := (LOf V g).mul_mem hbL huL
  have hkLprod' : b' * u' ∈ LOf V g := (LOf V g).mul_mem hbL' huL'
  have hkeq : (⟨k, hkL⟩ : ↥(LOf V g)) = ⟨b * u, hkLprod⟩ := Subtype.ext hk_eq.symm
  have hkeq' : (⟨k', hkL'⟩ : ↥(LOf V g)) = ⟨b' * u', hkLprod'⟩ := Subtype.ext hk_eq'.symm
  have hcomm : QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨k, hkL⟩ *
      QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨k', hkL'⟩ =
      QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨k', hkL'⟩ *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨k, hkL⟩ := by
    rw [hkeq, hkeq',
      s65_SixFiveQuot_pi_eq_mul (M := M) (V := V) (g := g) rfl hbL huL hkLprod,
      s65_SixFiveQuot_pi_eq_mul (M := M) (V := V) (g := g) rfl hbL' huL' hkLprod']
    have hbb' : Commute (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b, hbL⟩)
        (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b', hbL'⟩) :=
      s65_SixFiveQuot_comm_of_mem_abelian (M := M) (V := V) (g := g) h.swap.elemAbelian
        hbB.1 hbB'.1
    have huu' : Commute (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u, huL⟩)
        (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u', huL'⟩) :=
      s65_SixFiveQuot_comm_of_mem_abelian (M := M) (V := V) (g := g) h.elemAbelian
        huU.1 huU'.1
    have hbu : Commute (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b, hbL⟩)
        (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u, huL⟩) :=
      (s65_SixFiveQuot_comm_of_mem_N (M := M) (V := V) (g := g)
        (commutator_U_B_le_N h (Subgroup.commutator_mem_commutator huU hbB))).symm
    have hbu' : Commute (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b, hbL⟩)
        (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u', huL'⟩) :=
      (s65_SixFiveQuot_comm_of_mem_N (M := M) (V := V) (g := g)
        (commutator_U_B_le_N h (Subgroup.commutator_mem_commutator huU' hbB))).symm
    have hub' : Commute (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u, huL⟩)
        (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b', hbL'⟩) :=
      s65_SixFiveQuot_comm_of_mem_N (M := M) (V := V) (g := g)
        (commutator_U_B_le_N h (Subgroup.commutator_mem_commutator huU hbB'))
    exact (hbb'.mul_right hbu').mul_left (hub'.mul_right huu')
  exact s65_SixFiveQuot_mem_N_of_comm (M := M) (V := V) (g := g) hcomm

theorem sq_K_mem_N (h : Hyp65 n M V₀ V g) : ∀ k ∈ KOf M V g, k * k ∈ NOf M V g := by
  haveI := N_normal h
  intro k hk
  have hkL : k ∈ LOf V g := KOf_le_LOf M V g hk
  change k ∈ (KOf M V g : Set G) at hk
  rw [K_coe_eq_mul h, Set.mem_mul] at hk
  obtain ⟨b, hbB, u, huU, hk_eq⟩ := hk
  have hbL : b ∈ LOf V g := by
    rw [LOf]
    exact (le_sup_right : conjSubgroup V g ≤ V ⊔ conjSubgroup V g) hbB.1
  have huL : u ∈ LOf V g := by
    rw [LOf]
    exact (le_sup_left : V ≤ V ⊔ conjSubgroup V g) huU.1
  have hkLprod : b * u ∈ LOf V g := (LOf V g).mul_mem hbL huL
  have hkeq : (⟨k, hkL⟩ : ↥(LOf V g)) = ⟨b * u, hkLprod⟩ := Subtype.ext hk_eq.symm
  have h1 : QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g))
      (⟨k, hkL⟩ * ⟨k, hkL⟩) = 1 := by
    rw [map_mul, hkeq,
      s65_SixFiveQuot_pi_eq_mul (M := M) (V := V) (g := g) rfl hbL huL hkLprod]
    have hcomm : Commute (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u, huL⟩)
        (QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b, hbL⟩) :=
      s65_SixFiveQuot_comm_of_mem_N (M := M) (V := V) (g := g)
        (commutator_U_B_le_N h (Subgroup.commutator_mem_commutator huU hbB))
    rw [Commute.mul_mul_mul_comm hcomm]
    have hb2 : QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b, hbL⟩ *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨b, hbL⟩ = 1 := by
      rw [← map_mul]
      have hbb : (⟨b, hbL⟩ : ↥(LOf V g)) * ⟨b, hbL⟩ = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_one]
        exact h.swap.elemAbelian.mul_self_eq_one hbB.1)
      rw [hbb, map_one]
    have hu2 : QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u, huL⟩ *
        QuotientGroup.mk' ((NOf M V g).subgroupOf (LOf V g)) ⟨u, huL⟩ = 1 := by
      rw [← map_mul]
      have huu : (⟨u, huL⟩ : ↥(LOf V g)) * ⟨u, huL⟩ = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_one]
        exact h.elemAbelian.mul_self_eq_one huU.1)
      rw [huu, map_one]
    rw [hb2, hu2, one_mul]
  have hmem := (mk_eq_one_iff_mem_N M V g (⟨k, hkL⟩ * ⟨k, hkL⟩)).1 h1
  simpa only [Subgroup.coe_mul] using hmem

theorem N_le_U (h : Hyp65 n M V₀ V g) : NOf M V g ≤ UOf M V g := inf_le_left

end Hyp65

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}
  [((NOf M V g).subgroupOf (LOf V g)).Normal] [((KOf M V g).subgroupOf (LOf V g)).Normal]

local notation "Xbar" => (imgN M V g V ⊔ imgN M V g (conjSubgroup V g))

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81

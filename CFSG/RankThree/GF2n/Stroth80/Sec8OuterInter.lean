module

public import CFSG.RankThree.GF2n.Stroth80.Sec8OuterElt
public import CFSG.RankThree.GF2n.Stroth80.Sec8HGen

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_outer_inter (hD' : Sec8DPrimeStatement) (h53 : Stroth53Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r g : G}
    (h : Sec8Outer hc n t r g) :
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z := by
  have ht : t ∈ LB M Q B := h.hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    refine le_inf sec39_Z_le_Vt ?_
    have h1 : conjSubgroup g Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      Subgroup.map_mono sec39_Z_le_Vt
    rwa [hc.conj_Z_eq h.hg] at h1
  refine le_antisymm ?_ hZV
  by_contra hne
  have hlt : Z < Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    lt_of_le_of_ne hZV fun heq => hne heq.symm.le
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  obtain ⟨_, -, hsub⟩ := hD' G M Q Z B hc n t h.hs h.hna Z0 hZ0 g h.hg hlt
  have hxZ0 : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    rw [e]
    exact htZ0
  have hxN : g * t * g⁻¹ ∈ hc.CN t := (hsub hxZ0).2
  obtain ⟨w, hw, hxw⟩ := h.hout
  have hd := (h53.2.1 G M Q Z B hc n t h.hs.toSec5 h.hs.spNat r h.hr.mem h.hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl).2
  exact hxw (hd _ hxN w hw)

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_outer_normLB_aux (hc : Ctx M Q Z B) {t x : G} (ht : t ∈ LB M Q B) (hxM : x ∈ M)
    (hVx : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) :
    conjSubgroup x (LB M Q B) = LB M Q B := by
  obtain ⟨c, hc1, hcZ⟩ := sec8_gen_points_exists_out hc M.one_mem
  rw [conjSubgroup_one] at hc1
  have hxc : ⁅x, c⁆ ∈ Z := hVx c (hc.B_le_Vt ht hc1)
  have hcx : c ∈ conjSubgroup x B ⊔ Z := by
    have hZs : Z ≤ conjSubgroup x B ⊔ Z := le_sup_right
    have hCs : conjSubgroup x B ≤ conjSubgroup x B ⊔ Z := le_sup_left
    have h1 : x * c * x⁻¹ ∈ conjSubgroup x B := by
      rw [mem_conjSubgroup, show x⁻¹ * (x * c * x⁻¹) * x = c by group]
      exact hc1
    have h3 : c = ⁅x, c⁆⁻¹ * (x * c * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (conjSubgroup x B ⊔ Z).mul_mem (hZs (Z.inv_mem hxc)) (hCs h1)
  have hd₁ : c ∈ conjSubgroup 1 B ⊔ Z := by
    rw [conjSubgroup_one]
    have hBs : B ≤ B ⊔ Z := le_sup_left
    exact hBs hc1
  have hpt := sec8_point_eq (hc := hc) (m₁ := 1) (m₂ := x) M.one_mem hxM hd₁ hcx hcZ
  rw [conjSubgroup_one] at hpt
  have hLB := sec8_LB_eq_of_sup_eq hc (hc.conj_of_mem hxM) hpt
  rw [hc.LB_conj hxM] at hLB
  exact hLB.symm

theorem sec8_outer_normLB {hc : Ctx M Q Z B} {n : ℕ} {t r g : G} (h : Sec8Outer hc n t r g) :
    conjSubgroup (g * t * g⁻¹) (LB M Q B) = LB M Q B := by
  have ht : t ∈ LB M Q B := h.hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem h.hg htM) (M.inv_mem h.hg)
  have hVle : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r :=
    le_inf le_sup_right le_sup_right
  exact sec8_outer_normLB_aux hc ht hxM (fun v hv => h.hvan v (hVle hv))

end

end CFSG.RankThree.GF2n.Stroth80

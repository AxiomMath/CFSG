module

public import CFSG.RankThree.GF2n.Tim77.Sec3Conj
public import CFSG.RankThree.GF2n.Tim77.Sec32a
public import CFSG.RankThree.GF2n.Tim77.Assembly
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

namespace Sec3Ctx

theorem mem_centralizer_of_isSChoice (h : Sec3Ctx A Abar S₀ B) {s : G}
    (hs : Section3.IsSChoice A Abar S₀ B s) : s ∈ centralizer (A : Set G) := by
  obtain ⟨b, hb, -, hdisj⟩ := hs
  rcases hdisj with ⟨-, rfl⟩ | ⟨-, x, -, -, -, -, hsC, -⟩
  · exact h.b_le_centralizer hb
  · exact hsC

theorem N_le_normalizer (h : Sec3Ctx A Abar S₀ B) {s : G} (hsC : s ∈ centralizer (A : Set G)) :
    Section3.N A Abar s ≤ normalizer (A : Set G) := by
  have hA0 : Section3.A0 A Abar ≤ normalizer (A : Set G) :=
    h.setup.L_le.trans (le_normalizer)
  have hAb0 : Section3.Abar0 A Abar ≤ normalizer (A : Set G) := by
    rw [h.abar0_eq]
    exact inf_le_right
  have hAb0s : conjSubgroup s (Section3.Abar0 A Abar) ≤ normalizer (A : Set G) := by
    have h1 := (conjSubgroup_le_conj_iff s).2 hAb0
    rwa [conjSubgroup_map_normalizer, conjSubgroup_eq_of_mem_centralizer hsC] at h1
  unfold Section3.N
  exact sup_le (sup_le hA0 hAb0) hAb0s

theorem Y_eq_X_of_le_sup (h : Sec3Ctx A Abar S₀ B) {s : G} (hs : Section3.IsSChoice A Abar S₀ B s)
    (hle : Section3.Y A Abar s ≤ Section3.X A Abar ⊔ Section3.N A Abar s) :
    Section3.Y A Abar s = Section3.X A Abar := by
  have hsC := h.mem_centralizer_of_isSChoice hs
  have hAs : conjSubgroup s A = A := conjSubgroup_eq_of_mem_centralizer hsC
  have hXY : Section3.X A Abar ≤ Section3.Y A Abar s := by
    rw [h.x_eq]
    unfold Section3.Y
    exact le_sup_left
  obtain ⟨hNY, hYN, -⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hXN : Section3.X A Abar ≤ normalizer (Section3.N A Abar s : Set G) :=
    fun x hx => hYN x (hXY hx)
  have hC := h.conj s
  rw [hAs] at hC
  obtain ⟨k, hk, hAbs⟩ := hC.setup.exists_conj_eq
  have hkY : k ∈ Section3.Y A Abar s := by
    have : A ⊔ conjSubgroup s Abar ≤ Section3.Y A Abar s := by
      unfold Section3.Y
      exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    exact this hk
  have hkXN : k ∈ Section3.X A Abar ⊔ Section3.N A Abar s := hle hkY
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXN] at hkXN
  obtain ⟨x, hx, n, hn, hxn⟩ := hkXN
  have hxn' : x * n = k := hxn
  rw [← hxn'] at hAbs
  have hnA : conjSubgroup n A = A :=
    mem_normalizer_iff_conjSubgroup_eq.1 (h.N_le_normalizer hsC hn)
  have hAbsX : conjSubgroup s Abar ≤ Section3.X A Abar := by
    rw [hAbs, conjSubgroup_mul, hnA]
    intro y hy
    rw [mem_conjSubgroup] at hy
    have hAX : A ≤ Section3.X A Abar := by rw [h.x_eq]; exact le_sup_left
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx (hAX hy)) (Subgroup.inv_mem _ hx)
  refine le_antisymm ?_ hXY
  unfold Section3.Y
  rw [← h.x_eq]
  exact sup_le le_rfl hAbsX

end Sec3Ctx

end CFSG.RankThree.GF2n.Tim77

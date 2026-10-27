module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigUniq

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

universe u

variable {S : LieSetting.{u, 0}} {Y : Type} [Group Y] [Finite Y] (hS : S.Facts45L)
  (β : S.α.Completion Y) (hβ : β.IsFaithful) (hs : β.IsSmall S.m)

theorem smul_conj_of_fix {G X : Type*} [Group G] [MulAction G X] (w q : G) {x : X}
    (hx : w • x = x) : (w * q * w⁻¹) • x = w • q • x := by
  rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hx.symm]

include hS in
theorem Qb1_le_range (r : S.α.G1) (hr : r ∈ S.Qb1) : r ∈ S.α.α1.range := by
  have h : f1 (c := S.ι) r ∈ stv S.ι S.ι.lv := hS.Qle S.ι.xv S.ι.lv CosetGeom.adj_γ₀_γ₁ hr
  exact (f1_smul_lv_iff S.ι S.hι r).mp (MulAction.mem_stabilizer_iff.mp h)

@[expose] def commSub : Subgroup S.α.G1 where
  carrier := {a | ∀ z : Vs β (decide (Odd S.m)), vEq hS β hβ hs (f1 (c := β) a • z) =
    f1 (c := S.ι) a • vEq hS β hβ hs z}
  one_mem' := fun z => by simp
  mul_mem' := fun {a b} ha hb z => by
    rw [map_mul, map_mul, mul_smul, mul_smul, ha, hb]
  inv_mem' := fun {a} ha z => by
    have h := ha (f1 (c := β) a⁻¹ • z)
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at h
    calc vEq hS β hβ hs (f1 (c := β) a⁻¹ • z) = f1 (c := S.ι) a⁻¹ •
          f1 (c := S.ι) a • vEq hS β hβ hs (f1 (c := β) a⁻¹ • z) := by
          rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ = f1 (c := S.ι) a⁻¹ • vEq hS β hβ hs z := by rw [← h]

theorem mem_commSub_of_far {z₀ : Vs β (decide (Odd S.m))} (hz₀ : β.graph.dist β.xv z₀.1 = S.m)
    (hC : Cz β z₀.1 = Cz S.ι (vEq hS β hβ hs z₀).1) {w : S.α.G1} (hw : w ∈ Cz β z₀.1) :
    w ∈ commSub hS β hβ hs := by
  have hQ : S.Qb1.Normal := S.Qb1_normal
  have hwβ : f1 (c := β) w • z₀ = z₀ := Subtype.ext (mem_Cz.mp hw)
  have hwι : f1 (c := S.ι) w • vEq hS β hβ hs z₀ = vEq hS β hβ hs z₀ :=
    Subtype.ext (mem_Cz.mp (hC ▸ hw))
  have hQcomm : ∀ r ∈ S.Qb1, vEq hS β hβ hs (f1 (c := β) r • z₀) =
      f1 (c := S.ι) r • vEq hS β hβ hs z₀ := fun r hr =>
    vEq_B1 hS β hβ hs (Qb1_le_range hS r hr) z₀
  intro z
  by_cases hn : NearV S.m β z.1
  · exact vEq_f1_near hS β hβ hs w z hn
  have hzfar : β.graph.dist β.xv z.1 = S.m := (far_iff_not_near hS β hβ hs z).mpr hn
  obtain ⟨q, hq, hqz⟩ := qTrans_far hS β hβ hs hz₀ hzfar
  have hz : z = f1 (c := β) q • z₀ := (Subtype.ext hqz).symm
  have hq' : w * q * w⁻¹ ∈ S.Qb1 := hQ.conj_mem q hq w
  have e : f1 (c := β) w • z = f1 (c := β) (w * q * w⁻¹) • z₀ := by
    rw [hz, ← smul_conj_of_fix (f1 (c := β) w) (f1 (c := β) q) hwβ, map_mul, map_mul, map_inv]
  have hvz : vEq hS β hβ hs z = f1 (c := S.ι) q • vEq hS β hβ hs z₀ := by
    rw [hz, hQcomm q hq]
  rw [e, hQcomm _ hq', hvz, ← smul_conj_of_fix (f1 (c := S.ι) w) (f1 (c := S.ι) q) hwι, map_mul,
    map_mul, map_inv]

theorem vEq_f1 (hT : S.CartanFPF) (a : S.α.G1) (z : Vs β (decide (Odd S.m))) :
    vEq hS β hβ hs (f1 (c := β) a • z) = f1 (c := S.ι) a • vEq hS β hβ hs z := by
  obtain ⟨z₀, hz₀, hC, w, hwC, hwB⟩ := exists_far_data hS β hβ hs hT
  have hw : w ∈ commSub hS β hβ hs := mem_commSub_of_far hS β hβ hs hz₀ hC hwC
  have hB : S.α.α1.range ≤ commSub hS β hβ hs := fun a ha z => vEq_B1 hS β hβ hs ha z
  obtain ⟨-, h2⟩ := far_structure hS β hβ hs hz₀
  have hmax := maximal_inf_range β hβ (C := ⊤) fun u₁ u₂ u₃ u₄ h₁ h₂ h₃ h₄ hn₁ hn₂ => by
    obtain ⟨a, -, ha⟩ := h2 u₁ u₂ u₃ u₄ h₁ h₂ h₃ h₄ hn₁ hn₂
    exact ⟨a, Subgroup.mem_top a, ha⟩
  rcases hmax (commSub hS β hβ hs) (by rw [top_inf_eq]; exact hB) le_top with h | h
  · exact absurd (by rw [h] at hw; exact hw.2) hwB
  · have : a ∈ commSub hS β hβ hs := by rw [h]; exact Subgroup.mem_top a
    exact this z

end CFSG.Quasithin.H13.F48Rig

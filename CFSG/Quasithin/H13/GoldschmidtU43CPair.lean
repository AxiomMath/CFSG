module

public import CFSG.Quasithin.H13.GoldschmidtU43CLift
public import CFSG.Quasithin.H13.GoldschmidtU43CTwo

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

@[expose] def zK (z : G) : ↥(Hz z) := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem coe_zK (z : G) : ((zK z : ↥(Hz z)) : G) = z := rfl

namespace Swap

variable [Finite G] {z t w a : G} (d : Swap z t w) (ha : Good z t a)
  {R : Subgroup ↥(Hz z)} (hR : SylR d.hyp R)
include hR

theorem exists_lift : ∃ n : ↥(Hz z), n ∈ Subgroup.normalizer (R : Set ↥(Hz z)) ∧
    d.hyp.act n = d.hyp.act (d.mK ha) ∧ n * n = 1 ∧
      ∃ v ∈ Vg z t, ∃ i : ZMod 2, (n : G) = v * zp a i * (w⁻¹ * a * w) := by
  have h := d.hyp
  obtain ⟨x, hx, n, hn, hmk⟩ := hR.frattini_elt (d.mK ha)
  have hact : h.act n = h.act (d.mK ha) := by
    rw [hmk, map_mul, MonoidHom.mem_ker.mp hx, one_mul]
  have hE : (n : G) ∈ Eg z t w a := d.lift_mem_Eg ha hR hn hact
  refine ⟨n, hn, hact, Subtype.ext ?_, ?_⟩
  · rw [Subgroup.coe_mul]
    exact (d.Eg_comm_sq ha hE hE).2
  · obtain ⟨v, hv, i, j, hnG⟩ := (d.mem_Eg_iff ha _).1 hE
    refine ⟨v, hv, i, ?_⟩
    rcases zmod_two_cases j with rfl | rfl
    · exfalso
      rw [zp_zero, mul_one] at hnG
      have hnU : (n : G) ∈ Uz z := by
        rw [hnG]
        exact mul_mem (d.Vg_le_U hv) (by
          rcases zmod_two_cases i with rfl | rfl
          · rw [zp_zero]; exact one_mem _
          · rw [zp_one]; exact ha.mem.1)
      have hker : n ∈ h.act.ker := by
        rw [h.ker_act]
        exact hnU
      exact d.act_mK_ne_one ha (hact ▸ MonoidHom.mem_ker.mp hker)
    · rw [zp_one] at hnG
      exact hnG

end Swap

namespace Two

variable [Finite G] {z t w a a' : G} (e : Two z t w a a')
  {R : Subgroup ↥(Hz z)} (hR : SylR e.swap.hyp R)
include hR

theorem exists_uu' : ∃ u u' : ↥(Hz z), u ∈ Subgroup.normalizer (R : Set ↥(Hz z)) ∧
    u' ∈ Subgroup.normalizer (R : Set ↥(Hz z)) ∧
    e.swap.hyp.act u = e.swap.hyp.act (e.swap.mK e.ha) ∧
    e.swap.hyp.act u' = e.swap.hyp.act (e.swap.mK e.ha') ∧
    u * u = 1 ∧ u' * u' = 1 ∧ u * u' * u⁻¹ * u'⁻¹ = zK z := by
  have h := e.swap.hyp
  obtain ⟨u, hu, hau, hu2, v, hv, i, huG⟩ := e.swap.exists_lift e.ha hR
  obtain ⟨u', hu', hau', hu'2, v', hv', i', hu'G⟩ := e.swap.exists_lift e.ha' hR
  refine ⟨u, u', hu, hu', hau, hau', hu2, hu'2, ?_⟩
  have hs1 := e.swap.act_mK_ne_one e.ha
  have hs2 := e.swap.act_mK_ne_one e.ha'
  obtain ⟨hcomm, -⟩ := fix_pairA (e.swap.linePair_ta e.ha) (e.swap.linePair_ta e.ha')
    e.bq_eq_one (h.act_mem_Oq _) (h.act_mem_Oq _) (e.swap.vapp_mK_tau e.ha)
    (e.swap.vapp_mK_alpha e.ha) hs1 (e.swap.vapp_mK_tau e.ha') (e.swap.vapp_mK_alpha e.ha') hs2
  have hcN : u * u' * u⁻¹ * u'⁻¹ ∈ Subgroup.normalizer (R : Set ↥(Hz z)) :=
    mul_mem (mul_mem (mul_mem hu hu') (inv_mem hu)) (inv_mem hu')
  have hcker : u * u' * u⁻¹ * u'⁻¹ ∈ h.act.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hau, hau', hcomm]
    group
  rcases hR.normalizer_inf_ker hcN hcker with h1 | h1
  · exfalso
    have : br (u : G) (u' : G) = 1 := by
      unfold br
      simpa using h1
    rw [huG, hu'G] at this
    exact e.br_ne_one hv hv' i i' this
  · exact Subtype.ext h1

end Two

end CFSG.Quasithin.H13.U43

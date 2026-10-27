module

public import CFSG.Quasithin.H13.GoldschmidtU43BA
public import CFSG.Quasithin.H13.GoldschmidtU43CSylR

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem eq_of_add_eq_zero_V4 : ∀ a b : V4, a + b = 0 → a = b := by
  decide +kernel

namespace Hyp

variable {z : G} (h : Hyp z)

theorem vapp_fix_of_comm (x : ↥(Hz z)) (u : ↥(Uz z)) (hc : (x : G) * u = u * x) :
    vapp (h.act x) (h.tv u) = h.tv u := by
  rw [← h.tv_conj]
  congr 1
  apply Subtype.ext
  rw [coe_conjU]
  calc (x : G) * u * (x : G)⁻¹ = (u * (x : G)) * (x : G)⁻¹ := by rw [hc]
    _ = u := by group

end Hyp

namespace Swap

variable {z t w a : G} (d : Swap z t w) (ha : Good z t a)

@[expose] def mK : ↥(Hz z) := ⟨w⁻¹ * a * w, (d.m_mem_B ha).1⟩

theorem mK_mul_self : d.mK ha * d.mK ha = 1 := by
  apply Subtype.ext
  show (w⁻¹ * a * w) * (w⁻¹ * a * w) = 1
  exact m_sq ha

theorem vapp_mK_tau : vapp (d.hyp.act (d.mK ha)) d.tauV = d.tauV :=
  d.hyp.vapp_fix_of_comm (d.mK ha) ⟨t, d.ht.1⟩
    (Subgroup.mem_centralizer_singleton_iff.mp (d.m_mem_B ha).2)

theorem vapp_mK_alpha [Finite G] : vapp (d.hyp.act (d.mK ha)) (d.alphaV ha) = d.alphaV ha :=
  d.hyp.vapp_fix_of_comm (d.mK ha) ⟨a, ha.mem.1⟩ (d.a_comm_m ha).symm

theorem act_mK_ne_one [Finite G] : d.hyp.act (d.mK ha) ≠ 1 := by
  intro h1
  have hU : w⁻¹ * a * w ∈ Uz z := d.hyp.mem_U_of_act_eq_one _ h1
  apply d.m_notV ha
  exact (d.mem_N1_inf_N2 _).1 ⟨⟨hU, (d.m_mem_B ha).2⟩, m_mem_N2 ha⟩

theorem lift_mem_Eg [Finite G] {R : Subgroup ↥(Hz z)} (hR : SylR d.hyp R) {n : ↥(Hz z)}
    (hn : n ∈ Subgroup.normalizer (R : Set ↥(Hz z)))
    (hact : d.hyp.act n = d.hyp.act (d.mK ha)) : (n : G) ∈ Eg z t w a := by
  have h := d.hyp
  have hsO : h.act (d.mK ha) ∈ Oq := h.act_mem_Oq _
  obtain ⟨-, hss, hfix⟩ := fix_swapA (d.linePair_ta ha) hsO (d.vapp_mK_tau ha)
    (d.vapp_mK_alpha ha) (d.act_mK_ne_one ha)
  set mK := d.mK ha with hmK
  set x : ↥(Hz z) := mK⁻¹ * n with hx
  have hxker : x ∈ h.act.ker := by
    rw [MonoidHom.mem_ker, hx, map_mul, map_inv, hact]
    simp
  have hxU : (x : G) ∈ Uz z := h.mem_U_of_act_eq_one x (MonoidHom.mem_ker.mp hxker)
  have hn_eq : n = mK * x := by rw [hx]; group
  have hnn : n * n ∈ Subgroup.normalizer (R : Set ↥(Hz z)) := mul_mem hn hn
  have hnnker : n * n ∈ h.act.ker := by
    rw [MonoidHom.mem_ker, map_mul, hact]
    exact hss
  have hnn1 := hR.normalizer_inf_ker hnn hnnker
  set u₁ : ↥(Uz z) := ⟨x, hxU⟩ with hu₁
  have hmm : (mK : G) * mK = 1 := congrArg Subtype.val (d.mK_mul_self ha)
  have hnnG : ((n * n : ↥(Hz z)) : G) = ((conjU mK u₁ * u₁ : ↥(Uz z)) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_conjU, hn_eq, Subgroup.coe_mul]
    calc (mK : G) * x * ((mK : G) * x)
        = ((mK : G) * x * (mK : G)⁻¹) * ((mK : G) * mK) * x := by group
      _ = ((mK : G) * x * (mK : G)⁻¹) * x := by rw [hmm, mul_one]
  have hzero : h.tv (conjU mK u₁ * u₁) = 0 := by
    rw [h.tv_eq_zero_iff, ← hnnG]
    exact hnn1
  rw [h.tv_mul, h.tv_conj] at hzero
  have hfixx : vapp (h.act mK) (h.tv u₁) = h.tv u₁ := eq_of_add_eq_zero_V4 _ _ hzero
  have hA : Aset d.tauV (d.alphaV ha) (h.tv u₁) := hfix _ hfixx
  have hxA0 : (x : G) ∈ A0 d ha := ⟨hxU, hA⟩
  have hxE : (x : G) ∈ Eg z t w a := d.A0_le_E ha hxA0
  have hmE : (mK : G) ∈ Eg z t w a := Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))
  rw [hn_eq, Subgroup.coe_mul]
  exact mul_mem hmE hxE

end Swap

end CFSG.Quasithin.H13.U43

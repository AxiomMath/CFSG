module

public import CFSG.Quasithin.Vol2.Ch10SecCL3F
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Vol2.Ch10SecBL32K

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.L3F

open CFSG.Quasithin.Vol2.Ch10.SecB.L32

set_option maxRecDepth 100000 in
theorem ea_sq : ∀ g : L3.Γ, IsEa g → g * g = 1 := by
  unfold IsEa IsPa ent; decide +kernel

theorem pCore_pa : CFSG.pCore 2 ↥Pa = Ea.subgroupOf Pa := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    by_contra hxE
    obtain ⟨δ, hδ, hc1, hc3⟩ := pa_comm_three x x.2 hxE
    have hN := CFSG.pCore_normal (p := 2) (G := ↥Pa)
    set c : ↥Pa := x * ⟨δ, hδ⟩ * x⁻¹ * (⟨δ, hδ⟩ : ↥Pa)⁻¹ with hcdef
    have hcP : c ∈ CFSG.pCore 2 ↥Pa := by
      have h1 : ⟨δ, hδ⟩ * x⁻¹ * (⟨δ, hδ⟩ : ↥Pa)⁻¹ ∈ CFSG.pCore 2 ↥Pa :=
        hN.conj_mem _ (Subgroup.inv_mem _ hx) _
      have e : c = x * (⟨δ, hδ⟩ * x⁻¹ * (⟨δ, hδ⟩ : ↥Pa)⁻¹) := by rw [hcdef]; group
      rw [e]
      exact Subgroup.mul_mem _ hx h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Pa)) ⟨c, hcP⟩
    have hk' : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : c ^ 3 = 1 := by
      apply Subtype.ext
      rw [hcdef]
      change (x * δ * x⁻¹ * δ⁻¹ : L3.Γ) ^ 3 = 1
      rw [pow_succ, pow_two]
      exact hc3
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have h1 : c = 1 := by
      have := (pow_gcd_eq_one (a := c) (m := 3) (n := 2 ^ k)).mpr ⟨h3, hk'⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
    apply hc1
    have := congrArg Subtype.val h1
    exact this
  · unfold CFSG.pCore
    refine le_sSup ⟨⟨fun n hn g => ?_⟩, fun g => ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ea_normal g n g.2 hn
    · refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
      change ((g : ↥Pa) : L3.Γ) ^ 2 = 1
      rw [pow_two]
      exact ea_sq _ (Subgroup.mem_subgroupOf.mp g.2)

end CFSG.Quasithin.Vol2.Ch10.SecC.L3F

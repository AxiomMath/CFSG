module

public import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Walter.Models
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ1Model

public section

namespace CFSG.Quasithin.L139A5

open CFSG.Open CFSG.Walter CFSG.Walter.J1Props

theorem no_orderOf_four_walterJ1 (x : ↥walterJ1) :
    orderOf x ≠ 4 := by
  intro h4
  have hJ := jankoHyp₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, h4]
    norm_num
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨S, hS⟩ := hJ.exists_sylow_mem_t
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥walterJ1 Q S
  have hxQ : x ∈ (Q : Subgroup ↥walterJ1) := hQ (Subgroup.mem_zpowers x)
  have hxS : g * x * g⁻¹ ∈ (S : Subgroup ↥walterJ1) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hxQ
  have hsq := hJ.mul_self_of_mem_sylow S hS hxS
  have hx2 : x ^ 2 = 1 := by
    have : g * (x * x) * g⁻¹ = 1 := by
      calc g * (x * x) * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) := by group
        _ = 1 := hsq
    rw [sq]
    simpa using this
  have := orderOf_dvd_of_pow_eq_one hx2
  rw [h4] at this
  norm_num at this

theorem a5SecInner_j1 {X : Type} [Group X] [Finite X]
    (hX : IsSporadic .J1 X) : A5SecInner X := by
  obtain ⟨e₀⟩ := hX
  let e : X ≃* ↥walterJ1 := e₀.trans walterJ1EquivNative.symm
  intro A N _ hNA _ hA5 β hβA hβN
  obtain ⟨eA⟩ := hA5
  refine exists_inner_sec eA hNA (mem_stb_of_maps hβA hβN) ?_
  intro γ hγ a haA haN ha5 hc
  set b : ↥A ⧸ N.subgroupOf A := ((⟨a, haA⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) with hb
  have hb1 : b ≠ 1 := by
    rw [hb, Ne, QuotientGroup.eq_one_iff]
    exact haN
  have hb5 : b ^ 5 = 1 := by
    rw [hb, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using ha5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hbo : orderOf b = 5 := orderOf_eq_prime hb5 hb1
  have hρ : secRho ⟨γ, hγ⟩ b = b ^ 2 := by
    rw [hb, secRho_mk, ← QuotientGroup.mk_pow, QuotientGroup.eq]
    exact hc
  have h4 : 4 ∣ orderOf γ := by
    have h1 := orderOf_map_dvd (secRho (A := A) (N := N)) ⟨γ, hγ⟩
    rw [Subgroup.orderOf_mk] at h1
    exact (four_dvd_orderOf_of_aut hbo hρ).trans h1
  obtain ⟨s, hs⟩ := CFSG.QuasithinUnique.K1.autInner_walterJ1 (e.symm.trans (γ.trans e))
  set z : X := e.symm s⁻¹ with hz
  have hγz : γ = MulAut.conj z := by
    ext x
    have h1 := hs (e x)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    rw [h2, hz, MulAut.conj_apply]
    simp
  have h4z : 4 ∣ orderOf z := by
    have h1 := orderOf_map_dvd (MulAut.conj : X →* MulAut X) z
    rw [← hγz] at h1
    exact h4.trans h1
  obtain ⟨δ, hδ⟩ := exists_orderOf_eq_four (isOfFinOrder_of_finite z) h4z
  exact no_orderOf_four_walterJ1 (e δ) (by rw [MulEquiv.orderOf_eq]; exact hδ)

end CFSG.Quasithin.L139A5

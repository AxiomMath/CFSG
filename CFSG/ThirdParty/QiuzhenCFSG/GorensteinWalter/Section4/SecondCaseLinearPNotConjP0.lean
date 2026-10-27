module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaFixedPart
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The external and internal order-p subgroups are not conjugate

The selected external subgroup `P ≤ F` is centralized by the full ambient
Sylow two-subgroup `S`, while the internal subgroup `P₀ ≤ K₀` is inverted by
the selected reflection `s ∈ S`.  If `P^g = P₀`, then `S^g` centralizes
`P₀`.  Both `S` and `S^g` lie in `N_G(P₀)` and remain Sylow there, so Sylow
conjugacy inside the normalizer would make `S` centralize `P₀`, contradicting
inversion and the odd prime order of `P₀`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The selected external order-`p` subgroup is not conjugate to the
internal order-`p` subgroup. -/
public theorem secondCase_linear_P_not_conjugate_P0
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K) :
    ¬ ∃ g : G, conjugateSubgroup post.od.P g = post.od.P0 := by
  classical
  rintro ⟨g, hgP⟩
  let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
  let : IsCyclic post.od.K := post.od.K_cyclic
  have hK0cyc : IsCyclic post.od.K0 := by
    rw [post.od.K0_eq]
    exact Subgroup.isCyclic_of_le inf_le_right
  have hSleHM : (c.S : Subgroup G) ≤ c.H ⊓ w.M := by
    exact le_inf (centralizerSetup_S_le_H c)
      (post.hSleE.trans d.E_component.1)
  have hSleNK0 : (c.S : Subgroup G) ≤
      Subgroup.normalizer (post.od.K0 : Set G) :=
    hSleHM.trans (le_normalizer_of_isNormalIn post.K0_normal)
  have hSleNP0 : (c.S : Subgroup G) ≤
      Subgroup.normalizer (post.od.P0 : Set G) := by
    intro x hx
    exact prime_order_subgroup_fixed_by_normalizer_of_cyclic
      hK0cyc post.od.P0_le_K0 post.od.hp_prime post.od.P0_card (hSleNK0 hx)
  have hSleCP : (c.S : Subgroup G) ≤
      Subgroup.centralizer (post.od.P : Set G) := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro p hp
      have hpE := (Subgroup.mem_centralizer_iff.mp
        (post.od.F_centralizes_E (post.od.P_le_F hp))) x (post.hSleE hx)
      exact hpE.symm)
  have hSgLeCP0 : ((g • c.S : Sylow 2 G) : Subgroup G) ≤
      Subgroup.centralizer (post.od.P0 : Set G) := by
    intro x hx
    change x ∈ conjugateSubgroup (c.S : Subgroup G) g at hx
    rcases Subgroup.mem_map.mp hx with ⟨s0, hs0, hs0x⟩
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro p0 hp0
      have hp0conj : p0 ∈ conjugateSubgroup post.od.P g := by
        rw [hgP]
        exact hp0
      rcases Subgroup.mem_map.mp hp0conj with ⟨p, hp, hpp0⟩
      have hcomm : p * s0 = s0 * p :=
        (Subgroup.mem_centralizer_iff.mp (hSleCP hs0)) p hp
      have hxval : x = g * s0 * g⁻¹ := by
        simpa [MulAut.conj_apply] using hs0x.symm
      have hp0val : p0 = g * p * g⁻¹ := by
        simpa [MulAut.conj_apply] using hpp0.symm
      rw [hxval, hp0val]
      calc
        (g * p * g⁻¹) * (g * s0 * g⁻¹) = g * (p * s0) * g⁻¹ := by group
        _ = g * (s0 * p) * g⁻¹ := by rw [hcomm]
        _ = (g * s0 * g⁻¹) * (g * p * g⁻¹) := by group)
  have hSgLeNP0 : ((g • c.S : Sylow 2 G) : Subgroup G) ≤
      Subgroup.normalizer (post.od.P0 : Set G) :=
    hSgLeCP0.trans (Subgroup.centralizer_le_normalizer (post.od.P0 : Set G))
  let N : Subgroup G := Subgroup.normalizer (post.od.P0 : Set G)
  let SN : Sylow 2 N := c.S.subtype hSleNP0
  let SgN : Sylow 2 N := (g • c.S).subtype hSgLeNP0
  obtain ⟨n, hn⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq N (Sylow 2 N)
      inferInstance inferInstance SgN SN
  have hnSub : ((n • SgN : Sylow 2 N) : Subgroup N) =
      (SN : Subgroup N) := congrArg (fun T : Sylow 2 N => (T : Subgroup N)) hn
  rw [Sylow.coe_subgroup_smul] at hnSub
  have hSleCP0 : (c.S : Subgroup G) ≤
      Subgroup.centralizer (post.od.P0 : Set G) := by
    intro x hx
    let xN : N := ⟨x, hSleNP0 hx⟩
    have hxSN : xN ∈ (SN : Subgroup N) := by
      exact hx
    rw [← hnSub] at hxSN
    have hxsmul : xN ∈ MulAut.conj n • (SgN : Subgroup N) := hxSN
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hxsmul
    rcases hxsmul with ⟨y, hySg, hyx⟩
    have hyGcentral : (y : G) ∈
        Subgroup.centralizer (post.od.P0 : Set G) := by
      apply hSgLeCP0
      exact hySg
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro p0 hp0
      have hnNorm : (n : G) ∈ Subgroup.normalizer (post.od.P0 : Set G) := n.2
      have hp0back : (n : G)⁻¹ * p0 * (n : G) ∈ post.od.P0 := by
        apply (Subgroup.mem_normalizer_iff.mp hnNorm
          ((n : G)⁻¹ * p0 * (n : G))).mpr
        have hback : (n : G) * ((n : G)⁻¹ * p0 * (n : G)) * (n : G)⁻¹ = p0 := by
          group
        rwa [hback]
      have hycomm : ((n : G)⁻¹ * p0 * (n : G)) * (y : G) =
          (y : G) * ((n : G)⁻¹ * p0 * (n : G)) :=
        (Subgroup.mem_centralizer_iff.mp hyGcentral)
          ((n : G)⁻¹ * p0 * (n : G)) hp0back
      have hxval : x = (n : G) * (y : G) * (n : G)⁻¹ := by
        simpa [MulAut.smul_def] using congrArg Subtype.val hyx.symm
      rw [hxval]
      calc
        p0 * ((n : G) * (y : G) * (n : G)⁻¹) =
            (n : G) * (((n : G)⁻¹ * p0 * (n : G)) * (y : G)) * (n : G)⁻¹ := by
              group
        _ = (n : G) * ((y : G) * ((n : G)⁻¹ * p0 * (n : G))) * (n : G)⁻¹ := by
              rw [hycomm]
        _ = ((n : G) * (y : G) * (n : G)⁻¹) * p0 := by group)
  have hsCent : (post.od.s : G) ∈
      Subgroup.centralizer (post.od.P0 : Set G) :=
    hSleCP0 post.hsS
  have hP0bot : post.od.P0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hK0leK : post.od.K0 ≤ post.od.K := by
      rw [post.od.K0_eq]
      exact inf_le_right
    have hxK : x ∈ post.od.K :=
      hK0leK (post.od.P0_le_K0 hx)
    have hxInv : (post.od.s : G) * x * (post.od.s : G)⁻¹ = x⁻¹ := by
      have hxI : x ∈ invertedElements (c.U ⊓ w.M) (post.od.s : G) := by
        rw [← post.od.K_inverted]
        exact hxK
      exact hxI.2
    have hxFix : (post.od.s : G) * x * (post.od.s : G)⁻¹ = x := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp hsCent) x hx
      exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
    have hxx : x * x = 1 := by
      have hxeq : x = x⁻¹ := hxFix.symm.trans hxInv
      calc
        x * x = x * x⁻¹ := congrArg (fun z : G => x * z) hxeq
        _ = 1 := by simp
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hxx)
    have hp : orderOf x ∣ post.od.p := by
      simpa [post.od.P0_card] using Subgroup.orderOf_dvd_natCard post.od.P0 hx
    have hpodd : Odd post.od.p := secondCase_linear_omega_p_odd c w d post.od
    have hcop : Nat.Coprime 2 post.od.p := Nat.coprime_two_left.mpr hpodd
    have h1 : orderOf x ∣ 1 := by
      simpa [hcop.gcd_eq_one] using Nat.dvd_gcd h2 hp
    exact Subgroup.mem_bot.mpr
      (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  have hcard1 : Nat.card post.od.P0 = 1 := by rw [hP0bot]; simp
  exact post.od.hp_prime.ne_one (post.od.P0_card.symm.trans hcard1)

end CFSG.GorensteinWalter

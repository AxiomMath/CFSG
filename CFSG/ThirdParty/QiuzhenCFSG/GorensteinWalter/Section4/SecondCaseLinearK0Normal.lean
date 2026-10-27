module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normality of the linear inverted Fitting factor

The source writes `K₀ = F(U) ∩ K` and uses that `K₀` is normal in
`H ∩ M`.  The normality in `F(U) ∩ M` supplied by the inverted-subgroup
decomposition is not enough by itself.  This module supplies the missing
source endpoint after the ambient Sylow has been placed in `M`: `S₀` centralizes
`U`, and `H = U S` then gives the required extension from `U ∩ M` to `H ∩ M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise

private lemma S0_index_of_centralizerSetup
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index = 2 := by
  classical
  have hmap : (c.S0.subgroupOf (c.S : Subgroup G)).map
      (c.S : Subgroup G).subtype = c.S0 := by
    ext y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hx
    · intro hy
      refine Subgroup.mem_map.mpr ⟨⟨y, c.S0_le_S hy⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr hy
  have h1 := Subgroup.card_mul_index
    (c.S0.subgroupOf (c.S : Subgroup G))
  have hc : Nat.card (↥(c.S0.subgroupOf (c.S : Subgroup G))) =
      Nat.card (↥c.S0) := by
    have hcs := Subgroup.card_subtype (c.S : Subgroup G)
      (c.S0.subgroupOf (c.S : Subgroup G))
    rw [hmap] at hcs
    exact hcs.symm
  rw [hc, c.S_index_two] at h1
  have hpos : 0 < Nat.card (↥c.S0) := Nat.card_pos
  exact Nat.mul_right_cancel hpos
    (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h1)

private lemma reflection_product_mem_S0
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {r s : G} (hrS : r ∈ (c.S : Subgroup G)) (hr0 : r ∉ c.S0)
    (hsS : s ∈ (c.S : Subgroup G)) (hs0 : s ∉ c.S0) :
    r * s ∈ c.S0 := by
  classical
  let K : Subgroup (↥(c.S : Subgroup G)) :=
    (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hiff := Subgroup.mul_mem_iff_of_index_two
    (S0_index_of_centralizerSetup c)
    (G := ↥(c.S : Subgroup G)) (H := K)
    (a := ⟨r, hrS⟩) (b := ⟨s, hsS⟩)
  have hmem : (⟨r, hrS⟩ : ↥(c.S : Subgroup G)) *
      ⟨s, hsS⟩ ∈ K := by
    rw [hiff]
    dsimp [K]
    simp [Subgroup.mem_subgroupOf, hr0, hs0]
  simpa using Subgroup.mem_subgroupOf.mp hmem

private lemma k_conj_mem_of_mem_S_of_reflection
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (K : Subgroup G) (s : G)
    (hKleU : K ≤ c.U)
    (hKinv : ∀ x : G, x ∈ K → s * x * s⁻¹ = x⁻¹)
    (hsS : s ∈ (c.S : Subgroup G))
    (hsS0 : s ∉ c.S0)
    (hsI : IsInvolution s)
    (hS0centU : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (c.U : Set G)) :
    ∀ r : G, r ∈ (c.S : Subgroup G) →
      ∀ x : G, x ∈ K → r * x * r⁻¹ ∈ K := by
  have hUnormalH : IsNormalIn c.U c.H :=
    centralizerSetup_U_isNormalIn_H c
  have hsH : s ∈ c.H := centralizerSetup_S_le_H c hsS
  have hs_inv : s⁻¹ = s := by
    exact inv_eq_of_mul_eq_one_right (by
      simpa [pow_two] using hsI.2)
  intro r hrS x hx
  by_cases hr0 : r ∈ c.S0
  · have hcomm : x * r = r * x :=
      (Subgroup.mem_centralizer_iff.mp (hS0centU hr0)) x (hKleU hx)
    have hxr : r * x * r⁻¹ = x := by
      calc
        r * x * r⁻¹ = x * r * r⁻¹ := by rw [hcomm.symm]
        _ = x := by simp
    rw [hxr]
    exact hx
  · have hrs0 : r * s ∈ c.S0 :=
      reflection_product_mem_S0 c hrS hr0 hsS hsS0
    have hyU : s * x * s⁻¹ ∈ c.U :=
      hUnormalH.2 s hsH x (hKleU hx)
    have hcomm : (s * x * s⁻¹) * (r * s) =
        (r * s) * (s * x * s⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hS0centU hrs0)) _ hyU
    have hyfix : (r * s) * (s * x * s⁻¹) * (r * s)⁻¹ =
        s * x * s⁻¹ := by
      calc
        (r * s) * (s * x * s⁻¹) * (r * s)⁻¹ =
            (s * x * s⁻¹) * (r * s) * (r * s)⁻¹ := by
              rw [hcomm.symm]
        _ = s * x * s⁻¹ := by group
    have hxinv : s * x * s⁻¹ ∈ K := by
      rw [hKinv x hx]
      exact K.inv_mem hx
    have hconj : r * x * r⁻¹ =
        (r * s) * (s * x * s⁻¹) * (r * s)⁻¹ := by
      have hss : s * s = 1 := by
        simpa [pow_two] using hsI.2
      calc
        r * x * r⁻¹ = r * (s * s) * x * (s⁻¹ * s⁻¹) * r⁻¹ := by
          rw [hss, hs_inv, hss]
          group
        _ = (r * s) * (s * x * s⁻¹) * (r * s)⁻¹ := by group
    rw [hconj, hyfix]
    exact hxinv

/-! The public theorem is below. -/

public theorem secondCase_linear_K0_normal_H_inter_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (od : SecondCaseLinearOmegaData c w d)
    (hsSE : od.s ∈ (SE : Subgroup d.E))
    (hSleM : (c.S : Subgroup G) ≤ w.M)
    (hS0centU : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (c.U : Set G)) :
    IsNormalIn od.K0 (c.H ⊓ w.M) := by
  classical
  let X : Subgroup G := c.U ⊓ w.M
  have hUleH : c.U ≤ c.H :=
    (centralizerSetup_U_isNormalIn_H c).1
  have hKleX : od.K ≤ X := by
    intro x hx
    have hx' : x ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
      rw [← od.K_inverted]
      exact hx
    exact hx'.1
  have hsSEmap : (od.s : G) ∈
      (SE : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨od.s, hsSE, rfl⟩
  have hsSMmap : (od.s : G) ∈
      (SM : Subgroup w.M).map w.M.subtype := by
    rw [hSEamb] at hsSEmap
    exact hsSEmap.1
  have hsS : (od.s : G) ∈ (c.S : Subgroup G) :=
    hSMleS hsSMmap
  have hsH : (od.s : G) ∈ c.H :=
    centralizerSetup_S_le_H c hsS
  have hsIG : IsInvolution (od.s : G) := od.s_involution
  have hXnorm : ∀ x : G, x ∈ X →
      (od.s : G) * x * (od.s : G)⁻¹ ∈ X := by
    intro x hx
    refine ⟨(centralizerSetup_U_isNormalIn_H c).2
      (od.s : G) hsH x hx.1, ?_⟩
    have hsM : (od.s : G) ∈ w.M := d.E_component.1 od.s.2
    exact w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hXodd : Odd (Nat.card (↥X)) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hKnormalX : IsNormalIn od.K X :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal
      (X := X) (s := (od.s : G)) hsIG
      (Nat.coprime_two_left.mpr hXodd) hXnorm
      (I := od.K) od.K_inverted).2.1
  by_cases hs0 : (od.s : G) ∈ c.S0
  · have hKbot : od.K = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxU : x ∈ c.U := hKleX hx |>.1
      have hcomm : x * (od.s : G) = (od.s : G) * x :=
        (Subgroup.mem_centralizer_iff.mp (hS0centU hs0)) x hxU
      have hfix : (od.s : G) * x * (od.s : G)⁻¹ = x := by
        calc
          (od.s : G) * x * (od.s : G)⁻¹ =
              x * (od.s : G) * (od.s : G)⁻¹ := by rw [hcomm.symm]
          _ = x := by simp
      have hx' : x ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
        rw [← od.K_inverted]
        exact hx
      have hxinv : (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹ := hx'.2
      have hx2 : x ^ 2 = 1 := by
        have hxeq : x = x⁻¹ := hfix.symm.trans hxinv
        calc
          x ^ 2 = x * x := by rw [pow_two]
          _ = x * x⁻¹ := congrArg (fun y : G => x * y) hxeq
          _ = 1 := by simp
      have hdiv2 : orderOf x ∣ 2 :=
        (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).mpr hx2
      have hdivU : orderOf x ∣ Nat.card c.U :=
        Subgroup.orderOf_dvd_natCard c.U hxU
      have hdiv1 : orderOf x ∣ 1 := by
        simpa [(Nat.coprime_two_left.mpr hUodd).gcd_eq_one] using
          Nat.dvd_gcd hdiv2 hdivU
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdiv1)
    have hK0bot : od.K0 = ⊥ := by
      rw [od.K0_eq, hKbot, inf_bot_eq]
    rw [hK0bot]
    refine ⟨bot_le, ?_⟩
    intro g hg x hx
    rw [Subgroup.mem_bot] at hx ⊢
    simpa [hx]
  · have hKconjS : ∀ r : G, r ∈ (c.S : Subgroup G) →
        ∀ x : G, x ∈ od.K → r * x * r⁻¹ ∈ od.K :=
      k_conj_mem_of_mem_S_of_reflection c od.K (od.s : G)
        (hKleX.trans inf_le_left) (by
          intro x hx
          have hx' : x ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
            rw [← od.K_inverted]
            exact hx
          exact hx'.2)
        hsS hs0 hsIG hS0centU
    have hHset : (c.H : Set G) = (c.U : Set G) *
        ((c.S : Subgroup G) : Set G) := by
      have hsup : c.U ⊔ (c.S : Subgroup G) = c.H := by
        simpa [sup_comm] using fact_2_preamble_H_eq_SU_proved hmin c
      rw [← hsup]
      exact Subgroup.coe_mul_of_right_le_normalizer_left c.U
        (c.S : Subgroup G)
        ((centralizerSetup_S_le_H c).trans
          (le_normalizer_of_isNormalIn
            (centralizerSetup_U_isNormalIn_H c)))
    have hKnormalC : IsNormalIn od.K (c.H ⊓ w.M) := by
      refine ⟨?_, ?_⟩
      · intro x hx
        exact ⟨hUleH ((hKleX hx).1), (hKleX hx).2⟩
      · intro g hg x hx
        rcases (show g ∈ (c.H : Set G) from hg.1) with hgH
        rw [hHset] at hgH
        rcases hgH with ⟨u, huU, r, hrS, hgr⟩
        have hgr' : g = u * r := by simpa using hgr.symm
        have hrM : r ∈ w.M := hSleM hrS
        have huM : u ∈ w.M := by
          have hum : g * r⁻¹ ∈ w.M :=
            w.M.mul_mem hg.2 (w.M.inv_mem hrM)
          have hur : u = g * r⁻¹ := by
            rw [hgr']
            group
          rw [hur]
          exact hum
        have huX : u ∈ X := ⟨huU, huM⟩
        have hruK : r * x * r⁻¹ ∈ od.K := hKconjS r hrS x hx
        have huxK : u * (r * x * r⁻¹) * u⁻¹ ∈ od.K :=
          hKnormalX.2 u huX (r * x * r⁻¹) hruK
        rw [hgr']
        convert huxK using 1 <;> group
    have hFUconjC : ∀ g : G, g ∈ c.H ⊓ w.M →
        ∀ x : G, x ∈ c.FU → g * x * g⁻¹ ∈ c.FU := by
      intro g hg x hx
      exact (centralizerSetup_FU_isNormalIn_H c).2 g hg.1 x hx
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [od.K0_eq] at hx
      exact hKnormalC.1 hx.2
    · intro g hg x hx
      rw [od.K0_eq] at hx ⊢
      exact ⟨hFUconjC g hg x hx.1,
        hKnormalC.2 g hg x hx.2⟩

end CFSG.GorensteinWalter

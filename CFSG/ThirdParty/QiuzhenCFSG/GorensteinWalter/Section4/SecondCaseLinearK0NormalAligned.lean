module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingOddCoreEquality
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The aligned factor route for `K₀` normality

This module records the aligned core of the source argument.  An aligned
Sylow subgroup of `M` gives
`H ∩ M = (U ∩ M) · S_M`; if the source commutator identity is supplied, the
commutator is normal under the two factors and hence `K₀` is normal.

The conditional theorem below keeps the commutator identity as an explicit
source-facing input.  The separate aligned producer obtains it from the
quotient-torus comparison and feeds it to this core.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise commutatorElement

/-! A commutator is invariant under any subgroup which normalizes both
factors. -/

private theorem commutator_mem_of_normalized
    {G : Type u} [Group G]
    (A X N : Subgroup G)
    (hA : ∀ n : G, n ∈ N → ∀ a : G, a ∈ A →
      n * a * n⁻¹ ∈ A)
    (hX : ∀ n : G, n ∈ N → ∀ x : G, x ∈ X →
      n * x * n⁻¹ ∈ X) :
    ∀ n : G, n ∈ N → ∀ z : G, z ∈ ⁅A, X⁆ →
      n * z * n⁻¹ ∈ ⁅A, X⁆ := by
  intro n hn
  let f : G →* G := (MulAut.conj n).toMonoidHom
  have hAmap : A.map f = A := by
    apply le_antisymm
    · intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨a, ha, rfl⟩
      exact hA n hn a ha
    · intro y hy
      have hninv : n⁻¹ ∈ N := N.inv_mem hn
      have hy' : n⁻¹ * y * (n⁻¹)⁻¹ ∈ A := hA n⁻¹ hninv y hy
      exact Subgroup.mem_map.mpr ⟨n⁻¹ * y * (n⁻¹)⁻¹, hy', by
        simp [f, MulAut.conj_apply]
        group⟩
  have hXmap : X.map f = X := by
    apply le_antisymm
    · intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact hX n hn x hx
    · intro y hy
      have hninv : n⁻¹ ∈ N := N.inv_mem hn
      have hy' : n⁻¹ * y * (n⁻¹)⁻¹ ∈ X := hX n⁻¹ hninv y hy
      exact Subgroup.mem_map.mpr ⟨n⁻¹ * y * (n⁻¹)⁻¹, hy', by
        simp [f, MulAut.conj_apply]
        group⟩
  have hCmap : (⁅A, X⁆).map f = ⁅A, X⁆ := by
    rw [Subgroup.map_commutator, hAmap, hXmap]
  intro z hz
  have hz' : f z ∈ (⁅A, X⁆).map f :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  rw [hCmap] at hz'
  simpa [f, MulAut.conj_apply] using hz'

/-! ## The aligned factorization -/

private theorem aligned_H_inter_M_eq_U_inter_M_sup_SM
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (SM : Sylow 2 (↥w.M))
    (hSMcent : (SM : Subgroup w.M).map w.M.subtype ≤
      Subgroup.centralizer ({c.t} : Set G)) :
    (c.U ⊓ w.M) ⊔ ((SM : Subgroup w.M).map w.M.subtype) =
      c.H ⊓ w.M := by
  let X : Subgroup G := c.U ⊓ w.M
  let SMG : Subgroup G := (SM : Subgroup w.M).map w.M.subtype
  let M0 : Subgroup G := c.H ⊓ w.M
  have hSMGleH : SMG ≤ c.H := by
    intro x hx
    rw [c.H_eq_centralizer]
    exact hSMcent hx
  have hSMGleM : SMG ≤ w.M :=
    Subgroup.map_subtype_le (SM : Subgroup w.M)
  have hSMGleM0 : SMG ≤ M0 := le_inf hSMGleH hSMGleM
  have hUleH : c.U ≤ c.H :=
    (centralizerSetup_U_isNormalIn_H c).1
  have hXleM0 : X ≤ M0 := by
    intro x hx
    exact ⟨hUleH hx.1, hx.2⟩
  have hXnormalM0 : IsNormalIn X M0 := by
    refine ⟨hXleM0, ?_⟩
    intro g hg x hx
    refine ⟨(centralizerSetup_U_isNormalIn_H c).2 g hg.1 x hx.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hg.2 hx.2) (w.M.inv_mem hg.2)
  let M0M : Subgroup w.M := M0.subgroupOf w.M
  let XM : Subgroup w.M := X.subgroupOf w.M
  let X0 : Subgroup M0M := XM.subgroupOf M0M
  have hM0M_eq : M0M = c.H.comap w.M.subtype := by
    ext x
    simp [M0M, M0]
  have hXM_eq : XM = c.U.comap w.M.subtype := by
    ext x
    simp [XM, X]
  have hSMleM0M : (SM : Subgroup w.M) ≤ M0M := by
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    exact hSMGleM0 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  let P0 : Sylow 2 M0M := SM.subtype hSMleM0M
  have hXMleM0M : XM ≤ M0M := by
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    exact hXleM0 (Subgroup.mem_subgroupOf.mp hx)
  have hX0normal : X0.Normal := by
    rw [show X0 = XM.subgroupOf M0M by rfl,
      Subgroup.normal_subgroupOf_iff hXMleM0M]
    intro x y hx hy
    apply Subgroup.mem_subgroupOf.mpr
    apply hXnormalM0.2 (y : G)
      (Subgroup.mem_subgroupOf.mp hy) (x : G)
      (Subgroup.mem_subgroupOf.mp hx)
  have hU0normalH : (c.U.subgroupOf c.H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUleH]
    intro x y hx hy
    exact (centralizerSetup_U_isNormalIn_H c).2 (y : G) hy (x : G) hx
  have hSleH : (c.S : Subgroup G) ≤ c.H :=
    centralizerSetup_S_le_H c
  have hHsup : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU_proved hmin c
  let qH : c.H →* (c.H ⧸ c.U.subgroupOf c.H) :=
    QuotientGroup.mk' (c.U.subgroupOf c.H)
  let SH : Subgroup c.H := (c.S : Subgroup G).subgroupOf c.H
  let : (c.U.subgroupOf c.H).Normal := hU0normalH
  have hSHp : IsPGroup 2 SH := c.S.isPGroup'.comap_subtype
  have hSHsup : SH ⊔ c.U.subgroupOf c.H = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    have hxG : (x : G) ∈ (c.S : Subgroup G) ⊔ c.U := by
      rw [hHsup]
      exact x.2
    have hmap : (SH ⊔ c.U.subgroupOf c.H).map c.H.subtype =
        (c.S : Subgroup G) ⊔ c.U := by
      rw [Subgroup.map_sup]
      simp [SH, Subgroup.map_subgroupOf_eq_of_le hSleH,
        Subgroup.map_subgroupOf_eq_of_le hUleH]
    have hxmap : (x : G) ∈
        (SH ⊔ c.U.subgroupOf c.H).map c.H.subtype := by
      rw [hmap]
      exact hxG
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  have hqHsurj : Function.Surjective (qH.comp SH.subtype) := by
    intro y
    rcases QuotientGroup.mk'_surjective (c.U.subgroupOf c.H) y with ⟨h, rfl⟩
    have hh : h ∈ SH ⊔ c.U.subgroupOf c.H := by
      rw [hSHsup]
      trivial
    rcases (Subgroup.mem_sup_of_normal_right (s := SH)
      (t := c.U.subgroupOf c.H)).mp hh with ⟨s, hs, u, hu, hsu⟩
    have hqu : qH u = 1 := (QuotientGroup.eq_one_iff
      (N := c.U.subgroupOf c.H) u).2 hu
    refine ⟨⟨s, hs⟩, ?_⟩
    change qH (s : c.H) =
      QuotientGroup.mk' (c.U.subgroupOf c.H) h
    calc
      qH (s : c.H) = qH (s : c.H) * 1 := by simp
      _ = qH (s : c.H) * qH u := by rw [hqu]
      _ = qH ((s : c.H) * u) := by rw [map_mul]
      _ = qH h := by rw [hsu]
  have hQH : IsPGroup 2 (c.H ⧸ c.U.subgroupOf c.H) :=
    IsPGroup.of_surjective hSHp (qH.comp SH.subtype) hqHsurj
  have hXMq : IsPGroup 2 (M0M ⧸ X0) := by
    let iH : M0M →* c.H :=
      { toFun := fun x =>
          ⟨(x : G), (Subgroup.mem_subgroupOf.mp x.2).1⟩
        map_one' := by rfl
        map_mul' := by intro x y; rfl }
    have hiHker : (qH.comp iH).ker ≤ X0 := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxU : (x : G) ∈ c.U := by
        have hxq : qH (iH x) = 1 := hx
        have hxU0 : iH x ∈ c.U.subgroupOf c.H :=
          (QuotientGroup.eq_one_iff (N := c.U.subgroupOf c.H)
            (iH x)).mp hxq
        simpa [iH] using Subgroup.mem_subgroupOf.mp hxU0
      apply Subgroup.mem_subgroupOf.mpr
      apply Subgroup.mem_subgroupOf.mpr
      exact ⟨hxU, x.1.2⟩
    exact isPGroup_quotient_of_map_isPGroup_of_ker_le
      (qH.comp iH) X0 hiHker hQH
  have hjoinM0 : (P0 : Subgroup M0M) ⊔ X0 = ⊤ :=
    preambleSylow_sup_of_quotient_pgroup X0 P0 hXMq
  have hjoinM : (SM : Subgroup w.M) ⊔ XM = M0M := by
    have hmap := congrArg (Subgroup.map M0M.subtype) hjoinM0
    rw [Subgroup.map_sup] at hmap
    have hPmap : (P0 : Subgroup M0M).map M0M.subtype =
        (SM : Subgroup w.M) := by
      rw [show (P0 : Subgroup M0M) =
          (SM : Subgroup w.M).subgroupOf M0M by rfl]
      exact Subgroup.map_subgroupOf_eq_of_le hSMleM0M
    have hXMmap : X0.map M0M.subtype = XM := by
      simpa [X0] using Subgroup.map_subgroupOf_eq_of_le hXMleM0M
    rw [hPmap, hXMmap] at hmap
    have htop : (⊤ : Subgroup M0M).map M0M.subtype = M0M := by
      simpa using Subgroup.map_subgroupOf_eq_of_le
        (H := M0M) (K := M0M) le_rfl
    rw [htop] at hmap
    exact hmap
  have hmapM : M0M.map w.M.subtype = M0 := by
    simpa [M0M] using Subgroup.map_subgroupOf_eq_of_le
      (H := M0) (K := w.M) inf_le_right
  have hmapjoin := congrArg (Subgroup.map w.M.subtype) hjoinM
  rw [Subgroup.map_sup, hmapM] at hmapjoin
  simpa [SMG, XM, X, M0, sup_comm] using hmapjoin

/-! ## Normality from the source commutator identity -/

public theorem secondCase_linear_K0_normal_H_inter_M_of_aligned_commutator
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (_hK : IsOddPrimePower (Nat.card K))
    (_e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM : Sylow 2 (↥w.M))
    (hSMcent : (SM : Subgroup w.M).map w.M.subtype ≤
      Subgroup.centralizer ({c.t} : Set G))
    (_hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (_hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (od : SecondCaseLinearOmegaData c w d)
    (_hsSE : od.s ∈ (SE : Subgroup d.E))
    (hKcomm : od.K =
      ⁅(SE : Subgroup d.E).map d.E.subtype, c.U ⊓ w.M⁆) :
    IsNormalIn od.K0 (c.H ⊓ w.M) := by
  classical
  let X : Subgroup G := c.U ⊓ w.M
  let SMG : Subgroup G := (SM : Subgroup w.M).map w.M.subtype
  let M0 : Subgroup G := c.H ⊓ w.M
  let A : Subgroup G := (SE : Subgroup d.E).map d.E.subtype
  have hfactor : X ⊔ SMG = M0 := by
    exact aligned_H_inter_M_eq_U_inter_M_sup_SM hmin c w SM hSMcent
  have hSMGleH : SMG ≤ c.H := by
    intro x hx
    rw [c.H_eq_centralizer]
    exact hSMcent hx
  have hSMGleM : SMG ≤ w.M :=
    Subgroup.map_subtype_le (SM : Subgroup w.M)
  have hSMGleM0 : SMG ≤ M0 := le_inf hSMGleH hSMGleM
  have hUleH : c.U ≤ c.H :=
    (centralizerSetup_U_isNormalIn_H c).1
  have hXleM0 : X ≤ M0 := by
    intro x hx
    exact ⟨hUleH hx.1, hx.2⟩
  have hXnormalM0 : IsNormalIn X M0 := by
    refine ⟨hXleM0, ?_⟩
    intro g hg x hx
    refine ⟨(centralizerSetup_U_isNormalIn_H c).2 g hg.1 x hx.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hg.2 hx.2) (w.M.inv_mem hg.2)
  have hKleX : od.K ≤ X := by
    intro x hx
    have hxI : x ∈ invertedElements X (od.s : G) := by
      rw [← od.K_inverted]
      exact hx
    exact hxI.1
  have hKleM0 : od.K ≤ M0 := hKleX.trans hXleM0
  have hAinvSMG : ∀ g : G, g ∈ SMG → ∀ a : G, a ∈ A →
      g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    change a ∈ (SE : Subgroup d.E).map d.E.subtype at ha
    rw [_hSEamb] at ha
    have hgaSMG : g * a * g⁻¹ ∈ SMG :=
      SMG.mul_mem (SMG.mul_mem hg ha.1) (SMG.inv_mem hg)
    have hgaE : g * a * g⁻¹ ∈ d.E :=
      d.E_normal.2 g (hSMGleM hg) a ha.2
    change g * a * g⁻¹ ∈ (SE : Subgroup d.E).map d.E.subtype
    rw [_hSEamb]
    exact ⟨hgaSMG, hgaE⟩
  have hXinvSMG : ∀ g : G, g ∈ SMG → ∀ x : G, x ∈ X →
      g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    exact hXnormalM0.2 g (hSMGleM0 hg) x hx
  have hsM : (od.s : G) ∈ w.M :=
    d.E_component.1 od.s.2
  have hsX : ∀ x : G, x ∈ X →
      (od.s : G) * x * (od.s : G)⁻¹ ∈ X := by
    intro x hx
    refine ⟨(centralizerSetup_U_isNormalIn_H c).2
      (od.s : G) od.s_mem_H x hx.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hXodd : Odd (Nat.card (↥X)) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hKnormalX : IsNormalIn od.K X :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal
      (X := X) (s := (od.s : G)) od.s_involution
      (Nat.coprime_two_left.mpr hXodd) hsX
      (I := od.K) od.K_inverted).2.1
  have hKnormalSMG : ∀ g : G, g ∈ SMG → ∀ x : G, x ∈ od.K →
      g * x * g⁻¹ ∈ od.K := by
    intro g hg x hx
    rw [hKcomm] at hx ⊢
    exact commutator_mem_of_normalized A X SMG hAinvSMG hXinvSMG
      g hg x hx
  have hKnormalM0 : IsNormalIn od.K M0 := by
    refine ⟨hKleM0, ?_⟩
    intro g hg x hx
    let X0 : Subgroup M0 := X.subgroupOf M0
    let SM0 : Subgroup M0 := SMG.subgroupOf M0
    have hX0normal : X0.Normal := by
      rw [Subgroup.normal_subgroupOf_iff hXleM0]
      intro x0 y0 hx0 hy0
      exact hXnormalM0.2 (y0 : G) hy0 (x0 : G) hx0
    let : X0.Normal := hX0normal
    have hsup0 : X0 ⊔ SM0 = ⊤ := by
      calc
        X0 ⊔ SM0 = (X ⊔ SMG).subgroupOf M0 := by
          rw [Subgroup.subgroupOf_sup hXleM0 hSMGleM0]
        _ = M0.subgroupOf M0 := by rw [hfactor]
        _ = ⊤ := Subgroup.subgroupOf_self M0
    have hg0 : (⟨g, hg⟩ : M0) ∈ X0 ⊔ SM0 := by
      rw [hsup0]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left (s := X0)
      (t := SM0)).mp hg0 with ⟨u, hu, v, hv, huv⟩
    have huX : (u : G) ∈ X :=
      Subgroup.mem_subgroupOf.mp hu
    have hvSMG : (v : G) ∈ SMG :=
      Subgroup.mem_subgroupOf.mp hv
    have hvx : (v : G) * x * (v : G)⁻¹ ∈ od.K :=
      hKnormalSMG (v : G) hvSMG x hx
    have huvx : (u : G) * ((v : G) * x * (v : G)⁻¹) *
        (u : G)⁻¹ ∈ od.K :=
      hKnormalX.2 (u : G) huX _ hvx
    have hguv : (u : G) * (v : G) = g :=
      congrArg (fun z : M0 => (z : G)) huv
    rw [← hguv]
    have hconj_eq :
        ((u : G) * (v : G)) * x * ((u : G) * (v : G))⁻¹ =
          (u : G) * ((v : G) * x * (v : G)⁻¹) * (u : G)⁻¹ := by
      group
    rw [hconj_eq]
    exact huvx
  have hK0normalM0 : IsNormalIn od.K0 M0 := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [od.K0_eq] at hx
      exact ⟨(centralizerSetup_FU_isNormalIn_H c).1 hx.1,
        (hKleM0 hx.2).2⟩
    · intro g hg x hx
      rw [od.K0_eq] at hx ⊢
      exact ⟨(centralizerSetup_FU_isNormalIn_H c).2 g hg.1 x hx.1,
        hKnormalM0.2 g hg x hx.2⟩
  exact hK0normalM0

end CFSG.GorensteinWalter

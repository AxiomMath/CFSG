module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27PiCentralizes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingOddCoreEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma22
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# `O₂(M)` sits inside `O₂(Ĥ)` for Lemma 2.7

The paper's `O₂(M) = 1` step is split into two honest pieces:

1. `O₂(M)` centralizes `F(U) = O_{2'}(F(Ĥ))` by Bender 1.7(ii), and then
   Fact 1.1(iv) upgrades this to centralization of `U` (using that
   `N_G(F(U)) = Ĥ`, so `O₂(M) ≤ Ĥ` and hence acts on `U`).
2. Any `2`-subgroup of `Ĥ` that centralizes `U` lies in `O₂(Ĥ)`; this is a
   Sylow-transport argument inside `Ĥ`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- `O(H)` is normal in `H`, in ambient form. -/
private theorem oddCoreOf_isNormalIn {G : Type u} [Group G]
    (H : Subgroup G) : IsNormalIn (oddCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥H)).conj_mem y hy (⟨h, hh⟩ : ↥H)

/-- The Fitting subgroup of a nontrivial finite solvable group is
nontrivial. -/
private theorem nontrivial_of_subgroup_ne_bot {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : H ≠ ⊥) : Nontrivial (↥H) := by
  classical
  have hcard : 1 < Nat.card (↥H) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := H)).2 hH
  let : Fintype (↥H) := Fintype.ofFinite _
  exact (Fintype.one_lt_card_iff_nontrivial (α := ↥H)).mp (by
    simpa [Nat.card_eq_fintype_card] using hcard)

/-- The Fitting subgroup of a nontrivial finite solvable group is
nontrivial. -/
private theorem fittingSubgroup_ne_bot_of_solvable
    {G : Type u} [Group G] [Finite G]
    (hGnt : Nontrivial G) (hsolv : Group.IsSolvable G) : (fittingSubgroup G) ≠ ⊥ := by
  classical
  let : Group.IsSolvable G := hsolv
  obtain ⟨M, hMnormal, hMne, hMmin⟩ := exists_minimal_normal hsolv hGnt
  have : M.Normal := hMnormal
  have : IsMinimalNormal M := ⟨fun K hKnorm hKle => by
    by_cases hKbot : K = ⊥
    · exact Or.inl hKbot
    · exact Or.inr (hMmin K hKnorm hKle hKbot)⟩
  have hMleF : M ≤ fittingSubgroup G := by
    have hMleZ : M ≤ centerIn (G := G) (fittingSubgroup G) :=
      minimalNormal_solvable_le_centerIn_fittingSubgroup M
    exact hMleZ.trans (by intro x hx; exact hx.1)
  intro hF
  have hMbot : M = ⊥ := le_bot_iff.mp (hMleF.trans (le_of_eq hF))
  exact hMne hMbot

/-- A conjugate of a centralizer element by a normalizer element of `U`
still centralizes `U`. -/
private theorem conj_mem_centralizer_of_mem_centralizer_of_mem_normalizer
    {G : Type u} [Group G]
    (U : Subgroup G) {g x : G}
    (hgN : g ∈ Subgroup.normalizer (U : Set G))
    (hxC : x ∈ Subgroup.centralizer (U : Set G)) :
    g⁻¹ * x * g ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hgu : g * u * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hgN u).1 hu
  have hx : x * (g * u * g⁻¹) = (g * u * g⁻¹) * x :=
    (Subgroup.mem_centralizer_iff.mp hxC (g * u * g⁻¹) hgu).symm
  have h1 : (g⁻¹ * x * g) * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
  have h2 : g⁻¹ * (x * (g * u * g⁻¹)) * g =
      g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [hx]
  have h3 : g⁻¹ * ((g * u * g⁻¹) * x) * g = u * (g⁻¹ * x * g) := by group
  exact (h1.trans (h2.trans h3)).symm

/-- `O₂(M)` centralizes `U = O(Ĥ)` under the Lemma 2.7 hypotheses. -/
public theorem twoCoreOf_centralizes_U_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) (h26 : CentralizerStructure c) :
    twoCoreOf M ≤ Subgroup.centralizer (c.U : Set G) := by
  classical
  rcases hM with ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩
  have hU_eq : c.U = oddCoreOf c.Hhat := h26.1
  -- `2 ∈ π(F(Ĥ))`, since the involution `t` lies in `O₂(Ĥ) ≤ F(Ĥ)`.
  have h2π : 2 ∈ primesOfOrder (fittingSubgroupOf c.Hhat) := by
    have ht2 : c.t ∈ twoCoreOf c.Hhat := centralizerStructure_t_mem_twoCore c h26
    have hq2 : twoCoreOf c.Hhat = qCoreOf c.Hhat 2 := by
      rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton c.Hhat 2 Nat.prime_two]
    have hxt : c.t ∈ qCoreOf c.Hhat 2 := by simpa [hq2] using ht2
    have hxF : c.t ∈ fittingSubgroupOf c.Hhat :=
      qCoreOf_le_fittingSubgroupOf c.Hhat 2 Nat.prime_two hxt
    have hord : orderOf c.t = 2 :=
      orderOf_eq_prime c.t_involution.2 c.t_involution.1
    have h2dvd : 2 ∣ Nat.card (↥(fittingSubgroupOf c.Hhat)) := by
      have hdvd : orderOf c.t ∣ Nat.card (↥(fittingSubgroupOf c.Hhat)) := by
        let : Fintype (↥(fittingSubgroupOf c.Hhat)) := Fintype.ofFinite _
        have h := orderOf_dvd_card (x := (⟨c.t, hxF⟩ : fittingSubgroupOf c.Hhat))
        simpa [Nat.card_eq_fintype_card, Subgroup.orderOf_mk] using h
      rwa [hord] at hdvd
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, Nat.card_pos.ne'⟩
  -- Step 1: `O₂(M) ≤ C_G(F(U))`.
  have hPleCFU : twoCoreOf M ≤ Subgroup.centralizer (c.FU : Set G) := by
    have hOddCent := twoCoreOf_centralizes_oddPart_fittingSubgroupOf_of_control
      (minimalCounterexample_isSimple hmin) c M hControl h2π
    have hEq : piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} = c.FU := by
      calc
        piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} =
            fittingSubgroupOf (oddCoreOf c.Hhat) :=
          (fittingSubgroupOf_oddCore_eq_oddPart_fittingSubgroupOf c.Hhat).symm
        _ = fittingSubgroupOf c.U := by rw [hU_eq]
        _ = c.FU := rfl
    simpa [hEq] using hOddCent
  -- `F(U) ≠ 1`: `U` is a nontrivial solvable group.
  have hFU_ne : c.FU ≠ ⊥ := by
    have hU_ne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
    have hUodd : Odd (Nat.card (↥c.U)) := by
      rw [hU_eq]
      exact odd_card_oddCoreOf c.Hhat
    have hUsolv : Group.IsSolvable (↥c.U) := odd_order_theorem (↥c.U) hUodd
    have hF_ne : (fittingSubgroup (↥c.U)) ≠ ⊥ :=
      fittingSubgroup_ne_bot_of_solvable
        (nontrivial_of_subgroup_ne_bot c.U hU_ne) hUsolv
    intro hFUbot
    have hFUmap : c.FU = (fittingSubgroup (↥c.U)).map c.U.subtype := rfl
    rw [hFUmap] at hFUbot
    exact hF_ne ((Subgroup.map_eq_bot_iff_of_injective
      (H := fittingSubgroup (↥c.U)) (f := c.U.subtype) c.U.subtype_injective).1 hFUbot)
  -- `N_G(F(U)) = Ĥ`: `F(U)` is characteristic in `U ◃ Ĥ`, nontrivial and
  -- proper, so its normalizer cannot be `G`.
  have hFUnormHhat : IsNormalIn c.FU c.Hhat := by
    have hUnormH : IsNormalIn c.U c.Hhat := by
      simpa [hU_eq] using oddCoreOf_isNormalIn c.Hhat
    have hFchar : (fittingSubgroup (↥c.U)).Characteristic := by infer_instance
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := c.Hhat) (F := c.U) (K := fittingSubgroup (↥c.U)) hFchar hUnormH
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.Hhat
    exact h
  have hHleNFU : c.Hhat ≤ Subgroup.normalizer (c.FU : Set G) :=
    le_normalizer_of_isNormalIn hFUnormHhat
  have hNFU_eq : Subgroup.normalizer (c.FU : Set G) = c.Hhat := by
    apply (c.Hhat_maximal.ne_top_iff_eq hHleNFU).mp
    intro hNtop
    have hN : c.FU.Normal :=
      (Subgroup.normalizer_eq_top_iff (H := c.FU)).mp hNtop
    rcases (haveI := hN; (minimalCounterexample_isSimple hmin).eq_bot_or_eq_top_of_normal
        c.FU) with hFUbot | hFUtop
    · exact hFU_ne hFUbot
    · have hFUleHhat : c.FU ≤ c.Hhat := hFUnormHhat.1
      rw [hFUtop] at hFUleHhat
      exact c.Hhat_maximal.ne_top (top_unique hFUleHhat)
  -- Now `O₂(M) ≤ Ĥ`, so it acts on `U`.
  have hPleHhat : twoCoreOf M ≤ c.Hhat := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (c.FU : Set G) :=
      Subgroup.centralizer_le_normalizer (c.FU : Set G) (hPleCFU hx)
    rw [hNFU_eq] at hxN
    exact hxN
  have hUnormH : IsNormalIn c.U c.Hhat := by
    simpa [hU_eq] using oddCoreOf_isNormalIn c.Hhat
  have hPleNU : twoCoreOf M ≤ Subgroup.normalizer (c.U : Set G) :=
    hPleHhat.trans (le_normalizer_of_isNormalIn hUnormH)
  -- Fact 1.1(iv): `F(U) ≤ U` is normal and self-centralizing in the odd
  -- solvable group `U`.
  have hFUnormU : IsNormalIn c.FU c.U := by
    have hFchar : (fittingSubgroup (↥c.U)).Characteristic := by infer_instance
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := c.U) (F := c.U) (K := fittingSubgroup (↥c.U)) hFchar
      (by
        refine ⟨?_, ?_⟩
        · intro x hx; exact hx
        · intro u hu x hx
          exact c.U.mul_mem (c.U.mul_mem hu hx) (c.U.inv_mem hu))
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.U
    exact h
  have hK1norm : ((c.FU).subgroupOf c.U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := c.U) (N := c.FU)
      (le_normalizer_of_isNormalIn hFUnormU)
  have hself : c.U ⊓ Subgroup.centralizer (c.FU : Set G) ≤ c.FU := by
    have hUodd : Odd (Nat.card (↥c.U)) := by
      rw [hU_eq]
      exact odd_card_oddCoreOf c.Hhat
    have hUsolv : Group.IsSolvable (↥c.U) := odd_order_theorem (↥c.U) hUodd
    change c.U ⊓ Subgroup.centralizer
        (((fittingSubgroup (↥c.U)).map c.U.subtype : Subgroup G) : Set G) ≤
      (fittingSubgroup (↥c.U)).map c.U.subtype
    exact fact_1_2_centralizer_fitting_le_fitting c.U hUsolv
  have hPp : IsPGroup 2 (twoCoreOf M) := by
    have hq2 : qCoreOf M 2 = twoCoreOf M := by
      rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
    exact (qCoreOf_isPGroup M 2).of_equiv (MulEquiv.subgroupCongr hq2)
  have hUodd : Odd (Nat.card (↥c.U)) := by
    rw [hU_eq]
    exact odd_card_oddCoreOf c.Hhat
  have hcop : Nat.Coprime (Nat.card (twoCoreOf M)) (Nat.card (↥c.U)) := by
    rcases (IsPGroup.iff_card (p := 2) (G := twoCoreOf M)).mp hPp with ⟨n, hn⟩
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hUodd)
  have hUsolv : Group.IsSolvable (↥c.U) := odd_order_theorem (↥c.U) hUodd
  exact centralizes_of_normal_selfCentralizing_coprime (twoCoreOf M) c.U c.FU
    hPleNU hFUnormU.1 hK1norm hPleCFU hself hcop hUsolv

/-- A `2`-subgroup of `Ĥ` that centralizes `U` is contained in `O₂(Ĥ)`. -/
public theorem twoCoreOf_le_twoCoreOf_Hhat_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) (h26 : CentralizerStructure c) :
    twoCoreOf M ≤ twoCoreOf c.Hhat := by
  classical
  rcases hM with ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩
  have hPcentU := twoCoreOf_centralizes_U_of_Lemma27Hypothesis hmin c M
    ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩ h26
  have hU_eq : c.U = oddCoreOf c.Hhat := h26.1
  have hUnormH : IsNormalIn c.U c.Hhat := by
    simpa [hU_eq] using oddCoreOf_isNormalIn c.Hhat
  have hPleHhat : twoCoreOf M ≤ c.Hhat := by
    have hN_eq : Subgroup.normalizer (c.U : Set G) = c.Hhat := by
      -- `N_G(U) = Ĥ`: `U` is characteristic in `Ĥ`, nontrivial, proper.
      have hHleN : c.Hhat ≤ Subgroup.normalizer (c.U : Set G) :=
        le_normalizer_of_isNormalIn hUnormH
      apply (c.Hhat_maximal.ne_top_iff_eq hHleN).mp
      intro hNtop
      have hN : c.U.Normal :=
        (Subgroup.normalizer_eq_top_iff (H := c.U)).mp hNtop
      rcases (haveI := hN; (minimalCounterexample_isSimple hmin).eq_bot_or_eq_top_of_normal
          c.U) with hUbot | hUtop
      · exact (lemma_2_2 hmin c).2 hUbot
      · have hUleHhat : c.U ≤ c.Hhat := hUnormH.1
        rw [hUtop] at hUleHhat
        exact c.Hhat_maximal.ne_top (top_unique hUleHhat)
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (c.U : Set G) :=
      Subgroup.centralizer_le_normalizer (c.U : Set G) (hPcentU hx)
    rw [hN_eq] at hxN
    exact hxN
  -- The `2`-subgroup `P = O₂(M)` of `Ĥ` is contained in a Sylow `2`-subgroup
  -- `R` of `Ĥ`; since all Sylow subgroups of `Ĥ` are conjugate to `S`, the
  -- centralizer part is transported into `O₂(Ĥ)`.
  let P : Subgroup G := twoCoreOf M
  have hPsubH : P ≤ c.Hhat := by simpa [P] using hPleHhat
  let P' : Subgroup (↥c.Hhat) := P.subgroupOf c.Hhat
  have hP'p : IsPGroup 2 P' := by
    have hPp : IsPGroup 2 P := by
      have hq2 : qCoreOf M 2 = twoCoreOf M := by
        rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
      exact (qCoreOf_isPGroup M 2).of_equiv (MulEquiv.subgroupCongr hq2)
    exact hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPsubH).symm
  obtain ⟨R, hPR⟩ := IsPGroup.exists_le_sylow (G := ↥c.Hhat) (p := 2) hP'p
  let S' : Sylow 2 (↥c.Hhat) :=
    c.S.subtype ((centralizerSetup_S_le_H c).trans c.H_le_Hhat)
  obtain ⟨h, hR⟩ := MulAction.exists_smul_eq
    (M := ↥c.Hhat) S' R
  let g : G := h
  have hgH : g ∈ c.Hhat := h.property
  have hOnorm : IsNormalIn (twoCoreOf c.Hhat) c.Hhat := by
    have hq2 : twoCoreOf c.Hhat = qCoreOf c.Hhat 2 := by
      rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton c.Hhat 2 Nat.prime_two]
    simpa [hq2] using qCoreOf_normal_in c.Hhat 2
  have hSinter : (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) =
      twoCoreOf c.Hhat := h26.2.1
  intro x hx
  have hxH : x ∈ c.Hhat := hPsubH hx
  let z : ↥c.Hhat := ⟨x, hxH⟩
  have hzP' : z ∈ P' := hx
  have hzR : z ∈ (R : Subgroup (↥c.Hhat)) := hPR hzP'
  have hzS' : z ∈ (((h • S' : Sylow 2 (↥c.Hhat)) : Subgroup (↥c.Hhat))) := by
    simpa [hR] using hzR
  have hzS_sub : z ∈ (MulAut.conj h • (S' : Subgroup (↥c.Hhat))) := by
    rw [Sylow.coe_subgroup_smul] at hzS'
    exact hzS'
  have hzinvS : (MulAut.conj h)⁻¹ • z ∈ (S' : Subgroup (↥c.Hhat)) :=
    (Subgroup.mem_pointwise_smul_iff_inv_smul_mem
      (a := MulAut.conj h) (S := S') (x := z)).1 hzS_sub
  have hzinv : (h⁻¹ * z * h : ↥c.Hhat) ∈ (S' : Set (↥c.Hhat)) :=
    hzinvS
  let y : G := ((h⁻¹ * z * h : ↥c.Hhat) : G)
  have hyS : y ∈ (c.S : Subgroup G) := by
    have hSmap : (S' : Subgroup (↥c.Hhat)).map c.Hhat.subtype =
        (c.S : Subgroup G) := by
      dsimp [S']
      exact Subgroup.map_subgroupOf_eq_of_le ((centralizerSetup_S_le_H c).trans c.H_le_Hhat)
    rw [← hSmap]
    exact Subgroup.mem_map.mpr ⟨(h⁻¹ * z * h : ↥c.Hhat), hzinv, rfl⟩
  have hgN : g ∈ Subgroup.normalizer (c.U : Set G) :=
    (le_normalizer_of_isNormalIn hUnormH) hgH
  have hxCU : x ∈ Subgroup.centralizer (c.U : Set G) := hPcentU hx
  have hyC : y ∈ Subgroup.centralizer (c.U : Set G) := by
    dsimp [y]
    exact conj_mem_centralizer_of_mem_centralizer_of_mem_normalizer c.U hgN hxCU
  have hyO2 : y ∈ twoCoreOf c.Hhat := by
    have hySC : y ∈ (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
      ⟨hyS, hyC⟩
    rw [hSinter] at hySC
    exact hySC
  have hxeq : x = g * y * g⁻¹ := by
    change x = (h : G) * ((h⁻¹ * z * h : ↥c.Hhat) : G) * (h : G)⁻¹
    simp [z, Subgroup.coe_mul]
    group
  rw [hxeq]
  exact hOnorm.2 g hgH y hyO2

end CFSG.GorensteinWalter

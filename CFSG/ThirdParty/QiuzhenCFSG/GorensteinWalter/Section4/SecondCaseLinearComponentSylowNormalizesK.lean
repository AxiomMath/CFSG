module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FixedFactorCentralizesSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSubgroupCharacteristic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The aligned component Sylow normalizes the inverted factor

The quotient image of the inverted factor is the odd cyclic torus supplied by
the aligned PSL₂ decomposition.  A component-Sylow element therefore acts on
that image by a rotation or a reflection.  Fact 1.5 separates the resulting
conjugate into its fixed and inverted factors; the fixed factor has trivial
quotient image, and the odd centre removes the remaining central fibre.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! A central fibre on which a 2-element acts by a translation is trivial. -/

private theorem central_twist_eq_one_of_odd_center
    {E : Type u} [Group E] [Finite E]
    {a x z : E} (hz : z ∈ Subgroup.center E)
    (hodd : Odd (Nat.card (Subgroup.center E)))
    (hcomm : a * z = z * a)
    (hrel : a * x * a⁻¹ = z * x)
    (ha : ∃ n : ℕ, orderOf a = 2 ^ n) : z = 1 := by
  have hza : ∀ n : ℕ, a ^ n * z = z * a ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      calc
        (a ^ n * a) * z = a ^ n * (a * z) := by group
        _ = a ^ n * (z * a) := by rw [hcomm]
        _ = (a ^ n * z) * a := by group
        _ = (z * a ^ n) * a := by rw [ih]
        _ = z * (a ^ n * a) := by group
  have hiter : ∀ n : ℕ, a ^ n * x * (a ^ n)⁻¹ = z ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        a ^ (n + 1) * x * (a ^ (n + 1))⁻¹ =
            a ^ n * (a * x * a⁻¹) * (a ^ n)⁻¹ := by
              rw [pow_succ, mul_inv_rev]
              group
        _ = a ^ n * (z * x) * (a ^ n)⁻¹ := by rw [hrel]
        _ = (a ^ n * z) * x * (a ^ n)⁻¹ := by group
        _ = (z * a ^ n) * x * (a ^ n)⁻¹ := by rw [hza n]
        _ = z * (a ^ n * x * (a ^ n)⁻¹) := by group
        _ = z * (z ^ n * x) := by rw [ih]
        _ = z ^ (n + 1) * x := by rw [pow_succ]; group
  obtain ⟨n, hn⟩ := ha
  have hpow : z ^ orderOf a = 1 := by
    have h := hiter (orderOf a)
    rw [pow_orderOf_eq_one] at h
    have h' : x = z ^ orderOf a * x := by simpa using h
    have h'' : z ^ orderOf a * x = 1 * x := by simpa using h'.symm
    exact mul_right_cancel h''
  have hdiv : orderOf z ∣ 2 ^ n := by
    rw [← hn]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hzodd : Odd (orderOf z) :=
    Odd.of_dvd_nat hodd
      (Subgroup.orderOf_dvd_natCard (Subgroup.center E) hz)
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdiv with ⟨j, hj, hzpow⟩
  by_cases hj0 : j = 0
  · simpa [hj0] using hzpow
  · have htwo : 2 ∣ orderOf z := by
      rw [hzpow]
      refine ⟨2 ^ (j - 1), ?_⟩
      calc
        2 ^ j = 2 ^ (j - 1 + 1) := by congr 1; omega
        _ = 2 ^ (j - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (j - 1) := by rw [mul_comm]
    exact False.elim (hzodd.not_two_dvd_nat htwo)

/-! The quotient image of a fixed factor in the odd torus is trivial. -/

private theorem quotient_fixed_factor_eq_one
    {E : Type u} [Group E] [Finite E]
    (q : E →* (E ⧸ Subgroup.center E))
    (UEbar : Subgroup (E ⧸ Subgroup.center E))
    {s c : E}
    (hcUE : q c ∈ UEbar)
    (hcs : s * c * s⁻¹ = c)
    (hcinv : BenderGlauberman.IsInvertedBy (q s) UEbar)
    (hcodd : Odd (orderOf (q c))) : q c = 1 := by
  have hfix : q s * q c * (q s)⁻¹ = q c := by
    calc
      q s * q c * (q s)⁻¹ = q (s * c * s⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      _ = q c := by rw [hcs]
  have hinv : q s * q c * (q s)⁻¹ = (q c)⁻¹ := hcinv (q c) hcUE
  have hsq : (q c) ^ 2 = 1 := by
    have heq : q c = (q c)⁻¹ := hfix.symm.trans hinv
    rw [pow_two]
    calc
      q c * q c = (q c)⁻¹ * q c := by
        exact congrArg (fun z => z * q c) heq
      _ = 1 := by simp
  have hord : orderOf (q c) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsq
  have hord1 : orderOf (q c) = 1 :=
    hcodd.coprime_two_right.eq_one_of_dvd hord
  exact orderOf_eq_one_iff.mp hord1

/-! The quotient action of rotations normalizes the inverted factor. -/

public theorem secondCase_linear_componentSylow_le_normalizer_K
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb_join : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (s : d.E)
    (hsSE : s ∈ (SE : Subgroup d.E))
    (hsI : IsInvolution s)
    (hTcyc : IsCyclic T)
    (hqsnotT : QuotientGroup.mk' (Subgroup.center d.E) s ∉ T)
    (hPdecomp :
      (SE.mapSurjective
          (QuotientGroup.mk'_surjective (Subgroup.center d.E)) :
        Subgroup (d.E ⧸ Subgroup.center d.E)) ≤
        T ⊔ Subgroup.zpowers
          (QuotientGroup.mk' (Subgroup.center d.E) s))
    (hTinv : ∀ x : d.E ⧸ Subgroup.center d.E, x ∈ T →
      QuotientGroup.mk' (Subgroup.center d.E) s * x *
        (QuotientGroup.mk' (Subgroup.center d.E) s)⁻¹ = x⁻¹)
    (hUEbar_le_T :
      ((c.U ⊓ d.E).subgroupOf d.E).map
          (QuotientGroup.mk' (Subgroup.center d.E)) ≤ T)
    (hUEbar_odd : ∀ y : d.E ⧸ Subgroup.center d.E,
      y ∈ ((c.U ⊓ d.E).subgroupOf d.E).map
          (QuotientGroup.mk' (Subgroup.center d.E)) → Odd (orderOf y))
    (hUEbar_inverted :
      BenderGlauberman.IsInvertedBy
        (QuotientGroup.mk' (Subgroup.center d.E) s)
        (((c.U ⊓ d.E).subgroupOf d.E).map
          (QuotientGroup.mk' (Subgroup.center d.E))))
    (K B : Subgroup G)
    (hK_eq : (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hKleE : K ≤ d.E)
    (hKmap :
      (K.subgroupOf d.E).map (QuotientGroup.mk' (Subgroup.center d.E)) =
        ((c.U ⊓ d.E).subgroupOf d.E).map
          (QuotientGroup.mk' (Subgroup.center d.E)))
    (hKcenter :
      (K.subgroupOf d.E) ⊓ Subgroup.center d.E = ⊥)
    (hB : B = centralizerIn (c.U ⊓ w.M) (s : G))
    (hBcentSE : B ≤ Subgroup.centralizer
      (((SE : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G)) :
    ((SE : Subgroup d.E).map d.E.subtype) ≤
      Subgroup.normalizer (K : Set G) := by
  classical
  let X : Subgroup G := c.U ⊓ w.M
  let sG : G := s
  let q : d.E →* (d.E ⧸ Subgroup.center d.E) :=
    QuotientGroup.mk' (Subgroup.center d.E)
  let UEbar : Subgroup (d.E ⧸ Subgroup.center d.E) :=
    ((c.U ⊓ d.E).subgroupOf d.E).map q
  have hUEbar_le_T' : UEbar ≤ T := by
    simpa [UEbar, q] using hUEbar_le_T
  have hUEbar_odd' : ∀ y : d.E ⧸ Subgroup.center d.E,
      y ∈ UEbar → Odd (orderOf y) := by
    simpa [UEbar, q] using hUEbar_odd
  have hUEbar_inverted' :
      BenderGlauberman.IsInvertedBy (q s) UEbar := by
    simpa [UEbar, q] using hUEbar_inverted
  have hKmap' :
      (K.subgroupOf d.E).map q = UEbar := by
    simpa [UEbar, q] using hKmap
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hXodd : Odd (Nat.card (↥X)) := by
    exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hcopX : Nat.Coprime 2 (Nat.card (↥X)) :=
    Nat.coprime_two_left.mpr hXodd
  have hsX : ∀ x : G, x ∈ X → sG * x * sG⁻¹ ∈ X := by
    have hsmap : sG ∈ (SE : Subgroup d.E).map d.E.subtype :=
      Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
    have hsSM : sG ∈ ((SM : Subgroup w.M).map w.M.subtype) := by
      rw [hSEamb_join] at hsmap
      exact hsmap.1
    have hsS : sG ∈ (c.S : Subgroup G) := hSMleS hsSM
    have hsH : sG ∈ c.H := centralizerSetup_S_le_H c hsS
    have hsM : sG ∈ w.M :=
      (Subgroup.map_subtype_le (SM : Subgroup w.M)) hsSM
    intro x hx
    refine ⟨(centralizerSetup_U_isNormalIn_H c).2 sG hsH x hx.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)
  have hsIG : IsInvolution sG := by
    constructor
    · intro hs1
      exact hsI.1 (Subtype.ext hs1)
    · simpa [sG, pow_two] using congrArg Subtype.val hsI.2
  have hKleX : K ≤ X := by
    intro x hx
    have hxI : x ∈ invertedElements X sG := by
      rw [← hK_eq]
      exact hx
    exact hxI.1
  have hKinv : ∀ x : G, x ∈ K →
      sG * x * sG⁻¹ = x⁻¹ := by
    intro x hx
    have hxI : x ∈ invertedElements X sG := by
      rw [← hK_eq]
      exact hx
    exact hxI.2
  have hTcomm : ∀ a b : d.E ⧸ Subgroup.center d.E,
      a ∈ T → b ∈ T → a * b = b * a := by
    let : IsCyclic T := hTcyc
    let : CommGroup T := IsCyclic.commGroup
    intro a b ha hb
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : T) (⟨b, hb⟩ : T))
  have hUEbar_norm :
      T ⊔ Subgroup.zpowers (q s) ≤
        Subgroup.normalizer (UEbar : Set (d.E ⧸ Subgroup.center d.E)) := by
    apply sup_le
    · intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyT : y ∈ T := hUEbar_le_T' (by
          change y ∈ UEbar
          exact hy)
        have hcomm := hTcomm a y ha hyT
        have hconj : a * y * a⁻¹ = y := by
          rw [hcomm]
          group
        rw [hconj]
        exact hy
      · intro hy
        have hzT : a * y * a⁻¹ ∈ T :=
          hUEbar_le_T' hy
        have hainvT : a⁻¹ ∈ T := T.inv_mem ha
        have hcomm := hTcomm a⁻¹ (a * y * a⁻¹) hainvT hzT
        have hback : y = a⁻¹ * (a * y * a⁻¹) * a := by
          group
        have hback' :
            a⁻¹ * (a * y * a⁻¹) * a = a * y * a⁻¹ := by
          rw [hcomm]
          group
        have hyEq : y = a * y * a⁻¹ := hback.trans hback'
        rw [hyEq]
        exact hy
    · apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hUEbar_inverted' y hy]
        exact UEbar.inv_mem hy
      · intro hy
        have hy' :
            q s * (q s * y * (q s)⁻¹) * (q s)⁻¹ ∈ UEbar := by
          rw [hUEbar_inverted' (q s * y * (q s)⁻¹) hy]
          exact UEbar.inv_mem hy
        have hsq : q s * q s = 1 := by
          simpa [pow_two] using congrArg q hsI.2
        have hback :
            q s * (q s * y * (q s)⁻¹) * (q s)⁻¹ = y := by
          have hsinv : (q s)⁻¹ = q s :=
            inv_eq_of_mul_eq_one_right hsq
          calc
            q s * (q s * y * (q s)⁻¹) * (q s)⁻¹ =
                (q s * q s) * y * ((q s)⁻¹ * (q s)⁻¹) := by group
            _ = (q s * q s) * y * (q s * q s) := by rw [hsinv]
            _ = y := by rw [hsq]; simp
        rw [hback] at hy'
        exact hy'
  have hSE_normalizes_X : ∀ a : d.E, a ∈ SE →
      ∀ x : G, x ∈ X →
        (a : G) * x * (a : G)⁻¹ ∈ X := by
    have hU_normal := centralizerSetup_U_isNormalIn_H c
    intro a ha x hx
    have haMap : (a : G) ∈ (SE : Subgroup d.E).map d.E.subtype :=
      Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have haSM : (a : G) ∈ (SM : Subgroup w.M).map w.M.subtype := by
      rw [hSEamb_join] at haMap
      exact haMap.1
    have haS : (a : G) ∈ (c.S : Subgroup G) := hSMleS haSM
    have haH : (a : G) ∈ c.H := centralizerSetup_S_le_H c haS
    have haM : (a : G) ∈ w.M :=
      (Subgroup.map_subtype_le (SM : Subgroup w.M)) haSM
    refine ⟨hU_normal.2 (a : G) haH x hx.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem haM hx.2) (w.M.inv_mem haM)
  have hrot : ∀ a : d.E, a ∈ SE → q a ∈ T →
      ∀ x : G, x ∈ K → (a : G) * x * (a : G)⁻¹ ∈ K := by
    intro a ha hqaT x hx
    have hxX : x ∈ X := hKleX hx
    have hyX : (a : G) * x * (a : G)⁻¹ ∈ X :=
      hSE_normalizes_X a ha x hxX
    let xE : d.E := ⟨x, hKleE hx⟩
    let yE : d.E := a * xE * a⁻¹
    have hyE : (yE : G) ∈ X := by
      simpa [yE] using hyX
    have hxKE : xE ∈ K.subgroupOf d.E :=
      Subgroup.mem_subgroupOf.mpr hx
    have hxUE : q xE ∈ UEbar := by
      have hxUE' : q xE ∈ (K.subgroupOf d.E).map q :=
        Subgroup.mem_map.mpr ⟨xE, hxKE, rfl⟩
      rw [hKmap'] at hxUE'
      exact hxUE'
    have hqaP : q a ∈
        (SE.mapSurjective (QuotientGroup.mk'_surjective
          (Subgroup.center d.E)) : Subgroup (d.E ⧸ Subgroup.center d.E)) := by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hqaJoin : q a ∈ T ⊔ Subgroup.zpowers (q s) := by
      exact hPdecomp hqaP
    have hqaNorm : q a ∈ Subgroup.normalizer (UEbar : Set _) :=
      hUEbar_norm hqaJoin
    have hyUE : q yE ∈ UEbar := by
      have hconj := (Subgroup.mem_normalizer_iff.mp hqaNorm (q xE)).mp hxUE
      simpa [yE, q, map_mul, map_inv] using hconj
    rcases fact_1_5_ii_decomposition hsIG hcopX hsX
      ((a : G) * x * (a : G)⁻¹) hyX with
      ⟨cf, hcfB, i, hiI, hyi⟩
    have hiK : i ∈ K := by
      have hiInv : i ∈ invertedElements X sG := hiI
      rw [← hK_eq] at hiInv
      exact hiInv
    have hiE : i ∈ d.E := hKleE hiK
    let iE : d.E := ⟨i, hiE⟩
    have hiKE : iE ∈ K.subgroupOf d.E :=
      Subgroup.mem_subgroupOf.mpr hiK
    have hiUE : q iE ∈ UEbar := by
      have hiUE' : q iE ∈ (K.subgroupOf d.E).map q :=
        Subgroup.mem_map.mpr ⟨iE, hiKE, rfl⟩
      rw [hKmap'] at hiUE'
      exact hiUE'
    have hcf_eq : cf = (a : G) * x * (a : G)⁻¹ * i⁻¹ := by
      rw [hyi]
      group
    have hcfE : cf ∈ d.E := by
      rw [hcf_eq]
      exact d.E.mul_mem yE.2 (d.E.inv_mem hiE)
    let cfE : d.E := ⟨cf, hcfE⟩
    have hqcfUE : q cfE ∈ UEbar := by
      have hqcf : q cfE = q yE * (q iE)⁻¹ := by
        change q (cfE : d.E) = q yE * (q iE)⁻¹
        rw [show (cfE : d.E) = yE * iE⁻¹ by
          apply Subtype.ext
          change cf = ((a : G) * x * (a : G)⁻¹) * i⁻¹
          rw [hcf_eq]]
        rw [map_mul, map_inv]
      rw [hqcf]
      exact UEbar.mul_mem hyUE (UEbar.inv_mem hiUE)
    have hcf_fix : (s : d.E) * cfE * (s : d.E)⁻¹ = cfE := by
      apply Subtype.ext
      have hcomm : sG * cf = cf * sG :=
        (Subgroup.mem_centralizer_iff.mp hcfB.2) sG (by simp)
      calc
        (s : G) * cf * (s : G)⁻¹ = (cf * (s : G)) * (s : G)⁻¹ := by
          rw [hcomm]
        _ = cf := by simp
    have hqcf_one : q cfE = 1 := by
      apply quotient_fixed_factor_eq_one q UEbar hqcfUE hcf_fix
        hUEbar_inverted
      exact hUEbar_odd (q cfE) hqcfUE
    have hq_i_eq_x : q iE = q xE := by
      have hq_yx : q yE = q xE := by
        calc
          q yE = q a * q xE * (q a)⁻¹ := by
            rw [show yE = a * xE * a⁻¹ by rfl, map_mul, map_mul, map_inv]
          _ = q xE := by
            have hcomm := hTcomm (q a) (q xE) hqaT
              (hUEbar_le_T' hxUE)
            rw [hcomm]
            group
      have hq_yi : q yE = q cfE * q iE := by
        rw [show yE = cfE * iE by
          apply Subtype.ext
          simpa [cfE, iE, yE] using hyi]
        rw [map_mul]
      have hq_yi' : q yE = q iE := by
        simpa [hqcf_one] using hq_yi
      exact hq_yi'.symm.trans hq_yx
    have hi_eq_x : iE = xE := by
      have hdiffKE : iE * xE⁻¹ ∈ K.subgroupOf d.E := by
        apply Subgroup.mem_subgroupOf.mpr
        change i * x⁻¹ ∈ K
        exact K.mul_mem hiK (K.inv_mem hx)
      have hdiffCenter : iE * xE⁻¹ ∈ Subgroup.center d.E := by
        have hqdiff : q (iE * xE⁻¹) = 1 := by
          rw [map_mul, map_inv, hq_i_eq_x]
          simp
        exact (QuotientGroup.eq_one_iff
          (N := Subgroup.center d.E) (iE * xE⁻¹)).mp hqdiff
      have hdiffBot : iE * xE⁻¹ ∈ (⊥ : Subgroup d.E) := by
        rw [← hKcenter]
        exact ⟨hdiffKE, hdiffCenter⟩
      have hdiffOne : iE * xE⁻¹ = 1 := Subgroup.mem_bot.mp hdiffBot
      calc
        iE = (iE * xE⁻¹) * xE := by group
        _ = 1 * xE := by rw [hdiffOne]
        _ = xE := by simp
    have hiG : i = x := congrArg Subtype.val hi_eq_x
    have hcfCenter : cfE ∈ Subgroup.center d.E := by
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) cfE).mp hqcf_one
    have hcfComm : a * cfE = cfE * a := by
      apply Subtype.ext
      have haMap : (a : G) ∈
          (SE : Subgroup d.E).map d.E.subtype :=
        Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hcfB' : cf ∈ B := by
        rw [hB]
        exact hcfB
      have hcommG : (a : G) * cf = cf * (a : G) :=
        (Subgroup.mem_centralizer_iff.mp (hBcentSE hcfB'))
          (a : G) haMap
      exact hcommG
    have hrel : a * xE * a⁻¹ = cfE * xE := by
      apply Subtype.ext
      simpa [cfE, iE, xE, yE, hiG] using hyi
    have haPow : ∃ n : ℕ, orderOf a = 2 ^ n :=
      by
        rcases (IsPGroup.iff_orderOf.mp SE.isPGroup')
            (⟨a, ha⟩ : SE) with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        simpa using hn
    have hcf_one := central_twist_eq_one_of_odd_center
      hcfCenter d.center_odd hcfComm hrel haPow
    have hy_eq : yE = xE := by
      rw [show yE = a * xE * a⁻¹ by rfl, hrel, hcf_one]
      simp
    have : (a : G) * x * (a : G)⁻¹ = x :=
      congrArg Subtype.val hy_eq
    rw [this]
    exact hx
  intro a ha
  rcases Subgroup.mem_map.mp ha with ⟨aE, haSE, rfl⟩
  have hqaJoin : q aE ∈ T ⊔ Subgroup.zpowers (q s) := by
    have hqaP : q aE ∈
        (SE.mapSurjective (QuotientGroup.mk'_surjective
          (Subgroup.center d.E)) : Subgroup (d.E ⧸ Subgroup.center d.E)) := by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map.mpr ⟨aE, haSE, rfl⟩
    exact hPdecomp hqaP
  have hqsq : q s * q s = 1 := by
    have hss : s * s = 1 := by
      simpa [pow_two] using hsI.2
    calc
      q s * q s = q (s * s) := (map_mul q s s).symm
      _ = q 1 := by rw [hss]
      _ = 1 := map_one q
  have hforward : ∀ x : G, x ∈ K →
      (aE : G) * x * (aE : G)⁻¹ ∈ K := by
    rcases (mem_sup_zpowers_of_involution_inverts hqsnotT hqsq hTinv).mp hqaJoin with
      ⟨u, huT, hqa | hqa⟩
    · intro x hx
      exact hrot aE haSE (by rw [hqa]; exact huT) x hx
    · let b : d.E := aE * s
      have hbSE : b ∈ (SE : Subgroup d.E) := by
        exact SE.mul_mem haSE hsSE
      have hqbT : q b ∈ T := by
        have hqeq : q b = u := by
          calc
            q b = q aE * q s := by
              dsimp [b]
              rw [map_mul]
            _ = (u * q s) * q s := by rw [hqa]
            _ = u := by
              calc
                (u * q s) * q s = u * (q s * q s) := by group
                _ = u := by rw [hqsq]; simp
        rw [hqeq]
        exact huT
      have hzK : ∀ x : G, x ∈ K →
          (s : G) * x * (s : G)⁻¹ ∈ K := by
        intro x hx
        have hs_sq : sG * sG = 1 := by
          simpa [pow_two] using hsIG.2
        have hs_inv : sG⁻¹ = sG :=
          inv_eq_of_mul_eq_one_right hs_sq
        have hdouble :
            sG * (sG * x * sG⁻¹) * sG⁻¹ = x := by
          rw [hs_inv]
          calc
            sG * (sG * x * sG) * sG = (sG * sG) * x * (sG * sG) := by
              group
            _ = x := by rw [hs_sq]; simp
        have hinv_inv :
            sG * x⁻¹ * sG⁻¹ = x := by
          simpa [hKinv x⁻¹ (K.inv_mem hx)] using
            (show (x⁻¹)⁻¹ = x by simp)
        have hxI : sG * x * sG⁻¹ ∈ invertedElements X sG :=
          ⟨hsX x (hKleX hx), by
            calc
              sG * (sG * x * sG⁻¹) * sG⁻¹ = x := hdouble
              _ = sG * x⁻¹ * sG⁻¹ := hinv_inv.symm
              _ = (sG * x * sG⁻¹)⁻¹ := by group⟩
        have hxK : sG * x * sG⁻¹ ∈ (K : Set G) := by
          rw [hK_eq]
          exact hxI
        exact hxK
      intro x hx
      have hbx := hrot b hbSE hqbT
        ((s : G) * x * (s : G)⁻¹) (hzK x hx)
      have hbs : (b : G) * (s : G) = (aE : G) := by
        have hs_sq : (s : G) * (s : G) = 1 := by
          simpa [pow_two] using congrArg Subtype.val hsI.2
        calc
          (b : G) * (s : G) =
              ((aE : G) * (s : G)) * (s : G) := by rfl
          _ = (aE : G) * ((s : G) * (s : G)) := by group
          _ = (aE : G) := by rw [hs_sq]; simp
      have hconj :
          (aE : G) * x * (aE : G)⁻¹ =
            (b : G) * ((s : G) * x * (s : G)⁻¹) * (b : G)⁻¹ := by
        rw [← hbs]
        group
      rw [hconj]
      exact hbx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact hforward x hx
  · exact (Subgroup.card_map_of_injective (MulAut.conj (aE : G)).injective).ge

end CFSG.GorensteinWalter

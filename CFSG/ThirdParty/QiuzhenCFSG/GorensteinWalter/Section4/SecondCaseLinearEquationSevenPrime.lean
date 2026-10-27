module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingInvolutionDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostEquationFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingFixedPartCardDvd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentCentralizesOddCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvertedElementsInComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (7): the prime-support half for the `PSL₂` branch

This module formalizes the equation-(7) prime information of
`refs/bender-dihedral-sylow.tex` L696–705 — the "π = π(K₀)" half — in the
form needed by the `PSL₂` branch (equation (9), L793–795): the prime
divisors of the Fitting subgroup `F(M)` of the maximal subgroup are
controlled by those of `K₀ = F(U) ∩ K`, and `|F(M)|` is prime to
`q = |K|`.

The two control statements are proved PSL₂-independently from the
equations-(3)--(7) package:

* `secondCase_equationSevenPrime_oddPrimeFactors_fittingSubgroupOf_M_subset`:
  every odd prime divisor of `|F(M)|` divides `|F(U)|`.  The `r`-Sylow
  subgroup `R` of `F(M)` is characteristic in `F(M)`, hence normal in `M`;
  being odd it lies in `O₂′(M)`, which centralizes `t ∈ E` and therefore
  lies in `H = C_G(t)` and, being odd, in `U = O(H)`.  A `π′`-subgroup of
  `H` centralizing `K₀F = N_{F(U)}(F)` centralizes all of `F(U)` by the
  Fact 1.1(iv) transfer
  (`centralizes_of_subnormal_selfCentralizing_coprime`), and
  `U ∩ C_G(F(U)) ≤ F(U)` (Fact 1.2), so `R ≤ F(U)`.
* `secondCase_equationSevenPrime_primeFactors_FU_subset_K0`: every prime
  divisor of `|F(U)|` divides `|K₀|`.  An `r`-Sylow `R` of `F(U)` meeting
  `Y = K₀F = F(U) ∩ M` trivially centralizes `Y`: its elements are
  `r`-elements, the elements of `Y` are `r′`-elements (as `r ∤ |Y|`), and
  coprime elements of a nilpotent group commute
  (`commute_of_coprime_orderOf_of_nilpotent`).  The self-centralizing
  fact `C_{F(U)}(Y) ≤ Y` (from `N_G(F) = M`) then puts `R ≤ Y`, a
  contradiction.

The final theorem combines these controls with the quotient reflected torus:
`K₀` embeds injectively into the torus `T ≤ E/Z(E)` of order `(q ± 1)/2`,
so `|K₀|` is prime to `q`, and
`Nat.Coprime (Nat.card (fittingSubgroupOf w.M)) (Nat.card K)` follows.
This is the exact hypothesis consumed by
`secondCase_linearEquationNine_data` in `SecondCaseLinearEquationNine.lean`.
-/

noncomputable section

open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## Arithmetic: `q` is prime to the two halves `(q ± 1)/2` -/

/-- For odd `q`, the two halves `(q ± 1)/2` are prime to `q`. -/
private theorem coprime_card_field_half
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    Nat.Coprime (Nat.card K) ((Nat.card K + 1) / 2) ∧
      Nat.Coprime (Nat.card K) ((Nat.card K - 1) / 2) := by
  rcases hK with ⟨p, n, hp, hpOdd, hn, hcard⟩
  rw [hcard]
  constructor
  · apply Nat.coprime_of_dvd
    intro r hr hrdvd hrhalf
    have h2 : 2 ∣ p ^ n + 1 := by
      rcases hpOdd.pow with ⟨j, hj⟩
      refine ⟨j + 1, ?_⟩
      rw [hj]
      ring
    have hrdvdq1 : r ∣ p ^ n + 1 := by
      rcases hrhalf with ⟨k, hk⟩
      refine ⟨2 * k, ?_⟩
      calc
        p ^ n + 1 = (p ^ n + 1) / 2 * 2 := (Nat.div_mul_cancel h2).symm
        _ = (r * k) * 2 := by rw [hk]
        _ = r * (2 * k) := by ring
    have hrdvd1 : r ∣ 1 := by
      have hsub : r ∣ (p ^ n + 1) - p ^ n := Nat.dvd_sub hrdvdq1 hrdvd
      simpa using hsub
    exact hr.not_dvd_one hrdvd1
  · apply Nat.coprime_of_dvd
    intro r hr hrdvd hrhalf
    have h2 : 2 ∣ p ^ n - 1 := by
      rcases hpOdd.pow with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      rw [hj]
      omega
    have hrdvdq1 : r ∣ p ^ n - 1 := by
      rcases hrhalf with ⟨k, hk⟩
      refine ⟨2 * k, ?_⟩
      calc
        p ^ n - 1 = (p ^ n - 1) / 2 * 2 := (Nat.div_mul_cancel h2).symm
        _ = (r * k) * 2 := by rw [hk]
        _ = r * (2 * k) := by ring
    have hrdvd1 : r ∣ 1 := by
      have hsub : r ∣ p ^ n - (p ^ n - 1) := Nat.dvd_sub hrdvd hrdvdq1
      have h' : p ^ n - (p ^ n - 1) = 1 := by
        exact Nat.sub_sub_self (Nat.succ_le_of_lt (pow_pos hp.pos n))
      simpa [h'] using hsub
    exact hr.not_dvd_one hrdvd1

/-! ## Nilpotent coprime elements commute -/

/-- In a nilpotent group, elements of coprime order commute. -/
private theorem commute_of_coprime_orderOf_of_nilpotent
    {G : Type*} [Group G] [Group.IsNilpotent G]
    {x y : G} (hcop : Nat.Coprime (orderOf x) (orderOf y)) :
    x * y = y * x := by
  classical
  revert x y
  apply @nilpotent_center_quotient_ind _ G _ _ <;> clear! G
  · intro H _ _ x y hcop
    exact Subsingleton.elim _ _
  · intro H _ _ ih x y hcop
    let q : H →* H ⧸ Subgroup.center H := QuotientGroup.mk' (Subgroup.center H)
    have hqord : ∀ z : H, orderOf (q z) ∣ orderOf z := by
      intro z
      exact orderOf_dvd_of_pow_eq_one (by
        calc
          (q z) ^ orderOf z = q (z ^ orderOf z) := (map_pow q z (orderOf z)).symm
          _ = q 1 := by rw [pow_orderOf_eq_one z]
          _ = 1 := map_one q)
    have hcopQ : Nat.Coprime (orderOf (q x)) (orderOf (q y)) := by
      exact (hcop.coprime_dvd_left (hqord x)).coprime_dvd_right (hqord y)
    have hcommQ : q x * q y = q y * q x := ih (x := q x) (y := q y) hcopQ
    have hcommQ' : q (x * y) = q (y * x) := by
      simpa [q, map_mul] using hcommQ
    have hdiv : (x * y) / (y * x) ∈ Subgroup.center H :=
      (QuotientGroup.eq_iff_div_mem (N := Subgroup.center H)).mp hcommQ'
    have hcZ : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center H := by
      have hxy : x * y * x⁻¹ * y⁻¹ = (x * y) / (y * x) := by
        simp [div_eq_mul_inv, mul_assoc]
      rwa [← hxy] at hdiv
    let c : H := x * y * x⁻¹ * y⁻¹
    have hc_comm : ∀ z : H, z * c = c * z := by
      intro z
      exact Subgroup.mem_center_iff.mp hcZ z
    have hc_pow_central : ∀ n : ℕ, c ^ n ∈ Subgroup.center H := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ']
          exact (Subgroup.center H).mul_mem hcZ ih
    have hc_pow_left : ∀ n : ℕ, c ^ n = ⁅x ^ n, y⁆ := by
      intro n
      induction n with
      | zero => simp [c, commutatorElement_def]
      | succ n ih =>
          have hcx : x * ⁅x ^ n, y⁆ * x⁻¹ = ⁅x ^ n, y⁆ := by
            rw [← ih]
            calc
              x * (c ^ n) * x⁻¹ = (c ^ n) * x * x⁻¹ := by
                rw [(Subgroup.mem_center_iff.mp (hc_pow_central n) x).symm]
              _ = c ^ n := by simp
          calc
            c ^ (n + 1) = c ^ n * c := by rw [pow_succ]
            _ = ⁅x ^ n, y⁆ * ⁅x, y⁆ := by
              rw [ih]
              rfl
            _ = x * ⁅x ^ n, y⁆ * x⁻¹ * ⁅x, y⁆ := by rw [hcx]
            _ = ⁅x ^ (n + 1), y⁆ := by
              have hstep : ⁅x ^ (n + 1), y⁆ = x * ⁅x ^ n, y⁆ * x⁻¹ * ⁅x, y⁆ := by
                calc
                  ⁅x ^ (n + 1), y⁆ = ⁅x * x ^ n, y⁆ := by
                    congr 1
                    rw [pow_succ']
                  _ = x * ⁅x ^ n, y⁆ * x⁻¹ * ⁅x, y⁆ := commutator_mul_left x (x ^ n) y
              exact hstep.symm
    have hc_pow_right : ∀ n : ℕ, c ^ n = ⁅x, y ^ n⁆ := by
      intro n
      induction n with
      | zero => simp [c, commutatorElement_def]
      | succ n ih =>
          have hcy : y * ⁅x, y ^ n⁆ * y⁻¹ = ⁅x, y ^ n⁆ := by
            rw [← ih]
            calc
              y * (c ^ n) * y⁻¹ = (c ^ n) * y * y⁻¹ := by
                rw [(Subgroup.mem_center_iff.mp (hc_pow_central n) y).symm]
              _ = c ^ n := by simp
          calc
            c ^ (n + 1) = c ^ n * c := by rw [pow_succ]
            _ = ⁅x, y ^ n⁆ * ⁅x, y⁆ := by
              rw [ih]
              rfl
            _ = y * ⁅x, y ^ n⁆ * y⁻¹ * ⁅x, y⁆ := by rw [hcy]
            _ = ⁅x, y ^ (n + 1)⁆ := by
              have hstep : ⁅x, y ^ (n + 1)⁆ = y * ⁅x, y ^ n⁆ * y⁻¹ * ⁅x, y⁆ := by
                calc
                  ⁅x, y ^ (n + 1)⁆ = ⁅x, y * y ^ n⁆ := by
                    congr 1
                    rw [pow_succ']
                  _ = ⁅x, y⁆ * y * ⁅x, y ^ n⁆ * y⁻¹ := commutator_mul_right x y (y ^ n)
                  _ = y * ⁅x, y ^ n⁆ * y⁻¹ * ⁅x, y⁆ := by
                    have hcomm : y * ⁅x, y ^ n⁆ * y⁻¹ * ⁅x, y⁆ =
                        ⁅x, y⁆ * (y * ⁅x, y ^ n⁆ * y⁻¹) := by
                      exact hc_comm (y * ⁅x, y ^ n⁆ * y⁻¹)
                    calc
                      ⁅x, y⁆ * y * ⁅x, y ^ n⁆ * y⁻¹ = ⁅x, y⁆ * (y * ⁅x, y ^ n⁆ * y⁻¹) := by group
                      _ = y * ⁅x, y ^ n⁆ * y⁻¹ * ⁅x, y⁆ := hcomm.symm
              exact hstep.symm
    have hordx : orderOf c ∣ orderOf x := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hc_pow_left (orderOf x)]
      simp [pow_orderOf_eq_one]
    have hordy : orderOf c ∣ orderOf y := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hc_pow_right (orderOf y)]
      simp [pow_orderOf_eq_one]
    have hc1 : c = 1 := by
      have hdvd : orderOf c ∣ 1 := by
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd hordx hordy
      have hord1 : orderOf c = 1 := Nat.dvd_one.mp hdvd
      calc
        c = c ^ 1 := by simp
        _ = c ^ orderOf c := by rw [hord1]
        _ = 1 := pow_orderOf_eq_one c
    have hc1' : x * y * x⁻¹ * y⁻¹ = 1 := by
      simpa [c] using hc1
    calc
      x * y = x * y * (x⁻¹ * y⁻¹ * (y * x)) := by group
      _ = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = 1 * (y * x) := by rw [hc1']
      _ = y * x := by simp

/-! ## The self-centralizing equation-(6) intersection -/

/-- `C_{F(U)}(Y) ≤ Y` for `Y = K₀F = F(U) ∩ M`: an element of `F(U)`
centralizing `Y` centralizes `F ≤ Y`, hence lies in `N_G(F) = M`. -/
private theorem eq7prime_FU_centralizer_Y_le_Y
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (F : Subgroup G) (hFleY : F ≤ fittingSubgroupOf c.U ⊓ w.M)
    (hNFeq : Subgroup.normalizer (F : Set G) = w.M) :
    fittingSubgroupOf c.U ⊓ Subgroup.centralizer
      ((fittingSubgroupOf c.U ⊓ w.M : Subgroup G) : Set G) ≤
        fittingSubgroupOf c.U ⊓ w.M := by
  intro x hx
  have hxCentF : x ∈ Subgroup.centralizer (F : Set G) :=
    (Subgroup.centralizer_le (SetLike.coe_mono hFleY)) hx.2
  have hxN : x ∈ Subgroup.normalizer (F : Set G) :=
    Subgroup.centralizer_le_normalizer (F : Set G) hxCentF
  have hxM : x ∈ w.M := hNFeq ▸ hxN
  exact Subgroup.mem_inf.mpr ⟨hx.1, hxM⟩

/-- Coprimality of an `r`-group with an `r′`-group, `r` prime. -/
private theorem coprime_card_of_not_dvd_pow
    {r n m : ℕ} (hr : r.Prime) (h : ¬ r ∣ m) :
    Nat.Coprime (r ^ n) m := by
  apply Nat.coprime_of_dvd
  intro p hp hpdvd hpdvdn
  have hpr : p = r := by
    have hpdvdr : p ∣ r := hp.dvd_of_dvd_pow hpdvd
    exact (Nat.prime_dvd_prime_iff_eq hp hr).mp hpdvdr
  rw [hpr] at hpdvdn
  exact h hpdvdn

/-! ## Equation (7): prime divisors of `F(U)` are prime divisors of `K₀` -/

/-- Equation (7), `π(F(U)) ⊆ π(K₀)`: every prime divisor of `|F(U)|`
divides `|K₀|`.  An `r`-Sylow subgroup `R` of `F(U)` meeting
`Y = K₀F = F(U) ∩ M` trivially centralizes `Y` — `R` consists of
`r`-elements, `Y` consists of `r′`-elements, and coprime elements of the
nilpotent group `F(U)` commute — and `C_{F(U)}(Y) ≤ Y` (from
`N_G(F) = M`) then forces `R ≤ Y`, a contradiction. -/
public theorem secondCase_equationSevenPrime_primeFactors_FU_subset_K0
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (Kinv K0 F : Subgroup G) (s : d.E)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hKinv_cyclic : IsCyclic Kinv)
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ Nat.card (fittingSubgroupOf c.U)) :
    r ∣ Nat.card K0 := by
  classical
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
  have hK0leKinv : K0 ≤ Kinv := by
    rw [hK0_def]
    exact inf_le_right
  obtain ⟨_hFnormalM, hFnormalY, _hFne, hNFeq, hTI, _hFcyc, _hFcardle,
      _hK0ne, _hO2⟩ :=
    secondCase_fitting_equation5_7_of_component_centralization
      hmin c w d Kinv K0 F s hKinv_cyclic hK0leKinv hF_eq hjoin hFcentE hLayer
  have hK0leY : K0 ≤ Y := by
    intro x hx
    change x ∈ fittingSubgroupOf c.U ⊓ w.M
    rw [← hjoin]
    exact (le_sup_left : K0 ≤ K0 ⊔ F) hx
  have hFleY : F ≤ Y := by
    intro f hf
    change f ∈ fittingSubgroupOf c.U ⊓ w.M
    rw [← hjoin]
    exact (le_sup_right : F ≤ K0 ⊔ F) hf
  -- |F| | |K0| (equation (6), divisibility form)
  have hFcarddvd : Nat.card F ∣ Nat.card K0 := by
    obtain ⟨g, hgY, hgnotM⟩ := secondCase_exists_conjugator_not_mem_M hmin c w
    have hdisj : F ⊓ conjugateSubgroup F g = ⊥ := hTI g hgnotM
    exact secondCase_fitting_fixed_part_card_dvd_of_conjugate_disjoint
      K0 F Y hFnormalY (by simpa [Y, CentralizerSetup.FU] using hjoin) g
        (by simpa [Y, CentralizerSetup.FU] using hgY) hdisj
  by_contra hrn
  have hrnY : ¬ r ∣ Nat.card Y := by
    intro hrY
    -- |Y| = |F| * |Y/F| with |Y/F| | |K0|, so r | |Y| ⇒ r | |K0|
    let FY : Subgroup Y := F.subgroupOf Y
    have hFYnormal : FY.Normal := by
      rw [Subgroup.normal_subgroupOf_iff hFleY]
      intro f y hf hy
      exact hFnormalY.2 y hy f hf
    let : FY.Normal := hFYnormal
    let q : Y →* Y ⧸ FY := QuotientGroup.mk' FY
    let K0Y : Subgroup Y := K0.subgroupOf Y
    have hK0Ytop : K0Y ⊔ FY = ⊤ := by
      have hsub : (K0 ⊔ F).subgroupOf Y = ⊤ := by
        rw [hjoin]
        exact Subgroup.subgroupOf_self Y
      simpa [K0Y, FY, Subgroup.subgroupOf_sup hK0leY hFleY] using hsub
    have hq_surj : Function.Surjective (q.comp K0Y.subtype) := by
      intro z
      rcases QuotientGroup.mk'_surjective FY z with ⟨y, rfl⟩
      have hyTop : y ∈ K0Y ⊔ FY := by
        rw [hK0Ytop]
        trivial
      rcases (@Subgroup.mem_sup_of_normal_right Y _ K0Y FY hFYnormal y).mp hyTop
        with ⟨k, hk, f, hf, hy⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      change q (K0Y.subtype ⟨k, hk⟩) = q y
      rw [← hy]
      rw [map_mul]
      have hqf : q f = 1 :=
        (QuotientGroup.eq_one_iff (N := FY) f).2 hf
      rw [hqf]
      simp
    have hQK0 : Nat.card (Y ⧸ FY) ∣ Nat.card K0Y :=
      Subgroup.card_dvd_of_surjective hq_surj
    have hK0Ycard : Nat.card K0Y = Nat.card K0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0leY).toEquiv
    have hYeq : Nat.card Y = Nat.card F * Nat.card (Y ⧸ FY) := by
      have hFYcard : Nat.card FY = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleY).toEquiv
      have hindex : FY.index = Nat.card (Y ⧸ FY) := by
        simpa using (Subgroup.index_eq_card (H := FY))
      calc
        Nat.card Y = Nat.card FY * FY.index := by
          rw [Subgroup.card_mul_index]
        _ = Nat.card F * Nat.card (Y ⧸ FY) := by rw [hFYcard, hindex]
    have hYdvd : Nat.card Y ∣ Nat.card F * Nat.card K0 := by
      rw [hYeq]
      exact Nat.mul_dvd_mul_left (Nat.card F) (by simpa [hK0Ycard] using hQK0)
    have hrdvdFK : r ∣ Nat.card F * Nat.card K0 := hrY.trans hYdvd
    rcases (hr.dvd_mul.mp hrdvdFK) with hF | hK0
    · exact hrn (hF.trans hFcarddvd)
    · exact hrn hK0
  -- the r-Sylow of F(U) and its image
  let : Fact r.Prime := ⟨hr⟩
  let R : Sylow r (↥c.FU) := Classical.choice Sylow.nonempty
  let RG : Subgroup G := (R : Subgroup (↥c.FU)).map c.FU.subtype
  have hRGleFU : RG ≤ c.FU := Subgroup.map_subtype_le (R : Subgroup (↥c.FU))
  have hRGcard : Nat.card RG = Nat.card (R : Subgroup (↥c.FU)) :=
    Subgroup.card_map_of_injective (K := (R : Subgroup (↥c.FU)))
      (f := c.FU.subtype) c.FU.subtype_injective
  have hRne : (R : Subgroup (↥c.FU)) ≠ ⊥ :=
    R.ne_bot_of_dvd_card (by simpa [CentralizerSetup.FU] using hrdvd)
  have hRGne : RG ≠ ⊥ := by
    intro hbot
    exact hRne ((Subgroup.map_eq_bot_iff_of_injective
      (H := (R : Subgroup (↥c.FU))) (f := c.FU.subtype)
      (hf := c.FU.subtype_injective)).mp hbot)
  -- R meets Y trivially
  have hcopRY : Nat.Coprime (Nat.card RG) (Nat.card Y) := by
    rcases R.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hcop : Nat.Coprime (r ^ n) (Nat.card Y) :=
      coprime_card_of_not_dvd_pow (n := n) hr hrnY
    rwa [← hn, ← hRGcard] at hcop
  have hRGYinf : RG ⊓ Y = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcopRY).eq_bot
  -- elements of Y are r'-elements
  have hYr' : ∀ y : G, y ∈ Y → ¬ r ∣ orderOf y := by
    intro y hy hrOrd
    exact hrnY (hrOrd.trans (Subgroup.orderOf_dvd_natCard Y hy))
  -- R centralizes Y: r-elements commute with r'-elements in the nilpotent F(U)
  have hYleFU : Y ≤ c.FU := inf_le_left
  have hRGY : RG ≤ Subgroup.centralizer (Y : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hx with ⟨xFU, hxR, rfl⟩
    have hyFU : y ∈ c.FU := hYleFU hy
    let yFU : c.FU := ⟨y, hyFU⟩
    have hordx : orderOf xFU ∣ Nat.card (R : Subgroup (↥c.FU)) :=
      Subgroup.orderOf_dvd_natCard (R : Subgroup (↥c.FU)) hxR
    have hcop : Nat.Coprime (orderOf xFU) (orderOf yFU) := by
      apply Nat.coprime_of_dvd
      intro p hp hpdvdx hpdvdy
      have hpr : p = r := by
        rcases R.isPGroup'.exists_card_eq with ⟨n, hn⟩
        have hpdvdr : p ∣ r := hp.dvd_of_dvd_pow (by
          rw [← hn]
          exact hpdvdx.trans hordx)
        exact (Nat.prime_dvd_prime_iff_eq hp hr).mp hpdvdr
      rw [hpr] at hpdvdy
      have hordy : orderOf yFU = orderOf y :=
        (orderOf_injective c.FU.subtype c.FU.subtype_injective yFU).symm
      rw [hordy] at hpdvdy
      exact hYr' y hy hpdvdy
    have hxy : xFU * yFU = yFU * xFU := by
      let : Group.IsNilpotent (↥c.FU) := fittingSubgroupOf_isNilpotent c.U
      exact commute_of_coprime_orderOf_of_nilpotent hcop
    exact (congrArg Subtype.val hxy).symm
  -- C_{F(U)}(Y) ≤ Y, hence R ≤ Y — contradiction
  have hYleFU : Y ≤ c.FU := inf_le_left
  have hYself : c.FU ⊓ Subgroup.centralizer (Y : Set G) ≤ Y :=
    eq7prime_FU_centralizer_Y_le_Y c w F hFleY hNFeq
  have hRGleY : RG ≤ Y := by
    intro x hx
    exact hYself ⟨hRGleFU hx, hRGY hx⟩
  have hRGbot : RG = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxY : x ∈ Y := hRGleY hx
    have hxinf : x ∈ RG ⊓ Y := ⟨hx, hxY⟩
    rwa [hRGYinf] at hxinf
  exact hRGne hRGbot

/-! ## Equation (7): odd prime divisors of `F(M)` divide `F(U)` -/

/-- Equation (7), `π(F(M)) ⊆ π(F(U))` for odd primes: every odd prime
divisor of `|F(M)|` divides `|F(U)|`.  The `r`-Sylow subgroup `R` of
`F(M)` is characteristic in `F(M)`, hence normal in `M`; being odd it lies
in `O₂′(M)`, which centralizes `t ∈ E` and therefore lies in
`H = C_G(t)` and, being odd, in `U = O(H)`.  Since `r ∤ |F(U)|`, `R` is a
`π′`-subgroup of `H` centralizing `Y = K₀F = N_{F(U)}(F)` (coprime normal
subgroups of `H ∩ M`), and the Fact 1.1(iv) transfer
(`centralizes_of_subnormal_selfCentralizing_coprime`) puts `R ≤ C_G(F(U))`;
with `U ∩ C_G(F(U)) ≤ F(U)` (Fact 1.2), `R ≤ F(U)`, contradicting
`r ∤ |F(U)|`. -/
public theorem secondCase_equationSevenPrime_oddPrimeFactors_fittingSubgroupOf_M_subset
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (Kinv K0 F : Subgroup G) (s : d.E)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hKinv_cyclic : IsCyclic Kinv)
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E)
    {r : ℕ} (hr : r.Prime) (hrodd : Odd r)
    (hrdvd : r ∣ Nat.card (fittingSubgroupOf w.M)) :
    r ∣ Nat.card (fittingSubgroupOf c.U) := by
  classical
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
  let FM : Subgroup G := fittingSubgroupOf w.M
  have hK0leKinv : K0 ≤ Kinv := by
    rw [hK0_def]
    exact inf_le_right
  obtain ⟨_hFnormalM, hFnormalY, _hFne, hNFeq, _hTI, _hFcyc, _hFcardle,
      _hK0ne, _hO2⟩ :=
    secondCase_fitting_equation5_7_of_component_centralization
      hmin c w d Kinv K0 F s hKinv_cyclic hK0leKinv hF_eq hjoin hFcentE hLayer
  by_contra hrnFU
  -- the r-Sylow of F(M), its image, and its normality in M
  let : Fact r.Prime := ⟨hr⟩
  let R : Sylow r (↥FM) := Classical.choice Sylow.nonempty
  let RG : Subgroup G := (R : Subgroup (↥FM)).map FM.subtype
  have hRGleFM : RG ≤ FM := Subgroup.map_subtype_le (R : Subgroup (↥FM))
  have hRGcard : Nat.card RG = Nat.card (R : Subgroup (↥FM)) :=
    Subgroup.card_map_of_injective (K := (R : Subgroup (↥FM)))
      (f := FM.subtype) FM.subtype_injective
  have hRne : (R : Subgroup (↥FM)) ≠ ⊥ :=
    R.ne_bot_of_dvd_card (by simpa [FM] using hrdvd)
  have hRGne : RG ≠ ⊥ := by
    intro hbot
    exact hRne ((Subgroup.map_eq_bot_iff_of_injective
      (H := (R : Subgroup (↥FM))) (f := FM.subtype)
      (hf := FM.subtype_injective)).mp hbot)
  have hRnorm : (R : Subgroup (↥FM)).Normal :=
    Group.IsNilpotent.sylow_normal (fittingSubgroupOf_isNilpotent w.M) r R
  have hRchar : (R : Subgroup (↥FM)).Characteristic :=
    Sylow.characteristic_of_normal (p := r) R hRnorm
  have hFMnormalM : IsNormalIn FM w.M := fittingSubgroupOf_isNormalIn w.M
  have hRGnormalM : IsNormalIn RG w.M :=
    map_characteristic_isNormalIn_of_isNormalIn (G := G) (H := FM) (N := w.M)
      (R : Subgroup (↥FM)) hRchar hFMnormalM
  have hRGleM : RG ≤ w.M := hRGleFM.trans (Subgroup.map_subtype_le (fittingSubgroup w.M))
  -- R is odd, hence lies in O₂′(M), which lies in H = C_G(t)
  have hRGodd : Odd (Nat.card RG) := by
    rcases R.isPGroup'.exists_card_eq with ⟨n, hn⟩
    rw [hRGcard, hn]
    exact hrodd.pow
  have hRGleOdd : RG ≤ oddCoreOf w.M :=
    le_oddCoreOf_of_normal_of_coprime w.M RG hRGleM hRGnormalM
      (Nat.coprime_two_left.mpr hRGodd)
  have hOddleH : oddCoreOf w.M ≤ c.H := by
    intro o ho
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hEcent : d.E ≤ Subgroup.centralizer (oddCoreOf w.M : Set G) :=
      secondCase_component_centralizes_oddCore c w d
    have htcent : (c.t : G) ∈ Subgroup.centralizer (oddCoreOf w.M : Set G) :=
      hEcent d.t_mem_E
    exact (Subgroup.mem_centralizer_iff.mp htcent) o ho
  have hRGleH : RG ≤ c.H := hRGleOdd.trans hOddleH
  have hRGleU : RG ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hRGleH
      (Nat.coprime_two_left.mpr hRGodd)
  -- R centralizes Y = K₀F (coprime normal subgroups of H ∩ M)
  let C : Subgroup G := c.H ⊓ w.M
  have hYleC : Y ≤ C := by
    intro y hy
    exact ⟨(centralizerSetup_FU_isNormalIn_H c).1 hy.1, hy.2⟩
  have hFUnormalH : IsNormalIn c.FU c.H := centralizerSetup_FU_isNormalIn_H c
  have hYnormalC : IsNormalIn Y C := by
    refine ⟨hYleC, ?_⟩
    intro z hz y hy
    exact ⟨hFUnormalH.2 z hz.1 y hy.1,
      w.M.mul_mem (w.M.mul_mem hz.2 hy.2) (w.M.inv_mem hz.2)⟩
  have hRGleC : RG ≤ C := fun x hx => ⟨hRGleH hx, hRGleM hx⟩
  have hRGnormalC : IsNormalIn RG C := by
    refine ⟨hRGleC, ?_⟩
    intro z hz x hx
    exact hRGnormalM.2 z hz.2 x hx
  have hrnY : ¬ r ∣ Nat.card Y := by
    intro hrY
    exact hrnFU (hrY.trans (Subgroup.card_dvd_of_le (inf_le_left : Y ≤ c.FU)))
  have hcopRY : Nat.Coprime (Nat.card RG) (Nat.card Y) := by
    rcases R.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hcop : Nat.Coprime (r ^ n) (Nat.card Y) :=
      coprime_card_of_not_dvd_pow (n := n) hr hrnY
    rwa [← hn, ← hRGcard] at hcop
  let PC : Subgroup C := RG.subgroupOf C
  let YC : Subgroup C := Y.subgroupOf C
  have hPCnormal : PC.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRGleC]
    intro x z hx hz
    exact hRGnormalC.2 z hz x hx
  have hYCnormal : YC.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hYleC]
    intro y z hy hz
    exact hYnormalC.2 z hz y hy
  let : PC.Normal := hPCnormal
  let : YC.Normal := hYCnormal
  have hPCcard : Nat.card PC = Nat.card RG :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRGleC).toEquiv
  have hYCcard : Nat.card YC = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleC).toEquiv
  have hPCYCcop : Nat.Coprime (Nat.card PC) (Nat.card YC) := by
    simpa [hPCcard, hYCcard] using hcopRY
  have hPCYCdisj : Disjoint PC YC := Subgroup.disjoint_of_coprime_natCard hPCYCcop
  have hcommbot : ⁅PC, YC⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_le_inf PC YC).trans (by rw [hPCYCdisj.eq_bot])
  have hRGY : RG ≤ Subgroup.centralizer (Y : Set G) := by
    have hPCcentYC : PC ≤ Subgroup.centralizer (YC : Set C) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommbot
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let xC : C := ⟨x, hRGleC hx⟩
    let yC : C := ⟨y, hYleC hy⟩
    have hxPC : xC ∈ PC := Subgroup.mem_subgroupOf.mpr hx
    have hyYC : yC ∈ YC := Subgroup.mem_subgroupOf.mpr hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hPCcentYC hxPC)) yC hyYC
    exact congrArg Subtype.val hcomm
  -- the Fact 1.1(iv) transfer: R centralizes F(U)
  have hYleFU : Y ≤ c.FU := inf_le_left
  have hYsub : (Y.subgroupOf c.FU).IsSubnormal :=
    isSubnormal_of_nilpotent (fittingSubgroupOf_isNilpotent c.U) Y hYleFU
  have hFleY : F ≤ Y := by
    intro f hf
    change f ∈ fittingSubgroupOf c.U ⊓ w.M
    rw [← hjoin]
    exact (le_sup_right : F ≤ K0 ⊔ F) hf
  have hYself : c.FU ⊓ Subgroup.centralizer (Y : Set G) ≤ Y :=
    eq7prime_FU_centralizer_Y_le_Y c w F hFleY hNFeq
  have hcop : Nat.Coprime (Nat.card RG) (Nat.card c.FU) := by
    rcases R.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hcop' : Nat.Coprime (r ^ n) (Nat.card c.FU) :=
      coprime_card_of_not_dvd_pow (n := n) hr (by
        intro hrFU
        exact hrnFU (hrFU.trans (Subgroup.card_dvd_of_le
          (le_rfl : c.FU ≤ fittingSubgroupOf c.U))))
    rwa [← hn, ← hRGcard] at hcop'
  have hRGcentFU : RG ≤ Subgroup.centralizer (c.FU : Set G) := by
    let : Group.IsNilpotent (↥c.FU) := fittingSubgroupOf_isNilpotent c.U
    exact centralizes_of_subnormal_selfCentralizing_coprime
      RG c.FU Y (hRGleU.trans (le_normalizer_of_isNormalIn
        (fittingSubgroupOf_isNormalIn c.U)))
      hYleFU hYsub hRGY hYself hcop (inferInstance : Group.IsSolvable c.FU)
  -- R ≤ U ∩ C_G(F(U)) ≤ F(U) — contradiction
  have hUsolv : Group.IsSolvable c.U := odd_order_theorem c.U (by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H)
  have hFUself : c.U ⊓ Subgroup.centralizer (c.FU : Set G) ≤ c.FU :=
    fact_1_2_centralizer_fitting_le_fitting c.U hUsolv
  have hRGleFU : RG ≤ c.FU := by
    intro x hx
    exact hFUself ⟨hRGleU hx, hRGcentFU hx⟩
  have hrdvdFU : r ∣ Nat.card c.FU := by
    have hrdvdR : r ∣ Nat.card (R : Subgroup (↥FM)) := by
      have hfact : (Nat.card (↥FM)).factorization r ≠ 0 :=
        (hr.factorization_pos_of_dvd Nat.card_pos.ne' (by simpa [FM] using hrdvd)).ne'
      rw [R.card_eq_multiplicity]
      exact dvd_pow_self r hfact
    have hRGdvdFU : Nat.card RG ∣ Nat.card c.FU :=
      Subgroup.card_dvd_of_le hRGleFU
    exact hrdvdR.trans (by simpa [hRGcard] using hRGdvdFU)
  exact hrnFU hrdvdFU

/-! ## The quotient torus: `|K₀|` divides `|T|` -/

/-- The equation-(3) subgroup `K₀ = F(U) ∩ K` has trivial intersection with
the odd center of the component: `s` inverts every element of `K₀` while it
fixes the center pointwise, so an element of the intersection has order two
and odd order, hence is trivial. -/
private theorem eq7prime_K0_intersection_center_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv) :
    K0 ⊓ (Subgroup.center d.E).map d.E.subtype = ⊥ := by
  classical
  let Z : Subgroup G := (Subgroup.center d.E).map d.E.subtype
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_bot]
  have hxK0 : x ∈ K0 := hx.1
  rcases Subgroup.mem_map.mp hx.2 with ⟨e, he, hxeq⟩
  have hxKinv : x ∈ Kinv := by
    rw [hK0_def] at hxK0
    exact hxK0.2
  have hxinv : s * x * (s : G)⁻¹ = x⁻¹ := by
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hKinv_carrier]
      exact hxKinv
    rw [invertedElements] at hxI
    exact hxI.2
  have hxfix : s * x * (s : G)⁻¹ = x := by
    rw [← hxeq]
    have hecomm : s * e = e * s := (Subgroup.mem_center_iff.mp he) s
    have hcommG : (s : G) * (e : G) = (e : G) * (s : G) :=
      congrArg Subtype.val hecomm
    rw [mul_inv_eq_iff_eq_mul]
    exact hcommG
  have hxx : x * x = 1 := by
    have hxeqinv : x = x⁻¹ := hxfix.symm.trans hxinv
    calc
      x * x = x * x⁻¹ := congrArg (fun z : G => x * z) hxeqinv
      _ = 1 := by simp
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hleU : K0 ≤ c.U := by
    intro a ha
    rw [hK0_def] at ha
    exact fittingSubgroupOf_le c.U ha.1
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat hUodd ((Subgroup.orderOf_dvd_natCard K0 hxK0).trans
      (Subgroup.card_dvd_of_le hleU))
  have hx1 : x = 1 := by
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hxx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      exact (Odd.not_two_dvd_nat hxodd) (by simpa [h2'])
  exact hx1

/-- The quotient map `E → E/Z(E)` is injective on `K₀`. -/
private theorem eq7prime_quotient_injective_on_K0
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hK0leE : K0 ≤ d.E) :
    Function.Injective
      (fun x : K0 => QuotientGroup.mk' (Subgroup.center d.E)
        (⟨(x : G), hK0leE x.2⟩ : d.E)) := by
  classical
  have hbot := eq7prime_K0_intersection_center_eq_bot c w d s Kinv K0
    hKinv_carrier hK0_def
  intro x y hq
  have hdiv : (⟨(x : G), hK0leE x.2⟩ : d.E) / (⟨(y : G), hK0leE y.2⟩ : d.E) ∈
      Subgroup.center d.E :=
    (QuotientGroup.eq_iff_div_mem (N := Subgroup.center d.E)).mp hq
  have hxyK0 : (x : G) / (y : G) ∈ K0 := K0.div_mem x.2 y.2
  have hxyE : (x : G) / (y : G) ∈ d.E := hK0leE hxyK0
  have hz : (⟨(x : G) / (y : G), hxyE⟩ : d.E) ∈ Subgroup.center d.E := by
    convert hdiv using 1
    all_goals
      ext
      simp [div_eq_mul_inv]
  have hxyZ : (x : G) / (y : G) ∈
      (Subgroup.center d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨⟨(x : G) / (y : G), hxyE⟩, hz, rfl⟩
  have hxybot : (x : G) / (y : G) ∈
      K0 ⊓ (Subgroup.center d.E).map d.E.subtype := ⟨hxyK0, hxyZ⟩
  have hxy1 : (x : G) / (y : G) = 1 := by
    rw [hbot] at hxybot
    exact Subgroup.mem_bot.mp hxybot
  apply Subtype.ext
  exact div_eq_one.mp hxy1

/-- The quotient image of `K₀` lies in the reflected torus `T`: `K₀` is
cyclic of odd order and lies in `U ⊆ C_G(t)`, so its image is an odd cyclic
subgroup of `E/Z(E)` centralized by the image of `t`, hence contained in `T`
by the torus-maximality clause. -/
private theorem eq7prime_K0_image_le_torus
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hK0leE : K0 ≤ d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hTcontain : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
            Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T) :
    (K0.subgroupOf d.E).map (QuotientGroup.mk' (Subgroup.center d.E)) ≤ T := by
  classical
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  apply hTcontain
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyK0 : (y : G) ∈ K0 := Subgroup.mem_subgroupOf.mp hy
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    have hleU : K0 ≤ c.U := by
      intro a ha
      rw [hK0_def] at ha
      exact fittingSubgroupOf_le c.U ha.1
    have hK0odd : Odd (Nat.card K0) :=
      Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hleU)
    have hdvd : orderOf (y : G) ∣ Nat.card K0 :=
      Subgroup.orderOf_dvd_natCard K0 hyK0
    have hoddY : Odd (orderOf y) := by
      simpa [Subgroup.orderOf_coe] using Odd.of_dvd_nat hK0odd hdvd
    have hqdvd : orderOf (q y) ∣ orderOf y := by
      exact orderOf_dvd_of_pow_eq_one (by
        calc
          (q y) ^ orderOf y = q (y ^ orderOf y) := (map_pow q y (orderOf y)).symm
          _ = q 1 := by rw [pow_orderOf_eq_one y]
          _ = 1 := map_one q)
    exact Odd.of_dvd_nat hoddY hqdvd
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyK0 : (y : G) ∈ K0 := Subgroup.mem_subgroupOf.mp hy
    have hyU : (y : G) ∈ c.U := by
      rw [hK0_def] at hyK0
      exact fittingSubgroupOf_le c.U hyK0.1
    have hyC : (y : G) ∈ c.H :=
      (Subgroup.map_subtype_le (pPrimeCore 2 c.H)) hyU
    have hyT : (y : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hyC
    have hcomm : (y : G) * c.t = c.t * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyT
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommE : y * (⟨c.t, d.t_mem_E⟩ : d.E) =
        (⟨c.t, d.t_mem_E⟩ : d.E) * y := Subtype.ext hcomm
    exact (map_mul q y (⟨c.t, d.t_mem_E⟩ : d.E)).symm.trans
      ((congrArg q hcommE).trans (map_mul q (⟨c.t, d.t_mem_E⟩ : d.E) y))

/-- `|K₀|` divides `|T|`: the quotient map embeds `K₀` into the reflected
torus `T`. -/
private theorem eq7prime_K0_card_dvd_T
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hK0leE : K0 ≤ d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hTcontain : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
            Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T) :
    Nat.card K0 ∣ Nat.card T := by
  classical
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  have hle := eq7prime_K0_image_le_torus c w d s Kinv K0 hKinv_carrier hK0_def hK0leE T hTcontain
  have hinj := eq7prime_quotient_injective_on_K0 c w d s Kinv K0 hKinv_carrier hK0_def hK0leE
  let f : K0 →* T :=
    { toFun := fun x => ⟨q (⟨(x : G), hK0leE x.2⟩ : d.E),
        hle (Subgroup.mem_map.mpr ⟨⟨(x : G), hK0leE x.2⟩,
          Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)⟩
      map_one' := by
        apply Subtype.ext
        change q (1 : d.E) = 1
        exact map_one q
      map_mul' := by
        intro x y
        apply Subtype.ext
        change q (⟨((x : G) * (y : G)), hK0leE (K0.mul_mem x.2 y.2)⟩ : d.E) =
          q (⟨(x : G), hK0leE x.2⟩ : d.E) * q (⟨(y : G), hK0leE y.2⟩ : d.E)
        exact (map_mul q (⟨(x : G), hK0leE x.2⟩ : d.E)
          (⟨(y : G), hK0leE y.2⟩ : d.E)).symm.trans (by
            rfl)
    }
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply hinj
    exact (congrArg Subtype.val hxy)
  exact Subgroup.card_dvd_of_injective f hfinj

/-! ## The equation-(7) prime-support theorem

Combining the two prime-support halves with the torus cardinality, the order
of the fitting subgroup of `M` is coprime to the field size `|K|`. -/

/-- **Equation (7), prime-support half.** If `p` is a prime dividing
`|F(M)|`, then `p` divides `|K₀|` (via (A') and (B)); since `K₀` embeds into
the reflected torus `T` of order `(|K| ± 1)/2`, `p` cannot divide `|K|` when
`|K|` is an odd prime power. Hence `|F(M)|` is coprime to `|K|`. -/
public theorem secondCase_equationSevenPrime_fittingSubgroupOf_M_coprime
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (s : d.E) (Kinv K0 F : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hKinv_cyclic : IsCyclic Kinv)
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hK0leE : K0 ≤ d.E)
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hTcard : Nat.card T = (Nat.card K - 1) / 2 ∨
      Nat.card T = (Nat.card K + 1) / 2)
    (hTcontain : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
            Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T) :
    Nat.Coprime (Nat.card (fittingSubgroupOf w.M)) (Nat.card K) := by
  classical
  have hK0leK : K0 ≤ Kinv := by
    intro x hx
    rw [hK0_def] at hx
    exact hx.2
  have hK0leU : K0 ≤ c.U := by
    intro x hx
    rw [hK0_def] at hx
    exact (fittingSubgroupOf_le c.U) hx.1
  -- (5)-(7) package; only the normalizer and the non-triviality are needed
  obtain ⟨_hFnormalM, _hFnormalY, hFne, hNFeq, _hTI, _hFcyc, _hFleK0,
      _hK0ne, _h2core⟩ :=
    secondCase_fitting_equation5_7_of_component_centralization
      hmin c w d Kinv K0 F s hKinv_cyclic hK0leK hF_eq hjoin hFcentE hLayer
  -- `|K₀|` divides `|T|`, which is coprime to `|K|`
  have hK0dvdT : Nat.card K0 ∣ Nat.card T :=
    eq7prime_K0_card_dvd_T c w d s Kinv K0 hKinv_carrier hK0_def hK0leE T hTcontain
  have hcopK0q : Nat.Coprime (Nat.card K0) (Nat.card K) := by
    rcases hTcard with hTcard1 | hTcard2
    · have hcopqT : Nat.Coprime (Nat.card K) (Nat.card T) := by
        rw [hTcard1]
        exact (coprime_card_field_half hK).2
      exact hcopqT.symm.coprime_dvd_left hK0dvdT
    · have hcopqT : Nat.Coprime (Nat.card K) (Nat.card T) := by
        rw [hTcard2]
        exact (coprime_card_field_half hK).1
      exact hcopqT.symm.coprime_dvd_left hK0dvdT
  -- prime-by-prime: a prime dividing both orders is odd and divides `|K₀|`
  apply Nat.coprime_of_dvd
  intro p hp hpdvd hpdvdK
  have hpOdd : Odd p := by
    rcases hK with ⟨p0, n, hp0, hp0Odd, hn, hcard⟩
    have hpdvdq : p ∣ p0 ^ n := by
      simpa [hcard] using hpdvdK
    have hpeq : p = p0 := (Nat.prime_dvd_prime_iff_eq hp hp0).mp
      (hp.dvd_of_dvd_pow hpdvdq)
    exact hpeq ▸ hp0Odd
  -- (A'): odd prime divisor of `|F(M)|` divides `|F(U)|`
  have hpdvdA : p ∣ Nat.card (fittingSubgroupOf c.U) :=
    secondCase_equationSevenPrime_oddPrimeFactors_fittingSubgroupOf_M_subset
      hmin c w d Kinv K0 F s hKinv_carrier hKinv_cyclic hK0_def hF_eq hjoin
      hFcentE hLayer hp hpOdd hpdvd
  -- (B): prime divisor of `|F(U)|` divides `|K₀|`
  have hpdvdK0 : p ∣ Nat.card K0 :=
    secondCase_equationSevenPrime_primeFactors_FU_subset_K0
      hmin c w d Kinv K0 F s hKinv_carrier hKinv_cyclic hK0_def hF_eq hjoin
      hFcentE hLayer hp hpdvdA
  have hpgcd : p ∣ Nat.gcd (Nat.card K0) (Nat.card K) :=
    Nat.dvd_gcd hpdvdK0 hpdvdK
  rw [hcopK0q.gcd_eq_one] at hpgcd
  exact False.elim (hp.not_dvd_one hpgcd)

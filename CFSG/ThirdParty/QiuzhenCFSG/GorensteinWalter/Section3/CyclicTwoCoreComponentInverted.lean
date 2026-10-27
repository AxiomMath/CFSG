module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreMaximal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePPg
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A nontrivial odd subgroup of the component layer inverted by `t₂`

In the cyclic two-core subcase the maximal overgroup `M` contains `V₂` in
its component layer.  For a nontrivial `y ∈ P₀ = P ∩ M`, the element
`[t₂,y] = y⁻²` lies in the component layer because the layer is normalized
by `M`, and `t₂` inverts it because `t₂` inverts `P₀`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem zpow_inverted_of_generator_inverted
    {G : Type u} [Group G] {s z : G} (h : s * z * s⁻¹ = z⁻¹) (k : ℤ) :
    s * z ^ k * s⁻¹ = (z ^ k)⁻¹ := by
  calc
    s * z ^ k * s⁻¹ = (MulAut.conj s) (z ^ k) := (MulAut.conj_apply s (z ^ k)).symm
    _ = ((MulAut.conj s) z) ^ k := by rw [map_zpow]
    _ = (z⁻¹) ^ k := by rw [MulAut.conj_apply, h]
    _ = (z ^ k)⁻¹ := by
      rw [← zpow_neg]
      simp

public theorem inverted_zpowers_of_generator_inverted
    {G : Type u} [Group G] {s z : G} (h : s * z * s⁻¹ = z⁻¹) :
    BenderGlauberman.IsInvertedBy s (Subgroup.zpowers z) := by
  intro x hx
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, hk⟩
  subst x
  exact zpow_inverted_of_generator_inverted h k

public theorem firstCase_cyclic_inverted_component_odd
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (hV : fd.V2 ≤ componentLayerOf M) :
    ∃ X : Subgroup G,
      X ≤ componentLayerOf M ∧ X ≠ ⊥ ∧ IsCyclic X ∧
        IsPGroup od.p X ∧ X ≤ qCoreOf od.d.bg.U od.p ∧
          BenderGlauberman.IsInvertedBy od.d.bg.t2 X ∧
          X ≤ Subgroup.centralizer (fd.V1 : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let E : Subgroup G := componentLayerOf M
  have hP0ne : P ⊓ M ≠ ⊥ :=
    firstCase_P0_ne_bot hmin c od hfirst hHhat hU Q M hMmax hMN hSM
  have hP0nt : Nontrivial ↥(P ⊓ M) :=
    (Subgroup.nontrivial_iff_ne_bot (P ⊓ M)).2 hP0ne
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥(P ⊓ M))
  let yG : G := y
  have hyP : yG ∈ P := y.2.1
  have hyM : yG ∈ M := y.2.2
  have hyne : yG ≠ 1 := by
    intro h
    apply hy
    apply Subtype.ext
    exact h
  have hT2E : od.d.bg.t2 ∈ E := hV fd.t2_mem_V2
  have hEnorm : IsNormalIn E M := fstar_componentLayerOf_isNormalIn M
  have hyN : yG ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxE
      exact hEnorm.2 yG hyM x hxE
    · intro hxE
      have hyinvM : yG⁻¹ ∈ M := M.inv_mem hyM
      have h' : yG⁻¹ * (yG * x * yG⁻¹) * yG ∈ E :=
        by simpa using hEnorm.2 yG⁻¹ hyinvM (yG * x * yG⁻¹) hxE
      have hEq : yG⁻¹ * (yG * x * yG⁻¹) * yG = x := by group
      simpa [hEq] using h'
  have hinner : yG * od.d.bg.t2⁻¹ * yG⁻¹ ∈ E :=
    hEnorm.2 yG hyM (od.d.bg.t2⁻¹) (E.inv_mem hT2E)
  have hprod : od.d.bg.t2 * (yG * od.d.bg.t2⁻¹ * yG⁻¹) ∈ E :=
    E.mul_mem hT2E hinner
  have hinvY : od.d.bg.t2 * yG * od.d.bg.t2⁻¹ = yG⁻¹ :=
    firstCase_t2_inverts_primeCore c od yG hyP
  let zG : G := (yG⁻¹) ^ 2
  have hzG : od.d.bg.t2 * yG * od.d.bg.t2⁻¹ * yG⁻¹ = zG := by
    rw [hinvY]
    simp [zG, pow_two]
  have hzE : zG ∈ E := by
    have hprod' : (od.d.bg.t2 * yG * od.d.bg.t2⁻¹) * yG⁻¹ ∈ E := by
      simpa [mul_assoc] using hprod
    simpa [hzG] using hprod'
  have hzGne : zG ≠ 1 := by
    intro h
    have hpow2 : (yG⁻¹) ^ 2 = 1 := by
      change (yG⁻¹) ^ 2 = 1 at h
      exact h
    have hord2 : orderOf (yG⁻¹) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hpow2)
    have hordinv : orderOf yG = orderOf (yG⁻¹) := (orderOf_inv yG).symm
    have hordOdd : Odd (orderOf yG) := by
      have hdvd : orderOf yG ∣ Nat.card P :=
        Subgroup.orderOf_dvd_natCard P hyP
      have hPodd : Odd (Nat.card P) := by
        obtain ⟨n, hn⟩ := (qCoreOf_isPGroup od.d.bg.U od.p).exists_card_eq
        rw [hn]
        exact ((Fact.out : Nat.Prime od.p).odd_of_ne_two
          (firstCase_oriented_p_odd c od)).pow
      exact Odd.of_dvd_nat hPodd hdvd
    have hordne : orderOf yG ≠ 1 := by
      intro h
      exact hyne (orderOf_eq_one_iff.mp h)
    have hordle2 : orderOf yG ≤ 2 :=
      by
        have hdvd : orderOf yG ∣ 2 := by
          have hEq : orderOf (yG⁻¹) = orderOf yG := hordinv.symm
          rw [hEq] at hord2
          exact hord2
        exact Nat.le_of_dvd (by omega : 0 < 2) hdvd
    have hordne2 : orderOf yG ≠ 2 := by
      intro h
      exact hordOdd.not_two_dvd_nat (by rw [h])
    have hordpos : 0 < orderOf yG := orderOf_pos yG
    omega
  have hzInv : od.d.bg.t2 * (yG⁻¹) ^ 2 * od.d.bg.t2⁻¹ =
      ((yG⁻¹) ^ 2)⁻¹ := by
    have hconj : od.d.bg.t2 * yG⁻¹ * od.d.bg.t2⁻¹ = yG := by
      calc
        od.d.bg.t2 * yG⁻¹ * od.d.bg.t2⁻¹ =
            (od.d.bg.t2 * yG * od.d.bg.t2⁻¹)⁻¹ := by group
        _ = (yG⁻¹)⁻¹ := by rw [hinvY]
        _ = yG := by simp
    calc
      od.d.bg.t2 * (yG⁻¹) ^ 2 * od.d.bg.t2⁻¹ =
          (od.d.bg.t2 * yG⁻¹ * od.d.bg.t2⁻¹) *
            (od.d.bg.t2 * yG⁻¹ * od.d.bg.t2⁻¹) := by group
      _ = (od.d.bg.t2 * yG⁻¹ * od.d.bg.t2⁻¹) ^ 2 := by
        simp [pow_two]
      _ = yG ^ 2 := by rw [hconj]
      _ = ((yG⁻¹) ^ 2)⁻¹ := by group
  have hzInvGen : od.d.bg.t2 * zG * od.d.bg.t2⁻¹ = zG⁻¹ := by
    dsimp [zG]
    exact hzInv
  let X : Subgroup G := Subgroup.zpowers zG
  have hXleE : X ≤ E := by
    rw [Subgroup.zpowers_le]
    exact hzE
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hzGX : zG ∈ X := Subgroup.mem_zpowers zG
    have hzGbot : zG ∈ (⊥ : Subgroup G) := by simpa [hbot] using hzGX
    exact hzGne (Subgroup.mem_bot.mp hzGbot)
  have hzP : zG ∈ P := by
    have hyinvP : yG⁻¹ ∈ P := P.inv_mem hyP
    exact P.pow_mem hyinvP 2
  have hXleP : X ≤ P := Subgroup.zpowers_le.mpr hzP
  have hXcyc : IsCyclic X := by
    dsimp [X]
    infer_instance
  have hXp : IsPGroup od.p X := by
    exact (qCoreOf_isPGroup od.d.bg.U od.p).to_le hXleP
  have hXinv : BenderGlauberman.IsInvertedBy od.d.bg.t2 X := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, hk⟩
    subst x
    exact zpow_inverted_of_generator_inverted hzInvGen k
  have hXleC : X ≤ Subgroup.centralizer (fd.V1 : Set G) := by
    have hPleC : P ≤ Subgroup.centralizer (fd.V1 : Set G) :=
      firstCase_P_le_centralizer_V1 c od fd
    exact Subgroup.zpowers_le.mpr (hPleC hzP)
  exact ⟨X, hXleE, hXne, hXcyc, hXp, hXleP, hXinv, hXleC⟩

end CFSG.GorensteinWalter

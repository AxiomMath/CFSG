module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreMFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourExceptionTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenKleinFourCentralizerThreePart
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourQuotientOddKernel
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerMap
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The cyclic first-case `A₇` endpoint `|P₀| = 3`

In the `A₇` layer model, the odd-core equality `B ∩ M = O(M)` lets us
push `P₀ = P ∩ M` into the quotient `M / O(M) ≃ A₇` injectively:
`P ∩ B = 1` because `t₂` inverts `P` and fixes `B`, while `B` has odd
order.  The image of `P₀` is a `3`-subgroup of `A₇` (since `od.p = 3`)
which centralizes the Klein-four image of `V₁`; the finite `A₇` endpoint
bounds its order by `3`.  Nontriviality then forces equality.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic first-case `A₇` layer model, `P₀ = O_p(U) ∩ M` has
order `3`. -/
public theorem firstCase_cyclic_P0_card_three_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (hp3 : od.p = 3)
    (hP0ne : qCoreOf od.d.bg.U od.p ⊓ M ≠ ⊥) :
    Nat.card ((qCoreOf od.d.bg.U od.p ⊓ M : Subgroup G)) = 3 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let : BenderGlauberman.Hyp11KData od.d.bg := firstCaseBGKData hmin c od.d
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P0 : Subgroup G := P ⊓ M
  let P0M : Subgroup M := P0.subgroupOf M
  let O0 : Subgroup M := pPrimeCore 2 M
  let O : Subgroup G := O0.map M.subtype
  let : O0.Normal := pPrimeCore_normal
  let Q : Type u := M ⧸ O0
  let : Group Q := QuotientGroup.Quotient.group O0
  let q : M →* Q := QuotientGroup.mk' O0
  let P0Q : Subgroup Q := P0M.map q
  let V1M : Subgroup M := fd.V1.subgroupOf M
  let Vbar : Subgroup Q := V1M.map q
  let eM : Q ≃* alternatingGroup (Fin 7) :=
    (firstCase_cyclic_m_quotient_a7_of_layer_a7
      hmin M hMmax hA7).some
  let PA7 : Subgroup (alternatingGroup (Fin 7)) := P0Q.map eM.toMonoidHom
  let VA : Subgroup (alternatingGroup (Fin 7)) := Vbar.map eM.toMonoidHom

  have hBM : od.d.bg.B ⊓ M = O := by
    dsimp [O]
    exact firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer
      hmin c od M hMmax hSM fd hV2 hA7 hU

  have hPBbot : P ⊓ od.d.bg.B = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxP : x ∈ P := (Subgroup.mem_inf.mp hx).1
    have hxB : x ∈ od.d.bg.B := (Subgroup.mem_inf.mp hx).2
    have hxB2 : x ∈ od.d.bg.B2 :=
      BenderGlauberman.theoremC_mem_B2_of_mem_B od.d.bg hxB
    have hfix : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x :=
      BenderGlauberman.theoremC_fixed_by_t2_of_mem_B2 od.d.bg hxB2
    have hinv : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x⁻¹ :=
      firstCase_t2_inverts_primeCore c od x hxP
    have hx2 : x * x = 1 := by
      calc
        x * x = x⁻¹ * x := congrArg (fun z : G => z * x) (hfix.symm.trans hinv)
        _ = 1 := by simp
    have hord2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
    have hordB : orderOf x ∣ Nat.card (↥od.d.bg.B) :=
      Subgroup.orderOf_dvd_natCard od.d.bg.B hxB
    have hBodd : Odd (Nat.card (↥od.d.bg.B)) :=
      firstCase_cyclic_B_odd c od hU
    have hordOdd : Odd (orderOf x) := Odd.of_dvd_nat hBodd hordB
    have hord1 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact h
      · exfalso
        exact hordOdd.not_two_dvd_nat (by rw [h])
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp hord1

  have hP0O : P0 ⊓ O = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxP0 : x ∈ P0 := (Subgroup.mem_inf.mp hx).1
    have hxO : x ∈ O := (Subgroup.mem_inf.mp hx).2
    have hxP : x ∈ P := (Subgroup.mem_inf.mp hxP0).1
    have hxBM : x ∈ od.d.bg.B ⊓ M := by
      rw [hBM]
      exact hxO
    have hxB : x ∈ od.d.bg.B := (Subgroup.mem_inf.mp hxBM).1
    have hxPB : x ∈ P ⊓ od.d.bg.B := Subgroup.mem_inf.mpr ⟨hxP, hxB⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [hPBbot] at hxPB
      exact hxPB
    exact hxbot

  have hP0M_O0_bot : P0M ⊓ O0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    rw [Subgroup.mem_bot]
    have hxP0M : x ∈ P0M := (Subgroup.mem_inf.mp hx).1
    have hxO0 : x ∈ O0 := (Subgroup.mem_inf.mp hx).2
    have hxP0 : (x : G) ∈ P0 := Subgroup.mem_subgroupOf.mp hxP0M
    have hxO : (x : G) ∈ O := Subgroup.mem_map.mpr ⟨x, hxO0, rfl⟩
    have hxinf : (x : G) ∈ P0 ⊓ O := Subgroup.mem_inf.mpr ⟨hxP0, hxO⟩
    have hxbotG : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [hP0O] at hxinf
      exact hxinf
    have hx1G : (x : G) = 1 := Subgroup.mem_bot.mp hxbotG
    apply Subtype.ext
    exact hx1G

  have hker : q.ker = O0 := QuotientGroup.ker_mk' O0
  have hP0Mker : P0M ⊓ q.ker = ⊥ := by
    simpa [hker] using hP0M_O0_bot
  have hcardQ : Nat.card P0M = Nat.card P0Q := by
    have h := card_map_eq_card_mul_card_ker q P0M
    rw [hP0Mker] at h
    simpa [P0Q, Nat.mul_one] using h
  have hcardP0M : Nat.card P0M = Nat.card P0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcardP0 : Nat.card P0 = Nat.card P0Q :=
    hcardP0M.symm.trans hcardQ

  have hP0p : IsPGroup od.p P0 :=
    (qCoreOf_isPGroup od.d.bg.U od.p).to_inf_left
  have hP0Mp : IsPGroup od.p P0M :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hP0Qp : IsPGroup od.p P0Q := IsPGroup.map hP0Mp q
  have hP0Qp3 : IsPGroup 3 P0Q := by simpa [hp3] using hP0Qp
  have hPA7p3 : IsPGroup 3 PA7 := IsPGroup.map hP0Qp3 eM.toMonoidHom

  have hV1leM : fd.V1 ≤ M := fd.V1_le_S.trans hSM
  have hV1MK : IsKleinFour V1M := by
    dsimp [V1M]
    exact isKleinFour_subgroupOf hV1leM fd.V1_klein
  have hO0odd : Odd (Nat.card O0) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hVbarK : IsKleinFour Vbar := by
    dsimp [Vbar]
    exact isKleinFour_map_quotient_of_odd_kernel O0 V1M hO0odd hV1MK
  have hVAK : IsKleinFour VA := by
    dsimp [VA]
    exact isKleinFour_map_mulEquiv_cross Vbar hVbarK eM

  have hPleC : qCoreOf od.d.bg.U od.p ≤
      Subgroup.centralizer (fd.V1 : Set G) :=
    firstCase_cyclic_P_le_centralizer_V1 c od fd
  have hP0leC : P0 ≤ Subgroup.centralizer (fd.V1 : Set G) := by
    intro x hx
    exact hPleC (Subgroup.mem_inf.mp hx).1
  have hP0leM : P0 ≤ M := inf_le_right
  have hP0MleCV1M : P0M ≤ Subgroup.centralizer (V1M : Set M) := by
    dsimp [P0M, V1M]
    exact centralizer_subgroupOf_le (A := fd.V1) (V := P0)
      hV1leM hP0leM hP0leC
  have hP0QleCVbar : P0Q ≤ Subgroup.centralizer (Vbar : Set Q) := by
    dsimp [P0Q, Vbar]
    exact centralizer_map_le_of_hom q V1M P0M hP0MleCV1M
  have hPA7leCVA : PA7 ≤
      Subgroup.centralizer (VA : Set (alternatingGroup (Fin 7))) := by
    dsimp [PA7, VA]
    exact centralizer_map_le_of_mulEquiv eM Vbar P0Q hP0QleCVbar

  have hPA7le3 : Nat.card PA7 ≤ 3 :=
    aSeven_three_subgroup_centralizing_kleinFour_card_le_three
      hVAK hPA7p3 hPA7leCVA
  have hcardPA7 : Nat.card PA7 = Nat.card P0Q := by
    dsimp [PA7]
    exact Subgroup.card_map_of_injective
      (K := P0Q) (f := eM.toMonoidHom) eM.injective
  have hP0le3 : Nat.card P0 ≤ 3 := by
    rw [hcardP0, ← hcardPA7]
    exact hPA7le3

  have hP03 : IsPGroup 3 P0 := by simpa [hp3] using hP0p
  obtain ⟨n, hn⟩ := hP03.exists_card_eq
  have hnpos : n ≠ 0 := by
    intro h0
    apply hP0ne
    rw [Subgroup.eq_bot_iff_card]
    rw [hn, h0]
    norm_num
  have h3dvd : 3 ∣ Nat.card P0 := by
    rw [hn]
    exact dvd_pow_self 3 hnpos
  have hcardpos : 0 < Nat.card P0 := Nat.card_pos
  have h3le : 3 ≤ Nat.card P0 := Nat.le_of_dvd hcardpos h3dvd
  exact le_antisymm hP0le3 h3le

end CFSG.GorensteinWalter

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvolutionDecomposition
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (3): the Fitting-subgroup restriction

The involution decomposition `secondCase_involution_decomposition` provides
the cyclic inverted subgroup `K = I_{U∩M}(s)` and its centralizer complement
`B = C_{U∩M}(s)` in `X = U ∩ M`.  This module restricts that decomposition to
`F(U) ∩ M`: with `FU = F(U)`, `Y = FU ∩ M`, `sG = (s : G)`, equation (3)
asserts

* `K0 := FU ∩ K` is the set of elements of `Y` inverted by `sG`;
* `F := FU ∩ B = C_Y(sG)`;
* `K0 ⊔ F = Y`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Membership in `centralizerIn X s`, unfolded as membership in `X` plus
fixing `s` by conjugation. -/
private theorem mem_centralizerIn_local {G : Type u} [Group G]
    (X : Subgroup G) (s x : G) :
    x ∈ centralizerIn X s ↔ x ∈ X ∧ s * x * s⁻¹ = x := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hcomm : s * x = x * s :=
      (Subgroup.mem_centralizer_iff.mp hx.2) s (by simp)
    rw [hcomm]
    group
  · rintro ⟨hxX, hxfix⟩
    refine ⟨hxX, ?_⟩
    change x ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzs : z = s := by simpa using hz
    rw [hzs]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hxfix)

/-- Section 4, equation (3): the involution decomposition restricts to the
Fitting subgroup of `U`, producing `K0 = F(U) ∩ K`, `F = F(U) ∩ B =
C_{F(U) ∩ M}(s)`, and `F(U) ∩ M = K0 ⊔ F`.  The ambient and component Sylow
data, the involution `s`, and the original `K/B` decomposition are preserved. -/
public theorem secondCase_fitting_involution_decomposition
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    ∃ SM : Sylow 2 (↥w.M),
      ((SM : Subgroup w.M).map w.M.subtype) ≤
        Subgroup.centralizer ({c.t} : Set G) ∧
      ∃ SE : Sylow 2 (↥d.E),
        (SE : Subgroup d.E).map d.E.subtype =
          ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E ∧
        ∃ T : Subgroup (d.E ⧸ Subgroup.center d.E),
          ∃ s : d.E,
            let q : d.E →* d.E ⧸ Subgroup.center d.E :=
              QuotientGroup.mk' (Subgroup.center d.E)
            let qt : d.E ⧸ Subgroup.center d.E := q ⟨c.t, d.t_mem_E⟩
            let UEbar : Subgroup (d.E ⧸ Subgroup.center d.E) :=
              ((c.U ⊓ d.E).subgroupOf d.E).map q
            s ∈ (SE : Subgroup d.E) ∧ IsInvolution s ∧
              IsCyclic T ∧ q s ∉ T ∧
              BenderGlauberman.IsInvertedBy (q s) T ∧
              (∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
                (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X →
                  Odd (orderOf x)) →
                  X ≤ Subgroup.centralizer
                    ({qt} : Set (d.E ⧸ Subgroup.center d.E)) →
                    X ≤ T) ∧
              UEbar ≤ T ∧
              IsCyclic UEbar ∧
              BenderGlauberman.IsInvertedBy (q s) UEbar ∧
              ∃ K B : Subgroup G,
                (K : Set G) =
                  invertedElements (c.U ⊓ w.M) (s : G) ∧
                IsCyclic K ∧
                B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
                K ⊔ B = c.U ⊓ w.M ∧
                ∃ K0 F : Subgroup G,
                  K0 = fittingSubgroupOf c.U ⊓ K ∧
                  F = fittingSubgroupOf c.U ⊓ B ∧
                  F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G) ∧
                  K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc, hq_s_not_T,
      hinvT, hcontainT, hUEbar_le_T, hUEbar_cyclic, hUEbar_inv, K, B,
      hK_eq, hK_cyc, hB_def, hjoinX⟩ :=
    secondCase_involution_decomposition c w d
  let sG : G := s
  let X : Subgroup G := c.U ⊓ w.M
  let FU : Subgroup G := fittingSubgroupOf c.U
  let Y : Subgroup G := FU ⊓ w.M
  let K0 : Subgroup G := FU ⊓ K
  let F : Subgroup G := FU ⊓ B
  -- ambient membership of `s`
  have hsmap : sG ∈ (SE : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hsSM : sG ∈ ((SM : Subgroup w.M).map w.M.subtype) := by
    rw [hSEamb] at hsmap
    exact hsmap.1
  have hsM : sG ∈ w.M := (Subgroup.map_subtype_le (SM : Subgroup w.M)) hsSM
  have hsH : sG ∈ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent hsSM
  have hsIG : IsInvolution sG := by
    constructor
    · intro h1
      apply hsI.1
      apply Subtype.ext
      exact h1
    · simpa [sG, pow_two] using congrArg Subtype.val hsI.2
  -- `s` normalizes `F(U)`, because it lies in `H = C_G(t)` and `F(U)` is
  -- characteristic in the normal subgroup `U = O(H)` of `H`
  have hU_normalH : IsNormalIn c.U c.H := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
    · intro h hh x hx
      rcases (Subgroup.mem_map).1 hx with ⟨p, hp, rfl⟩
      have hconj : (⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹ ∈
          pPrimeCore 2 c.H :=
        (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
          p hp (⟨h, hh⟩ : ↥c.H)
      exact Subgroup.mem_map.mpr
        ⟨(⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹, hconj, by simp⟩
  have hFUnormalH : IsNormalIn (fittingSubgroupOf c.U) c.H := by
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.H
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := fittingSubgroup (↥c.U)) (hKchar := by infer_instance)
      (hHnormal := hU_normalH)
  -- `Y` is odd, and `s` normalizes `Y`
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hYleU : Y ≤ c.U := by
    intro y hy
    exact fittingSubgroupOf_le c.U hy.1
  have hoddY : Odd (Nat.card (↥Y)) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hYleU)
  have hcopY : Nat.Coprime 2 (Nat.card (↥Y)) :=
    Nat.coprime_two_left.mpr hoddY
  have hsY : ∀ y : G, y ∈ Y → sG * y * sG⁻¹ ∈ Y := by
    intro y hy
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨hFUnormalH.2 sG hsH y hy.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hsM hy.2) (w.M.inv_mem hsM)
  -- equation (3): `K0 = I_Y(sG)` and `F = C_Y(sG)`
  have hK0_carrier : (K0 : Set G) = invertedElements Y sG := by
    ext y
    constructor
    · intro hyK0
      have hyFU : y ∈ FU := hyK0.1
      have hyK : y ∈ K := hyK0.2
      have hyI : y ∈ invertedElements X sG := by
        rw [← hK_eq]
        exact hyK
      rw [invertedElements] at hyI ⊢
      exact ⟨⟨hyFU, hyI.1.2⟩, hyI.2⟩
    · intro hyI
      rw [invertedElements] at hyI
      have hyFU : y ∈ FU := hyI.1.1
      have hyM : y ∈ w.M := hyI.1.2
      have hyX : y ∈ X :=
        Subgroup.mem_inf.mpr ⟨fittingSubgroupOf_le c.U hyFU, hyM⟩
      have hyK : y ∈ K := by
        change y ∈ (K : Set G)
        rw [hK_eq]
        rw [invertedElements]
        exact ⟨hyX, hyI.2⟩
      show y ∈ FU ⊓ K
      exact ⟨hyFU, hyK⟩
  have hF_eq : F = centralizerIn Y sG := by
    ext x
    constructor
    · intro hxF
      have hxB : x ∈ B := hxF.2
      have hxfix : sG * x * sG⁻¹ = x :=
        (mem_centralizerIn_local X sG x).mp (by simpa [hB_def] using hxB) |>.2
      have hxM : x ∈ w.M :=
        (mem_centralizerIn_local X sG x).mp (by simpa [hB_def] using hxB) |>.1 |>.2
      exact (mem_centralizerIn_local Y sG x).mpr ⟨⟨hxF.1, hxM⟩, hxfix⟩
    · intro hxC
      have hxY : x ∈ Y := (mem_centralizerIn_local Y sG x).mp hxC |>.1
      have hxfix : sG * x * sG⁻¹ = x :=
        (mem_centralizerIn_local Y sG x).mp hxC |>.2
      have hxU : x ∈ c.U := fittingSubgroupOf_le c.U hxY.1
      have hxB : x ∈ B := by
        simpa [hB_def] using (mem_centralizerIn_local X sG x).mpr
          ⟨Subgroup.mem_inf.mpr ⟨hxU, hxY.2⟩, hxfix⟩
      exact Subgroup.mem_inf.mpr ⟨hxY.1, hxB⟩
  -- `K0 ⊔ F = Y` by Fact 1.5(ii)/(iii), exactly as for `K ⊔ B = X`
  have hK0_le_Y : K0 ≤ Y := by
    intro y hy
    have : y ∈ invertedElements Y sG := by
      rw [← hK0_carrier]
      exact hy
    rw [invertedElements] at this
    exact this.1
  have hF_le_Y : F ≤ Y := by
    intro x hx
    exact (mem_centralizerIn_local Y sG x).mp (by simpa [hF_eq] using hx) |>.1
  have hK0normal : IsNormalIn K0 Y :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal (X := Y) (s := sG)
      hsIG hcopY hsY (I := K0) hK0_carrier).2.1
  have hF_le_NK0 : F ≤ Subgroup.normalizer (K0 : Set G) := by
    intro f hf
    exact le_normalizer_of_isNormalIn hK0normal (hF_le_Y hf)
  have hcarrier : (↑(K0 ⊔ F) : Set G) = (K0 : Set G) * (F : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K0 F hF_le_NK0
  have hFK0_eq : (F : Set G) * (K0 : Set G) = (K0 : Set G) * (F : Set G) :=
    Subgroup.set_mul_normalizer_comm (S := (F : Set G)) (N := K0) hF_le_NK0
  have hjoinY : K0 ⊔ F = Y := by
    apply le_antisymm
    · exact sup_le hK0_le_Y hF_le_Y
    · intro y hyY
      rcases fact_1_5_ii_decomposition (X := Y) (s := sG) hsIG hcopY hsY y hyY
        with ⟨c, hcC, i, hiI, hyi⟩
      have hcF : c ∈ F := by
        rw [hF_eq]
        exact hcC
      have hiK0 : i ∈ K0 := by
        change i ∈ (K0 : Set G)
        rw [hK0_carrier]
        exact hiI
      have hy_FK0 : y ∈ (F : Set G) * (K0 : Set G) :=
        ⟨c, hcF, i, hiK0, hyi.symm⟩
      have hy_K0F : y ∈ (K0 : Set G) * (F : Set G) := by
        rw [hFK0_eq] at hy_FK0
        exact hy_FK0
      change y ∈ (↑(K0 ⊔ F) : Set G)
      rw [hcarrier]
      exact hy_K0F
  have hK0_def : K0 = fittingSubgroupOf c.U ⊓ K := by
    change K0 = FU ⊓ K
    rfl
  have hF_def : F = fittingSubgroupOf c.U ⊓ B := by
    change F = FU ⊓ B
    rfl
  refine ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc, hq_s_not_T,
    hinvT, hcontainT, hUEbar_le_T, hUEbar_cyclic, hUEbar_inv,
    K, B, hK_eq, hK_cyc, hB_def, hjoinX, K0, F, hK0_def, hF_def, ?_, ?_⟩
  · simpa [FU, Y, sG] using hF_eq
  · simpa [FU, Y] using hjoinY

end CFSG.GorensteinWalter

module

public import CFSG.LocalAnalysis.StandardType.GGResJTwE6Lagrange
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeBLinearNs
import CFSG.Quasithin.Vol2.Ch11L2Q5cF4Ord
import CFSG.Timmesfeld.Orders.Bang
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import CFSG.LocalAnalysis.StandardType.GGPZWeylType

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ppd_dvd_ordTwistedE6 {r m : ℕ} (hm : 1 ≤ m)
    (hr : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r (18 * m)) : r ∣ ordTwistedE6 (2 ^ m) := by
  have hk : 0 < 18 * m := by omega
  have h9 : r ∣ (2 ^ m) ^ 9 + 1 := by
    rw [← pow_mul]
    refine (hr.dvd_add_one_iff hk (m * 9)).mpr ⟨⟨1, by ring⟩, fun h => ?_⟩
    have := Nat.le_of_dvd (by omega) h
    omega
  have h3 : ¬ r ∣ 3 := fun h => by
    have := hr.eq_two_of_dvd_three hk h
    omega
  unfold ordTwistedE6
  set q := 2 ^ m
  have hrN : r ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1) :=
    h9.trans (((((dvd_mul_left _ _).mul_right _).mul_right _).mul_right _).mul_right _)
  have hgN : Nat.gcd 3 (q + 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) :=
    (Nat.gcd_dvd_right 3 (q + 1)).trans
      ((EvenSmallLie.CatalogOrders.add_one_dvd_sq_sub_one q).trans (dvd_mul_left _ _))
  have hcop : Nat.Coprime (Nat.gcd 3 (q + 1)) r :=
    (((Nat.Prime.coprime_iff_not_dvd hr.prime).mpr h3).coprime_dvd_right
      (Nat.gcd_dvd_left 3 (q + 1))).symm
  exact Nat.dvd_div_of_mul_dvd (hcop.mul_dvd_of_dvd_of_dvd hgN hrN)

theorem ggTwE6ThreeFreeLabel_of_linear {lab₀ : LargeEvenLabel} (h0 : LargeEvenInLambda2 lab₀)
    (ht : lab₀.tag = .A) (hr : lab₀.rank ≤ 16) : GGTwE6ThreeFreeLabel lab₀ := by
  intro _ lab hiso μ hμ htμ _ hdvd hdiv
  have hm : 1 ≤ μ.n := hμ.1
  have hle : lab.n ≤ μ.n := Nat.le_of_dvd hm hdvd
  have hkey : lab₀.n * (lab₀.rank + 1) < 18 * μ.n := by
    have hle' : lab₀.n ≤ μ.n → lab₀.n * (lab₀.rank + 1) < 18 * μ.n := fun h =>
      calc lab₀.n * (lab₀.rank + 1) ≤ μ.n * 17 := Nat.mul_le_mul h (by omega)
        _ < 18 * μ.n := by omega
    rcases hiso with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · subst h
      exact hle' hle
    · rw [ht] at h
      rcases h with h | h <;> cases h
    · rw [h] at ht
      cases ht
    · rw [h] at hle
      exact hle' hle
    · rw [h] at ht
      cases ht
    · rw [h] at ht
      cases ht
    · rw [h] at ht
      cases ht
    · rw [h]
      dsimp only
      omega
  obtain ⟨r, hppd⟩ :=
    CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 18 * μ.n) (by omega) (by omega)
  have hk : 0 < 18 * μ.n := by omega
  have hr₀ : r ∣ SporadicShape.labOrd lab₀ := by
    refine dvd_trans ?_ hdiv
    rw [labOrd_eq_ordTwistedE6 htμ]
    exact ppd_dvd_ordTwistedE6 hm hppd
  obtain ⟨t, l, n⟩ := lab₀
  dsimp only at ht hr hkey
  subst ht
  obtain ⟨hn, hl, -⟩ := h0
  dsimp only at hn hl
  have hA : SporadicShape.labOrd ⟨.A, l, n⟩ = ordA l (2 ^ n) := rfl
  rw [hA] at hr₀
  obtain ⟨i, hi, hdi⟩ := CFSG.Quasithin.Vol2.Ch11.SecB.index_of_prim_dvd_ordA hl hppd hk hr₀
  rw [Finset.mem_Icc] at hi
  have h1 : 18 * μ.n ≤ n * i := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdi
  have h2 : n * i ≤ n * (l + 1) := Nat.mul_le_mul_left n hi.2
  exact absurd (h1.trans h2) (Nat.not_le.mpr hkey)

theorem GGResHyp.nonsingAut_K_of_linearNs (hcyc : GGLabelCenterPCyclicInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hS : ∀ lab, S p lab → lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1)
    (hK : GGInnerDiagOnLabel S p Bs K) : GGResNonsingAut p Bs K := by
  refine ⟨hH.not_ggSingularWeylOrder_K_of_linearNs hcyc hS hK, fun hp3 r c hr5 hW => ?_⟩
  obtain ⟨k, lab, hk, ⟨e, -⟩, hΛ, hSl, hrk, hhas⟩ :=
    ggWeylOfType_B_nbr_of_linearNs hcyc hH.1 hH.2.2.2.1 hH.2.2.2.2.1 hS hK
  have hcard : Nat.card ↥(ggAutomizer K Bs) = 2 ^ k * k.factorial :=
    (Nat.card_congr e.toEquiv).symm.trans (ggCoxeterB_card k (by omega))
  have hB : GGWeylTypeData k (Nat.card ↥(ggAutomizer K Bs)) 2 :=
    Or.inr (Or.inl ⟨by omega, hcard, rfl⟩)
  have hrk' : r = k := ggWeylTypeData_rank_eq hW hB
  rw [hp3] at hrk
  exact ⟨lab, hΛ, hhas, ggTwE6ThreeFreeLabel_of_linear hΛ (hS lab hSl).1 (by omega)⟩

section Exclusion


theorem ggResExact3_false_of_linearNs_K (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hcyc : GGLabelCenterPCyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {S S' : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S' p Bs J)
    (hS : ∀ lab, S p lab → lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1)
    (hK : GGInnerDiagOnLabel S p Bs K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False :=
  ggResExact3_false_of_nonsingAut_K hT hLift hTCJ hRig hLB hP hH hJ
    (hH.nonsingAut_K_of_linearNs hcyc hS hK) hD

end Exclusion

end CFSG.StandardType

end

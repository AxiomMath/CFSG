module

public import CFSG.RankThree.GF2n.Stroth80.Sec117Config
public import CFSG.LocalAnalysis.StandardType.SURadicalVector
import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic
import CFSG.RankThree.OddKernel.OddLift
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.LocalAnalysis.StandardType.SUCenterOdd
import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.StandardType.SUTransvection

open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.StandardType.RCSTSU CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Stroth80
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom mat_iotaHom)

theorem range_forall_normal_of_isQuasisimple {Q X : Type*} [Group Q] [Group X] (ψ : Q →* X)
    (hQ : CFSG.IsQuasisimple Q) (H : Subgroup X) (hH : H ≤ ψ.range)
    (hHn : ∀ l ∈ ψ.range, ∀ h ∈ H, l * h * l⁻¹ ∈ H) :
    H ≤ centralizer (ψ.range : Set X) ∨ ψ.range ≤ H := by
  have hnorm : (H.comap ψ).Normal := ⟨fun n hn g => by
    show ψ (g * n * g⁻¹) ∈ H
    rw [map_mul, map_mul, map_inv]
    exact hHn _ ⟨g, rfl⟩ _ hn⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ (H.comap ψ) with hc | ht
  · left
    intro x hx
    obtain ⟨q, rfl⟩ := hH hx
    rw [mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    rw [← map_mul, ← map_mul, mem_center_iff.mp (hc (show q ∈ H.comap ψ from hx)) g]
  · right
    rintro _ ⟨g, rfl⟩
    have hg : g ∈ H.comap ψ := by
      rw [ht]
      exact mem_top g
    exact hg

theorem odd_orderOf_of_mem_centralizer_range {Q X : Type*} [Group Q] [Group X] [Finite Q]
    (ψ : Q →* X) (hQ : CFSG.IsQuasisimple Q) (hZ : Odd (Nat.card (center Q)))
    (hker : ψ.ker ≤ center Q) {z : X} (hz : z ∈ ψ.range)
    (hzc : z ∈ centralizer (ψ.range : Set X)) : Odd (orderOf z) := by
  obtain ⟨b, rfl⟩ := hz
  obtain ⟨-, hs, a₀, b₀, hab⟩ := hQ
  have hcomm : ∀ g : Q, ψ g * ψ b = ψ b * ψ g := fun g =>
    mem_centralizer_iff.mp hzc _ ⟨g, rfl⟩
  have hcen : (b : Q ⧸ center Q) ∈ center (Q ⧸ center Q) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hcomm g, inv_mul_cancel]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Q ⧸ center Q)) with h | h
  · rw [h, mem_bot, QuotientGroup.eq_one_iff] at hcen
    exact Odd.of_dvd_nat hZ ((orderOf_map_dvd ψ b).trans (Subgroup.orderOf_dvd_natCard _ hcen))
  · have ha : a₀ ∈ center (Q ⧸ center Q) := by
      rw [h]
      exact mem_top a₀
    exact absurd (mem_center_iff.mp ha b₀).symm hab

theorem isConj_sq_of_isStrothInvolution_map {G X : Type*} [Group G] [Group X] (π : G →* X)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center G) (hodd : Odd (Nat.card π.ker))
    {u : G} (hu : u ^ 2 = 1) {a : ℕ} (ht : IsStrothInvolution (π u) a) {x y : G}
    (hx : IsConj u x) (hy : IsConj u y) (h4 : orderOf (x * y) = 4) :
    IsConj ((x * y) ^ 2) u := by
  have h44 : ((x * y) ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = orderOf (x * y) by rw [h4], pow_orderOf_eq_one]
  have hne : ¬ π (x * y) ^ 2 ^ 1 = 1 := by
    intro h1
    rw [pow_one, ← map_pow] at h1
    have h2 : (⟨(x * y) ^ 2, MonoidHom.mem_ker.mpr h1⟩ : π.ker) = 1 :=
      CFSG.Alternating.Multipliers.eq_one_of_sq_eq_one_of_odd hodd
        (Subtype.ext (by simpa using h44))
    have h3 := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val h2)
    rw [h4] at h3
    norm_num at h3
  have hfin : π (x * y) ^ 2 ^ (1 + 1) = 1 := by
    rw [← map_pow, show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h44, map_one]
  have h4' : orderOf (π x * π y) = 4 := by
    rw [← map_mul]
    simpa using orderOf_eq_prime_pow (p := 2) (n := 1) hne hfin
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (ht.isConj_sq_of_orderOf_eq_four (π.map_isConj hx) (π.map_isConj hy) h4')
  obtain ⟨g, rfl⟩ := hπ c
  refine isConj_iff.mpr ⟨g, CFSG.Alternating.Multipliers.eq_of_sq_eq_one hker hodd ?_ ?_ hu⟩
  · rw [← hc]
    simp only [map_mul, map_pow, map_inv]
  · rw [conj_pow, h44, mul_one, mul_inv_cancel]

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

private theorem not_isMulCommutative_map_suRad {X : Type*} [Group X] {k : ℕ}
    (hσ : IsUnitaryInvolution σ) (hk : 1 ≤ k) (ψ : SU σ (k + 2) →* X)
    (hker : ψ.ker ≤ center (SU σ (k + 2))) :
    ¬ IsMulCommutative ↥((suRad σ k).map ψ) := by
  intro hS
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mem_suRad_not_commute hσ hk
  have hcomm : ψ x * ψ y = ψ y * ψ x := by
    simpa using congrArg Subtype.val (mul_comm' ⟨ψ x, mem_map_of_mem ψ hx⟩
      ⟨ψ y, mem_map_of_mem ψ hy⟩)
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ suRad σ k ⊓ ψ.ker := by
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact (suRad σ k).mul_mem ((suRad σ k).mul_mem ((suRad σ k).mul_mem hx hy)
        ((suRad σ k).inv_mem hx)) ((suRad σ k).inv_mem hy)
    · rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hcomm]
      group
  have hbot : suRad σ k ⊓ ψ.ker = ⊥ :=
    CFSG.RankThree.OddKernel.inf_eq_bot_of_odd suRad_isPGroup
      (CFSG.StandardType.odd_natCard_of_le_center_SU σ hker)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hxy (by
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [hmem, one_mul])

theorem iotaHom_mem_of_isA2PlaneKernel (hσ : IsUnitaryInvolution σ) {j : ℕ} (hj : 1 ≤ j)
    {X : Type*} [Group X] (π : SU σ (j + 2 + 2) →* X)
    (hker : π.ker ≤ center (SU σ (j + 2 + 2))) (hq : CFSG.IsQuasisimple (SU σ (j + 2)))
    {a : ℕ} {N : Subgroup X} (hN : IsA2PlaneKernel (π (ggInvSU σ (j + 2 + 2) 1)) a N)
    (g : SU σ (j + 2)) : π (iotaHom g) ∈ N := by
  set ψ : SU σ (j + 2) →* X := π.comp (iotaHom (σ := σ) (m := j + 2)) with hψ
  have hkerψ : ψ.ker ≤ center (SU σ (j + 2)) := by
    rw [hψ, ← MonoidHom.comap_ker]
    have hinj : Function.Injective (iotaHom (σ := σ) (m := j + 2)) :=
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom_injective
    exact (Subgroup.comap_mono hker).trans (Subgroup.comap_center_le_center hinj)
  have hZ : Odd (Nat.card (center (SU σ (j + 2)))) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU σ (H := center (SU σ (j + 2))) le_rfl
  have hL : ψ.range ≤ Subgroup.centralizer ({π (ggInvSU σ (j + 2 + 2) 1)} : Set X) := by
    rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hB := RCSTSU.range_iotaHom_le_centralizer (σ := σ) (k := j + 2) ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hB
    change π (iotaHom B) * π (ggInvSU σ (j + 2 + 2) 1) =
      π (ggInvSU σ (j + 2 + 2) 1) * π (iotaHom B)
    rw [← map_mul, ← map_mul, hB]
  refine hN.le_of_forall_normal (L := ψ.range) (S := (suRad σ j).map ψ) hL ?_ ?_
    (Subgroup.map_le_range ψ (suRad σ j)) (RCSTSU.suRad_isPGroup.map ψ) ?_ ⟨g, rfl⟩
  · intro H hH hHn
    exact range_forall_normal_of_isQuasisimple ψ hq H hH hHn
  · intro z hz hzc
    exact odd_orderOf_of_mem_centralizer_range ψ hq hZ hkerψ hz hzc
  · have hnc := not_isMulCommutative_map_suRad hσ hj ψ hkerψ
    rw [isMulCommutative_iff, not_forall] at hnc
    obtain ⟨x, hx⟩ := hnc
    rw [not_forall] at hx
    obtain ⟨y, hxy⟩ := hx
    exact ⟨x, x.2, y, y.2, fun h => hxy (Subtype.ext h)⟩

end CFSG.StandardType.SUTransvection

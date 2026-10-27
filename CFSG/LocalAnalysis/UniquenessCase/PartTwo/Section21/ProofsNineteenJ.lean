module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenJankoOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.LocalAnalysis.UniquenessCase.UC22P218a
import CFSG.LocalAnalysis.UniquenessCase.UC22P218s

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL)

variable {G : Type} [Group G] [Finite G]

private theorem exists_mem_normalizer_sylow_of_isJ1 {L : Subgroup G} (hJ1 : IsJ1 (Bar2 L))
    (Q : Sylow 2 ↥L) :
    ∃ y : ↥L, y ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) ∧ 3 ∣ orderOf y := by
  classical
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Qb : Sylow 2 (Bar2 L) := Q.mapSurjective (f := π) hπ
  obtain ⟨ybar, hybarN, hybar3⟩ :=
    exists_orderOf_eq_three_mem_normalizer_of_isJ1 hJ1 Qb
  obtain ⟨y, hy⟩ := hπ ybar
  have hQbmap : (Qb : Subgroup (Bar2 L)) = Q.map π := rfl
  have hker : π.ker ≤ Q := by
    rw [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _]
    exact CFSG.fitting_pCore_le_sylow Q
  have hcomap : (Qb : Subgroup (Bar2 L)).comap π = Q := by
    rw [hQbmap]
    exact Subgroup.comap_map_eq_self hker
  have hmemQ : ∀ z : ↥L, z ∈ Q ↔ π z ∈ (Qb : Subgroup (Bar2 L)) := by
    intro z
    have hiff : z ∈ Q ↔ z ∈ (Qb : Subgroup (Bar2 L)).comap π := by
      rw [hcomap]
      exact Iff.rfl
    exact hiff.trans Subgroup.mem_comap
  have hNQ : y ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have h1 : π (y * q * y⁻¹) ∈ (Qb : Subgroup (Bar2 L)) := by
        rw [map_mul, map_mul, map_inv, hy]
        exact (Subgroup.mem_normalizer_iff.1 hybarN (π q)).1 ((hmemQ q).1 hq)
      exact (hmemQ (y * q * y⁻¹)).2 h1
    · intro hq
      have h1 : π (y * q * y⁻¹) ∈ (Qb : Subgroup (Bar2 L)) := (hmemQ _).1 hq
      have h2 : ybar * π q * ybar⁻¹ ∈ (Qb : Subgroup (Bar2 L)) := by
        simpa only [map_mul, map_inv, hy] using h1
      exact (hmemQ q).2 ((Subgroup.mem_normalizer_iff.1 hybarN (π q)).2 h2)
  have hdvd : 3 ∣ orderOf y := by
    have := orderOf_map_dvd π y
    rwa [hy, hybar3] at this
  exact ⟨y, hNQ, hdvd⟩

private theorem conj_mem_inf_of_mem_normalizer_sylow {L T : Subgroup G} {Q : Sylow 2 ↥L}
    (hQ : (Q : Subgroup ↥L).map L.subtype = T ⊓ L) {a : ↥L}
    (ha : a ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)) {z : ↥L}
    (hz : (z : G) ∈ T ⊓ L) : ((a : G) * (z : G) * (a : G)⁻¹) ∈ T ⊓ L := by
  have hzQ : z ∈ (Q : Subgroup ↥L) :=
    (Subgroup.mem_map_iff_mem L.subtype_injective).mp (by rw [hQ]; exact hz)
  have h1 : L.subtype ((MulAut.conj a) z) ∈ (Q : Subgroup ↥L).map L.subtype :=
    Subgroup.mem_map_of_mem _ ((Subgroup.mem_normalizer_iff.1 ha z).1 hzQ)
  rw [hQ] at h1
  simpa [MulAut.conj_apply] using h1

private theorem exists_mem_normalizer_of_isJ1 {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowOf 2 (T ⊓ L) L)
    (hJ1 : IsJ1 (Bar2 L)) :
    ∃ u ∈ L, orderOf u = 3 ∧ u ∈ Subgroup.normalizer (T : Set G) := by
  have hinn : (T.subgroupOf (Subgroup.normalizer (L : Set G))).map (rhoL L) ≤
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
    rintro θ ⟨t, -, ht⟩
    obtain ⟨x, hx⟩ := (kJ1_holds (Bar2 L) hJ1).2.2 (rhoL L t)
    exact ⟨x, by rw [← hx]; exact ht⟩
  have hle := inf_normalizer_le_normalizer_of_inner hT hTL hS hinn
  obtain ⟨Q, hQ⟩ := hS
  obtain ⟨y, hyN, hy3⟩ := exists_mem_normalizer_sylow_of_isJ1 hJ1 Q
  have hyH : ((y : G)) ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    refine ⟨y.2, ?_⟩
    change (y : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact conj_mem_inf_of_mem_normalizer_sylow hQ hyN
        (z := ⟨z, (Subgroup.mem_inf.1 hz).2⟩) hz
    · intro hz
      have hzL : ((y : G) * z * (y : G)⁻¹) ∈ L := (Subgroup.mem_inf.1 hz).2
      have hkey := conj_mem_inf_of_mem_normalizer_sylow hQ (inv_mem hyN)
        (a := y⁻¹) (z := ⟨(y : G) * z * (y : G)⁻¹, hzL⟩) hz
      have hcalc : ((y⁻¹ : ↥L) : G) * ((y : G) * z * (y : G)⁻¹) *
          (((y⁻¹ : ↥L) : G))⁻¹ = z := by
        simp only [Subgroup.coe_inv]
        group
      rwa [hcalc] at hkey
  have hyN' : (y : G) ∈ Subgroup.normalizer (T : Set G) := hle hyH
  have h3dvd : 3 ∣ orderOf (y : G) := by rwa [Subgroup.orderOf_coe]
  let u : G := (y : G) ^ (orderOf (y : G) / 3)
  have huord : orderOf u = 3 := by
    dsimp only [u]
    exact orderOf_pow_orderOf_div (orderOf_pos (y : G)).ne' h3dvd
  exact ⟨u, L.pow_mem y.2 _, huord, (Subgroup.normalizer (T : Set G)).pow_mem hyN' _⟩

theorem exists_orderOf_eq_three_le_normalizer_of_isJ1 (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hLn : (L.subgroupOf D.M).Normal) (hJ1 : IsJ1 (Bar2 L)) :
    ∃ u ∈ L, orderOf u = 3 ∧ Subgroup.zpowers u ≤ Subgroup.normalizer (D.T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := hL.1.le
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hTL : D.T ≤ Subgroup.normalizer (L : Set G) := D.sylowM.le.trans hML
  have hS : IsSylowOf 2 (D.T ⊓ L) L := D.sylowM.inf_of_le_normalizer hLM hML
  obtain ⟨u, huL, huord, huN⟩ :=
    exists_mem_normalizer_of_isJ1 D.sylowM.isPGroup hTL hS hJ1
  exact ⟨u, huL, huord, Subgroup.zpowers_le.mpr huN⟩

namespace Ctx21

theorem false_of_isJ1_of_shape (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (h8107 : F08.R8107 D) (hH : H1930 D) (c : Ctx21 D Ch) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hLK : L ≠ K)
    (hLn : (L.subgroupOf D.M).Normal) (hJ1 : IsJ1 (Bar2 L))
    (hKs : (∃ n : ℕ, IsL2 (Bar2 K) n) ∨ (∃ m : ℕ, IsPowTwo m ∧ IsU3 (Bar2 K) m) ∨
      IsJ1 (Bar2 K) ∨ ∃ q : ℕ, q.Prime ∧ IsL2Odd (Bar2 K) q) : False := by
  obtain ⟨u, huL, huord, huT⟩ :=
    exists_orderOf_eq_three_le_normalizer_of_isJ1 D hL hLn hJ1
  have hL3 : CFSG.Open.pRank 3 L = 1 ∧ (F08.Thin8 L ∨ ∃ n : ℕ, IsU3 (Bar2 L) n) :=
    pRank_three_eq_one_and_thin8_or_isU3 (Or.inr (Or.inr (Or.inl hJ1)))
  have hK3 := pRank_three_eq_one_and_thin8_or_isU3 hKs
  have hU : Subgroup.zpowers u ∈ uniqueSet D.M :=
    mem_uniqueSet_of_card_eq_three D h8107 hL hK hLK hL3 hK3
      (Subgroup.zpowers_le.mpr huL) (by rw [Nat.card_zpowers, huord])
  exact uc22p218s_false_of_le_normalizer D Ch h211 hH c Nat.prime_three (by norm_num)
    huord hU huT

end Ctx21

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.Milestones.ASVolI.C61.HypSL2
public import CFSG.Milestones.ASVolI.C61.HypSmall

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.Quasithin.S152N
open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

theorem burnsideC56_pCoreOf_subgroupOf_self (H : Subgroup G) :
    (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H :=
  A4.subgroupOf_map_subtype' H (CFSG.pCore 2 ↥H)

theorem burnsideC56_ker_oTwoUpper {H : Subgroup G} {Y : Type} [Group Y]
    (φ : ↥(oTwoUpper H) →* Y) (hker : φ.ker = (pCoreOf 2 H).subgroupOf (oTwoUpper H)) :
    φ.ker = CFSG.pCore 2 ↥(oTwoUpper H) := by
  rw [hker]
  exact burnsideC56_subgroupOf_eq_pCore (burnsideC56_pCoreOf_oTwoUpper H)

theorem burnsideC56_hypI_minParabolic {H T : Subgroup G} (hc : CharTwo H)
    (hi : burnsideC56_HypI H) (hT : IsSylowTwoOf T H) :
    CFSG.QuasithinUnique.IsMinimalParabolic T H := by
  rcases hi with ⟨n, -, Y, _, φ, hφ, hker, hY⟩ | ⟨Y, _, ψ, hψ, hker, ⟨e⟩⟩ |
      ⟨Y, _, ψ, hψ, hker, ⟨e⟩⟩
  · exact burnsideC56_minParabolic_of_quot hT (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
      (burnsideC56_sup_eq hT) φ hφ (burnsideC56_ker_oTwoUpper φ hker)
      (burnsideC56_isPSL_umax hY) (burnsideC56_isPSL_card hY).2
  · have : Finite Y := Finite.of_equiv _ e.toEquiv.symm
    have hY6 : Nat.card Y = 6 := by
      rw [Nat.card_congr e.toEquiv, burnsideC56_card_perm_three]
    exact burnsideC56_minParabolic_of_quot hT le_rfl Subgroup.le_normalizer
      (sup_eq_left.mpr hT.1) ψ hψ (by rw [hker, burnsideC56_pCoreOf_subgroupOf_self])
      (burnsideC56_umax_of_card_six hY6) (by rw [hY6]; norm_num)
  · have hY72 : Nat.card Y = 72 := by
      rw [Nat.card_congr e.toEquiv]
      exact W3.card_eq
    exact burnsideC56_minParabolic_of_quot hT le_rfl Subgroup.le_normalizer
      (sup_eq_left.mpr hT.1) ψ hψ (by rw [hker, burnsideC56_pCoreOf_subgroupOf_self])
      (burnsideC56_umax_of_mulEquiv e burnsideC56_W3_umax) (by rw [hY72]; norm_num)

theorem burnsideC56_hypI_uniqueMax {H T : Subgroup G} (hc : CharTwo H)
    (hi : burnsideC56_HypI H) (hT : IsSylowTwoOf T H) :
    ∃ N : Subgroup G, CFSG.Quasithin.IsUniqueMaxOver H T N := by
  rcases hi with ⟨n, -, Y, _, φ, hφ, hker, hY⟩ | ⟨Y, _, ψ, hψ, hker, ⟨e⟩⟩ |
      ⟨Y, _, ψ, hψ, hker, ⟨e⟩⟩
  · exact burnsideC56_uniqueMax_of_quot hT (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
      (burnsideC56_sup_eq hT) φ hφ (burnsideC56_ker_oTwoUpper φ hker)
      (burnsideC56_isPSL_umax hY)
  · have : Finite Y := Finite.of_equiv _ e.toEquiv.symm
    have hY6 : Nat.card Y = 6 := by
      rw [Nat.card_congr e.toEquiv, burnsideC56_card_perm_three]
    exact burnsideC56_uniqueMax_of_quot hT le_rfl Subgroup.le_normalizer
      (sup_eq_left.mpr hT.1) ψ hψ (by rw [hker, burnsideC56_pCoreOf_subgroupOf_self])
      (burnsideC56_umax_of_card_six hY6)
  · exact burnsideC56_uniqueMax_of_quot hT le_rfl Subgroup.le_normalizer
      (sup_eq_left.mpr hT.1) ψ hψ (by rw [hker, burnsideC56_pCoreOf_subgroupOf_self])
      (burnsideC56_umax_of_mulEquiv e burnsideC56_W3_umax)

theorem burnsideC56_sqtk_of_quot_solvable {H : Subgroup G} {Y : Type} [Group Y] [Finite Y]
    (ψ : ↥H →* Y) (hψ : Function.Surjective ψ) (hker : ψ.ker = (pCoreOf 2 H).subgroupOf H)
    (hYs : Group.IsSolvable Y) (hY : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 3 ∣ Nat.card Y) :
    IsSQTKIn H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : IsPGroup 2 ↥ψ.ker := by
    rw [hker]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_of_injective H.subtype
      H.subtype_injective
  obtain ⟨k, hk⟩ := hO.exists_card_eq
  have hcard : Nat.card ψ.ker * Nat.card Y = Nat.card ↥H :=
    Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψ
  refine ⟨stronglyQuasithin_of_rankLeTwo fun p hp hp2 E hE => card_le_of_cube_free hp ?_ hE,
    isKGroupCat_of_ker ψ (isKGroupCat_of_pGroup hO) (isKGroupCat_of_solvable hYs)⟩
  rw [← hcard, hk]
  intro hd
  have hcop : Nat.Coprime (p ^ 3) (2 ^ k) :=
    Nat.Coprime.pow 3 k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact hY p hp hp2 (hcop.dvd_of_dvd_mul_left hd)

theorem burnsideC56_sqtk_of_psl {H : Subgroup G} {n : ℕ} {Y : Type}
    [Group Y] (φ : ↥(oTwoUpper H) →* Y) (hφ : Function.Surjective φ)
    (hker : φ.ker = (pCoreOf 2 H).subgroupOf (oTwoUpper H)) (hY : IsPSL 2 2 n Y) :
    IsSQTKIn H := by
  have hLH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hnorm : ((oTwoUpper H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 (le_normalizer_oTwoUpper H)
  have : (Subgroup.inclusion hLH).range.Normal := by
    rw [Subgroup.inclusion_range]
    exact hnorm
  have hq : IsPGroup 2 (↥H ⧸ (Subgroup.inclusion hLH).range) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨⟨(x : G) ^ 2 ^ k, hk⟩, Subtype.ext (by simp)⟩
  have hO : IsPGroup 2 ↥φ.ker := by
    rw [hker]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_of_injective
      (oTwoUpper H).subtype (oTwoUpper H).subtype_injective
  let eY : (↥(oTwoUpper H) ⧸ φ.ker) ≃* Y := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hR : RankLeTwo (↥(oTwoUpper H) ⧸ φ.ker) :=
    rankLeTwo_of_mulEquiv eY (burnsideC56_isPSL_rankLeTwo hY)
  have hK : IsKGroupCat (↥(oTwoUpper H) ⧸ φ.ker) :=
    IsKGroupCat.of_mulEquiv (burnsideC56_isPSL_isKGroupCat hY) eY
  exact ⟨stronglyQuasithin_of_rankLeTwo (rankLeTwo_of_hom (Subgroup.inclusion hLH)
      (Subgroup.inclusion_injective hLH) hq φ.ker hO hR),
    isKGroupCat_of_ext (Subgroup.inclusion hLH) (Subgroup.inclusion_injective hLH) hq φ.ker hO hK⟩

theorem burnsideC56_hypI_sqtk {H : Subgroup G} (hc : CharTwo H)
    (hi : burnsideC56_HypI H) : IsSQTKIn H := by
  rcases hi with ⟨n, -, Y, _, φ, hφ, hker, hY⟩ | ⟨Y, _, ψ, hψ, hker, ⟨e⟩⟩ |
      ⟨Y, _, ψ, hψ, hker, ⟨e⟩⟩
  · exact burnsideC56_sqtk_of_psl φ hφ hker hY
  · have : Finite Y := Finite.of_equiv _ e.toEquiv.symm
    have hY6 : Nat.card Y = 6 := by
      rw [Nat.card_congr e.toEquiv, burnsideC56_card_perm_three]
    refine burnsideC56_sqtk_of_quot_solvable ψ hψ hker ?_ fun p hp hp2 =>
      burnsideC56_not_cube_dvd_of_dvd_72 (by rw [hY6]; norm_num) hp hp2
    have := burnsideC56_perm_three_isSolvable
    exact CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_mulEquiv_lifted e
  · have : Finite Y := Finite.of_equiv _ e.toEquiv.symm
    have hY72 : Nat.card Y = 72 := by
      rw [Nat.card_congr e.toEquiv]
      exact W3.card_eq
    refine burnsideC56_sqtk_of_quot_solvable ψ hψ hker ?_ fun p hp hp2 =>
      burnsideC56_not_cube_dvd_of_dvd_72 (by rw [hY72]) hp hp2
    have := burnsideC56_W3_isSolvable
    exact CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_mulEquiv_lifted e

end CFSG.ASVolI

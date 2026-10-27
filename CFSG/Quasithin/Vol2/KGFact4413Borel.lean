module

public import CFSG.Quasithin.Vol2.KGFact4413Lie
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftLie
public import CFSG.Quasithin.H13.KGFact22TorusFacts
public import CFSG.Quasithin.Background.E6TorusCover

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin


namespace KG4413

theorem minParabolic_of_cComp {G : Type} [Group G] [Finite G] {H S MH K : Subgroup G}
    (hS : IsSylowTwoOf S H) (hU : IsUniqueMaxOver H S MH) (hK : K ∈ cComp H) :
    MinParabolic H S MH := by
  refine ⟨hS, fun hN => ?_, hU⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMmax, -, huniq⟩ := isUniqueMaxOver_iff.mp hU
  obtain ⟨g, hgH, hgM⟩ := IsConcreteLE.exists_of_lt hMmax.1
  have hHg : H ≤ Subgroup.zpowers g ⊔ S := by
    by_contra hne
    have hlt : Subgroup.zpowers g ⊔ S < H :=
      lt_of_le_of_ne (sup_le (Subgroup.zpowers_le.mpr hgH) hS.1) (fun h => hne h.ge)
    obtain ⟨N, hNmax, hle⟩ := exists_isMaxSubgroupIn hlt
    have hNM := huniq N hNmax (le_sup_right.trans hle)
    exact hgM (hNM ▸ hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers g)))
  set N : Subgroup H := S.subgroupOf H with hNdef
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hS.1).mpr hN
  have hNs : Group.IsSolvable N := by
    have h2 : IsPGroup 2 N := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    have := h2.isNilpotent
    infer_instance
  set g₀ : H := ⟨g, hgH⟩ with hg₀
  have hgen : ∀ x : H, ∃ k : ℤ, (QuotientGroup.mk' N x : H ⧸ N) = QuotientGroup.mk' N g₀ ^ k := by
    intro x
    have hx : (x : G) ∈ ((Subgroup.zpowers g ⊔ S : Subgroup G) : Set G) := hHg x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((Subgroup.zpowers_le.mpr hgH).trans hN)] at hx
    obtain ⟨_, ⟨k, rfl⟩, s, hs, hxs⟩ := hx
    refine ⟨k, ?_⟩
    have hsN : (⟨s, hS.1 hs⟩ : H) ∈ N := hs
    have hs1 : QuotientGroup.mk' N ⟨s, hS.1 hs⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hsN
    have hxe : x = g₀ ^ k * ⟨s, hS.1 hs⟩ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_zpow]
      exact hxs.symm)
    rw [hxe, map_mul, map_zpow, hs1, mul_one]
  have hQs : Group.IsSolvable (H ⧸ N) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    obtain ⟨k, hk⟩ := hgen x
    obtain ⟨l, hl⟩ := hgen y
    rw [hk, hl, ← zpow_add, ← zpow_add, add_comm]
  have hHs : Group.IsSolvable H :=
    Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', N.range_subtype])
  exact not_isSolvable_of_mem_cComp hK
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (le_of_mem_cComp hK)))

end KG4413

namespace Ch4

theorem e22BorelFactsLie_holds : E22BorelFactsLie := by
  intro G _ _ H S MH _ _ _ _ hL hS hU
  obtain ⟨K, hKc, hHK, hLc⟩ := hL
  have hmin : MinParabolic H S MH := KG4413.minParabolic_of_cComp hS hU hKc
  obtain ⟨n, -, -, R, hRS, hR2, hMR, ⟨C₀, hC₀M, hC₀odd, k₀, hk₀⟩, hall⟩ :=
    E2.e22BorelLift_lie (E2.e22TorusCover_of_facts e22TorusFacts_holds) hmin hKc hHK hLc
  refine ⟨?_, fun B hBM hBo hBi => (hall B hBM hBo hBi).2.2.1⟩
  obtain ⟨-, hX, -⟩ := hall C₀ hC₀M hC₀odd ⟨k₀, hk₀⟩
  have hSM : S ≤ MH := (isUniqueMaxOver_iff.mp hU).2.1
  have hMH : MH ≤ H := (isUniqueMaxOver_iff.mp hU).1.le
  set X := MH ⊓ oTwoUpper H with hXdef
  have hRM : R ≤ MH := hRS.trans hSM
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := inf_le_left.trans hMR
  have hC₀R : C₀ ≤ Subgroup.normalizer (R : Set G) := hC₀M.trans hMR
  have hodd : Odd (R.relIndex X) := by
    have h1 : R.relIndex (X ⊔ R) = R.relIndex X := A4.relIndex_sup_eq_of_le_normalizer' hXR
    have h2 : R.relIndex (C₀ ⊔ R) = R.relIndex C₀ := A4.relIndex_sup_eq_of_le_normalizer' hC₀R
    have h3 : R.relIndex (X ⊔ R) ∣ R.relIndex (C₀ ⊔ R) :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex R (X ⊔ R) (C₀ ⊔ R) le_sup_right
        (sup_le hX le_sup_right))
    rw [h1, h2] at h3
    exact (hC₀odd.of_dvd_nat (Subgroup.relIndex_dvd_card R C₀)).of_dvd_nat h3
  have he : (R ⊓ oTwoUpper H).relIndex X = R.relIndex X := by
    have h1 : R ⊓ oTwoUpper H ⊓ X = R ⊓ X := by
      rw [inf_assoc, inf_eq_right.mpr (inf_le_right : X ≤ oTwoUpper H)]
    rw [← Subgroup.inf_relIndex_right, h1, Subgroup.inf_relIndex_right]
  refine ⟨R ⊓ oTwoUpper H, ⟨le_inf (inf_le_left.trans hRM) inf_le_right,
    hR2.to_le inf_le_left, ?_⟩, ?_⟩
  · show ¬ 2 ∣ (R ⊓ oTwoUpper H).relIndex X
    rw [he]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  · intro x hx
    have h1 := hXR hx
    have h2 := le_normalizer_oTwoUpper H (hMH hx.1)
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 y, h2 y]

end Ch4

end CFSG.Quasithin.H13

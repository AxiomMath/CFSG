module

public import CFSG.Quasithin.Background.F918G1
public import CFSG.Quasithin.Background.F918G2
public import CFSG.Quasithin.Background.F918G3
public import CFSG.Quasithin.EmptyFaithful.S153D54
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

private theorem input21_not_three_dvd_card {N : Type*} [Group N] [Finite N]
    (hN : IsPGroup 2 N) : ¬ 3 ∣ Nat.card N := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hN
  rw [hn]
  intro h
  have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

private theorem input21_pRank_top_eq_of_ker {H B : Type*} [Group H] [Finite H] [Group B] [Finite B]
    (ρ : H →* B) (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker) :
    CFSG.Open.pRank 3 (⊤ : Subgroup B) = CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
  rw [← CFSG.SectionRank.pRank_quotient_eq (p := 3) ρ.ker (input21_not_three_dvd_card hk)]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)).symm

private theorem input21_pRank_le_pRank_map {H B : Type*} [Group H] [Finite H] [Group B] [Finite B]
    (ρ : H →* B) (hk : IsPGroup 2 ρ.ker) (Y : Subgroup H) :
    CFSG.Open.pRank 3 Y ≤ CFSG.Open.pRank 3 (Y.map ρ) := by
  have hp1 : 1 < 3 := by norm_num
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 Y
  have hcop : Nat.Coprime (3 ^ CFSG.Open.pRank 3 Y) (Nat.card ρ.ker) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (input21_not_three_dvd_card hk))
  have hdisj : Disjoint E ρ.ker :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hcard]; exact hcop)
  have hinj : Function.Injective (ρ.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
    have h1 : (s : H) ∈ E ⊓ ρ.ker := ⟨s.2, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  have := hE.1
  refine CFSG.SectionRank.le_pRank_of_injective hp1 (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hE.2 _ a.2)) hcard _ hinj ?_
  rintro _ ⟨e, rfl⟩
  exact ⟨(e : H), hEY e.2, rfl⟩

private theorem input21_pRank_eq_of_surjective {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {B : Type} [Group B] [Finite B] (ρ : ↥L →* B) (hρ : Function.Surjective ρ)
    (hk : ρ.ker = CFSG.pCore 2 ↥L) :
    CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup B) := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
  refine (input21_pRank_top_eq_of_ker ρ hρ ?_).symm
  rw [hk]
  exact CFSG.pCore_isPGroup

private theorem input21_pRank_le_one_of_surjective {G : Type} [Group G] [Finite G]
    {L S₀ X : Subgroup G} {B : Type} [Group B] [Finite B] (ρ : ↥L →* B)
    (hρ : Function.Surjective ρ) (hk : ρ.ker = CFSG.pCore 2 ↥L) (hS₀ : IsSylowTwoOf S₀ L)
    (hS₀X : S₀ ≤ X) (hXL : X ≤ L) (hXne : X ≠ L)
    (hB : ∀ {S Y : Subgroup B}, IsSylowTwoOf S ⊤ → S ≤ Y → Y ≠ ⊤ → CFSG.Open.pRank 3 Y ≤ 1) :
    CFSG.Open.pRank 3 X ≤ 1 := by
  have hker2 : IsPGroup 2 ρ.ker := by
    rw [hk]
    exact CFSG.pCore_isPGroup
  have hS₀' : IsPGroup 2 (S₀.subgroupOf L) :=
    hS₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀.1).symm
  have hkS : ρ.ker ≤ S₀.subgroupOf L := by
    rw [hk]
    exact IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup (hS₀'.toSylow hS₀.2.2)
  have hS₀X' : S₀.subgroupOf L ≤ X.subgroupOf L :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hS₀X (Subgroup.mem_subgroupOf.1 hx))
  have hproper : (X.subgroupOf L).map ρ ≠ ⊤ := by
    intro htop
    apply hXne
    have h1 : ((X.subgroupOf L).map ρ).comap ρ = X.subgroupOf L ⊔ ρ.ker :=
      Subgroup.comap_map_eq _ _
    rw [htop, Subgroup.comap_top, sup_eq_left.2 (hkS.trans hS₀X')] at h1
    exact le_antisymm hXL (Subgroup.subgroupOf_eq_top.1 h1.symm)
  have hsyl : IsSylowTwoOf ((S₀.subgroupOf L).map ρ) (⊤ : Subgroup B) := by
    have h := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hS₀ ρ
    rwa [MonoidHom.range_eq_top.2 hρ] at h
  have hrank : CFSG.Open.pRank 3 X = CFSG.Open.pRank 3 (X.subgroupOf L) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X,
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (X.subgroupOf L)]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (Subgroup.subgroupOfEquivOfLe hXL).symm
  calc CFSG.Open.pRank 3 X = CFSG.Open.pRank 3 (X.subgroupOf L) := hrank
    _ ≤ CFSG.Open.pRank 3 ((X.subgroupOf L).map ρ) := input21_pRank_le_pRank_map ρ hker2 _
    _ ≤ 1 := hB hsyl (Subgroup.map_mono hS₀X') hproper

theorem input21Rank_of : Input21Rank := by
  intro G _ _ L h
  rcases h with ⟨-, α, hα, hk, -⟩ | ⟨-, hG2, -⟩ | ⟨-, hHat, -⟩ | ⟨-, α, hα, hk, -⟩ |
    ⟨-, ⟨α, hα, hk⟩, -⟩
  · exact (input21_pRank_eq_of_surjective α hα hk).trans (pRank_three_alt_six_seven (Or.inl rfl))
  · exact (input21_pRank_eq_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).trans (pRank_three_psu33 hG2)
  · exact (input21_pRank_eq_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).trans (pRank_three_hatA6 hHat)
  · exact (input21_pRank_eq_of_surjective α hα hk).trans (pRank_three_alt_six_seven (Or.inr rfl))
  · exact (input21_pRank_eq_of_surjective α hα hk).trans (pRank_three_alt_six_seven (Or.inr rfl))

theorem input21ProperRank_of :
    Input21ProperRank := by
  intro G _ _ L S₀ X hblock hS₀ hS₀X hXL hXne
  rcases hblock with ⟨-, α, hα, hk, -⟩ | ⟨-, hG2, -⟩
  · exact input21_pRank_le_one_of_surjective α hα hk hS₀ hS₀X hXL hXne
      (fun hS hSY hY => pRank_three_overgroup_alt6 hS hSY hY)
  · exact input21_pRank_le_one_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hS₀ hS₀X hXL hXne
      (fun hS hSY hY => pRank_three_overgroup_psu33 hG2 hS hSY hY)

end CFSG.Quasithin

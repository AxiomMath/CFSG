module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204QImg
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.Quasithin.N204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem isQuasithinSub_twoQuot (hQ : IsQuasithinSub N) :
    IsQuasithinSub (⊤ : Subgroup (TwoQuot N)) := by
  intro p hp hp2 R _ hR0 hR2
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 ↥(twoProj N).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  set R₀ : Subgroup ↥N := R.comap (twoProj N) with hR₀
  have hR₀2 : IsPGroup 2 ↥R₀ := IsPGroup.comap_of_ker_isPGroup hR2 (twoProj N) hker
  have hR₀0 : R₀ ≠ ⊥ := by
    intro h
    apply hR0
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) R, ← hR₀, h,
      Subgroup.map_bot]
  set R' : Subgroup G := R₀.map N.subtype with hR'
  have hR'0 : R' ≠ ⊥ := fun h => hR₀0
    (Subgroup.map_injective N.subtype_injective (h.trans (Subgroup.map_bot _).symm))
  have hrank := hQ p hp hp2 R' (Subgroup.map_subtype_le _) hR'0 (hR₀2.map N.subtype)
  obtain ⟨Ê, hÊle, hÊab, hÊcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    ((⊤ : Subgroup (TwoQuot N)) ⊓ Subgroup.normalizer (R : Set (TwoQuot N)))
  have hcop : ¬ p ∣ Nat.card ↥(CFSG.Open.pCore 2 ↥N) := by
    obtain ⟨a, ha⟩ :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥N)).exists_card_eq
    rw [ha]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  obtain ⟨E₀, hE₀le, hE₀ab, hE₀card⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift
    (CFSG.Open.pCore 2 ↥N) hcop hÊab
  have hE₀R : E₀ ≤ Subgroup.normalizer (R₀ : Set ↥N) := fun e he => by
    have : e ∈ (Subgroup.normalizer (R : Set (TwoQuot N))).comap (twoProj N) :=
      (hÊle (hE₀le he)).2
    rwa [Subgroup.comap_normalizer_eq_of_surjective R (QuotientGroup.mk'_surjective _)] at this
  have hEle : E₀.map N.subtype ≤ N ⊓ Subgroup.normalizer (R' : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e.2, Subgroup.le_normalizer_map N.subtype ⟨e, hE₀R he, rfl⟩⟩
  have hEcard : Nat.card ↥(E₀.map N.subtype) = p ^ CFSG.Open.pRank p
      ((⊤ : Subgroup (TwoQuot N)) ⊓ Subgroup.normalizer (R : Set (TwoQuot N))) := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, hE₀card, hÊcard]
  exact (CFSG.SectionRank.le_pRank hp.one_lt hEle
    (CFSG.SectionRank.isElemAbelian_map hE₀ab N.subtype) hEcard).trans hrank

end CFSG.Quasithin.N204

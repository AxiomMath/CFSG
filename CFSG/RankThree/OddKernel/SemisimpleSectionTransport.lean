module

public import CFSG.RankThree.OddKernel.PerfectCentralQuotient
public import CFSG.RankThree.OddKernel.RankTwoActionsVanish
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open scoped commutatorElement Pointwise

universe u

section Semisimple

variable {p : ℕ}

theorem isPGroup_quotient_pPrimeCore_of_isNilpotent [Fact p.Prime] {C : Type*} [Group C]
    [Finite C] [Group.IsNilpotent C] : IsPGroup p (C ⧸ CFSG.pPrimeCore p C) := by
  have hpos : Nat.card (C ⧸ CFSG.pPrimeCore p C) ≠ 0 := Nat.card_pos.ne'
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {q} hq hqdvd => ?_)
  by_contra hqp
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨T⟩ : Nonempty (Sylow q C) := inferInstance
  have hTcop : Nat.Coprime p (Nat.card (T : Subgroup C)) := by
    obtain ⟨m, hm⟩ := T.isPGroup'.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.coprime_primes Fact.out hq).2 (Ne.symm hqp))
  have hTle : (T : Subgroup C) ≤ CFSG.pPrimeCore p C := le_sSup ⟨inferInstance, hTcop⟩
  have hT₀ : ((T.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pPrimeCore p C)) :
      Sylow q (C ⧸ CFSG.pPrimeCore p C)) : Subgroup (C ⧸ CFSG.pPrimeCore p C)) = ⊥ := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hTle
  have hcard := Sylow.card_eq_multiplicity
    (T.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pPrimeCore p C)))
  rw [hT₀, card_bot] at hcard
  have hpos' := hq.factorization_pos_of_dvd hpos hqdvd
  have : q ^ (Nat.card (C ⧸ CFSG.pPrimeCore p C)).factorization q ≠ 1 :=
    (Nat.one_lt_pow hpos'.ne' hq.one_lt).ne'
  exact this hcard.symm

theorem pRank_le_two_of_cover (hp : p.Prime) (hp3 : 3 < p) {X S : Type*} [Group X] [Group S]
    [Finite X] [Group.IsPerfect X] (hrank : pRank p X ≤ 2) (π : X →* S)
    (hπ : Function.Surjective π) (D : Subgroup X) [D.Normal]
    (hDC : D ≤ (center S).comap π) (hDcop : ¬ p ∣ Nat.card D)
    (hCD : ∀ c ∈ (center S).comap π, ∃ n : ℕ, c ^ p ^ n ∈ D)
    (hZXC : center (X ⧸ (center S).comap π) = ⊥)
    (hLXC : CFSG.layer (X ⧸ (center S).comap π) = ⊤) : pRank p S ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite S := Finite.of_surjective π hπ
  have hCn : ((center S).comap π).Normal := inferInstance
  have hPn : (((center S).comap π).map (QuotientGroup.mk' D)).Normal :=
    hCn.map _ (QuotientGroup.mk'_surjective D)
  have hPp : IsPGroup p (((center S).comap π).map (QuotientGroup.mk' D)) := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc, rfl⟩ := mem_map.1 hy
    obtain ⟨n, hn⟩ := hCD c hc
    refine ⟨n, Subtype.ext ?_⟩
    change (QuotientGroup.mk' D c) ^ p ^ n = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hn
  have e2 : (X ⧸ D) ⧸ ((center S).comap π).map (QuotientGroup.mk' D) ≃*
      X ⧸ (center S).comap π := QuotientGroup.quotientQuotientEquivQuotient D _ hDC
  have hE : CFSG.layer ((X ⧸ D) ⧸ ((center S).comap π).map (QuotientGroup.mk' D)) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hLXC e2.symm.toMonoidHom e2.symm.surjective
  have hZ : center ((X ⧸ D) ⧸ ((center S).comap π).map (QuotientGroup.mk' D)) = ⊥ := by
    rw [← map_center_eq e2.symm, hZXC, Subgroup.map_bot]
  have hYrank : pRank p (X ⧸ D) ≤ 2 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp D hDcop]
    exact hrank
  have hPrank : pRank p (((center S).comap π).map (QuotientGroup.mk' D)) ≤ 2 := by
    refine le_trans ?_ hYrank
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.one_lt _ (subtype_injective _)
  have hPZ := le_center_of_centerless_semisimple_prime_quotient hp hp2 _ hPp hE hZ _ hPp hPrank
  have hZ₀ : D.map π ≤ center S := map_le_iff_le_comap.2 hDC
  have hZ₀n : (D.map π).Normal := normal_of_le_center hZ₀
  have hfD : D ≤ ((QuotientGroup.mk' (D.map π)).comp π).ker := fun d hd => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact mem_map_of_mem π hd
  let f : X ⧸ D →* S ⧸ D.map π := QuotientGroup.lift D ((QuotientGroup.mk' (D.map π)).comp π) hfD
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (D.map π) z
    obtain ⟨x, rfl⟩ := hπ s
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hfker : f.ker ≤ center (X ⧸ D) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D y
    apply hPZ
    have h1 : QuotientGroup.mk' (D.map π) (π x) = 1 := hy
    exact mem_map_of_mem _ (hZ₀ ((QuotientGroup.eq_one_iff _).1 h1))
  have hquot := perfect_rank_two_large_prime_quotient_pRank_le_two hp hp3 hYrank f.ker hfker
  have e3 := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hS0 : pRank p (S ⧸ D.map π) ≤ 2 := by
    rw [pRank_eq_open_pRank_top, ← pRank_top_eq_of_mulEquiv hp.one_lt e3,
      ← pRank_eq_open_pRank_top]
    exact hquot
  have hZ₀cop : ¬ p ∣ Nat.card (D.map π) := fun h => hDcop (h.trans (card_map_dvd D π))
  rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp (D.map π) hZ₀cop]
  exact hS0

theorem pRank_le_two_of_surjective_semisimple (hp : p.Prime) (hp3 : 3 < p) {H₀ S : Type*}
    [Group H₀] [Group S] [Finite H₀] (hrank : pRank p H₀ ≤ 2) (hS : CFSG.layer S = ⊤)
    (ρ : H₀ →* S) (hρ : Function.Surjective ρ) : pRank p S ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite S := Finite.of_surjective ρ hρ
  obtain ⟨X, -, hXmin⟩ := Finite.exists_le_minimal (p := fun X : Subgroup H₀ => X.map ρ = ⊤)
    (show (⊤ : Subgroup H₀).map ρ = ⊤ from map_top_of_surjective ρ hρ)
  have hXS : X.map ρ = ⊤ := hXmin.prop
  have hπ : Function.Surjective (ρ.comp X.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype, hXS]
  have hmin : ∀ Y : Subgroup X, Y ≠ ⊤ → Y.map (ρ.comp X.subtype) ≠ ⊤ := by
    intro Y hY hYS
    apply hY
    have hle : Y.map X.subtype ≤ X := map_subtype_le Y
    have hYS' : (Y.map X.subtype).map ρ = ⊤ := by rw [map_map]; exact hYS
    have heq : Y.map X.subtype = X := le_antisymm hle (hXmin.2 hYS' hle)
    refine eq_top_iff.2 fun x _ => ?_
    have hx : (x : H₀) ∈ Y.map X.subtype := by rw [heq]; exact x.2
    obtain ⟨y, hy, hyx⟩ := mem_map.1 hx
    rwa [← Subtype.ext hyx]
  have hcover := CFSG.SectionRank.minimal_semisimple_cover hS (ρ.comp X.subtype) hπ hmin
  obtain ⟨hXp, -, hCnil, -, -, -, -, hZXC, hLXC⟩ := hcover
  have : Group.IsNilpotent ((center S).comap (ρ.comp X.subtype)) := hCnil
  have hKp := isPGroup_quotient_pPrimeCore_of_isNilpotent (p := p)
    (C := (center S).comap (ρ.comp X.subtype))
  have hDn : ((CFSG.pPrimeCore p ((center S).comap (ρ.comp X.subtype))).map
      ((center S).comap (ρ.comp X.subtype)).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hXrank : pRank p X ≤ 2 := by
    refine le_trans ?_ hrank
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.one_lt X.subtype X.subtype_injective
  refine pRank_le_two_of_cover hp hp3 hXrank (ρ.comp X.subtype) hπ
    ((CFSG.pPrimeCore p ((center S).comap (ρ.comp X.subtype))).map
      ((center S).comap (ρ.comp X.subtype)).subtype) (map_subtype_le _) ?_
    (fun c hc => ?_) hZXC hLXC
  · rw [card_map_of_injective (subtype_injective _)]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  · obtain ⟨n, hn⟩ := hKp (QuotientGroup.mk ⟨c, hc⟩)
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn
    exact mem_map_of_mem _ hn

theorem large_prime_rank_two_semisimple_section_transport (hp : p.Prime) (hp3 : 3 < p)
    {G : Type u} [Group G] [Finite G] (hrank : pRank p G ≤ 2) (H : Subgroup G)
    (N : Subgroup H) [N.Normal] (hS : CFSG.layer (H ⧸ N) = ⊤) : pRank p (H ⧸ N) ≤ 2 := by
  have hH : pRank p H ≤ 2 := by
    refine le_trans ?_ hrank
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.one_lt H.subtype H.subtype_injective
  exact pRank_le_two_of_surjective_semisimple hp hp3 hH hS (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)

end Semisimple

end CFSG.RankThree.OddKernel

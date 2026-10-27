module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_not_dvd_card_center_bar2 {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (h1 : CFSG.Open.pRank 3 K ≤ 1) : ¬ 3 ∣ Nat.card (center (Bar2 K)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKcyc : ∀ P : Sylow 3 ↥K, IsCyclic (P : Subgroup ↥K) := by
    intro P
    by_contra hnc
    have hPmap : IsPGroup 3 ((P : Subgroup ↥K).map K.subtype) := P.isPGroup'.map K.subtype
    have hnc' : ¬ IsCyclic ↥((P : Subgroup ↥K).map K.subtype) := by
      intro hc
      refine hnc (isCyclic_of_surjective
        ((P : Subgroup ↥K).equivMapOfInjective K.subtype K.subtype_injective).symm
        ((P : Subgroup ↥K).equivMapOfInjective K.subtype K.subtype_injective).symm.surjective)
    obtain ⟨E₉, hE₉le, hE₉ea, hE₉card⟩ :=
      uc22p22u_exists_elemAbelian_sq Nat.prime_three (by norm_num) hPmap hnc'
    have hleK : E₉ ≤ K := hE₉le.trans (Subgroup.map_subtype_le (P : Subgroup ↥K))
    have h2 : 2 ≤ CFSG.Open.pRank 3 K :=
      CFSG.SectionRank.le_pRank (by norm_num) hleK hE₉ea hE₉card
    omega
  let Z : Subgroup (Bar2 K) := Subgroup.center (Bar2 K)
  let J := Bar2 K ⧸ Z
  let π : Bar2 K →* J := QuotientGroup.mk' Z
  let f₀ : ↥K →* J := π.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hf₀s : Function.Surjective f₀ :=
    (QuotientGroup.mk'_surjective Z).comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
  have hcycJ : ∀ Q : Sylow 3 J, IsCyclic (Q : Subgroup J) := by
    intro Q
    obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf₀s 3 Q
    have hQmap : (Q : Subgroup J) = (P : Subgroup ↥K).map f₀ := by
      rw [← hP, Sylow.coe_mapSurjective hf₀s P]
    rw [hQmap]
    haveI : IsCyclic ↥(P : Subgroup ↥K) := hKcyc P
    exact isCyclic_of_surjective (f₀.subgroupMap (P : Subgroup ↥K))
      (f₀.subgroupMap_surjective (P : Subgroup ↥K))
  have hperf : Group.IsPerfect (Bar2 K) := Group.isPerfect_def.2 hq.1
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Subgroup.center (Bar2 K) := QuotientGroup.ker_mk' Z
  have hcentral : π.ker ≤ Subgroup.center (Bar2 K) := hker.le
  obtain ⟨C⟩ : Nonempty (Sylow 3 π.ker) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow 3 J) := inferInstance
  have hCb : (C : Subgroup π.ker) = ⊥ :=
    CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπs hcentral C Q
      (hcycJ Q)
  have hCcard : Nat.card C = 1 := by
    rw [hCb]
    simp
  have hval : Nat.factorization (Nat.card π.ker) 3 = 0 := by
    have hpow : 3 ^ Nat.factorization (Nat.card π.ker) 3 = 1 := by
      rw [← Sylow.card_eq_multiplicity C, hCcard]
    by_contra hne
    have hpos : 0 < Nat.factorization (Nat.card π.ker) 3 := Nat.pos_of_ne_zero hne
    have hdvd : 3 ∣ 3 ^ Nat.factorization (Nat.card π.ker) 3 := dvd_pow_self 3 hpos.ne'
    rw [hpow] at hdvd
    exact absurd hdvd (by norm_num)
  rw [← hker]
  intro h3
  have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_three
    (Nat.card_pos (α := ↥π.ker)).ne' h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

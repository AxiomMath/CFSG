module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Defs
public import CFSG.Quasithin.EmptyFaithful.A38c15Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

open CFSG.Quasithin CFSG.Quasithin.A38c15 Subgroup

private theorem oicore_three_dvd_sq_sub_one_of_not_dvd {q : ℕ} (h : ¬ 3 ∣ q) :
    3 ∣ q ^ 2 - 1 := by
  have h0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact h (dvd_zero 3))
  have h1 : q ^ 2 % 3 = 1 := by
    have hne : q % 3 ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
    have hlt : q % 3 < 3 := Nat.mod_lt q (by norm_num)
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [Nat.pow_mod, h]
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h0
  omega

theorem conclusion_of_levi {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {N Y : Subgroup Γ} (hYN : Y ≤ N) (hY : IsPerfA5Cover ↥Y)
    (hN : CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥N)
    (hlevi : IsLeviBlock p ↥(perfectCore N)) : p = 5 ∧ IsSL2Prime ↥Y 5 := by
  classical
  obtain ⟨hYperf, Z, hZn, hZ2, hYalt⟩ := hY
  obtain ⟨e⟩ := hYalt
  haveI := hZn
  have hcomm : ⁅Y, Y⁆ = Y := by
    have h := Subgroup.map_subtype_commutator Y
    rw [hYperf] at h
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  let C := perfectCore N
  have hYC : Y ≤ C := le_perfectCore_of_perfect hYN hcomm
  have hCN : C ≤ N := perfectCore_le N
  have hC : CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥C :=
    CFSG.KCore.KGroupNonab.of_injective (isoInvariant_dvdOrThreeFree 51840) hN
      (Subgroup.inclusion hCN) (Subgroup.inclusion_injective hCN)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, -⟩ := exists_hom_psl2_of_leviBlock hlevi
  have hCP : CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    CFSG.KCore.KGroupNonab.of_surjective (isoInvariant_dvdOrThreeFree 51840) hC g hg
  have h4p : 4 ≤ Nat.card (ZMod p) := by
    rw [Nat.card_zmod]
    have := hp.two_le
    omega
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4p
  have hnonab : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p), a * b ≠ b * a :=
    CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
      (ZMod p) (by rw [Nat.card_zmod]; exact hp2) (by rw [Nat.card_zmod]; exact hp3)
  have hcat := CFSG.KCore.KGroupNonab.catalogue_self (isoInvariant_dvdOrThreeFree 51840) hCP
    hnonab
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) * 2 =
      p * (p ^ 2 - 1) := by
    have hsl := CFSG.GorensteinWalter.sl2_card_formula (ZMod p)
    rw [Nat.card_zmod] at hsl
    rw [← CFSG.RankThree.SubgroupLists.natCard_sl2_eq htwo]
    exact hsl
  have h3dvd : 3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
    have h3sq : 3 ∣ p ^ 2 - 1 :=
      oicore_three_dvd_sq_sub_one_of_not_dvd fun h => hp3
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    have h3mul : 3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) * 2 := by
      rw [hcard]
      exact dvd_mul_of_dvd_right h3sq p
    exact (Nat.Coprime.dvd_mul_right (by norm_num : Nat.Coprime 3 2)).mp h3mul
  have hpdvd : p ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
    have hpmul : p ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) * 2 := by
      rw [hcard]
      exact dvd_mul_right p (p ^ 2 - 1)
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).dvd_mul_right.mp hpmul
  have hpdvd51840 : p ∣ 51840 := by
    rcases hcat with hdvd | hnot
    · exact hpdvd.trans hdvd
    · exact absurd h3dvd hnot
  have hp_eq : p = 5 := by
    have hpd : p ∣ 2 ^ 7 * 3 ^ 4 * 5 := by
      rwa [show 51840 = 2 ^ 7 * 3 ^ 4 * 5 by norm_num] at hpdvd51840
    rcases hp.dvd_mul.mp hpd with h | h5
    · rcases hp.dvd_mul.mp h with h2 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow h2)) hp2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h3)) hp3
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5
  refine ⟨hp_eq, ?_⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [hp_eq] at hlevi
  obtain ⟨f, hf, -, hfexp⟩ := exists_hom_sl2_of_leviBlock hlevi
  let ρ : ↥Y →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    f.comp (Subgroup.inclusion hYC)
  have hfker_pg : IsPGroup 5 ↥(MonoidHom.ker f) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (hfexp x x.2)
  have hKpg : IsPGroup 5 ↥(MonoidHom.ker ρ) := by
    rw [show MonoidHom.ker ρ = (MonoidHom.ker f).comap (Subgroup.inclusion hYC) from
      MonoidHom.comap_ker f (Subgroup.inclusion hYC)]
    exact hfker_pg.comap_of_injective _ (Subgroup.inclusion_injective hYC)
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  let q := QuotientGroup.mk' Z
  let W : Subgroup (alternatingGroup (Fin 5)) :=
    ((MonoidHom.ker ρ).map q).map e.toMonoidHom
  have hWpg : IsPGroup 5 W := (hKpg.map q).map e.toMonoidHom
  have hWn : W.Normal :=
    ((MonoidHom.normal_ker ρ).map q (QuotientGroup.mk'_surjective Z)).map e.toMonoidHom
      e.surjective
  have hWbot : W = ⊥ := by
    rcases hWn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hA5pg : IsPGroup 5 (alternatingGroup (Fin 5)) :=
        (h ▸ hWpg).of_equiv (Subgroup.topEquiv)
      obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hA5pg
      have hcard60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        decide
      rw [hcard60] at hn
      have h2dvd : 2 ∣ 5 ^ n := (by norm_num : 2 ∣ 60).trans hn
      exact absurd (Nat.prime_two.dvd_of_dvd_pow h2dvd) (by norm_num)
  have hKleZ : MonoidHom.ker ρ ≤ Z := by
    have hmapq : (MonoidHom.ker ρ).map q = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (MonoidHom.ker ρ).map q) e.injective).mp
        hWbot
    have h := (Subgroup.map_eq_bot_iff (MonoidHom.ker ρ)).mp hmapq
    rwa [QuotientGroup.ker_mk'] at h
  have hKbot : MonoidHom.ker ρ = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (IsPGroup.disjoint_of_ne 5 2 (by norm_num) (MonoidHom.ker ρ) Z hKpg hZ2).eq_bot_of_le
      hKleZ
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hKbot
  have hcardY60 : 60 ∣ Nat.card ↥Y := by
    have hcardq : Nat.card (↥Y ⧸ Z) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hcardq]
    exact dvd_mul_right 60 (Nat.card Z)
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
    have h := CFSG.GorensteinWalter.sl2_card_formula (ZMod 5)
    rw [Nat.card_zmod] at h
    norm_num at h
    rw [Nat.card_eq_fintype_card]
    exact h
  have hrange_card : Nat.card ↥(ρ.range) = Nat.card ↥Y := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hρinj]
    simp
  have hrange_dvd : Nat.card ↥(ρ.range) ∣ 120 := by
    rw [← hcardSL]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hindex_eq : ρ.range.index = 1 ∨ ρ.range.index = 2 := by
    have hmul : Nat.card ↥(ρ.range) * ρ.range.index = 120 := by
      rw [Subgroup.card_mul_index, hcardSL]
    have h60 : 60 ≤ Nat.card ↥(ρ.range) := by
      rw [hrange_card]
      exact Nat.le_of_dvd Nat.card_pos hcardY60
    have hpos : 0 < ρ.range.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ρ.range))
    have hmul' : 60 * ρ.range.index ≤ 120 := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ h60
    omega
  have htop : ρ.range = ⊤ := by
    rcases hindex_eq with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hnorm : ρ.range.Normal := Subgroup.normal_of_index_eq_two h2
      haveI := hnorm
      have hcomm_le : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ≤ ρ.range := by
        apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
        have hcardquot :
            Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ⧸ ρ.range) = 2 := by
          rw [← Subgroup.index_eq_card]
          exact h2
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : IsCyclic (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ⧸ ρ.range) :=
          isCyclic_of_prime_card (p := 2) hcardquot
        exact inferInstance
      have hfour : ∃ s : Finset (ZMod 5), s.card = 4 := by
        refine ⟨(Finset.univ : Finset (ZMod 5)).erase 4, ?_⟩
        rw [Finset.card_erase_of_mem (Finset.mem_univ 4), Finset.card_univ, ZMod.card]
      haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
        CFSG.LinearGroups.special_linear_dimension_two_perfect hfour
      have htoprange : ρ.range = ⊤ := by
        have : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ≤ ρ.range := by
          rw [← Group.IsPerfect.commutator_eq_top]
          exact hcomm_le
        exact top_le_iff.mp this
      have := Subgroup.index_eq_one.mpr htoprange
      omega
  have hρsurj : Function.Surjective ρ := MonoidHom.range_eq_top.mp htop
  let eY : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  refine ⟨ZMod 5, inferInstance, inferInstance, by rw [Nat.card_zmod], ?_⟩
  exact ⟨eY.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod 5))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

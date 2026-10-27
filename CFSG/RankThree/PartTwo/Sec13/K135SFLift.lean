module

public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

section SFLiftRank

open CFSG Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Assembly.RankThreeEven

theorem pRank_fixed_quotient_le {M : Type*} [Group M] [Finite M] (N₀ : Subgroup M) [N₀.Normal]
    (h3 : ¬ 3 ∣ Nat.card N₀) (h2 : ¬ 2 ∣ Nat.card N₀) (R : Subgroup M) (hN₀R : N₀ ≤ R) (t : M)
    (ht : orderOf t = 2) (hloc : localRank 3 M ≤ 3) :
    CFSG.Open.pRank 3 (R.map (QuotientGroup.mk' N₀) ⊓
      Subgroup.centralizer {QuotientGroup.mk' N₀ t}) ≤ 3 := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hA2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hAne : Subgroup.zpowers t ≠ ⊥ := fun h => ht1 (by
    have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rwa [h, Subgroup.mem_bot] at this)
  have hloc' : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers t : Set M)) :=
    ⟨_, hAne, hA2, rfl⟩
  have hCN : Subgroup.centralizer {t} ≤ Subgroup.normalizer (Subgroup.zpowers t : Set M) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hCrank : CFSG.Open.pRank 3 (Subgroup.centralizer {t}) ≤ 3 :=
    ((CFSG.SectionRank.pRank_mono (by norm_num : (1 : ℕ) < 3) hCN).trans
      (CFSG.RankThree.Classical.pRank_le_localRank (by norm_num : (1 : ℕ) < 3) hloc')).trans hloc
  let α : Subgroup.zpowers t →* MulAut M :=
    (MulAut.conj : M →* MulAut M).comp (Subgroup.zpowers t).subtype
  have hN : ∀ a : Subgroup.zpowers t, ∀ n ∈ N₀, α a n ∈ N₀ :=
    fun a n hn => Subgroup.Normal.conj_mem (inferInstance : N₀.Normal) n hn (a : M)
  have key := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hA2 α N₀ hN h2
  have hlift : ∀ g : M, Commute (QuotientGroup.mk' N₀ t) (QuotientGroup.mk' N₀ g) →
      ∃ c : M, Commute t c ∧ (c : M ⧸ N₀) = (g : M ⧸ N₀) := by
    intro g hg
    have hzp : ∀ a : Subgroup.zpowers t,
        Commute (QuotientGroup.mk' N₀ (a : M)) (QuotientGroup.mk' N₀ g) := by
      rintro ⟨a, ha⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      show Commute (QuotientGroup.mk' N₀ (t ^ k)) _
      rw [map_zpow]
      exact Commute.zpow_left hg k
    have hmem : ((g : M) : M ⧸ N₀) ∈ {x : M ⧸ N₀ | ∀ a : Subgroup.zpowers t,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N₀ hN a x = x} := by
      rw [Set.mem_setOf_eq]
      intro a
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      have h1 : QuotientGroup.mk' N₀ ((a : M) * g * (a : M)⁻¹) = QuotientGroup.mk' N₀ g := by
        rw [map_mul, map_mul, map_inv, (hzp a).eq]
        group
      exact h1
    rw [key] at hmem
    obtain ⟨c, hc, hcg⟩ := hmem
    have hc' : ∀ a : Subgroup.zpowers t, α a c = c := hc
    refine ⟨c, ?_, hcg⟩
    have h1 : t * c * t⁻¹ = c := hc' ⟨t, Subgroup.mem_zpowers t⟩
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hsub : R.map (QuotientGroup.mk' N₀) ⊓ Subgroup.centralizer {QuotientGroup.mk' N₀ t} ≤
      (R ⊓ Subgroup.centralizer {t}).map (QuotientGroup.mk' N₀) := by
    intro x hx
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hxR
    have hcomm : Commute (QuotientGroup.mk' N₀ t) (QuotientGroup.mk' N₀ r) :=
      Subgroup.mem_centralizer_iff.1 hxC (QuotientGroup.mk' N₀ t) (Set.mem_singleton _)
    obtain ⟨c, hct, hcr⟩ := hlift r hcomm
    have hc : c ∈ R := by
      have h1 : c⁻¹ * r ∈ N₀ := QuotientGroup.eq.1 hcr
      have h2 : c = r * (c⁻¹ * r)⁻¹ := by group
      rw [h2]
      exact R.mul_mem hr (hN₀R (N₀.inv_mem h1))
    refine Subgroup.mem_map.2 ⟨c, Subgroup.mem_inf.2 ⟨hc, ?_⟩, hcr⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh]
    exact hct
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' N₀ : M →* M ⧸ N₀).ker := by
    rw [QuotientGroup.ker_mk']
    exact h3
  calc CFSG.Open.pRank 3 (R.map (QuotientGroup.mk' N₀) ⊓
        Subgroup.centralizer {QuotientGroup.mk' N₀ t})
      ≤ CFSG.Open.pRank 3 ((R ⊓ Subgroup.centralizer {t}).map (QuotientGroup.mk' N₀)) :=
        CFSG.SectionRank.pRank_mono (by norm_num : (1 : ℕ) < 3) hsub
    _ ≤ CFSG.Open.pRank 3 (R ⊓ Subgroup.centralizer {t}) :=
        CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd Nat.prime_three
          (QuotientGroup.mk' N₀) hker _
    _ ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {t}) :=
        CFSG.SectionRank.pRank_mono (by norm_num : (1 : ℕ) < 3) inf_le_right
    _ ≤ 3 := hCrank

end SFLiftRank

section SFPCore

open CFSG

private lemma card_comap_eq_mul_card_ker {H L : Type*} [Group H] [Group L]
    (f : H →* L) (hf : Function.Surjective f) (K : Subgroup L) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  have hle : f.ker ≤ K.comap f := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    rw [Subgroup.mem_comap, hh]
    exact K.one_mem
  have h1 : f.ker.relIndex (K.comap f) = Nat.card K := by
    rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective hf]
  have h2 := Subgroup.relIndex_mul_card (H := f.ker) (K := K.comap f)
  rw [inf_eq_left.mpr hle, h1] at h2
  exact h2.symm

theorem pPrimeCore_map_quotient_eq_bot {M : Type*} [Group M] [Finite M] (R : Subgroup M)
    (N₀ : Subgroup M) [N₀.Normal] (hN₀ : N₀ = (CFSG.pPrimeCore 3 R).map R.subtype) :
    CFSG.pPrimeCore 3 ↥(R.map (QuotientGroup.mk' N₀)) = ⊥ := by
  let R₁ : Subgroup (M ⧸ N₀) := R.map (QuotientGroup.mk' N₀)
  let ι : ↥R →* ↥R₁ :=
    MonoidHom.codRestrict ((QuotientGroup.mk' N₀).comp R.subtype) R₁
      (fun r => Subgroup.mem_map_of_mem _ r.2)
  have hι : Function.Surjective ι := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker : ∀ r : ↥R, ι r = 1 ↔ r ∈ CFSG.pPrimeCore 3 ↥R := by
    intro r
    have h1 : ι r = 1 ↔ (r : M) ∈ N₀ := by
      rw [← QuotientGroup.eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1, hN₀]
    exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective R)
  have hkerEq : ι.ker = CFSG.pPrimeCore 3 ↥R := by
    ext r
    rw [MonoidHom.mem_ker]
    exact hker r
  apply CFSG.pPrimeCore_eq_bot_iff.mpr
  intro K hK hKc
  have hH'n : (K.comap ι).Normal := Subgroup.Normal.comap hK ι
  have hcard : Nat.card (K.comap ι) = Nat.card K * Nat.card (CFSG.pPrimeCore 3 ↥R) := by
    rw [card_comap_eq_mul_card_ker ι hι K, hkerEq]
  have hcop : Nat.Coprime 3 (Nat.card (K.comap ι)) := by
    rw [hcard]
    exact Nat.Coprime.mul_right hKc (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥R))
  have hle : K.comap ι ≤ CFSG.pPrimeCore 3 ↥R := le_sSup ⟨hH'n, hcop⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := hι x
  rw [Subgroup.mem_bot]
  exact (hker r).mpr (hle (Subgroup.mem_comap.mpr hx))

end SFPCore

section SFMineA

open CFSG Subgroup

theorem ker_le_of_perfect_solvable_kernel {X S : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [Group S] (hS : IsSimpleGroup S) (π : X →* S)
    (hπ : Function.Surjective π) (hsolv : Group.IsSolvable π.ker) {G : Type*} [Group G]
    (ρ : X →* G) (hρ : ρ ≠ 1) : ρ.ker ≤ π.ker := by
  by_contra hnot
  have hN : (ρ.ker.map π).Normal := (MonoidHom.normal_ker ρ).map π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map π) with h | h
  · apply hnot
    intro x hx
    have : π x ∈ ρ.ker.map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at this
    exact this
  · haveI : Group.IsSolvable π.ker := hsolv
    let f : π.ker →* X ⧸ ρ.ker := (QuotientGroup.mk' ρ.ker).comp π.ker.subtype
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hx : π x ∈ ρ.ker.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
      refine ⟨⟨k⁻¹ * x, ?_⟩, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
      · show ((k⁻¹ * x : X) : X ⧸ ρ.ker) = (x : X ⧸ ρ.ker)
        rw [QuotientGroup.eq]
        have := (MonoidHom.normal_ker ρ).conj_mem k hk x⁻¹
        simpa [mul_assoc] using this
    haveI : Group.IsSolvable (X ⧸ ρ.ker) := Group.isSolvable_of_surjective hf
    have hsub : Subsingleton (X ⧸ ρ.ker) := by
      by_contra hns
      haveI : Nontrivial (X ⧸ ρ.ker) := not_subsingleton_iff_nontrivial.mp hns
      exact Group.IsPerfect.not_isSolvable (X ⧸ ρ.ker) inferInstance
    apply hρ
    ext x
    have : (x : X ⧸ ρ.ker) = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.eq_one_iff] at this
    simpa using this

theorem exists_commuting_involutions_of_surjective {X S : Type*}
    [Group X] [Finite X] [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hSn : ∃ a b : S, a * b ≠ b * a) (π : X →* S)
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) :
    ∃ a b : X, orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b := by
  obtain ⟨V, hVc, hV2, hV4⟩ := CFSG.RankThree.OddKernel.exists_four_group_of_isSimpleGroup hSn
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  obtain ⟨A, hA2, hAV, hAinj⟩ :=
    CFSG.RankThree.OddKernel.exists_two_subgroup_map_eq π hπ hodd V hVp
  have hinj : ∀ x ∈ A, ∀ y ∈ A, π x = π y → x = y := fun x hx y hy h =>
    congrArg Subtype.val (hAinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  have hnt : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hV4]
    norm_num
  obtain ⟨v₁, hv₁⟩ := exists_ne (1 : V)
  have hv₁sq : (v₁ : S) ^ 2 = 1 := hV2 _ v₁.2
  have hnle : ¬ V ≤ Subgroup.zpowers (v₁ : S) := by
    intro hle
    have h1 : Nat.card V ∣ Nat.card (Subgroup.zpowers (v₁ : S)) := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf (v₁ : S) ∣ 2 := orderOf_dvd_of_pow_eq_one hv₁sq
    have := h1.trans h2
    rw [hV4] at this
    omega
  obtain ⟨v₂, hv₂V, hv₂⟩ := Set.not_subset.mp hnle
  have hv₂1 : v₂ ≠ 1 := fun h => hv₂ (h ▸ Subgroup.one_mem _)
  have hv₂₁ : v₂ ≠ (v₁ : S) := fun h => hv₂ (h ▸ Subgroup.mem_zpowers _)
  have hv₁1 : (v₁ : S) ≠ 1 := fun h => hv₁ (Subtype.ext h)
  have hmem₁ : (v₁ : S) ∈ A.map π := by rw [hAV]; exact v₁.2
  have hmem₂ : v₂ ∈ A.map π := by rw [hAV]; exact hv₂V
  obtain ⟨a, haA, hav⟩ := Subgroup.mem_map.mp hmem₁
  obtain ⟨b, hbA, hbv⟩ := Subgroup.mem_map.mp hmem₂
  have hv₂sq : v₂ ^ 2 = 1 := hV2 _ hv₂V
  have ha2 : a ^ 2 = 1 := by
    refine hinj _ (A.pow_mem haA 2) 1 A.one_mem ?_
    rw [map_pow, hav, hv₁sq, map_one]
  have hb2 : b ^ 2 = 1 := by
    refine hinj _ (A.pow_mem hbA 2) 1 A.one_mem ?_
    rw [map_pow, hbv, hv₂sq, map_one]
  have ha1 : a ≠ 1 := fun h => hv₁1 (by rw [← hav, h, map_one])
  have hb1 : b ≠ 1 := fun h => hv₂1 (by rw [← hbv, h, map_one])
  refine ⟨a, b, orderOf_eq_prime ha2 ha1, orderOf_eq_prime hb2 hb1, ?_, ?_⟩
  · refine hinj _ (A.mul_mem haA hbA) _ (A.mul_mem hbA haA) ?_
    rw [map_mul, map_mul, hav, hbv]
    exact hVc _ v₁.2 _ hv₂V
  · intro hab
    exact hv₂₁ (by rw [← hbv, ← hab, hav])

end SFMineA

section SFMineB

open CFSG Subgroup

theorem normal_map_of_characteristic {M : Type*} [Group M] (R : Subgroup M) [R.Normal]
    (H : Subgroup R) [H.Characteristic] : (H.map R.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨r, hr, rfl⟩ g
  refine ⟨MulAut.conjNormal g r, ?_, ?_⟩
  · exact (Subgroup.characteristic_iff_le_comap.mp ‹H.Characteristic› (MulAut.conjNormal g)) hr
  · simp [MulAut.conjNormal_apply]

theorem exists_involution_lift_of_odd_ker {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hker : Odd (Nat.card f.ker)) {x : G} (hx : orderOf (f x) = 2) :
    ∃ g : G, f g = f x ∧ orderOf g = 2 := by
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hfx2 : f x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hmdvd : m ∣ orderOf x := ⟨2 ^ k, by rw [hkm]; ring⟩
  have hog : orderOf (x ^ m) = 2 ^ k := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hkm]
    exact Nat.mul_div_cancel _ hm.pos
  obtain ⟨j, hj⟩ := hm
  have hfg : f (x ^ m) = f x := by
    rw [map_pow, hj, pow_succ, pow_mul, hfx2, one_pow, one_mul]
  refine ⟨x ^ m, hfg, ?_⟩
  have hg1 : x ^ m ≠ 1 := by
    intro h
    rw [h, map_one] at hfg
    rw [← hfg] at hx
    simp at hx
  have hmem : (x ^ m) ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hfg, hfx2]
  have hodd2 : Odd (orderOf ((x ^ m) ^ 2)) := by
    have h1 : orderOf (⟨(x ^ m) ^ 2, hmem⟩ : f.ker) ∣ Nat.card f.ker := orderOf_dvd_natCard _
    have h2 : orderOf (⟨(x ^ m) ^ 2, hmem⟩ : f.ker) = orderOf ((x ^ m) ^ 2) :=
      Subgroup.orderOf_mk _ _
    rw [h2] at h1
    exact Odd.of_dvd_nat hker h1
  have hdvd : orderOf ((x ^ m) ^ 2) ∣ 2 ^ k := hog ▸ orderOf_pow_dvd 2
  obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hodd2
    exact (Nat.not_even_iff_odd.mpr hodd2) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  have hsq : (x ^ m) ^ 2 = 1 := by
    rw [hi0, pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  exact orderOf_eq_prime hsq hg1

end SFMineB

end CFSG.RankThree.PartTwo.Sec13.K135SF

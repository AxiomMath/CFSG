module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Frat
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3L26Deg

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.PGLModel (projSU)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec11.LSSolvableProof (card_projSL_two_even isSimpleGroup_projSL)

theorem map_eq_bot_of_commutator_eq_self_of_isSolvable {P R : Type*} [Group P] [Group R]
    (φ : P →* R) {K : Subgroup P} (hK : ⁅K, K⁆ = K) (hs : Group.IsSolvable ↥(K.map φ)) :
    K.map φ = ⊥ := by
  by_contra h
  haveI : Nontrivial ↥(K.map φ) := (Subgroup.nontrivial_iff_ne_bot _).mpr h
  haveI : Group.IsPerfect ↥(K.map φ) :=
    Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hK])
  exact Group.IsPerfect.not_isSolvable _ hs

theorem false_of_frattini_section_of_cover_cent {P Q : Type*} [Group P] [Finite P] [Group Q]
    (ρ : P →* Q) {p : ℕ} [Fact p.Prime] {j : P} (hj : IsPGroup p (Subgroup.zpowers j))
    {r : ℕ} [Fact r.Prime] {S B I : Subgroup Q} [IsSimpleGroup ↥S] (hS : ⁅S, S⁆ = S)
    (hr : r ∣ Nat.card S) (hSj : S ≤ Subgroup.centralizer {ρ j}) (hSI : S ≤ I)
    (hIρ : I ≤ ρ.range) (hI : ⁅I, I⁆ = I) (hB : Group.IsSolvable B)
    (hcent : ∀ x ∈ Subgroup.centralizer {j}, ρ x ∈ B) {Θ : Subgroup P} [Θ.Normal]
    (hΘ : Nat.Coprime (Nat.card Θ) r) (hker : ∀ k ∈ ρ.ker, ∃ n : ℕ, k ^ r ^ n ∈ Θ)
    (hcov : ∀ SK Pi : Subgroup P, IsPGroup p SK → Pi ≤ Subgroup.normalizer (SK : Set P) →
      Pi.map ρ = I → ⁅Pi, Pi⁆ = Pi → Group.IsNilpotent ↥(ρ.comp Pi.subtype).ker →
      ∀ x ∈ Pi, ∀ s ∈ SK, x * s * x⁻¹ = s) :
    False := by
  classical
  have hrp : r.Prime := Fact.out
  have hS1 : S ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hr
    exact hrp.one_lt.ne' (Nat.dvd_one.mp hr)
  obtain ⟨Pi, SK, hPiS, hPi, hnil, hSK, hPS, -, hact⟩ :=
    exists_perfect_cover_act_sylow_of_centralizer ρ hj hS hS1 hSj (hSI.trans hIρ) hB hcent
  set N := Subgroup.normalizer (SK : Set P) with hNdef
  have hfrat : N ⊔ ρ.ker = ⊤ := by
    obtain ⟨T, hT⟩ := hSK
    rw [hNdef, ← hT]
    exact Sylow.normalizer_sup_eq_top T
  have hIN : I ≤ N.map ρ := by
    intro y hy
    obtain ⟨x, rfl⟩ := hIρ hy
    have hx : x ∈ ((N ⊔ ρ.ker : Subgroup P) : Set P) := by
      rw [hfrat]
      exact Subgroup.mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_mul.mp hx
    exact ⟨n, hn, by rw [map_mul, (MonoidHom.mem_ker).mp hk, mul_one]⟩
  obtain ⟨PiY, hPiYN, hPiYI, hPiY, hnilY⟩ := exists_perfect_cover_nilpotent ρ N I hI hIN
  have hY : ∀ x ∈ PiY, ∀ s ∈ SK, x * s * x⁻¹ = s :=
    hcov SK PiY hSK.isPGroup hPiYN hPiYI hPiY hnilY
  set β : ↥N →* MulAut ↥SK := SK.normalizerMonoidHom with hβ
  have hβ1 : ∀ x : ↥N, β x = 1 ↔ ∀ s ∈ SK, (x : P) * s * (x : P)⁻¹ = s := by
    intro x
    constructor
    · intro h s hs
      have h1 : ((β x ⟨s, hs⟩ : ↥SK) : P) = x * s * x⁻¹ := rfl
      rw [h] at h1
      exact h1.symm
    · intro h
      refine MulEquiv.ext fun s => Subtype.ext ?_
      change (x : P) * s * (x : P)⁻¹ = s
      exact h s s.2
  set Pi' : Subgroup ↥N := Pi.subgroupOf N with hPi'def
  have hPi'map : Pi'.map N.subtype = Pi := by
    rw [hPi'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hPS]
  have hPi' : ⁅Pi', Pi'⁆ = Pi' := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, hPi'map]
    exact hPi
  set Θ' : Subgroup ↥N := Θ.subgroupOf N with hΘ'def
  haveI hΘ'n : Θ'.Normal := Subgroup.Normal.subgroupOf inferInstance N
  set D : Subgroup ↥N := β.ker ⊔ Θ' with hDdef
  haveI : D.Normal := Subgroup.sup_normal β.ker Θ'
  have hrgrp : IsPGroup r ↥(Pi'.map (QuotientGroup.mk' D)) := by
    rintro ⟨_, x, hx, rfl⟩
    have hxS : ρ x ∈ S := by
      rw [← hPiS]
      exact ⟨x, hx, rfl⟩
    have hxI : ρ x ∈ PiY.map ρ := by
      rw [hPiYI]
      exact hSI hxS
    obtain ⟨c, hc, hcx⟩ := hxI
    have hcD : (⟨c, hPiYN hc⟩ : ↥N) ∈ D :=
      Subgroup.mem_sup_left ((hβ1 _).mpr (hY c hc))
    have hκ : ((x * (⟨c, hPiYN hc⟩ : ↥N)⁻¹ : ↥N) : P) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      change ρ ((x : P) * c⁻¹) = 1
      rw [map_mul, map_inv, hcx, mul_inv_cancel]
    obtain ⟨n, hn⟩ := hker _ hκ
    refine ⟨n, Subtype.ext ?_⟩
    change QuotientGroup.mk' D x ^ r ^ n = 1
    have hc1 : QuotientGroup.mk' D ⟨c, hPiYN hc⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hcD
    have h1 : QuotientGroup.mk' D x = QuotientGroup.mk' D (x * (⟨c, hPiYN hc⟩ : ↥N)⁻¹) := by
      rw [map_mul, map_inv, hc1, inv_one, mul_one]
    rw [h1, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr ?_)
    rw [Subgroup.coe_pow]
    exact hn
  haveI : Group.IsNilpotent ↥(Pi'.map (QuotientGroup.mk' D)) := hrgrp.isNilpotent
  have hPiD : Pi' ≤ D := by
    have h := map_eq_bot_of_commutator_eq_self_of_isSolvable (QuotientGroup.mk' D) hPi'
      inferInstance
    intro x hx
    have h1 : QuotientGroup.mk' D x ∈ Pi'.map (QuotientGroup.mk' D) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hstep3 : ∀ x : ↥N, (x : P) ∈ Pi → ∃ θ : ↥N, (θ : P) ∈ Θ ∧ β x = β θ := by
    intro x hx
    have hxD : x ∈ (D : Set ↥N) := hPiD hx
    rw [hDdef, Subgroup.mul_normal] at hxD
    obtain ⟨a, ha, θ, hθ, rfl⟩ := Set.mem_mul.mp hxD
    refine ⟨θ, hθ, ?_⟩
    rw [map_mul, (MonoidHom.mem_ker).mp ha, one_mul]
  set βP : ↥Pi →* MulAut ↥SK := β.comp (Subgroup.inclusion hPS) with hβP
  set T : Subgroup Q := βP.ker.map (ρ.comp Pi.subtype) with hTdef
  have hTS : T ≤ S := by
    rw [← hPiS]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, y.2, rfl⟩
  have hTn : (T.subgroupOf S).Normal := by
    constructor
    intro t ht s
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp ht
    have hs : (s : Q) ∈ Pi.map ρ := by
      rw [hPiS]
      exact s.2
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
    have hy' : (⟨x, hx⟩ : ↥Pi) * y * (⟨x, hx⟩ : ↥Pi)⁻¹ ∈ βP.ker :=
      (inferInstance : βP.ker.Normal).conj_mem y hy ⟨x, hx⟩
    refine Subgroup.mem_map.mpr ⟨_, hy', ?_⟩
    rw [map_mul, map_mul, map_inv, hyt]
    change ρ x * (t : Q) * (ρ x)⁻¹ = (s : Q) * t * (s : Q)⁻¹
    rw [hxs]
  haveI : Group.IsPerfect ↥Pi := Subgroup.isPerfect_iff.mpr hPi
  haveI := hTn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf S) with hT | hT
  ·
    have hT1 : ∀ y : ↥Pi, βP y = 1 → ρ y = 1 := by
      intro y hy
      have hyT : ρ y ∈ T := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      have hyS : (⟨ρ y, hTS hyT⟩ : ↥S) ∈ T.subgroupOf S := hyT
      rw [hT, Subgroup.mem_bot] at hyS
      exact congrArg Subtype.val hyS
    have hSfin : Finite ↥S := by
      rw [← hPiS]
      refine Finite.of_surjective (fun x : ↥Pi => (⟨ρ x, x, x.2, rfl⟩ : ↥(Pi.map ρ))) ?_
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨s₀, hs₀⟩ := exists_prime_orderOf_dvd_card' r hr
    have hs₀Pi : (s₀ : Q) ∈ Pi.map ρ := by
      rw [hPiS]
      exact s₀.2
    obtain ⟨x, hx, hxs⟩ := hs₀Pi
    obtain ⟨θ, hθ, hxθ⟩ := hstep3 ⟨x, hPS hx⟩ hx
    have hθr : Nat.Coprime (orderOf θ) r := by
      have h1 : orderOf θ ∣ Nat.card Θ := by
        rw [← Subgroup.orderOf_coe]
        exact Subgroup.orderOf_dvd_natCard Θ hθ
      exact Nat.Coprime.coprime_dvd_left h1 hΘ
    have hxm : βP (⟨x, hx⟩ ^ orderOf θ) = 1 := by
      rw [map_pow]
      change β ⟨x, hPS hx⟩ ^ orderOf θ = 1
      rw [hxθ, ← map_pow, pow_orderOf_eq_one, map_one]
    have h2 : (s₀ : Q) ^ orderOf θ = 1 := by
      rw [← hxs, ← map_pow]
      exact hT1 _ hxm
    have h3 : r ∣ orderOf θ := by
      rw [← hs₀, ← Subgroup.orderOf_coe s₀]
      exact orderOf_dvd_of_pow_eq_one h2
    exact (Nat.Prime.coprime_iff_not_dvd hrp).mp hθr.symm h3
  ·
    have hST : S ≤ T := Subgroup.subgroupOf_eq_top.mp hT
    set Kn : Subgroup ↥Pi := (ρ.comp Pi.subtype).ker with hKn
    haveI : Group.IsNilpotent ↥Kn := hnil
    have hrange : βP.range ≤ Kn.map βP := by
      rintro _ ⟨x, rfl⟩
      have hxT : ρ x ∈ T := by
        refine hST ?_
        rw [← hPiS]
        exact ⟨x, x.2, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxT
      refine Subgroup.mem_map.mpr ⟨y⁻¹ * x, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hyx]
        exact inv_mul_cancel _
      · rw [map_mul, map_inv, (MonoidHom.mem_ker).mp hy, inv_one, one_mul]
    haveI : Group.IsSolvable ↥(Kn.map βP) :=
      solvable_of_surjective (βP.subgroupMap_surjective Kn)
    haveI : Group.IsSolvable ↥βP.range :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective hrange)
    haveI : Group.IsPerfect ↥βP.range :=
      Group.IsPerfect.ofSurjective (f := βP.rangeRestrict) βP.rangeRestrict_surjective
    obtain ⟨x, hx, s, hs, hxs⟩ := hact
    have hne : βP ⟨x, hx⟩ ≠ 1 := fun h => hxs ((hβ1 ⟨x, hPS hx⟩).mp h s hs)
    haveI : Nontrivial ↥βP.range :=
      ⟨⟨⟨βP ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable ↥βP.range inferInstance

theorem false_of_frattini_section_u34 {G : Type} [Group G] [Finite G] {Q : Type*} [Group Q]
    (hloc : CFSG.Assembly.RankThreeEven.localRank 5 G < 3) {P : Subgroup G} (ρ : P →* Q)
    {j : P} (hj : IsPGroup 5 (Subgroup.zpowers j)) {S B I : Subgroup Q}
    (eS : S ≃* projSL 2 (GaloisField 2 2)) (eI : I ≃* projSU 3 2 2)
    (hSj : S ≤ Subgroup.centralizer {ρ j}) (hSI : S ≤ I) (hIρ : I ≤ ρ.range)
    (hB : Group.IsSolvable B) (hcent : ∀ x ∈ Subgroup.centralizer {j}, ρ x ∈ B)
    {Θ : Subgroup P} [Θ.Normal] (hΘ : Nat.Coprime (Nat.card Θ) 3)
    (hker : ∀ k ∈ ρ.ker, ∃ n : ℕ, k ^ 3 ^ n ∈ Θ) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI := isPerfect_projSL_two_even (le_refl 2)
  haveI := isSimpleGroup_projSL (le_refl 2)
  haveI := isPerfect_projSU_three_four
  haveI : IsSimpleGroup ↥S := MulEquiv.isSimpleGroup eS
  have hS : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp
    (Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective)
  have hI : ⁅I, I⁆ = I := Subgroup.isPerfect_iff.mp
    (Group.IsPerfect.ofSurjective (f := eI.symm.toMonoidHom) eI.symm.surjective)
  have h3 : 3 ∣ Nat.card S := by
    rw [Nat.card_congr eS.toEquiv, card_projSL_two_even 2 (by norm_num)]
    norm_num
  have hlocP : CFSG.Assembly.RankThreeEven.localRank 5 ↥P < 3 :=
    (CFSG.RankThree.PartTwo.localRank_subgroup_le (Fact.out : (5 : ℕ).Prime) P).trans_lt hloc
  refine false_of_frattini_section_of_cover_cent ρ hj hS h3 hSj hSI hIρ hI hB hcent hΘ hker ?_
  intro SK Pi hSK hPiN hPiI hPi hnil x hx s hs
  by_contra hxs
  haveI : Group.IsPerfect ↥Pi := Subgroup.isPerfect_iff.mpr hPi
  set σ : Pi →* Q := ρ.comp Pi.subtype with hσ
  have hrange : σ.range = I := by
    rw [hσ, MonoidHom.range_comp, Subgroup.range_subtype, hPiI]
  haveI : Group.IsNilpotent ↥σ.ker := hnil
  exact false_of_perfect_cover_act_u34 hlocP (N := σ.ker) inferInstance
    ((QuotientGroup.quotientKerEquivRange σ).trans ((MulEquiv.subgroupCongr hrange).trans eI))
    hSK hPiN ⟨x, hx, s, hs, hxs⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

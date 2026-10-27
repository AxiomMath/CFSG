module

public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTwin
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof153Twin

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem hasNonCentralThree_of_isPerfect {Y : Subgroup G}
    (hp : Group.IsPerfect (↥Y ⧸ aschbacherSolvableCore 3 ↥Y))
    (h3 : 3 ∣ Nat.card (↥Y ⧸ aschbacherSolvableCore 3 ↥Y)) : HasNonCentralThree Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ē, hē3, hēZ⟩ := Sec6.exists_pow_three_eq_one_not_mem_center hp h3
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥Y) ē
  have hθ := solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  obtain ⟨e, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₀).ne' 3 (by norm_num)
  have hēr : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Y) x₀) ^ r ∉
      Subgroup.center (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := by
    intro hc
    apply hēZ
    rcases (show r % 3 = 1 ∨ r % 3 = 2 by omega) with h1 | h2
    · rwa [pow_eq_pow_mod r hē3, h1, pow_one] at hc
    · rw [pow_eq_pow_mod r hē3, h2] at hc
      have h4 := pow_mem hc 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hē3, one_mul] at h4
  have hx3 : (x₀ ^ r) ^ 3 = 1 := by
    have h : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Y) ((x₀ ^ r) ^ 3) = 1 := by
      rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, hē3, one_pow]
    have hmem : (x₀ ^ r) ^ 3 ∈ aschbacherSolvableCore 3 ↥Y :=
      (QuotientGroup.eq_one_iff _).mp h
    have hk : ((x₀ ^ r) ^ 3) ^ 3 ^ e = 1 := by
      rw [← pow_mul, ← pow_mul, show r * (3 * 3 ^ e) = 3 ^ e * r * 3 by ring, pow_mul, ← hor,
        pow_orderOf_eq_one, one_pow]
    exact Sec13.eq_one_of_pow_three_pow_of_not_dvd hθ.2.2.1 hmem hk
  rw [Subgroup.mem_center_iff] at hēr
  push Not at hēr
  obtain ⟨q, hq⟩ := hēr
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥Y) q
  refine ⟨((x₀ ^ r : ↥Y) : G), (x₀ ^ r).2, ?_, (y₀ : G), y₀.2, fun hmem => hq ?_⟩
  · rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  · have hmem' : x₀ ^ r * y₀ * (x₀ ^ r)⁻¹ * y₀⁻¹ ∈ aschbacherSolvableCore 3 ↥Y := by
      refine (Subgroup.mem_map_iff_mem Y.subtype_injective).mp ?_
      simpa using hmem
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Y)
        (x₀ ^ r * y₀ * (x₀ ^ r)⁻¹ * y₀⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem'
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

theorem hasNonCentralThree_of_mem_scriptY4 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY4 A LB) : HasNonCentralThree Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYp : Group.IsPerfect ↥Y := isPerfect_of_mem_scriptY4 hY
  have hθ := solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  have hθc := hθ.2.1
  have : (aschbacherSolvableCore 3 ↥Y).Normal := Subgroup.normal_of_characteristic _
  have hp : Group.IsPerfect (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := inferInstance
  have hY4 := hY
  obtain ⟨-, h3', -, hq⟩ := hY4
  have hO2 : CFSG.pCore 2 ↥Y ≠ ⊤ := by
    intro h2
    obtain ⟨-, hs, -⟩ := hq
    have hnt := hs.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    apply hx
    rw [(QuotientGroup.eq_one_iff y).mpr (h2 ▸ Subgroup.mem_top y)]
    rfl
  have h3Y : 3 ∣ Nat.card ↥Y :=
    (three_dvd_card_quotient_of_eq_oPrimeResidualOf h3' (CFSG.pCore 2 ↥Y) hO2).trans
      (Subgroup.card_quotient_dvd_card _)
  have h3 : 3 ∣ Nat.card (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥Y)
    rw [hcard] at h3Y
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp h3Y |>.resolve_right hθ.2.2.1
  exact hasNonCentralThree_of_isPerfect hp h3

theorem index_eq_one_of_isPerfect {K : Type*} [Group K] [Finite K] (hK : Group.IsPerfect K)
    (T : Subgroup K) (h3 : T.index ≤ 3) : T.index = 1 := by
  have h0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : T.FiniteIndex := ⟨h0⟩
  have hfac : T.index.factorial ∣ 6 := by
    interval_cases hT : T.index <;> decide
  have hdvd : T.normalCore.index ∣ 6 :=
    (Subgroup.index_normalCore_dvd_factorial_index T).trans hfac
  have : T.normalCore.Normal := Subgroup.normalCore_normal T
  have hperf : Group.IsPerfect (K ⧸ T.normalCore) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' T.normalCore)
      (QuotientGroup.mk'_surjective _)
  have h1 : T.normalCore.index = 1 := by
    rw [Subgroup.index_eq_card] at hdvd ⊢
    exact Proof152Gen.card_eq_one_of_isPerfect_of_card_dvd_six hperf hdvd
  have hT : T = ⊤ := top_le_iff.mp ((Subgroup.index_eq_one.mp h1) ▸ T.normalCore_le)
  rw [hT, Subgroup.index_top]

section Conj

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem false_of_four_conj (h : Sec14Std G A c L) (h152 : Item152 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hN : HasNonCentralThree Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    (g : Fin 4 → G) (hgM : ∀ i, g i ∈ M)
    (hdist : ∀ i j : Fin 4, i ≠ j → Y.map (MulAut.conj (g i)).toMonoidHom ≠
      Y.map (MulAut.conj (g j)).toMonoidHom) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYM, -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  obtain ⟨Y', hY', hYY'⟩ := mem_thetaComponentsIn_of_item152 h h152 hY hM
  change Y'.map M.subtype = Y at hYY'
  set σ : Fin 4 → (↥M ≃* ↥M) := fun i => MulAut.conj (⟨g i, hgM i⟩ : M) with hσ
  have hσY : ∀ i, (Y'.map (σ i).toMonoidHom).map M.subtype =
      Y.map (MulAut.conj (g i)).toMonoidHom := by
    intro i
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨x, hxY, hx3, y, hyY, hxy⟩ := hN
  have hxY0 := hxY
  have hyY0 := hyY
  rw [← hYY'] at hxY0 hyY0
  obtain ⟨x', hxY', rfl⟩ := hxY0
  obtain ⟨y', hyY', rfl⟩ := hyY0
  obtain ⟨hθN, hθs, hθ3⟩ := map_aschbacherSolvableCore_facts M
  obtain ⟨-, hθc, hθ3', -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have hxyM : ⁅x', y'⁆ ∉ aschbacherSolvableCore 3 ↥M := by
    intro hmem
    apply hxy
    have hmemG : (x' : G) * y' * (x' : G)⁻¹ * (y' : G)⁻¹ ∈
        (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y := by
      refine ⟨?_, Y.mul_mem (Y.mul_mem (Y.mul_mem hxY hyY) (Y.inv_mem hxY)) (Y.inv_mem hyY)⟩
      have := Subgroup.mem_map_of_mem M.subtype hmem
      rwa [commutatorElement_def] at this
    exact inf_le_map_aschbacherSolvableCore (hYM.trans hθN) hθs hθ3 hmemG
  have h4 := four_le_pRank_of_thetaComponents (fun i => Y'.map (σ i).toMonoidHom)
    (fun i => map_mulEquiv_mem_thetaComponents Nat.prime_three (σ i) hY')
    (fun i j hij he => hdist i j hij (by rw [← hσY i, ← hσY j, he]))
    (fun i => σ i x') (fun i => σ i y')
    (fun i => Subgroup.mem_map_of_mem _ hxY') (fun i => Subgroup.mem_map_of_mem _ hyY')
    (fun i => by
      rw [← map_pow]
      have : x' ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one])
    (fun i hmem => by
      apply hxyM
      rw [← map_commutatorElement] at hmem
      have hchar : (aschbacherSolvableCore 3 ↥M).map (σ i).toMonoidHom =
          aschbacherSolvableCore 3 ↥M :=
        Subgroup.characteristic_iff_map_eq.mp hθc (σ i)
      have := Subgroup.mem_map_of_mem (σ i).symm.toMonoidHom hmem
      rw [← hchar, Subgroup.map_map] at this
      simpa using this)
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

theorem le_normalizer_of_isPerfect_of_le (h : Sec14Std G A c L) (h152 : Item152 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    {K : Subgroup G} (hK : Group.IsPerfect ↥K) (hKM : K ≤ M) :
    K ≤ Subgroup.normalizer (Y : Set G) := by
  have hN := hasNonCentralThree_of_mem_scriptY4 hY.prop.1
  set T : Subgroup ↥K := (Subgroup.normalizer (Y : Set G)).subgroupOf K with hT
  suffices hTtop : T = ⊤ by
    intro k hk
    have hkT : (⟨k, hk⟩ : ↥K) ∈ T := hTtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hkT
  by_contra hTne
  have h4 : 4 ≤ T.index := by
    by_contra hlt
    exact hTne (Subgroup.index_eq_one.mp (index_eq_one_of_isPerfect hK T (by omega)))
  have := Fintype.ofFinite (↥K ⧸ T)
  obtain ⟨f⟩ : Nonempty (Fin 4 ↪ ↥K ⧸ T) := by
    refine Function.Embedding.nonempty_of_card_le ?_
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact h4
  set k : Fin 4 → ↥K := fun i => (f i).out with hk
  have hkf : ∀ i, (QuotientGroup.mk (k i) : ↥K ⧸ T) = f i := fun i => QuotientGroup.out_eq' _
  refine false_of_four_conj h h152 hY hN hM (fun i => (k i : G)) (fun i => hKM (k i).2) ?_
  intro i j hij heq
  apply hij
  apply f.injective
  have hmem : (k i)⁻¹ * k j ∈ T := by
    rw [hT, Subgroup.mem_subgroupOf]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    show Y.map (MulAut.conj (((k i)⁻¹ * k j : ↥K) : G)).toMonoidHom = Y
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← Late.map_conj_map_conj, ← heq,
      Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
  rw [← hkf i, ← hkf j]
  exact QuotientGroup.eq.mpr hmem

end Conj

end CFSG.RankThree.PartTwo.Sec15.Proof153Twin

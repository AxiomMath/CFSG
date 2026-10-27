module

public import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofCore
public import CFSG.RankThree.PartTwo.Sec21.Item223Gaps
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223KFactsProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (torusVec torusSU mem_torusSU_iff diagU diagU_val diagUHom
  diagU_injective blk torusSU_le_unitarySU exists_isPrimitiveRoot)
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

section Inner

variable {X B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (X : Set G))

@[expose] noncomputable def barAct : B →* MulAut (X ⧸ aschbacherSolvableCore 3 X) :=
  (Sec4.thetaQuotMulAut X).comp ((Sec4.compAction X).comp (Subgroup.inclusion hBN))

theorem barAct_mk (b : B) (l : X) :
    barAct hBN b (l : X ⧸ aschbacherSolvableCore 3 X) =
      ((⟨(b : G) * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hBN b.2) l).mp l.2⟩ : X) :
        X ⧸ aschbacherSolvableCore 3 X) := by
  rw [barAct, MonoidHom.comp_apply, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk]
  congr 1

variable (hin : ∀ b ∈ B, ¬ Sec4.InducesOuterTheta b X)

include hin in
theorem barAct_mem_range (b : B) :
    barAct hBN b ∈ (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →*
      MulAut (X ⧸ aschbacherSolvableCore 3 X)).range := by
  by_contra h
  exact hin b b.2 ⟨hBN b.2, h⟩

variable (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥)

omit [Finite G] in
include hZ in
theorem conj_injective_of_center :
    Function.Injective (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →*
      MulAut (X ⧸ aschbacherSolvableCore 3 X)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hzc : z ∈ Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h := congrArg (fun σ : MulAut (X ⧸ aschbacherSolvableCore 3 X) => σ w) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc w * z = z * w * z⁻¹ * z := by rw [h]
      _ = z * w := by group
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hzc

@[expose] noncomputable def innerHom : B →* X ⧸ aschbacherSolvableCore 3 X :=
  (MonoidHom.ofInjective (conj_injective_of_center hZ)).symm.toMonoidHom.comp
    ((barAct hBN).codRestrict _ (barAct_mem_range hBN hin))

theorem conj_innerHom (b : B) :
    MulAut.conj (innerHom hBN hin hZ b) = barAct hBN b := by
  have h := (MonoidHom.ofInjective (conj_injective_of_center hZ)).apply_symm_apply
    ⟨barAct hBN b, barAct_mem_range hBN hin b⟩
  exact congrArg Subtype.val h

theorem innerHom_conj (b : B) (z : X ⧸ aschbacherSolvableCore 3 X) :
    innerHom hBN hin hZ b * z * (innerHom hBN hin hZ b)⁻¹ = barAct hBN b z := by
  rw [← conj_innerHom hBN hin hZ b, MulAut.conj_apply]

theorem mem_thetaQuotCentralizer_of_mem_ker {b : B} (hb : b ∈ (innerHom hBN hin hZ).ker) :
    (b : G) ∈ Sec4.thetaQuotCentralizer X := by
  have h1 : barAct hBN b = 1 := by
    rw [← conj_innerHom hBN hin hZ b, MonoidHom.mem_ker.mp hb, map_one]
  exact ⟨Subgroup.inclusion hBN b, h1, rfl⟩

end Inner

theorem exists_lift_of_fixed {X B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (X : Set G))
    (hB3 : IsPGroup 3 B) (z : X ⧸ aschbacherSolvableCore 3 X)
    (hz : ∀ b : B, barAct hBN b z = z) :
    ∃ y : X, (y : X ⧸ aschbacherSolvableCore 3 X) = z ∧
      (y : G) ∈ Subgroup.centralizer (B : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective z
  set φ : B →* MulAut X := (Sec4.compAction X).comp (Subgroup.inclusion hBN) with hφ
  have hφN : ∀ g : B, ∀ n ∈ aschbacherSolvableCore 3 X, φ g n ∈ aschbacherSolvableCore 3 X := by
    intro g n hn
    rw [← Sec4.map_aschbacherSolvableCore (φ g)]
    exact ⟨n, hn, rfl⟩
  have hy : ∀ g : B, ((φ g y₀ : X) : X ⧸ aschbacherSolvableCore 3 X) =
      (y₀ : X ⧸ aschbacherSolvableCore 3 X) := by
    intro g
    have h := hz g
    rw [barAct, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk] at h
    exact h
  obtain ⟨y, hyy, hfix⟩ := KFacts.exists_fixed_of_coprime hB3 φ (aschbacherSolvableCore 3 X)
    (KFacts.not_three_dvd_card_aschbacherSolvableCore X) hφN y₀ hy
  refine ⟨y, hyy, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h1 : h * (y : G) * h⁻¹ = y := congrArg Subtype.val (hfix ⟨h, hh⟩)
  calc h * (y : G) = h * y * h⁻¹ * h := by group
    _ = y * h := by rw [h1]

omit [Finite G] in
theorem nonempty_blk_mulEquiv_projSL {k : ℕ} (hk : 1 ≤ k) {a b : Fin 4} (hab : a ≠ b) :
    Nonempty (blk (unitaryFieldData_galoisField hk) hab ≃* projSL 2 (GaloisField 2 k)) := by
  set hU := unitaryFieldData_galoisField hk
  obtain ⟨e₁⟩ := CFSG.RankThree.PartOne.KFU.nonempty_blk_mulEquiv hU hab
  obtain ⟨e₂⟩ := CFSG.RankThree.PartOne.KFU.nonempty_gramSU_two_mulEquiv_SL2 hU
  have := hU.finite
  have := Fintype.ofFinite hU.fixedField
  have := Fintype.ofFinite (GaloisField 2 k)
  have hcard : Fintype.card hU.fixedField = Fintype.card (GaloisField 2 k) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hU.card_fixedField,
      GaloisField.card 2 k (by omega)]
  exact ⟨e₁.trans (e₂.trans ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr
    (Fin 2) (FiniteField.ringEquivOfCardEq hcard)).trans
    (projSLTwoEquivSL (GaloisField 2 k)).symm))⟩

omit [Finite G] in
theorem eq_of_mem_centralizer {Y : Type} [Group Y] [Finite Y] {k m : ℕ} (hko : Odd k)
    (e : Y ≃* projSU 4 2 k) (hZ : Subgroup.center Y = ⊥) {B' Kb : Subgroup Y}
    (hexp : ∀ z ∈ B', z ^ 3 = 1) (hcomm : ∀ z ∈ B', ∀ w ∈ B', z * w = w * z)
    (h9 : 9 ≤ Nat.card B') (hm : 2 ≤ m) (eK : Kb ≃* projSL 2 (GaloisField 2 m))
    (hKC : ∀ x ∈ Kb, ∀ z ∈ B', z * x = x * z)
    (hKN : ∀ z : Y, (∀ w ∈ B', w * z = z * w) → ∀ x ∈ Kb, z * x * z⁻¹ ∈ Kb) : k = m := by
  have hk1 : 1 ≤ k := hko.pos
  obtain ⟨ψ, hψ⟩ := exists_diag_model_le hk1 hko e hZ B' hexp hcomm
  set hU := unitaryFieldData_galoisField hk1 with hUdef
  have hpq := three_dvd_two_pow_add_one hko
  have := hU.finite
  obtain ⟨z₀, hz₀⟩ := exists_isPrimitiveRoot hU Nat.prime_three hpq
  have hz0 : z₀ ≠ 0 := hz₀.ne_zero (by norm_num)
  have hζ : IsPrimitiveRoot (Units.mk0 z₀ hz0) 3 :=
    IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz₀)
  let tor : torusVec 3 4 (GaloisField 2 (2 * k)) →* unitarySU 2 k (GaloisField 2 (2 * k)) 4 :=
    (diagUHom.comp (torusVec 3 4 (GaloisField 2 (2 * k))).subtype).codRestrict _
      fun d => torusSU_le_unitarySU hU hpq (mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩)
  have htor : ∀ d, ((tor d : unitarySU 2 k (GaloisField 2 (2 * k)) 4) :
      GL (Fin 4) (GaloisField 2 (2 * k))) = diagU (d : Fin 4 → (GaloisField 2 (2 * k))ˣ) :=
    fun _ => rfl
  set θ := ψ.toMonoidHom.comp tor with hθdef
  have hθ : Function.Injective θ := by
    intro d d' h
    have h1 := congrArg (fun v : unitarySU 2 k (GaloisField 2 (2 * k)) 4 =>
      (v : GL (Fin 4) (GaloisField 2 (2 * k)))) (ψ.injective h)
    simp only [htor] at h1
    exact Subtype.ext (diagU_injective h1)
  set H := B'.comap θ with hHdef
  have hB'r : B' ≤ θ.range := by
    intro z hz
    have hg := hψ (ψ.symm z) (by rwa [MulEquiv.apply_symm_apply])
    obtain ⟨d, hd1, hd2, hdg⟩ := mem_torusSU_iff.mp hg
    refine ⟨⟨d, hd1, hd2⟩, ?_⟩
    have htd : tor ⟨d, hd1, hd2⟩ = ψ.symm z := Subtype.ext hdg
    rw [hθdef, MonoidHom.comp_apply, htd, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hHB : H.map θ = B' := Subgroup.map_comap_eq_self hB'r
  have hH9 : 9 ≤ Nat.card H := by
    rw [← Subgroup.card_map_of_injective hθ, hHB]
    exact h9
  set S := (Kb.comap ψ.toMonoidHom).map (unitarySU 2 k (GaloisField 2 (2 * k)) 4).subtype
    with hSdef
  let e₁ : Kb.comap ψ.toMonoidHom ≃* Kb :=
    (Subgroup.equivMapOfInjective _ _ ψ.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective ψ.surjective Kb))
  let eS : S ≃* projSL 2 (GaloisField 2 m) :=
    (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm.trans (e₁.trans eK)
  have hSp := isPerfect_of_mulEquiv_projSL hm eS
  have hc : ∀ g ∈ S, ∀ d ∈ H, g * diagU (d : Fin 4 → (GaloisField 2 (2 * k))ˣ) =
      diagU (d : Fin 4 → (GaloisField 2 (2 * k))ˣ) * g := by
    rintro _ ⟨u, hu, rfl⟩ d hd
    have h1 : θ d * ψ u = ψ u * θ d := hKC (ψ u) hu (θ d) hd
    have h2 : ψ (tor d * u) = ψ (u * tor d) := by
      rw [map_mul, map_mul]
      exact h1
    have h3 := congrArg (fun v : unitarySU 2 k (GaloisField 2 (2 * k)) 4 =>
      (v : GL (Fin 4) (GaloisField 2 (2 * k)))) (ψ.injective h2)
    simp only [Subgroup.coe_mul, htor] at h3
    exact h3.symm
  rcases separating_or_le_hplane H with hsep | ⟨a, b, hab, hle⟩
  · exfalso
    obtain ⟨x, y, hxy⟩ := exists_not_commute_of_mulEquiv_projSL eS
    exact hxy (Subtype.ext (commute_of_separating hsep (hc x x.2) (hc y y.2)))
  · have hHeq := eq_hplane_of_le ⟨_, hζ⟩ hab hle hH9
    have hc' : ∀ g ∈ S, ∀ d ∈ hplane (GaloisField 2 (2 * k)) a b,
        g * diagU (d : Fin 4 → (GaloisField 2 (2 * k))ˣ) =
          diagU (d : Fin 4 → (GaloisField 2 (2 * k))ˣ) * g := by
      rw [← hHeq]
      exact hc
    have hSB := le_blk_of_perfect hU hζ hab (Subgroup.map_subtype_le _) hSp hc'
    have hnorm : ∀ s g : GL (Fin 4) (GaloisField 2 (2 * k)), s ∈ S → g ∈ blk hU hab →
        g * s * g⁻¹ ∈ S := by
      rintro _ g ⟨v, hv, rfl⟩ hg
      have hgU := CFSG.RankThree.PartOne.KFU.blk_le_unitarySU hab hg
      set u : unitarySU 2 k (GaloisField 2 (2 * k)) 4 := ⟨g, hgU⟩ with hu
      have huC : ∀ w ∈ B', w * ψ u = ψ u * w := by
        intro w hw
        rw [← hHB] at hw
        obtain ⟨d, hd, rfl⟩ := hw
        have hdab : (d : Fin 4 → (GaloisField 2 (2 * k))ˣ) a =
            (d : Fin 4 → (GaloisField 2 (2 * k))ˣ) b := mem_hplane_iff.mp (hHeq ▸ hd)
        have h1 := CFSG.RankThree.PartOne.KFU.blk_comm_diagU hab hdab hg
        have h2 : tor d * u = u * tor d := Subtype.ext h1.symm
        change ψ (tor d) * ψ u = ψ u * ψ (tor d)
        rw [← map_mul, ← map_mul, h2]
      have h3 := hKN (ψ u) huC (ψ v) hv
      refine ⟨u * v * u⁻¹, ?_, rfl⟩
      change ψ (u * v * u⁻¹) ∈ Kb
      rw [map_mul, map_mul, map_inv]
      exact h3
    have h4 : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
    have h60 : 4 * 15 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      refine Nat.mul_le_mul h4 ?_
      have : 16 ≤ (2 ^ m) ^ 2 := by nlinarith
      omega
    have hScard : Nat.card S = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr eS.toEquiv, card_projSL_two m (by omega)]
    by_cases hk : k = 1
    · exfalso
      have hle' := Subgroup.card_le_of_le hSB
      rw [card_blk hU hab, hScard, hk] at hle'
      norm_num at hle'
      omega
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨eB⟩ := nonempty_blk_mulEquiv_projSL hk1 hab
      have := isSimpleGroup_projSL_two hk2
      have : IsSimpleGroup (blk hU hab) := eB.isSimpleGroup
      have hN : (S.subgroupOf (blk hU hab)).Normal :=
        (Subgroup.normal_subgroupOf_iff hSB).mpr fun s g hs hg => hnorm s g hs hg
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf (blk hU hab)) with h | h
      · exfalso
        have hSbot : S = ⊥ := by
          rw [Subgroup.subgroupOf_eq_bot] at h
          exact h.eq_bot_of_le hSB
        rw [hSbot, Subgroup.card_bot] at hScard
        omega
      · have hSeq : S = blk hU hab := le_antisymm hSB (Subgroup.subgroupOf_eq_top.mp h)
        exact (eq_of_mulEquiv_projSL_two (by omega) (by omega)
          (eS.symm.trans ((MulEquiv.subgroupCongr hSeq).trans eB))).symm

theorem injective_mk_comp_subtype {X K : Subgroup G} (hKX : K ≤ X) [IsSimpleGroup K]
    (hKp : Group.IsPerfect K) :
    Function.Injective ((QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp
      (K.subgroupOf X).subtype) := by
  set ι := (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (K.subgroupOf X).subtype
  let eK : K.subgroupOf X ≃* K := Subgroup.subgroupOfEquivOfLe hKX
  have : IsSimpleGroup (K.subgroupOf X) := eK.isSimpleGroup
  have hKp' : Group.IsPerfect (K.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ι.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff ι).mp h
  · exfalso
    have hmem : ∀ x : K.subgroupOf X, (x : X) ∈ aschbacherSolvableCore 3 X := fun x =>
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
    have := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).1
    let f : K.subgroupOf X →* aschbacherSolvableCore 3 X :=
      (K.subgroupOf X).subtype.codRestrict _ hmem
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 : ((f x : aschbacherSolvableCore 3 X) : X) =
          ((f y : aschbacherSolvableCore 3 X) : X) := congrArg Subtype.val hxy
      exact Subtype.ext h1
    have hs : Group.IsSolvable (K.subgroupOf X) := Group.isSolvable_of_isSolvable_injective hf
    exact not_subsingleton _ (subsingleton_of_isPerfect_of_isSolvable hKp' hs)

theorem eq_of_innerConfig {X A B K : Subgroup G} {m k : ℕ}
    (eX : X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 k) (hko : Odd k)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X) (hBA : B ≤ A) (hB27 : Nat.card B = 3 ^ 3)
    (hKX : K ≤ X) (hKC : K ≤ Subgroup.centralizer (B : Set G))
    (hKN : ∀ y ∈ X ⊓ Subgroup.centralizer (B : Set G), ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (eK : K ≃* projSL 2 (GaloisField 2 m)) (hm1 : 1 < m) : k = m := by
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBA.trans hAN
  have hinB : ∀ b ∈ B, ¬ Sec4.InducesOuterTheta b X := fun b hb => hin b (hBA hb)
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) := isSimpleGroup_projSL_two (by omega)
  have : IsSimpleGroup K := eK.isSimpleGroup
  have hKp : Group.IsPerfect K := isPerfect_of_mulEquiv_projSL (by omega) eK
  set ι : K.subgroupOf X →* X ⧸ aschbacherSolvableCore 3 X :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (K.subgroupOf X).subtype with hιdef
  have hι : Function.Injective ι := injective_mk_comp_subtype hKX hKp
  let eKb : ι.range ≃* projSL 2 (GaloisField 2 m) :=
    (MonoidHom.ofInjective hι).symm.trans ((Subgroup.subgroupOfEquivOfLe hKX).trans eK)
  obtain ⟨u₁, u₂, hu⟩ := exists_not_commute_of_mulEquiv_projSL eKb
  have hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥ :=
    center_eq_bot_of_mulEquiv_projSU hko.pos eX (a := u₁) (b := u₂)
      (fun h => hu (Subtype.ext h))
  set β := innerHom hBN hinB hZ with hβ
  have hB3 : ∀ b : B, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hAe.2 _ (hBA b.2))
  have hBc : ∀ b b' : B, b * b' = b' * b := by
    intro b b'
    have h := congrArg Subtype.val (hAe.1.is_comm.comm ⟨(b : G), hBA b.2⟩ ⟨(b' : G), hBA b'.2⟩)
    exact Subtype.ext h
  have hexp : ∀ z ∈ β.range, z ^ 3 = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_pow, hB3, map_one]
  have hcomm : ∀ z ∈ β.range, ∀ w ∈ β.range, z * w = w * z := by
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    rw [← map_mul, ← map_mul, hBc]
  have hker : Nat.card β.ker ≤ 3 := by
    have hle : (β.ker).map B.subtype ≤ A ⊓ Sec4.thetaQuotCentralizer X := by
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨hBA b.2, mem_thetaQuotCentralizer_of_mem_ker hBN hinB hZ hb⟩
    rw [← Subgroup.card_map_of_injective B.subtype_injective]
    exact (Subgroup.card_le_of_le hle).trans hAC.le
  have hprod : Nat.card β.ker * Nat.card β.range = 27 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hB27]
    norm_num
  have hpos : 0 < Nat.card β.ker := Nat.card_pos
  have h9 : 9 ≤ Nat.card β.range := by
    interval_cases (Nat.card β.ker) <;> omega
  have hKC' : ∀ x ∈ ι.range, ∀ z ∈ β.range, z * x = x * z := by
    rintro _ ⟨x, rfl⟩ _ ⟨b, rfl⟩
    have hbx : barAct hBN b (ι x) = ι x := by
      rw [hιdef, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply, barAct_mk]
      congr 1
      apply Subtype.ext
      have hxB := Subgroup.mem_centralizer_iff.mp (hKC (Subgroup.mem_subgroupOf.mp x.2)) b b.2
      change (b : G) * ((x : X) : G) * (b : G)⁻¹ = ((x : X) : G)
      rw [hxB, mul_inv_cancel_right]
    have h := innerHom_conj hBN hinB hZ b (ι x)
    rw [hbx] at h
    calc β b * ι x = β b * ι x * (β b)⁻¹ * β b := by group
      _ = ι x * β b := by rw [h]
  have hKN' : ∀ z : X ⧸ aschbacherSolvableCore 3 X, (∀ w ∈ β.range, w * z = z * w) →
      ∀ x ∈ ι.range, z * x * z⁻¹ ∈ ι.range := by
    intro z hz x hx
    have hfix : ∀ b : B, barAct hBN b z = z := by
      intro b
      have h1 := innerHom_conj hBN hinB hZ b z
      rw [← hβ] at h1
      rw [← h1, hz (β b) ⟨b, rfl⟩, mul_inv_cancel_right]
    obtain ⟨y, rfl, hyC⟩ := exists_lift_of_fixed hBN (IsPGroup.of_card hB27) z hfix
    obtain ⟨x, rfl⟩ := hx
    have hyk : (y : G) * ((x : X) : G) * (y : G)⁻¹ ∈ K :=
      hKN y ⟨y.2, hyC⟩ _ (Subgroup.mem_subgroupOf.mp x.2)
    refine ⟨⟨y * (x : X) * y⁻¹, Subgroup.mem_subgroupOf.mpr hyk⟩, ?_⟩
    change QuotientGroup.mk' (aschbacherSolvableCore 3 X) (y * (x : X) * y⁻¹) =
      (y : X ⧸ aschbacherSolvableCore 3 X) * ι x * (y : X ⧸ aschbacherSolvableCore 3 X)⁻¹
    rw [map_mul, map_mul, map_inv]
    rfl
  exact eq_of_mem_centralizer hko eX hZ hexp hcomm h9 (by omega) eKb hKC' hKN'

end CFSG.RankThree.PartTwo.Sec21.Item223KFactsProof

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)


@[expose] def Inspection223List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A B K : Subgroup G) (m : ℕ),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 3 ^ 4 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal) →
    B ≤ A → Nat.card B = 3 ^ 3 → K ≤ X → K ≤ Subgroup.centralizer (B : Set G) →
    (∀ y ∈ X ⊓ Subgroup.centralizer (B : Set G), ∀ k ∈ K, y * k * y⁻¹ ∈ K) →
    Nonempty (K ≃* projSL 2 (GaloisField 2 m)) → 1 < m → Odd m →
    ∃ k : ℕ, Odd k ∧ Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 k)

@[expose] def U4OrderThreeNotStdDiagonal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (x : G) (k : ℕ), 1 ≤ k →
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 k) → x ^ 3 = 1 →
      ¬ KFacts.InducesStdKind X x .diagonal

theorem nonempty_mulEquiv_projSU_of_list (hList : Inspection223List) {G : Type} [Group G]
    [Finite G] {X A B K : Subgroup G} {m : ℕ}
    (hL : Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X)) (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hA81 : Nat.card A = 3 ^ 4) (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    (hdiag : ∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal)
    (hBA : B ≤ A) (hB27 : Nat.card B = 3 ^ 3) (hKX : K ≤ X)
    (hKC : K ≤ Subgroup.centralizer (B : Set G))
    (hKN : ∀ y ∈ X ⊓ Subgroup.centralizer (B : Set G), ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hK : Nonempty (K ≃* projSL 2 (GaloisField 2 m))) (hm1 : 1 < m) (hmo : Odd m)
    (hinner : ∀ k : ℕ, 1 ≤ k → Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 k) →
      ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X) :
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 m) := by
  obtain ⟨k, hko, ⟨eX⟩⟩ :=
    hList G X A B K m hL hAe hA81 hAN hAC hdiag hBA hB27 hKX hKC hKN hK hm1 hmo
  obtain ⟨eK⟩ := hK
  obtain rfl := Item223KFactsProof.eq_of_innerConfig eX hko hAe hAN hAC
    (hinner k hko.pos ⟨eX⟩) hBA hB27 hKX hKC hKN eK hm1
  exact ⟨eX⟩

theorem inspection223_of (hList : Inspection223List) (hDiag : U4OrderThreeNotStdDiagonal) :
    Inspection223 := by
  intro G _ _ X A B K m hL hAe hA81 hAN hAC hdiag hBA hB27 hKX hKC hKN hK hm1 hmo
  refine nonempty_mulEquiv_projSU_of_list hList hL hAe hA81 hAN hAC hdiag hBA hB27 hKX hKC hKN hK
    hm1 hmo fun k hk eX x hx hout => ?_
  exact hDiag G X x k hk eX (hAe.2 x hx) (hdiag x hx hout)

end CFSG.RankThree.PartTwo.Sec21

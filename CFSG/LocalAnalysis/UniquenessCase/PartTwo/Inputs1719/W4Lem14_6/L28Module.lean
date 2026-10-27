module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Bender
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Groups.PSL2
public import CFSG.Quasithin.Background.SmithB45MatIndRealize
public import CFSG.Quasithin.H13.GoldschmidtG52Sec
public import CFSG.RankThree.PartTwo.KFacts.K71Borel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem center_eq_bot_of_isL2_three {S : Type} [Group S] (h : UC22.IsL2 S 3) :
    Subgroup.center S = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel h
  haveI : IsSimpleGroup S := CFSG.GF2Type.Smith1979.OmegaPlus.isSimpleGroup_of_mulEquiv_psl28 e
  obtain ⟨a, b, hab⟩ := CFSG.GF2Type.Smith1979.OmegaPlus.exists_ne_comm_of_mulEquiv_psl28 e
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with hZ | hZ
  · exact hZ
  · exfalso
    have hb : b ∈ Subgroup.center S := hZ ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem odd_card_outer_of_isL2_three {S : Type} [Group S] [Finite S] (h : UC22.IsL2 S 3) :
    Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel h
  have hAut : Nat.card (MulAut S) = 3 * Nat.card S :=
    CFSG.GF2Type.Smith1979.OmegaPlus.card_mulAut_of_mulEquiv_psl28 e
  have hZ := center_eq_bot_of_isL2_three h
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun φ : MulAut S => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * g = g * x * g⁻¹ * g := by rw [hx]
        _ = g * x := by group
    rw [hZ, Subgroup.mem_bot] at hgZ
    exact hgZ
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) =
      Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  rw [hAut, hinner] at hsplit
  have h3 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = 3 :=
    (Nat.eq_of_mul_eq_mul_right Nat.card_pos hsplit).symm
  rw [h3]
  exact ⟨1, by norm_num⟩

theorem six_le_rk_of_isL2_three {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {S : Subgroup (MulAut U)} (h3 : UC22.IsL2 ↥S 3) : 6 ≤ rk U := by
  haveI : IsSimpleGroup ↥S :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
  have hne : S.subtype ≠ 1 := by
    intro h1
    obtain ⟨s, hs⟩ := exists_ne (1 : ↥S)
    apply hs
    apply Subtype.ext
    simpa using DFunLike.congr_fun h1 s
  have := Inputs1719.dMinDeg_le_rk_of_hom_ne_one (fun a b : U => mul_comm a b)
    (fun a => by rw [← sq]; exact hU a) S.subtype hne
  rw [dMinDeg_eq_six_of_isL2_three h3] at this
  exact this

theorem nonempty_mulEquiv_sl2_of_isL2_three {S : Type} [Group S] (h : UC22.IsL2 S 3) :
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel h
  exact ⟨e.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 3))⟩

theorem isIrreducible_autRepOfG {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {S : Subgroup (MulAut U)} {Γ : Type} [Group Γ] (θ : ↥S ≃* Γ) (hirr : IsIrrOn S ⊤ ⊥) :
    (CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ).IsIrreducible := by
  obtain ⟨x0, -, hx0⟩ := SetLike.exists_of_lt hirr.1
  haveI : Nontrivial U := ⟨⟨x0, 1, fun h => hx0 (h ▸ Subgroup.one_mem _)⟩⟩
  haveI : Nontrivial (CFSG.Quasithin.F2Vec U hU) := inferInstanceAs (Nontrivial (Additive U))
  exact CFSG.Quasithin.H13.A6.G52.isIrreducible_of_forall_submodule _
    (CFSG.Quasithin.B45Mat.Ind.irr_autRepOfG hU θ (fun V hV => hirr.2.2.2 V hV bot_le le_top))

theorem autRepOfG_injective {U : Type} [CommGroup U] (hU : ∀ u : U, u ^ 2 = 1)
    {S : Subgroup (MulAut U)} {Γ : Type} [Group Γ] (θ : ↥S ≃* Γ) :
    Function.Injective (CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ) := by
  intro g h hgh
  apply θ.symm.injective
  apply Subtype.ext
  apply MulEquiv.ext
  intro u
  have hu := LinearMap.congr_fun hgh (CFSG.Quasithin.F2Vec.ofV hU u)
  rw [CFSG.Quasithin.B45Mat.Ind.autRepOfG_apply, CFSG.Quasithin.B45Mat.Ind.autRepOfG_apply] at hu
  simpa [CFSG.Quasithin.F2Vec.toV_ofV] using congrArg (CFSG.Quasithin.F2Vec.toV hU) hu

theorem finrank_f2Vec_eq_rk {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.F2Vec U hU) = rk U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card (CFSG.Quasithin.F2Vec U hU) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Quasithin.F2Vec U hU) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (CFSG.Quasithin.F2Vec U hU) = Nat.card U := rfl
  unfold rk
  rw [← h2, h1, padicValNat.prime_pow]

theorem natCard_fixV_eq_autRepOfG {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {S : Subgroup (MulAut U)} {Γ : Type} [Group Γ] (θ : ↥S ≃* Γ) {P : Subgroup (MulAut U)}
    (hPS : P ≤ S) :
    Nat.card (fixV P) = Nat.card {w : CFSG.Quasithin.F2Vec U hU //
      ∀ g ∈ (P.subgroupOf S).map θ.toMonoidHom,
        CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ g w = w} := by
  have h1 : ∀ u : U, u ∈ fixV P → ∀ g ∈ (P.subgroupOf S).map θ.toMonoidHom,
      CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ g (CFSG.Quasithin.F2Vec.ofV hU u) =
        CFSG.Quasithin.F2Vec.ofV hU u := by
    rintro u hu _ ⟨⟨x, hxS⟩, hxP, rfl⟩
    rw [CFSG.Quasithin.B45Mat.Ind.autRepOfG_apply]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      CFSG.Quasithin.F2Vec.toV_ofV]
    exact congrArg (CFSG.Quasithin.F2Vec.ofV hU)
      (mem_fixV.mp hu x (Subgroup.mem_subgroupOf.mp hxP))
  have h2 : ∀ w : CFSG.Quasithin.F2Vec U hU, (∀ g ∈ (P.subgroupOf S).map θ.toMonoidHom,
      CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ g w = w) →
        CFSG.Quasithin.F2Vec.toV hU w ∈ fixV P := by
    intro w hw
    rw [mem_fixV]
    intro x hxP
    have h := hw (θ ⟨x, hPS hxP⟩) ⟨⟨x, hPS hxP⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
    rw [CFSG.Quasithin.B45Mat.Ind.autRepOfG_apply, MulEquiv.symm_apply_apply] at h
    exact congrArg (CFSG.Quasithin.F2Vec.toV hU) h
  exact Nat.card_congr
    { toFun := fun u => ⟨CFSG.Quasithin.F2Vec.ofV hU (u : U), h1 u u.2⟩
      invFun := fun w => ⟨CFSG.Quasithin.F2Vec.toV hU w, h2 w w.2⟩
      left_inv := fun u => rfl
      right_inv := fun w => rfl }

theorem two_mul_rkIdx_fixV_eq_rk_of_isL2_three {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {S : Subgroup (MulAut U)} (h3 : UC22.IsL2 ↥S 3)
    (hirr : IsIrrOn S ⊤ ⊥) {t : MulAut U} (htS : t ∈ S) (ht : orderOf t = 2) :
    2 * rkIdx (fixV (Subgroup.zpowers t)) = rk U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_sl2_of_isL2_three h3
  set ρ := CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ with hρ
  have hirrρ := isIrreducible_autRepOfG hU θ hirr
  have hinj := autRepOfG_injective hU θ
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set g₀ := θ ⟨t, htS⟩ with hg₀
  have hg₀2 : g₀ * g₀ = 1 := by
    rw [hg₀, ← map_mul]
    have : (⟨t, htS⟩ : ↥S) * ⟨t, htS⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have ha2 : ρ g₀ * ρ g₀ = 1 := by rw [← map_mul, hg₀2, map_one]
  have hτ : ∀ g, ρ g₀ * ρ g = ρ (g₀ * g * g₀⁻¹) * ρ g₀ := by
    intro g
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hτ1 : ∃ g, g₀ * g * g₀⁻¹ ≠ g := by
    by_contra hcon
    push Not at hcon
    have hcen : (⟨t, htS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply θ.injective
      rw [map_mul, map_mul, ← hg₀]
      have h1 := hcon (θ s)
      calc θ s * g₀ = g₀ * θ s * g₀⁻¹ * g₀ := by rw [h1]
        _ = g₀ * θ s := by group
    rw [center_eq_bot_of_isL2_three h3, Subgroup.mem_bot] at hcen
    have ht1 : t = 1 := congrArg Subtype.val hcen
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 3) = 2 ^ 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 3 (by norm_num)
  have hact : ∀ u : U, ρ g₀ (CFSG.Quasithin.F2Vec.ofV hU u) =
      CFSG.Quasithin.F2Vec.ofV hU (t u) := by
    intro u
    rw [hρ, CFSG.Quasithin.B45Mat.Ind.autRepOfG_apply, hg₀, MulEquiv.symm_apply_apply]
    rfl
  have hfixcard : Nat.card (fixV (Subgroup.zpowers t)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (ρ g₀ - 1)) := by
    rw [← CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.natCard_fixed_eq]
    refine Nat.card_congr
      { toFun := fun u => ⟨CFSG.Quasithin.F2Vec.ofV hU (u : U), ?_⟩
        invFun := fun w => ⟨CFSG.Quasithin.F2Vec.toV hU (w : CFSG.Quasithin.F2Vec U hU), ?_⟩
        left_inv := fun u => rfl
        right_inv := fun w => rfl }
    · have hu := CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp u.2
      rw [hact]
      exact congrArg (CFSG.Quasithin.F2Vec.ofV hU) hu
    · apply CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr
      have hw : ρ g₀ (CFSG.Quasithin.F2Vec.ofV hU (CFSG.Quasithin.F2Vec.toV hU
          (w : CFSG.Quasithin.F2Vec U hU))) =
          CFSG.Quasithin.F2Vec.ofV hU (CFSG.Quasithin.F2Vec.toV hU w) := w.2
      rw [hact] at hw
      exact congrArg (CFSG.Quasithin.F2Vec.toV hU) hw
  have hrkfix : rk ↥(fixV (Subgroup.zpowers t)) =
      Module.finrank (ZMod 2) (LinearMap.ker (ρ g₀ - 1)) := by
    unfold rk
    rw [hfixcard, padicValNat.prime_pow]
  have hfin := finrank_f2Vec_eq_rk hU
  have hadd := CFSG.Quasithin.rk_add_rkIdx (fixV (Subgroup.zpowers t))
  have hle := CFSG.Quasithin.E6.two_mul_rkIdx_fixV_le hU ht2
  rcases CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.finrank_le_or_orth_or (by norm_num) hF
      ρ hinj hirrρ (ρ g₀) ha2 (fun g => g₀ * g * g₀⁻¹) hτ hτ1 with h | ⟨s, hs, -⟩ | ⟨s, hs, -⟩
  · rw [hfin, ← hrkfix] at h
    omega
  · omega
  · omega

theorem rk_eq_six_or_eight_of_isL2_three {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {S : Subgroup (MulAut U)} (h3 : UC22.IsL2 ↥S 3)
    (hirr : IsIrrOn S ⊤ ⊥) (hrk : rk U ≤ 10) : rk U = 6 ∨ rk U = 8 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_sl2_of_isL2_three h3
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 3) = 2 ^ 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 3 (by norm_num)
  haveI : Fact (CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ).IsIrreducible :=
    ⟨isIrreducible_autRepOfG hU θ hirr⟩
  haveI : IsSimpleGroup ↥S :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
  have hnt : ∃ g, CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ g ≠ 1 := by
    obtain ⟨s, hs⟩ := exists_ne (1 : ↥S)
    refine ⟨θ s, fun h => hs ?_⟩
    apply θ.injective
    apply autRepOfG_injective hU θ
    rw [h, map_one, map_one]
  have hfin := finrank_f2Vec_eq_rk hU
  have hcard : Nat.card (CFSG.Quasithin.F2Vec U hU) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Quasithin.F2Vec U hU) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.natCard_eq_two_pow
  have hlt : Nat.card (CFSG.Quasithin.F2Vec U hU) < 2 ^ (4 * 3) := by
    rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt
      (by norm_num) hF (CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ) hnt
      (CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.rootSub (GaloisField 2 3))
      (fun u hu => CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.mul_self_of_mem_rootSub hu)
      (CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.natCard_rootSub.trans hF) hlt with
    ⟨φ, -⟩ | ⟨l, -, hl, -⟩ | ⟨l, hl, hW, -⟩
  · left
    have h64 : Nat.card (CFSG.Quasithin.F2Vec U hU) = 2 ^ 6 := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_fin, GaloisField.card 2 3 (by norm_num)]
      norm_num
    have := CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.finrank_eq_of_natCard h64
    omega
  · omega
  · right
    have hl1 : l = 1 := by omega
    subst hl1
    have := CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.finrank_eq_of_natCard hW
    omega

theorem exists_card_fixV_eq_two_of_isL2_three {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {S : Subgroup (MulAut U)} (h3 : UC22.IsL2 ↥S 3)
    (hirr : IsIrrOn S ⊤ ⊥) (hrk : rk U = 8) (A : Subgroup (MulAut U)) (hAS : A ≤ S)
    (hA : IsElemAbelian2 A) :
    ∃ P : Subgroup (MulAut U), A ≤ P ∧ P ≤ S ∧ IsElemAbelian2 P ∧ Nat.card P = 8 ∧
      Nat.card (fixV P) = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut U) :=
    Finite.of_injective (fun φ : MulAut U => (φ : U → U)) DFunLike.coe_injective
  obtain ⟨θ⟩ := nonempty_mulEquiv_sl2_of_isL2_three h3
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hGF : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have hF : Fintype.card (GaloisField 2 3) = 2 ^ 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hGF
  haveI : Fact (CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ).IsIrreducible :=
    ⟨isIrreducible_autRepOfG hU θ hirr⟩
  haveI : IsSimpleGroup ↥S :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
  have hnt : ∃ g, CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ g ≠ 1 := by
    obtain ⟨s, hs⟩ := exists_ne (1 : ↥S)
    refine ⟨θ s, fun h => hs ?_⟩
    apply θ.injective
    apply autRepOfG_injective hU θ
    rw [h, map_one, map_one]
  have hfin := finrank_f2Vec_eq_rk hU
  have hcard : Nat.card (CFSG.Quasithin.F2Vec U hU) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Quasithin.F2Vec U hU) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.natCard_eq_two_pow
  have hlt : Nat.card (CFSG.Quasithin.F2Vec U hU) < 2 ^ (4 * 3) := by
    rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hA' : IsPGroup 2 ↥((A.subgroupOf S).map θ.toMonoidHom) := by
    apply CFSG.Quasithin.isPGroup_two_of_sq_eq_one
    rintro ⟨_, x, hx, rfl⟩
    apply Subtype.ext
    have hx2 : x ^ 2 = 1 := Subtype.ext (hA.2 (x : MulAut U) (Subgroup.mem_subgroupOf.mp hx))
    change (θ.toMonoidHom x) ^ 2 = 1
    rw [← map_pow, hx2, map_one]
  obtain ⟨Q, hAQ⟩ := hA'.exists_le_sylow
  obtain ⟨hQe, hQ8, -⟩ := CFSG.RankThree.PartTwo.KFacts.sylow_two_sl2 Q
  rw [hGF] at hQ8
  rcases CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt
      (by norm_num) hF (CFSG.Quasithin.B45Mat.Ind.autRepOfG hU θ) hnt
      (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)))
      (fun a ha => by rw [← sq]; exact hQe.2 a ha) hQ8 hlt with
    ⟨φ, -⟩ | ⟨l, -, hl, -⟩ | ⟨l, hl, -, hfixQ⟩
  · exfalso
    have h64 : Nat.card (CFSG.Quasithin.F2Vec U hU) = 2 ^ 6 := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_fin, hGF]
      norm_num
    have := CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.finrank_eq_of_natCard h64
    omega
  · omega
  · have hl1 : l = 1 := by omega
    subst hl1
    have hPS : ((Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))).comap
        θ.toMonoidHom).map S.subtype ≤ S := Subgroup.map_subtype_le _
    have hPsub : (((Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))).comap
        θ.toMonoidHom).map S.subtype).subgroupOf S =
        (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))).comap
          θ.toMonoidHom :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
    have hPmap : ((((Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))).comap
        θ.toMonoidHom).map S.subtype).subgroupOf S).map θ.toMonoidHom =
        (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))) := by
      rw [hPsub]
      exact Subgroup.map_comap_eq_self_of_surjective θ.surjective _
    have hsqP : ∀ a ∈ ((Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))).comap
        θ.toMonoidHom).map S.subtype, a ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : θ.toMonoidHom (x ^ 2) = 1 := by
        rw [map_pow]
        exact hQe.2 _ hx
      have h2 : x ^ 2 = 1 := θ.injective (by rw [map_one]; exact h1)
      rw [← map_pow, h2, map_one]
    refine ⟨_, ?_, hPS, ⟨fun a ha b hb => ?_, hsqP⟩, ?_, ?_⟩
    · intro x hxA
      have hxS := hAS hxA
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      exact hAQ ⟨⟨x, hxS⟩, Subgroup.mem_subgroupOf.mpr hxA, rfl⟩
    · have ha2 : a * a = 1 := by rw [← sq]; exact hsqP a ha
      have hb2 : b * b = 1 := by rw [← sq]; exact hsqP b hb
      have hab2 : a * b * (a * b) = 1 := by rw [← sq]; exact hsqP _ (Subgroup.mul_mem _ ha hb)
      calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab2
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha2]
    · rw [Subgroup.card_map_of_injective S.subtype_injective]
      calc Nat.card ↥((Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))).comap
            θ.toMonoidHom) =
            Nat.card ↥(Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))) :=
            Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv (fun x => Iff.rfl))
        _ = 8 := by rw [hQ8]; norm_num
    · rw [natCard_fixV_eq_autRepOfG hU θ hPS, hPmap]
      rw [pow_one] at hfixQ
      exact (Nat.card_congr (Equiv.subtypeEquivRight fun w =>
        CFSG.QuasithinUnique.Setup.X7.mem_fixedSub.symm)).trans hfixQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

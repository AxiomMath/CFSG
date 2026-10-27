module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofTools
public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofG2
public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofAutCent
public import CFSG.RankThree.PartTwo.Sec21.ThreeLocalSporProofKS611
import CFSG.RankThree.PartTwo.Sec6.Item66Used
import CFSG.RankThree.PartTwo.Sec12.Item125Act
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofUPlus

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res611Fix

@[expose] def centerQuotAut (X : Type) [Group X] :
    MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun α := QuotientGroup.congr (Subgroup.center X) (Subgroup.center X) α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem centerQuotAut_mk {X : Type} [Group X] (α : MulAut X) (x : X) :
    centerQuotAut X α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  rfl

theorem centerQuotAut_conj {X : Type} [Group X] (l : X) :
    centerQuotAut X (MulAut.conj l) = MulAut.conj (QuotientGroup.mk l : X ⧸ Subgroup.center X) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x => rfl

theorem eq_one_of_centerQuotAut_eq_one {X : Type} [Group X] [Group.IsPerfect X]
    {β : MulAut X} (h : centerQuotAut X β = 1) : β = 1 := by
  have hc : ∀ x : X, β x * x⁻¹ ∈ Subgroup.center X := by
    intro x
    have h1 := congrArg (fun γ : MulAut (X ⧸ Subgroup.center X) => γ (QuotientGroup.mk x)) h
    simp only [centerQuotAut_mk, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    have h3 := Subgroup.inv_mem _ h2
    rw [mul_inv_rev, inv_inv] at h3
    have h4 := (inferInstance : (Subgroup.center X).Normal).conj_mem _ h3 x
    rwa [show x * (x⁻¹ * β x) * x⁻¹ = β x * x⁻¹ by group] at h4
  let _ : CommGroup (Subgroup.center X) :=
    { (inferInstance : Group (Subgroup.center X)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  let φ : X →* Subgroup.center X :=
    { toFun := fun x => ⟨β x * x⁻¹, hc x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change β (x * y) * (x * y)⁻¹ = (β x * x⁻¹) * (β y * y⁻¹)
        have hy := Subgroup.mem_center_iff.mp (hc y) (β x)
        calc β (x * y) * (x * y)⁻¹ = β x * (β y * y⁻¹) * x⁻¹ := by rw [map_mul]; group
          _ = (β y * y⁻¹) * β x * x⁻¹ := by rw [← hy]
          _ = (β y * y⁻¹) * (β x * x⁻¹) := by group
          _ = (β x * x⁻¹) * (β y * y⁻¹) :=
            Subgroup.mem_center_iff.mp (hc y) _ |>.symm }
  have hφ : ∀ x, φ x = 1 := by
    have hp : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have hs : Subsingleton φ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
    intro x
    have := Subsingleton.elim (⟨φ x, x, rfl⟩ : φ.range) 1
    exact congrArg Subtype.val this
  ext x
  have h1 := congrArg Subtype.val (hφ x)
  change β x * x⁻¹ = 1 at h1
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h1

variable {G : Type} [Group G] [Finite G]

theorem false_of_coverCase_plus (hK2 : KS611G2AutCent) {A E L T : Subgroup G} {c : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hEA : E ≤ A) (hE27 : Nat.card E = 27)
    (hcE : c ∈ E) (hc1 : c ≠ 1) (hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c)
    (hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hTN : T ≤ Subgroup.normalizer (L : Set G))
    (hTC : T ≤ Subgroup.centralizer (E : Set G)) (hTab : CFSG.Assembly.IsElemAbelian 2 T)
    (hT4 : Nat.card T = 4) (hTθ : T ⊓ thetaQuotCentralizer L = ⊥)
    (hcase : Item611CoverCase A L c) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hM, hinner⟩ := hcase
  set Lb := L ⧸ aschbacherSolvableCore 3 L with hLb
  have : Group.IsPerfect Lb := hq.1
  set N := Subgroup.normalizer (L : Set G) with hN
  set γ : N →* MulAut (Lb ⧸ Subgroup.center Lb) :=
    (centerQuotAut Lb).comp (Res611Res4.thetaAct L) with hγ
  have hkerγ : ∀ x : N, γ x = 1 → (x : G) ∈ thetaQuotCentralizer L := by
    intro x hx
    have h1 : Res611Res4.thetaAct L x = 1 := eq_one_of_centerQuotAut_eq_one hx
    exact (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct x.2).mpr h1
  set F := (E.subgroupOf N).map γ with hF
  set V := (T.subgroupOf N).map γ with hV
  have hFi : F ≤ (MulAut.conj : Lb ⧸ Subgroup.center Lb →* MulAut _).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ha, l, hl⟩ := hinner (x : G) (hEA (Subgroup.mem_subgroupOf.mp hx))
    have hx' : x = ⟨(x : G), ha⟩ := rfl
    refine ⟨QuotientGroup.mk (l : Lb), ?_⟩
    rw [hx', hγ, MonoidHom.comp_apply, hl, centerQuotAut_conj]
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := Sec5.isElemAbelian_of_le hAe hEA
  have hEN : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf N) := by
    refine Item434Kit.isElemAbelian_of_map_injective N.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hEL]
    exact hEe
  have hFe : CFSG.Assembly.IsElemAbelian 3 F :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 γ _ hEN
  have hF9 : 9 ≤ Nat.card F := by
    set f : E.subgroupOf N →* MulAut (Lb ⧸ Subgroup.center Lb) :=
      γ.comp (E.subgroupOf N).subtype with hf
    have hrange : f.range = F := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : Nat.card f.ker ≤ 3 := by
      have hmem : ∀ k : f.ker, (((k : E.subgroupOf N) : N) : G) ∈ Subgroup.zpowers c := by
        intro k
        rw [← hCA]
        exact ⟨hEA (Subgroup.mem_subgroupOf.mp (k : E.subgroupOf N).2), hkerγ _ k.2⟩
      have hinj : Function.Injective
          (fun k : f.ker => (⟨(((k : E.subgroupOf N) : N) : G), hmem k⟩ : Subgroup.zpowers c)) := by
        intro k k' h
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        simpa using congrArg Subtype.val h
      have h1 := Nat.card_le_card_of_injective _ hinj
      rwa [Nat.card_zpowers, orderOf_eq_prime (hAe.2 c (hEA hcE)) hc1] at h1
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h1
    have hEN27 : Nat.card (E.subgroupOf N) = 27 := by
      rw [← hE27]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
    rw [hEN27] at h1
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card F * Nat.card f.ker ≤ 8 * 3 := Nat.mul_le_mul (by omega) hker
    omega
  have hTN' : CFSG.Assembly.IsElemAbelian 2 (T.subgroupOf N) := by
    refine Item434Kit.isElemAbelian_of_map_injective N.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hTN]
    exact hTab
  have hVe : CFSG.Assembly.IsElemAbelian 2 V :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 2 γ _ hTN'
  have hV4 : Nat.card V = 4 := by
    have hker : T.subgroupOf N ⊓ γ.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyT, hyk⟩
      have hyC := hkerγ y hyk
      have hmem : (y : G) ∈ T ⊓ thetaQuotCentralizer L :=
        ⟨Subgroup.mem_subgroupOf.mp hyT, hyC⟩
      rw [hTθ, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
    rw [hV, card_map_of_inf_ker_eq_bot γ hker, ← hT4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hcomm : ∀ f ∈ F, ∀ v ∈ V, f * v = v * f := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (x : G) * y = y * x
    exact Subgroup.mem_centralizer_iff.mp (hTC (Subgroup.mem_subgroupOf.mp hy)) (x : G)
      (Subgroup.mem_subgroupOf.mp hx)
  have h := hK2 _ hM F V hFi hFe hF9 hVe hcomm
  rw [hV4] at h
  omega

end Res611Fix

open Res611Res4

section Certs

theorem item611UPlusCent_of_res4Fix (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (hK : KS611CentChar3) : Item611UPlusCent := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTN hTθ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  obtain ⟨hEmem, hEA⟩ := hE
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := hEmem.1
  have hE27 : Nat.card E = 27 := hEmem.2.1
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEe
  obtain ⟨hTU, hTE⟩ := hT
  obtain ⟨hET, hTab, hT4⟩ := mem_fourGroups_iff.mp hTU
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hT4
    omega
  have hTC : T ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTE
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hL
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hcA hc1 L hLc
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans hAL
  have hETL : E ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le hEL hTN
  have hθodd := Res611Res3.odd_card_theta_of_config h45 hst hA hrank hcA hc1 hLc
  have h642 : ∀ R : Subgroup G, IsPGroup 3 R → E ⊔ T ≤ Subgroup.normalizer (R : Set G) →
      R ≤ Subgroup.centralizer (T : Set G) := fun R hR3 hRN =>
    rank3II_6_4_2 G hst E hEmem T ⟨hTU, hTE⟩ T hTU.1 le_rfl R
      ((mem_invariantPiSubgroups_piOf_iff Nat.prime_three).mpr ⟨le_top, hR3, hRN⟩)
  have hfin : ∀ P : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 P →
      81 ≤ Nat.card P → E ⊔ T ≤ invG L P → False := fun P hPe h81 hinv =>
    false_of_invariant_elemAbelian hst.evenRank_eq hθodd hE3 hT2 hT1 hET hETL h642 hPe h81 hinv
  have hfix : ∀ P : Subgroup (L ⧸ aschbacherSolvableCore 3 L), IsPGroup 3 P →
      E ⊔ T ≤ invG L P → T ≤ fixG L P := fun P hP hinv =>
    le_fixG_of_invariant hθodd hE3 hT2 hET hETL h642 hP hinv
  have hcE : c ∈ E := mem_of_mem_thetaComponentFamily hAe hEA hc1 hCA hLE
  obtain ⟨k, hk5, hAcard⟩ := Sec4.exists_card_eq_of_four_lt_pRank hAe hrank
  have h243 : 243 ≤ Nat.card A := by
    rw [hAcard]
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
  rcases Res611Fix.cases413 h45 h41 h413 hst hA hrank hcA hc1 hL hCA with
    ⟨-, -, m, hm, ⟨φ⟩, -⟩ | ⟨hAL', K, hKn, hKdef, hK2⟩ | ⟨hdec, -, hK3⟩ | hcase
  ·
    exact false_of_field hEA hEe hE27 hc1 hcA hAe hCA hEL hETL hTC hfin hm φ
  ·
    have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime (hAe.2 c hcA) hc1, pow_one])
    have hKcard : Nat.card K = 3 := by
      rw [hKdef, card_map_mk_of_isPGroup hc3 (Subgroup.zpowers_le.mpr (hAL' hcA)),
        Nat.card_zpowers, orderOf_eq_prime (hAe.2 c hcA) hc1]
    have hEL' : E ⊓ L = E := inf_of_le_left (hEA.trans hAL')
    exact false_of_char3 hAe hEA hEe hEL hETL hTC hTab hfin hfix
      (hK _ (Or.inl ⟨K, hKn, hKcard, hK2⟩)) (by rw [hEL', hE27]; norm_num) hAL' le_rfl
      (by omega)
  ·
    have hAle := Res611Res3.card_le_three_mul_card_inf hAe hcA hc1 hdec
    have hEdec := eq_sup_inf_of_eq_sup hEA hAL hcE hdec
    have hEle := Res611Res3.card_le_three_mul_card_inf hEe hcE hc1 hEdec
    exact false_of_char3 hAe hEA hEe hEL hETL hTC hTab hfin hfix (hK _ (Or.inr hK3))
      (by omega) inf_le_right inf_le_left (by omega)
  ·
    have hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := by
      obtain ⟨L', hL', hLL'⟩ := hLc
      rw [← hLL']
      exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ L') hL'.2.2
    exact Res611Fix.false_of_coverCase_plus ks611G2AutCent_holds hAe hEA hE27 hcE hc1 hCA hq hEL
      hTN hTC hTab hT4 hTθ hcase

theorem item611UPlusCent_of_threeLocalFix
    (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (hL : KCentCharThreeL43) (hU : KCentCharThreeU43) :
    Item611UPlusCent :=
  item611UPlusCent_of_res4Fix h45 h41 h413 (ks611CentChar3_of hL hU)

theorem Res611Fix.false_of_mem_fourGroupsPlus (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h49 : Sec4.Item4_9) (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (hC : Item611UPlusCent) {G : Type} [Group G] [Finite G]
    (hst : PartTwoStanding G) {A : Subgroup G} (hA : A ∈ partTwoS G)
    (hrank : 4 < CFSG.Open.pRank 3 A) {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) {L : Subgroup G}
    (hL : L ∈ lZeroStarAt A c) (hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c)
    {E : Subgroup G} (hE : E ∈ collectionIn (partTwoE G) A) (hLE : L ∈ thetaComponentFamily 3 E)
    {T : Subgroup G} (hT : T ∈ fourGroupsPlus E) : False := by
  have hTN : T ≤ Subgroup.normalizer (L : Set G) :=
    rank3II_6_8_of_used h45 h48 h49 hKf G hst A hA E hE L ⟨hLE, hL.2.2⟩ T hT
  have hTθ : T ⊓ thetaQuotCentralizer L = ⊥ :=
    Res611Fix.inf_thetaQuotCentralizer_eq_bot h45 h41 h413 hst hA hrank hcA hc1 hL hCA
      (mem_fourGroups_iff.mp hT.1).2.1
  exact hC G hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTN hTθ

theorem item611UPlusOut_ofFix (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (hC : Item611UPlusCent) : Item611UPlusOut :=
  fun _ _ _ hst _ hA hrank _ hcA hc1 _ hL hCA _ hE hLE _ hT =>
    Res611Fix.false_of_mem_fourGroupsPlus h45 h48 h49 hKf h41 h413 hC hst hA hrank hcA hc1 hL
      hCA hE hLE.1 hT

end Certs

end CFSG.RankThree.PartTwo.Sec6

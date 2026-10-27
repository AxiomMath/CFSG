module

public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofComp
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec6.BThreeFromLBalance
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofOuter
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.RankThree.PartTwo.Sec4.T444.Lift
import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step143HJCompRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb → Subgroup.zpowers a ≠ Subgroup.zpowers d →
        ∀ X ∈ thetaComponentsAt 3 a, lB A B ≤ X → CFSG.Open.pRank 3 (X ⊔ A) ≤ 3

@[expose] def Step143HJObs : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb → Subgroup.zpowers a ≠ Subgroup.zpowers d →
        ∀ X ∈ thetaComponentsAt 3 a, lB A B ≤ X →
          ¬ Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def Step143HJCompM24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb → Subgroup.zpowers a ≠ Subgroup.zpowers d →
        ∀ X ∈ thetaComponentsAt 3 a, lB A B ≤ X →
          ¬ Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* CFSG.Blueprint.NativeSporadic.M24)

namespace Desc143X

open Main148 HJRes148

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isE27_subgroupOf {Γ : Type*} [Group Γ] {A C : Subgroup Γ} (hAC : A ≤ C)
    (hA : Late.IsE27 A) : Late.IsE27 (A.subgroupOf C) := by
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
  · have h := congrArg Subtype.val
      (hA.1.1.is_comm.comm ⟨((x : ↥C) : Γ), x.2⟩ ⟨((y : ↥C) : Γ), y.2⟩)
    simpa using h
  · simpa using hA.1.2 _ hx
  · rw [← hA.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv

theorem card_le_three_of_le_center {Γ : Type} [Group Γ] [Finite Γ] {K E : Subgroup Γ}
    (hEK : E ≤ K ⊓ Subgroup.centralizer (K : Set Γ)) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K)) = 3) :
    Nat.card E ≤ 3 := by
  set θ := aschbacherSolvableCore 3 ↥K with hθdef
  have hθn : θ.Normal := by
    obtain ⟨-, hc, -, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
    have := hc
    exact Subgroup.normal_of_characteristic θ
  set E' := E.subgroupOf K with hE'
  have hE'card : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEK.trans inf_le_left)).toEquiv
  have hinj : ∀ x ∈ E', QuotientGroup.mk' θ x = 1 → x = 1 := by
    intro x hx h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact eq_one_of_mem_aschbacherSolvableCore h1 (Subtype.ext (by simpa using hE3 _ hx))
  have hmap := card_map_eq_of_ker148 hinj
  have hle : E'.map (QuotientGroup.mk' θ) ≤ Subgroup.center (↥K ⧸ θ) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective θ w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hEK (Subgroup.mem_subgroupOf.mp hx)).2 (y : Γ) y.2
  calc Nat.card E = Nat.card E' := hE'card.symm
    _ = Nat.card (E'.map (QuotientGroup.mk' θ)) := hmap.symm
    _ ≤ Nat.card (Subgroup.center (↥K ⧸ θ)) := Subgroup.card_le_of_le hle
    _ = 3 := hZ

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem nonempty_quotTheta_equiv_img148 {X : Subgroup G} (hX : X ∈ thetaComponentsIn Y)
    (h3 : 3 ∣ Nat.card X) :
    Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* ↥(img148 A Y X)) := by
  obtain ⟨hXY, hX'⟩ := mem_thetaComponentsIn_iff.mp hX
  set J' := X.subgroupOf Y with hJ'def
  have h3' : 3 ∣ Nat.card J' := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv]
  have heq := Sec4.inf_pPrimeCore_eq_of_mem_thetaComponents hX' h3'
  set φ : ↥Y →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion le_sup_left) with hφ
  have hker : ∀ y : ↥Y, φ y = 1 ↔ y ∈ CFSG.pPrimeCore 3 ↥Y := by
    intro y
    change QuotientGroup.mk' (ker148 A Y) (Subgroup.inclusion le_sup_left y) = 1 ↔ _
    rw [mk'_ker148_eq_one_iff, Subgroup.coe_inclusion, pPrimeCoreOf, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hM : ∀ l : ↥J', l ∈ aschbacherSolvableCore 3 ↥J' ↔ φ (l : ↥Y) = 1 := by
    intro l
    rw [hker]
    constructor
    · intro hl
      have h1 : (l : ↥Y) ∈ inSubgroup (aschbacherSolvableCore 3) J' := ⟨l, hl, rfl⟩
      rw [← heq] at h1
      exact h1.2
    · intro hl
      have h1 : (l : ↥Y) ∈ J' ⊓ CFSG.pPrimeCore 3 ↥Y := ⟨l.2, hl⟩
      rw [heq] at h1
      obtain ⟨l', hl', he⟩ := h1
      rwa [← Subtype.ext he]
  obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map φ J' (aschbacherSolvableCore 3 ↥J') hM
  have hmap : J'.map φ = img148 A Y X := by
    ext x
    rw [Subgroup.mem_map, mem_img148_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (le_sup_left : Y ≤ Y ⊔ A) y.2, hy, rfl⟩
    · rintro ⟨g, hg, hgX, rfl⟩
      exact ⟨⟨g, hXY hgX⟩, hgX, rfl⟩
  exact ⟨(quotThetaEquiv (Subgroup.subgroupOfEquivOfLe hXY)).symm.trans
    (η.trans (MulEquiv.subgroupCongr hmap))⟩

theorem eq_sup_theta_of_img148_eq {X T : Subgroup G} (hX : X ∈ thetaComponentsIn Y)
    (h3 : 3 ∣ Nat.card X) (hXM : X ≤ Y ⊔ A) (hTX : T ≤ X)
    (heq : img148 A Y T = img148 A Y X) :
    X = T ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  obtain ⟨hXY, hX'⟩ := mem_thetaComponentsIn_iff.mp hX
  have h3' : 3 ∣ Nat.card (X.subgroupOf Y) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv]
  have hθeq := Sec4.inf_pPrimeCore_eq_of_mem_thetaComponents hX' h3'
  have hO : ∀ x ∈ X, x ∈ pPrimeCoreOf 3 Y → x ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    intro x hx hxO
    obtain ⟨y, hy, hyx⟩ := hxO
    have hyx' : (y : G) = x := hyx
    have hyX : y ∈ X.subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf, hyx']
      exact hx
    have h1 : y ∈ inSubgroup (aschbacherSolvableCore 3) (X.subgroupOf Y) :=
      hθeq ▸ (⟨hyX, hy⟩ : y ∈ X.subgroupOf Y ⊓ CFSG.pPrimeCore 3 ↥Y)
    obtain ⟨z, hz, hzy⟩ := h1
    set e := Subgroup.subgroupOfEquivOfLe hXY with he
    have hz' : e z ∈ aschbacherSolvableCore 3 ↥X := by
      rw [← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e]
      exact ⟨z, hz, rfl⟩
    refine ⟨e z, hz', ?_⟩
    rw [← hyx', ← hzy]
    rfl
  apply le_antisymm
  · intro x hx
    have hxα : QuotientGroup.mk' (ker148 A Y) ⟨x, hXM hx⟩ ∈ img148 A Y T :=
      heq ▸ mem_img148_iff.mpr ⟨x, hXM hx, hx, rfl⟩
    obtain ⟨t, ht, htT, hteq⟩ := mem_img148_iff.mp hxα
    have hto : t⁻¹ * x ∈ pPrimeCoreOf 3 Y := mk'_ker148_eq_iff.mp hteq
    have htx : t⁻¹ * x ∈ inSubgroup (aschbacherSolvableCore 3) X :=
      hO _ (X.mul_mem (X.inv_mem (hTX htT)) hx) hto
    have hxe : x = t * (t⁻¹ * x) := by group
    rw [hxe]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htT) (Subgroup.mem_sup_right htx)
  · exact sup_le hTX (Subgroup.map_subtype_le _)

end Quot

namespace One

variable {A L B Lb : Subgroup G} {c a b d : G}

theorem closure_d_a (h : One A c L a b d B Lb) : Subgroup.closure {d, a} = B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.std.isE27'
  obtain ⟨-, hd1⟩ := h.config.ne_one h.hyp hA
  have hdB : d ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  refine closure_pair_eq_of_not_mem hA h.hyp hdB h.mem_hyp hd1 fun had => ?_
  have hod : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d (h.hyp.1 hdB)) hd1
  have hoa : orderOf a = 3 := orderOf_eq_prime (hA.1.2 a h.mem) h.ne_one
  exact h.ne_d (zpowers_eq_of_mem hoa hod had)

theorem lB_mem (h : One A c L a b d B Lb) :
    lB A B ∈ thetaComponentsIn
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have h1 := Item148HJ.residual_mem_thetaComponentsIn h.std h.hyp h.config
  have h2 : Subgroup.centralizer (B : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
    have h3 := Main148.centralizer_closure_pair148 d a
    rw [h.closure_d_a, inf_comm] at h3
    exact h3
  rw [h.lB_eq, ← h2]
  exact h1

end One

theorem eq_sup_theta (h425 : Sec4.Item4_25Fix) (h41 : Sec4.Item4_1LargePrime)
    (hGW : Sec6.GWLBalanceStatement) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hR : Step143HJCompRank) (hO : Step143HJObs) (hM : Step143HJCompM24)
    {A L B Lb : Subgroup G} {c a b d : G} (h : One A c L a b d B Lb) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 a) (hJX : lB A B ≤ X) :
    X = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA := h.std.isE27'
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  obtain ⟨-, hd1⟩ := h.config.ne_one h.hyp hA
  have hdB : d ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := h.hyp.1 hdB
  have hd3 : d ^ 3 = 1 := hA3 d hdA
  set J := lB A B with hJdef
  have hJeq : J = inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) :=
    h.lB_eq
  set Y := Subgroup.centralizer ({a} : Set G) with hYdef
  have hAY' : A ≤ Y := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨a, h.mem⟩))
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hAY'.trans Subgroup.le_normalizer
  let := ker148_normal hAY
  have hYA : Y ⊔ A = Y := sup_of_le_left hAY'
  have hYtop : Y ≠ ⊤ := centralizer_singleton_ne_top h.std.isSimpleGroup h.std.nonabelian h.ne_one
  have hYsc : Y ∈ scriptY A := ⟨hYtop, hAY⟩
  have hX' : X ∈ thetaComponentsIn Y := hX
  have hXY : X ≤ Y := le_of_mem_thetaComponentsIn hX'
  have hXM : X ≤ Y ⊔ A := hXY.trans le_sup_left
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hAY'.trans (h.le_normalizer hX hJX)
  obtain ⟨hdL, S, hdS, hSd⟩ := h.config.2.2.2.2
  have hdJ : d ∈ J := hJeq ▸ Item148HJ.inf_le_residual h.std h.hyp h.config ⟨hdA, hdL⟩
  have hod : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have h3J : 3 ∣ Nat.card J := by
    rw [← hod, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hdJ)
  have h3X : 3 ∣ Nat.card X := h3J.trans (Subgroup.card_dvd_of_le hJX)
  have hXs : ¬ Group.IsSolvable ↥Y := by
    intro hYs
    have hXs' : Group.IsSolvable ↥X :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXY)
    have : Nontrivial ↥X := ⟨⟨⟨d, hJX hdJ⟩, 1, fun h1 => hd1 (congrArg Subtype.val h1)⟩⟩
    exact Sec4.Item419ThetaProof.not_isSolvable_of_isPerfect
      (isPerfect_of_mem_thetaComponentsIn hX') hXs'
  obtain ⟨hC4, -⟩ := hyp429In148_of h41 G A c L h.std Y hYsc hXs X hX' hAX h3X
  obtain ⟨hXq, hXθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hX' h3X
  set C := img148 A Y (X ⊔ A) with hCdef
  have hCeq : C = img148 A Y X ⊔ img148 A Y A := img148_sup hXM le_sup_right
  have hAαXα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y X : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAX
  have hAα3 : ∀ x ∈ img148 A Y A, x ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥C = ⊥ := by
    rw [hCeq]
    exact aschbacherSolvableCore_sup_eq_bot hAαXα hAα3 hXθ
  have hAC : img148 A Y A ≤ C := img148_mono le_sup_right
  have hLC : img148 A Y X ≤ C := img148_mono le_sup_left
  have hLn : C ≤ Subgroup.normalizer (img148 A Y X : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαXα
  have hCr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) = 3 := by
    apply le_antisymm
    · have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
        Nat.prime_three C.subtype C.subtype_injective ⊤
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      have h2 := Sec4.pRank_map_le_of_not_dvd Nat.prime_three (QuotientGroup.mk' (ker148 A Y))
        (by rw [QuotientGroup.ker_mk']; exact not_three_dvd_card_ker148)
        ((X ⊔ A).subgroupOf (Y ⊔ A))
      have h3 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
        Nat.prime_three (Y ⊔ A).subtype (Y ⊔ A).subtype_injective ((X ⊔ A).subgroupOf (Y ⊔ A))
      rw [Subgroup.map_subgroupOf_eq_of_le (sup_le hXM le_sup_right)] at h3
      have h4 := hR G A c L h.std a h.mem h.ne_one h.not_mem_omegaA B b d Lb h.hyp h.mem_hyp
        h.config h.ne_d X hX hJX
      exact h1.trans (h2.trans (h3.trans h4))
    · have hE := isE27_subgroupOf hAC (img148_isE27 hA)
      refine le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3
        Nat.prime_three ⊤) ⟨(img148 A Y A).subgroupOf C, le_top, hE.1, ?_⟩
      rw [hE.2]
      norm_num
  have hYd := h.lB_mem
  have hM4 : SectionFourHyp ↥(Y ⊔ A) :=
    h.std.toTheoremFourHyp.sectionFourHyp (by rw [hYA]; exact hYtop)
  have hθ := theta_commutator_le hGW hAY hM4 hdA hd3 hYd hX' hJX h3J
  obtain ⟨hKle, hKsub, hKp, hKθ, ⟨η⟩⟩ := ydAlpha_facts hAY hdA hd3 hYd hX' hJX hAX h3J hθ
  have hJ2 := Item148HJ.j2_of_isLBConfig h.config
  obtain ⟨-, htc, -, -⟩ := residual_facts h415 hJ2 hdL hd1 ⟨S, hdS, hSd⟩
  rw [← hJeq] at htc
  have htcα := KFacts.KS14.isTripleCover_congr η htc
  have hKq' : IsQuasisimple (↥(img148 A Y J) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y J)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv η (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd)
  have : Group.IsPerfect ↥(img148 A Y J) := hKp
  have hKq : IsQuasisimple ↥(img148 A Y J) :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective inferInstance
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(img148 A Y J)))
      (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])).mpr hKq'
  have hdα1 : alpha148 A Y d hdA ≠ 1 := alpha148_ne_one hdA hd1 hd3
  have hdα3 : alpha148 A Y d hdA ^ 3 = 1 := hAα3 _ (alpha148_mem_img148 hdA)
  have hJd : J ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hJeq]
    exact Item148HJ.residual_le_centralizer_singleton Lb d
  have hcent : img148 A Y A ⊓ (img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) =
      Subgroup.zpowers (alpha148 A Y d hdA) := by
    have hle : Subgroup.zpowers (alpha148 A Y d hdA) ≤ img148 A Y A ⊓ (img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) := by
      rw [Subgroup.zpowers_le]
      refine ⟨alpha148_mem_img148 hdA, mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdJ,
        rfl⟩, ?_⟩
      show alpha148 A Y d hdA ∈
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨j, hj, hjJ, rfl⟩ := mem_img148_iff.mp hx
      rw [alpha148_eq_mk', ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hJd hjJ)
    have hcard := card_le_three_of_le_center (E := img148 A Y A ⊓ (img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))) inf_le_right
      (fun x hx => hAα3 x hx.1) htcα.1
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime hdα3 hdα1]
    exact hcard
  have hW := normalizer_le_normalizer_zpowers_d h134 h48 h.std h.hyp h.config
  have hW' : ∀ g ∈ C, g ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      g ∈ Subgroup.normalizer
        (Subgroup.zpowers (alpha148 A Y d hdA) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun g _ hg => mem_normalizer_alpha_of (isPGroup_three_of_pow148 hA3) hdA hW hg
  obtain ⟨ηX⟩ := nonempty_quotTheta_equiv_img148 (A := A) (Y := Y) hX' h3X
  rcases item4_25Fix_of_le h425 C hC4 hCr hCθ hAC hLC (img148_isE27 hA) hW' hXq hLn hKle hKq
      hKsub htcα.isExtOf hcent with h1 | ⟨⟨φ⟩⟩ | ⟨p, f, hSL⟩ | ⟨⟨φ⟩⟩ | h7
  · exact eq_sup_theta_of_img148_eq hX' h3X hXM hJX h1
  · exact (hO G A c L h.std a h.mem h.ne_one h.not_mem_omegaA B b d Lb h.hyp h.mem_hyp h.config
      h.ne_d X hX hJX ⟨ηX.trans φ⟩).elim
  · exact (false_of_isSLThreePiAt hKθ htcα.isExtOf hSL).elim
  · exact (hM G A c L h.std a h.mem h.ne_one h.not_mem_omegaA B b d Lb h.hyp h.mem_hyp h.config
      h.ne_d X hX hJX ⟨ηX.trans φ⟩).elim
  · exact (false_of_isExtOf_seven htcα.isExtOf h7).elim

end Desc143X

theorem step143HJCompOne_of (h425 : Sec4.Item4_25Fix) (h41 : Sec4.Item4_1LargePrime)
    (hGW : Sec6.GWLBalanceStatement) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hR : Step143HJCompRank) (hO : Step143HJObs) (hM : Step143HJCompM24) :
    Step143HJCompOne := by
  intro G _ _ A c L h a ha ha1 hΩ B b d Lb hB haB hc hne X hX hJX
  exact Desc143X.eq_sup_theta h425 h41 hGW h134 h48 hR hO hM
    ⟨h, ha, ha1, hΩ, hB, haB, hc, hne⟩ hX hJX

namespace Desc143X

theorem card_quotTheta_eq {G : Type} [Group G] [Finite G] {A L B Lb : Subgroup G} {c a b d : G}
    (h : One A c L a b d B Lb) {X : Subgroup G} (hJX : lB A B ≤ X)
    (hXeq : X = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 1080 := by
  obtain ⟨-, hd1⟩ := h.config.ne_one h.hyp h.std.isE27'
  obtain ⟨hdL, S, hdS, hSd⟩ := h.config.2.2.2.2
  obtain ⟨-, htc, -, -⟩ := residual_facts Sec4.Sporadic.rank3II_4_15
    (Item148HJ.j2_of_isLBConfig h.config) hdL hd1 ⟨S, hdS, hSd⟩
  rw [← h.lB_eq] at htc
  obtain ⟨η⟩ := nonempty_quotTheta_equiv_of_eq_sup hJX hXeq
  rw [← Nat.card_congr η.toEquiv]
  exact card_eq_of_isTripleCover_six htc

end Desc143X

end CFSG.RankThree.PartTwo.Sec14

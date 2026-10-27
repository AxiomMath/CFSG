module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeG0
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal
import CFSG.GroupTheory.Fitting.SelfCentralizingComponent
import CFSG.GroupTheory.Fitting.MulEquiv
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAsc1411

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

namespace AscBridge

variable {G : Type} [Group G] [Finite G]

theorem sup_eq_top_of_map_mk'_eq_top {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal]
    {H : Subgroup Γ} (h : H.map (QuotientGroup.mk' N) = ⊤) : H ⊔ N = ⊤ := by
  rw [← QuotientGroup.ker_mk' N, ← Subgroup.comap_map_eq, h, Subgroup.comap_top]

section Cover

variable {M X T : Subgroup G} {c : G} {G₀ : Subgroup G}

theorem exists_mulEquiv_of_minimal (hG₀ : Minimal (CoverYR M X T c) G₀) :
    ∃ Ψ : (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) ≃*
        (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
          CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))),
      ∀ g : ↥G₀, Ψ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀) g) =
        QuotientGroup.mk' _ (Subgroup.inclusion hG₀.prop.2.1 g) := by
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set YR := yTwenty X c ⊔ R with hYRdef
  set K₀ := oThreePrimeYR M X T c with hK₀def
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  have hGYR : G₀ ≤ YR := hG₀.prop.2.1
  have hcov : G₀ ⊔ K₀ = YR := hG₀.prop.2.2
  set Φ : ↥G₀ →* ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR := π.comp (Subgroup.inclusion hGYR) with hΦ
  have hGK₀ : G₀ ≤ Subgroup.normalizer (K₀ : Set G) :=
    hGYR.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 YR)
  have hΦs : Function.Surjective Φ := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hx : (x : G) ∈ ((G₀ : Set G) * (K₀ : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right G₀ K₀ hGK₀, hcov]
      exact x.2
    obtain ⟨g, hg, k, hk, hgk⟩ := hx
    obtain ⟨k', hk', hk'k⟩ := Subgroup.mem_map.mp hk
    refine ⟨⟨g, hg⟩, ?_⟩
    have hxe : x = Subgroup.inclusion hGYR ⟨g, hg⟩ * k' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      rw [← hgk]
      exact congrArg _ hk'k.symm
    have hk1 : π k' = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk'
    rw [hΦ, MonoidHom.comp_apply, hxe, map_mul, hk1, mul_one]
  have hO := inSubgroup_pPrimeCore_eq_of_minimal hG₀
  have hΦker : Φ.ker = CFSG.pPrimeCore 3 ↥G₀ := by
    ext g
    rw [MonoidHom.mem_ker, hΦ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have h2 : (g : G) ∈ G₀ ⊓ K₀ := ⟨g.2, ⟨_, h, rfl⟩⟩
      have h2' : (g : G) ∈ inSubgroup (CFSG.pPrimeCore 3) G₀ := by
        rw [hO]
        exact h2
      obtain ⟨g', hg', hg'g⟩ := h2'
      have hgg : g' = g := Subtype.ext hg'g
      rw [← hgg]
      exact hg'
    · intro h
      have h2 : (g : G) ∈ inSubgroup (CFSG.pPrimeCore 3) G₀ := ⟨g, h, rfl⟩
      rw [hO] at h2
      obtain ⟨y, hy, hyg⟩ := h2.2
      have hyi : Subgroup.inclusion hGYR g = y := Subtype.ext hyg.symm
      rw [hyi]
      exact hy
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hΦker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Φ hΦs), fun g => rfl⟩

theorem map_map_subgroupOf_of_minimal (hG₀ : Minimal (CoverYR M X T c) G₀)
    {Ψ : (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) ≃*
        (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
          CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))}
    (hΨ : ∀ g : ↥G₀, Ψ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀) g) =
        QuotientGroup.mk' _ (Subgroup.inclusion hG₀.prop.2.1 g))
    {U : Subgroup G} (hU : U ≤ G₀) :
    ((U.subgroupOf G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))).map Ψ.toMonoidHom =
      (U.subgroupOf (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3
          ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))) := by
  ext z
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨Subgroup.inclusion hG₀.prop.2.1 s, hs, (hΨ s).symm⟩
  · rintro ⟨x, hx, rfl⟩
    have hxU : (x : G) ∈ U := hx
    refine ⟨QuotientGroup.mk' _ ⟨x, hU hxU⟩, ⟨⟨x, hU hxU⟩, hxU, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hΨ]
    rfl

end Cover

section YAlpha

variable {M X T : Subgroup G} {c : G}

theorem yAlpha_normal_and_sup_eq_top
    (hRY : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (yTwenty X c : Set G)) :
    (yAlpha M X T c).Normal ∧
      yAlpha M X T c ⊔ ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf
        (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map (QuotientGroup.mk'
          (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))) = ⊤ := by
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  have hYRY : YR ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hRY
  have hYn : (Y.subgroupOf YR).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hYRY
  refine ⟨hYn.map _ (QuotientGroup.mk'_surjective _), ?_⟩
  rw [yAlpha, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem isPGroup_quotient_yAlpha
    (hRY : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (yTwenty X c : Set G)) :
    haveI := (yAlpha_normal_and_sup_eq_top hRY).1
    IsPGroup 2 ((↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
      CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) ⧸
        yAlpha M X T c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hYbn, hsup⟩ := yAlpha_normal_and_sup_eq_top hRY
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set YR := yTwenty X c ⊔ R with hYRdef
  set Yb := yAlpha M X T c with hYbdef
  set Rb := (R.subgroupOf YR).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR)) with hRbdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRb2 : IsPGroup 2 Rb := (hR2.comap_subtype (K := YR)).map _
  refine hRb2.of_surjective ((QuotientGroup.mk' Yb).comp Rb.subtype) ?_
  intro q
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Yb q
  have hw : w ∈ ((Yb : Set (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)) *
      (Rb : Set (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR))) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Yb Rb
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hYbn).ge), hsup]
    trivial
  obtain ⟨y, hy, r, hr, hyr⟩ := hw
  refine ⟨⟨r, hr⟩, ?_⟩
  have hy1 : QuotientGroup.mk' Yb y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [← hyr, map_mul, hy1, one_mul]

theorem centralizer_yAlpha_eq_bot
    (hRY : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (yTwenty X c : Set G))
    (hZ : Subgroup.center ↥(yAlpha M X T c) = ⊥) :
    Subgroup.centralizer (yAlpha M X T c : Set (↥(yTwenty X c ⊔
      CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
        CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYbn, -⟩ := yAlpha_normal_and_sup_eq_top hRY
  have hq2 := isPGroup_quotient_yAlpha hRY
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set YR := yTwenty X c ⊔ R with hYRdef
  set Yb := yAlpha M X T c with hYbdef
  set C := Subgroup.centralizer (Yb : Set (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)) with hCdef
  have hCn : C.Normal := by
    refine ⟨fun w hw g => Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ Yb := by
      have h := hYbn.conj_mem u hu g⁻¹
      rwa [inv_inv] at h
    have h := Subgroup.mem_centralizer_iff.mp hw _ hu'
    calc u * (g * w * g⁻¹) = g * ((g⁻¹ * u * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
      _ = g * w * g⁻¹ * u := by group
  have hCYb : ∀ w ∈ C, w ∈ Yb → w = 1 := by
    intro w hw hwY
    have hcen : (⟨w, hwY⟩ : ↥Yb) ∈ Subgroup.center ↥Yb := by
      rw [Subgroup.mem_center_iff]
      intro u
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hw u u.2)
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hC2 : IsPGroup 2 C := by
    intro w
    obtain ⟨a, ha⟩ := hq2 (QuotientGroup.mk' Yb (w : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR))
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine hCYb _ (C.pow_mem w.2 _) ?_
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    exact ha
  have hle : C ≤ CFSG.pPrimeCore 3 (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) :=
    le_sSup ⟨hCn, Res6.coprime_card_of_isPGroup Nat.prime_three (by norm_num) hC2⟩
  rwa [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3, le_bot_iff] at hle

theorem generalizedFitting_eq_yAlpha
    (hRY : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (yTwenty X c : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a) :
    CFSG.generalizedFitting (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
      CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) =
        yAlpha M X T c := by
  obtain ⟨hqs, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  exact CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot _
    ⟨hqs, (yAlpha_normal_and_sup_eq_top hRY).1.isSubnormal⟩ (centralizer_yAlpha_eq_bot hRY hZ)

theorem perfectResidual_eq_yAlpha
    (hRY : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (yTwenty X c : Set G))
    (hY : Group.IsPerfect ↥(yAlpha M X T c)) :
    perfectResidual (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
      CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) =
        yAlpha M X T c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := (yAlpha_normal_and_sup_eq_top hRY).1
  have hq2 := isPGroup_quotient_yAlpha hRY
  refine le_antisymm ?_ ((CFSG.perfect_residual_transport (MonoidHom.id _)).2.2 _ hY)
  haveI : Group.IsNilpotent (_ ⧸ yAlpha M X T c) := hq2.isNilpotent
  exact ((CFSG.perfect_residual_characterization).2.2.2.2.1 (yAlpha M X T c)).mp inferInstance

end YAlpha

section Hyp

theorem hyp1411_of_simple {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    {G₀ : Subgroup G} (hG₀ : Minimal (CoverYR M X T c) G₀) :
    Hyp1411 ↥G₀ (perfectResidual ↥G₀) ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀) ∧
      ∃ Ψ : (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) ≃*
          (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
            CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))),
        (((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀).map
            (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))).map Ψ.toMonoidHom =
          ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf
            (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map (QuotientGroup.mk'
              (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))) ∧
        ((perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))).map
          Ψ.toMonoidHom = yAlpha M X T c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  have hRG : R ≤ G₀ := hG₀.prop.1
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hRY : R ≤ Subgroup.normalizer (yTwenty X c : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX).trans
      (le_normalizer_normalClosureIn X c)
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hYperf : Group.IsPerfect ↥(yAlpha M X T c) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_of_minimal hG₀
  set π₀ := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀) with hπ₀
  set S₀ := R.subgroupOf G₀ with hS₀def
  set L₀ := perfectResidual ↥G₀ with hL₀def
  have hS : (S₀.map π₀).map Ψ.toMonoidHom = _ := map_map_subgroupOf_of_minimal hG₀ hΨ hRG
  have hL : (L₀.map π₀).map Ψ.toMonoidHom = yAlpha M X T c := by
    rw [Subgroup.map_map, ← perfectResidual_eq_yAlpha hRY hYperf]
    exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq _
      (Ψ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hinj : Function.Injective (Subgroup.map Ψ.toMonoidHom) :=
    Subgroup.map_injective Ψ.injective
  have hLperf := (CFSG.perfect_residual_characterization (G := ↥G₀)).2.2.1
  have hF : CFSG.generalizedFitting (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) = L₀.map π₀ := by
    apply hinj
    rw [CFSG.WholeGroup.generalizedFitting_map_mulEquiv Ψ, hL,
      generalizedFitting_eq_yAlpha hRY hnab]
  have hQS : CFSG.pCore 2 ↥G₀ ≤ S₀ := by
    intro g hg
    rw [hS₀def, Subgroup.mem_subgroupOf]
    exact pCoreOf_le_of_minimal hset hX hG₀ ⟨g, hg, rfl⟩
  have hmin : ∀ H : Subgroup ↥G₀, CFSG.pCore 2 ↥G₀ ≤ H → H ⊔ CFSG.pPrimeCore 3 ↥G₀ = ⊤ →
      H = ⊤ := fun H hQH hcovH => eq_top_of_minimal hset hX hG₀ H hQH hcovH
  have hSL : S₀ ⊔ L₀ = ⊤ := by
    refine hmin _ (hQS.trans le_sup_left) (sup_eq_top_of_map_mk'_eq_top ?_)
    apply hinj
    rw [Subgroup.map_sup, Subgroup.map_sup, hS, hL, Subgroup.map_top_of_surjective _ Ψ.surjective]
    exact (sup_comm _ _).trans (yAlpha_normal_and_sup_eq_top hRY).2
  exact ⟨⟨generalizedFitting_eq_of_minimal hset hX hG₀, inferInstance,
    (Subgroup.isPerfect_iff).mp hLperf, hF, hR2.comap_subtype, hQS, hSL, hmin⟩, Ψ, hS, hL⟩

theorem covered_of_fourChar_normal {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (hY : Group.IsPerfect ↥(yAlpha M X T c)) {G₀ : Subgroup G}
    (hG₀ : Minimal (CoverYR M X T c) G₀) {i₁ i₂ : Fin 4} (h12 : i₁ ≠ i₂) (h1 : i₁ ≠ 3)
    (h2 : i₂ ≠ 3)
    (hn1 : (Sec18.fourChar ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀) i₁).Normal)
    (hn2 : (Sec18.fourChar ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀) i₂).Normal) :
    CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j := by
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  obtain ⟨k, hk1, hk2⟩ :=
    Res6.exists_mem_inter_of_ne h12 h1 h2 hset.ne hset.ne_three_left hset.ne_three_right
  have hkn : (Sec18.fourChar (R.subgroupOf G₀) k).Normal := by
    rcases hk1 with rfl | rfl
    · exact hn1
    · exact hn2
  have hk3 : k ≠ 3 := by
    rcases hk2 with rfl | rfl
    · exact hset.ne_three_left
    · exact hset.ne_three_right
  have hRG : R ≤ G₀ := hG₀.prop.1
  have hmap := Res5.map_fourChar_subgroupOf hRG k hk3
  have hGN : G₀ ≤ Subgroup.normalizer (Sec18.fourChar R k : Set G) := by
    intro g hg
    rw [← hmap]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hkn.conj_mem y hy ⟨g, hg⟩, ?_⟩
    simp
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hRY : R ≤ Subgroup.normalizer (yTwenty X c : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX).trans
      (le_normalizer_normalClosureIn X c)
  have hcov := coveredByNormalizer_of_coverYR hRY hY hG₀.prop hGN
  rcases hk2 with rfl | rfl
  · exact Or.inl hcov
  · exact Or.inr hcov

end Hyp

end AscBridge

end CFSG.RankThree.PartTwo.Sec20

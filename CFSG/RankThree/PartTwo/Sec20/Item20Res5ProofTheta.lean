module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofSevenCyclic
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblySections
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.PreuniquenessRankFour.PrimeCore
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace Res5

open IsMulCommutative in
theorem central_eq_one_of_abelian_index {E : Type*} [Group E] [Finite E]
    (hE : commutator E = ⊤) {P : Subgroup E} [IsMulCommutative P] {z : E}
    (hzc : z ∈ Subgroup.center E) (hcop : Nat.Coprime (orderOf z) P.index) : z = 1 := by
  set T : E →* P := (MonoidHom.id P).transfer with hT
  have hT1 : ∀ g, T g = 1 := fun g => by
    have h1 : g ∈ commutator E := hE ▸ Subgroup.mem_top g
    exact Abelianization.commutator_subset_ker T h1
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center E := pow_mem hzc k
    rw [mul_assoc, ← (Subgroup.mem_center_iff.mp hzk g₀), inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id P) z hkey
  rw [hT1] at h1
  have h2 : z ^ P.index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  have h3 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h2)
  exact orderOf_eq_one_iff.mp h3

section Rank

variable {X : Type*} [Group X] [Finite X]

theorem isCyclic_of_pRank_le_one (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1)
    {R : Subgroup X} (hR : IsPGroup 3 R) : IsCyclic ↥R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥R) := ⟨hR⟩
  by_contra hnc
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  set E' : Subgroup X := E.map R.subtype with hE'
  have hE'el : CFSG.Open.IsElemAbelian 3 E' :=
    CFSG.SectionRank.isElemAbelian_map
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).mp hel) _
  have hE'card : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective R.subtype_injective, hcard]
  have := CFSG.SectionRank.le_pRank (by norm_num) (le_top : E' ≤ ⊤) hE'el hE'card
  omega

theorem pRank_top_subgroup_le (H : Subgroup X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num) H]
  exact CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three le_top

theorem pRank_top_le_of_mulEquiv {X' : Type*} [Group X'] [Finite X'] (e : X ≃* X') :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X') := by
  apply csSup_le'
  rintro k ⟨E, -, hE, hk⟩
  refine CFSG.SectionRank.le_pRank (by norm_num) (le_top : E.map e.toMonoidHom ≤ ⊤)
    (CFSG.SectionRank.isElemAbelian_map hE _) ?_
  rw [Subgroup.card_map_of_injective e.injective, hk]

omit [Finite X] in
theorem isElemAbelian_zpowers {x : X} (hx : orderOf x = 3) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers (hx ▸ pow_orderOf_eq_one x)

theorem mem_zpowers_of_commute (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) {x y : X}
    (hx : orderOf x = 3) (hy : orderOf y = 3) (hxy : x * y = y * x) :
    y ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hyx
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hcomm : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left hxy k).eq
  obtain ⟨hel, hcard⟩ :=
    Sec5.isElemAbelian_sup_zpowers (isElemAbelian_zpowers hx) hyx hy3 hcomm
  have hcard' : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) = 3 ^ 2 := by
    rw [hcard, Nat.card_zpowers, hx]
    norm_num
  have := CFSG.SectionRank.le_pRank (by norm_num)
    (le_top : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) ≤ ⊤) hel hcard'
  omega

end Rank

section Components

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_pCore_of_normal {N : Subgroup Y} (hN : N.Normal) (hN3 : IsPGroup 3 N) :
    N ≤ CFSG.pCore 3 Y :=
  le_sSup ⟨hN, hN3⟩

theorem three_dvd_card_of_isComponent (hO : CFSG.pPrimeCore 3 Y = ⊥) {E : Subgroup Y}
    (hE : IsComponent E) : 3 ∣ Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h
  have hcop : Nat.Coprime 3 (Nat.card E) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
  have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hE.2 hcop
  rw [hO, le_bot_iff] at hle
  have : Nontrivial ↥E := CFSG.LocalCores.isQuasisimple_nontrivial hE.1
  rw [hle] at this
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this

theorem exists_pow_eq_one_of_mem_center (hO : CFSG.pPrimeCore 3 Y = ⊥) {E : Subgroup Y}
    (hE : IsComponent E) {z : ↥E} (hz : z ∈ Subgroup.center ↥E) :
    ∃ a : ℕ, orderOf z = 3 ^ a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  set z0 : ↥E := z ^ (3 ^ a) with hz0
  have hz0ord : orderOf z0 = m := by
    have := orderOf_pow_of_dvd (x := z) (n := 3 ^ a) (by positivity) (hn ▸ Dvd.intro _ rfl)
    rw [hz0, this, hn]
    simp [Nat.mul_div_cancel_left _ (by positivity : 0 < 3 ^ a)]
  have hz0central : z0 ∈ Subgroup.center ↥E := Subgroup.pow_mem _ hz _
  set Z0 : Subgroup ↥E := Subgroup.zpowers z0 with hZ0
  have hZ0le : Z0 ≤ Subgroup.center ↥E := (Subgroup.zpowers_le).mpr hz0central
  have hZ0n : Z0.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := Subgroup.mem_center_iff.mp (hZ0le hn) g
    rw [this, mul_inv_cancel_right]
    exact hn
  set Z1 : Subgroup Y := Z0.map E.subtype with hZ1
  have hZ1sub : Z1.IsSubnormal := by
    refine Subgroup.IsSubnormal.step Z1 E ?_ hE.2 ?_
    · rintro _ ⟨k, -, rfl⟩
      exact k.2
    · have : Z1.subgroupOf E = Z0 :=
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective Z0
      rw [this]
      exact hZ0n
  have hcard : Nat.card Z1 = m := by
    rw [hZ1, Subgroup.card_map_of_injective E.subtype_injective, Nat.card_zpowers, hz0ord]
  have hcop : Nat.Coprime 3 (Nat.card Z1) := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm
  have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hZ1sub hcop
  rw [hO, le_bot_iff] at hle
  have hZ0bot : Z0 = ⊥ :=
    Subgroup.map_injective E.subtype_injective (by rw [Subgroup.map_bot]; exact hle)
  have hz01 : z0 = 1 := by
    have : z0 ∈ Z0 := Subgroup.mem_zpowers z0
    rw [hZ0bot, Subgroup.mem_bot] at this
    exact this
  have hm1 : m = 1 := by rw [← hz0ord, hz01, orderOf_one]
  exact ⟨a, by rw [hn, hm1, mul_one]⟩

theorem center_eq_bot_of_isComponent (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) {E : Subgroup Y} (hE : IsComponent E) :
    Subgroup.center ↥E = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨a, ha⟩ := exists_pow_eq_one_of_mem_center hO hE hz
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥E) := inferInstance
  have hrE : CFSG.Open.pRank 3 (⊤ : Subgroup ↥E) ≤ 1 := (pRank_top_subgroup_le E).trans hr
  have hcyc : IsCyclic ↥(P : Subgroup ↥E) := isCyclic_of_pRank_le_one hrE P.isPGroup'
  have : IsMulCommutative ↥(P : Subgroup ↥E) := IsCyclic.isMulCommutative
  have hperf : commutator ↥E = ⊤ := hE.1.1.commutator_eq_top
  have hcop : Nat.Coprime (orderOf z) (P : Subgroup ↥E).index := by
    rw [ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      P.not_dvd_index)
  rw [Subgroup.mem_bot]
  exact central_eq_one_of_abelian_index hperf hz hcop

theorem exists_orderOf_eq_three (hO : CFSG.pPrimeCore 3 Y = ⊥) {E : Subgroup Y}
    (hE : IsComponent E) : ∃ x ∈ E, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) 3
    (three_dvd_card_of_isComponent hO hE)
  exact ⟨x, x.2, by rw [← Subgroup.orderOf_coe] at hx; exact hx⟩

theorem eq_of_isComponent (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) {E₁ E₂ : Subgroup Y} (h₁ : IsComponent E₁)
    (h₂ : IsComponent E₂) : E₁ = E₂ := by
  rcases CFSG.LocalCores.distinct_components_commute h₁ h₂ with h | hc
  · exact h
  exfalso
  obtain ⟨x₁, hx₁E, hx₁⟩ := exists_orderOf_eq_three hO h₁
  obtain ⟨x₂, hx₂E, hx₂⟩ := exists_orderOf_eq_three hO h₂
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hmem := mem_zpowers_of_commute hr hx₁ hx₂ (hcomm x₁ hx₁E x₂ hx₂E)
  have hx₂E₁ : x₂ ∈ E₁ := (Subgroup.zpowers_le.mpr hx₁E) hmem
  have hcen : (⟨x₂, hx₂E₁⟩ : ↥E₁) ∈ Subgroup.center ↥E₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 x₂ hx₂E)
  rw [center_eq_bot_of_isComponent hO hr h₁, Subgroup.mem_bot] at hcen
  have : x₂ = 1 := congrArg Subtype.val hcen
  rw [this, orderOf_one] at hx₂
  omega

theorem fittingSubgroup_le_pCore (hO : CFSG.pPrimeCore 3 Y = ⊥) :
    fittingSubgroup Y ≤ CFSG.pCore 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hnil, hnorm, -⟩ := CFSG.LocalCores.fitting_nilpotent (G := Y)
  exact le_pCore_of_normal hnorm (CFSG.isPGroup_of_nilpotent_normal _ hnorm hnil hO)

end Components

section Aut

variable {Λ Y : Type*} [Group Λ] [Group Y]

@[expose] noncomputable def restrictAut (φ : Λ →* MulAut Y) (H : Subgroup Y)
    (hH : ∀ g : Λ, H.map (φ g).toMonoidHom = H) : Λ →* MulAut ↥H where
  toFun g := ((φ g).subgroupMap H).trans (MulEquiv.subgroupCongr (hH g))
  map_one' := by
    ext x
    show (φ 1) (x : Y) = x
    rw [map_one]
    rfl
  map_mul' := by
    intro a b
    ext x
    show (φ (a * b)) (x : Y) = (φ a) ((φ b) x)
    rw [map_mul]
    rfl

theorem restrictAut_apply (φ : Λ →* MulAut Y) (H : Subgroup Y)
    (hH : ∀ g : Λ, H.map (φ g).toMonoidHom = H) (g : Λ) (x : ↥H) :
    ((restrictAut φ H hH g x : ↥H) : Y) = φ g x :=
  rfl

@[expose] noncomputable def autQuot (N : Subgroup Y) [N.Characteristic] :
    MulAut Y →* MulAut (Y ⧸ N) where
  toFun σ := QuotientGroup.congr N N σ ((Subgroup.characteristic_iff_map_eq.mp inferInstance) σ)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rfl
  map_mul' := by
    intro σ τ
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rfl

theorem autQuot_apply_mk (N : Subgroup Y) [N.Characteristic] (σ : MulAut Y) (y : Y) :
    autQuot N σ (QuotientGroup.mk' N y) = QuotientGroup.mk' N (σ y) :=
  rfl

end Aut

section Conj

variable {G : Type*} [Group G]

@[expose] noncomputable def conjAutOf (Y : Subgroup G) :
    ↥(Subgroup.normalizer (Y : Set G)) →* MulAut ↥Y where
  toFun g := ((MulAut.conj (g : G)).subgroupMap Y).trans (MulEquiv.subgroupCongr
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp g.2))
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro a b
    ext x
    simp [mul_assoc]

theorem conjAutOf_apply (Y : Subgroup G) (g : ↥(Subgroup.normalizer (Y : Set G))) (y : ↥Y) :
    ((conjAutOf Y g y : ↥Y) : G) = (g : G) * y * (g : G)⁻¹ :=
  rfl

end Conj

section FStar

variable {Y : Type*} [Group Y] [Finite Y]

theorem commute_of_fix_generalizedFitting {σ τ : MulAut Y}
    (hσ : ∀ f ∈ CFSG.generalizedFitting Y, σ f = f)
    (hτ : ∀ f ∈ CFSG.generalizedFitting Y, τ f = f) : σ * τ = τ * σ := by
  set F := CFSG.generalizedFitting Y with hF
  have hFn : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := Y)).2
  have hd : ∀ ρ : MulAut Y, (∀ f ∈ F, ρ f = f) → ∀ y : Y,
      y⁻¹ * ρ y ∈ Subgroup.centralizer (F : Set Y) := by
    intro ρ hρ y
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hyf : y * f * y⁻¹ ∈ F := hFn.conj_mem f hf y
    have h1 : ρ (y * f * y⁻¹) = y * f * y⁻¹ := hρ _ hyf
    rw [map_mul, map_mul, map_inv, hρ f hf] at h1
    have : f * (y⁻¹ * ρ y) = (y⁻¹ * ρ y) * f := by
      calc f * (y⁻¹ * ρ y) = y⁻¹ * (y * f * y⁻¹) * ρ y := by group
        _ = y⁻¹ * (ρ y * f * (ρ y)⁻¹) * ρ y := by rw [h1]
        _ = (y⁻¹ * ρ y) * f := by group
    exact this
  have hCF := CFSG.centralizer_generalizedFitting_le Y
  ext y
  have hdτ := hd τ hτ y
  have hdσ := hd σ hσ y
  have hdτF : y⁻¹ * τ y ∈ F := hCF hdτ
  have hdσF : y⁻¹ * σ y ∈ F := hCF hdσ
  have e1 : σ (τ y) = σ y * (y⁻¹ * τ y) := by
    calc σ (τ y) = σ (y * (y⁻¹ * τ y)) := by group
      _ = σ y * σ (y⁻¹ * τ y) := map_mul σ _ _
      _ = σ y * (y⁻¹ * τ y) := by rw [hσ _ hdτF]
  have e2 : τ (σ y) = τ y * (y⁻¹ * σ y) := by
    calc τ (σ y) = τ (y * (y⁻¹ * σ y)) := by group
      _ = τ y * τ (y⁻¹ * σ y) := map_mul τ _ _
      _ = τ y * (y⁻¹ * σ y) := by rw [hτ _ hdσF]
  have hc : (y⁻¹ * σ y) * (y⁻¹ * τ y) = (y⁻¹ * τ y) * (y⁻¹ * σ y) :=
    (Subgroup.mem_centralizer_iff.mp hdσ _ hdτF).symm
  show σ (τ y) = τ (σ y)
  rw [e1, e2]
  calc σ y * (y⁻¹ * τ y) = y * ((y⁻¹ * σ y) * (y⁻¹ * τ y)) := by group
    _ = y * ((y⁻¹ * τ y) * (y⁻¹ * σ y)) := by rw [hc]
    _ = τ y * (y⁻¹ * σ y) := by group

end FStar

section L34

variable {L : Type*} [Group L] [Finite L]

theorem exists_elemAbelian_nine_projSL :
    ∃ B : Subgroup ↥(projSL 3 (GaloisField 2 2)), CFSG.Open.IsElemAbelian 3 B ∧
      Nat.card B = 9 := by
  set e := CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  set B₀ := CFSG.RankThree.PartTwo.KFacts.L34.eZero (GaloisField 2 2)
  refine ⟨B₀.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map ?_ _, ?_⟩
  · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 B₀).mp
      (CFSG.RankThree.PartTwo.KFacts.L34.isElementaryAbelian_eZero hk)
  · rw [Subgroup.card_map_of_injective e.symm.injective,
      CFSG.RankThree.PartTwo.KFacts.L34.card_eZero hk]

theorem pRank_top_quotient_eq {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ N)) = CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have h := CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal 3
    Nat.prime_three N hN ⊤
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h

theorem hom_eq_one_of_l34 {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ CFSG.pCore 2 L ≃* ↥(projSL 3 (GaloisField 2 2))) {H : Type} [Group H] [Finite H]
    (hH : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 1) (ψ : L →* H) : ψ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 2 L with hOdef
  set π := QuotientGroup.mk' O with hπ
  set K := ψ.ker with hKdef
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  have hsimpP : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField 2 2)) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  have hsimp : IsSimpleGroup ↥(projSL 3 (GaloisField 2 2)) :=
    (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).isSimpleGroup
  have hsimpQ : IsSimpleGroup (L ⧸ O) := e.isSimpleGroup
  have hKn : (K.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective O)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map π) with hbot | htop
  ·
    exfalso
    have hKO : K ≤ O := by
      intro k hk
      have : π k ∈ K.map π := ⟨k, hk, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff k).mp this
    have hK3 : ¬ 3 ∣ Nat.card K := by
      intro h3
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3
      obtain ⟨n, hn⟩ := hO2 ⟨(k : L), hKO k.2⟩
      have h1 : (k : L) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have h2 : orderOf (k : L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
      rw [Subgroup.orderOf_coe, hk] at h2
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
      omega
    have hO3 : ¬ 3 ∣ Nat.card O := by
      intro h3
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥O) 3 h3
      obtain ⟨n, hn⟩ := hO2 k
      have h2 : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
      rw [hk] at h2
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
      omega
    obtain ⟨B, hB, hB9⟩ := exists_elemAbelian_nine_projSL
    have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ O)) := by
      have h1 := pRank_top_le_of_mulEquiv e.symm
      have h0 := CFSG.SectionRank.le_pRank (by norm_num) (le_top : B ≤ ⊤) hB
        (show Nat.card B = 3 ^ 2 by rw [hB9]; norm_num)
      omega
    have hLO := pRank_top_quotient_eq O hO3
    have hLK := pRank_top_quotient_eq K hK3
    have hrange := pRank_top_le_of_mulEquiv (QuotientGroup.quotientKerEquivRange ψ)
    have hsub := pRank_top_subgroup_le ψ.range
    omega
  ·
    have hKO : K ⊔ O = ⊤ := by
      have h1 := Subgroup.comap_mono (f := π) (le_of_eq htop.symm)
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
      exact top_le_iff.mp (h1.trans' (le_of_eq (Subgroup.comap_top π).symm))
    have hp : IsPGroup 2 ψ.range := by
      rintro ⟨h, l, rfl⟩
      have hl : l ∈ ((K ⊔ O : Subgroup L) : Set L) := hKO ▸ Subgroup.mem_top l
      rw [Subgroup.mul_normal K O] at hl
      obtain ⟨k, hk, o, ho, rfl⟩ := hl
      obtain ⟨n, hn⟩ := hO2 ⟨o, ho⟩
      refine ⟨n, Subtype.ext ?_⟩
      have hk1 : ψ k = 1 := hk
      have ho1 : o ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      simp only [Subgroup.coe_pow, MonoidHom.map_mul, hk1, one_mul, Subgroup.coe_one]
      rw [← map_pow, ho1, map_one]
    have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
    have : Group.IsNilpotent ψ.range := hp.isNilpotent
    have : Group.IsSolvable ψ.range := inferInstance
    have hsub : Subsingleton ψ.range :=
      CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    ext l
    have := hsub.elim (⟨ψ l, l, rfl⟩ : ψ.range) 1
    simpa using congrArg Subtype.val this

end L34

section Main

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_one_of_pRank_le_one {Λ : Type} [Group Λ] [Group.IsPerfect Λ]
    (hO : CFSG.pPrimeCore 3 Y = ⊥) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1)
    (hS : CFSG.ComponentClassification.LBalance.SchreierSections Y)
    (hPL : ∀ (H : Type) [Group H] [Finite H], CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 1 →
      ∀ ψ : Λ →* H, ψ = 1)
    (φ : Λ →* MulAut Y) : φ = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Fix : Λ → Subgroup Y := fun g => (φ g).toMonoidHom.eqLocus (MonoidHom.id Y) with hFix
  have hmemFix : ∀ g y, y ∈ Fix g ↔ φ g y = y := fun g y => Iff.rfl
  set Q := CFSG.pCore 3 Y with hQ
  have hQchar : ∀ g : Λ, Q.map (φ g).toMonoidHom = Q := fun g =>
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) (φ g)
  have hQcyc : IsCyclic ↥Q := isCyclic_of_pRank_le_one hr CFSG.pCore_isPGroup
  have hQfix : ∀ g : Λ, Q ≤ Fix g := by
    have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative
      ((IsCyclic.mulAutMulEquiv ↥Q).toMonoidHom.comp (restrictAut φ Q hQchar))
    intro g q hq
    have h2 : restrictAut φ Q hQchar g = 1 := by
      have h3 := congrArg (fun f : Λ →* (ZMod (Nat.card ↥Q))ˣ => f g) h1
      simp only [MonoidHom.comp_apply, MonoidHom.one_apply, MulEquiv.coe_toMonoidHom] at h3
      exact (IsCyclic.mulAutMulEquiv ↥Q).injective (h3.trans (map_one _).symm)
    have h4 := congrArg (fun σ : MulAut ↥Q => ((σ ⟨q, hq⟩ : ↥Q) : Y)) h2
    exact h4
  have hEfix : ∀ g : Λ, CFSG.layer Y ≤ Fix g := by
    by_cases hex : ∃ E : Subgroup Y, IsComponent E
    · obtain ⟨E, hE⟩ := hex
      have hlayer : CFSG.layer Y = E := by
        apply le_antisymm
        · exact sSup_le fun E' hE' => le_of_eq (eq_of_isComponent hO hr hE' hE)
        · exact CFSG.LocalCores.component_le_layer hE
      have hEinv : ∀ g : Λ, E.map (φ g).toMonoidHom = E := fun g =>
        eq_of_isComponent hO hr (CFSG.LocalCores.isComponent_map_mulEquiv (φ g) hE) hE
      set ρ := restrictAut φ E hEinv with hρ
      have hcen := center_eq_bot_of_isComponent hO hr hE
      obtain ⟨-, hsimpQ, a, b, hab⟩ := hE.1
      have e1 : ↥E ≃* ↥E ⧸ Subgroup.center ↥E :=
        ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
      have hsimpE : IsSimpleGroup ↥E := e1.isSimpleGroup
      have hnab : ∃ a b : ↥E, a * b ≠ b * a := by
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
      have hsol : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥E) :=
        hS.outer_solvable E hnab (MonoidHom.id ↥E) Function.surjective_id
      have hout := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
        ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥E)).comp ρ)
      have hinner : ∀ g : Λ, ρ g ∈ (MulAut.conj : ↥E →* MulAut ↥E).range := by
        intro g
        have h3 := congrArg (fun f : Λ →* CFSG.ComponentClassification.OuterAutomorphisms.Outer
          ↥E => f g) hout
        simp only [MonoidHom.comp_apply, MonoidHom.one_apply, QuotientGroup.mk'_apply] at h3
        exact (QuotientGroup.eq_one_iff _).mp h3
      have hinj : Function.Injective (MulAut.conj : ↥E →* MulAut ↥E) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        have hxc : x ∈ Subgroup.center ↥E := by
          rw [Subgroup.mem_center_iff]
          intro y
          have := congrArg (fun σ : MulAut ↥E => σ y) hx
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc y * x = x * y * x⁻¹ * x := by rw [this]
            _ = x * y := by group
        rw [hcen] at hxc
        exact hxc
      set ψ : Λ →* ↥E := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
        (ρ.codRestrict _ hinner) with hψ
      have hrE : CFSG.Open.pRank 3 (⊤ : Subgroup ↥E) ≤ 1 := (pRank_top_subgroup_le E).trans hr
      have hψ1 := hPL ↥E hrE ψ
      intro g
      rw [hlayer]
      intro x hx
      have hρg : ρ g = 1 := by
        have h3 := congrArg (fun f : Λ →* ↥E => f g) hψ1
        simp only [hψ, MonoidHom.comp_apply, MonoidHom.one_apply, MulEquiv.coe_toMonoidHom] at h3
        have h4 : ρ.codRestrict _ hinner g = 1 :=
          (MonoidHom.ofInjective hinj).symm.injective (h3.trans (map_one _).symm)
        exact congrArg Subtype.val h4
      have h5 := congrArg (fun σ : MulAut ↥E => ((σ ⟨x, hx⟩ : ↥E) : Y)) hρg
      exact h5
    · push Not at hex
      intro g
      rw [CFSG.LocalCores.layer_eq_bot_of_forall hex]
      exact bot_le
  have hFfix : ∀ g : Λ, ∀ f ∈ CFSG.generalizedFitting Y, φ g f = f := by
    intro g f hf
    have hle : CFSG.generalizedFitting Y ≤ Fix g :=
      sup_le ((fittingSubgroup_le_pCore hO).trans (hQfix g)) (hEfix g)
    exact hle hf
  have hcomm : ∀ a b : Λ, φ a * φ b = φ b * φ a := fun a b =>
    commute_of_fix_generalizedFitting (hFfix a) (hFfix b)
  have : IsMulCommutative ↥φ.range := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    show (x : MulAut Y) * y = y * x
    rw [← ha, ← hb]
    exact hcomm a b
  have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative
    φ.rangeRestrict
  ext g y
  have h2 := congrArg (fun f : Λ →* ↥φ.range => ((f g : ↥φ.range) : MulAut Y) y) h1
  exact h2

end Main

end Res5

theorem Res5.openIsKGroup_of_isKGroup {X : Type} [Group X] (h : CFSG.IsKGroup X) :
    CFSG.Open.IsKGroup X := fun K L _ _ hsimple _ => h K (L.subgroupOf K) hsimple

theorem kF207Theta_of_schreier
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog) :
    KF207Theta := by
  intro G _ _ Y L hK hLY hLL ⟨e⟩ hr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥Y with hN
  set φ : ↥L →* MulAut (↥Y ⧸ N) :=
    (Res5.autQuot N).comp ((Res5.conjAutOf Y).comp (Subgroup.inclusion hLY)) with hφ
  have hperf : Group.IsPerfect ↥L := by
    refine ⟨?_⟩
    apply Subgroup.map_injective L.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hLL]
  have hrY : CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ N)) ≤ 1 := by
    rw [Res5.pRank_top_quotient_eq N ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      CFSG.pPrimeCore_coprime_card),
      ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num) Y]
    exact hr
  have hSY : CFSG.ComponentClassification.LBalance.SchreierSections (↥Y ⧸ N) :=
    (CFSG.ComponentClassification.LBalance.SchreierSections.of_isKGroup
      (fun S _ _ _ hnc hcat => hSch S hnc hcat) (Res5.openIsKGroup_of_isKGroup hK)).quotient N
  have hφ1 := Res5.eq_one_of_pRank_le_one (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3) hrY hSY
    (fun H _ _ hH ψ => Res5.hom_eq_one_of_l34 e hH ψ) φ
  rw [Subgroup.commutator_le]
  intro l hl y hy
  have h1 := congrArg (fun f : ↥L →* MulAut (↥Y ⧸ N) =>
    f ⟨l, hl⟩ (QuotientGroup.mk' N ⟨y, hy⟩)) hφ1
  simp only [hφ, MonoidHom.comp_apply, MonoidHom.one_apply, MulAut.one_apply] at h1
  rw [Res5.autQuot_apply_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at h1
  set y' : ↥Y := Res5.conjAutOf Y (Subgroup.inclusion hLY ⟨l, hl⟩) ⟨y, hy⟩ with hy'
  have hy'v : (y' : G) = l * y * l⁻¹ := Res5.conjAutOf_apply Y _ ⟨y, hy⟩
  have hNn : N.Normal := CFSG.pPrimeCore_normal
  have h2 : y' * (⟨y, hy⟩ : ↥Y)⁻¹ ∈ N := by
    have h3 := hNn.conj_mem _ (N.inv_mem h1) (⟨y, hy⟩ : ↥Y)
    simpa [mul_assoc] using h3
  refine ⟨_, h2, ?_⟩
  simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, hy'v,
    commutatorElement_def]

end CFSG.RankThree.PartTwo.Sec20

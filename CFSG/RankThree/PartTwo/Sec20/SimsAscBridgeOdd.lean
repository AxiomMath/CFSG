module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeG0
public import CFSG.RankThree.PartTwo.Sec4.Item41PRankNarrow41
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.RankThree.PartTwo.Late.Item2010

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

noncomputable abbrev rAlpha {G : Type} [Group G] (M X T : Subgroup G) (c : G) :
    Subgroup (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
      CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) :=
  ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf
    (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3
        ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))))

noncomputable abbrev kAlpha {G : Type} [Group G] (M X T : Subgroup G) (c : G) :
    Subgroup (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
      CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) :=
  ((kTwenty M c).subgroupOf (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))))

namespace AscBridge

variable {G : Type} [Group G] [Finite G]
variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P X : Subgroup G}

theorem isSylowOf_sup_oThreePrimeYR (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))
      (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ⊔ oThreePrimeYR M X T c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set K₀ := oThreePrimeYR M X T c with hK₀def
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRK₀ : R ≤ Subgroup.normalizer (K₀ : Set G) :=
    le_sup_right.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 (Y ⊔ R))
  obtain ⟨S', hS', hRS'⟩ := Sec20.exists_isSylowOf_le hR2 (le_sup_left : R ≤ R ⊔ K₀)
  have hS'K₀ : S' ⊓ K₀ ≤ R := by
    refine le_of_isPGroup_of_le_oThreePrimeYR hset hX (hS'.isPGroup.to_le inf_le_left)
      inf_le_right fun r hr => ?_
    exact Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer (hRS' hr)) (hRK₀ hr)
  have hle : S' ≤ R := by
    intro s hs
    have hs' : s ∈ ((R : Set G) * (K₀ : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right R K₀ hRK₀]
      exact hS'.le hs
    obtain ⟨r, hr, k, hk, rfl⟩ := hs'
    have hkS : k ∈ S' := by
      have e : k = r⁻¹ * (r * k) := by group
      rw [e]
      exact S'.mul_mem (S'.inv_mem (hRS' hr)) hs
    exact R.mul_mem hr (hS'K₀ ⟨hkS, hk⟩)
  have heq : S' = R := le_antisymm hle hRS'
  rw [heq] at hS'
  exact hS'

theorem mk_mem_normalizer_kAlpha {u : ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))}
    (hu : (u : G) ∈ Subgroup.normalizer (kTwenty M c : Set G)) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))
      u ∈ Subgroup.normalizer (SetLike.coe (kAlpha M X T c)) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨k, hk, rfl⟩ := hz
  refine ⟨u * k * u⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hu k).mp (Subgroup.mem_subgroupOf.mp hk)

theorem normalizer_rAlpha_le_normalizer_kAlpha (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) :
    Subgroup.normalizer (SetLike.coe (rAlpha M X T c)) ≤
      Subgroup.normalizer (SetLike.coe (kAlpha M X T c)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  set K₀ := oThreePrimeYR M X T c with hK₀def
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  have hRsyl := isSylowOf_sup_oThreePrimeYR hset hX
  have hRK₀ : R ≤ Subgroup.normalizer (K₀ : Set G) :=
    le_sup_right.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 (Y ⊔ R))
  have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer
      (hset.sylow.le.trans (le_normalizer_normalClosureIn M c)))
  have hK₀YR : K₀ ≤ YR := Res6.inSubgroup_pPrimeCore_le 3 YR
  have hRK₀YR : R ⊔ K₀ ≤ YR := sup_le le_sup_right hK₀YR
  have hk1 : ∀ k : ↥YR, (k : G) ∈ K₀ → π k = 1 := by
    intro k hk
    obtain ⟨k', hk', hkk'⟩ := hk
    have : k' = k := Subtype.ext hkk'
    rw [← this, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk'
  intro z hz
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ z
  set Rg := R.map (MulAut.conj (g : G)).toMonoidHom with hRgdef
  have hRgle : Rg ≤ R ⊔ K₀ := by
    rintro _ ⟨r, hr, rfl⟩
    have hrYR : r ∈ YR := Subgroup.mem_sup_right hr
    have hmem : π g * π ⟨r, hrYR⟩ * (π g)⁻¹ ∈ rAlpha M X T c :=
      (Subgroup.mem_normalizer_iff.mp hz _).mp ⟨⟨r, hrYR⟩, hr, rfl⟩
    obtain ⟨r', hr', hr'e⟩ := hmem
    have hq : π (r'⁻¹ * (g * ⟨r, hrYR⟩ * g⁻¹)) = 1 := by
      rw [map_mul, map_inv, hr'e, map_mul, map_mul, map_inv]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    have hk : ((r'⁻¹ * (g * ⟨r, hrYR⟩ * g⁻¹) : ↥YR) : G) ∈ K₀ := ⟨_, hq, rfl⟩
    have e : (MulAut.conj (g : G)).toMonoidHom r =
        (r' : G) * ((r'⁻¹ * (g * ⟨r, hrYR⟩ * g⁻¹) : ↥YR) : G) := by
      simp [MulAut.conj_apply]
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hr') hk
  have hRgsyl : CFSG.ABGLocalTools.IsSylowOf 2 Rg (R ⊔ K₀) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hRgle ?_
    rw [← hRsyl.card_eq]
    exact Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective
  obtain ⟨h, hh, hhR⟩ := hRsyl.exists_mem_conj hRgsyl
  have hnR : h⁻¹ * (g : G) ∈ Subgroup.normalizer (R : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hrg : (g : G) * r * (g : G)⁻¹ ∈ Rg := ⟨r, hr, by simp [MulAut.conj_apply]⟩
    have := (hhR _).mp hrg
    have e : h⁻¹ * (g : G) * r * (h⁻¹ * (g : G))⁻¹ = h⁻¹ * ((g : G) * r * (g : G)⁻¹) * h := by
      group
    rw [e]
    exact this
  have hnK := hset.normalizer_le hnR
  have hhYR : h ∈ YR := hRK₀YR hh
  have hh' : h ∈ ((R : Set G) * (K₀ : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R K₀ hRK₀]
    exact hh
  obtain ⟨r, hr, k, hk, hrk⟩ := hh'
  have hrYR : r ∈ YR := Subgroup.mem_sup_right hr
  have hkYR : k ∈ YR := hK₀YR hk
  have hnYR : h⁻¹ * (g : G) ∈ YR := YR.mul_mem (YR.inv_mem hhYR) g.2
  have hg : g = ⟨r, hrYR⟩ * ⟨k, hkYR⟩ * ⟨h⁻¹ * (g : G), hnYR⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← mul_assoc, show r * k = h from hrk]
    group
  rw [hg, map_mul, map_mul, hk1 ⟨k, hkYR⟩ hk, mul_one]
  exact Subgroup.mul_mem _ (mk_mem_normalizer_kAlpha (hRK hr)) (mk_mem_normalizer_kAlpha hnK)

theorem kAlpha_le_yAlpha (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) :
    kAlpha M X T c ≤ yAlpha M X T c := by
  have hKX : kTwenty M c ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hKY := Res6.kTwenty_le_yTwenty hset hKX
  exact Subgroup.map_mono fun k hk => hKY hk

theorem rAlpha_ne_bot (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [hs : IsSimpleGroup ↥(yAlpha M X T c)]
    (hYK : ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c) : rAlpha M X T c ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  set K₀ := oThreePrimeYR M X T c with hK₀def
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  intro hR
  have hKX : K ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hKYR : K ≤ YR := hKY.trans le_sup_left
  have hKle := kAlpha_le_yAlpha hset hX
  have hKn : ∀ z, z ∈ Subgroup.normalizer (SetLike.coe (kAlpha M X T c)) := by
    intro z
    refine normalizer_rAlpha_le_normalizer_kAlpha hset hX ?_
    rw [hR]
    exact Subgroup.mem_normalizer_iff.mpr fun x => by simp
  haveI hKn' : ((kAlpha M X T c).subgroupOf (yAlpha M X T c)).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hKn (y : _)) _).mp hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((kAlpha M X T c).subgroupOf (yAlpha M X T c)) with hbot | htop
  ·
    have hc3 := Res6.orderOf_c_of_setting204 hset
    have hcK : c ∈ K := self_mem_normalClosureIn M c
    have hcm : π ⟨c, hKYR hcK⟩ ∈ kAlpha M X T c := ⟨⟨c, hKYR hcK⟩, hcK, rfl⟩
    have hcm' : (⟨π ⟨c, hKYR hcK⟩, hKle hcm⟩ : ↥(yAlpha M X T c)) ∈
        (kAlpha M X T c).subgroupOf (yAlpha M X T c) := hcm
    rw [hbot, Subgroup.mem_bot] at hcm'
    have h1 : π ⟨c, hKYR hcK⟩ = 1 := congrArg Subtype.val hcm'
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdvd : orderOf (⟨c, hKYR hcK⟩ : ↥YR) ∣ Nat.card (CFSG.pPrimeCore 3 ↥YR) := by
      rw [← Subgroup.orderOf_mk _ h1]
      exact orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hc3] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card hdvd
  ·
    apply hYK
    intro y hy
    have hyYR : y ∈ YR := Subgroup.mem_sup_left hy
    have hym : (⟨π ⟨y, hyYR⟩, ⟨⟨y, hyYR⟩, hy, rfl⟩⟩ : ↥(yAlpha M X T c)) ∈
        (kAlpha M X T c).subgroupOf (yAlpha M X T c) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_subgroupOf.mp hym
    have hq : π (k⁻¹ * ⟨y, hyYR⟩) = 1 := by rw [map_mul, map_inv, hke, inv_mul_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    have hk0 : ((k⁻¹ * ⟨y, hyYR⟩ : ↥YR) : G) ∈ K₀ := ⟨_, hq, rfl⟩
    have e : y = (k : G) * ((k⁻¹ * ⟨y, hyYR⟩ : ↥YR) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hk) hk0

theorem commute_of_kAlpha_inf_rAlpha_eq_bot (hset : Setting204 G A M L N c T i j P)
    (h : kAlpha M X T c ⊓ rAlpha M X T c = ⊥) :
    ∀ k ∈ kAlpha M X T c, ∀ r ∈ rAlpha M X T c, k * r = r * k := by
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer
      (hset.sylow.le.trans (le_normalizer_normalClosureIn M c)))
  rintro _ ⟨k, hk, rfl⟩ _ ⟨r, hr, rfl⟩
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
  have hkR : (k : G) ∈ Subgroup.normalizer (R : Set G) := hKR hkK
  have hrK : (r : G) ∈ Subgroup.normalizer (K : Set G) := hRK hrR
  have hKmem : k * r * k⁻¹ * r⁻¹ ∈ K.subgroupOf (yTwenty X c ⊔ R) := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    have e : ((k * r * k⁻¹ * r⁻¹ : ↥(yTwenty X c ⊔ R)) : G) =
        (k : G) * ((r : G) * (k : G)⁻¹ * (r : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact K.mul_mem hkK ((Subgroup.mem_normalizer_iff.mp hrK _).mp (K.inv_mem hkK))
  have hRmem : k * r * k⁻¹ * r⁻¹ ∈ R.subgroupOf (yTwenty X c ⊔ R) := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    have e : ((k * r * k⁻¹ * r⁻¹ : ↥(yTwenty X c ⊔ R)) : G) =
        ((k : G) * (r : G) * (k : G)⁻¹) * (r : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp hkR _).mp hrR) (R.inv_mem hrR)
  have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) (k * r * k⁻¹ * r⁻¹) ∈
      kAlpha M X T c ⊓ rAlpha M X T c := ⟨⟨_, hKmem, rfl⟩, ⟨_, hRmem, rfl⟩⟩
  rw [h, Subgroup.mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv] at hmem
  have h1 := mul_inv_eq_one.mp hmem
  have h2 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) k *
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) r =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) r *
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) k := by
    calc _ = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) k *
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) r *
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) k)⁻¹ *
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ R)) k := by group
      _ = _ := by rw [h1]
  exact h2

section Rank


theorem pRank_yAlpha_le_two (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(yAlpha M X T c)) ≤ 2 := by
  have : IsSimpleGroup G := hset.isSimpleGroup
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  have hKTX : K ⊔ T ≤ X := fun x hx => hX.2 hx
  have hcX : c ∈ X := hKTX (Subgroup.mem_sup_left (self_mem_normalClosureIn M c))
  have hYRX : YR ≤ X :=
    sup_le (normalClosureIn_le hcX) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX)
  have hXtop : X ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot hset.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hX.1)
  have hYRtop : YR ≠ ⊤ := ne_top_of_le_ne_top hXtop hYRX
  have hS4 := hset.toTheoremFourHyp.sectionFourHyp hYRtop
  have hYR2 : CFSG.Open.pRank p (⊤ : Subgroup ↥YR) ≤ 2 := by
    have hloc : CFSG.Open.pRank p X ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
      le_csSup ⟨Nat.card G, by
        rintro _ ⟨Z, -, rfl⟩
        exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp Z).trans
          (Subgroup.card_le_card_group Z)⟩ ⟨X, hX.1.1, rfl⟩
    have hlt := hset.localRank_lt p hp (by omega)
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt hYRX).trans
      (Nat.lt_succ_iff.mp (hloc.trans_lt hlt))
  set H : Subgroup ↥YR := Y.subgroupOf YR with hHdef
  set φ : ↥H →* _ := π.comp H.subtype with hφ
  have hrange : φ.range = yAlpha M X T c := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  let e₁ : ↥H ⧸ φ.ker ≃* ↥(yAlpha M X T c) :=
    (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)
  have hsimple : IsSimpleGroup (↥H ⧸ φ.ker) := e₁.isSimpleGroup
  have hnab' : ∃ a b : ↥H ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e₁.symm a, e₁.symm b, fun h => hab ?_⟩
    have := congrArg e₁ h
    simpa using this
  have hlayer : CFSG.layer (↥H ⧸ φ.ker) = ⊤ :=
    CFSG.WholeGroup.layer_eq_top_of_isQuasisimple
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab').1
  have h := Sec4.Item41Narrow.item4_1PRankLargePrime_of_griess
    ComponentClassification.TBLit.griessMultipliersAllModels_holds ↥YR hS4 H φ.ker hlayer p hp
    (by omega) (hYR2.trans (by norm_num))
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e₁] at h
  exact h.trans hYR2

end Rank

end AscBridge

end CFSG.RankThree.PartTwo.Sec20

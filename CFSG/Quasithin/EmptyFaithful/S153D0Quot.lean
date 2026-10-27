module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S153Cases
public import CFSG.Quasithin.EmptyFaithful.S153DGen2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

section Generic

theorem mem_of_cube_of_pow_two_pow {G : Type*} [Group G] (N : Subgroup G) {y : G} {k : ℕ}
    (h3 : y ^ 3 ∈ N) (hk : y ^ 2 ^ k = 1) : y ∈ N := by
  have hcop : IsCoprime (3 : ℤ) (2 ^ k) :=
    IsCoprime.pow_right (by rw [Int.isCoprime_iff_gcd_eq_one]; norm_num)
  obtain ⟨u, v, huv⟩ := hcop
  have e : y = (y ^ 3) ^ u * (y ^ 2 ^ k) ^ v := by
    have h1 : y ^ (u * 3 + v * 2 ^ k) = y := by rw [huv, zpow_one]
    conv_lhs => rw [← h1]
    rw [zpow_add]
    congr 1
    · rw [zpow_mul', ← zpow_natCast]
      norm_num
    · rw [zpow_mul', ← zpow_natCast]
      norm_num
  rw [e, hk, one_zpow, mul_one]
  exact N.zpow_mem h3 u

theorem classLeTwo_top_of_le {H : Type*} [Group H] {A B : Subgroup H} (hAB : A ≤ B)
    (hB : ⁅⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆, (⊤ : Subgroup B)⁆ = ⊥) :
    ⁅⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆, (⊤ : Subgroup A)⁆ = ⊥ := by
  have hinj : Function.Injective (Subgroup.inclusion hAB) := Subgroup.inclusion_injective hAB
  have e : Subgroup.map (Subgroup.inclusion hAB)
      ⁅⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆, (⊤ : Subgroup A)⁆ =
        ⁅⁅Subgroup.map (Subgroup.inclusion hAB) ⊤, Subgroup.map (Subgroup.inclusion hAB) ⊤⁆,
          Subgroup.map (Subgroup.inclusion hAB) ⊤⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
  have hle : ⁅⁅Subgroup.map (Subgroup.inclusion hAB) (⊤ : Subgroup A),
      Subgroup.map (Subgroup.inclusion hAB) (⊤ : Subgroup A)⁆,
        Subgroup.map (Subgroup.inclusion hAB) (⊤ : Subgroup A)⁆ ≤
      ⁅⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆, (⊤ : Subgroup B)⁆ :=
    Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top) le_top
  rw [hB, le_bot_iff] at hle
  rw [hle] at e
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 e

end Generic

section Quot

variable {G : Type} [Group G] [Finite G]

theorem exists_mulEquiv_imageOTwoQuot_of_le {M Y X : Subgroup G} (hXY : X ≤ Y) (hYM : Y ≤ M)
    (h3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 M) :
    ∃ φ : OTwoQuot X ≃* ↥(imageOTwoQuot M X), ∀ x : ↥X,
      ((φ (QuotientGroup.mk x) : ↥(imageOTwoQuot M X)) : OTwoQuot M) =
        QuotientGroup.mk (⟨(x : G), hYM (hXY x.2)⟩ : ↥M) := by
  classical
  have hXM : X ≤ M := hXY.trans hYM
  have hnormX : (CFSG.Open.pCore 2 ↥X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  let f₀ : ↥X →* OTwoQuot M :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)).comp (Subgroup.inclusion hXM)
  have hf₀mem : ∀ y : ↥X, f₀ y ∈ imageOTwoQuot M X := fun y =>
    mem_imageOTwoQuot_iff.mpr ⟨(y : G), hXM y.2, y.2, rfl⟩
  let f : ↥X →* ↥(imageOTwoQuot M X) := f₀.codRestrict (imageOTwoQuot M X) hf₀mem
  have hfsurj : Function.Surjective f := by
    rintro ⟨u, hu⟩
    obtain ⟨x, hxM, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact ⟨⟨x, hxX⟩, rfl⟩
  have hker : f.ker = CFSG.Open.pCore 2 ↥X := by
    ext y
    have h1 : y ∈ f.ker ↔ (y : G) ∈ pCoreOf 2 M := by
      rw [MonoidHom.mem_ker, Subtype.ext_iff]
      exact mk_eq_one_iff_mem_pCoreOf (⟨(y : G), hXM y.2⟩ : ↥M)
    have h2 : y ∈ CFSG.Open.pCore 2 ↥X ↔ (y : G) ∈ pCoreOf 2 X :=
      (Subgroup.mem_map_iff_mem X.subtype_injective).symm
    rw [h1, h2]
    constructor
    · intro hy
      have hXN : X ≤ Subgroup.normalizer ((X ⊓ pCoreOf 2 M : Subgroup G) : Set G) := fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 M (hXM hg)⟩
      exact le_pCoreOf_of_le_normalizer 2 (inf_le_left : X ⊓ pCoreOf 2 M ≤ X) hXN
        ((pCoreOf_isPGroup 2 M).to_le inf_le_right) ⟨y.2, hy⟩
    · intro hy
      have hp := pCoreOf_isPGroup 2 X
      obtain ⟨k, hk⟩ := hp ⟨(y : G), hy⟩
      have hk' : (y : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact mem_of_cube_of_pow_two_pow (pCoreOf 2 M) (h3 y (hXY y.2)) hk'
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfsurj), fun y => ?_⟩
  rfl

end Quot

end S153D

namespace Hyp153

open S153D

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem cube_mem_pCoreOf_M (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {y : G}
    (hy : y ∈ Y153 Mc M) : y ^ 3 ∈ pCoreOf 2 M := by
  have h1 := h.pow_three_mem_pCoreOf_Y153 h113 hy
  have hle : pCoreOf 2 (Y153 Mc M) ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (Y153_le Mc M))
      (fun m hm => normalizer_le_normalizer_pCoreOf 2 _ (le_normalizer_Y153 Mc M hm))
      (pCoreOf_isPGroup 2 _)
  exact hle h1

theorem exists_mulEquiv_imageOTwoQuot_of_le_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {X : Subgroup G} (hXY : X ≤ Y153 Mc M) :
    ∃ φ : OTwoQuot X ≃* ↥(imageOTwoQuot M X), ∀ x : ↥X,
      ((φ (QuotientGroup.mk x) : ↥(imageOTwoQuot M X)) : OTwoQuot M) =
        QuotientGroup.mk (⟨(x : G), (Y153_le Mc M) (hXY x.2)⟩ : ↥M) :=
  exists_mulEquiv_imageOTwoQuot_of_le hXY (Y153_le Mc M) fun _ hy => h.cube_mem_pCoreOf_M h113 hy

theorem struct_of_le (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {X : Subgroup G}
    (hXY : X ≤ Y153 Mc M) (hr : CFSG.Open.pRank 3 X = 2) :
    IsElemAbelianOfRank 3 2 (OTwoQuot X) ∨ IsPOnePlusTwo 3 (OTwoQuot X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, -⟩ := h.exists_mulEquiv_imageOTwoQuot_of_le_Y153 h113 hXY
  obtain ⟨⟨hcl, -, hexp⟩, -⟩ := h.Ystar_structure h113
  set Ys := imageOTwoQuot M (Y153 Mc M) with hYs
  set Q := imageOTwoQuot M X with hQ
  have hQY : Q ≤ Ys := imageOTwoQuot_mono hXY
  have hQ3 : ∀ x : ↥Q, x ^ 3 = 1 := fun x =>
    Subtype.ext (by simpa using congrArg Subtype.val (hexp ⟨(x : OTwoQuot M), hQY x.2⟩))
  have hQp : IsPGroup 3 ↥Q := fun x => ⟨1, by simpa using hQ3 x⟩
  have hΩ : Subgroup.closure {x : ↥Q | x ^ 3 = 1} = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.subset_closure (hQ3 x)
  have hclQ : ClassLeTwo (⊤ : Subgroup ↥Q) := classLeTwo_top_of_le hQY hcl
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Q) = 2 := by
    have hp1 : 1 < 3 := by norm_num
    have e1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 φ
    have hnd : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥X) := by
      intro hd
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).exists_card_eq
      rw [hk] at hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
    have e2 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.Open.pCore 2 ↥X) hnd
    have e3 := pRank_top_subtype (p := 3) X
    rw [← e1]
    calc CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot X))
        = CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) := e2
      _ = CFSG.Open.pRank 3 X := e3
      _ = 2 := hr
  rcases isElemAbelianOfRank_two_or_isPOnePlusTwo (by norm_num : (3 : ℕ) ≠ 2) hQp hΩ hrank hclQ
    with he | hp
  · left
    obtain ⟨e⟩ := he
    exact ⟨φ.trans e⟩
  · right
    exact A36B.isPOnePlusTwo_of_mulEquiv φ.symm hp

end Hyp153

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.C22PfD
public import CFSG.Quasithin.Background.C22PfC
public import CFSG.Quasithin.Background.SmithC27RLieCentral

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Blueprint

namespace C22Pf

variable {G : Type} [Group G] [Finite G]

theorem asc22Four_of (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hRP : ∀ (X : Type) [Group X] [Finite X], (EvenLieType X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) →
      SmithC27.IsRadicalParabolic (⊤ : Subgroup X)) :
    ASC22Four G := by
  intro H R L hH hR hL hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := R ⊓ L with hA
  have hAL : A ≤ L := inf_le_right
  have hOA : pCoreOf 2 L ≤ A := by
    refine le_inf ?_ (pCoreOf_le 2 L)
    exact le_of_le_cComp_of_sqtk hA37 hH hR hL (pCoreOf_le 2 L) (pCoreOf_isPGroup 2 L)
      fun g hg => normalizer_le_normalizer_pCoreOf 2 L hg.2
  have hN : modO2Image L (L ⊓ Subgroup.normalizer (A : Set G)) =
      Subgroup.normalizer ((modO2Image L A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
        Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    ext u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ u
    constructor
    · intro hu
      obtain ⟨x, hx, hxy⟩ := mem_modO2Image_iff.mp hu
      rw [← hxy]
      exact mk_mem_normalizer hx.2
    · intro hu
      exact mem_modO2Image_iff.mpr ⟨y, ⟨y.2, mem_normalizer_of_mk hAL hOA hu⟩, rfl⟩
  have hO2 : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := pCore_two_quotient_pCore_two ↥L
  have hZo : Odd (Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) 2 (even_iff_two_dvd.1 hev)
    have hzn : (Subgroup.zpowers (z : ↥L ⧸ CFSG.pCore 2 ↥L)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hnc : n ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := (Subgroup.zpowers_le.mpr z.2) hn
      rw [Subgroup.mem_center_iff.mp hnc g, mul_inv_cancel_right]
      exact hn
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers (z : ↥L ⧸ CFSG.pCore 2 ↥L)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hle : Subgroup.zpowers (z : ↥L ⧸ CFSG.pCore 2 ↥L) ≤ CFSG.pCore 2 _ :=
      le_sSup ⟨hzn, hz2⟩
    rw [hO2] at hle
    have h1 : (z : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
      Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
    have h2 : z = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hz
    exact absurd hz (by decide)
  have hRPL : SmithC27.IsRadicalParabolic (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    SmithC27.isRadicalParabolic_top_of_quotient _ le_rfl hZo (hRP _ hT)
  show IsParabolic2 ⊤ (modO2Image L (L ⊓ Subgroup.normalizer (A : Set G)))
  rw [hN]
  by_cases hbot : modO2Image L A = ⊥
  · have htop : Subgroup.normalizer ((modO2Image L A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
        Set (↥L ⧸ CFSG.pCore 2 ↥L)) = ⊤ := by
      rw [hbot]
      refine eq_top_iff.mpr fun g _ => Subgroup.mem_normalizer_iff.mpr fun h => ?_
      simp
    rw [htop]
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L)))
    exact ⟨le_rfl, S, SmithC27.sylow_two_isSylowTwoOf_top S, inf_le_left⟩
  · have hA0 : A ≠ ⊥ := by
      intro h0
      apply hbot
      rw [h0, modO2Image, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    have hrad : IsTwoRadicalIn L A := ((asc22Two_of hA37 H R L hH hR hL).2.2) hA0
    have hcore := eq_pCoreOf_normalizer_modO2Image hrad
    have h := hRPL (modO2Image L A) le_top hbot (isPGroup_modO2Image (hR.isPGroup.to_le
      inf_le_left)) (by rw [top_inf_eq]; exact hcore.symm)
    rwa [top_inf_eq] at h

theorem asc22Statement_of (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hRP : ∀ (X : Type) [Group X] [Finite X], (EvenLieType X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) →
      SmithC27.IsRadicalParabolic (⊤ : Subgroup X)) :
    ASC22Statement G :=
  ⟨asc22One_of hA37, asc22Two_of hA37, asc22Three_of hA37, asc22Four_of hA37 hRP⟩

end C22Pf

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModel
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineInvol
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineNorm
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineOdd
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineCore
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5TwoLocalK
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Struct
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.Dihedral.GorensteinWalter.Helpers

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem nineJ_subgroupOf_normal {G : Type} [Group G] {b₀ b₂ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal) :
    ((nineJ K b₂).subgroupOf
      (Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer ({b₂} : Set G))).Normal := by
  set Y : Subgroup G :=
    Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer ({b₂} : Set G) with hY
  set H : Subgroup G := K ⊓ Subgroup.centralizer ({b₂} : Set G) with hH
  have hHY : H ≤ Y := le_inf (inf_le_left.trans hKC) inf_le_right
  have hYleK : Y ≤ Subgroup.normalizer (K : Set G) := fun y hy =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn (Subgroup.mem_inf.mp hy).1
  have hYleC : Y ≤ Subgroup.normalizer (Subgroup.centralizer ({b₂} : Set G) : Set G) :=
    fun y hy => Subgroup.le_normalizer (Subgroup.mem_inf.mp hy).2
  have hYleH : Y ≤ Subgroup.normalizer (H : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf (H := K)
      (K := Subgroup.centralizer ({b₂} : Set G))
      (Subgroup.mem_inf.mpr ⟨hYleK hy, hYleC hy⟩)
  have hJY : nineJ K b₂ ≤ Y := (Subgroup.commutator_le_self _).trans hHY
  have hYleJ : Y ≤ Subgroup.normalizer (nineJ K b₂ : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hHmap : H.map (MulAut.conj y).toMonoidHom = H :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hYleH hy)
    show (⁅H, H⁆).map (MulAut.conj y).toMonoidHom = ⁅H, H⁆
    rw [Subgroup.map_commutator, hHmap]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).mpr hYleJ

theorem six_dvd_card_nineJ {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hchar : IsCharTwoType G) (hfus : Fus42 B b₀) :
    6 ∣ Nat.card ↥(nineJ K (B.b 2)) := by
  have hD := odd_card_centralizer_inf_of_isCharTwoType hstd hchar hB hrec hfus
  have hodd := odd_card_centralizer_span_of_odd hstd hB hrec hD
  obtain ⟨t, ht, ht0, ht1, ht2⟩ := exists_nineInvol_of_recOutTwD5 hB hrec hodd
  have htN0 : t ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * b₀ * t⁻¹) = Subgroup.zpowers b₀
    have hta : t * b₀ * t⁻¹ = b₀⁻¹ := by simpa [hB.2.1] using ht0
    rw [hta, Subgroup.zpowers_inv]
  have htK : t ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_of_mem_normalizer_zpowers hstd hB hrec hodd hD htN0
  obtain ⟨-, -, h6, -⟩ :=
    t5NineModel_holds G b₀ K E hstd B hB hrec t ht htK ht1 ht2
  exact h6.trans (Subgroup.card_dvd_of_le inf_le_left)

theorem isQuasisimple_nineJ {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    CFSG.Assembly.IsQuasisimple ↥(nineJ K (B.b 2)) := by
  have hJsimple : IsSimpleGroup ↥(nineJ K (B.b 2)) := nineJ_simple_of_recOutTwD5 hstd hB hrec
  have hnonab : ∃ a b : ↥(nineJ K (B.b 2)), a * b ≠ b * a := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative ↥(nineJ K (B.b 2)) := ⟨⟨h⟩⟩
    haveI := hJsimple.toNontrivial
    exact bot_ne_top ((center_nineJ_eq_bot hstd hB hrec).symm.trans
      (Subgroup.center_eq_top_iff.mpr inferInstance))
  refine ⟨CFSG.GorensteinWalter.Helpers.commutator_eq_top_of_noncommutative hnonab, ?_⟩
  let e : (↥(nineJ K (B.b 2)) ⧸ Subgroup.center ↥(nineJ K (B.b 2))) ≃*
      ↥(nineJ K (B.b 2)) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.GorensteinWalter.Helpers.center_eq_bot_of_noncommutative hnonab)).trans
        QuotientGroup.quotientBot
  exact @MulEquiv.isSimpleGroup _ _ _ _ hJsimple e

theorem nineJ_not_le_primeCore {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hchar : IsCharTwoType G) (hfus : Fus42 B b₀)
    (Y : Subgroup G) :
    ¬ nineJ K (B.b 2) ≤ CFSG.Open.lBalancePrimeCore 3 Y := by
  have h6 : 6 ∣ Nat.card ↥(nineJ K (B.b 2)) := six_dvd_card_nineJ hstd hB hrec hchar hfus
  have hcop : Nat.Coprime 3
      (Nat.card (CFSG.Open.lBalancePrimeCore 3 Y : Subgroup G)) :=
    @CFSG.ComponentClassification.LBalance.primeCore_coprime G _ 3 ⟨Nat.prime_three⟩
      (inferInstance : Finite G) Y
  intro hle
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop ?_
  exact (dvd_trans (by norm_num : 3 ∣ 6) h6).trans (Subgroup.card_dvd_of_le hle)

theorem centralizer_b_two_ne_top {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) :
    Subgroup.centralizer ({B.b 2} : Set G) ≠ ⊤ := by
  have hb2K : B.b 2 ∈ K := hB.2.2 2 (by decide)
  have hb2ne : B.b 2 ≠ 1 := by
    intro h
    have hord := B.ord 2
    rw [h, orderOf_one] at hord
    norm_num at hord
  intro htop
  have hb2center : (⟨B.b 2, hb2K⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : (y : G) ∈ Subgroup.centralizer ({B.b 2} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy)
  rw [hstd.2.1.2.2.2.1] at hb2center
  exact hb2ne (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hb2center))

end CFSG.StandardType.FrameRoute.FS81

end

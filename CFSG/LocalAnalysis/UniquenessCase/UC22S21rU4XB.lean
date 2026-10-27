module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XA
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem u4x_false_of_normalizer_le {D : Data G} {Ch : Choice2011 G} (h1930 : H1930 D)
    (c : Ctx21 D Ch) {b : G} (hb : b ∈ c.B0) (hN : normalizer (zpowers b : Set G) ≤ D.M) :
    False :=
  s21_2 D Ch h1930 { c with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers b)
    (zpowers_le.2 hb) hN

theorem u4x_bar2_equiv {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    Nonempty (Bar2 L ≃* Bar2 K) := by
  obtain ⟨g, -, rfl⟩ := hK
  exact uc22p20d_bar2_conj g L

theorem u4x_centralizesBar {M X : Subgroup G} (hXM : X ≤ M) (hMX : M ≤ normalizer (X : Set G))
    {x : G} (hxM : x ∈ M)
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
      centralizer ((barImage M X : Subgroup (Bar2 M)) : Set (Bar2 M))) :
    CentralizesBar x X := by
  refine ⟨hMX hxM, fun l hl => uc22p2214_pCoreOf_inf_le hXM ⟨?_, ?_⟩⟩
  · set m : ↥M := ⟨x, hxM⟩
    set k : ↥M := ⟨l, hXM hl⟩
    have hk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) k ∈ barImage M X := ⟨k, hl, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.1 hx _ hk
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (m * k * m⁻¹ * k⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hc]
      group
    exact ⟨m * k * m⁻¹ * k⁻¹, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  · exact X.mul_mem ((Subgroup.mem_normalizer_iff.1 (hMX hxM) l).1 hl) (X.inv_mem hl)

theorem u4x_card_barImage_dvd {M X : Subgroup G} (hXM : X ≤ M)
    (hMX : M ≤ normalizer (X : Set G)) : Nat.card ↥(barImage M X) ∣ Nat.card (Bar2 X) := by
  let π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let ψ : ↥X →* Bar2 M := π.comp (Subgroup.inclusion hXM)
  have hle : barImage M X ≤ ψ.range := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, Subgroup.mem_subgroupOf.1 ha⟩, rfl⟩
  have hO : pCoreOf 2 X ≤ pCoreOf 2 M := uc22p22r_pCoreOf_le_of_isSubnormal
    (CFSG.Quasithin.A3.subnormal_of_normal hXM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX))
  have hker : CFSG.pCore 2 ↥X ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show π (Subgroup.inclusion hXM x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyx⟩ := hO ⟨x, hx, rfl⟩
    have : y = Subgroup.inclusion hXM x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hr : Nat.card ψ.range ∣ Nat.card (Bar2 X) := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hker
  exact (Subgroup.card_dvd_of_le hle).trans hr

theorem u4x_two_pow_twelve {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) (hSz : IsSz (Bar2 L) 5) :
    2 ^ 12 ∣ Nat.card (Bar2 (conjClosure M L)) := by
  obtain ⟨hcomm, hinf, -, -, hX, -, -⟩ := u4x_bar_structure hL hK hne hset (n := 5) (Or.inr hSz)
  obtain ⟨e₀, -⟩ := uc22p22l_barImage_equiv hL
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨eK⟩ := u4x_bar2_equiv (M := M) (L := L) (K := K) (by rw [hset]; simp)
  have h6 : 2 ^ 6 ∣ Nat.card (Bar2 L) := by
    rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 hSz]
    norm_num
  have hc₀ : Nat.card ↥(barImage M L) = Nat.card (Bar2 L) := (Nat.card_congr e₀.toEquiv).symm
  have hc₁ : Nat.card ↥(barImage M K) = Nat.card (Bar2 L) :=
    (Nat.card_congr (eK.trans e₁).toEquiv).symm
  have hN : barImage M L ≤ normalizer (barImage M K : Set (Bar2 M)) :=
    le_trans (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
      (centralizer_le_normalizer _)
  have hsup := PartTwo.card_sup_mul_card_inf_of_le_normalizer hN
  rw [inf_comm, hinf, Subgroup.card_bot, mul_one, hc₀, hc₁] at hsup
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have hdvd := u4x_card_barImage_dvd hXM hMX
  rw [hX, hsup] at hdvd
  calc 2 ^ 12 = 2 ^ 6 * 2 ^ 6 := by norm_num
    _ ∣ Nat.card (Bar2 L) * Nat.card (Bar2 L) := Nat.mul_dvd_mul h6 h6
    _ ∣ Nat.card (Bar2 (conjClosure M L)) := hdvd

theorem u4x_two_le_pRank {M L : Subgroup G} (hL : L ∈ calC M)
    (hc2 : (conjSetOf M L).ncard = 2) {n : ℕ}
    (hLS : (n = 3 ∧ IsL2 (Bar2 L) n) ∨ (n = 5 ∧ IsSz (Bar2 L) n)) :
    2 ≤ CFSG.Open.pRank n (conjClosure M L) := by
  have hn : n.Prime ∧ n ≠ 2 := by
    rcases hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  haveI : IsSimpleGroup (Bar2 L) := by
    rcases hLS with ⟨-, h⟩ | ⟨-, h⟩
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
  refine P2214R.two_le_pRank_pair hL hc2 hn.1 hn.2 ?_
  rw [uc22p21k_center_eq_bot hL.2.2, Subgroup.index_bot]
  rcases hLS with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [uc22p22r_L2_card h]
    norm_num
  · rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 h]
    norm_num

theorem u4x_normalizer_le {D : Data G} (h869 : F08.R869NS5 D)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hLS : (n = 3 ∧ IsL2 (Bar2 L) n) ∨ (n = 5 ∧ IsSz (Bar2 L) n)) (hσ : n ∈ D.sig)
    {w : G} (hwM : w ∈ D.M) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hwo : orderOf w = q)
    (hw : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨w, hwM⟩ ∈
      centralizer ((barImage D.M (conjClosure D.M L) : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) :
    normalizer (zpowers w : Set G) ≤ D.M := by
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have hcard : Nat.card (zpowers w) = q := by rw [Nat.card_zpowers, hwo]
  refine h869 (conjClosure D.M L) hXM hMX hprod ⟨n, hσ, u4x_two_le_pRank hL hc2 hLS, fun h5 => ?_⟩
    q hq hq2 (zpowers w) (zpowers_le.2 hwM) hcard
    (uc22p21d_sup_pCore_eq hq hq2 hcard fun a ha => ?_)
  · rcases hLS with ⟨rfl, -⟩ | ⟨-, hSz⟩
    · norm_num at h5
    · subst h5
      exact u4x_two_pow_twelve hL hK hne hset hSz
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine u4x_centralizesBar hXM hMX (D.M.zpow_mem hwM k) ?_
    have he : (⟨w ^ k, D.M.zpow_mem hwM k⟩ : ↥D.M) = ⟨w, hwM⟩ ^ k := Subtype.ext (by simp)
    rw [he, map_zpow]
    exact Subgroup.zpow_mem _ hw k

theorem u4x_not_mem_centralizer {D : Data G} {Ch : Choice2011 G}
    (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K})
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hLS : (n = 3 ∧ IsL2 (Bar2 L) n) ∨ (n = 5 ∧ IsSz (Bar2 L) n)) (hσ : n ∈ D.sig)
    {b : G} (hb : b ∈ c.B0) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩ ∉
      centralizer ((barImage D.M (conjClosure D.M L) : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) :=
  fun hw => u4x_false_of_normalizer_le h1930 c hb
    (u4x_normalizer_le h869 hL hK hne hset hc2 hLS hσ (c.hBM hb) hq hq2 hbo hw)

end CFSG.LocalAnalysis.UniquenessCase.UC22

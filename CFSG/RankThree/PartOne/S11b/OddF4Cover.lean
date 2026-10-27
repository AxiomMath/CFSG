module

public import CFSG.RankThree.GroupTheory.SteinbergBYCentralCoverRank
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped commutatorElement

theorem oddF4_commute_of_involution {Y T : Type*} [Group Y] [Group T] {φ : Y →* T}
    (hker : φ.ker ≤ Subgroup.center Y) {n : ℕ} (hn : Odd n) {u x : Y} (hu : u ^ 2 = 1)
    (hxn : x ^ n = 1) (hφ : φ u * φ x = φ x * φ u) : u * x = x * u := by
  have huu : u * u = 1 := by rw [← pow_two, hu]
  have hinvinv : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, huu, inv_one]
  obtain ⟨c, hc⟩ : ∃ c : Y, c = u * x * u⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hcker : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc]
    simp only [map_mul, map_inv]
    rw [hφ]
    group
  have hcc : c ∈ Subgroup.center Y := hker hcker
  have hcomm : ∀ y : Y, y * c = c * y := fun y => Subgroup.mem_center_iff.mp hcc y
  have h1 : u * x * u⁻¹ = c * x := by rw [hc]; group
  have hcc1 : c * c = 1 := by
    have h2 : x = c * c * x := by
      calc x = u * (u * x * u⁻¹) * u⁻¹ := by
            calc x = (u * u) * x * (u⁻¹ * u⁻¹) := by rw [huu, hinvinv, one_mul, mul_one]
              _ = u * (u * x * u⁻¹) * u⁻¹ := by group
        _ = u * (c * x) * u⁻¹ := by rw [h1]
        _ = c * (u * x * u⁻¹) := by
            calc u * (c * x) * u⁻¹ = (u * c) * x * u⁻¹ := by group
              _ = (c * u) * x * u⁻¹ := by rw [hcomm u]
              _ = c * (u * x * u⁻¹) := by group
        _ = c * (c * x) := by rw [h1]
        _ = c * c * x := by rw [mul_assoc]
    have h3 : (c * c) * x = 1 * x := by rw [one_mul]; exact h2.symm
    exact mul_right_cancel h3
  have hcn : c ^ n = 1 := by
    have h4 : (u * x * u⁻¹) ^ n = 1 := by
      rw [conj_pow, hxn, mul_one, mul_inv_cancel]
    rw [h1, Commute.mul_pow (hcomm x).symm, hxn, mul_one] at h4
    exact h4
  have hc1 : c = 1 := by
    obtain ⟨k, rfl⟩ := hn
    have : c ^ (2 * k + 1) = c := by
      rw [pow_succ, pow_mul, pow_two, hcc1, one_pow, one_mul]
    rw [← this]
    exact hcn
  rw [hc] at hc1
  have h5 : u * x * u⁻¹ = x := by
    have := congrArg (fun w => w * x) hc1
    simpa [mul_assoc] using this
  calc u * x = u * x * u⁻¹ * u := by group
    _ = x * u := by rw [h5]

theorem exists_involution_elemAbelian_four_of_cover_six {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) {T : Type*} [Group T] {φ : Y →* T} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Subgroup T} (hU : IsElementaryAbelian p U) {r : ℕ} (hUcard : Nat.card U = p ^ r)
    (hr : 6 ≤ r) {z : T} (hz : orderOf z = 2) (hzU : ∀ x ∈ U, Commute z x) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ V : Subgroup G, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ 4 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := hφ z
  have hdvd : 2 ∣ orderOf y := by
    rw [← hz, ← hy]
    exact orderOf_map_dvd φ y
  have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  set u : Y := y ^ (orderOf y / 2) with hudef
  have hu : orderOf u = 2 := orderOf_pow_orderOf_div hy0 hdvd
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have huU : ∀ x : Y, φ x ∈ U → φ u * φ x = φ x * φ u := fun x hx => by
    rw [hudef, map_pow, hy]
    exact ((hzU _ hx).pow_left _).eq
  set F : Subgroup Y := U.comap φ with hF
  let g : F →* U := (φ.comp F.subtype).codRestrict U fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨y', hy'⟩ := hφ w
    refine ⟨⟨y', ?_⟩, Subtype.ext hy'⟩
    change φ y' ∈ U
    rw [hy']
    exact hw
  have hgker : g.ker ≤ Subgroup.center F := by
    intro x hx
    have hx1 : φ x = 1 := congrArg Subtype.val hx
    have hxc := Subgroup.mem_center_iff.mp (hker hx1)
    exact Subgroup.mem_center_iff.mpr fun w => Subtype.ext (hxc w)
  have hUtop : IsElementaryAbelian p (⊤ : Subgroup U) := by
    have := hU.toIsMulCommutative
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr
      ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : U) b)⟩⟩, fun x _ =>
        Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian (A := U) (x : T) x.2)⟩
  have hUtopcard : Nat.card (⊤ : Subgroup U) = p ^ r := by
    rw [Subgroup.card_top]
    exact hUcard
  have hrank : 4 ≤ CFSG.pRank p F :=
    CFSG.RankThree.GroupTheory.SteinbergBY.four_le_pRank_of_central_cover hp hp2 g hg hgker hUtop
      hUtopcard hr
  have hrank' : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup F) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrank
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (G := F) (H := ⊤) hrank'
  have hcomm : ∀ x : F, x ∈ E → (u : Y) * (x : Y) = (x : Y) * u := fun x hx =>
    oddF4_commute_of_involution hker (hp.odd_of_ne_two hp2) hu2
      (by rw [← Subgroup.coe_pow, hE.2 x hx, Subgroup.coe_one]) (huU _ x.2)
  set V : Subgroup G := (E.map F.subtype).map Y.subtype with hV
  refine ⟨u, u.2, by rw [Subgroup.orderOf_coe, hu], V, ?_, ?_, ?_⟩
  · refine le_inf (Subgroup.map_subtype_le _) ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcomm x hx).symm
  · exact CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hE _) _
  · rw [hV, Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective F.subtype_injective, hEcard]

theorem oddF4_cover_six_local_rank {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    {T : Type*} [Group T] {φ : Y →* T} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup T}
    (hU : IsElementaryAbelian p U) {r : ℕ} (hUcard : Nat.card U = p ^ r) (hr : 6 ≤ r) {z : T}
    (hz : orderOf z = 2) (hzU : ∀ x ∈ U, Commute z x) :
    (∃ u ∈ Y, orderOf u = 2 ∧ ∃ V : Subgroup G, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ 4) ∧ 4 ≤ localRank p G ∧
      4 ≤ CFSG.twoLocalOddRank G := by
  obtain ⟨u, huY, hu, V, hV, hVab, hVcard⟩ :=
    exists_involution_elemAbelian_four_of_cover_six Y hφ hker hp hp2 hU hUcard hr hz hzU
  have hrank : 4 ≤ localRank p G :=
    CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp hu (le_inf_iff.1 hV).2
      hVab hVcard
  exact ⟨⟨u, huY, hu, V, hV, hVab, hVcard⟩, hrank,
    hrank.trans (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hp hp2
      (CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hp (by omega)))⟩

end CFSG.RankThree.PartOne

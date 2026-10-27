module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Odd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Dih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Fix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G]

theorem normal_imBar {H C : Subgroup G} (hCn : H ≤ Subgroup.normalizer (C : Set G)) :
    (imBar H C).Normal := by
  refine ⟨fun n hn z => ?_⟩
  obtain ⟨c, hcH, hcC, rfl⟩ := mem_imBar.mp hn
  obtain ⟨h, hhH, rfl⟩ := bar_surjective H z
  have hc := (Subgroup.mem_normalizer_iff.mp (hCn hhH) c).mp hcC
  refine mem_imBar.mpr ⟨h * c * h⁻¹, H.mul_mem (H.mul_mem hhH hcH) (H.inv_mem hhH), hc, ?_⟩
  rw [bar_mul (H.mul_mem hhH hcH) (H.inv_mem hhH), bar_mul hhH hcH, bar_inv hhH]

theorem bar_mem_imBar_iff {H C : Subgroup G} (hQC : pCoreOf 2 H ≤ C) {g : G} (hg : g ∈ H) :
    bar H g ∈ imBar H C ↔ g ∈ C := by
  constructor
  · intro h
    obtain ⟨c, hcH, hcC, hcg⟩ := mem_imBar.mp h
    have hq : c⁻¹ * g ∈ pCoreOf 2 H := (bar_eq_iff hcH hg).mp hcg
    have := C.mul_mem hcC (hQC hq)
    simpa using this
  · exact bar_mem_imBar hg

theorem isElemAbelian_imBar {H A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (imBar H A) := by
  refine ⟨⟨⟨fun z w => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨a, haH, haA, ha⟩ := mem_imBar.mp z.2
    obtain ⟨b, hbH, hbA, hb⟩ := mem_imBar.mp w.2
    apply Subtype.ext
    show z.1 * w.1 = w.1 * z.1
    rw [← ha, ← hb, ← bar_mul haH hbH, ← bar_mul hbH haH, B2F.isElemAbelian_comm hA haA hbA]
  · obtain ⟨a, haH, haA, rfl⟩ := mem_imBar.mp hz
    rw [← bar_pow haH, hA.2 a haA, bar_one]

theorem comm_of_inverts {W : Type*} [Group W] {u v t : W} (hu : u * t * u⁻¹ = t⁻¹)
    (hv : v * t * v⁻¹ = t⁻¹) : u⁻¹ * v * t = t * (u⁻¹ * v) := by
  have h1 : u * t = t⁻¹ * u := by
    calc u * t = (u * t * u⁻¹) * u := by group
      _ = t⁻¹ * u := by rw [hu]
  have h2 : v * t = t⁻¹ * v := by
    calc v * t = (v * t * v⁻¹) * v := by group
      _ = t⁻¹ * v := by rw [hv]
  have h3 : t * u⁻¹ = u⁻¹ * t⁻¹ := by
    calc t * u⁻¹ = u⁻¹ * (u * t) * u⁻¹ := by group
      _ = u⁻¹ * t⁻¹ := by rw [h1]; group
  calc u⁻¹ * v * t = u⁻¹ * (v * t) := by group
    _ = u⁻¹ * (t⁻¹ * v) := by rw [h2]
    _ = (u⁻¹ * t⁻¹) * v := by group
    _ = (t * u⁻¹) * v := by rw [h3]
    _ = t * (u⁻¹ * v) := by group

theorem bar_conj_comm {H : Subgroup G} {a x : G} (ha : a ∈ H) (hx : x ∈ H) :
    bar H (a * x * a⁻¹ * x⁻¹) = bar H a * bar H x * (bar H a)⁻¹ * (bar H x)⁻¹ := by
  rw [bar_mul (H.mul_mem (H.mul_mem ha hx) (H.inv_mem ha)) (H.inv_mem hx),
    bar_mul (H.mul_mem ha hx) (H.inv_mem ha), bar_mul ha hx, bar_inv ha, bar_inv hx]

theorem bar_conj_mul {H : Subgroup G} {a x : G} (ha : a ∈ H) (hx : x ∈ H) :
    bar H (a * x * a⁻¹ * x) = bar H a * bar H x * (bar H a)⁻¹ * bar H x := by
  rw [bar_mul (H.mul_mem (H.mul_mem ha hx) (H.inv_mem ha)) hx,
    bar_mul (H.mul_mem ha hx) (H.inv_mem ha), bar_mul ha hx, bar_inv ha]

variable [Finite G]

theorem exists_dihData {H C A : Subgroup G} (hCH : C ≤ H)
    (hCn : H ≤ Subgroup.normalizer (C : Set G)) (hCsyl : IsSylowTwoOf (pCoreOf 2 H) C)
    (hAH : A ≤ H) (hAe : IsElemAbelian 2 A) {x : G} (hxH : x ∈ H) (hxC : x ∉ C) (hx3 : x ^ 3 ∈ C)
    (hxA : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ C ∨ a * x * a⁻¹ * x ∈ C)
    (hxinv : ∃ a ∈ A, a * x * a⁻¹ * x ∈ C) :
    ∃ (y : OTwoQuot H) (A₀ : Subgroup (OTwoQuot H)) (a₁ : G), a₁ ∈ A ∧
      DihData y (imBar H A) A₀ (bar H a₁) ∧ (bar H x)⁻¹ * y ∈ imBar H C := by
  have hQC : pCoreOf 2 H ≤ C := hCsyl.1
  have hĈn : (imBar H C).Normal := normal_imBar hCn
  have hodd : Odd (Nat.card (imBar H C)) := odd_card_imBar hCH hCsyl
  have hÂe : IsElemAbelian 2 (imBar H A) := isElemAbelian_imBar hAe
  let q : OTwoQuot H →* OTwoQuot H ⧸ imBar H C := QuotientGroup.mk' (imBar H C)
  have hq : ∀ z, z ∈ imBar H C ↔ q z = 1 := fun z => (QuotientGroup.eq_one_iff z).symm
  have hqC : ∀ g ∈ H, g ∈ C ↔ q (bar H g) = 1 := fun g hg =>
    ((bar_mem_imBar_iff hQC hg).symm.trans (hq _))
  have hx3q : q (bar H x) ^ 3 = 1 := by
    rw [← map_pow, ← hq, ← bar_pow hxH]
    exact bar_mem_imBar (H.pow_mem hxH 3) hx3
  have hxne : q (bar H x) ≠ 1 := fun h => hxC ((hqC x hxH).mpr h)
  have hcomm_iff : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ C ↔
      q (bar H a) * q (bar H x) = q (bar H x) * q (bar H a) := by
    intro a ha
    have haH := hAH ha
    rw [hqC _ (H.mul_mem (H.mul_mem (H.mul_mem haH hxH) (H.inv_mem haH)) (H.inv_mem hxH)),
      bar_conj_comm haH hxH]
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  have hinv_iff : ∀ a ∈ A, a * x * a⁻¹ * x ∈ C ↔
      q (bar H a) * q (bar H x) * (q (bar H a))⁻¹ = (q (bar H x))⁻¹ := by
    intro a ha
    have haH := hAH ha
    rw [hqC _ (H.mul_mem (H.mul_mem (H.mul_mem haH hxH) (H.inv_mem haH)) hxH),
      bar_conj_mul haH hxH]
    simp only [map_mul, map_inv]
    rw [mul_eq_one_iff_eq_inv]
  let A₀ : Subgroup (OTwoQuot H) :=
    imBar H A ⊓ (Subgroup.centralizer ({q (bar H x)} : Set _)).comap q
  have hA₀ : ∀ z, z ∈ A₀ ↔ z ∈ imBar H A ∧ q z * q (bar H x) = q (bar H x) * q z := fun z => by
    show z ∈ imBar H A ∧ z ∈ (Subgroup.centralizer ({q (bar H x)} : Set _)).comap q ↔ _
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  have hA₀fix : ∀ z ∈ A₀, z * bar H x * z⁻¹ * (bar H x)⁻¹ ∈ imBar H C := by
    intro z hz
    have := ((hA₀ z).mp hz).2
    rw [hq]
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact this
  have hA₀p : IsPGroup 2 A₀ :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono inf_le_left hÂe)
  obtain ⟨y₀, hy₀C, hy₀fix⟩ := exists_fixed_mem_coset hodd hA₀p hA₀fix
  obtain ⟨a₁, ha₁A, ha₁⟩ := hxinv
  have ha₁H := hAH ha₁A
  have hâ₁inv := (hinv_iff a₁ ha₁A).mp ha₁
  have hâ₁sq : bar H a₁ * bar H a₁ = 1 := by
    rw [← bar_mul ha₁H ha₁H, ← pow_two, hAe.2 a₁ ha₁A, bar_one]
  have hqy₀ : q y₀ = q (bar H x) := by
    have := (hq _).mp hy₀C
    simp only [map_mul, map_inv] at this
    exact (inv_mul_eq_one.mp this).symm
  set y := y₀⁻¹ * (bar H a₁ * y₀ * (bar H a₁)⁻¹) with hy
  have hqy : q y = q (bar H x) := by
    rw [hy]
    simp only [map_mul, map_inv]
    rw [hqy₀, hâ₁inv]
    have : q (bar H x) * q (bar H x) = (q (bar H x))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      simpa [pow_succ, mul_assoc] using hx3q
    calc (q (bar H x))⁻¹ * (q (bar H x))⁻¹ = (q (bar H x) * q (bar H x))⁻¹ := by group
      _ = q (bar H x) := by rw [this, inv_inv]
  refine ⟨y, A₀, a₁, ha₁A, ⟨?_, ?_, hÂe, inf_le_left, bar_mem_imBar ha₁H ha₁A, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    have hy3 : y ^ 3 ∈ imBar H C := by
      rw [hq, map_pow, hqy]
      exact hx3q
    have hd1 : orderOf (y ^ 3) ∣ Nat.card (imBar H C) := Subgroup.orderOf_dvd_natCard _ hy3
    have hodd3 : Odd (orderOf (y ^ 3)) := Odd.of_dvd_nat hodd hd1
    have hd2 : orderOf y ∣ 3 * orderOf (y ^ 3) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    exact Odd.of_dvd_nat (Odd.mul (by decide) hodd3) hd2
  · intro h1
    exact hxne (by rw [← hqy, h1, map_one])
  ·
    intro h0
    have hc := ((hA₀ _).mp h0).2
    have h2 : q (bar H x) * q (bar H x) = 1 := by
      calc q (bar H x) * q (bar H x) = (q (bar H a₁) * q (bar H x) * (q (bar H a₁))⁻¹) *
          q (bar H x) := by rw [hc]; group
        _ = 1 := by rw [hâ₁inv]; group
    have : q (bar H x) = 1 := by
      calc q (bar H x) = q (bar H x) ^ 3 * (q (bar H x) * q (bar H x))⁻¹ := by group
        _ = 1 := by rw [hx3q, h2]; group
    exact hxne this
  ·
    intro z hz
    obtain ⟨a, haH, haA, rfl⟩ := mem_imBar.mp hz
    rcases hxA a haA with h1 | h1
    · left
      exact (hA₀ _).mpr ⟨hz, (hcomm_iff a haA).mp h1⟩
    · right
      have hu := (hinv_iff a haA).mp h1
      refine (hA₀ _).mpr ⟨(imBar H A).mul_mem
        ((imBar H A).inv_mem (bar_mem_imBar ha₁H ha₁A)) hz, ?_⟩
      simp only [map_mul, map_inv]
      exact comm_of_inverts hâ₁inv hu
  ·
    intro a ha
    have haA := ((hA₀ a).mp ha).1
    have hcomm : a * bar H a₁ = bar H a₁ * a := by
      obtain ⟨b, hbH, hbA, rfl⟩ := mem_imBar.mp haA
      rw [← bar_mul hbH ha₁H, ← bar_mul ha₁H hbH, B2F.isElemAbelian_comm hAe hbA ha₁A]
    have hfix := hy₀fix a ha
    have e1 : a * y₀⁻¹ * a⁻¹ = y₀⁻¹ := by
      calc a * y₀⁻¹ * a⁻¹ = (a * y₀ * a⁻¹)⁻¹ := by group
        _ = y₀⁻¹ := by rw [hfix]
    have hb : a * bar H a₁ * a⁻¹ = bar H a₁ := by rw [hcomm]; group
    have hb' : a * (bar H a₁)⁻¹ * a⁻¹ = (bar H a₁)⁻¹ := by
      calc a * (bar H a₁)⁻¹ * a⁻¹ = (a * bar H a₁ * a⁻¹)⁻¹ := by group
        _ = (bar H a₁)⁻¹ := by rw [hb]
    have e2 : a * (bar H a₁ * y₀ * (bar H a₁)⁻¹) * a⁻¹ = bar H a₁ * y₀ * (bar H a₁)⁻¹ := by
      calc a * (bar H a₁ * y₀ * (bar H a₁)⁻¹) * a⁻¹
          = (a * bar H a₁ * a⁻¹) * (a * y₀ * a⁻¹) * (a * (bar H a₁)⁻¹ * a⁻¹) := by group
        _ = bar H a₁ * y₀ * (bar H a₁)⁻¹ := by rw [hb, hfix, hb']
    calc a * y * a⁻¹ = (a * y₀⁻¹ * a⁻¹) * (a * (bar H a₁ * y₀ * (bar H a₁)⁻¹) * a⁻¹) := by
          rw [hy]; group
      _ = y := by rw [e1, e2]
  · exact exists_lift_inverted hâ₁sq
  · rw [hq]
    simp only [map_mul, map_inv]
    rw [hqy]
    group

end X1512

end CFSG.Quasithin

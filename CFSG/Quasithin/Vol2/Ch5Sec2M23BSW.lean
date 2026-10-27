module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoOrder
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneQuotient

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.BenderSuzuki.PFAppendixIII CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G]

theorem exists_conj_eq_or_eq_inv_of_order_three {X : Subgroup G} [Finite X]
    (h9 : ¬ 9 ∣ Nat.card X) {a b : G} (ha : a ∈ X) (hb : b ∈ X) (ha3 : orderOf a = 3)
    (hb3 : orderOf b = 3) : ∃ c ∈ X, c * b * c⁻¹ = a ∨ c * b * c⁻¹ = a⁻¹ := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a' : ↥X := ⟨a, ha⟩
  set b' : ↥X := ⟨b, hb⟩
  have ha'3 : orderOf a' = 3 := by rw [← Subgroup.orderOf_coe]; exact ha3
  have hb'3 : orderOf b' = 3 := by rw [← Subgroup.orderOf_coe]; exact hb3
  have hsyl : ∀ z : ↥X, orderOf z = 3 → ¬ 3 ∣ (Subgroup.zpowers z).index := by
    intro z hz h
    apply h9
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers z)
    rw [Nat.card_zpowers, hz] at h1
    rw [← h1]
    exact Nat.mul_dvd_mul_left 3 h
  have hPa : IsPGroup 3 (Subgroup.zpowers a') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha'3, pow_one])
  have hPb : IsPGroup 3 (Subgroup.zpowers b') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb'3, pow_one])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥X (hPb.toSylow (hsyl b' hb'3))
    (hPa.toSylow (hsyl a' ha'3))
  have hmem : c * b' * c⁻¹ ∈ Subgroup.zpowers a' := by
    have h1 : c * b' * c⁻¹ ∈ ((c • hPb.toSylow (hsyl b' hb'3) : Sylow 3 ↥X) : Subgroup ↥X) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨b', by rw [IsPGroup.toSylow_coe]; exact Subgroup.mem_zpowers b', rfl⟩
    rw [hc, IsPGroup.toSylow_coe] at h1
    exact h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf, ha'3] at hk
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  refine ⟨c, c.2, ?_⟩
  rcases hk3 with h | h | h
  · exfalso
    rw [h, zpow_zero] at hk
    have : b' = 1 := by
      have e := congrArg (fun z => c⁻¹ * z * c) hk
      simp only [mul_one, inv_mul_cancel] at e
      rw [show c⁻¹ * (c * b' * c⁻¹) * c = b' by group] at e
      exact e.symm
    rw [this, orderOf_one] at hb'3
    norm_num at hb'3
  · left
    rw [h, zpow_one] at hk
    exact congrArg Subtype.val hk.symm
  · right
    rw [h] at hk
    have h3' : a' ^ 3 = 1 := by rw [← ha'3]; exact pow_orderOf_eq_one a'
    have e : a' ^ (2 : ℤ) = a'⁻¹ := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, eq_inv_iff_mul_eq_one,
        ← pow_succ, h3']
    rw [e] at hk
    exact congrArg Subtype.val hk.symm

theorem isInvolution_of_orderOf_eq_two {x : G} (h : orderOf x = 2) :
    GorensteinWalter.IsInvolution x :=
  ⟨fun h1 => by rw [h1, orderOf_one] at h; norm_num at h,
    by rw [← h]; exact pow_orderOf_eq_one x⟩

theorem orderOf_eq_two_of_isInvolution {x : G} (h : GorensteinWalter.IsInvolution x) :
    orderOf x = 2 :=
  orderOf_eq_prime h.2 h.1

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_two {t z : G} (ht : orderOf t = 2)
    (hz : z ∈ Subgroup.zpowers t) : z = 1 ∨ z = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← zpow_mod_orderOf, ht]
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem card_centralizer_conj [Finite G] (g w : G) :
    Nat.card (Subgroup.centralizer ({g * w * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({w} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨g⁻¹ * c * g, ?_⟩
      invFun := fun c => ⟨g * c * g⁻¹, ?_⟩
      left_inv := fun c => Subtype.ext (by dsimp only; group)
      right_inv := fun c => Subtype.ext (by dsimp only; group) }
  · have h := Subgroup.mem_centralizer_singleton_iff.mp c.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * c * g * w = g⁻¹ * (c * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * c) * g := by rw [h]
      _ = w * (g⁻¹ * c * g) := by group
  · have h := Subgroup.mem_centralizer_singleton_iff.mp c.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * (g * w * g⁻¹) = g * (c * w) * g⁻¹ := by group
      _ = g * (w * c) * g⁻¹ := by rw [h]
      _ = g * w * g⁻¹ * (g * c * g⁻¹) := by group

theorem centralizer_inv_eq (y : G) :
    Subgroup.centralizer ({y⁻¹} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem exists_conj_eq_or_eq_inv_of_commute [Finite G] {y u w j : G} (hy3 : orderOf y = 3)
    (hu2 : orderOf u = 2) (hyu : y * u = u * y)
    (hinv : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → ∃ g : G, g * i * g⁻¹ = j)
    (h9 : ¬ 9 ∣ Nat.card (Subgroup.centralizer ({u} : Set G))) (hw3 : orderOf w = 3)
    (hj2 : orderOf j = 2) (hwj : w * j = j * w) :
    ∃ g : G, g * w * g⁻¹ = y ∨ g * w * g⁻¹ = y⁻¹ := by
  obtain ⟨h, hh⟩ := hinv j u hj2 hu2
  have hw'3 : orderOf (h * w * h⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hw3
  have hw'u : h * w * h⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hh]
    calc h * w * h⁻¹ * (h * j * h⁻¹) = h * (w * j) * h⁻¹ := by group
      _ = h * (j * w) * h⁻¹ := by rw [hwj]
      _ = h * j * h⁻¹ * (h * w * h⁻¹) := by group
  have hyCu : y ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyu
  obtain ⟨k, -, hk⟩ := exists_conj_eq_or_eq_inv_of_order_three h9 hyCu hw'u hy3 hw'3
  refine ⟨k * h, ?_⟩
  have e : k * h * w * (k * h)⁻¹ = k * (h * w * h⁻¹) * k⁻¹ := by group
  rw [e]
  exact hk

theorem card_centralizer_eq_of_conj [Finite G] {y w g : G}
    (hg : g * w * g⁻¹ = y ∨ g * w * g⁻¹ = y⁻¹) :
    Nat.card (Subgroup.centralizer ({w} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  rw [← card_centralizer_conj g w]
  rcases hg with h | h
  · rw [h]
  · rw [h, centralizer_inv_eq]

theorem card_centralizer_eq_or_of_bsw [Finite G] {E : Subgroup G} {y u r : G}
    (hy3 : orderOf y = 3) (hu2 : orderOf u = 2) (huE : u ∈ E)
    (hEy : E ≤ Subgroup.centralizer ({y} : Set G)) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hE4 : Nat.card E = 4)
    (hcent : ∀ g : G, g * y = y * g → g * u = u * g → ∃ e ∈ E, ∃ a : ℕ, g = e * y ^ a)
    (hru : r * u = u * r) (hry : r * y * r⁻¹ = y⁻¹)
    (hinv : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → ∃ g : G, g * i * g⁻¹ = j)
    (h9 : ¬ 9 ∣ Nat.card (Subgroup.centralizer ({u} : Set G))) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) = 36 ∨
      Nat.card (Subgroup.centralizer ({y} : Set G)) = 180 := by
  classical
  set C := Subgroup.centralizer ({y} : Set G) with hCdef
  have hmemC : ∀ g : G, g ∈ C ↔ g * y = y * g := fun g => Subgroup.mem_centralizer_singleton_iff
  have hyC : y ∈ C := (hmemC y).mpr rfl
  set y₀ : ↥C := ⟨y, hyC⟩ with hy₀
  set Y : Subgroup ↥C := Subgroup.zpowers y₀ with hYdef
  have hcomm₀ : ∀ c : ↥C, Commute c y₀ := fun c => Subtype.ext ((hmemC c).mp c.2)
  have hYn : Y.Normal := by
    refine ⟨fun n hn c => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((hcomm₀ c).zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers y₀ k
  have hY3 : Nat.card Y = 3 := by
    rw [hYdef, Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hy3
  have hYodd : Odd (Nat.card Y) := by rw [hY3]; decide
  set mk : ↥C →* ↥C ⧸ Y := QuotientGroup.mk' Y with hmk
  have hmk1 : ∀ c : ↥C, mk c = 1 ↔ c ∈ Y := fun c => by
    rw [← MonoidHom.mem_ker, hmk, QuotientGroup.ker_mk']
  have hYG : ∀ c : ↥C, c ∈ Y → (c : G) ∈ Subgroup.zpowers y := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [Subgroup.coe_zpow]⟩
  have hEY : ∀ e ∈ E, e ∈ Subgroup.zpowers y → e = 1 := by
    intro e he hey
    have h1 : orderOf e ∣ 3 := hy3 ▸ orderOf_dvd_of_mem_zpowers hey
    have h2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hE2 e he)
    have h3 : orderOf e ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 3 2 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have huC : u ∈ C := hEy huE
  set u₀ : ↥C := ⟨u, huC⟩ with hu₀
  have hu₀2 : orderOf u₀ = 2 := by rw [← Subgroup.orderOf_coe]; exact hu2
  set t : ↥C ⧸ Y := mk u₀ with ht
  have ht2 : orderOf t = 2 := orderOf_mk_eq_two hYodd hu₀2
  set E₀ : Subgroup ↥C := E.subgroupOf C with hE₀
  have hmemE₀ : ∀ c : ↥C, c ∈ E₀ ↔ (c : G) ∈ E := fun c => Subgroup.mem_subgroupOf
  set H : Subgroup (↥C ⧸ Y) := Subgroup.centralizer ({t} : Set (↥C ⧸ Y)) with hHdef
  have hH : H = E₀.map mk := by
    rw [hHdef, ht, hmk, ← map_centralizer_eq hYodd hu₀2]
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      have hcu : (c : G) * u = u * c := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hc
        exact congrArg Subtype.val this
      obtain ⟨e, he, a, hea⟩ := hcent c ((hmemC c).mp c.2) hcu
      have heC : e ∈ C := hEy he
      refine ⟨⟨e, heC⟩, (hmemE₀ _).mpr he, ?_⟩
      have hc' : c = ⟨e, heC⟩ * y₀ ^ a := Subtype.ext (by rw [hea]; rfl)
      have hya : QuotientGroup.mk' Y (y₀ ^ a) = 1 :=
        (hmk1 _).mpr (Subgroup.npow_mem_zpowers y₀ a)
      rw [hc', map_mul, hya, mul_one]
    · rintro _ ⟨c, hc, rfl⟩
      refine ⟨c, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hEc c ((hmemE₀ c).mp hc) u huE)
  have hinj : ∀ a ∈ E₀, ∀ b ∈ E₀, mk a = mk b → a = b := by
    intro a ha b hb hab
    have h1 : mk (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : a * b⁻¹ ∈ E₀ := E₀.mul_mem ha (E₀.inv_mem hb)
    have h3 := hEY _ ((hmemE₀ _).mp h2) (hYG _ ((hmk1 _).mp h1))
    have h4 : a * b⁻¹ = 1 := Subtype.ext h3
    exact mul_inv_eq_one.mp h4
  have hH4 : Nat.card H = 4 := by
    have h1 : Nat.card E₀ = 4 := by
      rw [← hE4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEy).toEquiv
    rw [hH, ← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn, ← h1]
    · rfl
    · intro a ha b hb hab
      exact hinj a ha b hb hab
  have hHmem : ∀ z ∈ H, ∃ c ∈ E₀, mk c = z := by
    intro z hz
    rw [hH] at hz
    obtain ⟨c, hc, rfl⟩ := hz
    exact ⟨c, hc, rfl⟩
  have hHsq : ∀ z ∈ H, z * z = 1 := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := hHmem z hz
    rw [← map_mul, show c * c = 1 from Subtype.ext (hE2 _ ((hmemE₀ c).mp hc)), map_one]
  have hHc : ∀ z ∈ H, ∀ w ∈ H, z * w = w * z := by
    intro z hz w hw
    obtain ⟨c, hc, rfl⟩ := hHmem z hz
    obtain ⟨d, hd, rfl⟩ := hHmem w hw
    rw [← map_mul, ← map_mul,
      show c * d = d * c from Subtype.ext (hEc _ ((hmemE₀ c).mp hc) _ ((hmemE₀ d).mp hd))]
  obtain ⟨e, he, heu⟩ : ∃ e ∈ E, e ∉ Subgroup.zpowers u := by
    by_contra hcon
    have hle : E ≤ Subgroup.zpowers u := fun e he => by
      by_contra h
      exact hcon ⟨e, he, h⟩
    have := Subgroup.card_le_of_le hle
    rw [hE4, Nat.card_zpowers, hu2] at this
    norm_num at this
  set e₀ : ↥C := ⟨e, hEy he⟩ with he₀
  set s : ↥C ⧸ Y := mk e₀ with hs
  set K : Subgroup (↥C ⧸ Y) := Subgroup.zpowers t with hK
  have htH : t ∈ H := by
    rw [hH]
    exact ⟨u₀, (hmemE₀ u₀).mpr huE, rfl⟩
  have hsH : s ∈ H := by
    rw [hH]
    exact ⟨e₀, (hmemE₀ e₀).mpr he, rfl⟩
  have hsK : s ∉ K := by
    intro hsK
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsK
    have h1 : mk (u₀ ^ k) = mk e₀ := by rw [map_zpow]; exact hk
    have h2 := hinj _ (E₀.zpow_mem ((hmemE₀ u₀).mpr huE) k) _ ((hmemE₀ e₀).mpr he) h1
    apply heu
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_zpow] at h3
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, h3⟩
  have hs_inv : GorensteinWalter.IsInvolution s :=
    ⟨fun h => hsK (h ▸ K.one_mem), by rw [pow_two]; exact hHsq s hsH⟩
  have hKH : K ≤ H := Subgroup.zpowers_le.mpr htH
  have hK2 : Nat.card K = 2 := by rw [hK, Nat.card_zpowers, ht2]
  have hJ : K ⊔ Subgroup.zpowers s = H := by
    have hJH : K ⊔ Subgroup.zpowers s ≤ H := sup_le hKH (Subgroup.zpowers_le.mpr hsH)
    have hd1 : Nat.card ↥(K ⊔ Subgroup.zpowers s) ∣ 4 := hH4 ▸ Subgroup.card_dvd_of_le hJH
    have hd2 : 2 ∣ Nat.card ↥(K ⊔ Subgroup.zpowers s) :=
      hK2 ▸ Subgroup.card_dvd_of_le le_sup_left
    have hne : Nat.card ↥(K ⊔ Subgroup.zpowers s) ≠ 2 := by
      intro h2
      have : K = K ⊔ Subgroup.zpowers s :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h2, hK2])
      apply hsK
      rw [this]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    have h4 : Nat.card ↥(K ⊔ Subgroup.zpowers s) = 4 := by
      have hle : Nat.card ↥(K ⊔ Subgroup.zpowers s) ≤ 4 := Nat.le_of_dvd (by norm_num) hd1
      generalize Nat.card ↥(K ⊔ Subgroup.zpowers s) = c at hd1 hd2 hne hle ⊢
      interval_cases c <;> omega
    exact Subgroup.eq_of_le_of_card_ge hJH (by rw [hH4, h4])
  have hfix : K ⊓ Subgroup.centralizer ({s} : Set (↥C ⧸ Y)) = Subgroup.zpowers t := by
    apply inf_of_le_left
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hHc z (hKH hz) s hsH
  have hinvK : ∀ x : ↥C ⧸ Y, x ∈ K → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have hxH := hKH hx
    rw [hHc s hsH x hxH, mul_inv_cancel_right]
    exact (inv_eq_of_mul_eq_one_right (hHsq x hxH)).symm
  have ht_inv : GorensteinWalter.IsInvolution t := isInvolution_of_orderOf_eq_two ht2
  have hdisj : ∀ g : ↥C ⧸ Y, g ∉ H → Disjoint K (K.conjBy g) := by
    intro g hg
    rw [Subgroup.disjoint_def]
    intro z hzK hzc
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two ht2 hzK with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw, hwz⟩ := hzc
      have hwz' : g * w * g⁻¹ = z := by simpa [MulAut.conj_apply] using hwz
      rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two ht2 hw with h' | h'
      · rw [h', mul_one, mul_inv_cancel, h] at hwz'
        exact ht_inv.1 hwz'.symm
      · apply hg
        rw [hHdef, Subgroup.mem_centralizer_singleton_iff]
        rw [h', h] at hwz'
        calc g * t = g * t * g⁻¹ * g := by group
          _ = t * g := by rw [hwz']
  have hconj : ∀ v : ↥C ⧸ Y, GorensteinWalter.IsInvolution v →
      ∃ g : ↥C ⧸ Y, g * v * g⁻¹ = t := by
    intro v hv
    obtain ⟨c, hc2, rfl⟩ := exists_involution_lift hYodd (orderOf_eq_two_of_isInvolution hv)
    have hc2' : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hc2
    obtain ⟨h, hh⟩ := hinv (c : G) u hc2' hu2
    have hcy : (c : G) * y = y * c := (hmemC c).mp c.2
    have hyu : y * u = u * y := ((hmemC u).mp huC).symm
    have hy'3 : orderOf (h * y * h⁻¹) = 3 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hy3
    have hy'u : h * y * h⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hh]
      calc h * y * h⁻¹ * (h * ↑c * h⁻¹) = h * (y * c) * h⁻¹ := by group
        _ = h * (c * y) * h⁻¹ := by rw [hcy]
        _ = h * ↑c * h⁻¹ * (h * y * h⁻¹) := by group
    have hyCu : y ∈ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyu
    obtain ⟨k, hk, hk'⟩ := exists_conj_eq_or_eq_inv_of_order_three h9 hyCu hy'u hy3 hy'3
    have hku : k * u = u * k := Subgroup.mem_centralizer_singleton_iff.mp hk
    obtain ⟨g₀, hg₀y, hg₀c⟩ : ∃ g₀ : G, g₀ * y * g₀⁻¹ = y ∧ g₀ * c * g₀⁻¹ = u := by
      rcases hk' with h1 | h1
      · refine ⟨k * h, ?_, ?_⟩
        · calc k * h * y * (k * h)⁻¹ = k * (h * y * h⁻¹) * k⁻¹ := by group
            _ = y := h1
        · calc k * h * ↑c * (k * h)⁻¹ = k * (h * ↑c * h⁻¹) * k⁻¹ := by group
            _ = u := by rw [hh, hku, mul_inv_cancel_right]
      · refine ⟨r * k * h, ?_, ?_⟩
        · calc r * k * h * y * (r * k * h)⁻¹ = r * (k * (h * y * h⁻¹) * k⁻¹) * r⁻¹ := by group
            _ = r * y⁻¹ * r⁻¹ := by rw [h1]
            _ = (r * y * r⁻¹)⁻¹ := by group
            _ = y := by rw [hry, inv_inv]
        · calc r * k * h * ↑c * (r * k * h)⁻¹ = r * (k * (h * ↑c * h⁻¹) * k⁻¹) * r⁻¹ := by
                group
            _ = u := by rw [hh, hku, mul_inv_cancel_right, hru, mul_inv_cancel_right]
    have hg₀C : g₀ ∈ C := (hmemC g₀).mpr (by
      calc g₀ * y = g₀ * y * g₀⁻¹ * g₀ := by group
        _ = y * g₀ := by rw [hg₀y])
    refine ⟨mk ⟨g₀, hg₀C⟩, ?_⟩
    rw [ht, ← map_inv, hmk, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hg₀c
  let hB : BrauerSuzukiWallHypotheses (↥C ⧸ Y) :=
    { t := t
      K := K
      H := H
      s := s
      t_involution := ht_inv
      t_mem_K := Subgroup.mem_zpowers t
      H_eq_centralizer := rfl
      K_commutative := Subgroup.zpowers_isMulCommutative t
      s_involution := hs_inv
      s_not_mem_K := hsK
      H_eq_join := hJ.symm
      fixed_subgroup_eq := hfix
      s_inverts_K := hinvK
      conjugate_disjoint := hdisj
      involutions_conjugate := hconj }
  have hk : Nat.card hB.K = 2 := hK2
  have hQ : Nat.card (↥C ⧸ Y) = 12 ∨ Nat.card (↥C ⧸ Y) = 60 := by
    by_cases hN : Subgroup.normalizer (hB.H : Set (↥C ⧸ Y)) = ⊤
    · left
      obtain ⟨φ⟩ := hB.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
      have h1 := Nat.card_congr φ.toEquiv
      rw [nat_card_alternatingGroup, Nat.card_fin] at h1
      rw [← Subgroup.card_top (G := ↥C ⧸ Y), ← hN, h1]
      rfl
    · right
      exact hB.card_eq_sixty_of_card_K_eq_two_of_normalizer_ne_top hk hN
  have hCQ := Subgroup.card_eq_card_quotient_mul_card_subgroup Y
  rw [hY3] at hCQ
  rcases hQ with h | h
  · left
    rw [hCQ, h]
  · right
    rw [hCQ, h]

end CFSG.Quasithin.H13

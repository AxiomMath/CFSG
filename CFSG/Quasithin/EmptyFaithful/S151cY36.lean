module

public import CFSG.Quasithin.EmptyFaithful.S151cShape
public import CFSG.Quasithin.EmptyFaithful.S151cGrp
public import CFSG.Quasithin.EmptyFaithful.S151cOm4

public section

namespace CFSG.Quasithin

section Y36

theorem y36_two_pow_dvd_six {n : ℕ} (h : 2 ^ n ∣ 6) : 2 ^ n ∣ 2 := by
  have hn : n ≤ 1 := by
    by_contra hn
    have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans h
    omega
  interval_cases n <;> simp

theorem y36_two_pow_dvd_thirty_six {n : ℕ} (h : 2 ^ n ∣ 36) : 2 ^ n ∣ 4 := by
  have hn : n ≤ 2 := by
    by_contra hn
    have h8 : 2 ^ 3 ∣ 36 := (pow_dvd_pow 2 (by omega)).trans h
    omega
  interval_cases n <;> simp

theorem y36_orderOf_eq_two {G : Type*} [Group G] {g : G} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    (hg6 : orderOf g ∣ 6) (hg1 : g ≠ 1) : orderOf g = 2 := by
  have hd1 : orderOf g ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hg
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  rw [hj] at hg6 ⊢
  have h2 := y36_two_pow_dvd_six hg6
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.mp (by simpa using hj))
  have hj1 : j ≤ 1 := by
    by_contra hn
    have : 2 ^ 2 ∣ 2 := (pow_dvd_pow 2 (by omega)).trans h2
    omega
  have : j = 1 := by omega
  rw [this]
  norm_num

theorem y36_even_dvd_six {n : ℕ} (h6 : n ∣ 6) (h2 : 2 ∣ n) : n = 2 ∨ n = 6 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases n <;> omega

theorem y36_card_eq_six {G : Type*} [Group G] {L : Subgroup G} (e : ↥L ≃* DihedralGroup 3) :
    Nat.card L = 6 := by
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem y36_decomp {G : Type*} [Group G] {L Y : Subgroup G} (e : ↥L ≃* DihedralGroup 3)
    (hLY : L ≤ Y) (hYn : Y ≤ Subgroup.normalizer (L : Set G)) {y : G} (hy : y ∈ Y) :
    ∃ l ∈ L, ∃ d ∈ Y ⊓ Subgroup.centralizer (L : Set G), y = l * d := by
  obtain ⟨l, hl, d, hd, hdc, rfl⟩ := exists_mul_eq_of_normalizes_D3 e hLY (fun x hx => hYn hx) hy
  exact ⟨l, hl, d, ⟨hd, Subgroup.mem_centralizer_iff.mpr fun m hm => (hdc m hm).symm⟩, rfl⟩

theorem y36_eq_sup {G : Type*} [Group G] {L Y : Subgroup G} (e : ↥L ≃* DihedralGroup 3)
    (hLY : L ≤ Y) (hYn : Y ≤ Subgroup.normalizer (L : Set G)) :
    Y = L ⊔ (Y ⊓ Subgroup.centralizer (L : Set G)) := by
  refine le_antisymm (fun y hy => ?_) (sup_le hLY inf_le_left)
  obtain ⟨l, hl, d, hd, rfl⟩ := y36_decomp e hLY hYn hy
  exact Subgroup.mul_mem_sup hl hd

theorem y36_card_eq {G : Type*} [Group G] {L Y : Subgroup G} (e : ↥L ≃* DihedralGroup 3)
    (hLY : L ≤ Y) (hYn : Y ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card Y = 6 * Nat.card ↥(Y ⊓ Subgroup.centralizer (L : Set G)) := by
  have hcomm : ∀ a ∈ L, ∀ b ∈ Y ⊓ Subgroup.centralizer (L : Set G), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a ha
  have hinf : L ⊓ (Y ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h1 : x ∈ L ⊓ Subgroup.centralizer (L : Set G) := ⟨hx.1, hx.2.2⟩
    rw [inf_centralizer_eq_bot_D3 e] at h1
    exact Subgroup.mem_bot.mp h1
  have h := card_sup_of_commute hcomm hinf
  rw [← y36_eq_sup e hLY hYn, y36_card_eq_six e] at h
  exact h

theorem y36_card_dvd_four {G : Type*} [Group G] [Finite G] {P Y : Subgroup G}
    (hP : IsPGroup 2 P) (hPY : P ≤ Y) (hY : Nat.card Y ∣ 36) : Nat.card P ∣ 4 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  rw [hn]
  exact y36_two_pow_dvd_thirty_six (hn ▸ (Subgroup.card_dvd_of_le hPY).trans hY)

theorem y36_closure_eq_top {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16)
    {L : Subgroup (MulAut U)} (e : ↥L ≃* DihedralGroup 3)
    (hfix : ∀ g ∈ L, orderOf g = 3 → ∀ u : U, g u = u → u = 1)
    {t : MulAut U} (htL : t ∈ L) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Subgroup.closure {x : U | ∃ g ∈ L, ∃ z ∈ fixV (Subgroup.zpowers t), g z = x} = ⊤ := by
  set a : MulAut U := ((e.symm (DihedralGroup.r 1) : ↥L) : MulAut U) with ha
  have haL : a ∈ L := (e.symm (DihedralGroup.r 1)).2
  have hordA : orderOf a = 3 := by
    rw [ha, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact DihedralGroup.orderOf_r_one
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [hordA] at this
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordA
    omega
  have hfixa : ∀ u : U, a u = u → u = 1 := fun u hu => hfix a haL hordA u hu
  have hta : t * a * t⁻¹ = a⁻¹ := by
    have hD : ∀ d : DihedralGroup 3, d ≠ 1 → d * d = 1 →
        d * DihedralGroup.r 1 * d⁻¹ = (DihedralGroup.r 1)⁻¹ := by decide
    set τ : ↥L := ⟨t, htL⟩ with hτ
    have hτ1 : e τ ≠ 1 := fun h =>
      ht1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
    have hτ2 : e τ * e τ = 1 := by
      have : τ * τ = 1 := Subtype.ext (by simpa [pow_two] using ht2)
      rw [← map_mul, this, map_one]
    have h2 : τ * e.symm (DihedralGroup.r 1) * τ⁻¹ = (e.symm (DihedralGroup.r 1))⁻¹ := by
      apply e.injective
      simpa using hD _ hτ1 hτ2
    exact congrArg (fun x : ↥L => (x : MulAut U)) h2
  refine S3mod_eq_top_of_invariant hU hcard ha3 ha1 ht2 ht1 hta hfixa
    (fun b hb => genTop_invariant haL hb) (fun b hb => genTop_invariant htL hb) ?_
  intro u hu
  exact Subgroup.subset_closure ⟨1, L.one_mem, u, hu, rfl⟩

theorem Y_eq_of_not_genTop {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (hcard : Nat.card U = 16)
    {L Y H : Subgroup (MulAut U)} (e : ↥L ≃* DihedralGroup 3)
    (hfix : ∀ g ∈ L, orderOf g = 3 → ∀ u : U, g u = u → u = 1)
    (hLY : L ≤ Y) (hYn : Y ≤ Subgroup.normalizer (L : Set (MulAut U)))
    (hHY : H ≤ Y) (hH2 : IsPGroup 2 H)
    (ht : ∃ t ∈ H ⊓ L, t ≠ 1)
    (hnot : Subgroup.closure {x : U | ∃ g ∈ L, ∃ z ∈ fixV H, g z = x} ≠ ⊤)
    (hgen : Subgroup.closure {x : U | ∃ g ∈ Y, ∃ z ∈ fixV H, g z = x} = ⊤) :
    Y = L ⊔ Subgroup.centralizer (L : Set (MulAut U)) ∧ Nat.card H = 4 ∧ IsOmegaFourPlus Y := by
  set C : Subgroup (MulAut U) := Subgroup.centralizer (L : Set (MulAut U)) with hC
  set Y' : Subgroup (MulAut U) := Y ⊓ C
  have hLcard : Nat.card L = 6 := y36_card_eq_six e
  have hCcard : Nat.card C = 6 := S3mod_card_centralizer_of_equiv hU hcard e hfix
  have hYeq : Y = L ⊔ Y' := y36_eq_sup e hLY hYn
  have hYcard : Nat.card Y = 6 * Nat.card Y' := y36_card_eq e hLY hYn
  have hY'6 : Nat.card Y' ∣ 6 := hCcard ▸ Subgroup.card_dvd_of_le inf_le_right
  have hY36 : Nat.card Y ∣ 36 := by
    rw [hYcard]
    exact mul_dvd_mul_left 6 hY'6
  obtain ⟨t, ⟨htH, htL⟩, ht1⟩ := ht
  have hto : orderOf t = 2 := by
    obtain ⟨k, hk⟩ := hH2 ⟨t, htH⟩
    exact y36_orderOf_eq_two (congrArg Subtype.val hk)
      (hLcard ▸ Subgroup.orderOf_dvd_natCard L htL) ht1
  have ht2 : t ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one t
  have hzt : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hto]
  have hHLzt : Subgroup.zpowers t ≤ H := Subgroup.zpowers_le.mpr htH
  have hHL : ¬ H ≤ L := by
    intro hHL
    apply hnot
    have hH6 : Nat.card H ∣ 6 := hLcard ▸ Subgroup.card_dvd_of_le hHL
    have hH2' : Nat.card H ∣ 2 := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hH2
      rw [hn] at hH6 ⊢
      exact y36_two_pow_dvd_six hH6
    have hHt : Subgroup.zpowers t = H :=
      Subgroup.eq_of_le_of_card_ge hHLzt (by rw [hzt]; exact Nat.le_of_dvd (by norm_num) hH2')
    rw [← hHt]
    exact y36_closure_eq_top hU hcard e hfix htL ht1 ht2
  obtain ⟨h0, hh0, hh0L⟩ : ∃ h0 ∈ H, h0 ∉ L := by
    by_contra hcon
    push Not at hcon
    exact hHL hcon
  have hH4 : Nat.card H = 4 := by
    have hHdvd : Nat.card H ∣ 4 := y36_card_dvd_four hH2 hHY hY36
    have hpos : 0 < Nat.card H := Nat.pos_of_dvd_of_pos hHdvd (by norm_num)
    have h2dvd : 2 ∣ Nat.card H := hzt ▸ Subgroup.card_dvd_of_le hHLzt
    have hle : 4 ≤ Nat.card H := by
      by_contra hlt
      have h2 : Nat.card H = 2 := by omega
      have hHt : Subgroup.zpowers t = H :=
        Subgroup.eq_of_le_of_card_ge hHLzt (by rw [hzt, h2])
      exact hh0L (Subgroup.zpowers_le.mpr htL (hHt ▸ hh0))
    exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hHdvd) hle
  obtain ⟨l', hl', d', hd', hh0eq⟩ := y36_decomp e hLY hYn (hHY hh0)
  have hd'1 : d' ≠ 1 := by
    rintro rfl
    exact hh0L (by rw [hh0eq, mul_one]; exact hl')
  have hd'C : d' ∈ C := hd'.2
  have hcomm' : Commute l' d' := Subgroup.mem_centralizer_iff.mp hd'C l' hl'
  have hd'ord : orderOf d' = 2 := by
    obtain ⟨k, hk⟩ := hH2 ⟨h0, hh0⟩
    have hk' : h0 ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [hh0eq, hcomm'.mul_pow] at hk'
    have h1 : d' ^ 2 ^ k = (l' ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hk'
    have h2 : d' ^ 2 ^ k ∈ L ⊓ C :=
      ⟨by rw [h1]; exact L.inv_mem (L.pow_mem hl' _), C.pow_mem hd'C _⟩
    rw [hC, inf_centralizer_eq_bot_D3 e] at h2
    exact y36_orderOf_eq_two (Subgroup.mem_bot.mp h2)
      (hCcard ▸ Subgroup.orderOf_dvd_natCard C hd'C) hd'1
  have h2dvd : 2 ∣ Nat.card Y' := hd'ord ▸ Subgroup.orderOf_dvd_natCard Y' hd'
  rcases y36_even_dvd_six hY'6 h2dvd with h2 | h6
  · exfalso
    have hY'cyc : Subgroup.zpowers d' = Y' :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd')
        (by rw [Nat.card_zpowers, hd'ord, h2])
    have hcen : ∀ b ∈ Y', ∀ y ∈ Y, b * y = y * b := by
      intro b hb y hy
      obtain ⟨l, hl, d, hd, rfl⟩ := y36_decomp e hLY hYn hy
      have hbl : b * l = l * b := (Subgroup.mem_centralizer_iff.mp hb.2 l hl).symm
      have hbd : b * d = d * b := by
        have hb' : b ∈ Subgroup.zpowers d' := hY'cyc ▸ hb
        have hd'' : d ∈ Subgroup.zpowers d' := hY'cyc ▸ hd
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd''
        exact ((Commute.refl d').zpow_zpow m n).eq
      calc b * (l * d) = (b * l) * d := (mul_assoc _ _ _).symm
        _ = l * b * d := by rw [hbl]
        _ = l * (b * d) := mul_assoc _ _ _
        _ = l * (d * b) := by rw [hbd]
        _ = l * d * b := (mul_assoc _ _ _).symm
    have hY'2 : IsPGroup 2 Y' := IsPGroup.of_card (n := 1) (by rw [h2]; norm_num)
    have hsup2 : IsPGroup 2 ↥(H ⊔ Y') :=
      isPGroup_sup_of_commute151c hH2 hY'2 fun a ha b hb => (hcen b hb a (hHY ha)).symm
    have hsupY : H ⊔ Y' ≤ Y := sup_le hHY inf_le_left
    have hsupdvd : Nat.card ↥(H ⊔ Y') ∣ 4 := y36_card_dvd_four hsup2 hsupY hY36
    have hHeq : H = H ⊔ Y' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left
        (by rw [hH4]; exact Nat.le_of_dvd (by norm_num) hsupdvd)
    have hY'H : Y' ≤ H := le_sup_right.trans hHeq.ge
    apply hnot
    refine eq_top_iff.mpr (le_trans (le_of_eq hgen.symm) (Subgroup.closure_mono ?_))
    rintro x ⟨y, hy, z, hz, rfl⟩
    obtain ⟨l, hl, d, hd, rfl⟩ := y36_decomp e hLY hYn hy
    refine ⟨l, hl, z, hz, ?_⟩
    have hdz : d z = z := (mem_fixV.mp hz) d (hY'H hd)
    show l z = (l * d) z
    rw [MulAut.mul_apply, hdz]
  · have hY'C : Y' = C := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hCcard, h6])
    have hYC : Y = L ⊔ C := by rw [hYeq, hY'C]
    refine ⟨hYC, hH4, ?_⟩
    rw [hYC]
    exact isOmegaFourPlus_of_S3_centralizer hU hcard e hfix

end Y36

end CFSG.Quasithin

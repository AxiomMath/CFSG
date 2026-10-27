module

public import CFSG.Quasithin.Vol2.Ch3E213MOS4

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS

variable {K : Type} [Group K] [Finite K]

theorem fix_of_odd (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {M₀ : Subgroup (MulAut K)} {C : Subgroup K} {k : ℕ} (ψ : ↥C ≃* DihedralGroup k)
    (hD : M₀ ⊓ innAut K = C.map MulAut.conj) {u : MulAut K} (hu : u ∈ pCoreOf 2 M₀)
    {c : K} (hc : c ∈ C) (hodd : Odd (orderOf c)) : u c = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huM : u ∈ M₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 M₀ hu
  have hcD : MulAut.conj c ∈ M₀ ⊓ innAut K := hD ▸ ⟨c, hc, rfl⟩
  have hucD : MulAut.conj (u c) ∈ M₀ ⊓ innAut K := by
    rw [← mul_conj_mul_inv]
    exact ⟨M₀.mul_mem (M₀.mul_mem huM hcD.1) (M₀.inv_mem huM), ⟨u c, (mul_conj_mul_inv u c).symm⟩⟩
  obtain ⟨c', hc'C, hc'⟩ := hD ▸ hucD
  have hc'eq : c' = u c := hinj hc'
  have hucC : u c ∈ C := hc'eq ▸ hc'C
  have hoddu : Odd (orderOf (u c)) := by
    rw [MulEquiv.orderOf_eq]
    exact hodd
  have hcomm : c * u c = u c * c := by
    obtain ⟨i, hi⟩ := Dih.exists_eq_r_of_odd (g := ψ ⟨c, hc⟩) (by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hodd)
    obtain ⟨j, hj⟩ := Dih.exists_eq_r_of_odd (g := ψ ⟨u c, hucC⟩) (by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hoddu)
    have h1 : (⟨c, hc⟩ : ↥C) * ⟨u c, hucC⟩ = ⟨u c, hucC⟩ * ⟨c, hc⟩ := by
      apply ψ.injective
      rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
    exact congrArg Subtype.val h1
  have hg : MulAut.conj c * u * (MulAut.conj c)⁻¹ * u⁻¹ ∈ pCoreOf 2 M₀ := by
    refine (pCoreOf 2 M₀).mul_mem ?_ ((pCoreOf 2 M₀).inv_mem hu)
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₀ hcD.1) u).mp hu
  have hgeq : MulAut.conj c * u * (MulAut.conj c)⁻¹ * u⁻¹ = MulAut.conj (c * (u c)⁻¹) := by
    rw [map_mul, ← map_inv u c, ← mul_conj_mul_inv u c⁻¹, map_inv]
    group
  rw [hgeq] at hg
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀ ⟨_, hg⟩
  have h2 : orderOf (c * (u c)⁻¹) ∣ 2 ^ n := by
    rw [← orderOf_injective _ hinj]
    have : (MulAut.conj (c * (u c)⁻¹)) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    exact orderOf_dvd_of_pow_eq_one this
  have hodd2 : Odd (orderOf (c * (u c)⁻¹)) := by
    have hc1 : Commute c (u c)⁻¹ := (Commute.inv_right hcomm)
    have hdvd := hc1.orderOf_mul_dvd_mul_orderOf
    rw [orderOf_inv] at hdvd
    exact Odd.of_dvd_nat (hodd.mul hoddu) hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd2
    exact (Nat.not_even_iff_odd.mpr hodd2) (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff, mul_inv_eq_one] at hj
  exact hj.symm

theorem card_inf_le_two (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {M₀ : Subgroup (MulAut K)} {C : Subgroup K} {k : ℕ} (ψ : ↥C ≃* DihedralGroup k)
    (hk : ∀ j : ℕ, k ≠ 2 ^ j) (hD : M₀ ⊓ innAut K = C.map MulAut.conj)
    {V₀ : Subgroup (MulAut K)} (hVM : V₀ ≤ pCoreOf 2 M₀) (hsq : ∀ v ∈ V₀, v * v = 1) :
    Nat.card ↥(V₀ ⊓ innAut K) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι : ↥C →* MulAut K := MulAut.conj.comp C.subtype with hι
  have hιinj : Function.Injective ι := hinj.comp Subtype.val_injective
  have hιrange : ι.range = M₀ ⊓ innAut K := by
    rw [hD, hι, MonoidHom.range_comp, Subgroup.range_subtype]
  set N' : Subgroup ↥C := (pCoreOf 2 M₀).comap ι with hN'
  set V' : Subgroup ↥C := V₀.comap ι with hV'
  have hVle : V₀ ≤ M₀ := hVM.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M₀)
  have hcardV : Nat.card V' = Nat.card ↥(V₀ ⊓ innAut K) := by
    have h1 : V'.map ι = V₀ ⊓ innAut K := by
      rw [hV', Subgroup.map_comap_eq, hιrange]
      apply le_antisymm
      · exact fun x hx => ⟨hx.2, hx.1.2⟩
      · exact fun x hx => ⟨⟨hVle hx.1, hx.2⟩, hx.1⟩
    rw [← h1]
    exact Nat.card_congr (Subgroup.equivMapOfInjective V' ι hιinj).toEquiv
  rw [← hcardV, Nat.card_congr (Subgroup.equivMapOfInjective V' ψ.toMonoidHom
    ψ.injective).toEquiv]
  refine Dih.card_le_two_of_le_normal hk (N := N'.map ψ.toMonoidHom) ?_ ?_
    (Subgroup.map_mono fun y hy => hVM hy) ?_
  · rintro _ ⟨y, hy, rfl⟩
    set c₁ : ↥C := ψ.symm (DihedralGroup.r 1) with hc₁
    have hc₁M : ι c₁ ∈ M₀ := (hιrange ▸ ⟨c₁, rfl⟩ : ι c₁ ∈ M₀ ⊓ innAut K).1
    refine ⟨c₁ * y * c₁⁻¹, ?_, ?_⟩
    · show ι (c₁ * y * c₁⁻¹) ∈ pCoreOf 2 M₀
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₀ hc₁M) _).mp hy
    · rw [MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv, hc₁, MulEquiv.apply_symm_apply]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀ ⟨ι y, hy⟩
    refine ⟨j, ?_⟩
    have h1 : ι (y ^ 2 ^ j) = ι 1 := by
      rw [map_pow, map_one]
      exact congrArg Subtype.val hj
    rw [← map_pow, hιinj h1, map_one]
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : ι (y * y) = ι 1 := by
      rw [map_mul, map_one]
      exact hsq _ hy
    rw [← map_mul, hιinj h1, map_one]

omit [Finite K] in
theorem exists_orderOf_eq {C : Subgroup K} {k a m : ℕ} (ψ : ↥C ≃* DihedralGroup k)
    (hk : k = 2 ^ a * m) (hm : 2 ≤ m) : ∃ c ∈ C, orderOf c = m := by
  refine ⟨(ψ.symm (DihedralGroup.r ((2 ^ a : ℕ) : ZMod k)) : K), Subtype.prop _, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Dih.orderOf_r_two_pow hk hm]

variable {F : Type} [Field F] [Finite F]

theorem card_of_isDihedralOrder {Y : Type} [Group Y] {d : ℕ} (h : IsDihedralOrder Y d) :
    Nat.card Y = d := by
  obtain ⟨k, rfl, -, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]

theorem mem_innAut_of_mem (h13b : IVK_1_3b) (hF : L2Field F) (e : K ≃* L2 F)
    (hq : (Nat.card F : ℤ) ≡ 1 [ZMOD 4])
    {M₀ : Subgroup (MulAut K)} {C : Subgroup K} {k a m : ℕ} (ψ : ↥C ≃* DihedralGroup k)
    (hD : M₀ ⊓ innAut K = C.map MulAut.conj) (hk : k = 2 ^ a * m) (hm3 : 3 ≤ m)
    (hmodd : Odd m) (hkq : 2 * k + 1 = Nat.card F)
    {v : MulAut K} (hv : v ∈ pCoreOf 2 M₀) (hvD : v ∈ innDiagSub e) (hv2 : orderOf v = 2) :
    v ∈ innAut K := by
  by_contra hvI
  have hinj := conj_injective_of_L2 e
  obtain ⟨c, hcC, hcm⟩ := exists_orderOf_eq ψ hk (by omega)
  have hfix : v c = c := fix_of_odd hinj ψ hD hv hcC (hcm ▸ hmodd)
  have hcard := card_of_isDihedralOrder
    ((h13b F hF K e 1 (Or.inl rfl) hq (Nat.card F + 1) (by push_cast; ring) v hvD hvI hv2).2.1)
  have h1 : m ∣ Nat.card F + 1 := by
    rw [← hcm, ← hcard]
    exact Subgroup.orderOf_dvd_natCard (fixedSubgroup K v) (show c ∈ fixedSubgroup K v from hfix)
  have h2 : m ∣ Nat.card F - 1 := by
    rw [← hkq, Nat.add_sub_cancel, hk]
    exact Dvd.intro_left (2 * 2 ^ a) (by ring)
  have h3 : m ∣ 2 := by
    have := Nat.dvd_sub h1 h2
    rwa [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at this
  have := Nat.le_of_dvd two_pos h3
  omega

end CFSG.Quasithin.Ch3E213M.OS

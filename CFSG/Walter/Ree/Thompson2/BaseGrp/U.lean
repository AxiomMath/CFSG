module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.Real

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward

theorem pow_odd_inv {G : Type*} [Group G] {x c : G} (hx : x * c * x⁻¹ = c⁻¹) (m : ℕ) :
    x ^ (2 * m + 1) * c * (x ^ (2 * m + 1))⁻¹ = c⁻¹ := by
  have hx2 : x ^ 2 * c * (x ^ 2)⁻¹ = c := by
    calc x ^ 2 * c * (x ^ 2)⁻¹ = x * (x * c * x⁻¹) * x⁻¹ := by rw [sq]; group
      _ = c := by rw [hx, show x * c⁻¹ * x⁻¹ = (x * c * x⁻¹)⁻¹ by group, hx, inv_inv]
  have hpow : ∀ m : ℕ, x ^ (2 * m) * c * (x ^ (2 * m))⁻¹ = c := by
    intro m
    induction m with
    | zero => group
    | succ m ih =>
      calc x ^ (2 * (m + 1)) * c * (x ^ (2 * (m + 1)))⁻¹
          = x ^ 2 * (x ^ (2 * m) * c * (x ^ (2 * m))⁻¹) * (x ^ 2)⁻¹ := by
            rw [show 2 * (m + 1) = 2 + 2 * m by ring, pow_add]; group
        _ = c := by rw [ih, hx2]
  calc x ^ (2 * m + 1) * c * (x ^ (2 * m + 1))⁻¹
      = x * (x ^ (2 * m) * c * (x ^ (2 * m))⁻¹) * x⁻¹ := by rw [pow_succ']; group
    _ = c⁻¹ := by rw [hpow, hx]

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ) [Fintype k]

omit [Fintype k] in
theorem exists_inv_comm_T
    {c : G} (hc7 : orderOf c = 7)
    (hTc : C.T⁻¹ * c * C.T ∈ Subgroup.zpowers c) :
    ∃ u : G, u * u = 1 ∧ u * C.T = C.T * u ∧ u * c * u⁻¹ = c⁻¹ := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨n₀, hn₀⟩ := exists_inv_of_orderOf_seven C.h hc7
  set D : Set G := {x | x * c * x⁻¹ = c⁻¹} with hD
  have hfwd : ∀ z : G, z * c = c * z → n₀ * z * c * (n₀ * z)⁻¹ = c⁻¹ := by
    intro z hz
    calc n₀ * z * c * (n₀ * z)⁻¹ = n₀ * (z * c) * z⁻¹ * n₀⁻¹ := by group
      _ = n₀ * c * n₀⁻¹ := by rw [hz]; group
      _ = c⁻¹ := hn₀
  have hbwd : ∀ x : G, x * c * x⁻¹ = c⁻¹ → n₀⁻¹ * x * c = c * (n₀⁻¹ * x) := by
    intro x hx
    have h1 : n₀⁻¹ * c⁻¹ * n₀ = c := by rw [← hn₀]; group
    calc n₀⁻¹ * x * c = n₀⁻¹ * (x * c * x⁻¹) * x := by group
      _ = n₀⁻¹ * c⁻¹ * n₀ * (n₀⁻¹ * x) := by rw [hx]; group
      _ = c * (n₀⁻¹ * x) := by rw [h1]
  have hDcard : Nat.card D = Nat.card (Subgroup.centralizer ({c} : Set G)) := by
    symm
    refine Nat.card_congr ⟨fun z => ⟨n₀ * z, hfwd z
      (Subgroup.mem_centralizer_singleton_iff.mp z.2)⟩, fun x => ⟨n₀⁻¹ * x,
      Subgroup.mem_centralizer_singleton_iff.mpr (hbwd x x.2)⟩, ?_, ?_⟩
    · intro z; ext; simp
    · intro x; ext; simp
  have h3 : ¬ 3 ∣ Nat.card D := by
    rw [hDcard]
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨⟨y, hy⟩, hyo⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hyo' : orderOf y = 3 := by rw [← Subgroup.orderOf_mk y hy, hyo]
    exact not_commute_three_seven C.h hyo' hc7
      (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hTc
  have hTD : ∀ x ∈ D, C.T * x * C.T⁻¹ ∈ D := by
    intro x hx
    have hx' : x * c * x⁻¹ = c⁻¹ := hx
    change C.T * x * C.T⁻¹ * c * (C.T * x * C.T⁻¹)⁻¹ = c⁻¹
    have hca : C.T * c ^ a * C.T⁻¹ = c := by rw [ha]; group
    have hxa : x * c ^ a * x⁻¹ = (c ^ a)⁻¹ := by
      rw [show x * c ^ a * x⁻¹ = (x * c * x⁻¹) ^ a by
        rw [show x * c * x⁻¹ = MulAut.conj x c from rfl, ← map_zpow]; rfl, hx', inv_zpow]
    calc C.T * x * C.T⁻¹ * c * (C.T * x * C.T⁻¹)⁻¹
          = C.T * (x * (C.T⁻¹ * c * C.T) * x⁻¹) * C.T⁻¹ := by group
      _ = (C.T * c ^ a * C.T⁻¹)⁻¹ := by rw [← ha, hxa]; group
      _ = c⁻¹ := by rw [hca]
  let f : Function.End D := fun x => ⟨C.T * x * C.T⁻¹, hTD x x.2⟩
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    change C.T * (C.T * (C.T * x * C.T⁻¹) * C.T⁻¹) * C.T⁻¹ = x
    rw [show C.T * (C.T * (C.T * (x : G) * C.T⁻¹) * C.T⁻¹) * C.T⁻¹ =
      C.T * C.T * C.T * x * (C.T * C.T * C.T)⁻¹ by group, ← pow_three', C.T_pow_three]
    group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  obtain ⟨⟨x, hxD⟩, hxf⟩ : (Function.fixedPoints f).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Fintype.card (Function.fixedPoints f) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      rintro ⟨y, hy⟩
      rw [hne] at hy
      exact hy
    rw [h0, ← Nat.card_eq_fintype_card] at hmod
    exact h3 (Nat.dvd_of_mod_eq_zero hmod)
  have hxT : C.T * x * C.T⁻¹ = x := congrArg Subtype.val hxf
  have hxT' : x * C.T = C.T * x := by
    calc x * C.T = C.T * x * C.T⁻¹ * C.T := by rw [hxT]
      _ = C.T * x := by group
  have hx : x * c * x⁻¹ = c⁻¹ := hxD
  obtain ⟨e, b, hb, hob⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  obtain ⟨m, rfl⟩ := hb
  set u := x ^ (2 * m + 1) with hu
  have huc : u * c * u⁻¹ = c⁻¹ := pow_odd_inv hx m
  have huT : u * C.T = C.T * u := (Commute.pow_left hxT' _).eq
  have hu2e : u ^ 2 ^ e = 1 := by
    rw [hu, ← pow_mul, mul_comm, ← hob, pow_orderOf_eq_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hup : IsPGroup 2 (Subgroup.zpowers u) := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hd : orderOf (u ^ j) ∣ 2 ^ e := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2e, one_zpow]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨i, by rw [Subgroup.orderOf_mk]; exact hi⟩
  obtain ⟨S', hS'⟩ := hup.exists_le_sylow
  have hu2 : u * u = 1 := by
    have hel := C.h.elementary_sylow S'
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p
      ⟨u, hS' (Subgroup.mem_zpowers u)⟩
    have := congrArg Subtype.val this
    simpa [sq] using this
  exact ⟨u, hu2, huT, huc⟩

theorem exists_u
    (S : Sylow 2 G) (hJS : C.J ∈ (S : Subgroup G)) {c : G} (hc7 : orderOf c = 7)
    (hcN : c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hTc : C.T⁻¹ * c * C.T ∈ Subgroup.zpowers c) :
    ∃ γ : k, γ ≠ 0 ∧
      C.J * C.ι (pp σ 0 0 γ) * c * (C.J * C.ι (pp σ 0 0 γ))⁻¹ = c⁻¹ := by
  obtain ⟨u, hu2, huT, huc⟩ := C.exists_inv_comm_T hc7 hTc
  have huN : u ∈ C.N := C.mem_N_of_commute C.T_mem_P C.T_ne_one huT
  obtain ⟨nn, rfl⟩ := C.exists_ι huN
  have hnn2 : nn * nn = 1 := C.ι_injective (by rw [map_mul, hu2, map_one])
  have hnn1 : nn ≠ 1 := by
    rintro rfl
    rw [map_one, one_mul, inv_one, mul_one] at huc
    have : c ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [huc]; exact inv_mul_cancel c
    have := orderOf_dvd_of_pow_eq_one this
    rw [hc7] at this
    norm_num at this
  have hnnT : nn * tT σ = tT σ * nn := C.ι_injective (by rw [map_mul, map_mul]; exact huT)
  obtain ⟨γ, rfl⟩ := invol_comm_tT hnn2 hnn1 hnnT
  rw [map_mul] at huc
  refine ⟨γ, ?_, huc⟩
  rintro rfl
  rw [pp_zero, map_one, mul_one] at huc
  have hcJ : c * C.J * c⁻¹ ∈ (S : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hcN _).mp hJS
  have hmem : C.J * (c * C.J * c⁻¹) ∈ (S : Subgroup G) := Subgroup.mul_mem _ hJS hcJ
  have hJc : C.J * c * C.J⁻¹ = c⁻¹ := huc
  have he : C.J * (c * C.J * c⁻¹) = c⁻¹ * c⁻¹ := by
    calc C.J * (c * C.J * c⁻¹) = C.J * c * C.J⁻¹ * c⁻¹ := by rw [C.J_inv]; group
      _ = c⁻¹ * c⁻¹ := by rw [hJc]
  rw [he] at hmem
  have h8 : (c⁻¹ * c⁻¹) ^ 8 = 1 := by
    have := Subgroup.orderOf_dvd_natCard (S : Subgroup G) hmem
    rw [C.h.card_sylow S] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have h16 : c ^ 16 = 1 := by
    rw [show c⁻¹ * c⁻¹ = (c ^ 2)⁻¹ by group, inv_pow, inv_eq_one, ← pow_mul] at h8
    exact h8
  have := orderOf_dvd_of_pow_eq_one h16
  rw [hc7] at this
  norm_num at this

end Ctx

end CFSG.Walter.Ree.T2.BaseGrp

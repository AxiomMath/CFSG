module

public import CFSG.Quasithin.H13.A6S1372L76N3g
public import CFSG.Quasithin.H13.A6S1372L76O

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge CFSG.Assembly.LowTwoRank
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76N3

theorem sl3_pow_84 : ∀ g : SL3.S, g ^ 84 = 1 := by
  intro g
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0e : ∀ q : SL3.S, SL3.InX1 q → SL3.InX2 q → q ^ 4 = 1 := by decide +kernel
  have h168 : g ^ 168 = 1 := by
    rw [← SL3.card_S]
    exact pow_card_eq_one'
  have h8 : (g ^ 21) ^ 2 ^ 3 = 1 := by
    rw [← pow_mul]
    exact h168
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h8)
  have hz : IsPGroup 2 ↥(Subgroup.zpowers (g ^ 21)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hP0 : IsPGroup 2 ↥SL3.P0 := IsPGroup.of_card (n := 3) (by rw [SL3.card_P0]; norm_num)
  have hP0i : ¬ 2 ∣ SL3.P0.index := by
    have h := SL3.P0.card_mul_index
    rw [SL3.card_P0, SL3.card_S] at h
    have h21 : SL3.P0.index = 21 := by omega
    rw [h21]
    decide
  obtain ⟨P, hP⟩ := hz.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq SL3.S (hP0.toSylow hP0i) P
  have hq : g ^ 21 ∈ ((x • hP0.toSylow hP0i : Sylow 2 SL3.S) : Subgroup SL3.S) := by
    rw [hx]
    exact hP (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
  have e : (MulAut.conj x)⁻¹ • g ^ 21 = x⁻¹ * g ^ 21 * x := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  rw [e] at hq
  have hq0 := Subgroup.mem_inf.1 ((IsPGroup.mem_toSylow _ _).1 hq)
  have hq4 := hP0e _ hq0.1 hq0.2
  have e2 : x⁻¹ * (g ^ 21) ^ 4 * x = 1 := by
    have h := conj_pow (a := x⁻¹) (b := g ^ 21) (i := 4)
    rw [inv_inv] at h
    rw [← h, hq4]
  calc g ^ 84 = x * (x⁻¹ * (g ^ 21) ^ 4 * x) * x⁻¹ := by group
    _ = 1 := by rw [e2]; group

theorem pow_four_of_two {g : SL3.S} {j : ℕ} (hg : g ^ 2 ^ j = 1) : g ^ 4 = 1 := by
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hg)
  have h84 := orderOf_dvd_of_pow_eq_one (sl3_pow_84 g)
  rw [he] at h84
  have he2 : e ≤ 2 := by
    by_contra h
    have h8 : 2 ^ 3 ∣ 2 ^ e := Nat.pow_dvd_pow 2 (by omega)
    have := h8.trans h84
    norm_num at this
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [he]
  exact (Nat.pow_dvd_pow 2 he2).trans (by norm_num)

theorem comm_not_two : ∀ κ : SL3.S, κ ^ 3 = 1 → κ ≠ 1 →
    ∃ p : SL3.S, SL3.InX1 p ∧ SL3.InX2 p ∧ (p * κ * p⁻¹ * κ⁻¹) ^ 4 ≠ 1 := by
  decide +kernel

theorem x1_pow_24 : ∀ g : SL3.S, SL3.InX1 g → g ^ 24 = 1 := by
  decide +kernel

theorem x2_pow_24 : ∀ g : SL3.S, SL3.InX2 g → g ^ 24 = 1 := by
  decide +kernel

theorem cube_of_odd {X : Type*} [Monoid X] {g : X} (h24 : g ^ 24 = 1) (hodd : Odd (orderOf g)) :
    g ^ 3 = 1 := by
  have hcop : Nat.Coprime (orderOf g) (2 ^ 3) :=
    Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hodd)
  have h1 : orderOf g ∣ 3 * 2 ^ 3 := orderOf_dvd_of_pow_eq_one (by norm_num; exact h24)
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right h1)

theorem x1_three_conj : ∀ a g : SL3.S, SL3.InX1 a → SL3.InX1 g → a ^ 3 = 1 → a ≠ 1 → g ^ 3 = 1 →
    g = 1 ∨ ∃ h : SL3.S, SL3.InX1 h ∧ (g = h * a * h⁻¹ ∨ g = h * a⁻¹ * h⁻¹) := by
  decide +kernel

theorem x2_three_conj : ∀ a g : SL3.S, SL3.InX2 a → SL3.InX2 g → a ^ 3 = 1 → a ≠ 1 → g ^ 3 = 1 →
    g = 1 ∨ ∃ h : SL3.S, SL3.InX2 h ∧ (g = h * a * h⁻¹ ∨ g = h * a⁻¹ * h⁻¹) := by
  decide +kernel

theorem exists_conj_P0 {P : Subgroup SL3.S} (hP : IsPGroup 2 ↥P) (hodd : ¬ 2 ∣ P.index) :
    ∃ g : SL3.S, ∀ q ∈ SL3.P0, g⁻¹ * q * g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0 : IsPGroup 2 ↥SL3.P0 := IsPGroup.of_card (n := 3) (by rw [SL3.card_P0]; norm_num)
  have hP0i : ¬ 2 ∣ SL3.P0.index := by
    have h := SL3.P0.card_mul_index
    rw [SL3.card_P0, SL3.card_S] at h
    have h21 : SL3.P0.index = 21 := by omega
    rw [h21]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL3.S (hP.toSylow hodd) (hP0.toSylow hP0i)
  refine ⟨g, fun q hq => ?_⟩
  have hq' : q ∈ ((g • hP.toSylow hodd : Sylow 2 SL3.S) : Subgroup SL3.S) := by
    rw [hg]
    exact (IsPGroup.mem_toSylow _ _).2 hq
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq'
  have e : (MulAut.conj g)⁻¹ • q = g⁻¹ * q * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  rw [e] at hq'
  exact (IsPGroup.mem_toSylow _ _).1 hq'

section Inner

open A6L76Of

variable {W : Type} [CommGroup W]

structure NatReal (Y : Subgroup (MulAut W)) where
  π : ↥(StatedSL 3 (ZMod 2)) →* ↥Y
  β : ↥(commV Y) →* Multiplicative (Fin 3 → ZMod 2)
  surj : Function.Surjective π
  inj : Function.Injective π
  βsurj : Function.Surjective β
  βker : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y
  βeq : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥(commV Y))
    (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = natHom γ (β u)

theorem nonempty_natReal {Y : Subgroup (MulAut W)} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {π : ↥(StatedSL 3 F) →* ↥Y}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia Y (commV Y) (fixV Y ⊓ commV Y) π) :
    Nonempty (NatReal Y) := by
  obtain ⟨π', hπ'⟩ := A6L76O.realizesVia_zmod hF hπ
  obtain ⟨hs, -, β, hβs, hβk, hβe0⟩ := A6L76Z.natRealizes_clean hπ'
  exact ⟨⟨π', β, hs, FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ', hβs, hβk,
    fun γ u hu => hβe0 γ u hu⟩⟩

@[expose] def incY {Y : Subgroup (MulAut W)} :
    ↥Y →* ↥(Subgroup.normalizer (Y : Set (MulAut W))) :=
  Subgroup.inclusion Subgroup.le_normalizer

namespace NatReal

variable {Y : Subgroup (MulAut W)} (D : NatReal Y)

@[expose] noncomputable def phiN : ↥(Subgroup.normalizer (Y : Set (MulAut W))) →* SL3.S :=
  toSL.toMonoidHom.comp (liftHom D.βsurj D.βker)

theorem phiN_incY_pi (γ : ↥(StatedSL 3 (ZMod 2))) :
    D.phiN (incY (D.π γ)) = (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm γ := by
  have h := liftHom_of_mem D.βsurj D.βker D.βeq γ (Subgroup.le_normalizer (D.π γ).2)
  have h2 : D.phiN (incY (D.π γ)) = toSL (natHom γ) := congrArg toSL h
  rw [h2]
  show (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm (natHomEquiv.symm (natHom γ)) = _
  rw [← natHomEquiv_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def phiY : ↥Y →* SL3.S := D.phiN.comp incY

theorem phiY_bijective : Function.Bijective D.phiY := by
  refine ⟨fun y₁ y₂ h => ?_, fun A => ?_⟩
  · obtain ⟨γ₁, rfl⟩ := D.surj y₁
    obtain ⟨γ₂, rfl⟩ := D.surj y₂
    have h1 : (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm γ₁ =
        (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm γ₂ := by
      rw [← D.phiN_incY_pi, ← D.phiN_incY_pi]
      exact h
    rw [(specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.injective h1]
  · refine ⟨D.π (specialLinearGroupEquivStatedSL 3 (ZMod 2) A), ?_⟩
    show D.phiN (incY _) = A
    rw [D.phiN_incY_pi, MulEquiv.symm_apply_apply]

@[expose] noncomputable def phiYEquiv : ↥Y ≃* SL3.S :=
  MulEquiv.ofBijective D.phiY D.phiY_bijective

@[expose] noncomputable def kappaN : ↥(Subgroup.normalizer (Y : Set (MulAut W))) →* ↥Y :=
  D.phiYEquiv.symm.toMonoidHom.comp D.phiN

theorem phiN_incY_kappaN (n : ↥(Subgroup.normalizer (Y : Set (MulAut W)))) :
    D.phiN (incY (D.kappaN n)) = D.phiN n :=
  D.phiYEquiv.apply_symm_apply (D.phiN n)

theorem kappaN_incY (y : ↥Y) : D.kappaN (incY y) = y :=
  D.phiYEquiv.symm_apply_apply y

theorem comm_of_phiN_eq_one {n : ↥(Subgroup.normalizer (Y : Set (MulAut W)))}
    (hn : D.phiN n = 1) (y : ↥Y) : (n : MulAut W) * y = y * n := by
  have hy' : (n : MulAut W) * y * (n : MulAut W)⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp n.2 y).mp y.2
  have h1 : D.phiY ⟨_, hy'⟩ = D.phiY y := by
    have e : incY ⟨_, hy'⟩ = n * incY y * n⁻¹ := Subtype.ext rfl
    show D.phiN (incY ⟨_, hy'⟩) = D.phiN (incY y)
    rw [e, map_mul, map_mul, map_inv, hn, one_mul, inv_one, mul_one]
  have h2 : (n : MulAut W) * y * (n : MulAut W)⁻¹ = y :=
    congrArg Subtype.val (D.phiY_bijective.1 h1)
  calc (n : MulAut W) * y = (n : MulAut W) * y * (n : MulAut W)⁻¹ * n := by group
    _ = y * n := by rw [h2]

@[expose] noncomputable def cN :
    ↥(Subgroup.normalizer (Y : Set (MulAut W))) →* ↥(Subgroup.normalizer (Y : Set (MulAut W))) where
  toFun n := (incY (D.kappaN n))⁻¹ * n
  map_one' := by rw [map_one, map_one, inv_one, one_mul]
  map_mul' n m := by
    have hc : D.phiN ((incY (D.kappaN n))⁻¹ * n) = 1 := by
      rw [map_mul, map_inv, D.phiN_incY_kappaN, inv_mul_cancel]
    have hcomm : ((incY (D.kappaN n))⁻¹ * n) * incY (D.kappaN m) =
        incY (D.kappaN m) * ((incY (D.kappaN n))⁻¹ * n) :=
      Subtype.ext (D.comm_of_phiN_eq_one hc (D.kappaN m))
    rw [map_mul, map_mul]
    calc (incY (D.kappaN n) * incY (D.kappaN m))⁻¹ * (n * m) =
          (incY (D.kappaN m))⁻¹ * (((incY (D.kappaN n))⁻¹ * n) * incY (D.kappaN m)) *
            ((incY (D.kappaN m))⁻¹ * m) := by group
      _ = (incY (D.kappaN n))⁻¹ * n * ((incY (D.kappaN m))⁻¹ * m) := by rw [hcomm]; group

theorem cN_apply (n : ↥(Subgroup.normalizer (Y : Set (MulAut W)))) :
    D.cN n = (incY (D.kappaN n))⁻¹ * n := rfl

theorem cN_incY (y : ↥Y) : D.cN (incY y) = 1 := by
  rw [cN_apply, D.kappaN_incY, inv_mul_cancel]

theorem mem_of_cN_eq_one {n : ↥(Subgroup.normalizer (Y : Set (MulAut W)))} (h : D.cN n = 1) :
    (n : MulAut W) ∈ Y := by
  rw [cN_apply, inv_mul_eq_one] at h
  rw [← h]
  exact (D.kappaN n).2

end NatReal

end Inner

end A6L76N3

end CFSG.Quasithin.H13.A6

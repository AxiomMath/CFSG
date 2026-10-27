module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG
open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.fix_tau_mul_t1
    {B : Subgroup G} {b b₁ b₂ b₃ : G}
    (hB : B = (Subgroup.zpowers b ⊔ Subgroup.zpowers b₁) ⊔
      (Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃))
    (hE4 : IsElemAb 3 4 B)
    (hbB : b ∈ B) (hb₁B : b₁ ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B)
    {τX tX : MulAut ↥B}
    (hτXb : τX ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (hτX₁ : τX ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹)
    (hτX₂ : τX ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹)
    (hτX₃ : τX ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹)
    (htXb : tX ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (htX₁ : tX ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹)
    (htX₂ : tX ⟨b₂, hb₂B⟩ = ⟨b₂, hb₂B⟩)
    (htX₃ : tX ⟨b₃, hb₃B⟩ = ⟨b₃, hb₃B⟩) :
    ∀ x : ↥B, (τX * tX) x = x ↔
      x ∈ Subgroup.zpowers (⟨b, hbB⟩ : ↥B) ⊔ Subgroup.zpowers (⟨b₁, hb₁B⟩ : ↥B) := by
  let bB : ↥B := ⟨b, hbB⟩
  let b₁B : ↥B := ⟨b₁, hb₁B⟩
  let b₂B : ↥B := ⟨b₂, hb₂B⟩
  let b₃B : ↥B := ⟨b₃, hb₃B⟩
  let B₀ : Subgroup ↥B := Subgroup.zpowers bB ⊔ Subgroup.zpowers b₁B
  let B₁₂ : Subgroup ↥B := Subgroup.zpowers b₂B ⊔ Subgroup.zpowers b₃B
  let σ : MulAut ↥B := τX * tX
  haveI : IsElementaryAbelian 3 ↥B := hE4.1
  have hpow3 : ∀ x : ↥B, x ^ 3 = 1 := fun x =>
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 ↥B)) x
  have hmap₀ : B₀.map B.subtype = Subgroup.zpowers b ⊔ Subgroup.zpowers b₁ := by
    change (Subgroup.zpowers bB ⊔ Subgroup.zpowers b₁B).map B.subtype =
      Subgroup.zpowers b ⊔ Subgroup.zpowers b₁
    simp only [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have hmap₁₂ : B₁₂.map B.subtype = Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃ := by
    change (Subgroup.zpowers b₂B ⊔ Subgroup.zpowers b₃B).map B.subtype =
      Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃
    simp only [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have htop : (⊤ : Subgroup ↥B) = B₀ ⊔ B₁₂ := by
    apply (Subgroup.map_subtype_inj (H := B)).mp
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup, hmap₀, hmap₁₂]
    exact hB
  have hx_decomp : ∀ x : ↥B, ∃ u ∈ B₀, ∃ v ∈ B₁₂, u * v = x := by
    intro x
    have hx : x ∈ B₀ ⊔ B₁₂ := by
      rw [← htop]
      exact Subgroup.mem_top x
    exact Subgroup.mem_sup.mp hx
  have hσ_mul : ∀ x : ↥B, σ x = τX (tX x) := fun x => by
    change (τX * tX) x = τX (tX x)
    rw [MulAut.mul_apply]
  have hσb : σ bB = bB := by
    rw [hσ_mul, htXb, hτXb]
  have hσ₁ : σ b₁B = b₁B := by
    rw [hσ_mul, htX₁, map_inv, hτX₁, inv_inv]
  have hσ₂ : σ b₂B = b₂B⁻¹ := by
    rw [hσ_mul, htX₂, hτX₂]
  have hσ₃ : σ b₃B = b₃B⁻¹ := by
    rw [hσ_mul, htX₃, hτX₃]
  have hfix_zp : ∀ (g : ↥B), σ g = g → ∀ a ∈ Subgroup.zpowers g, σ a = a := by
    intro g hg a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk, map_zpow, hg]
  have hinv_zp : ∀ (g : ↥B), σ g = g⁻¹ → ∀ a ∈ Subgroup.zpowers g, σ a = a⁻¹ := by
    intro g hg a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk, map_zpow, hg, inv_zpow]
  have hfix_B₀ : ∀ u ∈ B₀, σ u = u := by
    intro u hu
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, hfix_zp bB hσb a ha, hfix_zp b₁B hσ₁ c hc]
  have hinv_B₁₂ : ∀ v ∈ B₁₂, σ v = v⁻¹ := by
    intro v hv
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul, hinv_zp b₂B hσ₂ a ha, hinv_zp b₃B hσ₃ c hc, mul_inv_rev]
    exact mul_comm' _ _
  have hiff : ∀ x : ↥B, σ x = x ↔ x ∈ B₀ := by
    intro x
    constructor
    · intro hx
      obtain ⟨u, hu, v, hv, rfl⟩ := hx_decomp x
      have hσuv : σ (u * v) = u * v⁻¹ := by
        rw [map_mul, hfix_B₀ u hu, hinv_B₁₂ v hv]
      rw [hσuv] at hx
      have hvv : v⁻¹ = v := mul_left_cancel hx
      have hv2 : v * v = 1 := by
        calc v * v = v⁻¹ * v := by rw [hvv]
          _ = 1 := inv_mul_cancel v
      have hv1 : v = 1 := by
        calc v = v * v ^ 2 := by rw [pow_two, hv2, mul_one]
          _ = v ^ 3 := by
              rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one]
          _ = 1 := hpow3 v
      rw [hv1, mul_one]
      exact hu
    · intro hx
      exact hfix_B₀ x hx
  intro x
  exact hiff x

theorem FF81Hyp.commutator_t1
    {B : Subgroup G} {b b₁ b₂ b₃ : G}
    (hB : B = (Subgroup.zpowers b ⊔ (Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃)) ⊔
      Subgroup.zpowers b₁)
    (hE4 : IsElemAb 3 4 B)
    (hbB : b ∈ B) (hb₁B : b₁ ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B)
    {tX : MulAut ↥B}
    (htXb : tX ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (htX₁ : tX ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹)
    (htX₂ : tX ⟨b₂, hb₂B⟩ = ⟨b₂, hb₂B⟩)
    (htX₃ : tX ⟨b₃, hb₃B⟩ = ⟨b₃, hb₃B⟩) :
    (∀ x : ↥B, x⁻¹ * tX x ∈ Subgroup.zpowers (⟨b₁, hb₁B⟩ : ↥B)) ∧
    (∀ y ∈ Subgroup.zpowers (⟨b₁, hb₁B⟩ : ↥B), ∃ x : ↥B, x⁻¹ * tX x = y) := by
  let bB : ↥B := ⟨b, hbB⟩
  let b₁B : ↥B := ⟨b₁, hb₁B⟩
  let b₂B : ↥B := ⟨b₂, hb₂B⟩
  let b₃B : ↥B := ⟨b₃, hb₃B⟩
  let B₀ : Subgroup ↥B :=
    Subgroup.zpowers bB ⊔ (Subgroup.zpowers b₂B ⊔ Subgroup.zpowers b₃B)
  let B₁ : Subgroup ↥B := Subgroup.zpowers b₁B
  haveI : IsElementaryAbelian 3 ↥B := hE4.1
  have hpow3 : ∀ x : ↥B, x ^ 3 = 1 := fun x =>
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 ↥B)) x
  have hmap₀ : B₀.map B.subtype =
      Subgroup.zpowers b ⊔ (Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃) := by
    change (Subgroup.zpowers bB ⊔
      (Subgroup.zpowers b₂B ⊔ Subgroup.zpowers b₃B)).map B.subtype =
      Subgroup.zpowers b ⊔ (Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃)
    simp only [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have hmap₁ : B₁.map B.subtype = Subgroup.zpowers b₁ := by
    change (Subgroup.zpowers b₁B).map B.subtype = Subgroup.zpowers b₁
    simp only [MonoidHom.map_zpowers]
    rfl
  have htop : (⊤ : Subgroup ↥B) = B₀ ⊔ B₁ := by
    apply (Subgroup.map_subtype_inj (H := B)).mp
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup, hmap₀, hmap₁]
    exact hB
  have hx_decomp : ∀ x : ↥B, ∃ u ∈ B₀, ∃ v ∈ B₁, u * v = x := by
    intro x
    have hx : x ∈ B₀ ⊔ B₁ := by
      rw [← htop]
      exact Subgroup.mem_top x
    exact Subgroup.mem_sup.mp hx
  have hfix_zp : ∀ (g : ↥B), tX g = g → ∀ a ∈ Subgroup.zpowers g, tX a = a := by
    intro g hg a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk, map_zpow, hg]
  have hinv_zp : ∀ (g : ↥B), tX g = g⁻¹ → ∀ a ∈ Subgroup.zpowers g, tX a = a⁻¹ := by
    intro g hg a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk, map_zpow, hg, inv_zpow]
  have hfix_B₀ : ∀ u ∈ B₀, tX u = u := by
    intro u hu
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    obtain ⟨d, hd, e, he, rfl⟩ := Subgroup.mem_sup.mp hc
    rw [map_mul, map_mul, hfix_zp bB htXb a ha, hfix_zp b₂B htX₂ d hd,
      hfix_zp b₃B htX₃ e he]
  have hinv_B₁ : ∀ v ∈ B₁, tX v = v⁻¹ := by
    intro v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← hk, map_zpow, htX₁, inv_zpow]
  constructor
  · intro x
    obtain ⟨u, hu, v, hv, rfl⟩ := hx_decomp x
    have hval : (u * v)⁻¹ * tX (u * v) = v⁻¹ * v⁻¹ := by
      rw [map_mul, hfix_B₀ u hu, hinv_B₁ v hv, mul_inv_rev]
      group
    rw [hval]
    exact B₁.mul_mem (B₁.inv_mem hv) (B₁.inv_mem hv)
  · intro y hy
    refine ⟨y, ?_⟩
    have hy_inv : y⁻¹ = y ^ 2 := by
      calc y⁻¹ = y⁻¹ * 1 := (mul_one _).symm
        _ = y⁻¹ * y ^ 3 := by rw [hpow3 y]
        _ = y ^ 2 := by group
    have hy4 : y ^ 4 = y := by
      calc y ^ 4 = y ^ 3 * y := by
            rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
        _ = y := by rw [hpow3 y, one_mul]
    have hsq : y⁻¹ * y⁻¹ = y := by
      calc y⁻¹ * y⁻¹ = y ^ 2 * y ^ 2 := by rw [hy_inv]
        _ = y ^ 4 := (pow_add y 2 2).symm
        _ = y := hy4
    rw [hinv_B₁ y hy, hsq]

end CFSG.RankThree.PartTwo.Sec21.FF81

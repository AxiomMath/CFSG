module

public import CFSG.Quasithin.Vol2.Ch3E213MOS6
public import CFSG.Quasithin.Vol2.Ch3E213MOS5

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS

theorem dihedral_eight_conj : ∀ s : DihedralGroup 8, s * s = 1 → s ≠ 1 →
    s ≠ DihedralGroup.r 4 →
    DihedralGroup.r 1 * s * (DihedralGroup.r 1)⁻¹ ≠ s ∧
      DihedralGroup.r 1 * s * (DihedralGroup.r 1)⁻¹ ≠ DihedralGroup.r 4 * s := by
  decide

theorem false_of_conj_mem {X : Type*} [Group X] {Pt : Subgroup X} {x z : X}
    (φ : ↥Pt ≃* DihedralGroup 8) (hxPt : x ∈ Pt) (hzPt : z ∈ Pt) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxz : x ≠ z) (hz1 : z ≠ 1) (hzc : ∀ g ∈ Pt, g * z = z * g)
    (hall : ∀ g ∈ Pt, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = z * x) : False := by
  have hzZ : φ ⟨z, hzPt⟩ ∈ Subgroup.center (DihedralGroup 8) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc _ g'.2)
  have hz4 : φ ⟨z, hzPt⟩ = DihedralGroup.r 4 := by
    rcases (Dih.mem_center_iff' (k := 8) (by decide) (by norm_num)).mp hzZ with h | h
    · exfalso
      apply hz1
      have : (⟨z, hzPt⟩ : ↥Pt) = 1 := φ.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
    · rw [h]
      rfl
  set s := φ ⟨x, hxPt⟩ with hs
  have hs2 : s * s = 1 := by
    rw [hs, ← map_mul]
    have : (⟨x, hxPt⟩ : ↥Pt) * ⟨x, hxPt⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hs1 : s ≠ 1 := by
    intro h
    apply hx1
    have : (⟨x, hxPt⟩ : ↥Pt) = 1 := φ.injective (by rw [← hs, h, map_one])
    exact congrArg Subtype.val this
  have hs4 : s ≠ DihedralGroup.r 4 := by
    intro h
    apply hxz
    have : (⟨x, hxPt⟩ : ↥Pt) = ⟨z, hzPt⟩ := φ.injective (by rw [← hs, h, hz4])
    exact congrArg Subtype.val this
  obtain ⟨h1, h2⟩ := dihedral_eight_conj s hs2 hs1 hs4
  set g : ↥Pt := φ.symm (DihedralGroup.r 1) with hg
  rcases hall (g : X) g.2 with h | h
  · apply h1
    have : g * ⟨x, hxPt⟩ * g⁻¹ = ⟨x, hxPt⟩ := Subtype.ext h
    have := congrArg φ this
    rwa [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply] at this
  · apply h2
    have : g * ⟨x, hxPt⟩ * g⁻¹ = ⟨z, hzPt⟩ * ⟨x, hxPt⟩ := Subtype.ext h
    have := congrArg φ this
    rwa [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply, map_mul, hz4] at this

variable {K : Type} [Group K] [Finite K]

theorem false_of_central (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {P T₀ M₀ : Subgroup (MulAut K)} {C : Subgroup K}
    (uniq : ∀ Y : Subgroup (MulAut K), Y ≤ innAut K → P ≤ Y → Y ≠ innAut K →
      T₀ ≤ Subgroup.normalizer (Y : Set (MulAut K)) → Y ≤ M₀)
    (hD : M₀ ⊓ innAut K = C.map MulAut.conj) (hPinn : P ≤ innAut K) {f₀ : MulAut K}
    (hf₀1 : f₀ ≠ 1) (hcent : ∀ g ∈ T₀, g * f₀ = f₀ * g) (hPf : ∀ x ∈ P, x * f₀ = f₀ * x)
    (hcard : Nat.card C < Nat.card (fixedSubgroup K f₀)) : False := by
  set Y : Subgroup (MulAut K) := (fixedSubgroup K f₀).map MulAut.conj with hY
  have hYinn : Y ≤ innAut K := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hPY : P ≤ Y := by
    intro x hx
    obtain ⟨y, rfl⟩ := hPinn hx
    refine ⟨y, ?_, rfl⟩
    exact (conj_mem_centralizer_iff hinj f₀ y).mp
      (Subgroup.mem_centralizer_singleton_iff.mpr (hPf _ hx))
  have hYne : Y ≠ innAut K := by
    intro h
    apply hf₀1
    ext y
    obtain ⟨y', hy', hyy'⟩ := (h ▸ (⟨y, rfl⟩ : MulAut.conj y ∈ innAut K) : MulAut.conj y ∈ Y)
    have : y' = y := hinj hyy'
    rw [← this]
    exact hy'
  have hconj : ∀ g : MulAut K, g * f₀ = f₀ * g → ∀ h ∈ Y, g * h * g⁻¹ ∈ Y := by
    rintro g hg _ ⟨y, hy, rfl⟩
    refine ⟨g y, ?_, (mul_conj_mul_inv g y).symm⟩
    have hy' : f₀ y = y := hy
    show f₀ (g y) = g y
    rw [← MulAut.mul_apply, ← hg, MulAut.mul_apply, hy']
  have hTY : T₀ ≤ Subgroup.normalizer (Y : Set (MulAut K)) := by
    intro g hgT
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hg := hcent g hgT
    have hg' : g⁻¹ * f₀ = f₀ * g⁻¹ := by
      calc g⁻¹ * f₀ = g⁻¹ * (f₀ * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * f₀) * g⁻¹ := by rw [hg]
        _ = f₀ * g⁻¹ := by group
    constructor
    · exact hconj g hg h
    · intro hh
      have := hconj g⁻¹ hg' _ hh
      simpa [mul_assoc] using this
  have hle := uniq Y hYinn hPY hYne hTY
  have hle' : Y ≤ C.map MulAut.conj := hD ▸ le_inf hle hYinn
  rw [hY, Subgroup.map_le_map_iff_of_injective hinj] at hle'
  exact absurd (Subgroup.card_le_of_le hle') (not_le.mpr hcard)

theorem false_of_fixes (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {M₀ : Subgroup (MulAut K)} {z₀ : K}
    (hcoat : IsCoatom (Subgroup.centralizer ({z₀} : Set K)))
    {k b m : ℕ} (ψ : ↥(Subgroup.centralizer ({z₀} : Set K)) ≃* DihedralGroup k)
    (hD : M₀ ⊓ innAut K = (Subgroup.centralizer ({z₀} : Set K)).map MulAut.conj)
    (hk : k = 2 ^ b * m) (hm2 : 2 ≤ m) (hmodd : Odd m) {S : Subgroup K}
    (hSC : S ≤ Subgroup.centralizer ({z₀} : Set K)) (hSodd : Odd S.index) {u : MulAut K}
    (hu : u ∈ pCoreOf 2 M₀) (hu1 : u ≠ 1) (hS : ∀ x ∈ S, u x = x) {p : ℕ} (hp1 : 1 < p)
    (hcard : Nat.card (fixedSubgroup K u) = p * Nat.card (Subgroup.centralizer ({z₀} : Set K))) :
    False := by
  obtain ⟨c, hcC, hcm⟩ := exists_orderOf_eq ψ hk hm2
  have hc : u c = c := fix_of_odd hinj ψ hD hu hcC (hcm ▸ hmodd)
  have hCcard : Nat.card (Subgroup.centralizer ({z₀} : Set K)) = 2 ^ (b + 1) * m := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card, hk, pow_succ]
    ring
  have hle := le_fixed hSC hSodd hcC hcm hCcard (by omega) hS hc
  rw [eq_of_le_fixed hcoat hu1 hle] at hcard
  have hpos : 0 < Nat.card (Subgroup.centralizer ({z₀} : Set K)) := Nat.card_pos
  have h1 : 1 * Nat.card (Subgroup.centralizer ({z₀} : Set K)) =
      p * Nat.card (Subgroup.centralizer ({z₀} : Set K)) := by rw [one_mul]; exact hcard
  have := Nat.eq_of_mul_eq_mul_right hpos h1
  omega

end CFSG.Quasithin.Ch3E213M.OS

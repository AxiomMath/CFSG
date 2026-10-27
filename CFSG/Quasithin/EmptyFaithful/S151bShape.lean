module

public import CFSG.Quasithin.EmptyFaithful.S152NWreath
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Small

variable {W : Type*} [CommGroup W] [Finite W]

theorem card_le_two_of_not_four_dvd151b {E X : Subgroup (MulAut W)} (hE : IsElemAbelian2 E)
    (hEX : E ≤ X) (h4 : ¬ 4 ∣ Nat.card X) : Nat.card E ≤ 2 := by
  have hcard : Nat.card E = 2 ^ rk E := B1.card_elemAbelian hE
  have hdvd : Nat.card E ∣ Nat.card X := Subgroup.card_dvd_of_le hEX
  by_contra hgt
  push Not at hgt
  have hrk : 2 ≤ rk E := by
    by_contra hlt
    push Not at hlt
    have : rk E ≤ 1 := by omega
    have : 2 ^ rk E ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h4E : 4 ∣ Nat.card E := by
    rw [hcard]
    have : 2 ^ 2 ∣ 2 ^ rk E := pow_dvd_pow 2 hrk
    simpa using this
  exact h4 (h4E.trans hdvd)

theorem card_le_two_of_le_cyclic151b {E Tb : Subgroup (MulAut W)} (hE : IsElemAbelian2 E)
    (hET : E ≤ Tb) {n : ℕ} (hn : n = 2 ∨ n = 4) (f : ↥Tb ≃* Multiplicative (ZMod n)) :
    Nat.card E ≤ 2 := by
  have hdvd : Nat.card E ∣ Nat.card Tb := Subgroup.card_dvd_of_le hET
  rcases hn with rfl | rfl
  · have hT : Nat.card Tb = 2 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card]
      rfl
    exact (Nat.le_of_dvd (by norm_num) (hT ▸ hdvd))
  · have hT : Nat.card Tb = 4 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card]
      rfl
    by_contra hgt
    push Not at hgt
    have hle : Nat.card E ≤ 4 := Nat.le_of_dvd (by norm_num) (hT ▸ hdvd)
    have hE4 : Nat.card E = 4 := by
      have hcard : Nat.card E = 2 ^ rk E := B1.card_elemAbelian hE
      have hrk : rk E ≤ 2 := by
        by_contra h
        have : 2 ^ 3 ≤ 2 ^ rk E := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain h0 | h1 | h2 : rk E = 0 ∨ rk E = 1 ∨ rk E = 2 := by omega
      · rw [h0] at hcard; omega
      · rw [h1] at hcard; omega
      · rw [h2] at hcard; omega
    have hEeq : E = Tb := Subgroup.eq_of_le_of_card_ge hET (by omega)
    have hgE : ((f.symm (Multiplicative.ofAdd (1 : ZMod 4)) : ↥Tb) : MulAut W) ∈ E := by
      rw [hEeq]; exact (f.symm (Multiplicative.ofAdd (1 : ZMod 4))).2
    have hsq := hE.2 _ hgE
    have hsq' : (f.symm (Multiplicative.ofAdd (1 : ZMod 4))) ^ 2 = 1 := Subtype.ext hsq
    have h1 : f ((f.symm (Multiplicative.ofAdd (1 : ZMod 4))) ^ 2) = f 1 := congrArg f hsq'
    rw [map_pow, MulEquiv.apply_symm_apply, map_one f] at h1
    revert h1
    decide

end Small

namespace S152N

noncomputable local instance instFintypeW3151b : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3151b : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

theorem P0_nonabelian151b : ∃ a b : W3, a ∈ W3.P0 ∧ b ∈ W3.P0 ∧ a * b ≠ b * a := by
  have : ∃ a b : W3, (∀ q, a.left q = 1 ∨ a.left q = W3.s01) ∧
      (∀ q, b.left q = 1 ∨ b.left q = W3.s01) ∧ a * b ≠ b * a := by
    decide +kernel
  obtain ⟨a, b, ha, hb, hab⟩ := this
  exact ⟨a, b, ha, hb, hab⟩

theorem card_le_four_of_elemAbelian_W3 {F : Subgroup W3} (hc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (h2 : ∀ a ∈ F, a ^ 2 = 1) : Nat.card F ≤ 4 := by
  by_contra hgt
  push Not at hgt
  have hp : IsPGroup 2 F := fun x => ⟨1, Subtype.ext (by simpa using h2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card F ∣ 72 := W3.card_eq ▸ Subgroup.card_subgroup_dvd_card F
  have hF8 : Nat.card F = 8 := by
    have hk3 : k ≤ 3 := by
      by_contra h
      have h1 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      rw [← hk] at h1
      have := h1.trans hdvd
      omega
    obtain h0 | h1 | h2 | h3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · rw [h0] at hk; omega
    · rw [h1] at hk; omega
    · rw [h2] at hk; omega
    · rw [h3] at hk; omega
  have hFsyl : IsSylowTwoOf F ⊤ := by
    refine ⟨le_top, hp, ?_⟩
    have h1 : (F.subgroupOf ⊤).index = F.index := Subgroup.relIndex_top_right (H := F)
    have h2' := F.index_mul_card
    rw [hF8, W3.card_eq] at h2'
    rw [h1]
    omega
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf W3.P0_isSylowTwoOf hFsyl
  obtain ⟨a, b, ha, hb, hab⟩ := P0_nonabelian151b
  apply hab
  have ha' : g * a * g⁻¹ ∈ F := by
    have := (hg (g * a * g⁻¹)).mpr (by simpa [mul_assoc] using ha)
    exact this
  have hb' : g * b * g⁻¹ ∈ F := by
    have := (hg (g * b * g⁻¹)).mpr (by simpa [mul_assoc] using hb)
    exact this
  have hcomm := hc _ ha' _ hb'
  have : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := hcomm
      _ = g * (b * a) * g⁻¹ := by group
  simpa using this

end S152N

end CFSG.Quasithin

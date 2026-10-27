module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Y1Quot
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Fix

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem mem_blockQ_iff_pCore {L : Subgroup G} (l : ↥L) :
    (l : G) ∈ blockQ L ↔ l ∈ CFSG.pCore 2 ↥L := by
  have h : blockQ L = (CFSG.pCore 2 ↥L).map L.subtype := by
    unfold blockQ pCoreOf
    try with_reducible rfl
  rw [h]
  exact Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective


open Matrix in
theorem eq_zero_of_mulVec_eq_of_pow_three {F : Type*} [Field F] [CharP F 2]
    (M : Matrix.SpecialLinearGroup (Fin 2) F) (h3 : M ^ 3 = 1) (h1 : M ≠ 1) (v : Fin 2 → F)
    (hv : (M : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : v = 0 := by
  by_contra hv0
  have h20 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.det_coe
  rw [Matrix.det_fin_two] at hdet
  have e0 := congrFun hv 0
  have e1 := congrFun hv 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  set a := (M : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (M : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (M : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (M : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hD : ((a - 1) * (d - 1) - b * c) * v 0 = 0 ∧ ((a - 1) * (d - 1) - b * c) * v 1 = 0 := by
    constructor
    · linear_combination (d - 1) * e0 - b * e1
    · linear_combination (a - 1) * e1 - c * e0
  have hD0 : (a - 1) * (d - 1) - b * c = 0 := by
    by_contra hne
    apply hv0
    ext i
    fin_cases i
    · exact (mul_eq_zero.mp hD.1).resolve_left hne
    · exact (mul_eq_zero.mp hD.2).resolve_left hne
  have hsum : a + d = 0 := by linear_combination hdet - hD0 + h20
  have h2 : M ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc, ← hd]
    · linear_combination a * hsum - hdet - h20
    · linear_combination b * hsum
    · linear_combination c * hsum
    · linear_combination d * hsum - hdet - h20
  apply h1
  calc M = M ^ 3 * (M ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp



theorem mem_blockZ_of_fixed [Finite G] {L : Subgroup G} (hL : IsShort2 L)
    (htype : IsAltType L 3 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)
    {k u : G} (hk : k ∈ L) (hk3 : k ^ 3 = 1) (hkQ : k ∉ blockQ L)
    (hu : u ∈ blockU L) (hfix : k * u * k⁻¹ = u) : u ∈ blockZ L := by
  have hk' : (⟨k, hk⟩ : ↥L) ∉ CFSG.pCore 2 ↥L := fun h => hkQ ((mem_blockQ_iff_pCore ⟨k, hk⟩).mpr h)
  rcases htype with ⟨α, hαs, hαk, -⟩ | ⟨n, hn, F, hFf, hFfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩
  ·
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hα1 : α ⟨k, hk⟩ ≠ 1 := fun h => hk' (hαk ▸ h)
    have hcard3 : Nat.card (alternatingGroup (Fin 3)) = 3 := S15221.card_alternatingGroup_three
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨i, hi⟩ : α ⟨l, hl⟩ ∈ Subgroup.zpowers (α ⟨k, hk⟩) :=
      mem_zpowers_of_prime_card hcard3 hα1
    have hq : (⟨l, hl⟩ : ↥L) * ⟨k, hk⟩ ^ (-i) ∈ CFSG.pCore 2 ↥L := by
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_zpow, zpow_neg, ← hi]
      simp
    have hqQ : l * k ^ (-i) ∈ blockQ L := (mem_blockQ_iff_pCore _).mpr hq
    have hc1 := C1.blockU_comm hL u hu _ hqQ
    have hc2 : ∀ j : ℤ, u * k ^ j = k ^ j * u := by
      intro j
      have : k * u = u * k := by
        have := hfix
        calc k * u = (k * u * k⁻¹) * k := by group
          _ = u * k := by rw [hfix]
      have hcomm : Commute u k := this.symm
      exact (hcomm.zpow_right j).eq
    have : l = (l * k ^ (-i)) * k ^ i := by
      rw [mul_assoc, ← zpow_add]; simp
    calc l * u = (l * k ^ (-i)) * k ^ i * u := by rw [← this]
      _ = (l * k ^ (-i)) * (k ^ i * u) := by group
      _ = (l * k ^ (-i)) * (u * k ^ i) := by rw [← hc2 i]
      _ = ((l * k ^ (-i)) * u) * k ^ i := by group
      _ = (u * (l * k ^ (-i))) * k ^ i := by rw [← hc1]
      _ = u * ((l * k ^ (-i)) * k ^ i) := by group
      _ = u * l := by rw [← this]
  ·
    have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
    have : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hn.le hq
    have hα1 : α ⟨k, hk⟩ ≠ 1 := fun h => hk' (hαk ▸ h)
    have hα3 : (α ⟨k, hk⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨k, hk⟩ : ↥L) ^ 3 = 1 := Subtype.ext hk3
      rw [this, map_one]
    have hβu := hβe ⟨k, hk⟩ ⟨u, hu⟩ ⟨u, hu⟩ hfix.symm
    have hv0 := eq_zero_of_mulVec_eq_of_pow_three (α ⟨k, hk⟩) hα3 hα1
      (Multiplicative.toAdd (β ⟨u, hu⟩)) hβu.symm
    have hβ1 : β ⟨u, hu⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hv0
    have : (⟨u, hu⟩ : ↥(blockU L)) ∈ β.ker := hβ1
    rw [hβk] at this
    exact this



theorem centralizes_of_fixed [Finite G] {X U₂ : Subgroup G} (hX : IsShort2 X)
    (htype : IsAltType X 3 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type X n)
    {z : G} (hz2 : z ^ 2 = 1) (hzN : z ∈ Subgroup.normalizer (X : Set G))
    (hzQ : ∀ l ∈ X, z * l * z⁻¹ * l⁻¹ ∈ blockQ X)
    (hU₂z : ∀ u ∈ U₂, u * z = z * u) (hodd : ¬ 2 ∣ (U₂.subgroupOf X).index)
    {k : G} (hk : k ∈ X) (hk3 : k ^ 3 = 1) (hkQ : k ∉ blockQ X) (hkz : k * z = z * k) :
    ∀ x ∈ X, x * z = z * x := by
  have hzinv : z⁻¹ = z := by
    have : z * z = 1 := by rw [← pow_two]; exact hz2
    exact inv_eq_of_mul_eq_one_right this
  have hzU : ∀ u ∈ blockU X, u * z = z * u :=
    C1.commute_blockU_of_mem hX hzN ⟨1, by simpa using hz2⟩ hzQ
  have hUab := (C1.elemAb2_blockU hX).1
  have hc : ∀ x ∈ X, z⁻¹ * (x * z * x⁻¹) ∈ blockU X := by
    intro x hx
    have := C1.commutator_mem_blockU_of_mem_blockQ hX hzQ x hx
    rw [hzinv]
    have e : z * (x * z * x⁻¹) = z * x * z⁻¹ * x⁻¹ := by rw [hzinv]; group
    rw [e]
    exact this
  obtain ⟨b, hbU, hb⟩ := exists_fixed_mul_of_odd (X := X) (A := blockU X) (U := U₂) hz2 hUab hzU
    (C1.le_normalizer_blockU X) hU₂z hodd hc
  have hkb : k * b * k⁻¹ = b := by
    have h1 := hb k hk
    have h2 : k * (z * b) * k⁻¹ = z * (k * b * k⁻¹) := by
      calc k * (z * b) * k⁻¹ = (k * z) * b * k⁻¹ := by group
        _ = (z * k) * b * k⁻¹ := by rw [hkz]
        _ = z * (k * b * k⁻¹) := by group
    rw [h2] at h1
    exact mul_left_cancel h1
  have hbZ : b ∈ blockZ X := mem_blockZ_of_fixed hX htype hk hk3 hkQ hbU hkb
  intro x hx
  have h1 := hb x hx
  have hbx : x * b * x⁻¹ = b := by
    have := Subgroup.mem_centralizer_iff.mp hbZ.2 x hx
    calc x * b * x⁻¹ = (x * b) * x⁻¹ := rfl
      _ = (b * x) * x⁻¹ := by rw [this]
      _ = b := by group
  have h2 : x * (z * b) * x⁻¹ = (x * z * x⁻¹) * (x * b * x⁻¹) := by group
  rw [h2, hbx] at h1
  have h3 := mul_right_cancel h1
  calc x * z = (x * z * x⁻¹) * x := by group
    _ = z * x := by rw [h3]


end CFSG.Quasithin.S15223

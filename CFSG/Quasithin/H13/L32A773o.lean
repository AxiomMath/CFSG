module

public import CFSG.Quasithin.H13.L32A773n

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsL24Section.eq_or_eq {K X Y : Subgroup G} (h : IsL24Section K X Y) {D : Subgroup G}
    (hYD : Y ≤ D) (hDX : D ≤ X) (hDK : K ≤ Subgroup.normalizer (D : Set G)) : D = Y ∨ D = X := by
  obtain ⟨hKX, π, β, hπs, -, -, hβk, hβe⟩ := h
  have hβ1 : ∀ x : ↥X, β x = 1 ↔ (x : G) ∈ Y := fun x => by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  by_cases hDY : D ≤ Y
  · exact Or.inl (le_antisymm hDY hYD)
  right
  obtain ⟨w, hwD, hwY⟩ := Set.not_subset.mp hDY
  have hwX := hDX hwD
  have hβw : Multiplicative.toAdd (β ⟨w, hwX⟩) ≠ 0 := fun h0 => hwY ((hβ1 _).mp (by
    rw [← ofAdd_toAdd (β ⟨w, hwX⟩), h0]; rfl))
  refine le_antisymm hDX fun x hx => ?_
  by_cases hβx : Multiplicative.toAdd (β ⟨x, hx⟩) = 0
  · exact hYD ((hβ1 _).mp (by rw [← ofAdd_toAdd (β ⟨x, hx⟩), hβx]; rfl))
  obtain ⟨A, hA⟩ := sl24_transitive _ _ hβw hβx
  obtain ⟨k, rfl⟩ := hπs A
  have hkw : (k : G) * w * (k : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hKX k.2) w).mp hwX
  have h1 := hβe k ⟨w, hwX⟩ ⟨_, hkw⟩ rfl
  rw [hA, ofAdd_toAdd] at h1
  have h2 : β (⟨x, hx⟩ * (⟨_, hkw⟩ : ↥X)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1]
    exact mul_inv_cancel _
  have h3 := (hβ1 _).mp h2
  have hkwD : (k : G) * w * (k : G)⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hDK k.2) w).mp hwD
  have h3' : x * ((k : G) * w * (k : G)⁻¹)⁻¹ ∈ Y := by simpa using h3
  rw [show x = (x * ((k : G) * w * (k : G)⁻¹)⁻¹) * ((k : G) * w * (k : G)⁻¹) by group]
  exact mul_mem (hYD h3') hkwD

omit [Finite G] in
theorem le_normalizer_sup_of {K A B : Subgroup G} (hA : K ≤ Subgroup.normalizer (A : Set G))
    (hB : K ≤ Subgroup.normalizer (B : Set G)) :
    K ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := fun g hg => by
  rw [← conjSub_eq_self_iff, conjSub, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (conjSub_eq_self_iff.mpr (hA hg)) (conjSub_eq_self_iff.mpr (hB hg))

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

variable {k : G} (hk : k ∈ kz T V) (hkM : k ∉ m1 T L V)
include hk hkM

theorem inf_le_of_comm {Y : Subgroup G} (hUY : fsuU T V ≤ Y)
    (hcomm : ∀ b ∈ (sL T L V).map (MulAut.conj k).toMonoidHom ⊓ pCoreOf 2 (kz T V),
      ∀ s ∈ sL T L V, b * s * b⁻¹ * s⁻¹ ∈ Y) :
    sL T L V ⊓ pCoreOf 2 (kz T V) ≤ Y := by
  obtain ⟨θ, χ, hθs, hθk, hθLl, hχk, hχt, hχs, hχe, -, hχW⟩ := C.exists_theta_chi
  have hO := C.pCoreOf_hz_eq
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hQT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le C.hyp hTH
  set B := (sL T L V).map (MulAut.conj k).toMonoidHom ⊓ pCoreOf 2 (kz T V) with hB
  have hBQ : B ≤ pCoreOf 2 (hz T V) := by rw [hO]; exact inf_le_right
  have hB4 : (sL T L V).relIndex B = 4 := by
    have hB9 : Nat.card ↥B = 2 ^ 9 := by
      rw [hB, conj_inf_kz hk, conjSub, Subgroup.card_map_of_injective (MulAut.conj k).injective,
        C.card_sL_inf_kz]
    have hSB : sL T L V ⊓ B = sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom := by
      rw [hB, ← inf_assoc, inf_eq_left.mpr]
      rw [C.sL_inf_conj_eq hk hkM]
      exact inf_le_left
    have h1 := Subgroup.relIndex_mul_card (sL T L V) B
    rw [hSB, C.sL_inf_conj_eq hk hkM, ← hO, C.card_CU, hB9] at h1
    omega
  obtain ⟨⟨b₁, hb₁, hθb₁⟩, ⟨b₂, hb₂, hθb₂⟩⟩ := C.theta_mem_u hθs hθk hθLl hBQ hB4
  have hχ1 : ∀ s : ↥(sL T L V), χ s = 1 ↔ (s : G) ∈ V := fun s => by
    rw [← MonoidHom.mem_ker, hχk, Subgroup.mem_subgroupOf]
  intro a ha
  obtain ⟨haS, haO⟩ := Subgroup.mem_inf.mp ha
  have haW := hχW ⟨a, haS⟩ (by rw [hO]; exact haO)
  obtain ⟨hB₁, hB₂, hdec⟩ := st_W_decomp _ (hχt _) haW
  obtain ⟨s₁, hs₁⟩ := hχs _ hB₁
  obtain ⟨s₂, hs₂⟩ := hχs _ hB₂
  have hw : ∀ (q : ↥L), (q : G) ∈ B → ∀ s : ↥(sL T L V),
      (q : G) * s * (q : G)⁻¹ * (s : G)⁻¹ ∈ sL T L V := fun q hq s =>
    mul_mem ((Subgroup.mem_normalizer_iff.mp (C.T_le_normalizer_sL (hQT (hBQ hq))) s).mp s.2)
      (inv_mem s.2)
  have h1 := chi_comm hχe b₁ s₁ (hw b₁ hb₁ s₁)
  have h2 := chi_comm hχe b₂ s₂ (hw b₂ hb₂ s₂)
  have hχa : χ ⟨a, haS⟩ = χ (⟨_, hw b₁ hb₁ s₁⟩ * ⟨_, hw b₂ hb₂ s₂⟩) := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, h1, h2, hθb₁, hθb₂, hs₁, hs₂, toAdd_ofAdd, toAdd_ofAdd]
    exact hdec
  have hv : ((⟨_, hw b₁ hb₁ s₁⟩ * ⟨_, hw b₂ hb₂ s₂⟩ : ↥(sL T L V))⁻¹ * ⟨a, haS⟩ :
      ↥(sL T L V)) ∈ χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hχa]
    exact inv_mul_cancel _
  rw [hχk, Subgroup.mem_subgroupOf] at hv
  have e : a = ((b₁ : G) * s₁ * (b₁ : G)⁻¹ * (s₁ : G)⁻¹) *
      ((b₂ : G) * s₂ * (b₂ : G)⁻¹ * (s₂ : G)⁻¹) *
      (((⟨_, hw b₁ hb₁ s₁⟩ * ⟨_, hw b₂ hb₂ s₂⟩ : ↥(sL T L V))⁻¹ * ⟨a, haS⟩ :
        ↥(sL T L V)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact mul_mem (mul_mem (hcomm _ hb₁ _ s₁.2) (hcomm _ hb₂ _ s₂.2)) (hUY (v_le_fsuU hv))

theorem isIndec_kz : IsIndecOnSection (kz T V) (pCoreOf 2 (kz T V)) (fsuU T V) := by
  have hO := C.pCoreOf_hz_eq
  have hL24 : IsL24Section (kz T V) (pCoreOf 2 (kz T V))
      (pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) := by
    rw [← hO]
    exact (C.l71 G T L V C.hyp).1.1
  have hCK : ⁅pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G), kz T V⁆ ≤
      fsuU T V := by
    rw [← hO]
    exact (C.l71 G T L V C.hyp).1.2
  set Cc := pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) with hCc
  have hKCc : kz T V ≤ Subgroup.normalizer (Cc : Set G) := by
    rw [hCc, ← hO]
    exact (oTwoUpper_le _).trans C.hz_le_normalizer_CU
  have hUCc : fsuU T V ≤ Cc := by
    rw [hCc, ← hO]
    exact C.fsuU_le_CU
  have hOK : pCoreOf 2 (kz T V) ≤ kz T V := pCoreOf_le 2 _
  have hCc7 : Nat.card ↥Cc = 2 ^ 7 := by rw [hCc, ← hO]; exact C.card_CU
  have hO11 : Nat.card ↥(pCoreOf 2 (kz T V)) = 2 ^ 11 := by rw [← hO]; exact C.card_QH
  have hU5 := C.card_fsuU
  have key : ∀ X Y : Subgroup G, fsuU T V ≤ X → fsuU T V ≤ Y → X ≤ pCoreOf 2 (kz T V) →
      Y ≤ pCoreOf 2 (kz T V) → kz T V ≤ Subgroup.normalizer (X : Set G) →
      kz T V ≤ Subgroup.normalizer (Y : Set G) → X ⊓ Y = fsuU T V →
      X ⊔ Y = pCoreOf 2 (kz T V) → X ≤ Cc → X = fsuU T V := by
    intro X Y hUX hUY hXO hYO hXK hYK hXY hXYs hXC
    have hOY : ∀ o ∈ pCoreOf 2 (kz T V), ∀ g ∈ kz T V, g * o * g⁻¹ * o⁻¹ ∈ Y := by
      intro o ho g hg
      have hXN : X ≤ Subgroup.normalizer (Y : Set G) := hXO.trans (hOK.trans hYK)
      have ho' : o ∈ ((X ⊔ Y : Subgroup G) : Set G) := by rw [hXYs]; exact ho
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXN] at ho'
      obtain ⟨x, hx, y, hy, rfl⟩ := ho'
      have hgx : g * x * g⁻¹ * x⁻¹ ∈ fsuU T V := by
        have h1 := hCK (Subgroup.commutator_mem_commutator (hXC hx) hg)
        rw [commutatorElement_def] at h1
        have h2 := inv_mem h1
        rwa [show (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ by group] at h2
      have hgy : g * y * g⁻¹ * y⁻¹ ∈ Y :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (hYK hg) y).mp hy) (inv_mem hy)
      rw [show g * (x * y) * g⁻¹ * (x * y)⁻¹ =
        (g * x * g⁻¹ * x⁻¹) * (x * (g * y * g⁻¹ * y⁻¹) * x⁻¹) by group]
      exact mul_mem (hUY hgx)
        ((Subgroup.mem_normalizer_iff.mp (hXN hx) _).mp hgy)
    have hSY : sL T L V ⊓ pCoreOf 2 (kz T V) ≤ Y := C.inf_le_of_comm hk hkM hUY fun b hb s hs => by
      have h1 := hOY b (Subgroup.mem_inf.mp hb).2 s (C.sL_le_kz hs)
      have h2 := inv_mem h1
      rwa [show (s * b * s⁻¹ * b⁻¹)⁻¹ = b * s * b⁻¹ * s⁻¹ by group] at h2
    have hCcS : Cc ≤ sL T L V ⊓ pCoreOf 2 (kz T V) := fun x hx => by
      have h : x ∈ sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom := by
        rw [C.sL_inf_conj_eq hk hkM]
        exact hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h).1, (Subgroup.mem_inf.mp hx).1⟩
    rw [← hXY]
    exact le_antisymm (le_inf le_rfl (hXC.trans (hCcS.trans hSY))) inf_le_left
  intro X Y hUX hUY hXO hYO hXK hYK hXY hXYs
  rcases hL24.eq_or_eq (D := X ⊔ Cc) le_sup_right (sup_le hXO inf_le_left)
    (le_normalizer_sup_of hXK hKCc) with hX | hX
  · exact Or.inl (key X Y hUX hUY hXO hYO hXK hYK hXY hXYs (hX ▸ le_sup_left))
  rcases hL24.eq_or_eq (D := Y ⊔ Cc) le_sup_right (sup_le hYO inf_le_left)
    (le_normalizer_sup_of hYK hKCc) with hY | hY
  · exact Or.inr (key Y X hUY hUX hYO hXO hYK hXK (by rw [inf_comm]; exact hXY)
      (by rw [sup_comm]; exact hXYs) (hY ▸ le_sup_left))
  exfalso
  have hbig : ∀ Z : Subgroup G, fsuU T V ≤ Z → Z ≤ pCoreOf 2 (kz T V) →
      Z ⊔ Cc = pCoreOf 2 (kz T V) →
      2 ^ 9 ≤ Nat.card ↥Z := by
    intro Z hUZ hZO hZC
    have hZN : Z ≤ Subgroup.normalizer (Cc : Set G) := hZO.trans (hOK.trans hKCc)
    have h1 := card_sup_mul_card_inf' hZN
    rw [hZC, hO11, hCc7] at h1
    have h2 : 2 ^ 5 ∣ Nat.card ↥(Z ⊓ Cc) := by
      rw [← hU5]
      exact Subgroup.card_dvd_of_le (le_inf hUZ hUCc)
    have h3 : 0 < Nat.card ↥(Z ⊓ Cc) := Nat.card_pos
    omega
  have hXb := hbig X hUX hXO hX
  have hYb := hbig Y hUY hYO hY
  have hXN : X ≤ Subgroup.normalizer (Y : Set G) := hXO.trans (hOK.trans hYK)
  have h1 := card_sup_mul_card_inf' hXN
  rw [hXYs, hXY, hO11, hU5] at h1
  have h2 : 2 ^ 9 * 2 ^ 9 ≤ Nat.card ↥X * Nat.card ↥Y := Nat.mul_le_mul hXb hYb
  rw [← h1] at h2
  norm_num at h2

end Ctx73

end CFSG.Quasithin.H13.L32A

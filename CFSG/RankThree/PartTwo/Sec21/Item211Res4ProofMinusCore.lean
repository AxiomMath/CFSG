module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusCore

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG
open CFSG.Assembly (IsElemAbelian)
open scoped MatrixGroups commutatorElement

namespace Item211Res4Proof

section Core

variable {M : Type} [Group M]

theorem centralizes_of_sl2_normal {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F)
    {H Q : Subgroup M} (κ : SL(2, F) →* M) (hκH : ∀ B, κ B ∈ H)
    (hκker : ∀ B, κ B = 1 → B = 1 ∨ B = -1) (hQ2 : IsPGroup 2 Q)
    (hQH : H ≤ Subgroup.normalizer (Q : Set M)) {q : M} (hq : q ∈ Q) (β : MulAut SL(2, F))
    (hβ : ∀ B, κ (β B) = q * κ B * q⁻¹) (B₀ : SL(2, F)) : q * κ B₀ = κ B₀ * q := by
  let N : Subgroup SL(2, F) := Q.comap κ
  have hNn : N.Normal := ⟨fun B hB a => by
    change κ (a * B * a⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hQH (hκH a)) _).mp hB⟩
  have hN2 : ∀ B ∈ N, ∃ e : ℕ, B ^ 2 ^ e = 1 := by
    intro B hB
    obtain ⟨e, he⟩ := exists_pow_two_pow_eq_one hQ2 hB
    refine ⟨e + 1, ?_⟩
    rcases hκker _ (by rw [map_pow, he]) with h | h
    · rw [pow_succ, pow_mul, h, one_pow]
    · rw [pow_succ, pow_mul, h]
      apply Subtype.ext
      simp [sq]
  have hcen := Item211Lie2Proof.le_center_of_normal_two hF4 N hN2
  have hmem : ∀ B, β B * B⁻¹ ∈ Subgroup.center SL(2, F) := by
    intro B
    apply hcen
    change κ (β B * B⁻¹) ∈ Q
    rw [map_mul, hβ, map_inv]
    have e : q * κ B * q⁻¹ * (κ B)⁻¹ = q * (κ B * q⁻¹ * (κ B)⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hQH (hκH B)) _).mp (Q.inv_mem hq))
  have hS := CFSG.ClassicalInvolution.sl2_isPerfect hF4
  have key := CFSG.GH74.Generic.S3.eq_of_inv_mul_mem_center hS β.toMonoidHom
    (MonoidHom.id SL(2, F)) (fun B => by
      have h1 := hmem B
      change (β B)⁻¹ * B ∈ Subgroup.center SL(2, F)
      have e : (β B)⁻¹ * B = B⁻¹ * (β B * B⁻¹)⁻¹ * B⁻¹⁻¹ := by group
      rw [e]
      exact (Subgroup.center SL(2, F)).normal_of_characteristic.conj_mem _
        (Subgroup.inv_mem _ h1) _)
  have hB₀ : β B₀ = B₀ := DFunLike.congr_fun key B₀
  have e := hβ B₀
  rw [hB₀] at e
  calc q * κ B₀ = q * κ B₀ * q⁻¹ * q := by group
    _ = κ B₀ * q := by rw [← e]

theorem le_range_of_commutator_eq {S : Type} [Group S] {ι : S →* M} {T D C : Subgroup M}
    (hTC : T ≤ C) (hDC : D ≤ C) (hTD : ⁅T, D⁆ = T)
    (hcomm : ∀ g ∈ C, ∀ h ∈ C, g * h * g⁻¹ * h⁻¹ ∈ ι.range) : T ≤ ι.range := by
  rw [← hTD, Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact hcomm g (hTC hg) h (hDC hh)

theorem mem_normalizer_threeGen {H : Subgroup M} {g : M} (hg : g ∈ H) :
    g ∈ Subgroup.normalizer (threeGen H : Set M) := by
  have hconj : ∀ {g : M}, g ∈ H → ∀ y ∈ threeGen H, g * y * g⁻¹ ∈ threeGen H := by
    intro g hg y hy
    have hle : threeGen H ≤ (threeGen H).comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hx, n, hn⟩
      refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg), n, ?_⟩
      change (g * x * g⁻¹) ^ 3 ^ n = 1
      rw [conj_pow, hn, mul_one, mul_inv_cancel]
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj hg y, fun hy => ?_⟩
  have e := hconj (H.inv_mem hg) _ hy
  rwa [inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at e

theorem card_le_two_of_le_range_sl2 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {ι : SL(2, F) →* M}
    (hι : Function.Injective ι) {T : Subgroup M} (hT : IsElemAbelian 2 T) (hTι : T ≤ ι.range) :
    Nat.card T ≤ 2 := by
  classical
  have hsq : ∀ x : SL(2, F), x ^ 2 = 1 → x = 1 ∨ x = -1 := by
    intro x hx
    have hm : (x : Matrix (Fin 2) (Fin 2) F) * x = 1 := by
      have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hx
      simpa [sq] using this
    have hdet := x.2
    rw [Matrix.det_fin_two] at hdet
    have e00 := congrFun (congrFun hm 0) 0
    have e01 := congrFun (congrFun hm 0) 1
    have e10 := congrFun (congrFun hm 1) 0
    have e11 := congrFun (congrFun hm 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    have htr : ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1) *
        (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination e01
    have htr' : ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1) *
        (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e10
    by_cases ht : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
    · exfalso
      apply h2
      have : (x : Matrix (Fin 2) (Fin 2) F) 1 1 = -(x : Matrix (Fin 2) (Fin 2) F) 0 0 := by
        linear_combination ht
      rw [this] at hdet
      linear_combination -e00 - hdet
    · have h01 : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := (mul_eq_zero.mp htr).resolve_left ht
      have h10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := (mul_eq_zero.mp htr').resolve_left ht
      rw [h01, h10, mul_zero, sub_zero] at hdet
      rw [h01] at e00 e11
      simp at e00 e11
      have e00' : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
        linear_combination e00
      rcases mul_self_eq_one_iff.mp e00' with h | h
      · left
        have h11 : (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by rw [h, one_mul] at hdet; exact hdet
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h, h01, h10, h11]
      · right
        have h11 : (x : Matrix (Fin 2) (Fin 2) F) 1 1 = -1 := by
          rw [h] at hdet
          linear_combination -hdet
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h, h01, h10, h11]
  have hsub : ∀ t ∈ T, t = 1 ∨ t = ι (-1) := by
    intro t ht
    obtain ⟨x, rfl⟩ := hTι ht
    have hx2 : x ^ 2 = 1 := hι (by rw [map_pow, hT.2 _ ht, map_one])
    rcases hsq x hx2 with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
  have : Finite T := by
    have hfin : Set.Finite ({1, ι (-1)} : Set M) := by simp
    exact Set.Finite.subset hfin (fun t ht => by
      rcases hsub t ht with h | h
      · simp [h]
      · simp [h])
  have : Fintype T := Fintype.ofFinite T
  rw [Nat.card_eq_fintype_card]
  calc Fintype.card T ≤ Fintype.card ({1, ι (-1)} : Finset M) := by
        refine Fintype.card_le_of_injective (fun t => ⟨t.1, ?_⟩) ?_
        · rcases hsub t.1 t.2 with h | h
          · simp [h]
          · simp [h]
        · intro a b h
          exact Subtype.ext (by simpa using congrArg Subtype.val h)
    _ ≤ 2 := by
        rw [Fintype.card_coe]
        exact Finset.card_le_two

theorem four_group_cases {T : Subgroup M} (hT : IsElemAbelian 2 T) (hT4 : Nat.card T = 4)
    {t₁ t₂ : M} (h1 : t₁ ∈ T) (h2 : t₂ ∈ T) (h11 : t₁ ≠ 1) (h21 : t₂ ≠ 1) (h12 : t₂ ≠ t₁) :
    ∀ t ∈ T, t = 1 ∨ t = t₁ ∨ t = t₂ ∨ t = t₁ * t₂ := by
  intro t ht
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3, n4⟩ := hne
  have ht1 : t₁ * t₁ = 1 := by rw [← sq]; exact hT.2 _ h1
  have h3 : t₁ * t₂ ≠ 1 := fun h => h12 (by
    calc t₂ = t₁ * (t₁ * t₂) := by rw [← mul_assoc, ht1, one_mul]
      _ = t₁ := by rw [h, mul_one])
  have h4 : t₁ * t₂ ≠ t₁ := fun h => h21 (by
    calc t₂ = t₁⁻¹ * (t₁ * t₂) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have h5 : t₁ * t₂ ≠ t₂ := fun h => h11 (by
    calc t₁ = (t₁ * t₂) * t₂⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  let f : Fin 5 → T := ![1, ⟨t₁, h1⟩, ⟨t₂, h2⟩, ⟨t₁ * t₂, T.mul_mem h1 h2⟩, ⟨t, ht⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have e := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp [f, h11, h11.symm, h21, h21.symm, h12, h12.symm, h3, h3.symm, h4, h4.symm,
          h5, h5.symm, n1, n1.symm, n2, n2.symm, n3, n3.symm, n4, n4.symm] at e)
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT4]; norm_num)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, hT4] at hle
  omega

theorem sl2_eq_one_or_neg_one_of_sq {R : Type*} [CommRing R] [IsDomain R] (h2 : (2 : R) ≠ 0)
    {x : SL(2, R)} (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have hm : (x : Matrix (Fin 2) (Fin 2) R) * x = 1 := by
    have := congrArg (fun A : SL(2, R) => (A : Matrix (Fin 2) (Fin 2) R)) hx
    simpa [sq] using this
  have hdet := x.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have htr : ((x : Matrix (Fin 2) (Fin 2) R) 0 0 + (x : Matrix (Fin 2) (Fin 2) R) 1 1) *
      (x : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by linear_combination e01
  have htr' : ((x : Matrix (Fin 2) (Fin 2) R) 0 0 + (x : Matrix (Fin 2) (Fin 2) R) 1 1) *
      (x : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by linear_combination e10
  by_cases ht : (x : Matrix (Fin 2) (Fin 2) R) 0 0 + (x : Matrix (Fin 2) (Fin 2) R) 1 1 = 0
  · exfalso
    apply h2
    have : (x : Matrix (Fin 2) (Fin 2) R) 1 1 = -(x : Matrix (Fin 2) (Fin 2) R) 0 0 := by
      linear_combination ht
    rw [this] at hdet
    linear_combination -e00 - hdet
  · have h01 : (x : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := (mul_eq_zero.mp htr).resolve_left ht
    have h10 : (x : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := (mul_eq_zero.mp htr').resolve_left ht
    rw [h01, h10, mul_zero, sub_zero] at hdet
    rw [h01] at e00 e11
    simp at e00 e11
    have e00' : (x : Matrix (Fin 2) (Fin 2) R) 0 0 * (x : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 := by
      linear_combination e00
    rcases mul_self_eq_one_iff.mp e00' with h | h
    · left
      have h11 : (x : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by rw [h, one_mul] at hdet; exact hdet
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, h01, h10, h11]
    · right
      have h11 : (x : Matrix (Fin 2) (Fin 2) R) 1 1 = -1 := by
        rw [h] at hdet
        linear_combination -hdet
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, h01, h10, h11]

theorem sl2_eq_one_or_neg_one_of_mem_center {R : Type*} [CommRing R] [IsDomain R]
    {x : SL(2, R)} (hx : x ∈ Subgroup.center SL(2, R)) : x = 1 ∨ x = -1 := by
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  rw [Fintype.card_fin] at hr2
  have hrr : r * r = 1 := by rw [← sq]; exact hr2
  rcases mul_self_eq_one_iff.mp hrr with h | h
  · left
    apply Subtype.ext
    rw [← hr, h, Matrix.SpecialLinearGroup.coe_one]
    simp
  · right
    apply Subtype.ext
    rw [← hr, h, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

end Core

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21

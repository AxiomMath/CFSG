module

public import CFSG.LocalAnalysis.StandardType.GGHalfAlphaCent
public import CFSG.LocalAnalysis.StandardType.GGHalfAux
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private noncomputable def rhoFun (m : ℕ) (hm : 3 ≤ m) (x : Fin (m + 1 + 1 + 1)) :
    Fin (m + 1 + 1 + 1) :=
  if h0 : x.val ≤ 1 then x
  else if h1 : x.val ≤ m then ⟨x.val + 2, by omega⟩
  else if h2 : x.val = m + 1 then ⟨2, by omega⟩
  else ⟨3, by omega⟩

private theorem rhoFun_val (m : ℕ) (hm : 3 ≤ m) (x : Fin (m + 1 + 1 + 1)) :
    (rhoFun m hm x).val =
      (if x.val ≤ 1 then x.val
       else if x.val ≤ m then x.val + 2
       else if x.val = m + 1 then 2 else 3) := by
  unfold rhoFun
  split_ifs <;> simp

private theorem rhoFun_injective (m : ℕ) (hm : 3 ≤ m) : Function.Injective (rhoFun m hm) := by
  intro x y h
  apply Fin.ext
  have hv : (rhoFun m hm x).val = (rhoFun m hm y).val := congrArg Fin.val h
  rw [rhoFun_val m hm x, rhoFun_val m hm y] at hv
  split_ifs at hv <;> omega

private noncomputable def rho (m : ℕ) (hm : 3 ≤ m) : Equiv.Perm (Fin (m + 1 + 1 + 1)) :=
  Equiv.ofBijective (rhoFun m hm)
    (Finite.injective_iff_bijective.mp (rhoFun_injective m hm))

private theorem rho_apply (m : ℕ) (hm : 3 ≤ m) (x : Fin (m + 1 + 1 + 1)) :
    rho m hm x = rhoFun m hm x := by
  simp only [rho, Equiv.ofBijective_apply]

private theorem rho_zero (m : ℕ) (hm : 3 ≤ m) : rho m hm (0 : Fin (m + 1 + 1 + 1)) = 0 := by
  rw [rho_apply]
  simp [rhoFun]

private theorem rho_one (m : ℕ) (hm : 3 ≤ m) : rho m hm (1 : Fin (m + 1 + 1 + 1)) = 1 := by
  rw [rho_apply]
  simp [rhoFun]

private theorem rho_of_two_le (m : ℕ) (hm : 3 ≤ m) {i : Fin (m + 1)} (hi : 2 ≤ i.val) :
    rho m hm (i.castSucc.castSucc : Fin (m + 1 + 1 + 1)) = i.succ.succ := by
  rw [rho_apply]
  have h1 : ¬ (i.castSucc.castSucc : Fin (m + 1 + 1 + 1)).val ≤ 1 := by
    simp only [Fin.val_castSucc]; omega
  have h2 : (i.castSucc.castSucc : Fin (m + 1 + 1 + 1)).val ≤ m := by
    simp only [Fin.val_castSucc]; omega
  unfold rhoFun
  rw [dif_neg h1, dif_pos h2]
  apply Fin.ext
  simp only [Fin.val_mk, Fin.val_castSucc, Fin.val_succ]

private theorem rho_m1 (m : ℕ) (hm : 3 ≤ m) :
    rho m hm (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) = ⟨2, by omega⟩ := by
  rw [rho_apply]
  have h1 : ¬ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)).val ≤ 1 := by
    show ¬ (m + 1 ≤ 1); omega
  have h2 : ¬ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)).val ≤ m := by
    show ¬ (m + 1 ≤ m); omega
  have h3 : (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)).val = m + 1 := rfl
  unfold rhoFun
  rw [dif_neg h1, dif_neg h2, dif_pos h3]

private theorem rho_m2 (m : ℕ) (hm : 3 ≤ m) :
    rho m hm (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) = ⟨3, by omega⟩ := by
  rw [rho_apply]
  have h1 : ¬ (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)).val ≤ 1 := by
    show ¬ (m + 2 ≤ 1); omega
  have h2 : ¬ (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)).val ≤ m := by
    show ¬ (m + 2 ≤ m); omega
  have h3 : ¬ (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)).val = m + 1 := by
    show ¬ (m + 2 = m + 1); omega
  unfold rhoFun
  rw [dif_neg h1, dif_neg h2, dif_neg h3]

private theorem rho_two (m : ℕ) (hm : 3 ≤ m) :
    rho m hm (2 : Fin (m + 1 + 1 + 1)) = 4 := by
  rw [rho_apply]
  have h1 : ¬ (2 : Fin (m + 1 + 1 + 1)).val ≤ 1 := by
    rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega)]
    omega
  have h2 : (2 : Fin (m + 1 + 1 + 1)).val ≤ m := by
    rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega)]
    omega
  unfold rhoFun
  rw [dif_neg h1, dif_pos h2]
  apply Fin.ext
  simp only [Fin.val_mk, Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega),
    Nat.mod_eq_of_lt (show (4:ℕ) < m + 1 + 1 + 1 by omega)]

private theorem rho_image_012 (m : ℕ) (hm : 3 ≤ m) :
    rho m hm '' ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))) = {0, 1, 4} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with rfl | rfl | rfl
    · simp [rho_zero m hm]
    · simp [rho_one m hm]
    · simp [rho_two m hm]
  · intro hy
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy) with rfl | rfl | rfl
    · exact ⟨0, by simp, rho_zero m hm⟩
    · exact ⟨1, by simp, rho_one m hm⟩
    · exact ⟨2, by simp, rho_two m hm⟩

private theorem slPerm_conj_transvection {N : ℕ} (π : Equiv.Perm (Fin N)) {i j : Fin N}
    (hij : i ≠ j) (c : F2) :
    slPerm gf2_two π * SpecialLinearGroup.transvection hij c * (slPerm gf2_two π)⁻¹ =
      SpecialLinearGroup.transvection (π.injective.ne hij) c := by
  have h := conj_transvection_of_coe_eq_signedPerm (coe_slPerm gf2_two π) (fun s => by simp) hij c
  simpa using h

private theorem slUpper2Hom_transvection {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j) (c : F2) :
    slUpper2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij)) c := by
  rw [slUpper2Hom, MonoidHom.comp_apply, slUpperBlockHom_transvection,
    slUpperBlockHom_transvection]

private theorem slLower2Hom_transvection {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j) (c : F2) :
    slLower2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hij)) c := by
  rw [slLower2Hom, MonoidHom.comp_apply, slLowerBlockHom_transvection,
    slLowerBlockHom_transvection]

theorem map_conj_slOn012 {m : ℕ} (hm : 3 ≤ m) {a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (h1 : ∀ s ∈ slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val},
      a * slUpper2Hom m s * a⁻¹ = slLower2Hom m s)
    (h2 : a * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * a⁻¹ = omegaBlock (m + 1 + 1) ⟨0, by omega⟩)
    (h3 : a * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * a⁻¹ =
      omegaBlock (m + 1 + 1) ⟨2, by omega⟩) :
    (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
        (MulAut.conj a).toMonoidHom =
      slOn (m + 1 + 1 + 1) ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1))) := by
  let P : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := slPerm gf2_two (rho m hm)
  let d : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := P⁻¹ * a
  have hR : ∀ s ∈ slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val},
      P * slUpper2Hom m s * P⁻¹ = slLower2Hom m s := by
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, j, hij, c, hi, hj, rfl⟩ := hx
        rw [slUpper2Hom_transvection, slLower2Hom_transvection]
        rw [show P = slPerm gf2_two (rho m hm) from rfl,
          slPerm_conj_transvection (rho m hm) _ c]
        apply Subtype.ext
        rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe,
          rho_of_two_le m hm hi, rho_of_two_le m hm hj]
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [map_mul, map_mul]
        rw [show P * (slUpper2Hom m x * slUpper2Hom m y) * P⁻¹ =
            (P * slUpper2Hom m x * P⁻¹) * (P * slUpper2Hom m y * P⁻¹) by group]
        rw [ihx, ihy]
    | inv x hx ihx =>
        rw [map_inv, map_inv]
        rw [show P * (slUpper2Hom m x)⁻¹ * P⁻¹ = (P * slUpper2Hom m x * P⁻¹)⁻¹ by group]
        rw [ihx]
  have hset : ((fun i : Fin (m + 1) => i.castSucc.castSucc) ''
        {j : Fin (m + 1) | 2 ≤ j.val}) =
      {j : Fin (m + 1 + 1 + 1) | 2 ≤ j.val ∧ j.val ≤ m} := by
    ext j
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp only [Set.mem_setOf_eq] at hi
      refine ⟨hi, ?_⟩
      simp only [Fin.val_castSucc]
      have := i.isLt
      omega
    · intro hj
      simp only [Set.mem_setOf_eq] at hj
      refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
      · exact hj.1
      · apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_mk]
  have hS : ∀ s ∈ slOn (m + 1 + 1 + 1) {j : Fin (m + 1 + 1 + 1) | 2 ≤ j.val ∧ j.val ≤ m},
      d * s = s * d := by
    have hmap : slOn (m + 1 + 1 + 1) {j : Fin (m + 1 + 1 + 1) | 2 ≤ j.val ∧ j.val ≤ m} =
        (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}).map (slUpper2Hom m) := by
      rw [slUpper2Hom_map_slOn, hset]
    intro s hs
    rw [hmap] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have hU : slUpper2Hom m s' = P⁻¹ * slLower2Hom m s' * P := by
      rw [← hR s' hs']; group
    calc d * slUpper2Hom m s' = P⁻¹ * a * slUpper2Hom m s' := rfl
      _ = P⁻¹ * (a * slUpper2Hom m s' * a⁻¹) * a := by group
      _ = P⁻¹ * slLower2Hom m s' * a := by rw [h1 s' hs']
      _ = (P⁻¹ * slLower2Hom m s' * P) * (P⁻¹ * a) := by group
      _ = slUpper2Hom m s' * d := by rw [← hU]
  have hR0 : P * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * P⁻¹ =
      omegaBlock (m + 1 + 1) ⟨0, by omega⟩ := by
    have hc0 : rho m hm ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc) =
        (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
      rw [show (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc = (0 : Fin (m + 1 + 1 + 1)) by
        apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_zero]]
      exact rho_zero m hm
    have hs0 : rho m hm ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ) =
        (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ := by
      rw [show (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ = (1 : Fin (m + 1 + 1 + 1)) by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_mk, Fin.val_zero, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega), Nat.zero_mod]]
      exact rho_one m hm
    rw [show P = slPerm gf2_two (rho m hm) from rfl,
      slPerm_conj_omegaBlock (rho m hm) hc0 hs0]
  have h0comm : d * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ =
      omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * d := by
    have ha0 : a * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ =
        omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * a := by
      calc a * omegaBlock (m + 1 + 1) ⟨0, by omega⟩
          = (a * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * a⁻¹) * a := by group
        _ = omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * a := by rw [h2]
    have hP0 : P * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ =
        omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * P := by
      calc P * omegaBlock (m + 1 + 1) ⟨0, by omega⟩
          = (P * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * P⁻¹) * P := by group
        _ = omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * P := by rw [hR0]
    have hPi0 : P⁻¹ * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ =
        omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * P⁻¹ := by
      calc P⁻¹ * omegaBlock (m + 1 + 1) ⟨0, by omega⟩
          = P⁻¹ * (omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * P) * P⁻¹ := by group
        _ = P⁻¹ * (P * omegaBlock (m + 1 + 1) ⟨0, by omega⟩) * P⁻¹ := by rw [← hP0]
        _ = omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * P⁻¹ := by group
    calc d * omegaBlock (m + 1 + 1) ⟨0, by omega⟩
        = P⁻¹ * (a * omegaBlock (m + 1 + 1) ⟨0, by omega⟩) := by
          rw [show d = P⁻¹ * a from rfl]; group
      _ = P⁻¹ * (omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * a) := by rw [ha0]
      _ = (P⁻¹ * omegaBlock (m + 1 + 1) ⟨0, by omega⟩) * a := by group
      _ = (omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * P⁻¹) * a := by rw [hPi0]
      _ = omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * d := by
          rw [show d = P⁻¹ * a from rfl]; group
  have hRk : P * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * P⁻¹ =
      omegaBlock (m + 1 + 1) ⟨2, by omega⟩ := by
    have hc : rho m hm ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc) =
        (⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
      rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc =
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) by
        apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk]]
      rw [rho_m1 m hm]
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_mk]
    have hs : rho m hm ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ) =
        (⟨2, by omega⟩ : Fin (m + 1 + 1)).succ := by
      rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ =
          (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) by
        apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]]
      rw [rho_m2 m hm]
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk]
    rw [show P = slPerm gf2_two (rho m hm) from rfl,
      slPerm_conj_omegaBlock (rho m hm) hc hs]
  have hkcomm : d * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ =
      omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * d := by
    have hconj : d * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * d⁻¹ =
        omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ := by
      calc d * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * d⁻¹
          = P⁻¹ * (a * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * a⁻¹) * P := by
            rw [show d = P⁻¹ * a from rfl]; group
        _ = P⁻¹ * omegaBlock (m + 1 + 1) ⟨2, by omega⟩ * P := by rw [h3]
        _ = omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ := by rw [← hRk]; group
    calc d * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩
        = (d * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * d⁻¹) * d := by group
      _ = omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * d := by rw [hconj]
  obtain ⟨p, q, hd_eq⟩ := eq_omegaBlock_pow_mul_pow hm hS h0comm hkcomm
  have hω0H : omegaBlock (m + 1 + 1) ⟨0, by omega⟩ ∈
      slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))) :=
    omegaBlock_mem_slOn (n := m + 1 + 1) (k := ⟨0, by omega⟩)
      (S := ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))))
      (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        left
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_zero])
      (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        right; left
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_mk, Fin.val_zero, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega), Nat.zero_mod])
  have hkN : omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ ∈
      Subgroup.normalizer (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))) := by
    have hkc : (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc ∉
        ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))) := by
      intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h
      · have hv := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_mk, Fin.val_zero] at hv; omega
      · have hv := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_mk, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega)] at hv; omega
      · have hv := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_mk, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega)] at hv; omega
    have hks : (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ ∉
        ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))) := by
      intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h
      · have hv := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_mk, Fin.val_zero] at hv; omega
      · have hv := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega)] at hv; omega
      · have hv := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega)] at hv; omega
    have hcomm : ∀ g ∈ slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))),
        omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * g =
          g * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ :=
      fun g hg => commute_omegaBlock_slOn (n := m + 1 + 1)
        (S := ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))) (k := ⟨m + 1, by omega⟩)
        ⟨hkc, hks⟩ hg
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx
      have hci : (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ * x =
          x * (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ := by
        calc (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ * x
            = (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ *
                (x * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) *
                (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ := by group
          _ = (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ *
                (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * x) *
                (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ := by rw [← hcomm x hx]
          _ = x * (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ := by group
      rw [hci, mul_assoc, inv_mul_cancel, mul_one]
      exact hx
    · intro hx
      have hc := hcomm ((omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ * x *
        omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) hx
      have heq : x = (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ * x *
          omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ := by
        calc x = omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ *
              ((omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ * x *
                omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) *
              (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ := by group
          _ = (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ * x *
                omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ := by rw [hc]; group
      rw [heq]
      exact hx
  have hdH : (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
        (MulAut.conj d).toMonoidHom =
      slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))) := by
    have hdN : d ∈ Subgroup.normalizer
        (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))) := by
      rw [hd_eq]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.le_normalizer hω0H) p)
        (Subgroup.pow_mem _ hkN q)
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp hdN
  have ha_eq : a = P * d := by
    rw [show d = P⁻¹ * a from rfl]; group
  have hcomp : (MulAut.conj a).toMonoidHom =
      (MulAut.conj P).toMonoidHom.comp (MulAut.conj d).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ha_eq]
    group
  calc
    (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
        (MulAut.conj a).toMonoidHom
      = (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
          ((MulAut.conj P).toMonoidHom.comp (MulAut.conj d).toMonoidHom) := by rw [hcomp]
    _ = ((slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
          (MulAut.conj d).toMonoidHom).map (MulAut.conj P).toMonoidHom := by
        rw [Subgroup.map_map]
    _ = (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
          (MulAut.conj P).toMonoidHom := by rw [hdH]
    _ = slOn (m + 1 + 1 + 1) ((rho m hm) '' ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))) :=
        slOn_map_conj_slPerm (rho m hm) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))
    _ = slOn (m + 1 + 1 + 1) ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1))) := by
        rw [rho_image_012 m hm]

end CFSG.StandardType.GGHalf

end

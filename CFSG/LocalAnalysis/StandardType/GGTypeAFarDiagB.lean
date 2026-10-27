module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarU

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Reg

variable {X : Type*} [Group X] {F : Type} [Field F] {m : ℕ}

theorem units_eq_one_of_mul_self_of_two (h2 : (2 : F) = 0) {τ : Fˣ} (h : τ * τ = 1) :
    τ = 1 := by
  have h' : (τ : F) * τ = 1 := by
    have e := congrArg (fun t : Fˣ => (t : F)) h
    simpa using e
  have h3 : ((τ : F) - 1) * ((τ : F) - 1) = 0 := by
    linear_combination h' + (1 - (τ : F)) * h2
  exact Units.ext (by simpa using sub_eq_zero.mp (mul_self_eq_zero.mp h3))

theorem slEntry_eq_zero_of_commute_diagAt (hm : 2 ≤ m) (h2 : (2 : F) = 0)
    {φ : SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F))
    {s : SpecialLinearGroup (Fin m) F}
    (hS : ∀ r : Fin m, ∃ g : X, ∃ τ : Fˣ, τ ≠ 1 ∧ GGActsVec φ g (diagAt r τ) ∧
      g * φ s = φ s * g)
    {i j : Fin m} (hij : i ≠ j) : (s : Matrix (Fin m) (Fin m) F) i j = 0 := by
  classical
  obtain ⟨g, τ, hτ, hg, hgs⟩ := hS i
  have hφ : φ (ggDiagConj (diagAt i τ) s) = φ s := by
    rw [← hg s, hgs]
    group
  have hz : ggDiagConj (diagAt i τ) s * s⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin m) F) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, mul_inv_cancel])
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hent : ∀ a b, (diagAt i τ a : F) * (s : Matrix (Fin m) (Fin m) F) a b *
      (((diagAt i τ b)⁻¹ : Fˣ) : F) = c * (s : Matrix (Fin m) (Fin m) F) a b := by
    intro a b
    have e : ((ggDiagConj (diagAt i τ) s : SpecialLinearGroup (Fin m) F) :
        Matrix (Fin m) (Fin m) F) = scalar (Fin m) c * (s : Matrix (Fin m) (Fin m) F) := by
      have e0 : ggDiagConj (diagAt i τ) s = (ggDiagConj (diagAt i τ) s * s⁻¹) * s := by group
      rw [e0, Matrix.SpecialLinearGroup.coe_mul, ← hc]
    have e1 := congrFun (congrFun e a) b
    rw [ggDiagConj_apply] at e1
    rw [e1, Matrix.scalar_apply, Matrix.diagonal_mul]
  by_contra hne
  have hcτ : c = τ := by
    have e := hent i j
    rw [diagAt_apply_self, diagAt_apply_of_ne hij.symm] at e
    simp only [inv_one, Units.val_one, mul_one] at e
    exact (mul_right_cancel₀ hne e).symm
  have hm1 : 1 < Fintype.card (Fin m) := by simpa using (by omega : 1 < m)
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card hm1 i
  have hrow : ∀ l, (s : Matrix (Fin m) (Fin m) F) k l = 0 := by
    intro l
    have e := hent k l
    rw [diagAt_apply_of_ne hk, hcτ] at e
    by_cases hl : l = i
    · subst hl
      rw [diagAt_apply_self] at e
      by_contra hkl
      apply hτ
      apply units_eq_one_of_mul_self_of_two h2
      have e' : (((τ⁻¹ : Fˣ)) : F) = τ := by
        simp only [Units.val_one, one_mul] at e
        exact mul_left_cancel₀ hkl (e.trans (mul_comm _ _))
      have e'' : τ⁻¹ = τ := Units.ext e'
      calc τ * τ = τ * τ⁻¹ := by rw [e'']
        _ = 1 := mul_inv_cancel τ
    · rw [diagAt_apply_of_ne hl] at e
      simp only [Units.val_one, one_mul, inv_one, mul_one] at e
      by_contra hkl
      apply hτ
      exact Units.ext (by simpa using (mul_right_cancel₀ hkl (e.symm.trans (one_mul _).symm)))
  have hdet : (s : Matrix (Fin m) (Fin m) F).det = 0 := Matrix.det_eq_zero_of_row_eq_zero k hrow
  rw [s.prop] at hdet
  exact one_ne_zero hdet

theorem ggActsDiag_of_offDiag_eq_zero {φ : SpecialLinearGroup (Fin m) F →* X}
    {s : SpecialLinearGroup (Fin m) F}
    (hs : ∀ i j, i ≠ j → (s : Matrix (Fin m) (Fin m) F) i j = 0) : GGActsDiag φ (φ s) := by
  classical
  have hdiag : (s : Matrix (Fin m) (Fin m) F) =
      diagonal (fun i => (s : Matrix (Fin m) (Fin m) F) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hs i j hij, diagonal_apply_ne _ hij]
  have hne : ∀ i, (s : Matrix (Fin m) (Fin m) F) i i ≠ 0 := by
    intro i h
    have hdet := s.prop
    rw [hdiag, det_diagonal] at hdet
    exact one_ne_zero (hdet.symm.trans (Finset.prod_eq_zero (Finset.mem_univ i) h))
  refine ⟨fun i => Units.mk0 _ (hne i), fun t => ?_⟩
  have e : ggDiagConj (fun i => Units.mk0 _ (hne i)) t * s = s * t := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_ggDiagConj]
    have hinv : diagonal (fun i => ((((Units.mk0 _ (hne i))⁻¹ : Fˣ)) : F)) *
        (s : Matrix (Fin m) (Fin m) F) = 1 := by
      ext a b
      rw [diagonal_mul, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp [hne a]
      · rw [hs a b hab, if_neg hab, mul_zero]
    have hd : diagonal (fun i => ((Units.mk0 _ (hne i) : Fˣ) : F)) =
        (s : Matrix (Fin m) (Fin m) F) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
      · rw [diagonal_apply_ne _ hab, hs a b hab]
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one, hd]
  have e' : s * t * s⁻¹ = ggDiagConj (fun i => Units.mk0 _ (hne i)) t := by
    rw [← e]
    group
  rw [← map_mul, ← map_inv, ← map_mul, e']

theorem ggActsDiag_of_commute_diagAt (hm : 2 ≤ m) (h2 : (2 : F) = 0)
    {φ : SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F))
    {s : SpecialLinearGroup (Fin m) F}
    (hS : ∀ r : Fin m, ∃ g : X, ∃ τ : Fˣ, τ ≠ 1 ∧ GGActsVec φ g (diagAt r τ) ∧
      g * φ s = φ s * g) : GGActsDiag φ (φ s) :=
  ggActsDiag_of_offDiag_eq_zero fun _ _ hij => slEntry_eq_zero_of_commute_diagAt hm h2 hker hS hij

theorem exists_mem_actsVec_diagAt (h2 : (2 : F) = 0) {p : ℕ} {Bs : Subgroup X}
    (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set X), g ^ p = 1 → g ∈ Bs) {n : ℕ}
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b) {g₀ : X} (hg₀ : g₀ ∈ Bs) {k : Fin (n + 1)} {τ : Fˣ}
    (hv : GGActsVec φ g₀ (diagAt k τ)) (r : Fin (n + 1)) :
    ∃ g ∈ Bs, GGActsVec φ g (diagAt r τ) := by
  have hN := slPerm_mem_normalizer_of_actsDiag h2 hBp hBs hker hdiag (Equiv.swap k r)
  refine ⟨_, (Subgroup.mem_normalizer_iff.1 hN g₀).1 hg₀, ?_⟩
  have e := hv.conj_perm h2 (Equiv.swap k r)
  rwa [diagAt_comp_perm, Equiv.swap_apply_left] at e

end Reg

section CoreK

variable {X : Type*} [Group X] {n : ℕ} {F : Type} [Field F]

theorem commute_of_ggDiagConj_right [Finite F] (h2 : (2 : F) = 0) (hF : Odd (Nat.card Fˣ))
    (hn : 3 ≤ n) {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hker₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n) {u : X}
    (hu : u = φ₁ (weylRep n F i) * φ₂ (weylRep n F j) * φ₁ (weylRep n F i) *
      φ₂ (weylRep n F j))
    {h' : Fin (n + 1) → Fˣ} (hu₂ : ∀ s, u * φ₂ s * u⁻¹ = φ₂ (ggDiagConj h' s))
    (hodd : (∀ s, u * φ₂ s = φ₂ s * u) → u * u = 1 → u = 1) :
    Commute (φ₂ (weylRep n F j)) (φ₁ (weylRep n F i)) := by
  set a := φ₁ (weylRep n F i) with ha_def
  set b := φ₂ (weylRep n F j) with hb_def
  have ha2 : a * a = 1 := by rw [ha_def, ← map_mul, weylRep_mul_self n h2, map_one]
  have hb2 : b * b = 1 := by rw [hb_def, ← map_mul, weylRep_mul_self n h2, map_one]
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hau : a * u * a = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, hu]
    calc a * (a * b * a * b) * a * (a * b * a * b)
        = (a * a) * b * a * b * (a * a) * b * a * b := by group
      _ = b * a * (b * b) * a * b := by rw [ha2]; group
      _ = b * (a * a) * b := by rw [hb2]; group
      _ = 1 := by rw [ha2, mul_one, hb2]
  have hbu : b * u * b = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, hu]
    calc b * (a * b * a * b) * b * (a * b * a * b)
        = b * a * b * a * (b * b) * a * b * a * b := by group
      _ = b * a * b * (a * a) * b * a * b := by rw [hb2]; group
      _ = b * a * (b * b) * a * b := by rw [ha2]; group
      _ = b * (a * a) * b := by rw [hb2]; group
      _ = 1 := by rw [ha2, mul_one, hb2]
  have hsq : ∀ x y : Fˣ, x * x = y * y → x = y := fun x y hxy =>
    eq_of_sq_eq_sq_of_odd hF (by rw [pow_two, pow_two, hxy])
  have hB := ratio_eq_of_ggDiagConj hker₂ (ggDiagConj_swap_eq_inv h2 j hbu hu₂)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set ψ : SpecialLinearGroup (Fin m) F →* X :=
    (φ₁.comp (slLowerBlockHom (m + 1) F)).comp (slLowerBlockHom m F) with hψ
  have hψK : ∀ s, ψ s = φ₂ (slUpperBlockHom (m + 1) F (slLowerBlockHom m F s)) := fun s => by
    have e := DFunLike.congr_fun hc (slLowerBlockHom m F s)
    simp only [MonoidHom.comp_apply] at e
    exact e
  have hic : i.castSucc = (0 : Fin (m + 1 + 1)) := Fin.ext (by simp [hi])
  have his : i.succ = (0 : Fin (m + 1)).succ := by rw [show i = 0 from Fin.ext hi]
  have ha_comm : ∀ s, a * ψ s = ψ s * a := fun s => by
    have e := congrArg φ₁ (slPerm_swap_zero_one_commute_lowerLower h2 s)
    rw [map_mul, map_mul] at e
    rw [ha_def, ← slPerm_swap_castSucc_succ h2, hic, his]
    exact e
  set g : Fin m → Fˣ := (h' ∘ Fin.castSucc) ∘ Fin.succ with hg
  have huψ : ∀ s, u * ψ s * u⁻¹ = ψ (ggDiagConj g s) := fun s => by
    rw [hψK, hu₂, ggDiagConj_slUpperBlockHom, ggDiagConj_slLowerBlockHom, hψK]
  have hψinv : ∀ s, ψ (ggDiagConj g s) = ψ (ggDiagConj g⁻¹ s) := fun s => by
    have e1 : u⁻¹ * ψ s * u = ψ (ggDiagConj g⁻¹ s) := by
      have e := (GGActsVec.inv (φ := ψ) huψ) s
      rwa [inv_inv] at e
    have ha_comm2 : ∀ t, a * ψ t * a = ψ t := fun t => by
      rw [ha_comm t, mul_assoc, ha2, mul_one]
    have hu' : u = a * u⁻¹ * a := by
      calc u = (a * a) * u * (a * a) := by rw [ha2]; group
        _ = a * (a * u * a) * a := by group
        _ = a * u⁻¹ * a := by rw [hau]
    have e2 : u⁻¹ * ψ s * u = ψ (ggDiagConj g s) := by
      calc u⁻¹ * ψ s * u = (a * u * a) * ψ s * (a * u⁻¹ * a) := by rw [← hu', hau]
        _ = a * (u * (a * ψ s * a) * u⁻¹) * a := by group
        _ = a * (u * ψ s * u⁻¹) * a := by rw [ha_comm2]
        _ = a * ψ (ggDiagConj g s) * a := by rw [huψ]
        _ = ψ (ggDiagConj g s) := ha_comm2 _
    rw [← e2, e1]
  have hθ : (φ₁.comp (slLowerBlockHom (m + 1) F)).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (injective_comp_slLowerBlockHom hker₁)]
    exact bot_le
  have hψker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F) := by
    rw [hψ, (MonoidHom.ker_eq_bot_iff _).mpr (injective_comp_slLowerBlockHom hθ)]
    exact bot_le
  have hA := ratio_eq_of_ggDiagConj hψker hψinv
  have hm : 2 ≤ m := by omega
  set e0 : Fin (m + 1 + 1) := ⟨0, by omega⟩ with he0
  set e1 : Fin (m + 1 + 1) := ⟨1, by omega⟩ with he1
  have hπ'k : ∀ k : Fin (m + 1 + 1), k.val + 2 ≤ m + 1 → Equiv.swap j.castSucc j.succ k = k := by
    intro k hk
    exact Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp; omega))
  have hB0 : ∀ k : Fin (m + 1 + 1), k.val + 2 ≤ m + 1 → h' k = h' e0 := by
    intro k hk
    have e := hB k e0
    simp only [Function.comp_apply, Pi.inv_apply, inv_inv, hπ'k k hk,
      hπ'k e0 (by simp [e0]; omega)] at e
    exact hsq _ _ e
  have hBl : h' j.succ * h' j.castSucc = h' e0 * h' e0 := by
    have e := hB j.castSucc e0
    simp only [Function.comp_apply, Pi.inv_apply, inv_inv, Equiv.swap_apply_left,
      hπ'k e0 (by simp [e0]; omega)] at e
    exact e
  have hA1 : ∀ k : Fin m, h' k.succ.castSucc = h' e1 := by
    intro k
    have e := hA k ⟨0, by omega⟩
    simp only [hg, Function.comp_apply, Pi.inv_apply, inv_inv] at e
    have e' := hsq _ _ e
    rw [e']
    rfl
  have h10 : h' e1 = h' e0 := hB0 e1 (by simp [e1]; omega)
  have hmid : ∀ k : Fin (m + 1 + 1), 1 ≤ k.val → k.val ≤ m → h' k = h' e0 := by
    intro k hk1 hkm
    have e := hA1 ⟨k.val - 1, by omega⟩
    rw [show (Fin.castSucc (Fin.succ (⟨k.val - 1, by omega⟩ : Fin m)) : Fin (m + 1 + 1)) = k from
      Fin.ext (by simp; omega)] at e
    rw [e, h10]
  have hlast : h' j.succ = h' e0 := by
    have hjc : h' j.castSucc = h' e0 := hmid _ (by simp; omega) (by simp; omega)
    rw [hjc] at hBl
    exact mul_right_cancel hBl
  have hall : ∀ k : Fin (m + 1 + 1), h' k = h' e0 := by
    intro k
    by_cases hk0 : k.val = 0
    · rw [show k = e0 from Fin.ext (by simp [e0, hk0])]
    by_cases hkl : k.val = m + 1
    · rw [show k = j.succ from Fin.ext (by simp; omega), hlast]
    exact hmid k (by omega) (by omega)
  have hconst : ∀ k l : Fin (m + 1 + 1), h' k = h' l := fun k l => by rw [hall k, hall l]
  have hcent : ∀ s, u * φ₂ s = φ₂ s * u := by
    intro s
    have e := hu₂ s
    rw [ggDiagConj_eq_self_of_const hconst] at e
    calc u * φ₂ s = u * φ₂ s * u⁻¹ * u := by group
      _ = φ₂ s * u := by rw [e]
  have hub : u * b = b * u := hcent (weylRep (m + 1) F j)
  have huu : u * u = 1 := by
    have e : u⁻¹ = u := by
      rw [← hbu, ← hub, mul_assoc, hb2, mul_one]
    calc u * u = u * u⁻¹ := by rw [e]
      _ = 1 := mul_inv_cancel u
  have hu1 := hodd hcent huu
  have hab : (a * b) * (a * b) = 1 := by
    rw [← hu1, hu]
    group
  have hab' : a * b = b * a := by
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      _ = b * a := by rw [_root_.mul_inv_rev, ha', hb']
  exact hab'.symm

end CoreK

end CFSG.StandardType

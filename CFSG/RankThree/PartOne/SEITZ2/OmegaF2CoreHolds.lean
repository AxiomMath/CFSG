module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Iface
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Emb
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Kernel
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Ring

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix CFSG.RankThree.PartOne.CTP

section Zvec

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (T : F2Triple Q) (u w : V)

@[expose] def F2Triple.zvec : V :=
  Phi Q u w (T.x 1) (T.x 2) • T.x 0 + Phi Q u w (T.x 0) (T.x 2) • T.x 1 +
    Phi Q u w (T.x 0) (T.x 1) • T.x 2

theorem F2Triple.polar_zvec_x (i : Fin 3) : polar Q (T.zvec u w) (T.x i) = 0 := by
  unfold F2Triple.zvec
  simp only [polar_add_left, polar_smul_left_eq, T.polar_xx]
  ring

theorem F2Triple.Q_zvec : Q (T.zvec u w) = 0 := by
  unfold F2Triple.zvec
  rw [map_add₃]
  simp only [map_smul_eq_sq, T.Q_x, polar_smul_left_eq, polar_smul_right_eq, T.polar_xx]
  ring

theorem F2Triple.polar_zvec_y2 :
    polar Q (T.zvec u w) (T.y 2) = Phi Q u w (T.x 0) (T.x 1) := by
  unfold F2Triple.zvec
  simp only [polar_add_left, polar_smul_left_eq, T.polar_xy]
  simp

section CharTwo

variable [CharP K 2]

theorem F2Triple.polar_zvec_u : polar Q (T.zvec u w) u = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold F2Triple.zvec Phi
  simp only [polar_add_left, polar_smul_left_eq]
  linear_combination (polar Q (T.x 0) u * polar Q (T.x 1) u * polar Q (T.x 2) w +
    polar Q (T.x 0) u * polar Q (T.x 1) w * polar Q (T.x 2) u +
    polar Q (T.x 0) w * polar Q (T.x 1) u * polar Q (T.x 2) u) * h2

theorem F2Triple.polar_zvec_w : polar Q (T.zvec u w) w = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold F2Triple.zvec Phi
  simp only [polar_add_left, polar_smul_left_eq]
  linear_combination (polar Q (T.x 0) w * polar Q (T.x 1) u * polar Q (T.x 2) w +
    polar Q (T.x 0) w * polar Q (T.x 1) w * polar Q (T.x 2) u +
    polar Q (T.x 0) u * polar Q (T.x 1) w * polar Q (T.x 2) w) * h2

theorem eichler_shear_step {M : Subgroup (V ≃ₗ[K] V)} {z e y b : V} (hz : Q z = 0) (he : Q e = 0)
    (hb : Q b = 0) (hze : polar Q z e = 0) (hzb : polar Q z b = 0) (heb : polar Q e b = 0) {c : K}
    (hrz : eichler Q e y z = z + c • e) (hrb : eichler Q e y b = b)
    (hr : eichler Q e y ∈ M) (hE : eichler Q z b ∈ M) : eichler Q e (c • b) ∈ M := by
  have hconj := eichler_conj (eichler_mem_orthogonalGroup Q e y) z b
  rw [hrz, hrb] at hconj
  have hce : Q (c • e) = 0 := by rw [map_smul_eq_sq, he, mul_zero]
  have hzce : polar Q z (c • e) = 0 := by rw [polar_smul_right_eq, hze, mul_zero]
  have hceb : polar Q (c • e) b = 0 := by rw [polar_smul_left_eq, heb, mul_zero]
  rw [eichler_left_add hz hce hb hzce hzb hceb, eichler_smul_left] at hconj
  have : eichler Q e (c • b) =
      (eichler Q z b)⁻¹ * (eichler Q e y * eichler Q z b * (eichler Q e y)⁻¹) := by
    rw [hconj]
    group
  rw [this]
  exact M.mul_mem (M.inv_mem hE) (M.mul_mem (M.mul_mem hr hE) (M.inv_mem hr))

theorem F2Triple.shear_line {M : Subgroup (V ≃ₗ[K] V)} {i : Fin 3} (hi : i ≠ 2)
    (hsh : eichler Q (T.x i) (T.y 2) ∈ M) (c₁ c₀ : K)
    (hE : eichler Q (T.zvec u w) (c₁ • T.x 1 + c₀ • T.x 0) ∈ M) :
    eichler Q (T.x i) ((Phi Q u w (T.x 0) (T.x 1) * c₁) • T.x 1 +
      (Phi Q u w (T.x 0) (T.x 1) * c₀) • T.x 0) ∈ M := by
  have hxy : polar Q (T.x i) (T.y 2) = 0 := by rw [T.polar_xy]; simp [hi]
  have hQb : Q (c₁ • T.x 1 + c₀ • T.x 0) = 0 :=
    map_comb_eq_zero (T.Q_x 1) (T.Q_x 0) (T.polar_xx 1 0) c₁ c₀
  have hpb : ∀ j, polar Q (T.x j) (c₁ • T.x 1 + c₀ • T.x 0) = 0 := fun j => by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, T.polar_xx, T.polar_xx]
    ring
  have hzb : polar Q (T.zvec u w) (c₁ • T.x 1 + c₀ • T.x 0) = 0 := by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, T.polar_zvec_x,
      T.polar_zvec_x]
    ring
  have hrz : eichler Q (T.x i) (T.y 2) (T.zvec u w) =
      T.zvec u w + Phi Q u w (T.x 0) (T.x 1) • T.x i := by
    rw [eichler_ts_apply (T.Q_x i) (T.Q_y 2) hxy, T.polar_zvec_x, T.polar_zvec_y2, zero_smul,
      add_zero]
  have hrb : eichler Q (T.x i) (T.y 2) (c₁ • T.x 1 + c₀ • T.x 0) = c₁ • T.x 1 + c₀ • T.x 0 := by
    rw [eichler_ts_apply (T.Q_x i) (T.Q_y 2) hxy]
    have h1 : polar Q (c₁ • T.x 1 + c₀ • T.x 0) (T.x i) = 0 := by
      rw [polar_comm]; exact hpb i
    have h2 : polar Q (c₁ • T.x 1 + c₀ • T.x 0) (T.y 2) = 0 := by
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, T.polar_xy, T.polar_xy]
      simp
    rw [h1, h2, zero_smul, zero_smul, add_zero, add_zero]
  have hstep := eichler_shear_step (M := M) (T.Q_zvec u w) (T.Q_x i) hQb (T.polar_zvec_x u w i)
    hzb (hpb i) hrz hrb hsh hE
  have : Phi Q u w (T.x 0) (T.x 1) • (c₁ • T.x 1 + c₀ • T.x 0) =
      (Phi Q u w (T.x 0) (T.x 1) * c₁) • T.x 1 + (Phi Q u w (T.x 0) (T.x 1) * c₀) • T.x 0 := by
    rw [smul_add, smul_smul, smul_smul]
  rwa [this] at hstep

end CharTwo

end Zvec

section Main

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem omegaF2_core {k : Subfield K} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ p) (hk : Nat.card k = 2) (T : F2Triple Q) {u w : V}
    (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) (hgen : T.Generic u w)
    {M : Subgroup (V ≃ₗ[K] V)} (huwM : eichler Q u w ∈ M)
    (h01 : eichler Q (T.x 0) (T.x 1) ∈ M) (h02 : eichler Q (T.x 0) (T.x 2) ∈ M)
    (h12 : eichler Q (T.x 1) (T.x 2) ∈ M)
    (hsh : ∀ i j, i ≠ j → eichler Q (T.x i) (T.y j) ∈ M) (t : K) :
    eichler Q (T.x 0) (t • T.x 1) ∈ M := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hδ, hgen2⟩ := hgen
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = Phi Q u w (T.x 0) (T.x 1) := ⟨_, rfl⟩
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ = Phi Q u w (T.x 1) (T.x 2) := ⟨_, rfl⟩
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, z₁ = Phi Q u w (T.x 0) (T.x 2) := ⟨_, rfl⟩
  rw [← hδdef] at hδ
  obtain ⟨z, hzdef⟩ : ∃ z, z = T.zvec u w := ⟨_, rfl⟩
  have hz : z = z₀ • T.x 0 + z₁ • T.x 1 + δ • T.x 2 := by
    rw [hzdef, F2Triple.zvec, ← hz₀, ← hz₁, ← hδdef]
  have hzu : polar Q z u = 0 := by rw [hzdef]; exact T.polar_zvec_u u w
  have hzw : polar Q z w = 0 := by rw [hzdef]; exact T.polar_zvec_w u w
  have hzx : ∀ i, polar Q z (T.x i) = 0 := fun i => by rw [hzdef]; exact T.polar_zvec_x u w i
  have hQz : Q z = 0 := by rw [hzdef]; exact T.Q_zvec u w
  have hδ' : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, a₂ = δ⁻¹ * z₁ := ⟨_, rfl⟩
  obtain ⟨a₃, ha₃⟩ : ∃ a₃, a₃ = δ⁻¹ * z₀ := ⟨_, rfl⟩
  have e1 : δ⁻¹ • z = a₃ • T.x 0 + a₂ • T.x 1 + T.x 2 := by
    rw [hz, ha₂, ha₃]
    match_scalars <;> first | rfl | field_simp
  have hx2 : T.x 2 = δ⁻¹ • z + a₃ • T.x 0 + a₂ • T.x 1 := by
    rw [e1]
    match_scalars <;>
      first | rfl | linear_combination (-a₃) * h2 | linear_combination (-a₂) * h2
  have ha : ¬ ((a₂ = 0 ∨ a₂ = 1) ∧ (a₃ = 0 ∨ a₃ = 1)) := by
    rintro ⟨h₂, h₃⟩
    have hvec : T.x 2 + a₃ • T.x 0 + a₂ • T.x 1 = δ⁻¹ • z := by
      rw [e1]
      abel
    refine hgen2 a₃ a₂ h₃ h₂ ⟨?_, ?_⟩
    · rw [hvec, polar_smul_left_eq, hzu, mul_zero]
    · rw [hvec, polar_smul_left_eq, hzw, mul_zero]
  have hδ'' : polar Q (T.x 0) u * polar Q (T.x 1) w + polar Q (T.x 0) w * polar Q (T.x 1) u ≠ 0 :=
    by rw [hδdef] at hδ; exact hδ
  obtain ⟨P, P', hOrth, hPe, hP'e, hperp, hE⟩ :=
    exists_dual_data (T.Q_x 0) (T.Q_x 1) (T.polar_xx 0 1) hu hw huw hδ''
  have hscal : polar Q (T.x 0) u * polar Q (T.x 1) w + polar Q (T.x 0) w * polar Q (T.x 1) u =
      δ := by rw [hδdef]; rfl
  rw [hscal] at hE
  have hze : polar Q z P.e = 0 := by rw [hPe]; exact hzx 0
  have hzf : polar Q z P.f = 0 := (hperp z hzu hzw).1
  have hze' : polar Q z P'.e = 0 := by rw [hP'e]; exact hzx 1
  have hzf' : polar Q z P'.f = 0 := (hperp z hzu hzw).2
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Aff K →* (V ≃ₗ[K] V),
      ∀ x : Aff K, Ψ x = eichler Q z (vecOf P P' x.b) * planeHom hOrth x.m :=
    ⟨psi hOrth z hze hzf hze' hzf', fun x => rfl⟩
  have hQz' : Q (δ⁻¹ • z) = 0 := by rw [map_smul_eq_sq, hQz, mul_zero]
  have hpz : ∀ i, polar Q (δ⁻¹ • z) (T.x i) = 0 := fun i => by
    rw [polar_smul_left_eq, hzx i, mul_zero]
  have hpz' : ∀ i, polar Q (T.x i) (δ⁻¹ • z) = 0 := fun i => by
    rw [polar_comm]; exact hpz i
  have hΨ1 : Ψ ⟨u2 1, 0⟩ = eichler Q (T.x 0) (T.x 1) := by
    rw [hΨ]
    show eichler Q z (vecOf P P' 0) * planeHom hOrth (u2 1) = _
    rw [vecOf_zero, eichler_zero_right, one_mul, planeHom_u2, hPe, hP'e, one_smul]
  have hΨ2 : Ψ ⟨l2 δ, 0⟩ = eichler Q u w := by
    rw [hΨ]
    show eichler Q z (vecOf P P' 0) * planeHom hOrth (l2 δ) = _
    rw [vecOf_zero, eichler_zero_right, one_mul, planeHom_l2, hE]
  have hΨ3 : Ψ ⟨u2 a₂, !![0, δ⁻¹; 0, 0]⟩ = eichler Q (T.x 0) (T.x 2) := by
    rw [hΨ]
    show eichler Q z (vecOf P P' !![0, δ⁻¹; 0, 0]) * planeHom hOrth (u2 a₂) = _
    have hv : vecOf P P' !![0, δ⁻¹; 0, 0] = δ⁻¹ • T.x 0 := by simp [vecOf, hPe]
    have e1' : eichler Q z (δ⁻¹ • T.x 0) = eichler Q (T.x 0) (δ⁻¹ • z) :=
      (eichler_smul_left δ⁻¹ z (T.x 0)).symm.trans (eichler_symm_ts hQz' (T.Q_x 0) (hpz 0))
    have hp01 : polar Q (T.x 0) (a₂ • T.x 1) = 0 := by
      rw [polar_smul_right_eq, T.polar_xx, mul_zero]
    have hre : δ⁻¹ • z + a₃ • T.x 0 + a₂ • T.x 1 = (δ⁻¹ • z + a₂ • T.x 1) + a₃ • T.x 0 := by abel
    rw [hv, planeHom_u2, hPe, hP'e, e1', eichler_mul (hpz' 0) hp01, hx2, hre,
      eichler_add_smul_self (T.Q_x 0)]
  have hΨ4 : Ψ ⟨u2 a₃, !![δ⁻¹, 0; 0, 0]⟩ = eichler Q (T.x 1) (T.x 2) := by
    rw [hΨ]
    show eichler Q z (vecOf P P' !![δ⁻¹, 0; 0, 0]) * planeHom hOrth (u2 a₃) = _
    have hv : vecOf P P' !![δ⁻¹, 0; 0, 0] = δ⁻¹ • T.x 1 := by simp [vecOf, hP'e]
    have e1' : eichler Q z (δ⁻¹ • T.x 1) = eichler Q (T.x 1) (δ⁻¹ • z) :=
      (eichler_smul_left δ⁻¹ z (T.x 1)).symm.trans (eichler_symm_ts hQz' (T.Q_x 1) (hpz 1))
    have hQa : Q (a₃ • T.x 0) = 0 := by rw [map_smul_eq_sq, T.Q_x, mul_zero]
    have hpa : polar Q (a₃ • T.x 0) (T.x 1) = 0 := by
      rw [polar_smul_left_eq, T.polar_xx, mul_zero]
    have e2' : eichler Q (T.x 0) (a₃ • T.x 1) = eichler Q (T.x 1) (a₃ • T.x 0) :=
      (eichler_smul_left a₃ (T.x 0) (T.x 1)).symm.trans (eichler_symm_ts hQa (T.Q_x 1) hpa)
    have hp10 : polar Q (T.x 1) (a₃ • T.x 0) = 0 := by
      rw [polar_smul_right_eq, T.polar_xx, mul_zero]
    rw [hv, planeHom_u2, hPe, hP'e, e1', e2', eichler_mul (hpz' 1) hp10, hx2,
      eichler_add_smul_self (T.Q_x 1)]
  have g1 : (⟨u2 1, 0⟩ : Aff K) ∈ M.comap Ψ := Subgroup.mem_comap.2 (by rw [hΨ1]; exact h01)
  have g2 : (⟨l2 δ, 0⟩ : Aff K) ∈ M.comap Ψ := Subgroup.mem_comap.2 (by rw [hΨ2]; exact huwM)
  have g3 : (⟨u2 a₂, !![0, δ⁻¹; 0, 0]⟩ : Aff K) ∈ M.comap Ψ :=
    Subgroup.mem_comap.2 (by rw [hΨ3]; exact h02)
  have g4 : (⟨u2 a₃, !![δ⁻¹, 0; 0, 0]⟩ : Aff K) ∈ M.comap Ψ :=
    Subgroup.mem_comap.2 (by rw [hΨ4]; exact h12)
  have hK' : Nat.card K = Nat.card k ^ p := by rw [hK, hk]
  have hk' : ∀ x ∈ k, x = 0 ∨ x = 1 := fun x hx => (mem_subfield_two_iff hk).1 hx
  obtain ⟨β₀, β₁, hβ, hline⟩ := aff_kernel_line hp hp2 hK' hk' hδ ha (M.comap Ψ) g1 g2 g3 g4
  have hEz : ∀ s : K, eichler Q z ((s * β₀) • T.x 1 + (s * β₁) • T.x 0) ∈ M := by
    intro s
    have h := Subgroup.mem_comap.1 (hline s)
    rw [hΨ] at h
    have hv : vecOf P P' !![s * β₀, s * β₁; 0, 0] = (s * β₀) • T.x 1 + (s * β₁) • T.x 0 := by
      simp [vecOf, hPe, hP'e]
    change eichler Q z (vecOf P P' !![s * β₀, s * β₁; 0, 0]) * planeHom hOrth 1 ∈ M at h
    rwa [hv, map_one, mul_one] at h
  have hz' : z = T.zvec u w := hzdef
  have swap01 : ∀ r : K, eichler Q (T.x 0) (r • T.x 1) = eichler Q (T.x 1) (r • T.x 0) := fun r =>
    (eichler_smul_left r (T.x 0) (T.x 1)).symm.trans
      (eichler_symm_ts (by rw [map_smul_eq_sq, T.Q_x, mul_zero]) (T.Q_x 1)
        (by rw [polar_smul_left_eq, T.polar_xx, mul_zero]))
  have key : ∀ s : K, eichler Q (T.x 0) (s • T.x 1) ∈ M := by
    intro s
    by_cases hβ₀ : β₀ = 0
    · subst hβ₀
      have hβ₁ : β₁ ≠ 0 := hβ.resolve_left (not_not.2 rfl)
      have hδβ : δ * β₁ ≠ 0 := mul_ne_zero hδ hβ₁
      have h := T.shear_line u w (i := 1) (by decide) (hsh 1 2 (by decide)) _ _
        (hz' ▸ hEz (s / (δ * β₁)))
      rw [← hδdef] at h
      simp only [mul_zero, zero_smul, zero_add] at h
      have hs : δ * (s / (δ * β₁) * β₁) = s := by field_simp
      rw [hs] at h
      rw [swap01]
      exact h
    · have hδβ : δ * β₀ ≠ 0 := mul_ne_zero hδ hβ₀
      have h := T.shear_line u w (i := 0) (by decide) (hsh 0 2 (by decide)) _ _
        (hz' ▸ hEz (s / (δ * β₀)))
      rw [← hδdef, eichler_add_smul_self (T.Q_x 0)] at h
      have hs : δ * (s / (δ * β₀) * β₀) = s := by field_simp
      rw [hs] at h
      exact h
  exact key t

end Main

theorem omegaF2Core_holds : OmegaF2Core := by
  intro K V _ _ _ _ _ Q k p hp hp2 hK hk T u w hu hw huw hgen M huwM h01 h02 h12 hsh t
  exact omegaF2_core hp hp2 hK hk T hu hw huw hgen huwM h01 h02 h12 hsh t

end CFSG.RankThree.PartOne.SEITZ2

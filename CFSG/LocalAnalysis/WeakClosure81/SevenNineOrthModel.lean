module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthModelY

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace OrthFrame

variable {p m : ℕ} [Fact p.Prime] {f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p)}
  (F : OrthFrame p m f)

private theorem f_orthRefl_mulVec_a {v w : Fin m → ZMod p} (hvv : f v v = -2) :
    f ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) F.a =
      f w F.a + f w v * f F.a v := by
  rw [orthRefl_mulVec f hvv]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [F.symm v F.a]

private theorem f_orthRefl_self_mulVec_a {v : Fin m → ZMod p} (hvv : f v v = -2) :
    f ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a) F.a =
      -2 + f F.a v * f F.a v := by
  rw [orthRefl_mulVec f hvv]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [F.norm_a, F.symm v F.a]

private theorem mulVec_orthRefl_mulVec {v : Fin m → ZMod p} (hvv : f v v = -2)
    (x : Fin m → ZMod p) :
    (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ
      ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) = x := by
  have hmat : (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *
      (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) = 1 := by
    have h := congrArg (fun g : GL (Fin m) (ZMod p) => (g : Matrix (Fin m) (Fin m) (ZMod p)))
      (orthRefl_mul_self f hvv)
    simpa [Matrix.GeneralLinearGroup.coe_mul] using h
  rw [Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]

private theorem siegel_eq_pow_siegel_smul {v : Fin m → ZMod p} {c : ZMod p}
    (hc : c ≠ 0) (hcs : f (c • v) F.s = 0) :
    F.siegel v = (F.siegel (c • v)) ^ (c⁻¹).val := by
  rw [← siegel_nsmul F hcs]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul]
  rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ hc, one_smul]

private theorem conj_siegel_orthRefl {v w : Fin m → ZMod p} (hvU : v ∈ F.U)
    (hvv : f v v = -2) :
    orthRefl f v * F.siegel w * (orthRefl f v)⁻¹
      = F.siegel ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) :=
  F.siegel_conj (isOrthIsometry_orthRefl f F.symm v) (F.orthRefl_mulVec_s (F.mem_U.1 hvU).1) w

private theorem exists_conj_of_siegel_a_not_mem {B : Subgroup (GL (Fin m) (ZMod p))}
    (hTa : F.siegel F.a ∉ B) (hBZ : B ≠ F.Z) :
    ∃ h ∈ Subgroup.closure (orthReflSet p m f),
      h ∈ Subgroup.normalizer (F.Y : Set (GL (Fin m) (ZMod p))) ∧
        conjSubgroup B h ≠ F.Z ∧ ¬ ⁅F.Y, Subgroup.zpowers F.refl⁆ ≤ conjSubgroup B h := by
  refine ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, ?_, ?_⟩
  · rwa [conjSubgroup_one]
  · rw [conjSubgroup_one]
    exact fun hle => hTa (hle F.siegel_a_mem_commutator)

private theorem exists_conj_of_eq_Z (hsq : ∀ c : ZMod p, c * c ≠ 2)
    (hvw : ∃ v w, v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0 ∧ w ∈ F.U ∧ f w F.a = 0 ∧
      f w v ≠ 0) :
    ∃ h ∈ Subgroup.closure (orthReflSet p m f),
      h ∈ Subgroup.normalizer (F.Y : Set (GL (Fin m) (ZMod p))) ∧
        conjSubgroup F.Z h ≠ F.Z ∧ ¬ ⁅F.Y, Subgroup.zpowers F.refl⁆ ≤ conjSubgroup F.Z h := by
  obtain ⟨v, w, hvU, hvv, hav, hwU, hwa, hwv⟩ := hvw
  have hrvwU : (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w ∈ F.U := by
    rw [orthRefl_mulVec f hvv]
    exact F.U.add_mem hwU (F.U.smul_mem _ hvU)
  have hrv_a_U : (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a ∈ F.U := by
    rw [orthRefl_mulVec f hvv]
    exact F.U.add_mem F.a_mem_U (F.U.smul_mem _ hvU)
  have hrvw_ne : f ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) F.a ≠ 0 := by
    rw [f_orthRefl_mulVec_a F hvv, hwa, zero_add]
    exact mul_ne_zero hwv hav
  have hconj_w := conj_siegel_orthRefl F hvU hvv (w := w)
  have hconj_a := conj_siegel_orthRefl F hvU hvv (w := F.a)
  have hTwZ : F.siegel w ∈ F.Z := (F.siegel_mem_Z_iff hwU).2 hwa
  have hconjZ : conjSubgroup F.Z (orthRefl f v) ≠ F.Z := by
    intro hEq
    have hmem : F.siegel w ∈ conjSubgroup F.Z (orthRefl f v) := by
      rw [hEq]
      exact hTwZ
    rw [mem_conjSubgroup_iff, hconj_w, F.siegel_mem_Z_iff hrvwU] at hmem
    exact hrvw_ne hmem
  have hTaNotConj : F.siegel F.a ∉ conjSubgroup F.Z (orthRefl f v) := by
    intro hmem
    rw [mem_conjSubgroup_iff, hconj_a] at hmem
    have hzero : f ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a) F.a = 0 :=
      (F.siegel_mem_Z_iff hrv_a_U).1 hmem
    rw [f_orthRefl_self_mulVec_a F hvv] at hzero
    exact hsq (f F.a v) (by linear_combination hzero)
  refine ⟨orthRefl f v, Subgroup.subset_closure (orthRefl_mem f hvv),
    F.orthRefl_mem_normalizer_Y hvU, hconjZ, ?_⟩
  intro hle
  exact hTaNotConj (hle F.siegel_a_mem_commutator)

private theorem exists_siegel_not_mem {B : Subgroup (GL (Fin m) (ZMod p))}
    (hspan : F.U ≤ Submodule.span (ZMod p) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0})
    (hBY : B ≤ F.Y) (hcard : Nat.card B * p = Nat.card F.Y) :
    ∃ v, v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0 ∧ F.siegel v ∉ B := by
  by_contra h
  push Not at h
  have hclosure :
      Subgroup.closure (F.siegel '' {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0}) ≤ B := by
    rw [Subgroup.closure_le]
    rintro x ⟨v, hv, rfl⟩
    exact h v hv.1 hv.2.1 hv.2.2
  have hYle : F.Y ≤ B := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := F.mem_Y.1 hg
    exact hclosure (F.siegel_mem_closure_of_span hspan hw)
  have hBY' : B = F.Y := le_antisymm hBY hYle
  have hBpos : 0 < Nat.card ↥B := by
    haveI : Nonempty ↥B := ⟨⟨1, B.one_mem⟩⟩
    exact Nat.card_pos
  have hc : Nat.card ↥B * p = Nat.card ↥B * 1 := by
    rw [mul_one]
    calc Nat.card ↥B * p = Nat.card ↥F.Y := hcard
      _ = Nat.card ↥B := by rw [hBY']
  have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_left hBpos hc
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

private theorem siegel_smul_a_mem_conj_not_mem_Z (hsq : ∀ c : ZMod p, c * c ≠ 2)
    {v : Fin m → ZMod p} (hvU : v ∈ F.U) (hvv : f v v = -2)
    {B : Subgroup (GL (Fin m) (ZMod p))} (hTa : F.siegel F.a ∈ B) :
    F.siegel ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a)
        ∈ conjSubgroup B (orthRefl f v) ∧
      F.siegel ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a) ∉ F.Z := by
  constructor
  · rw [mem_conjSubgroup_iff]
    have hconj : orthRefl f v *
        F.siegel ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a) *
          (orthRefl f v)⁻¹ = F.siegel F.a := by
      rw [conj_siegel_orthRefl F hvU hvv
        (w := (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a)]
      rw [mulVec_orthRefl_mulVec hvv F.a]
    rw [hconj]
    exact hTa
  · intro hz
    have hrv_a_U : (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a ∈ F.U := by
      rw [orthRefl_mulVec f hvv]
      exact F.U.add_mem F.a_mem_U (F.U.smul_mem _ hvU)
    rw [F.siegel_mem_Z_iff hrv_a_U, f_orthRefl_self_mulVec_a F hvv] at hz
    exact hsq (f F.a v) (by linear_combination hz)

private theorem exists_conj_of_siegel_a_mem (hsq : ∀ c : ZMod p, c * c ≠ 2)
    (hspan : F.U ≤ Submodule.span (ZMod p) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0})
    {B : Subgroup (GL (Fin m) (ZMod p))} (hBY : B ≤ F.Y)
    (hcard : Nat.card B * p = Nat.card F.Y) (hTa : F.siegel F.a ∈ B) :
    ∃ h ∈ Subgroup.closure (orthReflSet p m f),
      h ∈ Subgroup.normalizer (F.Y : Set (GL (Fin m) (ZMod p))) ∧
        conjSubgroup B h ≠ F.Z ∧ ¬ ⁅F.Y, Subgroup.zpowers F.refl⁆ ≤ conjSubgroup B h := by
  obtain ⟨v, hvU, hvv, hav, hvB⟩ := exists_siegel_not_mem F hspan hBY hcard
  have hs : f v F.s = 0 := (F.mem_U.1 hvU).1
  set c : ZMod p := f F.a v with hc
  have hcne : c ≠ 0 := by rw [hc]; exact hav
  have hcs : f (c • v) F.s = 0 := by
    rw [hc]
    simp [smul_eq_mul, hs]
  have hrv_a : (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a = F.a + c • v := by
    rw [orthRefl_mulVec f hvv, hc]
  have hTa_cv : F.siegel ((orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.a)
      = F.siegel F.a * F.siegel (c • v) := by
    rw [hrv_a, F.siegel_add (F.mem_U.1 F.a_mem_U).1 hcs]
  have hTv_pow : F.siegel v = (F.siegel (c • v)) ^ (c⁻¹).val :=
    siegel_eq_pow_siegel_smul F hcne hcs
  have hTcvB : F.siegel (c • v) ∉ B := by
    intro hmem
    exact hvB (by rw [hTv_pow]; exact B.pow_mem hmem _)
  have hTaTcvB : F.siegel F.a * F.siegel (c • v) ∉ B := by
    intro hmem
    apply hTcvB
    have heq : F.siegel (c • v) = (F.siegel F.a)⁻¹ * (F.siegel F.a * F.siegel (c • v)) := by
      group
    rw [heq]
    exact B.mul_mem (B.inv_mem hTa) hmem
  have hTaNotConj : F.siegel F.a ∉ conjSubgroup B (orthRefl f v) := by
    intro hmem
    rw [mem_conjSubgroup_iff, conj_siegel_orthRefl F hvU hvv (w := F.a), hTa_cv] at hmem
    exact hTaTcvB hmem
  obtain ⟨hTaMemConj, hTaNotZ⟩ := siegel_smul_a_mem_conj_not_mem_Z F hsq hvU hvv hTa
  have hconjZ : conjSubgroup B (orthRefl f v) ≠ F.Z := by
    intro hEq
    rw [hEq] at hTaMemConj
    exact hTaNotZ hTaMemConj
  refine ⟨orthRefl f v, Subgroup.subset_closure (orthRefl_mem f hvv),
    F.orthRefl_mem_normalizer_Y hvU, hconjZ, ?_⟩
  intro hle
  exact hTaNotConj (hle F.siegel_a_mem_commutator)

theorem exists_conj_of_span (hsq : ∀ c : ZMod p, c * c ≠ 2)
    (hspan : F.U ≤ Submodule.span (ZMod p) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0})
    (hvw : ∃ v w, v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0 ∧ w ∈ F.U ∧ f w F.a = 0 ∧ f w v ≠ 0) :
    ∀ B : Subgroup (GL (Fin m) (ZMod p)), B ≤ F.Y → Nat.card B * p = Nat.card F.Y →
      ∃ h ∈ Subgroup.closure (orthReflSet p m f),
        h ∈ Subgroup.normalizer (F.Y : Set (GL (Fin m) (ZMod p))) ∧ conjSubgroup B h ≠ F.Z ∧
          ¬ ⁅F.Y, Subgroup.zpowers F.refl⁆ ≤ conjSubgroup B h := by
  intro B hBY hcard
  by_cases hBZ : B = F.Z
  · subst hBZ
    exact exists_conj_of_eq_Z F hsq hvw
  · by_cases hTa : F.siegel F.a ∈ B
    · exact exists_conj_of_siegel_a_mem F hsq hspan hBY hcard hTa
    · exact exists_conj_of_siegel_a_not_mem F hTa hBZ

theorem sevenNineConfig_of_span (hsq : ∀ c : ZMod p, c * c ≠ 2)
    (hspan : F.U ≤ Submodule.span (ZMod p) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0})
    (hvw : ∃ v w, v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0 ∧ w ∈ F.U ∧ f w F.a = 0 ∧ f w v ≠ 0)
    (hz : ∀ w ∈ F.U, f w F.a = 0 → F.siegel w ∈ orthConjSup f F.a) :
    SevenNineConfig (Subgroup.closure (orthReflSet p m f)) (Subgroup.zpowers F.refl) p F.Y F.Z :=
  { prime := Fact.out
    ne_two := by
      rintro rfl
      exact F.two_ne (ZMod.natCast_self 2)
    card_s := card_zpowers_refl F
    le := Y_le_closure F hspan
    elemAbelian := isElemAbelian_Y F
    s_le := zpowers_refl_le_normalizer F
    z_eq := rfl
    card_z := card_Z_mul F
    z_le := Z_le_orthConjSup F hz
    exists_conj := exists_conj_of_span F hsq hspan hvw }

end OrthFrame

end CFSG.LocalAnalysis.WeakClosure81

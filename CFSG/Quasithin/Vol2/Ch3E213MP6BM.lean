module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BL
public import CFSG.Quasithin.Vol2.Ch3E213MP6BH

public section

namespace CFSG.Quasithin.Ch3E213M.P6B

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt uMat glMat_uElt
  mem_antiSp antiUnipotentCenter transpose_mul_minorJ_mul_apply minorJ_apply)
open CFSG.Quasithin.SteinbergBS (mul_uMat_apply_two mul_uMat_apply_three uMat_mul_apply_zero
  uMat_mul_apply_one uMat_mul_apply_two)
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj uElt_zero_eq_one)
open CFSG.Blueprint (suzukiGroup)
open CFSG.LieType.Ree (suzukiU suzukiSElt mem_suzukiZ0_iff)

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem uMat_mul_apply_three (N : Matrix (Fin 4) (Fin 4) k) (a b c d : k) (j : Fin 4) :
    (uMat a b c d * N) 3 j = N 3 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

theorem isUpper_of_conj_center {d : antiSp k} {b c b' c' : k} (hb : b ≠ 0) (hc : c ≠ 0)
    (hb' : b' ≠ 0) (h : d * uElt 0 b' c' 0 * d⁻¹ = uElt 0 b c 0) : IsUpper d := by
  have h1 : d * uElt 0 b' c' 0 = uElt 0 b c 0 * d := by rw [← h]; group
  have h2 := congrArg (fun g : antiSp k => glMat (g : GL (Fin 4) k)) h1
  have hE : glMat (d : GL (Fin 4) k) * uMat 0 b' c' 0 =
      uMat 0 b c 0 * glMat (d : GL (Fin 4) k) := by
    simpa [glMat_uElt] using h2
  have hJ := mem_antiSp.mp d.2
  have htwo : (2 : k) = 0 := CharTwo.two_eq_zero
  set M := glMat (d : GL (Fin 4) k) with hM
  have entry : ∀ (P Q : Matrix (Fin 4) (Fin 4) k), P = Q → ∀ i j, P i j = Q i j :=
    fun P Q h i j => by rw [h]
  have e22 := entry _ _ hE 2 2
  have e32 := entry _ _ hE 3 2
  have e23 := entry _ _ hE 2 3
  have e33 := entry _ _ hE 3 3
  have e12 := entry _ _ hE 1 2
  have e02 := entry _ _ hE 0 2
  have j02 := entry _ _ hJ 0 2
  rw [mul_uMat_apply_two, uMat_mul_apply_two] at e22
  rw [mul_uMat_apply_two, uMat_mul_apply_three] at e32
  rw [mul_uMat_apply_three, uMat_mul_apply_two] at e23
  rw [mul_uMat_apply_three, uMat_mul_apply_three] at e33
  rw [mul_uMat_apply_two, uMat_mul_apply_one] at e12
  rw [mul_uMat_apply_two, uMat_mul_apply_zero] at e02
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at j02
  norm_num at j02
  have h20 : M 2 0 = 0 :=
    (mul_eq_zero.mp (show M 2 0 * b' = 0 by linear_combination e22)).resolve_right hb'
  have h30 : M 3 0 = 0 :=
    (mul_eq_zero.mp (show M 3 0 * b' = 0 by linear_combination e32)).resolve_right hb'
  have h21 : M 2 1 = 0 :=
    (mul_eq_zero.mp (show M 2 1 * b' = 0 by linear_combination e23 - c' * h20)).resolve_right hb'
  have h31 : M 3 1 = 0 :=
    (mul_eq_zero.mp (show M 3 1 * b' = 0 by linear_combination e33 - c' * h30)).resolve_right hb'
  have E1 : M 1 0 * b' = b * M 3 2 := by linear_combination e12
  have E2 : M 0 0 * b' = b * M 2 2 + c * M 3 2 := by linear_combination e02
  have hS : M 0 0 * M 3 2 + M 1 0 * M 2 2 = 0 := by
    rw [h20, h30] at j02
    linear_combination j02
  have key : c * (M 1 0 * M 3 2) = 0 := by
    linear_combination M 0 0 * E1 - M 1 0 * E2 + b * hS - b * M 1 0 * M 2 2 * htwo
  have hprod : M 1 0 * M 3 2 = 0 := (mul_eq_zero.mp key).resolve_left hc
  have h10 : M 1 0 = 0 := by
    have h3 : M 1 0 * M 1 0 * b' = 0 := by linear_combination M 1 0 * E1 + b * hprod
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hb')
  have h32 : M 3 2 = 0 := by
    have h3 : b * M 3 2 = 0 := by rw [← E1, h10, zero_mul]
    exact (mul_eq_zero.mp h3).resolve_left hb
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij
  exacts [h10, h20, h21, h30, h31, h32]

variable [Finite k]

theorem exists_isUpper_of_le_subfieldSz {W : Subgroup (antiSp k)}
    (hWZ : W ≤ antiUnipotentCenter k) {F₀ : Subfield k} {a : ℕ}
    (hcard : Nat.card F₀ = 2 ^ (2 * a + 1)) {x : antiSp k}
    (hW : W ≤ (subfieldSz F₀ a).map (MulAut.conj x).toMonoidHom) {β γ : k} (hβ : β ≠ 0)
    (hγ : γ ≠ 0) (hz : uElt 0 β γ 0 ∈ W) :
    ∃ d : antiSp k, IsUpper d ∧ W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι := szEmb F₀ a hcard (x * wLong) with hιdef
  have hι : Function.Injective ι := szEmb_injective hcard
  set incl := Subgroup.inclusion (suzukiGroup_le_antiSp F₀ a hcard) with hincl
  have hιg : ∀ g, ι g = x * subAntiSp F₀ (incl g) * x⁻¹ := by
    intro g
    rw [hιdef, szEmb_apply]
    calc x * wLong * (wLong * subAntiSp F₀ (incl g) * wLong) * (x * wLong)⁻¹
        = x * (wLong * wLong) * subAntiSp F₀ (incl g) * (wLong * wLong⁻¹) * x⁻¹ := by group
      _ = x * subAntiSp F₀ (incl g) * x⁻¹ := by rw [wLong_mul_self, mul_inv_cancel]; group
  have hWr : W ≤ ι.range := by
    intro w hw
    obtain ⟨_, ⟨g, hg, rfl⟩, rfl⟩ := hW hw
    exact ⟨⟨(g : GL (Fin 4) ↥F₀), hg⟩, by rw [hιg]; rfl⟩
  set E := W.comap ι with hE
  have hE2 : IsPGroup 2 E := by
    intro e
    refine ⟨1, Subtype.ext (hι ?_)⟩
    obtain ⟨b, c, hbc⟩ := hWZ (show ι (e : ↥(suzukiGroup a ↥F₀)) ∈ W from e.2)
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, map_pow, hbc, pow_two,
      uElt_center_mul_self, map_one]
  obtain ⟨S₀, hS₀⟩ := CFSG.ShultStronglyClosedTI.SuzukiModel.exists_sylow_eq_suzukiU hcard
  obtain ⟨P, hEP⟩ := hE2.exists_le_sylow
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq ↥(suzukiGroup a ↥F₀) S₀ P
  set d := ι s * (x * wLong) with hd
  have hmem : ∀ e ∈ E, ∃ v : ↥F₀, ι e = d * uElt 0 (v : k) ((v : k) ^ 2 ^ (a + 1)) 0 * d⁻¹ := by
    intro e he
    have heP : e ∈ (P : Subgroup ↥(suzukiGroup a ↥F₀)) := hEP he
    rw [← hs, Sylow.coe_subgroup_smul, hS₀, Subgroup.mem_smul_pointwise_iff_exists] at heP
    obtain ⟨u, hu, rfl⟩ := heP
    have hsq : u ^ 2 = 1 := by
      have h1 : ι (MulAut.conj s • u) ∈ W := he
      obtain ⟨b, c, hbc⟩ := hWZ h1
      have h2 : ι ((MulAut.conj s • u) ^ 2) = 1 := by
        rw [map_pow, hbc, pow_two, uElt_center_mul_self]
      have h3 : (MulAut.conj s • u) ^ 2 = 1 := hι (h2.trans (map_one ι).symm)
      rw [MulAut.smul_def, MulAut.conj_apply] at h3
      have h4 : s * u ^ 2 * s⁻¹ = 1 := by rw [← conj_pow]; exact h3
      have h5 : u ^ 2 = s⁻¹ * (s * u ^ 2 * s⁻¹) * s := by group
      rw [h5, h4]
      group
    have hZ := (CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one
      hcard).mpr ⟨hu, hsq⟩
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hcard).mp hZ
    refine ⟨v, ?_⟩
    have hS : ι (suzukiSElt a ↥F₀ 0 v) = (x * wLong) *
        uElt 0 (v : k) ((v : k) ^ 2 ^ (a + 1)) 0 * (x * wLong)⁻¹ := by
      rw [hιdef, szEmb_apply, wLong_conj_suzukiS_zero hcard]
    rw [MulAut.smul_def, MulAut.conj_apply, map_mul, map_mul, map_inv, hS, hd]
    group
  refine ⟨d, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hWr hz
    have heE : e ∈ E := by
      change ι e ∈ W
      rw [he]
      exact hz
    obtain ⟨v, hv⟩ := hmem e heE
    have hv0 : (v : k) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (pow_ne_zero _ two_ne_zero), uElt_zero_eq_one, mul_one,
        mul_inv_cancel] at hv
      rw [hv, ← uElt_zero_eq_one] at he
      exact hβ (uElt_inj he).2.1.symm
    exact isUpper_of_conj_center hβ hγ hv0 (hv.symm.trans he)
  · intro w hw
    obtain ⟨e, rfl⟩ := hWr hw
    obtain ⟨v, hv⟩ := hmem e hw
    exact ⟨_, ⟨(v : k), v.2, rfl⟩, by rw [hv]; rfl⟩

end CFSG.Quasithin.Ch3E213M.P6B

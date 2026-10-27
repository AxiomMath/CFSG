module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelS
public import CFSG.LargeExtraspecial.S45QLin

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def E01 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 0]
@[expose] def E02 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 0, 0, 0; 1, 0, 0]
@[expose] def E12 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 0; 0, 0, 1; 0, 1, 0]

@[expose] def P12 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
@[expose] def P02 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem P12_conj : P12 * E01 * Matrix.transpose P12 = E02 := by decide +kernel
theorem P02_conj : P02 * E01 * Matrix.transpose P02 = E12 := by decide +kernel
theorem P12_mul : P12 * Matrix.transpose P12 = 1 := by decide +kernel
theorem P02_mul : P02 * Matrix.transpose P02 = 1 := by decide +kernel
theorem transpose_P12_mul : Matrix.transpose P12 * P12 = 1 := by decide +kernel
theorem transpose_P02_mul : Matrix.transpose P02 * P02 = 1 := by decide +kernel

theorem orbit_E01 : ∀ C : Matrix (Fin 3) (Fin 3) (ZMod 2), IsAlt C → C ≠ 0 →
    ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det ≠ 0 ∧ A * C * Matrix.transpose A = E01 := by
  decide +kernel

theorem alt_combo : ∀ D : Matrix (Fin 3) (Fin 3) (ZMod 2), IsAlt D →
    ∃ a b c : ZMod 2, D = a • E01 + b • E02 + c • E12 := by
  decide +kernel

theorem gA_zero : gA (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 :=
  LinearEquiv.ext fun v => by
  show gfun 0 v = v
  unfold gfun
  rw [Matrix.zero_mulVec, add_zero, mkV_xp_yp]

theorem gA_mul (C D : Matrix (Fin 3) (Fin 3) (ZMod 2)) : gA C * gA D = gA (C + D) :=
  LinearEquiv.ext fun v => by
    show gfun C (gfun D v) = gfun (C + D) v
    funext k
    cases k with
    | inl i =>
      simp only [gfun_inl, yp_gfun, Matrix.add_mulVec, Pi.add_apply]
      ring
    | inr i => simp only [gfun_inr]

theorem LA_gA_LA_inv (u : GL3) (C : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    LA u * gA C * (LA u)⁻¹ =
      gA ((u : Matrix (Fin 3) (Fin 3) (ZMod 2)) * C * Matrix.transpose (u : Matrix _ _ _)) :=
  LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    show LAfun u (gfun C (LAfun u⁻¹ v)) = gfun _ v
    exact LAfun_gfun_LAfun_inv u C v

theorem gA_fix_Sm (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) (hv : v ∈ Sm) : gA B v = v := by
  have hyv : yp v = 0 := (mem_Sm_iff_yp v).1 hv
  have e : mkV (xp v) (yp v) = v := mkV_xp_yp v
  rw [hyv] at e
  rw [← e, gA_mkV_zero]

theorem gA_injective {B B' : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : gA B = gA B') : B = B' := by
  apply mat_eq_of_mulVec_ex
  intro j
  have e : gA B (mkV 0 (ex j)) = gA B' (mkV 0 (ex j)) := by rw [h]
  rw [gA_mkV_zero_ex, gA_mkV_zero_ex] at e
  have := congrArg xp e
  simpa using this

theorem conj_mem_Omega {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) {γ n : VM ≃ₗ[ZMod 2] VM} (hγ : γ ∈ GM) (hn : n ∈ Ω) :
    γ * n * γ⁻¹ ∈ Ω := by
  have hidx : (Ω.subgroupOf GM).index = 2 := hrel
  haveI : (Ω.subgroupOf GM).Normal := Subgroup.normal_of_index_eq_two hidx
  have hn' : (⟨n, hΩG hn⟩ : GM) ∈ Ω.subgroupOf GM := Subgroup.mem_subgroupOf.2 hn
  have h := Subgroup.Normal.conj_mem inferInstance _ hn' ⟨γ, hγ⟩
  exact Subgroup.mem_subgroupOf.1 h

@[expose] def LAhom : GL3 →* (VM ≃ₗ[ZMod 2] VM) where
  toFun := LA
  map_one' := LA_one
  map_mul' := LA_mul

theorem LA_mem_Omega {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) (u : GL3) : LA u ∈ Ω := by
  haveI : IsSimpleGroup GL3 := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two (by norm_num)
  have hidx : (Ω.subgroupOf GM).index = 2 := hrel
  let LAG : GL3 →* GM := LAhom.codRestrict GM (fun u => LA_mem_GM u)
  let K : Subgroup GL3 := (Ω.subgroupOf GM).comap LAG
  have hK : K.index ≤ 2 := by
    have h1 : (Ω.subgroupOf GM).relIndex LAG.range ≤ (Ω.subgroupOf GM).relIndex ⊤ :=
      Subgroup.relIndex_le_of_le_right le_top (by rw [Subgroup.relIndex_top_right, hidx]; norm_num)
    rw [Subgroup.relIndex_top_right, hidx] at h1
    rw [Subgroup.index_comap]
    exact h1
  have hK_top : K = ⊤ := by
    by_contra hne
    have h2 : K.index = 2 := by
      have h1 : K.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
      have h0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    haveI : K.Normal := Subgroup.normal_of_index_eq_two h2
    rcases Subgroup.Normal.eq_bot_or_eq_top K with h | h
    · rw [h, Subgroup.index_bot, card_GL3] at h2
      norm_num at h2
    · exact hne h
  have hu : u ∈ K := by
    rw [hK_top]
    exact Subgroup.mem_top u
  have h3 : (LAG u : VM ≃ₗ[ZMod 2] VM) ∈ Ω := Subgroup.mem_subgroupOf.1 hu
  exact h3

@[expose] def K0 : Subgroup (VM ≃ₗ[ZMod 2] VM) where
  carrier := {g | g ∈ GM ∧ ∀ v ∈ Sm, g v = v}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v hv => by
    show a (b v) = v
    rw [hb.2 v hv, ha.2 v hv]⟩
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v hv => by
    show a.symm v = v
    rw [LinearEquiv.symm_apply_eq]
    exact (ha.2 v hv).symm⟩

theorem K0_le_GM : K0 ≤ GM := fun _ hg => hg.1

theorem mem_Sm_mkV_zero (x : Fin 3 → ZMod 2) : mkV x 0 ∈ Sm := (mem_Sm_iff_yp _).2 (yp_mkV_zero x)

theorem card_K0 : Nat.card K0 = 8 := by
  let f : {B : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsAlt B} → K0 := fun B =>
    ⟨gA B.1, gA_mem_GM B.2, fun v hv => gA_fix_Sm B.1 v hv⟩
  have hf : Function.Bijective f := by
    constructor
    · intro B B' h
      exact Subtype.ext (gA_injective (congrArg (fun g : K0 => (g : VM ≃ₗ[ZMod 2] VM)) h))
    · rintro ⟨g, hgG, hgfix⟩
      obtain ⟨B, hB, hBeq⟩ := GM_fix_Sm hgG (fun x => hgfix (mkV x 0) (mem_Sm_mkV_zero x))
      exact ⟨⟨B, hB⟩, Subtype.ext hBeq.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), card_alt]

theorem gA_add_mem {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} {C D : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hC : gA C ∈ Ω) (hD : gA D ∈ Ω) : gA (C + D) ∈ Ω := by
  rw [← gA_mul]
  exact Subgroup.mul_mem _ hC hD

theorem gA_mem_Omega {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : IsAlt B) :
    gA B ∈ Ω := by
  have hcount : Ω.relIndex K0 * Nat.card (Ω ⊓ K0 : Subgroup _) = Nat.card K0 :=
    Subgroup.relIndex_mul_card Ω K0
  have hrelK : Ω.relIndex K0 ≤ Ω.relIndex GM :=
    Subgroup.relIndex_le_of_le_right K0_le_GM (by rw [hrel]; norm_num)
  rw [hrel] at hrelK
  rw [card_K0] at hcount
  have hr : Ω.relIndex K0 = 1 ∨ Ω.relIndex K0 = 2 := by
    have h0 : Ω.relIndex K0 ≠ 0 := by
      intro h
      rw [h, zero_mul] at hcount
      norm_num at hcount
    omega
  have hcard : 1 < Nat.card (Ω ⊓ K0 : Subgroup _) := by
    rcases hr with h | h <;> rw [h] at hcount <;> omega
  haveI : Finite ↥(Ω ⊓ K0 : Subgroup _) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial ↥(Ω ⊓ K0 : Subgroup _) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥(Ω ⊓ K0 : Subgroup _))
  obtain ⟨hgΩ, hgK0⟩ := Subgroup.mem_inf.1 g.2
  have hg1 : (g : VM ≃ₗ[ZMod 2] VM) ≠ 1 := fun h => hg (Subtype.ext h)
  obtain ⟨C, hCalt, hCeq⟩ := GM_fix_Sm hgK0.1 (fun x => hgK0.2 (mkV x 0) (mem_Sm_mkV_zero x))
  have hC0 : C ≠ 0 := by
    intro h0
    apply hg1
    rw [hCeq, h0, gA_zero]
  have hgC : gA C ∈ Ω := hCeq ▸ hgΩ
  obtain ⟨A, hdet, hAC⟩ := orbit_E01 C hCalt hC0
  have hAunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet)
  let uA : GL3 := hAunit.unit
  have huA : (uA : Matrix (Fin 3) (Fin 3) (ZMod 2)) = A := hAunit.unit_spec
  have hE01 : gA E01 ∈ Ω := by
    have h1 : gA E01 = LA uA * gA C * (LA uA)⁻¹ := by
      rw [LA_gA_LA_inv, huA, hAC]
    rw [h1]
    exact conj_mem_Omega hΩG hrel (LA_mem_GM uA) hgC
  let uP12 : GL3 := ⟨P12, Matrix.transpose P12, P12_mul, transpose_P12_mul⟩
  let uP02 : GL3 := ⟨P02, Matrix.transpose P02, P02_mul, transpose_P02_mul⟩
  have hE02 : gA E02 ∈ Ω := by
    have h1 : gA E02 = LA uP12 * gA E01 * (LA uP12)⁻¹ := by
      rw [LA_gA_LA_inv]
      have : (uP12 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = P12 := rfl
      rw [this, P12_conj]
    rw [h1]
    exact conj_mem_Omega hΩG hrel (LA_mem_GM uP12) hE01
  have hE12 : gA E12 ∈ Ω := by
    have h1 : gA E12 = LA uP02 * gA E01 * (LA uP02)⁻¹ := by
      rw [LA_gA_LA_inv]
      have : (uP02 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = P02 := rfl
      rw [this, P02_conj]
    rw [h1]
    exact conj_mem_Omega hΩG hrel (LA_mem_GM uP02) hE01
  obtain ⟨a, b, c, hcomb⟩ := alt_combo B hB
  rw [hcomb]
  have h0 : gA 0 ∈ Ω := by
    rw [gA_zero]
    exact Subgroup.one_mem _
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c with rfl | rfl <;>
    simp only [zero_smul, one_smul, zero_add, add_zero]
  · exact h0
  · exact hE12
  · exact hE02
  · exact gA_add_mem hE02 hE12
  · exact hE01
  · exact gA_add_mem hE01 hE12
  · exact gA_add_mem hE01 hE02
  · exact gA_add_mem (gA_add_mem hE01 hE02) hE12

theorem stab_le_Omega {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) {γ : VM ≃ₗ[ZMod 2] VM} (hγ : γ ∈ GM) (hS : γ ∈ stabM Sm) :
    γ ∈ Ω := by
  obtain ⟨u, B, hB, hEq⟩ := stab_decomp hγ hS
  rw [hEq]
  exact Subgroup.mul_mem _ (LA_mem_Omega hΩG hrel u) (gA_mem_Omega hΩG hrel hB)

end CFSG.Quasithin.H13.C1294.Model

end

module

public import CFSG.Quasithin.H13.L32NG5Model
public import CFSG.Quasithin.H13.L32NLem144Bb

public section

namespace CFSG.Quasithin.H13.L14410

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert S8Cert G5Cert L1442M L14411 L144B

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

omit [Finite G] in
theorem form5 (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    {b₁ : Bool} (hiso : IsModelIso D (l32nH T V) e (q5 true) (g5 b₁ true)) (x y : D.V) :
    D.B x y = b5V (e x) (e y) := by
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact hext.2.2.2
  have hq : ∀ u ∈ fsuU T V, quadOf q5n (e (D.π u)) = 0 ↔ u * u = 1 := hiso.quad
  exact form_of_quadOf D e hZ2 (L1444.comm_mem_centerOf hext) hq x y

omit [Finite G] in
theorem card_V (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : Nat.card D.V = 256 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem card_hatE_sq_of_base (C : Base G T L V V₂ g) (D : HatModelU (fsuU T V))
    (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : Nat.card ↥(D.hat (l32nE T V V₂ g)) ^ 2 ≤ 256 := by
  have hEU : l32nE T V V₂ g ≤ fsuU T V := inf_le_left.trans inf_le_left
  have hEc : ∀ x ∈ l32nE T V V₂ g, ∀ y ∈ l32nE T V V₂ g, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (C.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [← card_V e]
  exact card_sq_le_of_isotropic D.nondegenerate (D.isotropic_hat hEU hEc)

omit [Finite G] in
theorem card_map_hat (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
    Nat.card ↥((D.hat (l32nE T V V₂ g)).map e.toLinearMap) =
      Nat.card ↥(D.hat (l32nE T V V₂ g)) :=
  Nat.card_congr ((Submodule.equivMapOfInjective e.toLinearMap e.injective _).toEquiv.symm)


theorem relIndex_PA : PA.relIndex (g5 false true) = 45 := by
  have h := Subgroup.relIndex_mul_card PA (g5 false true)
  rw [inf_eq_left.mpr PA_le_gA, card_PA, card_gA] at h
  omega

theorem false_of_A5 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11) (h12812 : Lemma12_8_12_two)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) {e₀ : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (hiso : IsModelIso D (l32nH T V) e₀ (q5 true) (g5 false true))
    (hW8 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3) : False := by
  have B := exists_base h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP hgH
  have himgH := img8_eq_of_iso hiso
  have hT8 := B.card_imgT e₀ himgH (m := 3) (k := 45) (by rw [card_gA]; norm_num) (by decide)
  obtain ⟨e, himgH', hform, himgT⟩ := B.exists_normalized e₀ himgH (form5 hext hiso)
    PA_le_gA (IsPGroup.of_card (n := 3) (by rw [card_PA]; norm_num)) (by rw [relIndex_PA]; decide)
    (by rw [hT8, card_PA]; norm_num)
  obtain ⟨a, ha, haV⟩ := B.abs.exists_mem_not_mem
  have hfix : ∀ γ ∈ PA, (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) :=
    fun γ hγ => B.T_fix e ha haV (by rw [himgT]; exact hγ)
  have hv4 := code_lt_of_fixed_PA _ hfix
  have hevec : vec8 (code8 (e (D.π a))) = e (D.π a) := vec8_code8 _
  have hv0 : code8 (e (D.π a)) ≠ 0 := fun h0 => B.pi_a_ne D ha haV
    ((map_eq_zero_iff e e.injective).mp (by rw [← hevec, h0, vec8_zero]))
  have hvmem : code8 (e (D.π a)) ∈ [1, 2, 3] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hWle : img8 D e (CFSG.conjugate (l32nW T V V₂) g) ≤ PA := fun x hx =>
    mem_PA_of_fix (himgH' ▸ img8_mono D e B.WgH hx) hvmem (by rw [hevec]; exact B.Wg_fix e ha hx)
  have hWeq : img8 D e (CFSG.conjugate (l32nW T V V₂) g) = PA :=
    Subgroup.eq_of_le_of_card_ge hWle (by rw [card_PA, card_img8, hW8]; norm_num)
  have hW : ∀ p ∈ eWA (code8 (e (D.π a))), vec8 (mv8 p.1 p.2 ^^^ p.2) ∈
      (D.hat (l32nE T V V₂ g)).map e.toLinearMap := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := (wB_spec.2 _ hvmem).1 p hp
    obtain ⟨w₀, hw₀⟩ := mem_elemsOf hp1
    obtain ⟨x, hxP, hx⟩ := exists_evalW pAG (subB_spec pB_spec.2.2.2.2.1).2.2.2.2
      (unit_of_gAE pB_spec.2.2.2.2.2.1) w₀
    have hxW : x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
      rw [hWeq]
      exact hxP
    have hB : D.B (e.symm (vec8 p.2)) (D.π a) = 0 := by
      rw [hform, LinearEquiv.apply_symm_apply, ← hevec, ← b5N_spec, hp2]
      rfl
    have := B.mulVec_add_mem_hatE e ha haV hxW hB
    rwa [hx, dec8_mulVec, ← hw₀, ← vec8_xor] at this
  have h32 := card_le_of_eSpanA hvmem _ hW
  rw [card_map_hat] at h32
  have hsq := card_hatE_sq_of_base B D e
  nlinarith

end CFSG.Quasithin.H13.L14410

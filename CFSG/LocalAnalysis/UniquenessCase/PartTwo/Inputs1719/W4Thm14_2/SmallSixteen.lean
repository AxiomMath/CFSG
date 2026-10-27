module

public import CFSG.Quasithin.Background.H47WW16
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KGMPf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open scoped MatrixGroups Matrix

private theorem nat_card_ker_le_of_normalizes
    {T : Matrix (Fin 16) (Fin 16) (ZMod 2)} (hT2 : T * T = 1) (hT1 : T ≠ 1)
    (hN : ∀ g : SL(3, CFSG.Fischer.F4),
      ∃ h, T * CFSG.Quasithin.H13.Ch9.L34B.R16 g = CFSG.Quasithin.H13.Ch9.L34B.R16 h * T) :
    Nat.card ↥(LinearMap.ker (Matrix.toLin' (T - 1))) ≤ 2 ^ 10 := by
  let t : MulAut (CFSG.Quasithin.H.Mathieu.Wn 16) :=
    { toFun := fun w => Multiplicative.ofAdd (T.mulVec (Multiplicative.toAdd w))
      invFun := fun w => Multiplicative.ofAdd (T.mulVec (Multiplicative.toAdd w))
      left_inv := fun w => by
        show Multiplicative.ofAdd (T.mulVec (T.mulVec (Multiplicative.toAdd w))) = w
        rw [Matrix.mulVec_mulVec, hT2, Matrix.one_mulVec]
        exact ofAdd_toAdd w
      right_inv := fun w => by
        show Multiplicative.ofAdd (T.mulVec (T.mulVec (Multiplicative.toAdd w))) = w
        rw [Matrix.mulVec_mulVec, hT2, Matrix.one_mulVec]
        exact ofAdd_toAdd w
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (T.mulVec (Multiplicative.toAdd (x * y))) =
          Multiplicative.ofAdd (T.mulVec (Multiplicative.toAdd x)) *
            Multiplicative.ofAdd (T.mulVec (Multiplicative.toAdd y))
        rw [toAdd_mul, Matrix.mulVec_add, ofAdd_add] }
  have ht_apply : ∀ w : CFSG.Quasithin.H.Mathieu.Wn 16,
      t w = Multiplicative.ofAdd (T.mulVec (Multiplicative.toAdd w)) := fun w => rfl
  have haut : CFSG.Quasithin.L34Bin.autMat t = T := by
    apply Matrix.mulVec_injective
    funext v
    simp only [CFSG.Quasithin.L34Bin.autMat_mulVec, ht_apply, toAdd_ofAdd]
  have htt : t * t = 1 := by
    apply CFSG.Quasithin.L34Bin.autMat_injective
    rw [map_mul, haut, hT2, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    apply hT1
    rw [← haut, h, map_one]
  have hR : ∀ g : SL(3, CFSG.Fischer.F4),
      CFSG.Quasithin.L34Bin.autMat
        (CFSG.Quasithin.H13.Ch9.L34N.slRep CFSG.Quasithin.H13.Ch9.L34M.rho16GL g) =
        CFSG.Quasithin.H13.Ch9.L34B.R16 g := fun g => rfl
  have hconj : ∀ x ∈ CFSG.Quasithin.H13.Ch9.L34N.img16, t * x * t⁻¹ ∈
      CFSG.Quasithin.H13.Ch9.L34N.img16 := by
    intro x hx
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨h, hh⟩ := hN g
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [htinv]
    exact ⟨h, by
      apply CFSG.Quasithin.L34Bin.autMat_injective
      rw [map_mul, map_mul, haut, hR h, hR g, hh, Matrix.mul_assoc, hT2, Matrix.mul_one]⟩
  have hNt : t ∈ Subgroup.normalizer
      (CFSG.Quasithin.H13.Ch9.L34N.img16 :
        Set (MulAut (CFSG.Quasithin.H.Mathieu.Wn 16))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · exact hconj s
    · intro hs
      obtain ⟨h, hh⟩ := hs
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      have hseq : s =
          t * CFSG.Quasithin.H13.Ch9.L34N.slRep CFSG.Quasithin.H13.Ch9.L34M.rho16GL h *
            t⁻¹ := by
        rw [hh, htinv]
        calc s = (t * t) * s * (t * t) := by rw [htt]; group
          _ = t * (t * s * t) * t := by group
      rw [hseq]
      exact hconj _ ⟨h, rfl⟩
  have hfix := CFSG.Quasithin.H47W.rk_fixV_w16_le (t := t) htt ht1 hNt
  let F : ↥(CFSG.Quasithin.fixV (Subgroup.zpowers t)) ≃
      ↥(LinearMap.ker (Matrix.toLin' (T - 1))) :=
    { toFun := fun w =>
        ⟨Multiplicative.toAdd (w : CFSG.Quasithin.H.Mathieu.Wn 16), by
          rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
            sub_eq_zero]
          have hw := CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp w.2
          exact Multiplicative.ofAdd.injective (by
            rw [ofAdd_toAdd]
            exact (ht_apply (w : CFSG.Quasithin.H.Mathieu.Wn 16)).symm.trans hw)⟩
      invFun := fun v =>
        ⟨Multiplicative.ofAdd (v : Fin 16 → ZMod 2), by
          refine (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).mpr ?_
          have hv : T.mulVec (v : Fin 16 → ZMod 2) = (v : Fin 16 → ZMod 2) := by
            have h := v.2
            rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
              sub_eq_zero] at h
            exact h
          exact (ht_apply (Multiplicative.ofAdd (v : Fin 16 → ZMod 2))).trans (by
            rw [toAdd_ofAdd, hv])⟩
      left_inv := fun w => Subtype.ext (ofAdd_toAdd (w : CFSG.Quasithin.H.Mathieu.Wn 16))
      right_inv := fun v => Subtype.ext (toAdd_ofAdd (v : Fin 16 → ZMod 2)) }
  have hcard := Nat.card_congr F
  have h1 := CFSG.Quasithin.card_eq_two_pow (V := CFSG.Quasithin.H.Mathieu.Wn 16)
    CFSG.Quasithin.H47W.sq_eq_one_Wn16 (CFSG.Quasithin.fixV (Subgroup.zpowers t))
  calc Nat.card ↥(LinearMap.ker (Matrix.toLin' (T - 1)))
      = Nat.card ↥(CFSG.Quasithin.fixV (Subgroup.zpowers t)) := hcard.symm
    _ = 2 ^ CFSG.Quasithin.rk ↥(CFSG.Quasithin.fixV (Subgroup.zpowers t)) := h1
    _ ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hfix

section Rep
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

theorem five_le_rank_of_finrank_sixteen
    (hF : Fintype.card F = 2 ^ 2) (ρ : Representation (ZMod 2) SL(3, F) U)
    (hirr : ρ.IsIrreducible) (hz : ∀ x ∈ LinearFlag.scalars 3 F, ρ x = 1)
    (hdim : Module.finrank (ZMod 2) U = 16) (a : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (haN : ∀ x : SL(3, F), ∃ y, X7a.Intertwines ρ a x y) :
    5 ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  let φ : F ≃+* CFSG.Fischer.F4 :=
    FiniteField.ringEquivOfCardEq (by rw [hF, CFSG.Quasithin.L34Bin.card_F4])
  let φSL : SL(3, F) ≃* SL(3, CFSG.Fischer.F4) :=
    { toFun := Matrix.SpecialLinearGroup.map φ.toRingHom
      invFun := Matrix.SpecialLinearGroup.map φ.symm.toRingHom
      left_inv := by
        intro A
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      right_inv := by
        intro A
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      map_mul' := by intro A B; exact map_mul _ A B }
  let ρF4 : Representation (ZMod 2) SL(3, CFSG.Fischer.F4) U := ρ.comp φSL.symm.toMonoidHom
  let e : U ≃ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
    LinearEquiv.ofFinrankEq U (Fin 16 → ZMod 2) (by rw [hdim, Module.finrank_fin_fun])
  let ρ₁ : Representation (ZMod 2) SL(3, CFSG.Fischer.F4) (Fin 16 → ZMod 2) :=
    { toFun := fun g => e.toLinearMap ∘ₗ ρF4 g ∘ₗ e.symm.toLinearMap
      map_one' := by
        ext v
        simp only [LinearMap.coe_comp, Function.comp_apply, map_one, Module.End.one_apply,
          LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
      map_mul' := by
        intro g h
        ext v
        simp only [LinearMap.coe_comp, Function.comp_apply, map_mul, Module.End.mul_apply,
          LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
          LinearEquiv.symm_apply_apply] }
  let ρ₀ : SL(3, CFSG.Fischer.F4) →* Matrix (Fin 16) (Fin 16) (ZMod 2) :=
    { toFun := fun g => LinearMap.toMatrix' (ρ₁ g)
      map_one' := by
        rw [map_one ρ₁]
        exact LinearMap.toMatrix'_id
      map_mul' := by
        intro g h
        rw [map_mul ρ₁]
        exact LinearMap.toMatrix'_comp _ _ }
  have hn : 0 < 16 := by norm_num
  have hirr₀ : ∀ N : Submodule (ZMod 2) (Fin 16 → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    let N' : Submodule (ZMod 2) U := N.comap e.toLinearMap
    have hN' : ∀ g : SL(3, F), ∀ u ∈ N', ρ g u ∈ N' := by
      intro g u hu
      have hx : (ρ₀ (φSL g)).mulVec (e u) ∈ N := hN (φSL g) (e u) hu
      have h_eq : (ρ₀ (φSL g)).mulVec (e u) = e (ρ g u) := by
        change (LinearMap.toMatrix' (ρ₁ (φSL g))).mulVec (e u) = e (ρ g u)
        rw [LinearMap.toMatrix'_mulVec]
        simp [ρ₁, ρF4, LinearEquiv.symm_apply_apply]
      rw [h_eq] at hx
      exact hx
    have h := (X7.isIrreducible_iff ρ).mp hirr
    rcases h.2 N' hN' with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv' : e.symm v ∈ N' := by
        rw [Submodule.mem_comap]
        simpa using hv
      rw [hbot, Submodule.mem_bot] at hv'
      calc v = e (e.symm v) := (LinearEquiv.apply_symm_apply e v).symm
        _ = e 0 := by rw [hv']
        _ = 0 := map_zero e
    · right
      rw [eq_top_iff]
      intro v _
      have hv' : e.symm v ∈ N' := by
        rw [htop]
        exact Submodule.mem_top
      rw [Submodule.mem_comap] at hv'
      change e (e.symm v) ∈ N at hv'
      rwa [LinearEquiv.apply_symm_apply e v] at hv'
  have hZ₀ : ρ₀ CFSG.Quasithin.L34Bin.zSL = 1 := by
    have hcenter : CFSG.Quasithin.L34Bin.zSL ∈ Subgroup.center (SL(3, CFSG.Fischer.F4)) :=
      CFSG.Quasithin.H13.Ch9.L34B.zSL_mem_center
    have hcenter_F : φSL.symm CFSG.Quasithin.L34Bin.zSL ∈ Subgroup.center (SL(3, F)) := by
      rw [Subgroup.mem_center_iff] at hcenter ⊢
      intro g
      apply φSL.injective
      simpa using hcenter (φSL g)
    have hscalar_F : φSL.symm CFSG.Quasithin.L34Bin.zSL ∈ LinearFlag.scalars 3 F := by
      rw [LinearFlag.scalars_eq_center]
      exact hcenter_F
    have hρF4 : ρF4 CFSG.Quasithin.L34Bin.zSL = 1 := by
      change ρ (φSL.symm CFSG.Quasithin.L34Bin.zSL) = 1
      exact hz _ hscalar_F
    have hρ1 : ρ₁ CFSG.Quasithin.L34Bin.zSL = 1 := by
      apply LinearMap.ext
      intro v
      change e (ρF4 CFSG.Quasithin.L34Bin.zSL (e.symm v)) = v
      rw [hρF4]
      exact e.apply_symm_apply v
    change LinearMap.toMatrix' (ρ₁ CFSG.Quasithin.L34Bin.zSL) = 1
    rw [hρ1]
    exact LinearMap.toMatrix'_id
  have hnt₀ : ∃ g, ρ₀ g ≠ 1 :=
    CFSG.Quasithin.L34Bin.exists_ne_one_of_hirr ρ₀ (by norm_num) hirr₀
  rcases CFSG.Quasithin.H13.Ch9.L34B.classify ρ₀ hn hirr₀ hZ₀ hnt₀ with
    ⟨M, hM, hMint⟩ | ⟨M, hM, hMint⟩ | ⟨M, hM, hMint⟩ | ⟨M, hM, hMint⟩
  ·
    exfalso
    have hcard : Nat.card (Fin 16 → ZMod 2) = Nat.card (Fin 9 → ZMod 2) :=
      Nat.card_congr (Equiv.ofBijective M.mulVec hM)
    simp at hcard
  ·
    exfalso
    have hcard : Nat.card (Fin 16 → ZMod 2) = Nat.card (Fin 9 → ZMod 2) :=
      Nat.card_congr (Equiv.ofBijective M.mulVec hM)
    simp at hcard
  ·
    have hunit : IsUnit M := (Matrix.mulVec_injective_iff_isUnit).mp hM.1
    obtain ⟨N, hMN, hNM⟩ := isUnit_iff_exists.mp hunit
    obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Matrix (Fin 16) (Fin 16) (ZMod 2),
        ∀ v, A₀.mulVec v = e (a (e.symm v)) :=
      ⟨LinearMap.toMatrix' (e.toLinearMap ∘ₗ a.toLinearMap ∘ₗ e.symm.toLinearMap),
        fun v => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
    have hρ₀ : ∀ (g : SL(3, CFSG.Fischer.F4)) (v : Fin 16 → ZMod 2),
        (ρ₀ g).mulVec v = e (ρ (φSL.symm g) (e.symm v)) := by
      intro g v
      change (LinearMap.toMatrix' (ρ₁ g)).mulVec v = e (ρ (φSL.symm g) (e.symm v))
      rw [LinearMap.toMatrix'_mulVec]
      rfl
    have haa : ∀ u : U, a (a u) = u := by
      intro u
      have h := congrArg (fun f : U ≃ₗ[ZMod 2] U => f u) ha2
      simpa using h
    have hA₀sq : A₀ * A₀ = 1 := by
      apply Matrix.mulVec_injective
      funext v
      rw [← Matrix.mulVec_mulVec, hA₀, hA₀, LinearEquiv.symm_apply_apply, haa,
        LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
    have hT2 : (M * A₀ * N) * (M * A₀ * N) = 1 := by
      calc (M * A₀ * N) * (M * A₀ * N)
          = M * A₀ * (N * M) * A₀ * N := by simp only [Matrix.mul_assoc]
        _ = M * A₀ * 1 * A₀ * N := by rw [hNM]
        _ = M * (A₀ * A₀) * N := by simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = M * 1 * N := by rw [hA₀sq]
        _ = 1 := by rw [Matrix.mul_one, hMN]
    have hT1 : M * A₀ * N ≠ 1 := by
      intro hT
      have hA₁ : A₀ = 1 := by
        calc A₀ = (N * M) * A₀ * (N * M) := by rw [hNM]; simp
          _ = N * (M * A₀ * N) * M := by simp only [Matrix.mul_assoc]
          _ = N * 1 * M := by rw [hT]
          _ = 1 := by rw [Matrix.mul_one, hNM]
      have ha1' : a = 1 := by
        ext u
        have h := hA₀ (e u)
        rw [hA₁, Matrix.one_mulVec] at h
        simpa using (e.injective (by simpa using h)).symm
      exact ha1 ha1'
    have hA₀ρ : ∀ g : SL(3, CFSG.Fischer.F4), ∃ y : SL(3, F),
        A₀ * ρ₀ g = ρ₀ (φSL y) * A₀ := by
      intro g
      obtain ⟨y, hy⟩ := haN (φSL.symm g)
      refine ⟨y, ?_⟩
      apply Matrix.mulVec_injective
      funext v
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hρ₀ g v, hA₀]
      rw [hρ₀ (φSL y) (A₀.mulVec v), hA₀]
      rw [MulEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact congrArg e (hy (e.symm v))
    have hNR : ∀ g : SL(3, CFSG.Fischer.F4),
        N * CFSG.Quasithin.H13.Ch9.L34B.R16 g = ρ₀ g * N := by
      intro g
      have h1 : N * CFSG.Quasithin.H13.Ch9.L34B.R16 g * M = ρ₀ g := by
        calc N * CFSG.Quasithin.H13.Ch9.L34B.R16 g * M
            = N * (CFSG.Quasithin.H13.Ch9.L34B.R16 g * M) := by rw [Matrix.mul_assoc]
          _ = N * (M * ρ₀ g) := by rw [← hMint g]
          _ = (N * M) * ρ₀ g := by rw [Matrix.mul_assoc]
          _ = ρ₀ g := by rw [hNM, Matrix.one_mul]
      calc N * CFSG.Quasithin.H13.Ch9.L34B.R16 g
          = N * CFSG.Quasithin.H13.Ch9.L34B.R16 g * (M * N) := by rw [hMN, Matrix.mul_one]
        _ = (N * CFSG.Quasithin.H13.Ch9.L34B.R16 g * M) * N := by
            simp only [Matrix.mul_assoc]
        _ = ρ₀ g * N := by rw [h1]
    have hTnorm : ∀ g : SL(3, CFSG.Fischer.F4), ∃ h : SL(3, CFSG.Fischer.F4),
        (M * A₀ * N) * CFSG.Quasithin.H13.Ch9.L34B.R16 g =
          CFSG.Quasithin.H13.Ch9.L34B.R16 h * (M * A₀ * N) := by
      intro g
      obtain ⟨y, hy⟩ := hA₀ρ g
      refine ⟨φSL y, ?_⟩
      calc (M * A₀ * N) * CFSG.Quasithin.H13.Ch9.L34B.R16 g
          = M * A₀ * (N * CFSG.Quasithin.H13.Ch9.L34B.R16 g) := by
            simp only [Matrix.mul_assoc]
        _ = M * A₀ * (ρ₀ g * N) := by rw [hNR g]
        _ = M * (A₀ * ρ₀ g) * N := by simp only [Matrix.mul_assoc]
        _ = M * (ρ₀ (φSL y) * A₀) * N := by rw [hy]
        _ = (M * ρ₀ (φSL y)) * A₀ * N := by simp only [Matrix.mul_assoc]
        _ = (CFSG.Quasithin.H13.Ch9.L34B.R16 (φSL y) * M) * A₀ * N := by
            rw [← hMint (φSL y)]
        _ = CFSG.Quasithin.H13.Ch9.L34B.R16 (φSL y) * (M * A₀ * N) := by
            simp only [Matrix.mul_assoc]
    have hNcard : Nat.card ↥(LinearMap.ker (Matrix.toLin' ((M * A₀ * N) - 1))) ≤ 2 ^ 10 :=
      nat_card_ker_le_of_normalizes hT2 hT1 hTnorm
    have hMinj : Function.Injective M.mulVec := hM.1
    have hTid : ∀ x : Fin 16 → ZMod 2,
        ((M * A₀ * N) - 1).mulVec (M.mulVec x) = M.mulVec ((A₀ - 1).mulVec x) := by
      intro x
      calc ((M * A₀ * N) - 1).mulVec (M.mulVec x)
          = (M * A₀ * N).mulVec (M.mulVec x) - M.mulVec x := by
            rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        _ = M.mulVec (A₀.mulVec (N.mulVec (M.mulVec x))) - M.mulVec x := by
            simp only [← Matrix.mulVec_mulVec]
        _ = M.mulVec (A₀.mulVec x) - M.mulVec x := by
            have hx : N.mulVec (M.mulVec x) = x := by
              rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
            rw [hx]
        _ = M.mulVec (A₀.mulVec x - x) := by rw [← Matrix.mulVec_sub]
        _ = M.mulVec ((A₀ - 1).mulVec x) := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    let K : ↥(LinearMap.ker (a.toLinearMap - 1)) ≃
        ↥(LinearMap.ker (Matrix.toLin' ((M * A₀ * N) - 1))) :=
      { toFun := fun u =>
          ⟨M.mulVec (e (u : U)), by
            rw [LinearMap.mem_ker, Matrix.toLin'_apply, hTid]
            have hu : a (u : U) = u := by
              have h := u.2
              simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
                sub_eq_zero] at h
              exact h
            have hA : (A₀ - 1).mulVec (e (u : U)) = 0 := by
              rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA₀, LinearEquiv.symm_apply_apply, hu,
                sub_self]
            rw [hA, Matrix.mulVec_zero]⟩
        invFun := fun w =>
          ⟨e.symm (N.mulVec (w : Fin 16 → ZMod 2)), by
            rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
            have hw : ((M * A₀ * N) - 1).mulVec (w : Fin 16 → ZMod 2) = 0 := by
              have h := w.2
              rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at h
            have hMw : M.mulVec (N.mulVec (w : Fin 16 → ZMod 2)) = (w : Fin 16 → ZMod 2) := by
              rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
            have h0 : M.mulVec ((A₀ - 1).mulVec (N.mulVec (w : Fin 16 → ZMod 2))) = 0 := by
              rw [← hTid (N.mulVec w), hMw]
              exact hw
            have h1 : (A₀ - 1).mulVec (N.mulVec (w : Fin 16 → ZMod 2)) = 0 := by
              apply hMinj
              rw [h0, Matrix.mulVec_zero]
            rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
            have h2 : e (a (e.symm (N.mulVec (w : Fin 16 → ZMod 2))))
                = e (e.symm (N.mulVec (w : Fin 16 → ZMod 2))) := by
              rw [← hA₀ (N.mulVec w), h1, LinearEquiv.apply_symm_apply]
            exact e.injective h2⟩
        left_inv := fun u => Subtype.ext (by
          show e.symm (N.mulVec (M.mulVec (e (u : U)))) = (u : U)
          rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec, LinearEquiv.symm_apply_apply])
        right_inv := fun w => Subtype.ext (by
          show M.mulVec (e (e.symm (N.mulVec (w : Fin 16 → ZMod 2)))) = (w : Fin 16 → ZMod 2)
          rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]) }
    have hcardK : Nat.card ↥(LinearMap.ker (a.toLinearMap - 1))
        = Nat.card ↥(LinearMap.ker (Matrix.toLin' ((M * A₀ * N) - 1))) :=
      Nat.card_congr K
    have hpow : 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker (a.toLinearMap - 1))
        = Nat.card ↥(LinearMap.ker (a.toLinearMap - 1)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := ↥(LinearMap.ker (a.toLinearMap - 1)))]
      simp
    have hfinle : Module.finrank (ZMod 2) ↥(LinearMap.ker (a.toLinearMap - 1)) ≤ 10 := by
      apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      rw [hpow, hcardK]
      exact hNcard
    have hrn := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - 1)
    omega
  ·
    exfalso
    have hcard : Nat.card (Fin 16 → ZMod 2) = Nat.card (Fin 64 → ZMod 2) :=
      Nat.card_congr (Equiv.ofBijective M.mulVec hM)
    simp at hcard
end Rep

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

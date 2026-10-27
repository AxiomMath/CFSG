module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrKFrame
public import CFSG.LocalAnalysis.StandardType.GGA8NbrKAut
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordLift

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix
open Certificates.A8Nbr476

namespace CFSG.StandardType.A11

private lemma a11ah_fPow_add {Bs : Type} [Group Bs] [IsMulCommutative Bs]
    (g : Fin 4 → Bs) (horder : ∀ i, orderOf (g i) = 7) (v w : Fin 4 → ZMod 7) :
    fPow g (v + w) = fPow g v * fPow g w := by
  letI : CommMonoid Bs := { mul_comm := fun a b => mul_comm' a b }
  have hprod : ∀ x : Fin 4 → ZMod 7, fPow g x = ∏ i : Fin 4, g i ^ (x i).val := by
    intro x
    simp only [fPow, Fin.prod_univ_four]
  have key : ∀ i : Fin 4, g i ^ ((v + w) i).val = g i ^ (v i).val * g i ^ (w i).val := by
    intro i
    have h1 : g i ^ ((v + w) i).val = g i ^ ((v i).val + (w i).val) := by
      apply pow_eq_pow_iff_modEq.mpr
      rw [horder i, Pi.add_apply, ZMod.val_add]
      exact Nat.mod_modEq _ 7
    rw [h1, pow_add]
  rw [hprod (v + w), hprod v, hprod w, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => key i

private lemma a11ah_fPow_injective {Bs : Type} [Group Bs] [Finite Bs] [IsMulCommutative Bs]
    (g : Fin 4 → Bs) (horder : ∀ i, orderOf (g i) = 7)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hcard : Nat.card Bs = 7 ^ 4) :
    Function.Injective (fPow g) := by
  let φ : Multiplicative (Fin 4 → ZMod 7) →* Bs :=
    { toFun := fun v => fPow g (Multiplicative.toAdd v)
      map_one' := by simp [fPow]
      map_mul' := fun v w => by
        rw [toAdd_mul, a11ah_fPow_add g horder] }
  have hsingle : ∀ i : Fin 4, fPow g (Pi.single i 1) = g i := by
    intro i
    fin_cases i <;> simp [fPow, ZMod.val_one]
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd (Pi.single i 1), hsingle i⟩
  have hcarddom : Nat.card (Multiplicative (Fin 4 → ZMod 7)) = 7 ^ 4 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun]
    simp [ZMod.card]
  have hker : Nat.card φ.ker = 1 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hrange, Subgroup.card_top, hcard, hcarddom] at h
    omega
  have hinj : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff φ).mp (Subgroup.card_eq_one.mp hker)
  intro v w hvw
  have h : Multiplicative.ofAdd v = Multiplicative.ofAdd w := by
    apply hinj
    simpa [φ] using hvw
  exact Multiplicative.ofAdd.injective h

private lemma a11ah_iota_fPow {Bs : Type} [Group Bs]
    (g : Fin 4 → Bs) (ι : Additive Bs ≃+ (Fin 4 → ZMod 7)) (v : Fin 4 → ZMod 7) :
    ι (Additive.ofMul (fPow g v)) =
      v ᵥ* (Matrix.of fun i j => ι (Additive.ofMul (g i)) j) := by
  have hprod : fPow g v =
      g 0 ^ (v 0).val * g 1 ^ (v 1).val * g 2 ^ (v 2).val * g 3 ^ (v 3).val := by
    simp only [fPow]
  rw [hprod]
  simp only [ofMul_mul, ofMul_pow]
  simp only [map_add, map_nsmul]
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.vecMul, dotProduct,
    Matrix.of_apply]
  rw [Fin.sum_univ_four]
  simp only [← Nat.cast_smul_eq_nsmul (ZMod 7), ZMod.natCast_zmod_val, smul_eq_mul]

private lemma a11ah_mulAut_of_matrix {Bs : Type} [Group Bs]
    (N : M4) (hNdet : N.det ≠ 0) (ι : Additive Bs ≃+ (Fin 4 → ZMod 7)) :
    ∃ φ : Bs ≃* Bs, ∀ b : Bs,
      ι (Additive.ofMul (φ b)) = vecMul (ι (Additive.ofMul b)) N := by
  have hN : IsUnit N.det := isUnit_iff_ne_zero.mpr hNdet
  let L : (Fin 4 → ZMod 7) ≃+ (Fin 4 → ZMod 7) :=
    { toFun := fun v => vecMul v N
      invFun := fun v => vecMul v N⁻¹
      left_inv := fun v => by
        change v ᵥ* N ᵥ* N⁻¹ = v
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv N hN, Matrix.vecMul_one]
      right_inv := fun v => by
        change v ᵥ* N⁻¹ ᵥ* N = v
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul N hN, Matrix.vecMul_one]
      map_add' := fun v w => by rw [Matrix.add_vecMul] }
  let e : Additive Bs ≃+ Additive Bs := ι.trans (L.trans ι.symm)
  let φ : Bs ≃* Bs := (MulEquiv.toAdditive (G := Bs) (H := Bs)).symm e
  refine ⟨φ, fun b => ?_⟩
  have h1 : Additive.ofMul (φ b) = e (Additive.ofMul b) := rfl
  rw [h1]
  change ι (e (Additive.ofMul b)) = L (ι (Additive.ofMul b))
  rw [show e (Additive.ofMul b) = ι.symm (L (ι (Additive.ofMul b))) from rfl]
  exact ι.apply_symm_apply _

private lemma a11ah_ell_fPow {G : Type} [Group G] (f : Fin 4 → G) (c : ZMod 7) :
    ell f c = fPow f ![1, 1, 1, c] := by
  simp [ell, fPow, ZMod.val_one]

theorem a11A8HomolInput_holds
    : A11A8HomolInput := by
  intro hMp hLB G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb hKm c hline
  obtain ⟨hRest, hA11, hFrameSpec, hFrameExtra, hCoh, hRho⟩ := hctx
  have hcfg : GGConfig 7 B Bs x L D J := hRest.1
  have hinnAll : GGInnerDiagAll 7 B Bs x L D J := hRest.2.2.1
  have hI : GGThmIHyp 7 B x L := hcfg.1
  have hDJ : LargeEvenStdSub 7 B x L D J := hcfg.2.2
  have hBle : B ≤ Bs := hcfg.2.1.1
  have hEab : IsElemAbelian 7 Bs := hcfg.2.1.2.1
  haveI : IsMulCommutative ↥Bs := hEab.1
  have hmodL : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 := hA11.2.1
  have hglue : A11GlueHyp φ₃ f n := hFrameSpec.1
  have hbs : Subgroup.closure (Set.range f) = Bs := hFrameSpec.2.2.2.1
  have hfcomm : ∀ i j, f i * f j = f j * f i := hglue.2.2.1
  have hforder : ∀ i, orderOf (f i) = 7 := hglue.2.2.2.1
  have hfcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4 := hglue.2.2.2.2.1
  have h7J : 7 ∣ Nat.card J := hFrameExtra.1
  have hinn : GGInnerDiagOn Bs K' := hinnAll.2 y' K' hnb
  have hJK : J ≤ K' := le_of_ggNbr hLB hI hDJ h7J hnb
  have hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
    ggA8Nbr_bstar_inf_centralizer_J_le hMp hcfg hinnAll.1 hmodL hnb
  have hy' : y' ∈ Bs := hBle hnb.1.2.1
  obtain ⟨ρ', ι, hF⟩ := ggA8Nbr_kFrame hMp hcfg hnb hinn hKm hJK hCJ hy'
  have hKc := isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hnb)
  have hyK : ∀ k ∈ K', y' * k = k * y' := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKc.1.1 hk)).symm
  have hfi : ∀ i, f i ∈ Bs := by
    intro i
    rw [← hbs]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  let g : Fin 4 → ↥Bs := fun i => ⟨f i, hfi i⟩
  have hg_coe : ∀ v : Fin 4 → ZMod 7, (fPow (G := ↥Bs) g v : G) = fPow f v := by
    intro v
    simp only [fPow, g, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_mk]
  have horder_g : ∀ i, orderOf (g i) = 7 := fun i => by
    rw [Subgroup.orderOf_mk, hforder i]
  have hcardBs : Nat.card ↥Bs = 7 ^ 4 := by
    rw [← hbs, hfcard]
  have hgen_g : Subgroup.closure (Set.range g) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range g)).map (Subgroup.subtype Bs) =
        Subgroup.closure (Set.range f) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨g i, ⟨i, rfl⟩, rfl⟩
    apply eq_top_iff.mpr
    intro b _
    have hb : (b : G) ∈ (Subgroup.closure (Set.range g)).map (Subgroup.subtype Bs) := by
      rw [hmap, hbs]
      exact b.2
    obtain ⟨cc, hcc, hccb⟩ := Subgroup.mem_map.mp hb
    rwa [show cc = b from Subtype.ext hccb] at hcc
  have hfPow_inj_g : Function.Injective (fPow g) :=
    a11ah_fPow_injective g horder_g hgen_g hcardBs
  have hfPow_inj : Function.Injective (fPow f) := by
    intro v w hvw
    apply hfPow_inj_g
    apply Subtype.ext
    rw [hg_coe v, hg_coe w, hvw]
  let C : M4 := Matrix.of fun i j => ι (Additive.ofMul (g i)) j
  have hC : ∀ v : Fin 4 → ZMod 7, ι (Additive.ofMul (fPow g v)) = vecMul v C :=
    fun v => a11ah_iota_fPow g ι v
  have hCdet : IsUnit C.det := by
    have h1 : Function.Injective C.vecMul := by
      intro v w hvw
      have h : ι (Additive.ofMul (fPow g v)) = ι (Additive.ofMul (fPow g w)) := by
        rw [hC v, hC w]
        exact hvw
      exact hfPow_inj_g (ι.injective h)
    exact (Matrix.isUnit_iff_isUnit_det (A := C)).mp
      ((Matrix.vecMul_injective_iff_isUnit (A := C)).mp h1)
  have hCinv_mul : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hCdet
  have hmul_Cinv : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCdet
  let N : Fin 3 → M4 := fun i => a8MonK 1 (Pi.single i 1)
  have hNdet : ∀ i : Fin 3, (N i).det ≠ 0 := by decide +kernel
  have hNinj : Function.Injective N := by decide +kernel
  have hNpow : ∀ i : Fin 3, N i ^ 3 = 1 := by decide +kernel
  have hNrank : ∀ i : Fin 3, (N i - 1).rank = 1 := by
    intro i
    have hdiag : N i - 1 =
        Matrix.diagonal (Pi.single i.succ (1 : ZMod 7) : Fin 4 → ZMod 7) := by
      ext a b
      fin_cases i <;> fin_cases a <;> fin_cases b <;> decide +kernel
    rw [hdiag, Matrix.rank_diagonal]
    fin_cases i <;> decide +kernel
  have hExists : ∀ i : Fin 3,
      ∃ h ∈ K', h ∈ Subgroup.normalizer (Bs : Set G) ∧ ConjMat f h (C * N i * C⁻¹) := by
    intro i
    obtain ⟨φ, hφ⟩ := a11ah_mulAut_of_matrix (N i) (hNdet i) ι
    have hmem : φ ∈ ggAutomizer K' Bs :=
      (ggA8Nbr_kAut hy' hyK hF φ).mpr ⟨1, Pi.single i 1, fun b => by
        exact hφ b⟩
    obtain ⟨h, hhK, hhN, hhconj⟩ := mem_ggAutomizer_iff.mp hmem
    refine ⟨h, hhK, hhN, ?_⟩
    intro v
    have hconj1 : h * fPow f v * h⁻¹ = (φ (fPow g v) : G) := by
      rw [← hg_coe v]
      exact (hhconj (fPow g v)).symm
    have hιeq : ι (Additive.ofMul (φ (fPow g v))) =
        ι (Additive.ofMul (fPow g (vecMul v (C * N i * C⁻¹)))) := by
      rw [hφ (fPow g v), hC v, hC (vecMul v (C * N i * C⁻¹))]
      rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
      rw [show (C * N i * C⁻¹) * C = C * N i * (C⁻¹ * C) from by noncomm_ring,
        hCinv_mul, mul_one]
    have hφeq : φ (fPow g v) = fPow g (vecMul v (C * N i * C⁻¹)) := ι.injective hιeq
    rw [hconj1, hφeq]
    exact hg_coe (vecMul v (C * N i * C⁻¹))
  choose h hhK hhN hconj using hExists
  refine ⟨fun i => C * N i * C⁻¹, ?_, ?_⟩
  ·
    intro i j hij
    change C * N i * C⁻¹ = C * N j * C⁻¹ at hij
    apply hNinj
    calc N i = C⁻¹ * (C * N i * C⁻¹) * C := by
          rw [show C⁻¹ * (C * N i * C⁻¹) * C = (C⁻¹ * C) * N i * (C⁻¹ * C) from by
            noncomm_ring, hCinv_mul, one_mul, mul_one]
      _ = C⁻¹ * (C * N j * C⁻¹) * C := by rw [hij]
      _ = N j := by
          rw [show C⁻¹ * (C * N j * C⁻¹) * C = (C⁻¹ * C) * N j * (C⁻¹ * C) from by
            noncomm_ring, hCinv_mul, one_mul, mul_one]
  · intro i
    refine ⟨⟨h i, hhK i, hhN i, hconj i⟩, ?_, ?_, ?_⟩
    ·
      have hsub : C * N i * C⁻¹ - 1 = C * (N i - 1) * C⁻¹ := by
        rw [mul_sub, sub_mul, mul_one, hmul_Cinv]
      rw [hsub, show C * (N i - 1) * C⁻¹ = (C * (N i - 1)) * C⁻¹ from rfl,
        Matrix.rank_mul_eq_left_of_isUnit_det C⁻¹ (C * (N i - 1))
          (Matrix.isUnit_nonsing_inv_det (A := C) hCdet),
        Matrix.rank_mul_eq_right_of_det_ne_zero C (N i - 1) (IsUnit.ne_zero hCdet)]
      exact hNrank i
    ·
      have hconjpow : ∀ n : ℕ, (C * N i * C⁻¹) ^ n = C * N i ^ n * C⁻¹ := by
        intro n
        induction n with
        | zero => rw [pow_zero, pow_zero, mul_one, hmul_Cinv]
        | succ n ih =>
            rw [pow_succ, ih, pow_succ]
            rw [show (C * N i ^ n * C⁻¹) * (C * N i * C⁻¹) =
                C * N i ^ n * (C⁻¹ * C) * N i * C⁻¹ from by noncomm_ring,
              hCinv_mul, mul_one]
            noncomm_ring
      rw [hconjpow 3, hNpow i, mul_one, hmul_Cinv]
    ·
      have hell : ell f c = fPow f ![1, 1, 1, c] := a11ah_ell_fPow f c
      have hfix_y : h i * y' * (h i)⁻¹ = y' := by
        have hcomm : h i * y' = y' * h i :=
          Subgroup.mem_centralizer_singleton_iff.mp (hKc.1.1 (hhK i))
        rw [hcomm]
        group
      have hell_mem : ell f c ∈ Subgroup.zpowers y' := by
        rw [hline]
        exact Subgroup.mem_zpowers _
      have hfix_ell : h i * ell f c * (h i)⁻¹ = ell f c := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hell_mem
        calc h i * ell f c * (h i)⁻¹ = h i * y' ^ k * (h i)⁻¹ := by rw [hk]
          _ = (h i * y' * (h i)⁻¹) ^ k := by
              rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
          _ = y' ^ k := by rw [hfix_y]
          _ = ell f c := hk
      have h1 : h i * fPow f ![1, 1, 1, c] * (h i)⁻¹ =
          fPow f (vecMul ![1, 1, 1, c] (C * N i * C⁻¹)) := hconj i ![1, 1, 1, c]
      rw [← hell] at h1
      rw [hfix_ell] at h1
      rw [hell] at h1
      exact hfPow_inj h1.symm

end CFSG.StandardType.A11

end

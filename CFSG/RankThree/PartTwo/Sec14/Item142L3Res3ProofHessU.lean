module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofHessTools
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofArith
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofNine
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofHessList
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC homMat blockOneGL)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

namespace L3PGLU27

open CFSG.RankThree.PartTwo.Sec14.L3PGLU

variable {K : Type} [Field K]

theorem cycThree_pow_three' : (cycThree : GL (Fin 3) K) ^ 3 = 1 :=
  CFSG.RankThree.PartTwo.Sec4.cycThree_pow_three

section HessU

variable {p f : ℕ} [Finite K] (hπ : false = false → UnitaryFieldData p f K)
  {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
  (hc : (cycThree : GL (Fin 3) K) ∈ glPi false 3 (p ^ f) K)
  (hd : diagTau hτ ∈ glPi false 3 (p ^ f) K)

omit [Finite K] in
theorem map_conj_cyc_le {Y : Subgroup (projImage (slPi false 3 (p ^ f) K))}
    (hc2 : (cycThree : GL (Fin 3) K) ^ 2 ∈ glPi false 3 (p ^ f) K)
    (hY : Y.map (Res8Hess.conjM' hπ hc2).toMonoidHom ≤ Y) :
    Y.map (Res8Hess.conjM' hπ hc).toMonoidHom ≤ Y := by
  have h3 : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← map_pow, cycThree_pow_three', map_one]
  rintro _ ⟨y, hy, rfl⟩
  have e : Res8Hess.conjM' hπ hc y =
      Res8Hess.conjM' hπ hc2 (Res8Hess.conjM' hπ hc2 y) := by
    apply Subtype.ext
    rw [Res8Hess.coe_conjM', Res8Hess.coe_conjM', Res8Hess.coe_conjM', map_pow]
    set m := ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
    have h4 : m ^ 2 * m ^ 2 = m := by
      rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_succ, h3, one_mul]
    calc m * (y : ProjGenLinGroup (Fin 3) K) * m⁻¹
        = (m ^ 2 * m ^ 2) * (y : ProjGenLinGroup (Fin 3) K) * (m ^ 2 * m ^ 2)⁻¹ := by rw [h4]
      _ = m ^ 2 * (m ^ 2 * (y : ProjGenLinGroup (Fin 3) K) * (m ^ 2)⁻¹) * (m ^ 2)⁻¹ := by group
  change Res8Hess.conjM' hπ hc y ∈ Y
  rw [e]
  exact hY ⟨_, hY ⟨y, hy, rfl⟩, rfl⟩

include hτ1 in
theorem fourierGL_mem_normGU (hq3 : 3 ∣ p ^ f + 1) {ε : K} (hε : (hπ rfl).bar ε * ε = 3)
    (h3 : (3 : K) ≠ 0) :
    fourierGL hτ hτ1 (hπ rfl) hq3 hε h3 ∈
      normGU hπ (sSup (invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd))) := by
  have h := hπ rfl
  set F := fourierGL hτ hτ1 h hq3 hε h3 with hF
  have hFU : F ∈ glPi false 3 (p ^ f) K :=
    (mem_glPi_false h).mpr (fourierGL_unitary hτ hτ1 h hq3 hε h3)
  refine ⟨hFU, ?_⟩
  have hc2 : (cycThree : GL (Fin 3) K) ^ 2 ∈ glPi false 3 (p ^ f) K := pow_mem hc 2
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hyg : ProjGenLinGroup.mk (diagTau hτ * F) = ProjGenLinGroup.mk (F * cycThree) := by
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨τu ^ 2, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      coe_fourierGL, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, fourier_mul_cyc hτ, Matrix.mul_smul, smul_smul,
      smul_smul, Units.val_pow_eq_pow_val, Units.val_mk0, mul_comm]
  have hsg : ProjGenLinGroup.mk ((cycThree : GL (Fin 3) K) ^ 2 * F) =
      ProjGenLinGroup.mk (F * diagTau hτ) := by
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨τu, Units.ext ?_⟩
    have hc2i : (cycThree : GL (Fin 3) K) ^ 2 = cycThree⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, cycThree_pow_three']
    rw [hc2i, Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      coe_fourierGL, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, fourier_mul_diagTau hτ, Matrix.mul_smul, smul_smul,
      smul_smul, Units.val_mk0, mul_comm]
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hX' := L3PGL.map_conjM'_mem_invSet142 hπ hd hc2 hc hd hFU hyg hsg hX
  exact le_sSup ⟨hX'.1, map_conj_cyc_le hπ hc hc2 hX'.2.2, hX'.2.1⟩

variable (hK : PiField false p f K) (hq : ModThree false (p ^ f))

include hK hq hτ1 in
theorem hessU_top (h9 : p ^ f % 9 = 8) (h8 : p ^ f ≠ 8) :
    sSup (invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd)) = ⊤ := by
  classical
  have h := hπ rfl
  have hfin := finite_pgl (K := K)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨h.prime⟩
  set N := sSup (invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd)) with hN
  set ρ := projOf (slPi false 3 (p ^ f) K) with hρ
  set Q := normGU hπ N with hQ
  have hcm : ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisC 1 :=
    L3PGL.coe_cycThree_eq_heisC
  have hq' : p ^ f % 3 = 2 := hq
  have hq3 : 3 ∣ p ^ f + 1 := by omega
  have hq2 : p ^ f ≠ 2 := by omega
  have hq4 : 4 ≤ p ^ f := by omega
  have hm9 := nine_mul_mU_dvd h9
  obtain ⟨hm2, hsf⟩ := mU_facts (f := f) h.prime h9 h8
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hcQ : (cycThree : GL (Fin 3) K) ∈ Q := cβ_mem_normGU hπ hτ hc hd
  have hdiag3 : ∀ x : Kˣ, x ^ (3 * mU (p ^ f)) = 1 → diagUnits 1 1 x ∈ Q := fun x hx =>
    diagUnits_mem_normGU hπ hK hq hτ hτ1 hc hd hcm hx
  have hdiag1 : ∀ x : Kˣ, x ^ (3 * mU (p ^ f)) = 1 → diagUnits x 1 1 ∈ Q := by
    intro x hx
    rw [← conj_diagUnits_heisC hcm 1 1 x]
    exact Q.mul_mem (Q.mul_mem hcQ (hdiag3 x hx)) (Q.inv_mem hcQ)
  have hscal : ∀ c : Kˣ, c ^ (p ^ f + 1) = 1 →
      Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Q := fun c hc' =>
    scalar_mem_normGU hπ ((scalar_mem_glPi_false_iff h c).mpr
      (by rw [← Units.val_pow_eq_pow_val, hc', Units.val_one]))
  obtain ⟨a₀, ha₀⟩ := CFSG.LieType.SeitzGeneration.exists_orderOf_eq h
  obtain ⟨r, hr⟩ := hm9
  have hr0 : r ≠ 0 := by
    rintro rfl
    omega
  set a : K := a₀ ^ r with hadef
  have ha : orderOf a = 9 * mU (p ^ f) := by
    rw [hadef, orderOf_pow_of_dvd hr0 (by rw [ha₀, hr]; exact dvd_mul_left r _), ha₀, hr,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at ha
    omega
  set au : Kˣ := Units.mk0 a ha0 with hau
  have hau' : (au : K) = a := rfl
  have haK : a ^ (p ^ f + 1) = 1 := by
    rw [hr, pow_mul, ← ha, pow_orderOf_eq_one, one_pow]
  have haq : au ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hau', Units.val_one]
    exact haK
  have hou : orderOf au = 9 * mU (p ^ f) := by rw [← ha, ← orderOf_units, hau']
  have hau9 : au ^ (9 * mU (p ^ f)) = 1 := by rw [← hou]; exact pow_orderOf_eq_one au
  set x : Kˣ := au⁻¹ ^ 3 with hxdef
  have hx : x ^ (3 * mU (p ^ f)) = 1 := by
    rw [hxdef, ← pow_mul, show 3 * (3 * mU (p ^ f)) = 9 * mU (p ^ f) by ring, inv_pow, hau9,
      inv_one]
  have hratio : orderOf (a⁻¹ ^ 2 / a) = 3 * mU (p ^ f) := by
    have e : a⁻¹ ^ 2 / a = (((au ^ 3)⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hau']
      field_simp
    rw [e, orderOf_units, orderOf_inv, orderOf_pow' _ (by norm_num), hou,
      Nat.gcd_eq_right (dvd_mul_of_dvd_left (by norm_num : 3 ∣ 9) _)]
    omega
  have hxa : (x : K) = a⁻¹ ^ 2 * a⁻¹ := by
    rw [hxdef, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hau', pow_succ]
  have hH1 : ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0] := by
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) au * diagUnits x 1 1,
      Q.mul_mem (hscal au haq) (hdiag1 x hx), ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagUnits, hau', hxa]
    ext i j
    rw [CFSG.LieType.SeitzGeneration.homMat_apply]
    fin_cases i <;> fin_cases j <;> simp
    all_goals field_simp
  have hH3 : ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1] := by
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) au * diagUnits 1 1 x,
      Q.mul_mem (hscal au haq) (hdiag3 x hx), ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagUnits, hau', hxa]
    ext i j
    rw [CFSG.LieType.SeitzGeneration.homMat_apply]
    fin_cases i <;> fin_cases j <;> simp
    all_goals field_simp
  obtain ⟨ε, hε⟩ : ∃ ε : K, h.bar ε * ε = 3 := by
    have : CharP K p := h.charP
    have hK2 : Nat.card K = (p ^ f) ^ 2 := h.card_eq_sq
    have hfix : CFSG.LieType.BorelTits.unitaryInvolution K p f 3 = 3 := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply, map_ofNat]
    obtain ⟨ε, hε⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed (p := p) (f := f) hK2
      hfix h3
    refine ⟨ε, ?_⟩
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply] at hε
    exact hε
  set F := fourierGL hτ hτ1 h hq3 hε h3 with hF
  have hFQ : F ∈ Q := fourierGL_mem_normGU hπ hτ hτ1 hc hd hq3 hε h3
  set ζ : Kˣ := au ^ 3 with hζ
  have hζo : orderOf ζ = 3 * mU (p ^ f) := by
    rw [hζ, orderOf_pow' _ (by norm_num), hou,
      Nat.gcd_eq_right (dvd_mul_of_dvd_left (by norm_num : 3 ∣ 9) _)]
    omega
  set S : Finset K := (Finset.range (3 * mU (p ^ f))).image (fun k => ((ζ ^ k : Kˣ) : K))
    with hS
  have hScard : S.card = 3 * mU (p ^ f) := by
    rw [hS, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hij' : ζ ^ i = ζ ^ j := Units.ext hij
    exact pow_injOn_Iio_orderOf (by rw [hζo]; exact Finset.mem_range.mp hi)
      (by rw [hζo]; exact Finset.mem_range.mp hj) hij'
  obtain ⟨x₀, hx₀S, hx₀1, hx₀2, hx₀7⟩ := exists_good_of_card S (by omega) 1 (-2)
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx₀S
  set y : Kˣ := ζ ^ k with hy
  have hy3m : y ^ (3 * mU (p ^ f)) = 1 := by
    rw [hy, ← pow_mul, mul_comm, pow_mul, ← hζo, pow_orderOf_eq_one, one_pow]
  have hyq : (y : K) ^ (p ^ f + 1) = 1 := by
    obtain ⟨s, hs⟩ : 3 * mU (p ^ f) ∣ p ^ f + 1 :=
      (Nat.mul_dvd_mul_right (by norm_num : 3 ∣ 9) _).trans ⟨r, hr⟩
    rw [hs, pow_mul, ← Units.val_pow_eq_pow_val, hy3m, Units.val_one, one_pow]
  have hy0 : (y : K) ≠ 0 := y.ne_zero
  have hybar : h.bar (y : K) = (y : K)⁻¹ := by
    have hn : h.bar (y : K) * y = 1 := by
      rw [CFSG.LieType.SeitzGeneration.bar_mul_self_eq_pow]
      exact hyq
    exact eq_inv_of_mul_eq_one_left hn
  set z : GL (Fin 3) K := (cycThree : GL (Fin 3) K)⁻¹ * F * diagUnits y 1 1 * F⁻¹ with hz
  have hzQ : z ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.inv_mem hcQ) hFQ) (hdiag1 y hy3m)) (Q.inv_mem hFQ)
  have hzm : (z : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] *
      ((ε⁻¹ • fourierMat τ) * diagonal ![(y : K), 1, 1] *
        ((h.bar ε)⁻¹ • ((fourierMat τ).map h.bar)ᵀ)) := by
    rw [hz, Units.val_mul, Units.val_mul, Units.val_mul, coe_fourierGL, coe_fourierGL_inv,
      coe_diagUnits]
    simp only [Matrix.mul_assoc, Units.val_one]
    rfl
  have hzw : (z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1] =
      ![((y : K) - 1) / 3, ((y : K) + 2) / 3, ((y : K) - 1) / 3] := by
    rw [hzm]
    exact fourier_conj_mulVec hτ hτ1 h hq3 hε (y : K)
  have hzU : ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (z : Matrix (Fin 3) (Fin 3) K) = 1 :=
    (mem_glPi_false h).mp hzQ.1
  have hy1' : (y : K) - 1 ≠ 0 := sub_ne_zero.mpr hx₀1
  have hy2' : (y : K) + 2 ≠ 0 := by
    intro h0
    exact hx₀2 (by linear_combination h0)
  have hB := block_mem_of_generic_column h hq4 haK (by rw [ha]; omega) (by rw [hratio]; omega)
    (by rw [hratio]; exact hsf) Q hH1 hH3 hzQ hzU
    (by rw [hzw]; exact div_ne_zero hy1' h3) (by rw [hzw]; exact div_ne_zero hy2' h3)
    (by rw [hzw]; exact div_ne_zero hy1' h3)
    (by
      rw [hzw]
      intro h1
      apply hx₀7
      simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1
      rw [map_div₀, map_sub, map_one, map_ofNat, hybar] at h1
      field_simp at h1
      linear_combination -h1)
  have hSU := su_le_of_block_le h hq2 (by rw [map_one, one_mul]) hcm hcQ hB
  have hnorm : N.Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨z', rfl⟩ := projOf_surjective _ m
    have hzQ' := hSU (z' : GL (Fin 3) K) z'.2
    have hmap := map_le_of_mem_normGU hπ (slPi_le_glPi hπ z'.2) hzQ'
    rw [conjM'_eq_conj hπ z'] at hmap
    exact hmap ⟨n, hn, rfl⟩
  have hsimple : IsSimpleGroup (projImage (slPi false 3 (p ^ f) K)) := by
    have hK2 : Nat.card K = (p ^ f) ^ 2 := h.card_eq_sq
    have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK2 3 le_rfl
      (by intro e; exact hq2 (Prod.ext_iff.mp e).2)
    exact (Sec4.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)
      (P := projImage (slPi false 3 (p ^ f) K)) rfl).symm.isSimpleGroup
  set t : Kˣ := ζ ^ 3 with ht
  have hto : orderOf t = mU (p ^ f) := by
    rw [ht, orderOf_pow' _ (by norm_num), hζo, Nat.gcd_eq_right (dvd_mul_right 3 _)]
    omega
  have htm : t ∈ rootsOfUnity (mU (p ^ f)) K := by
    rw [mem_rootsOfUnity, ← hto]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hto
    omega
  have hTsl : torusHom (t, t⁻¹) ∈ slPi false 3 (p ^ f) K := by
    have htR : t ∈ rootsOfUnity (qSubPi false (p ^ f)) K := by
      rw [mem_rootsOfUnity]
      obtain ⟨s, hs⟩ := mU_dvd (p ^ f)
      change t ^ (p ^ f + 1) = 1
      rw [hs, pow_mul, ← hto, pow_orderOf_eq_one, one_pow]
    exact torusHom_mem_slPi hK htR (inv_mem htR)
  set w : slPi false 3 (p ^ f) K := ⟨torusHom (t, t⁻¹), hTsl⟩ with hw
  have hwN : ρ w ∈ N :=
    le_sSup (diagMuU_mem_invSet142 hπ hτ hc hd hcm)
      ⟨w, mem_diagMuU.mpr ⟨t, t⁻¹, htm, inv_mem htm, rfl⟩, rfl⟩
  have hw1 : ρ w ≠ 1 := by
    intro e
    rw [projOf_eq_one_iff] at e
    obtain ⟨s, hs⟩ := e
    have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hs
    have h22 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hs
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h00 h22
    change (s : K) = ((torusHom (t, t⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 at h00
    change (s : K) = ((torusHom (t, t⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 at h22
    rw [coe_torusHom] at h00 h22
    simp at h00 h22
    exact ht1 (Units.ext (by rw [← h00, h22]))
  have := hnorm
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exact absurd (hbot ▸ hwN : ρ w ∈ (⊥ : Subgroup _)) (by
      rw [Subgroup.mem_bot]
      exact hw1)
  · exact htop

end HessU

theorem eq_two_three_of_pow_eq_eight {p f : ℕ} (hp : p.Prime) (h8 : p ^ f = 8) :
    p = 2 ∧ f = 3 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    norm_num at h8
  have hp2 : p = 2 := by
    have hd : p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8]
      exact dvd_pow_self p hf0
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective le_rfl (h8.trans (by norm_num))⟩

end L3PGLU27

open L3PGLU27 L3PGLU Res8Hess in
theorem ks142L3HessGenNineModel_unitary (p f : ℕ) (K : Type)
    [Field K] (hK : PiField false p f K) (hq : ModThree false (p ^ f))
    (h9 : p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) (h28 : ¬ (p = 2 ∧ f = 3)) (τ : K) (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (dM cM : projImage (slPi false 3 (p ^ f) K))
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)) :
    ⨆ (b : projImage (slPi false 3 (p ^ f) K)) (_ : b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM)
      (_ : b ≠ 1), thetaC b = ⊤ := by
  have hπ : false = false → UnitaryFieldData p f K := fun _ => hK.unitary
  have h := hπ rfl
  have := hK.finite
  have hfin := finite_pgl (K := K)
  have hq' : p ^ f % 3 = 2 := hq
  have h9' : p ^ f % 9 = 8 := by omega
  have h8 : p ^ f ≠ 8 := fun e => h28 (eq_two_three_of_pow_eq_eight h.prime e)
  have hcS : (cycThree : GL (Fin 3) K) ∈ slPi false 3 (p ^ f) K := cycThree_mem_slPi hπ
  have hdS : diagTau hτ ∈ slPi false 3 (p ^ f) K := diagTau_mem_slPi hπ (fun _ => hq) hτ
  have hc : (cycThree : GL (Fin 3) K) ∈ glPi false 3 (p ^ f) K := slPi_le_glPi hπ hcS
  have hd : diagTau hτ ∈ glPi false 3 (p ^ f) K := slPi_le_glPi hπ hdS
  have htop := hessU_top hπ hτ hτ1 hc hd hK hq h9' h8
  obtain ⟨dM', cM', hdM', hcM', hdc, hdo, hco, hcd⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  have e1 : dM = dM' := Subtype.ext (hdM.trans hdM'.symm)
  have e2 : cM = cM' := Subtype.ext (hcM.trans hcM'.symm)
  subst e1 e2
  set ρ := projOf (slPi false 3 (p ^ f) K) with hρ
  have hρd : ρ ⟨diagTau hτ, hdS⟩ = dM := Subtype.ext (by rw [coe_projOf, hdM])
  have hρc : ρ ⟨cycThree, hcS⟩ = cM := Subtype.ext (by rw [coe_projOf, hcM])
  have hconjd : conjM' hπ hd = MulAut.conj dM := by
    rw [← hρd]
    exact conjM'_eq_conj hπ ⟨diagTau hτ, hdS⟩
  have hconjc : conjM' hπ hc = MulAut.conj cM := by
    rw [← hρc]
    exact conjM'_eq_conj hπ ⟨cycThree, hcS⟩
  rw [eq_top_iff, ← htop]
  refine sSup_le fun X hX => ?_
  obtain ⟨hX3, hXc, hXd⟩ := hX
  rw [hconjc] at hXc
  rw [hconjd] at hXd
  have hEY : Subgroup.zpowers dM ⊔ Subgroup.zpowers cM ≤
      Subgroup.normalizer (X : Set (projImage (slPi false 3 (p ^ f) K))) :=
    sup_le (Subgroup.zpowers_le.mpr (L3PGLU.mem_normalizer_of_map_le hXd))
      (Subgroup.zpowers_le.mpr (L3PGLU.mem_normalizer_of_map_le hXc))
  obtain ⟨b, hb, hb1, hXb⟩ :=
    L3PGL.hess_le_thetaC hτ hτ1 hK hq hdM hcM hdc hdo hco hcd hX3 hEY
  exact le_trans hXb (le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl))

end CFSG.RankThree.PartTwo.Sec14

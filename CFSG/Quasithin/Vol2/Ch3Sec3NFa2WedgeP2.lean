module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321W
public import CFSG.Quasithin.Background.FLc2Fix

public section

namespace CFSG.Quasithin.H13.NFa2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.Lift

abbrev k₀ : Fin 6 := 0

abbrev k₁ : Fin 6 := 5

theorem P2_lower (g : L3321.SL4) (hg : g ∈ L3321.P2) (k l : Fin 4) (hk : 2 ≤ (k : ℕ))
    (hl : (l : ℕ) < 2) : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) k l = 0 :=
  (L3321.mem_P2_iff g).1 hg k l hl hk

theorem P2_det_C (g : L3321.SL4) (hg : g ∈ L3321.P2) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 2 * (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 3 -
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3 * (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 2 = 1 := by
  have h := (L3321.blkC ⟨g, hg⟩).2
  rw [L3321.coe_blkC, Matrix.det_fin_two] at h
  exact h

theorem blkA_one_entry (g : L3321.SL4) (hg : g ∈ L3321.P2) (hA : L3321.blkA ⟨g, hg⟩ = 1)
    (i j : Fin 2) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨i, by omega⟩ ⟨j, by omega⟩ =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j := by
  have h := L3321.blkAM_apply ⟨g, hg⟩ i j
  have hA' : L3321.blkAM ⟨g, hg⟩ = 1 := by
    have := congrArg (fun x : SL2F2 => (x : Matrix (Fin 2) (Fin 2) (ZMod 2))) hA
    simpa [L3321.coe_blkA] using this
  rw [hA'] at h
  exact h.symm

theorem blkC_one_entry (g : L3321.SL4) (hg : g ∈ L3321.P2) (hC : L3321.blkC ⟨g, hg⟩ = 1)
    (i j : Fin 2) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨2 + i, by omega⟩ ⟨2 + j, by omega⟩ =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j := by
  have h := L3321.blkCM_apply ⟨g, hg⟩ i j
  have hC' : L3321.blkCM ⟨g, hg⟩ = 1 := by
    have := congrArg (fun x : SL2F2 => (x : Matrix (Fin 2) (Fin 2) (ZMod 2))) hC
    simpa [L3321.coe_blkC] using this
  rw [hC'] at h
  exact h.symm

theorem wedge_P2_coord_pair23 (g : L3321.SL4) (hg : g ∈ L3321.P2) (v : Fin 6 → ZMod 2) :
    (B5FinWedge.wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) k₁ = v k₁ := by
  have h20 := P2_lower g hg 2 0 (by decide) (by decide)
  have h21 := P2_lower g hg 2 1 (by decide) (by decide)
  have h30 := P2_lower g hg 3 0 (by decide) (by decide)
  have h31 := P2_lower g hg 3 1 (by decide) (by decide)
  have hdet := P2_det_C g hg
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, B5FinWedge.wedgeMat4, B5FinWedge.pr4,
    Matrix.of_apply, k₁]
  simp only [Matrix.cons_val, h20, h21, h30, h31]
  linear_combination (v 5) * hdet

theorem wedge_U2_comm_Hz (g : L3321.SL4) (hg : g ∈ L3321.P2) (hA : L3321.blkA ⟨g, hg⟩ = 1)
    (hC : L3321.blkC ⟨g, hg⟩ = 1) (v : Fin 6 → ZMod 2) (hv : v k₁ = 0) (j : Fin 6)
    (hj : j ≠ k₀) :
    (B5FinWedge.wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) j = v j := by
  have eA := blkA_one_entry g hg hA
  have eC := blkC_one_entry g hg hC
  have e00 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0 = 1 := by simpa using eA 0 0
  have e01 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1 = 0 := by simpa using eA 0 1
  have e10 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 0 = 0 := by simpa using eA 1 0
  have e11 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 1 = 1 := by simpa using eA 1 1
  have e22 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 2 = 1 := by simpa using eC 0 0
  have e23 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3 = 0 := by simpa using eC 0 1
  have e32 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 2 = 0 := by simpa using eC 1 0
  have e33 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 3 = 1 := by simpa using eC 1 1
  have h20 := P2_lower g hg 2 0 (by decide) (by decide)
  have h21 := P2_lower g hg 2 1 (by decide) (by decide)
  have h30 := P2_lower g hg 3 0 (by decide) (by decide)
  have h31 := P2_lower g hg 3 1 (by decide) (by decide)
  simp only [k₁] at hv
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, B5FinWedge.wedgeMat4, B5FinWedge.pr4,
    Matrix.of_apply]
  fin_cases j
  · exact absurd rfl hj
  all_goals simp [e00, e01, e10, e11, e22, e23, e32, e33, h20, h21, h30, h31, hv]

@[expose] def uBmat (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, B 0 0, B 0 1; 0, 1, B 1 0, B 1 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem uBmat_det (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) : (uBmat B).det = 1 := by
  simp only [uBmat]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ] <;> ring

@[expose] def uB (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) : L3321.SL4 :=
  ⟨uBmat B, uBmat_det B⟩

theorem uB_mem_P2 (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) : uB B ∈ L3321.P2 := by
  rw [L3321.mem_P2_iff]
  intro k l hl hk
  fin_cases k <;> fin_cases l <;> first | rfl | exact absurd hl (by decide) | exact absurd hk (by decide)

theorem wedge_P2_fixed_aux : ∀ v : Fin 6 → ZMod 2,
    B5FinWedge.wedgeMat4 (uBmat (Matrix.single 0 0 1)) *ᵥ v = v →
    B5FinWedge.wedgeMat4 (uBmat (Matrix.single 0 1 1)) *ᵥ v = v →
    B5FinWedge.wedgeMat4 (uBmat (Matrix.single 1 0 1)) *ᵥ v = v →
    B5FinWedge.wedgeMat4 (uBmat (Matrix.single 1 1 1)) *ᵥ v = v →
    v = 0 ∨ v = Pi.single k₀ 1 := by
  decide +kernel

theorem wedge_P2_fixed (v : Fin 6 → ZMod 2)
    (hv : ∀ g : L3321.SL4, g ∈ L3321.P2 →
      B5FinWedge.wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) :
    v = 0 ∨ v = Pi.single k₀ 1 :=
  wedge_P2_fixed_aux v (hv (uB (Matrix.single 0 0 1)) (uB_mem_P2 _))
    (hv (uB (Matrix.single 0 1 1)) (uB_mem_P2 _)) (hv (uB (Matrix.single 1 0 1)) (uB_mem_P2 _))
    (hv (uB (Matrix.single 1 1 1)) (uB_mem_P2 _))

theorem wedge_P2_coord_pair23_actW (g : L3321.SL4) (hg : g ∈ L3321.P2)
    (a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :
    B5FinWedge.wedgeCoord4 (Multiplicative.toAdd (FLc.actW g a)) k₁ =
      B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a) k₁ := by
  rw [FLc.coord4_actW]
  exact wedge_P2_coord_pair23 g hg _

theorem wedge_U2_comm_Hz_actW (g : L3321.SL4) (hg : g ∈ L3321.P2) (hA : L3321.blkA ⟨g, hg⟩ = 1)
    (hC : L3321.blkC ⟨g, hg⟩ = 1) (a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)))
    (ha : B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a) k₁ = 0) (j : Fin 6) (hj : j ≠ k₀) :
    B5FinWedge.wedgeCoord4 (Multiplicative.toAdd (FLc.actW g a)) j =
      B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a) j := by
  rw [FLc.coord4_actW]
  exact wedge_U2_comm_Hz g hg hA hC _ ha j hj

theorem wedge_P2_fixed_actW (a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)))
    (ha : ∀ g : L3321.SL4, g ∈ L3321.P2 → FLc.actW g a = a) :
    Multiplicative.toAdd a = 0 ∨
      Multiplicative.toAdd a = B5FinWedge.wedgeBasis4 k₀ := by
  have hv : ∀ g : L3321.SL4, g ∈ L3321.P2 →
      B5FinWedge.wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a) =
        B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a) := by
    intro g hg
    have h := FLc.coord4_actW g a
    rw [ha g hg] at h
    exact h.symm
  rcases wedge_P2_fixed _ hv with h | h
  · left
    apply (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)).1
    rw [h, map_zero]
  · right
    apply (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)).1
    rw [h, B5FinWedge.wedgeCoord4_basis]

@[expose] noncomputable def U2 : Subgroup L3321.SL4 :=
  (L3321.blkA.ker ⊓ L3321.blkC.ker : Subgroup L3321.P2).map L3321.P2.subtype

theorem mem_U2_iff (g : L3321.SL4) :
    g ∈ U2 ↔ ∃ hg : g ∈ L3321.P2, L3321.blkA ⟨g, hg⟩ = 1 ∧ L3321.blkC ⟨g, hg⟩ = 1 := by
  constructor
  · intro h
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 h
    obtain ⟨hA, hC⟩ := Subgroup.mem_inf.1 hx
    subst hxg
    exact ⟨x.2, MonoidHom.mem_ker.1 hA, MonoidHom.mem_ker.1 hC⟩
  · rintro ⟨hg, hA, hC⟩
    exact Subgroup.mem_map.2
      ⟨⟨g, hg⟩, Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 hA, MonoidHom.mem_ker.2 hC⟩, rfl⟩

theorem U2_le_P2 : U2 ≤ L3321.P2 := by
  intro g hg
  obtain ⟨hgP, -⟩ := (mem_U2_iff g).1 hg
  exact hgP

theorem U2_subgroupOf : U2.subgroupOf L3321.P2 = L3321.blkA.ker ⊓ L3321.blkC.ker := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    obtain ⟨_hx, hA, hC⟩ := (mem_U2_iff (x : L3321.SL4)).1 h
    exact ⟨hA, hC⟩
  · rintro ⟨hA, hC⟩
    exact (mem_U2_iff (x : L3321.SL4)).2 ⟨x.2, hA, hC⟩

theorem U2_normal_in_P2 : (U2.subgroupOf L3321.P2).Normal := by
  rw [U2_subgroupOf]
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨hA, hC⟩ := Subgroup.mem_inf.1 hn
  rw [MonoidHom.mem_ker] at hA hC
  rw [Subgroup.mem_inf]
  constructor <;> rw [MonoidHom.mem_ker] <;> simp [hA, hC]

theorem uB_mem_U2 (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) : uB B ∈ U2 := by
  rw [mem_U2_iff]
  refine ⟨uB_mem_P2 B, ?_, ?_⟩
  · apply Subtype.ext
    rw [L3321.coe_blkA, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    rw [L3321.blkAM_apply]
    fin_cases i <;> fin_cases j <;> rfl
  · apply Subtype.ext
    rw [L3321.coe_blkC, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    rw [L3321.blkCM_apply]
    fin_cases i <;> fin_cases j <;> rfl

@[expose] def uBlock (g : L3321.SL4) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![(g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3;
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3]

theorem uB_uBlock (g : L3321.SL4) (hg : g ∈ L3321.P2) (hA : L3321.blkA ⟨g, hg⟩ = 1)
    (hC : L3321.blkC ⟨g, hg⟩ = 1) : uB (uBlock g) = g := by
  apply Subtype.ext
  show uBmat (uBlock g) = (g : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have eA := blkA_one_entry g hg hA
  have eC := blkC_one_entry g hg hC
  have e00 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0 = 1 := by simpa using eA 0 0
  have e01 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1 = 0 := by simpa using eA 0 1
  have e10 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 0 = 0 := by simpa using eA 1 0
  have e11 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 1 = 1 := by simpa using eA 1 1
  have e22 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 2 = 1 := by simpa using eC 0 0
  have e23 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3 = 0 := by simpa using eC 0 1
  have e32 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 2 = 0 := by simpa using eC 1 0
  have e33 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 3 = 1 := by simpa using eC 1 1
  have h20 := P2_lower g hg 2 0 (by decide) (by decide)
  have h21 := P2_lower g hg 2 1 (by decide) (by decide)
  have h30 := P2_lower g hg 3 0 (by decide) (by decide)
  have h31 := P2_lower g hg 3 1 (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uBmat, uBlock, e00, e01, e10, e11, e22, e23, e32, e33, h20, h21, h30, h31]

theorem uB_injective : Function.Injective uB := by
  intro B B' h
  have h' : uBmat B = uBmat B' := congrArg (fun g : L3321.SL4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h' 0) 2
  · exact congrFun (congrFun h' 0) 3
  · exact congrFun (congrFun h' 1) 2
  · exact congrFun (congrFun h' 1) 3

theorem uB_surjective_U2 : Function.Surjective (fun B : Matrix (Fin 2) (Fin 2) (ZMod 2) => (⟨uB B, uB_mem_U2 B⟩ : U2)) := by
  rintro ⟨g, hg⟩
  obtain ⟨hgP, hA, hC⟩ := (mem_U2_iff g).1 hg
  exact ⟨uBlock g, Subtype.ext (uB_uBlock g hgP hA hC)⟩

@[expose] noncomputable def U2Equiv : Matrix (Fin 2) (Fin 2) (ZMod 2) ≃ U2 :=
  Equiv.ofBijective (fun B => (⟨uB B, uB_mem_U2 B⟩ : U2))
    ⟨fun B B' h => uB_injective (congrArg Subtype.val h), uB_surjective_U2⟩

theorem card_U2 : Nat.card U2 = 16 := by
  rw [← Nat.card_congr U2Equiv, Nat.card_eq_fintype_card]
  decide +kernel

theorem U2_isPGroup : IsPGroup 2 U2 :=
  IsPGroup.of_card (n := 4) (by rw [card_U2]; norm_num)

theorem U2_subgroupOf_isPGroup : IsPGroup 2 (U2.subgroupOf L3321.P2) :=
  IsPGroup.of_card (n := 4) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe U2_le_P2).toEquiv, card_U2]
    norm_num)

@[expose] def c3 : SL2F2 := ⟨!![0, 1; 1, 1], by decide⟩

theorem sl2F2_sq_of_pow_four : ∀ a : SL2F2, a ^ 4 = 1 → a ^ 2 = 1 := by
  decide

theorem sl2F2_sq_of_pow_two_pow : ∀ (m : ℕ) (a : SL2F2), a ^ 2 ^ m = 1 → a ^ 2 = 1 := by
  intro m
  induction m with
  | zero =>
    intro a ha
    rw [pow_zero, pow_one] at ha
    rw [ha, one_pow]
  | succ m ih =>
    intro a ha
    have hb : (a ^ 2) ^ 2 ^ m = 1 := by
      have e : (a ^ 2) ^ 2 ^ m = a ^ 2 ^ (m + 1) := by
        rw [← pow_mul]
        congr 1
        ring
      rw [e]
      exact ha
    have h4 : (a ^ 2) ^ 2 = 1 := ih _ hb
    have h4' : a ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      exact h4
    exact sl2F2_sq_of_pow_four a h4'

theorem sl2F2_key_S3 : ∀ a : SL2F2, a ^ 2 = 1 → (a * (c3 * a * c3⁻¹)⁻¹) ^ 2 = 1 → a = 1 := by
  decide

theorem sq_eq_one_of_pgroup (K : Subgroup L3321.P2) (hKp : IsPGroup 2 K) (f : L3321.P2 →* SL2F2)
    (x : L3321.P2) (hx : x ∈ K) : (f x) ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hKp ⟨x, hx⟩
  have hx' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  apply sl2F2_sq_of_pow_two_pow k
  rw [← map_pow, hx', map_one]

theorem blkA_eq_one_of_normal (K : Subgroup L3321.P2) (hKn : K.Normal) (hKp : IsPGroup 2 K)
    (x : L3321.P2) (hx : x ∈ K) : L3321.blkA x = 1 := by
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : L3321.P2, L3321.blkA h₀ = c3 :=
    ⟨⟨L3321.diagSL c3 1, L3321.diagSL_mem c3 1⟩, L3321.blkA_diagSL c3 1⟩
  have hz : x * (h₀ * x * h₀⁻¹)⁻¹ ∈ K := K.mul_mem hx (K.inv_mem (hKn.conj_mem x hx h₀))
  have h1 := sq_eq_one_of_pgroup K hKp L3321.blkA x hx
  have h2 := sq_eq_one_of_pgroup K hKp L3321.blkA _ hz
  simp only [map_mul, map_inv, hh₀] at h2
  exact sl2F2_key_S3 _ h1 h2

theorem blkC_eq_one_of_normal (K : Subgroup L3321.P2) (hKn : K.Normal) (hKp : IsPGroup 2 K)
    (x : L3321.P2) (hx : x ∈ K) : L3321.blkC x = 1 := by
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : L3321.P2, L3321.blkC h₀ = c3 :=
    ⟨⟨L3321.diagSL 1 c3, L3321.diagSL_mem 1 c3⟩, L3321.blkC_diagSL 1 c3⟩
  have hz : x * (h₀ * x * h₀⁻¹)⁻¹ ∈ K := K.mul_mem hx (K.inv_mem (hKn.conj_mem x hx h₀))
  have h1 := sq_eq_one_of_pgroup K hKp L3321.blkC x hx
  have h2 := sq_eq_one_of_pgroup K hKp L3321.blkC _ hz
  simp only [map_mul, map_inv, hh₀] at h2
  exact sl2F2_key_S3 _ h1 h2

theorem U2_eq_pCore : U2.subgroupOf L3321.P2 = CFSG.pCore 2 ↥L3321.P2 := by
  unfold CFSG.pCore
  apply le_antisymm
  · exact le_sSup ⟨U2_normal_in_P2, U2_subgroupOf_isPGroup⟩
  · refine sSup_le ?_
    rintro K ⟨hKn, hKp⟩ x hx
    rw [U2_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨blkA_eq_one_of_normal K hKn hKp x hx, blkC_eq_one_of_normal K hKn hKp x hx⟩

end CFSG.Quasithin.H13.NFa2

module

public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.Open
open scoped Matrix Pointwise

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr

section Codes

theorem burnsideF48t_gf4Mul_lt {a b : ℕ} (ha : a < 4) (hb : b < 4) : burnsideF48t_gf4Mul a b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

theorem burnsideF48t_gf4Sq_lt {a : ℕ} (ha : a < 4) : burnsideF48t_gf4Sq a < 4 := by
  interval_cases a <;> decide

theorem burnsideF48t_xor_lt {a b : ℕ} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 :=
  Nat.xor_lt_two_pow (n := 2) ha hb

variable {K : Type} [Field K] {ω : K}

theorem burnsideF48t_gf4D_inj (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) {a b : ℕ} (ha : a < 4)
    (hb : b < 4) (h : burnsideF48t_gf4D ω a = burnsideF48t_gf4D ω b) : a = b := by
  interval_cases a <;> interval_cases b <;>
    first | rfl | (simp only [burnsideF48t_gf4D] at h; (try norm_num at h) <;> grind)

end Codes

section Vectors

variable {K : Type} [Field K] (ω : K)

@[expose] def burnsideF48t_u52dv (v : Array ℕ) : Fin 5 → K :=
  fun j => burnsideF48t_gf4D ω v[(j : ℕ)]!

variable {ω}

@[expose] def burnsideF48t_u52Small (v : Array ℕ) : Prop := ∀ j < 5, v[j]! < 4

theorem burnsideF48t_u52_dv_dot (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) {a b : Array ℕ}
    (ha : burnsideF48t_u52Small a) (hb : burnsideF48t_u52Small b) :
    burnsideF48t_u52dv ω a ⬝ᵥ burnsideF48t_u52dv ω b =
      burnsideF48t_gf4D ω (burnsideF48t_u52Dot a b) := by
  have hm : ∀ j < 5, burnsideF48t_gf4Mul a[j]! b[j]! < 4 := fun j hj =>
    burnsideF48t_gf4Mul_lt (ha j hj) (hb j hj)
  have hd : ∀ j < 5, burnsideF48t_gf4D ω (burnsideF48t_gf4Mul a[j]! b[j]!) =
      burnsideF48t_gf4D ω a[j]! * burnsideF48t_gf4D ω b[j]! := fun j hj =>
    burnsideF48t_gf4D_mul h2 hω (ha j hj) (hb j hj)
  simp only [dotProduct, Fin.sum_univ_five, burnsideF48t_u52dv, burnsideF48t_u52Dot]
  rw [burnsideF48t_gf4D_xor h2 (burnsideF48t_xor_lt (burnsideF48t_xor_lt (burnsideF48t_xor_lt
      (hm 0 (by norm_num)) (hm 1 (by norm_num))) (hm 2 (by norm_num))) (hm 3 (by norm_num)))
      (hm 4 (by norm_num)),
    burnsideF48t_gf4D_xor h2 (burnsideF48t_xor_lt (burnsideF48t_xor_lt
      (hm 0 (by norm_num)) (hm 1 (by norm_num))) (hm 2 (by norm_num))) (hm 3 (by norm_num)),
    burnsideF48t_gf4D_xor h2 (burnsideF48t_xor_lt (hm 0 (by norm_num)) (hm 1 (by norm_num)))
      (hm 2 (by norm_num)),
    burnsideF48t_gf4D_xor h2 (hm 0 (by norm_num)) (hm 1 (by norm_num)),
    hd 0 (by norm_num), hd 1 (by norm_num), hd 2 (by norm_num), hd 3 (by norm_num),
    hd 4 (by norm_num)]
  rfl

theorem burnsideF48t_u52_dv_bar (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) {a : Array ℕ}
    (ha : burnsideF48t_u52Small a) :
    burnsideF48t_u52dv ω (burnsideF48t_u52Bar a) = fun j => burnsideF48t_u52dv ω a j ^ 2 := by
  funext j
  simp only [burnsideF48t_u52dv, burnsideF48t_u52Bar]
  rw [getElem!_ofFn_nat _ j.2]
  exact burnsideF48t_gf4D_sq h2 hω (ha j j.2)

theorem burnsideF48t_u52_small_bar {a : Array ℕ} (ha : burnsideF48t_u52Small a) :
    burnsideF48t_u52Small (burnsideF48t_u52Bar a) := fun j hj => by
  simp only [burnsideF48t_u52Bar]
  rw [getElem!_ofFn_nat _ hj]
  exact burnsideF48t_gf4Sq_lt (ha j hj)

theorem burnsideF48t_u52_dv_TV (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) (bar : K →+* K)
    (hbar : ∀ c, bar c = c ^ 2) {u v : Array ℕ} (hu : burnsideF48t_u52Small u)
    (hv : burnsideF48t_u52Small v) :
    burnsideF48t_u52dv ω (burnsideF48t_u52TV u v) =
      burnsideF48t_trans bar (burnsideF48t_u52dv ω u) *ᵥ burnsideF48t_u52dv ω v := by
  have hs : (fun j => bar (burnsideF48t_u52dv ω u j)) ⬝ᵥ burnsideF48t_u52dv ω v =
      burnsideF48t_gf4D ω (burnsideF48t_u52Dot (burnsideF48t_u52Bar u) v) := by
    rw [← burnsideF48t_u52_dv_dot h2 hω (burnsideF48t_u52_small_bar hu) hv,
      burnsideF48t_u52_dv_bar h2 hω hu]
    simp only [hbar]
  have hslt : burnsideF48t_u52Dot (burnsideF48t_u52Bar u) v < 4 := by
    have hb := burnsideF48t_u52_small_bar hu
    simp only [burnsideF48t_u52Dot]
    refine burnsideF48t_xor_lt (burnsideF48t_xor_lt (burnsideF48t_xor_lt (burnsideF48t_xor_lt
      ?_ ?_) ?_) ?_) ?_ <;> exact burnsideF48t_gf4Mul_lt (hb _ (by norm_num)) (hv _ (by norm_num))
  rw [burnsideF48t_trans_mulVec, hs]
  funext j
  simp only [burnsideF48t_u52dv, burnsideF48t_u52TV, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [getElem!_ofFn_nat _ j.2, burnsideF48t_gf4D_xor h2 (hv j j.2)
    (burnsideF48t_gf4Mul_lt (hu j j.2) hslt), burnsideF48t_gf4D_mul h2 hω (hu j j.2) hslt]
  ring

theorem burnsideF48t_u52_dv_inj (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) {a b : Array ℕ}
    (ha5 : a.size = 5) (hb5 : b.size = 5) (ha : burnsideF48t_u52Small a)
    (hb : burnsideF48t_u52Small b) (h : burnsideF48t_u52dv ω a = burnsideF48t_u52dv ω b) :
    a = b := by
  apply Array.ext (by rw [ha5, hb5])
  intro j hj1 hj2
  rw [ha5] at hj1
  have e := burnsideF48t_gf4D_inj h2 hω (ha j hj1) (hb j hj1) (congrFun h ⟨j, hj1⟩)
  rwa [getElem!_pos a j (by rw [ha5]; exact hj1), getElem!_pos b j hj2] at e

end Vectors

section Iso

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem burnsideF48t_u52_card_SU (h : UnitaryFieldData 2 1 K) :
    Nat.card ↥(StatedSU 5 (2 ^ 1) K) = 13685760 := by
  have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 5) (by norm_num)
  have hp : ∏ i ∈ Finset.Icc 2 5, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 13365 := by decide
  rw [hp] at hc
  norm_num at hc
  exact_mod_cast hc

theorem burnsideF48t_u52_bar (h : UnitaryFieldData 2 1 K) (c : K) : h.bar c = c ^ 2 := by
  rw [UnitaryFieldData.bar_apply, pow_one]

theorem burnsideF48t_u52_scalars (h : UnitaryFieldData 2 1 K) :
    (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 1) K) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hs
  rw [Subgroup.mem_subgroupOf] at hs
  obtain ⟨l, hl⟩ := hs
  have hl' : Matrix.GeneralLinearGroup.scalar (Fin 5) l = g := hl
  have hg' := hg
  rw [show StatedSU 5 (2 ^ 1) K = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 5 from rfl,
    CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, ← hl',
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hg'
  obtain ⟨hdet, hu⟩ := hg'
  rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have h00 := congrFun (congrFun hu 0) 0
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_eq, Matrix.one_apply_eq, burnsideF48t_u52_bar h] at h00
  have hl3 : (l : K) ^ 3 = 1 := by rw [← h00]; ring
  have hl1 : (l : K) = 1 := by
    have hl2 : (l : K) ^ 2 = 1 := by
      have : (l : K) ^ 5 = (l : K) ^ 3 * (l : K) ^ 2 := by ring
      rw [hdet, hl3, one_mul] at this
      exact this.symm
    calc (l : K) = (l : K) * (l : K) ^ 2 := by rw [hl2, mul_one]
      _ = (l : K) ^ 3 := by ring
      _ = 1 := hl3
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  show g = 1
  rw [← hl', show l = 1 from Units.ext hl1, map_one]

end Iso

end CFSG.ASVolI

module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.HFL3Cent
public import CFSG.Quasithin.Background.HFL3Four
public import CFSG.Quasithin.Background.HFL3Six
public import CFSG.Quasithin.SteinbergCBTwistedField
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix Tri
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def rTr (hK : Nat.card K = (2 ^ n) ^ 2) : MulAut (HMod n K) :=
  rhoT hK (trGL (0 : Fin 3) 2 (by decide) (1 : K))

theorem rhoT_trGL_fix_of_entries (hK : Nat.card K = (2 ^ n) ^ 2) {c : K} (hc : bar n c = c)
    {X : HMod n K} (h21 : mat X 2 1 = 0) (h22 : mat X 2 2 = 0) (h12 : mat X 1 2 = 0)
    (h02 : bar n (mat X 0 2) = mat X 0 2) :
    rhoT hK (trGL (0 : Fin 3) 2 (by decide) c) X = X := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h20 : mat X 2 0 = mat X 0 2 := (herm_apply X 2 0).symm.trans h02
  apply mat_injective
  rw [mat_rhoT, tw, coe_trGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.single_apply,
      h21, h22, h12, h20, hc]
  · linear_combination (c * mat X 0 2) * h2

theorem mem_fixV_rTr (hK : Nat.card K = (2 ^ n) ^ 2) {X : HMod n K} :
    X ∈ fixV (Subgroup.zpowers (rTr hK)) ↔
      mat X 2 1 = 0 ∧ mat X 2 2 = 0 ∧ mat X 1 2 = 0 ∧ bar n (mat X 0 2) = mat X 0 2 := by
  rw [mem_fixV_zpowers_iff]
  constructor
  · intro h
    exact fix_trGL_entries hK h
  · rintro ⟨h21, h22, h12, h02⟩
    exact rhoT_trGL_fix_of_entries hK (map_one _) h21 h22 h12 h02

theorem rk_fixV_rTr (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    rk ↥(fixV (Subgroup.zpowers (rTr hK))) = 5 * n := by
  classical
  let Fq := {b : K // bar n b = b}
  let mk : Fq × Fq × K × Fq → HMod n K := fun p =>
    mkH !![p.1.1, p.2.2.1, p.2.2.2.1; bar n p.2.2.1, p.2.1.1, 0; p.2.2.2.1, 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjM, p.1.2, p.2.1.2, p.2.2.2.2, bar_bar hK])
  let e : ↥(fixV (Subgroup.zpowers (rTr hK))) ≃ Fq × Fq × K × Fq :=
    { toFun := fun X => (⟨mat (X : HMod n K) 0 0, herm_apply _ 0 0⟩,
        ⟨mat (X : HMod n K) 1 1, herm_apply _ 1 1⟩, mat (X : HMod n K) 0 1,
        ⟨mat (X : HMod n K) 0 2, ((mem_fixV_rTr hK).1 X.2).2.2.2⟩)
      invFun := fun p => ⟨mk p, (mem_fixV_rTr hK).2 ⟨by simp [mk, mat_mkH],
        by simp [mk, mat_mkH], by simp [mk, mat_mkH], by simp [mk, mat_mkH, p.2.2.2.2]⟩⟩
      left_inv := fun X => by
        obtain ⟨h21, h22, h12, h02⟩ := (mem_fixV_rTr hK).1 X.2
        have h10 : mat (X : HMod n K) 1 0 = bar n (mat (X : HMod n K) 0 1) :=
          (herm_apply _ 1 0).symm
        have h20 : mat (X : HMod n K) 2 0 = mat (X : HMod n K) 0 2 :=
          (herm_apply _ 2 0).symm.trans h02
        apply Subtype.ext
        apply mat_injective
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mk, mat_mkH, h21, h22, h12, h02, h10, h20]
      right_inv := fun p => by
        simp [mk, mat_mkH] }
  have h5 : 2 ^ n * (2 ^ n * ((2 ^ n) ^ 2 * 2 ^ n)) = 2 ^ (5 * n) := by ring
  rw [rk, Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_prod, card_fixed hn hK, hK,
    h5, padicValNat.prime_pow]

theorem rhoT_trGL_fixes (hK : Nat.card K = (2 ^ n) ^ 2) {c : K} (hc : bar n c = c)
    {X : HMod n K} (hX : X ∈ fixV (Subgroup.zpowers (rTr hK))) :
    rhoT hK (trGL (0 : Fin 3) 2 (by decide) c) X = X := by
  obtain ⟨h21, h22, h12, h02⟩ := (mem_fixV_rTr hK).1 hX
  exact rhoT_trGL_fix_of_entries hK hc h21 h22 h12 h02

theorem eq_trGL_of_cent (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {x : MulAut (HMod n K)} (hx : x ∈ norm hK)
    (hfix : ∀ v ∈ fixV (Subgroup.zpowers (rTr hK)), x v = v) :
    ∃ c : K, bar n c = c ∧ x = rhoT hK (trGL (0 : Fin 3) 2 (by decide) c) := by
  have hQ : SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) (1 : K) ∈ Q2 K :=
    transvection02_mem_Q2 1
  have hblk : ∀ X ∈ blkW n K, X ∈ fixV (Subgroup.zpowers (rTr hK)) := by
    intro X hX
    rw [mem_fixV_zpowers_iff]
    have := blkW_le_fixV hQ hK hX
    rw [rho_transvection] at this
    exact this
  have hpt : ∀ v : Fin 3 → K, v 2 = 0 → x (pt hK v) = pt hK v := fun v hv =>
    hfix _ (hblk _ (pt_mem_blkW hK hv))
  have hli : LinearIndependent K ![(Pi.single 0 1 : Fin 3 → K), Pi.single 1 1] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    exact ⟨h0, h1⟩
  obtain ⟨D, α, hxD, -, -, -⟩ := eq_rhoT_of_fix_line hn hK hx hli
    (fun c => hpt _ (by simp)) (hpt _ (by simp))
  subst hxD
  have h2 : rhoT hK D (e02s n) = e02s n :=
    hfix _ (mem_fixV_zpowers_iff.2 (fix_trGL02 hK).2.2.2)
  obtain ⟨c, hc, hD⟩ := eq_root_of_fix hK (y := D) (hpt _ (by simp)) (hpt _ (by simp))
    (hpt _ (by simp)) h2
  exact ⟨c, hc, hD⟩

end CFSG.Quasithin.RonanH44

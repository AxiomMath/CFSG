module

public import CFSG.Quasithin.Background.SmithB45ExcSylow
public import CFSG.Quasithin.Background.SmithB45ExcOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import Certificates.Certificate260381

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.Quasithin CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.Native
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.X1.J4Inv
  CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement

theorem j4C11_check : eqRows (powRows (C11 ()) 11) idRows = true ∧
    eqRows (C11 ()) idRows = false ∧ wfRows (C11 ()) = true :=
  Certificates.certificate260381

@[expose] noncomputable def gW11 : J := a * b * a

@[expose] noncomputable def c11 : J := eta uJ 11 1 * (gW11⁻¹ * eta uJ 11 1 * gW11)

theorem Mx_c11 (hF : J4Facts) : Mx c11 = rowsMatrix (C11 ()) := by
  have hM := hF.mat
  have hg0 := Mx_gEl hM (show 0 < 3 by norm_num)
  have hg1 := Mx_gEl hM (show 1 < 3 by norm_num)
  have e0 : gEl 0 = a := by simp [gEl]
  have e1 : gEl 1 = b := by simp [gEl]
  rw [e0] at hg0
  rw [e1] at hg1
  have hinv : gW11⁻¹ = a⁻¹ * b⁻¹ * a⁻¹ := by unfold gW11; group
  rw [c11, hinv, gW11]
  simp only [map_mul]
  rw [Mx_etaR hM, hg0.1, hg1.1, hg0.2, hg1.2]
  unfold C11
  simp only [rowsMatrix_mulRows]
  rfl

theorem c11_pow (hF : J4Facts) : c11 ^ 11 = 1 := pow_eq_one_of_rows (Mx_c11 hF) j4C11_check.1

theorem c11_ne (hF : J4Facts) : c11 ≠ 1 := by
  intro h1
  have h2 : rowsMatrix (C11 ()) = rowsMatrix idRows := by
    rw [← Mx_c11 hF, h1, map_one, rowsMatrix_idRows]
  obtain ⟨hs1, hw1⟩ := wfRows_spec j4C11_check.2.2
  obtain ⟨hs2, hw2⟩ := wfRows_spec Z11_wf.2
  exact rowsMatrix_ne_of_eqRows_false hs1 hs2 hw1 hw2 j4C11_check.2.1 h2

section Moved

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_hundred_le_index_J
    (hW : ∀ w : W, w * w = 1) (σ : J →* MulAut W) (hσ : Function.Injective σ) {g : J}
    (hg : g ^ 11 = 1) (hg1 : g ≠ 1) : 2 ^ 100 ≤ (fixV (Subgroup.zpowers (σ g))).index := by
  have hF := j4Facts
  obtain ⟨h1, -, h3, h4, h5, -, -, -⟩ := witness11 hF
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hz : ⁅xE, yE⁆ = zE := by rw [commutatorElement_def]; rfl
  have hzx : Commute ⁅xE, yE⁆ xE := by rw [hz]; exact h4.symm
  have hzy : Commute ⁅xE, yE⁆ yE := by rw [hz]; exact h5.symm
  have hG : ¬ 11 ^ 4 ∣ Nat.card J := by rw [card_J hF]; norm_num
  have h := two_pow_le_index_of_pow_eq_one (p := 11) (by norm_num) h1 (yE_pow hF)
    (by rw [hz]; exact h3) hzx hzy hG hW σ hσ hg hg1
  rw [orderOf_two_zmod_11] at h
  exact h

theorem two_pow_fifty_le_index_eta1
    (hW : ∀ w : W, w * w = 1) (σ : J →* MulAut W) (hσ : Function.Injective σ) :
    2 ^ 50 ≤ (fixV (Subgroup.zpowers (σ (eta uJ 11 1)))).index := by
  have hF := j4Facts
  have hc := two_pow_hundred_le_index_J hW σ hσ (c11_pow hF) (c11_ne hF)
  set i := (fixV (Subgroup.zpowers (σ (eta uJ 11 1)))).index with hi
  have hmul : (fixV (Subgroup.zpowers (σ c11))).index ≤ i * i := by
    have h1 : σ c11 = σ (eta uJ 11 1) *
        ((σ gW11)⁻¹ * σ (eta uJ 11 1) * ((σ gW11)⁻¹)⁻¹) := by
      rw [c11, map_mul, map_mul, map_mul, map_inv, inv_inv]
    rw [h1]
    refine (index_fixV_mul_le _ _).trans ?_
    rw [index_fixV_conj]
  by_contra hlt
  push Not at hlt
  have h2 : i * i < 2 ^ 50 * 2 ^ 50 := Nat.mul_lt_mul'' hlt hlt
  have h3 : (2 : ℕ) ^ 50 * 2 ^ 50 = 2 ^ 100 := by norm_num
  omega

theorem moved50_J
    (hW : ∀ w : W, w * w = 1) (σ : J →* MulAut W) (hσ : Function.Injective σ)
    (t : J) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    2 ^ 50 ≤ (fixV (Subgroup.zpowers (σ t))).index := by
  have hF := j4Facts
  rcases inv_conj_root hF ht2 ht1 with h | h
  · rw [index_conj_J σ h]
    exact two_pow_fifty_le_index_eta1 hW σ hσ
  · have hconj : IsConj a t := (isConj_eta_three_a hF).symm.trans h
    rw [index_conj_J σ hconj]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := witness11 hF
    have hsq := a_mul_a hF.mat
    have hE := two_pow_hundred_le_index_sq hW (X := σ xE) (Y := σ yE) (Zm := σ zE) (T := σ a)
      (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])
      (fun h => h3 (hσ (by rw [h, map_one])))
      (by rw [← map_mul, ← map_mul, h4]) (by rw [← map_mul, ← map_mul, h5])
      (by have := congrArg σ h6; simpa [map_mul, map_inv] using this)
      (by rw [← map_mul, hsq, map_one])
      (by have := congrArg σ h7; simpa [map_mul, map_inv] using this)
      (by rw [← map_mul, ← map_mul, h8])
    by_contra hlt
    push Not at hlt
    have : (fixV (Subgroup.zpowers (σ a))).index ^ 2 < (2 ^ 50) ^ 2 :=
      Nat.pow_lt_pow_left hlt (by norm_num)
    have h100 : ((2 : ℕ) ^ 50) ^ 2 = 2 ^ 100 := by norm_num
    omega

end Moved

theorem j4MovedRank50_aux :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ σ : NativeSporadic.J4 →* MulAut W, Function.Injective σ →
        ∀ t : NativeSporadic.J4, t ≠ 1 → t * t = 1 →
          2 ^ 50 ≤ (fixV (Subgroup.zpowers (σ t))).index := by
  intro W _ _ hW σ hσ t ht1 ht2
  have e : NativeSporadic.J4 ≃* J := seedEquiv j4Facts.mat
  exact @moved_of_mulEquiv_pow NativeSporadic.J4 J inferInstance inferInstance e 50
    (fun W _ _ hW σ hσ t ht1 ht2 => moved50_J hW σ hσ t ht1 ht2) W _ _ hW σ hσ t ht1 ht2

theorem j4MovedRank50 :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ σ : NativeSporadic.Carrier .J4 →* MulAut W, Function.Injective σ →
        ∀ t : NativeSporadic.Carrier .J4, t ≠ 1 → t * t = 1 →
          2 ^ 50 ≤ (fixV (Subgroup.zpowers (σ t))).index :=
  j4MovedRank50_aux

theorem sporadicExclusion2F_J4 :
    SporadicExclusion2F .J4 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel
  exact weight2_lt_of_outer_odd_cover hW hq.1 hirr hE hEne hEel e (r := 17) (ρ := 50)
    (by norm_num) j4OuterOdd (fun E _ _ _ π hπ hC hodd => j4_cover E π hπ hC hodd) j4TwoRank
    j4MovedRank50

end CFSG.Quasithin.B45Exc

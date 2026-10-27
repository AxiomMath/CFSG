module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowGen
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

variable {W : Type} [CommGroup W] [Finite W]

theorem le_rkIdx_of_heisCfg (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hO2 : O2Trivial L) {S : Type} [Group S] (e : CQ L ≃* S) {ρ p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hρ : 2 * ρ < (p - 1) * p ^ n * orderOf (2 : ZMod p) + 2)
    (hgen : ∀ t : S, t * t = 1 → t ≠ 1 → ∃ (x y : Fin (n + 1) → S) (z : S),
      HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹)
    {t : MulAut W} (htL : t ∈ L) (hto : orderOf t = 2) :
    ρ ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have ht2 : t * t = 1 := by
    rw [← sq, ← hto]
    exact pow_orderOf_eq_one t
  have hb2 : centerQuotientHom e ⟨t, htL⟩ * centerQuotientHom e ⟨t, htL⟩ = 1 := by
    rw [← map_mul, ← map_one (centerQuotientHom e)]
    congr 1
    exact Subtype.ext ht2
  have hK := ker_centerQuotientHom e
  have hb1 : centerQuotientHom e ⟨t, htL⟩ ≠ 1 := by
    intro h
    have hc : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := hK ▸ MonoidHom.mem_ker.2 h
    exact redHom_ne_one_of_o2Trivial hO2 e htL hto ((redHom_eq_one_iff L e _).2 hc)
  obtain ⟨x, y, z, h, hy, htx⟩ := hgen _ hb2 hb1
  have hKp : ¬ p ∣ Nat.card (centerQuotientHom e).ker := by rw [hK]; exact hZ
  obtain ⟨x', y', z', h', hx'1, -, -, -⟩ := HeisCfg.exists_lift (centerQuotientHom e)
    (centerQuotientHom_surjective e) hK.le hKp h hy
  have hinv : (⟨t, htL⟩ : ↥L) * x' 0 * (⟨t, htL⟩ : ↥L)⁻¹ = (x' 0)⁻¹ := by
    refine eq_of_map_eq_of_pow_eq_one (centerQuotientHom e) hK.le hKp
      (by rw [conj_pow, h'.xp 0, mul_one, mul_inv_cancel]) (by rw [inv_pow, h'.xp 0, inv_one]) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hx'1]
    exact htx
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hinv' : t * L.subtype (x' 0) * t⁻¹ = (L.subtype (x' 0))⁻¹ := by
    have := congrArg L.subtype hinv
    simp only [map_mul, map_inv] at this
    exact this
  have h1 := two_pow_le_index_sq_of_heisCfg hW hp2 (h'.map L.subtype hz') ht2 hinv'
  obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hW (Subgroup.zpowers t)
  have h2 := two_pow_le_of_pow_le ⟨m, hm⟩ h1 hρ
  rw [hm] at h2
  have hρm : ρ ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  rwa [rkIdx, hm, padicValNat.prime_pow]

theorem le_mParam_of_heisCfg (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hO2 : O2Trivial L) (hYL : ∀ t ∈ Y, orderOf t = 2 → t ∈ L) {S : Type}
    [Group S] (e : CQ L ≃* S) (h2S : 2 ∣ Nat.card S) {ρ p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hρ : 2 * ρ < (p - 1) * p ^ n * orderOf (2 : ZMod p) + 2)
    (hgen : ∀ t : S, t * t = 1 → t ≠ 1 → ∃ (x y : Fin (n + 1) → S) (z : S),
      HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹) :
    ρ ≤ E3.mParam Y := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hEven : Even (Nat.card Y) := by
    rw [even_iff_two_dvd]
    have hS : Nat.card S ∣ Nat.card L := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    exact (h2S.trans hS).trans (Subgroup.card_dvd_of_le hLY)
  unfold E3.mParam
  rw [if_pos hEven]
  refine le_csInf ?_ ?_
  · obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
    exact ⟨_, (t : MulAut W), t.2, by rwa [Subgroup.orderOf_coe], rfl⟩
  · rintro n' ⟨t, htY, hto, rfl⟩
    exact le_rkIdx_of_heisCfg hW' hO2 e hp2 hZ hρ hgen (hYL t htY hto) hto

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

module

public import CFSG.LocalAnalysis.StandardType.FS81.GoldLayerSetup
import CFSG.LocalAnalysis.StandardType.FS81.GoldLayerTypeI
import CFSG.LocalAnalysis.StandardType.FS81.GoldLayerTypeII

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Goldschmidt

variable {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y} {B L : Subgroup Y}

theorem goldLayer_compFacts
    (D : GoldLayerFacts Y S B) (hL : IsComponentOf L ⊤) : G310.CompFacts B L := by
  have hL' : IsComponentOf L (normalClosureIn ⊤ B) := by
    rw [goldLayer_normalClosureIn_top D.hyp.gen]
    exact hL
  exact G310.compFacts D.hyp.oddCore D.sstar hL'

theorem goldLayer_inf_eq
    (D : GoldLayerFacts Y S B) (hL : IsComponentOf L ⊤) {P : Sylow 2 Y} (hBP : B ≤ P) :
    (P : Subgroup Y) ⊓ L = (S : Subgroup Y) ⊓ L := by
  have hF := goldLayer_compFacts D hL
  rcases hF.types with hI | hII
  · exact goldLayer_inf_eq_of_typeI D hL hF hI hBP
  · exact goldLayer_inf_eq_of_typeII D hL hF hII hBP

theorem goldLayer_exists_odd_of_not_le {T : Subgroup Y}
    (hT : fusionIsSylowIn 2 T L) {y : Y} (hyL : y ∈ L)
    (hyN : y ∈ Subgroup.normalizer (T : Set Y)) (hyT : y ∉ T) :
    ∃ y' ∈ L, y' ∈ Subgroup.normalizer (T : Set Y) ∧ y' ≠ 1 ∧ Odd (orderOf y') := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hdvd : 2 ^ a ∣ orderOf y := hord ▸ dvd_mul_right _ _
  have hord' : orderOf (y ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) hdvd, hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  refine ⟨y ^ 2 ^ a, L.pow_mem hyL _, (Subgroup.normalizer (T : Set Y)).pow_mem hyN _, ?_, ?_⟩
  · intro h1
    let Z : Subgroup Y := Subgroup.zpowers y
    have hy2 : IsPGroup 2 Z := by
      obtain ⟨k, -, hk⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hZT : Z ≤ Subgroup.normalizer (T : Set Y) := by
      simpa [Z] using Subgroup.zpowers_le.mpr hyN
    have hsup : IsPGroup 2 (T ⊔ Z : Subgroup Y) :=
      hT.2.1.to_sup_of_normal_left' hy2 hZT
    have hle : T ⊔ Z ≤ L :=
      sup_le hT.1 (by simpa [Z] using Subgroup.zpowers_le.mpr hyL)
    have heq := hT.2.2 (T ⊔ Z) hle hsup le_sup_left
    have hy_sup : y ∈ T ⊔ Z :=
      Subgroup.mem_sup_right (by simpa [Z] using Subgroup.mem_zpowers y)
    exact hyT (heq ▸ hy_sup)
  · rw [hord']
    exact hm

theorem goldLayer_mem_normalizer_B (D : GoldLayerFacts Y S B) (hF : G310.CompFacts B L) {y : Y}
    (hyL : y ∈ L) (hyN : y ∈ Subgroup.normalizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y)) :
    y ∈ Subgroup.normalizer (B : Set Y) := by
  have key : ∀ z : Y, z ∈ L →
      z ∈ Subgroup.normalizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) →
      ∀ b ∈ B, z * b * z⁻¹ ∈ B := by
    intro z hzL hzN b hb
    have hBL : (B ⊓ L).map (MulAut.conj z).toMonoidHom ≤ B := by
      rintro _ ⟨c, hc, rfl⟩
      have hcSL : c ∈ (S : Subgroup Y) ⊓ L := ⟨D.hyp.le hc.1, hc.2⟩
      have hconj : z * c * z⁻¹ ∈ (S : Subgroup Y) ⊓ L :=
        (Subgroup.mem_normalizer_iff.mp hzN c).mp hcSL
      have hS : z * c * z⁻¹ ∈ (S : Subgroup Y) := hconj.1
      have hmem := D.hyp.closed c hc.1 z⁻¹ (by simpa using hS)
      simpa [MulAut.conj_apply] using hmem
    have hBC : (B ⊓ Subgroup.centralizer (L : Set Y)).map (MulAut.conj z).toMonoidHom ≤ B := by
      rintro _ ⟨c, hc, rfl⟩
      have hcomm : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc.2 z hzL
      have hzc : z * c * z⁻¹ = c := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have hmem : c ∈ B := hc.1
      simpa [MulAut.conj_apply, hzc] using hmem
    have hb' : b ∈ B ⊓ L ⊔ B ⊓ Subgroup.centralizer (L : Set Y) := by
      rw [← hF.split]
      exact hb
    have hbmap : MulAut.conj z b ∈ (B ⊓ L ⊔ B ⊓ Subgroup.centralizer (L : Set Y)).map
        (MulAut.conj z).toMonoidHom := Subgroup.mem_map_of_mem _ hb'
    rw [Subgroup.map_sup] at hbmap
    have hmem := sup_le hBL hBC hbmap
    simpa [MulAut.conj_apply] using hmem
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact key y hyL hyN b hb
  · intro hb
    have hy'L : y⁻¹ ∈ L := L.inv_mem hyL
    have hy'N : y⁻¹ ∈ Subgroup.normalizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) :=
      (Subgroup.normalizer _).inv_mem hyN
    have hmem := key y⁻¹ hy'L hy'N (y * b * y⁻¹) hb
    rwa [show y⁻¹ * (y * b * y⁻¹) * (y⁻¹)⁻¹ = b by group] at hmem

theorem goldLayer_exists_odd_normalizer
    (D : GoldLayerFacts Y S B) (hL : IsComponentOf L ⊤) :
    ∃ y ∈ L, y ∈ Subgroup.normalizer (B : Set Y) ∧ y ≠ 1 ∧ Odd (orderOf y) := by
  have hF := goldLayer_compFacts D hL
  have hLn := goldLayer_comp_normal D hL
  obtain ⟨y, hyL, hyN, hyS⟩ : ∃ y ∈ L,
      y ∈ Subgroup.normalizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) ∧
        y ∉ (S : Subgroup Y) := by
    rcases hF.types with hI | hII
    · exact goldLayer_exists_not_le_of_typeI D hL hF hI
    · exact goldLayer_exists_not_le_of_typeII D hL hF hII
  have hyT : y ∉ (S : Subgroup Y) ⊓ L := fun h => hyS h.1
  obtain ⟨y', hy'L, hy'N, hy'1, hy'o⟩ :=
    goldLayer_exists_odd_of_not_le (goldLayer_sylow_inf S hLn) hyL hyN hyT
  exact ⟨y', hy'L, goldLayer_mem_normalizer_B D hF hy'L hy'N, hy'1, hy'o⟩

end CFSG.StandardType.FrameRoute.FS81

end

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3ElevTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_normalizer_le_of_case11 (D : Data G) (h1217 : R1217 D) (h61 : UC6.R6_1 D)
    (h1610 : R16_10_2 D) (h169 : R16_9 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h11 : Case168_11 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hp : 7 ∈ D.sig := by
    rw [h11.2.2.2]
    exact Set.mem_singleton 7
  have hodd : Odd (Nat.card ↥(barSub V₀ V hV L)) := by
    have h7 : Nat.card ↥(barSub V₀ V hV L) = 7 := h11.1.2
    rw [h7]
    norm_num
  obtain ⟨g, hT⟩ := s16t_twoConj_of_odd D h1217 hV hc hodd h11.2.2.1
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let B : Subgroup (MulAut (Vtil V₀ V hV)) := A.map (MulAut.conj g).toMonoidHom
  let P : Subgroup (MulAut (Vtil V₀ V hV)) := A ⊔ B
  have hT' : S16n9bTwo Mb A g := hT
  have hAcyc : IsCyclic ↥A := h11.1.1
  have hAcard : Nat.card ↥A = 7 := h11.1.2
  obtain ⟨a, ha⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp hAcyc
  have haorder : orderOf a = 7 := by
    rw [← Nat.card_zpowers, ha]
    exact hAcard
  have ha7 : a ^ 7 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, haorder]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at haorder
    omega
  let b : MulAut (Vtil V₀ V hV) := (MulAut.conj g).toMonoidHom a
  have hb : Subgroup.zpowers b = B := by
    show Subgroup.zpowers ((MulAut.conj g).toMonoidHom a) = B
    rw [← MonoidHom.map_zpowers, ha]
  have hBcard : Nat.card ↥B = 7 := by
    have h1 : Nat.card ↥B = Nat.card ↥A := by
      rw [show B = A.map (MulAut.conj g).toMonoidHom from rfl]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    exact h1.trans hAcard
  have hborder : orderOf b = 7 := by
    rw [← Nat.card_zpowers, hb]
    exact hBcard
  have hb7 : b ^ 7 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hborder]
  have hamem : a ∈ A := by rw [← ha]; exact Subgroup.mem_zpowers a
  have hbmem : b ∈ B := by rw [← hb]; exact Subgroup.mem_zpowers b
  have hab : a * b = b * a := by
    have hAc : A ≤ Subgroup.centralizer (B : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hT'.comm
    exact ((Subgroup.mem_centralizer_iff.mp (hAc hamem)) b hbmem).symm
  have hbna : b ∉ Subgroup.zpowers a := by
    intro hb'
    have hle : B ≤ A := by
      rw [← hb, ← ha]
      exact Subgroup.zpowers_le.mpr hb'
    exact hT'.ne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hAcard.trans hBcard.symm)))
  obtain ⟨hEl, hcardEl⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers (p := 7) (a := a) (y := b)
      (by norm_num) ha7 hb7 ha1 hbna hab
  have hP_eq : P = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [ha, hb]
  have hElP : CFSG.Open.IsElemAbelian 7 P := by
    rw [hP_eq]
    exact hEl
  have hcardP : Nat.card ↥P = 7 ^ 2 := by
    rw [hP_eq]
    exact hcardEl
  have hPp : IsPGroup 7 ↥P := CFSG.Open.IsElemAbelian.isPGroup hElP
  have h7dvd : 7 ^ 2 ∣ Nat.card ↥P := by
    rw [hcardP]
  have hPc : ¬ IsCyclic ↥P :=
    s16c11_not_isCyclic_of_exponent (p := 7) (by norm_num) (fun x hx => hElP.2 x hx) h7dvd
  have hPM : P ≤ Mb := by
    refine sup_le hT'.le ?_
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [MulAut.conj_apply] using
      Mb.mul_mem (Mb.mul_mem hT'.mem (hT'.le hy)) (Mb.inv_mem hT'.mem)
  have hmap_le : ∀ φ ∈ Mb, P.map (MulAut.conj φ).toMonoidHom ≤ P := by
    intro φ hφ
    have hPsup : P = A ⊔ B := rfl
    rw [hPsup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rcases hT'.conj φ hφ with h1 | h1
      · rw [h1]; exact le_sup_left
      · rw [h1]; exact le_sup_right
    · have h1 : B.map (MulAut.conj φ).toMonoidHom =
          A.map (MulAut.conj (φ * g)).toMonoidHom :=
        s16n9b_map_conj_map_conj A g φ
      rcases hT'.conj (φ * g) (Mb.mul_mem hφ hT'.mem) with h2 | h2
      · rw [h1, h2]; exact le_sup_left
      · rw [h1, h2]; exact le_sup_right
  have hPN : Mb ≤ normalizer (P : Set (MulAut (Vtil V₀ V hV))) := by
    intro φ hφ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hmap_le φ hφ) ?_
    have h2 : P.map (MulAut.conj φ⁻¹).toMonoidHom ≤ P := hmap_le φ⁻¹ (Mb.inv_mem hφ)
    have h3 : P ≤ P.map (MulAut.conj φ).toMonoidHom := by
      have h4 := Subgroup.map_mono (f := (MulAut.conj φ).toMonoidHom) h2
      rwa [s16n9b_map_conj_map_conj P φ⁻¹ φ, mul_inv_cancel, s16n9b_map_conj_one] at h4
    exact h3
  exact s16c11_normalizer_le_of_routeF_normal D h61 h1610 h169 hV hc hp hPM hPp hPc hPN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

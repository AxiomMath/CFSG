module

public import CFSG.Quasithin.Background.SmithB42Sp4Real
public import CFSG.Quasithin.Background.SmithB42Sp4Nat
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB51LnB42

public section

namespace CFSG.Quasithin

namespace B42Sp4

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H

section Facts

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_fixV_map_congrHom {W : Type} [CommGroup W] (e : V ≃* W) (X : Subgroup (MulAut V)) :
    Nat.card ↥(fixV (X.map (congrHom e))) = Nat.card ↥(fixV X) := by
  rw [fixV_map_congrHom]
  exact Subgroup.card_map_of_injective e.injective

theorem two_thirds_le_rAV (hV : ∀ v : V, v ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hB : IsElemAbelian2 B) (hB1 : B ≠ ⊥)
    (h : Nat.card B ^ 2 * Nat.card ↥(fixV B) ^ 3 ≤ Nat.card V ^ 3) :
    (2 / 3 : ℚ) ≤ rAV B := by
  have hBc := B1.card_elemAbelian hB
  have hCc := card_eq_two_pow hV (fixV B)
  have hVc := card_eq_two_pow_rk hV
  have hsum := rk_add_rkIdx (fixV B)
  rw [hBc, hCc, hVc, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add] at h
  have h1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hpos : 0 < rk ↥B := IsA2.rk_pos (X := B) ⟨le_rfl, hB1, hB⟩
  unfold rAV
  rw [div_le_div_iff₀ (by norm_num) (by exact_mod_cast hpos)]
  have h2 : 2 * rk ↥B ≤ rkIdx (fixV B) * 3 := by omega
  exact_mod_cast h2

theorem natural_facts (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes L ⊤ ⊥) :
    (∀ B, IsFFStarOffender G B → B ≤ L) ∧ (∀ B, IsFFStarOffender G B → (2 / 3 : ℚ) ≤ rAV B) ∧
      ∃ R, IsFFStarOffender G R ∧ rAV R = 2 / 3 := by
  classical
  have : CharP K 2 := CFSG.QuasithinUnique.Setup.X7b.charP_two_of_card_pow hK
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia (StatedSp 2 K) hπ
  have hLe : L.map (congrHom e) = natImage (StatedSp 2 K) :=
    map_congrHom_eq_natImage (StatedSp 2 K) hπ.1 e he
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B42L2.le_normalizer_of_b4Hyp hHyp
  have hLG : L ≤ G := (FFC.b4hyp_data hHyp).1
  have hGe : G.map (congrHom e) ≤ natNorm (StatedSp 2 K) := by
    have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))) :
          Set (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))) :=
      Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
    rw [natNorm, ← hLe, ← h1]
    exact Subgroup.map_mono hGN
  have hcardV : Nat.card V = Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) := Nat.card_congr e.toEquiv
  have hinL : ∀ B, IsFFStarOffender G B → B ≤ L := by
    intro B hB
    by_contra hBL
    have hEN : B.map (congrHom e) ≤ natNorm (StatedSp 2 K) := (Subgroup.map_mono hB.1).trans hGe
    have hEel : IsElemAbelian2 (B.map (congrHom e)) :=
      (isElemAbelian2_map_congrHom e).2 hB.2.2.1
    have hEnot : ¬ B.map (congrHom e) ≤ natImage (StatedSp 2 K) := by
      intro h
      rw [← hLe, map_congrHom_le_iff] at h
      exact hBL h
    have hlt := FFC.Sp4Off.card_mul_card_fixV_lt hn hK hEN hEel hEnot
    have hff := B42L2.card_le_of_offender hB
    rw [card_map_congrHom, card_fixV_map_congrHom, ← hcardV] at hlt
    omega
  refine ⟨hinL, fun B hB => ?_, ?_⟩
  ·
    have hE : B.map (congrHom e) ≤ natImage (StatedSp 2 K) := by
      rw [← hLe]
      exact Subgroup.map_mono (hinL B hB)
    have hEel : IsElemAbelian2 (B.map (congrHom e)) :=
      (isElemAbelian2_map_congrHom e).2 hB.2.2.1
    have h := natImage_card_sq_mul_card_fixV_cube_le hE hEel
    rw [card_map_congrHom, card_fixV_map_congrHom, ← hcardV] at h
    exact two_thirds_le_rAV hV hB.2.2.1 hB.2.1 h
  ·
    obtain ⟨R, hRL, hRe⟩ := exists_eq_map_congrHom e (radImage_le.trans hLe.symm.le)
    refine ⟨R, ⟨hRL.trans hLG, ?_, ?_, fun B hBR => ?_⟩, ?_⟩
    · intro h
      apply radImage_ne_bot (K := K)
      rw [← hRe, h, Subgroup.map_bot]
    · rw [← isElemAbelian2_map_congrHom e, hRe]
      exact isElemAbelian2_radImage
    · have h1 := card_mul_card_fixV_le_of_le_radImage (K := K) (B := B.map (congrHom e))
        (by rw [← hRe]; exact Subgroup.map_mono hBR)
      rw [card_map_congrHom, card_fixV_map_congrHom, ← hRe, card_map_congrHom,
        card_fixV_map_congrHom] at h1
      exact h1
    · have hrk : rk ↥R = 3 * n := by
        rw [← rk_map_congrHom e, hRe, rk, card_radImage, hK, ← pow_mul, mul_comm]
        exact @padicValNat.prime_pow 2 ⟨Nat.prime_two⟩ _
      have hidx : rkIdx (fixV R) = 2 * n := by
        rw [← rkIdx_fixV_map_congrHom e, hRe]
        have h1 := (fixV (radImage K)).card_mul_index
        rw [card_fixV_radImage, card_stdMod, hK] at h1
        simp only [Fintype.card_sum, Fintype.card_fin] at h1
        have h2 : (fixV (radImage K)).index = 2 ^ (2 * n) := by
          have h3 : (2 ^ n) ^ 2 * (fixV (radImage K)).index = (2 ^ n) ^ 2 * (2 ^ n) ^ 2 := by
            rw [h1]
            ring
          rw [Nat.eq_of_mul_eq_mul_left (by positivity) h3, ← pow_mul, mul_comm]
        rw [rkIdx, h2]
        exact @padicValNat.prime_pow 2 ⟨Nat.prime_two⟩ _
      rw [rAV, hrk, hidx]
      have hn0 : (n : ℚ) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        omega
      push_cast
      field_simp

end Facts

end B42Sp4

theorem asB42Sp4Even_holds : AsB42Sp4Even := by
  intro V _ _ hV G L hHyp hP A hA
  obtain ⟨hZ, f, hf2, hmodel⟩ := hP
  have hnat := B42Sp4.binaryNaturalSp4_of_offender hV hHyp hZ hf2 hmodel hA
  obtain ⟨K, _, _, hK, hreal⟩ := hnat
  obtain ⟨hinL, hlow, R, hR, hrR⟩ := B42Sp4.natural_facts hV hHyp hf2 hK hreal
  have hJ : ffJ G = L :=
    le_antisymm (iSup₂_le fun B hB => hinL B hB) (B5.Ln.le_ffJ_of_center hHyp hZ hA)
  have hq : qOf G = ((2 / 3 : ℚ) : WithTop ℚ) :=
    qOf_eq_of_offenders hV (by norm_num) hlow ⟨R, hR, hrR.le⟩
  refine Or.inr (Or.inr (Or.inl ⟨⟨f, ?_, fun _ => hJ⟩, hq⟩))
  rw [hJ]
  exact ⟨K, inferInstance, inferInstance, hK, hreal⟩

end CFSG.Quasithin

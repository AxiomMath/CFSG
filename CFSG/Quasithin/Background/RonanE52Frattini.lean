module

public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.RonanE52

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem mQuot_le_of_card_le {D D₁ : Subgroup G} {n : ℕ} (hle : D₁ ≤ D)
    (hcard : Nat.card D ≤ 2 ^ n * Nat.card D₁) : E3.mQuot D D₁ ≤ n := by
  have h1 := Subgroup.relIndex_mul_card D₁ D
  rw [inf_eq_left.2 hle] at h1
  have h2 : D₁.relIndex D ≤ 2 ^ n := by
    have h3 : D₁.relIndex D * Nat.card D₁ ≤ 2 ^ n * Nat.card D₁ := by
      rw [h1]; exact hcard
    exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos
  have h0 : 0 < D₁.relIndex D := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' D D₁)
  unfold E3.mQuot
  have hd : 2 ^ padicValNat 2 (D₁.relIndex D) ∣ D₁.relIndex D := pow_padicValNat_dvd
  have hle2 : 2 ^ padicValNat 2 (D₁.relIndex D) ≤ 2 ^ n := (Nat.le_of_dvd h0 hd).trans h2
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle2

theorem pRank_eq_top_of_isSylow {P : Subgroup G} (hP : IsSylowIn 2 P ⊤) :
    CFSG.Open.pRank 2 P = CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian P
  have h1 := (isMaxElemAbelian_iff_corank_zero.mp hA₀).2.2
  have h2 := (isMaxElemAbelian_iff_corank_zero.mp (B6.isMaxElemAbelian_of_sylow hP hA₀)).2.2
  rw [pow_zero, mul_one] at h1 h2
  exact Nat.pow_right_injective le_rfl (h1.symm.trans h2)

private theorem isElemAbelianCorank_cjSub (g : G) {H A : Subgroup G} {i : ℕ}
    (hA : IsElemAbelianCorank H i A) : IsElemAbelianCorank (cjSub g H) i (cjSub g A) :=
  ⟨CFSG.Quasithin.cjSub_mono hA.1, CFSG.Quasithin.isElemAbelian_cjSub hA.2.1, by
    rw [CFSG.Quasithin.card_cjSub, CFSG.Quasithin.B2F.pRank_cjSub]; exact hA.2.2⟩

theorem cjSub_thompsonJi (g : G) (H : Subgroup G) (i : ℕ) :
    cjSub g (thompsonJi H i) = thompsonJi (cjSub g H) i := by
  apply le_antisymm
  · have h : thompsonJi H i ≤ cjSub g⁻¹ (thompsonJi (cjSub g H) i) := iSup₂_le fun A hA =>
      (cjSub_inv_cjSub g A).symm.le.trans (CFSG.Quasithin.cjSub_mono
        (le_iSup₂_of_le (cjSub g A) (isElemAbelianCorank_cjSub g hA) le_rfl))
    exact (CFSG.Quasithin.cjSub_mono h).trans (cjSub_cjSub_inv g _).le
  · refine iSup₂_le fun B hB => ?_
    have hB' : IsElemAbelianCorank H i (cjSub g⁻¹ B) := by
      have h := isElemAbelianCorank_cjSub g⁻¹ hB
      rwa [cjSub_inv_cjSub] at h
    have hJ : cjSub g⁻¹ B ≤ thompsonJi H i := le_iSup₂_of_le _ hB' le_rfl
    exact (cjSub_cjSub_inv g B).symm.le.trans (CFSG.Quasithin.cjSub_mono hJ)

theorem thompsonJi_le_thompsonJi_of_pRank_eq {S R : Subgroup G} (hSR : S ≤ R)
    (hr : CFSG.Open.pRank 2 S = CFSG.Open.pRank 2 R) (i : ℕ) :
    thompsonJi S i ≤ thompsonJi R i := by
  refine iSup₂_le fun A hA => ?_
  have hA' : IsElemAbelianCorank R i A := ⟨hA.1.trans hSR, hA.2.1, by rw [← hr]; exact hA.2.2⟩
  exact le_iSup₂_of_le A hA' le_rfl

end CFSG.Quasithin.RonanE52

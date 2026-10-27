module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.Quasithin.MS93.SkConcl

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_of_pCore_le_ker {G₀ L : Subgroup G} (hLG : L ≤ G₀) {Γ : Type*} [Group Γ]
    (α : ↥L →* Γ) (hα : Function.Surjective α) (hk : CFSG.pCore 2 ↥L ≤ α.ker) :
    Nat.card Γ ∣ Nat.card (↥G₀ ⧸ CFSG.pCore 2 ↥G₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ↥L →* ↥G₀ ⧸ CFSG.pCore 2 ↥G₀ :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥G₀)).comp (Subgroup.inclusion hLG) with hψ
  have hψk : ψ.ker ≤ CFSG.pCore 2 ↥L := by
    refine le_sSup ⟨MonoidHom.normal_ker ψ, ?_⟩
    have hk : ψ.ker = (CFSG.pCore 2 ↥G₀).comap (Subgroup.inclusion hLG) := by
      ext x
      simp [hψ, QuotientGroup.eq_one_iff]
    rw [hk]
    exact (isPGroup_cfsgPCore ↥G₀).comap_of_injective _ (Subgroup.inclusion_injective hLG)
  have h1 : α.ker.index ∣ ψ.ker.index := Subgroup.index_dvd_of_le (hψk.trans hk)
  rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hα,
    Subgroup.card_top] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card _)

theorem not_case3_of_g2Two {G₀ R L : Subgroup G} (h : PUHyp G₀ R L)
    (hG2 : IsG2Two (↥G₀ ⧸ CFSG.pCore 2 ↥G₀)) : ¬ MS93Case3 G₀ R L := by
  rintro ⟨hVX, k, F, _, _, α, hk, hF, hα, hn, -⟩
  have hmod := isModO2Surj_of_natural h hVX inf_le_right hα hn
  have hd := card_dvd_of_pCore_le_ker h.L_le α hα hmod.2.ge
  rw [hG2.1, LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    Nat.card_eq_fintype_card, hF] at hd
  have h4 : (2 : ℕ) ^ 8 ∣ ((2 : ℕ) ^ k) ^ (2 ^ 2) := by
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  have h8 : (2 : ℕ) ^ 8 ∣ 12096 := h4.trans ((dvd_mul_right _ _).trans hd)
  exact absurd h8 (by decide)

end CFSG.Quasithin.MS93

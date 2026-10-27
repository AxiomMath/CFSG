module

public import CFSG.LocalAnalysis.WeakClosure81.W19Chief
public import CFSG.LocalAnalysis.WeakClosure81.Eleven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_le_card_four {R : Subgroup G} (hR : IsPGroup 2 R) (hcard : 2 < Nat.card R) :
    ∃ R' : Subgroup G, R' ≤ R ∧ Nat.card R' = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR
  have hn2 : 2 ≤ n := by
    by_contra h
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card R := by rw [hn]; exact pow_dvd_pow 2 hn2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨K.map R.subtype, Subgroup.map_subtype_le K, ?_⟩
  rw [Subgroup.card_map_of_injective R.subtype_injective, hK]
  norm_num

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem rankThreeGamma_le_of_le_F (c : MinCex193 D V₀ V p X) {F R : Subgroup G} (hRV : R ≤ V)
    (hRF : R ≤ F) (hF : ⁅F, twoResidual (X ⊔ D.T)⁆ = ⊥) : rankThreeGamma 1 2 R ≤ D.M := by
  unfold rankThreeGamma GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQR, hQ1, rfl⟩
  have hQb : Q ≠ ⊥ := by
    obtain ⟨E, hEQ, -, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) Q
    rintro rfl
    have hE : E = ⊥ := le_bot_iff.1 hEQ
    rw [hE, Subgroup.card_bot] at hEc
    have h3 : 2 ^ 1 ≤ 2 ^ CFSG.Open.pRank 2 (⊥ : Subgroup G) :=
      Nat.pow_le_pow_right (by norm_num) hQ1
    omega
  have hQ2 : IsPGroup 2 Q :=
    (CFSG.Open.IsElemAbelian.isPGroup c.setting.isElemAbelian).to_le (hQR.trans hRV)
  have hXQ : X ≤ normalizer (Q : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Q : Set G))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : ⁅q, x⁆ ∈ ⁅F, twoResidual (X ⊔ D.T)⁆ :=
      Subgroup.commutator_mem_commutator (hRF (hQR hq)) (c.X_le_twoResidual hx)
    rw [hF, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  exact normalizer_le_of_uniqueMax (c.hyp.uniqueMax X le_rfl c.hyp.noncyclic) hQb hQ2 hXQ

theorem exists_four_group (c : MinCex193 D V₀ V p X) {E F B : Subgroup G} {g : G}
    (hE : Hyp198 D X E F) (hFE : F < E) (hEV : E ≤ V)
    (hB : B ∈ E3.gammaSet V 1 (conjSubgroup V g))
    (hAV : ⁅conjSubgroup V g, V⁆ ≤ conjSubgroup V g ⊓ V)
    (hcard : 2 < Nat.card ↥(commEB E F B)) :
    ∃ R : Subgroup G, R ≤ V ⊓ conjSubgroup V g ∧ Nat.card R = 4 ∧
      rankThreeGamma 1 2 R ≤ D.M := by
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hE.isElemAbelian hx hy
  have hBA : B ≤ conjSubgroup V g := hB.1
  have hEBV : eB E F B ≤ V := (eB_le E F B).trans hEV
  have hRV : commEB E F B ≤ V ⊓ conjSubgroup V g := by
    have h1 : ⁅eB E F B, B⁆ ≤ ⁅V, conjSubgroup V g⁆ := Subgroup.commutator_mono hEBV hBA
    rw [Subgroup.commutator_comm V (conjSubgroup V g)] at h1
    exact (h1.trans hAV).trans (inf_comm _ _).le
  have hRF : commEB E F B ≤ F := by
    refine Subgroup.commutator_le.2 fun e he b hb => ?_
    exact ((mem_eB_iff hE.F_le hEcomm).1 he).2 b hb
  have hR2 : IsPGroup 2 (commEB E F B) :=
    (CFSG.Open.IsElemAbelian.isPGroup c.setting.isElemAbelian).to_le (hRV.trans inf_le_left)
  obtain ⟨R, hRle, hR4⟩ := exists_le_card_four hR2 hcard
  exact ⟨R, hRle.trans hRV, hR4,
    c.rankThreeGamma_le_of_le_F (hRle.trans (hRV.trans inf_le_left)) (hRle.trans hRF) hE.comm_F⟩

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end

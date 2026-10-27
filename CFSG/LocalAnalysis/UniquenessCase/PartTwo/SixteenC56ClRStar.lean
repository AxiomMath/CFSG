module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43TI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R34

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem Q_eq_zero_of_mem_imgTil_of_normalizer (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    (h5 : R16_5 D) (h22 : R1622 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {m : ℕ} (hm : Case1633 D V₀ V hV L m)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = lBar V₀ V hV L)
    (hSK : Nat.card S.K = 2 ^ m) {p : ℕ} (hp : D.sig = {p}) {U : Subgroup G} (hUV : U ≤ V)
    (hUN : ¬ normalizer (U : Set G) ≤ D.M) {u : Vtil V₀ V hV}
    (hu : u ∈ imgTil V₀ V hV U) : S.Q u = 0 := by
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U u).1 hu
  by_contra hne
  have hC := (r16_34_coord D h61 hext h5 hS hm S hSω hSK hp hne).2
  have hx1 : x.val ≠ 1 := by
    intro h
    apply hne
    have : x = 1 := IntMod.val_injective h
    rw [this, map_one, S.Q_one]
  apply hUN
  intro y hy
  by_contra hyM
  have hyx : y * x.val * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hy x.val).1 hxU
  exact s16c1G43_conj_not_mem h22 hS x.val_mem hx1 hC hyM (hUV hyx)

private theorem le_rStarMV_of_forall_rk_imgTil_le (M : Subgroup G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {b c : ℕ} (hbc : b + c ≤ mSub V)
    (hb : ∀ U : Subgroup G, U ≤ V → ¬ normalizer (U : Set G) ≤ M →
      rk ↥(imgTil ⊥ V hV U) ≤ b) :
    (c : ℕ∞) ≤ rStarMV M V := by
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨hUV, hUN⟩ := hU
  have hinf : U ⊓ (⊥ : Subgroup G) = ⊥ := inf_bot_eq U
  have hmU : mSub U = rk ↥(imgTil ⊥ V hV U) := by
    have := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V U hV hUV
    rw [hinf] at this
    simpa [mSub, rk] using this
  have hq := mSub_eq_mQuot_add V U hV hUV
  have hbU := hb U hUV hUN
  exact_mod_cast (by omega : c ≤ E3.mQuot V U)

theorem c33_four_le_rStarMV (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    (h22 : R1622 D) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hm : Case1633 D ⊥ V hV L 2) : (4 : ℕ∞) ≤ rStarMV D.M V := by
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  have hsig : D.sig = {5} := by
    rcases hm with ⟨hc, -⟩ | ⟨-, h⟩
    · exact hc.2.2
    · omega
  have hrk8 : mSub V = 8 := by
    have h1 := rk_top_vtil_add_mSub ⊥ V hV bot_le
    rw [rk_top, rk, S.card_eq, hSK] at h1
    have h0 : mSub (⊥ : Subgroup G) = 0 := rk_bot
    rw [h0] at h1
    have h2 : padicValNat 2 ((2 ^ 2) ^ 4) = 8 := by
      rw [← pow_mul, padicValNat.prime_pow]
    omega
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact S.mul_self_eq_one w
  refine le_rStarMV_of_forall_rk_imgTil_le D.M hV (b := 4) (c := 4) (by omega) ?_
  intro U hUV hUN
  have hsing : ∀ u ∈ imgTil ⊥ V hV U, S.Q u = 0 := fun u hu =>
    Q_eq_zero_of_mem_imgTil_of_normalizer D h61 hext h5 h22 hS hm S hSω hSK hsig hUV hUN hu
  have hcard := S.card_le_of_totallySingular hsing
  rw [card_eq_two_pow hW2 (imgTil ⊥ V hV U), hSK, ← pow_mul] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard

theorem c33_lt_rStarMV (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    (h22 : R1622 D) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hm : Case1633 D ⊥ V hV L 2) : (2 : ℕ∞) < rStarMV D.M V :=
  lt_of_lt_of_le (by norm_num) (c33_four_le_rStarMV D h61 hext h5 h22 hS hm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

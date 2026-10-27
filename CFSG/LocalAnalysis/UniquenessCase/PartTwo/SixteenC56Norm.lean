module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56NormA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56NormB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56NormC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

include S in
theorem mul_self_eq_one (w : W) : w * w = 1 := by
  apply S.vec_injective
  rw [S.vec_mul, S.vec_one]
  exact CharTwo.add_self_eq_zero (S.vec w)

theorem Q_apply_eq_of_similitude {g : MulAut W} {c : S.K} (hc : ∀ w : W, S.Q (g w) = c * S.Q w)
    (hord : ∃ k : ℕ, g ^ 2 ^ k = 1) : ∀ w : W, S.Q (g w) = S.Q w := by
  obtain ⟨k, hk⟩ := hord
  have hpow : ∀ (j : ℕ) (w : W), S.Q ((g ^ j) w) = c ^ j * S.Q w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, hc, ih, pow_succ', mul_assoc]
  obtain ⟨w₀, hw₀⟩ := S.exists_Q_ne_zero
  have h1 : c ^ 2 ^ k = 1 := by
    have h := hpow (2 ^ k) w₀
    rw [hk, MulAut.one_apply] at h
    exact (mul_left_eq_self₀.1 h.symm).resolve_right hw₀
  have h2 : c = 1 := by
    have h3 : (c - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, h1, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (by positivity) |>.1 h3)
  intro w
  rw [hc, h2, one_mul]

theorem card_fixed_le_of_singular_commutator {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (S.omega : Set (MulAut W))) (hord : ∃ k : ℕ, g ^ 2 ^ k = 1)
    {w : W} (h1 : g w * w⁻¹ ≠ 1) (h0 : S.Q (g w * w⁻¹) = 0) :
    Nat.card {v : W // g v = v} ≤ Nat.card S.K ^ 2 := by
  obtain ⟨σ, hσ⟩ := S.exists_ringEquiv_of_mem_normalizer hg
  by_cases hσ1 : σ = RingEquiv.refl S.K
  · have hlin : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w) := by
      intro c w
      simpa [hσ1] using hσ c w
    obtain ⟨c, -, hc⟩ := S.exists_similitude_of_linear hg hlin
    exact S.card_fixed_le_of_isometry hlin (S.Q_apply_eq_of_similitude hc hord) h1 h0
  · exact S.card_fixed_le_of_semilinear hσ1 hσ

theorem rk_top_eq {m : ℕ} (hSK : Nat.card S.K = 2 ^ m) : rk (⊤ : Subgroup W) = 4 * m := by
  rw [rk_top, rk, S.card_eq, hSK, ← pow_mul, padicValNat.prime_pow]
  ring

end OmegaModel

variable {G : Type} [Group G] [Finite G]

theorem Mbar_le_normalizer_lBar {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) :
    Mbar D.M V₀ V hV ≤ Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) := by
  intro g hg
  by_contra hgn
  obtain ⟨t, -, -, -, -, -, hconj, -⟩ := hS.conc
  have hgn' : g ∉ Subgroup.normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) := by
    rwa [← hSω]
  have h := (hconj g hg hgn').2
  rw [← hSω, S.commSub_top_omega] at h
  have hfix := (commSub_eq_bot_iff.1 h)
  have hbot : S.omega.map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    refine MulEquiv.ext fun v => ?_
    exact hfix (Subgroup.mem_top v) x hx
  have hbot' := (Subgroup.map_eq_bot_iff_of_injective S.omega
    (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective (MulAut.conj g))).1 hbot
  exact hS.ne_bot (hSω.symm.trans hbot')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthHeis
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthIrr

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.Classical2 CFSG.SignalizerFunctorTheorem.CatalogBridge
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal.Orth

theorem sq_lt_two_pow (d : ℕ) (hd : 5 ≤ d) : d ^ 2 < 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    have h1 : 2 * d + 1 ≤ d ^ 2 := by nlinarith
    have h2 : (d + 1) ^ 2 = d ^ 2 + (2 * d + 1) := by ring
    have h3 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    omega

theorem orth_numerics {s q d m V : ℕ} (hs : 2 ≤ s) (hq : 2 ≤ q) (hd : 5 ≤ d)
    (hdq : d ≤ q ^ (d - 4)) (hm : d ≤ m + 4) (hlow : s ^ (q ^ m) ≤ V)
    (hup : V ≤ s ^ (d - 1) ∨ ∃ e : ℕ, e ≤ d ∧ V ≤ e ^ 2) : False := by
  have hN : d ≤ q ^ m := hdq.trans (Nat.pow_le_pow_right (by omega) (by omega))
  rcases hup with h | ⟨e, he, hVe⟩
  · have h1 : s ^ (q ^ m) ≤ s ^ (d - 1) := hlow.trans h
    have h2 := (Nat.pow_le_pow_iff_right hs).mp h1
    omega
  · have h1 : s ^ (q ^ m) ≤ e ^ 2 := hlow.trans hVe
    have h2 : e ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left he 2
    have h3 : d ^ 2 < 2 ^ d := sq_lt_two_pow d hd
    have h4 : 2 ^ d ≤ 2 ^ (q ^ m) := Nat.pow_le_pow_right (by norm_num) hN
    have h5 : 2 ^ (q ^ m) ≤ s ^ (q ^ m) := Nat.pow_le_pow_left hs _
    omega

section Main

variable {K : Type} [Field K] [Finite K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem matrixProjectiveDerived_simple {F : Type} [Field F] [Finite F]
    {Q' : QuadraticForm F (Fin d → F)} (hd : 0 < d) (hnd : (polarBilin Q').Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q' u = 0) :
    IsSimpleGroup (matrixProjectiveDerived Q') := by
  obtain ⟨-, -, -, hsimple, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  exact (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge Q' hd).isSimpleGroup

theorem nonLocalized_orthogonalSubfield_of_centralizer (hext : IsExtension k Q₀ Q)
    (hnd₀ : (polarBilin Q₀).Nondegenerate) (hnd : (polarBilin Q).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hd : 5 ≤ d) (hdq : d ≤ Nat.card k ^ (d - 4))
    (hcent : ∀ x : matrixProjectiveDerived Q,
      (∀ g : matrixDerived Q₀, x * matrixProjectiveProjection Q (inclHom k hext g) =
        matrixProjectiveProjection Q (inclHom k hext g) * x) → x = 1) :
    NonLocalized (incl k hext).range := by
  classical
  obtain ⟨r, hrK⟩ := CharP.exists K
  have hr : r.Prime := CharP.char_is_prime K r
  have : Fact r.Prime := ⟨hr⟩
  have hkr : CharP k r := (RingHom.charP_iff k.subtype k.subtype.injective r).mpr hrK
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  let P := orthProjData Q
  let φH := inclHom k hext
  have hrange : (P.π.comp φH).range = (incl k hext).range := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨matrixProjectiveProjection Q₀ g, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q₀ z
      exact ⟨g, rfl⟩
  have hsimple : IsSimpleGroup (P.π.comp φH).range := by
    rw [hrange]
    have := matrixProjectiveDerived_simple hd0 hnd₀ hT₀
    exact (MonoidHom.ofInjective (incl_injective k hext hd0)).symm.isSimpleGroup
  obtain ⟨P3, hP3⟩ := exists_hyp_triple' hnd₀ hT₀
  obtain ⟨m, A, Z, y, hdm, hAcomm, hArp, hZA, hcomm, ⟨z, hzZ, hz⟩, hdist⟩ :=
    exists_heisenberg_system (exists_matrixDerived_eichler hnd₀ hT₀) hnd₀ (P3 0) (P3 1)
      (hP3 0 1 (by decide)) (r := r)
  rw [← hrange]
  have : Finite A := inferInstance
  refine P.nonLocalized_of_heisenberg φH
    (fun W hW => orth_irreducible k hext hnd₀ hnd hT₀ W hW) hsimple hcent A Z hAcomm hArp hZA y
    hcomm ?_ ?_ ?_
  ·
    refine ⟨z, hzZ, fun hπ => ?_⟩
    obtain ⟨c, hc⟩ := (P.hker (φH z)).mp hπ
    have h1 : ((glIncl k z.val : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ vecIncl k (P3 0).f =
        (c : K) • vecIncl k (P3 0).f := by
      have : ((glIncl k z.val : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          Matrix.scalar (Fin d) (c : K) := hc
      rw [this]
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [mulVec_vecIncl] at h1
    have h2 : (z.val : Matrix (Fin d) (Fin d) k) *ᵥ (P3 0).f = (P3 0).f + (P3 1).e := by
      have h3 : matrixLinearIso (d := d) (K := k) z.val (P3 0).f = (P3 0).f + (P3 1).e := by
        rw [hz, eichler_apply (P3 0).Q_e (hP3 0 1 (by decide)).ee, (P3 0).polar_fe,
          (hP3 0 1 (by decide)).fe, (P3 1).Q_e]
        simp only [one_smul, zero_smul, add_zero, zero_mul, sub_zero]
      exact h3
    rw [h2, vecIncl_add] at h1
    have h4 := congrArg (fun v => polar Q v (vecIncl k (P3 1).f)) h1
    simp only [polar_add_left, polar_smul_left_eq, polar_vecIncl' k hext] at h4
    rw [(hP3 0 1 (by decide)).ff, (P3 1).polar_ef] at h4
    simp at h4
  · intro s _ F _ _ ξ h1 h2 h3 i j hij
    exact hdist F ξ h1 h2 h3 i j hij
  · intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hlow hup
    have hq0 : 2 ≤ Nat.card k := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hcardfun : Nat.card (Fin m → k) = Nat.card k ^ m := by
      simp [Nat.card_fun]
    rw [hcardfun] at hlow
    refine orth_numerics (V := Nat.card V) hs.two_le hq0 hd hdq hdm hlow ?_
    rcases hup with h | ⟨e, he, -, hle⟩
    · left
      rw [Fintype.card_fin] at h
      exact h
    · right
      rw [Fintype.card_fin] at he
      exact ⟨e, he, hle⟩

end Main

end CFSG.SignalizerFunctorTheorem.NonLocal.Orth

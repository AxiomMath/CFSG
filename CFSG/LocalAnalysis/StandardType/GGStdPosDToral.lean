module

public import CFSG.LocalAnalysis.StandardType.GGStdPosDTorus
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusModel
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalGroups.Orthogonal

namespace StdPosD

theorem exists_omega_lines {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {E : Subgroup (spinGroup (quadPlus n F))} (hE : IsElemAbelian p E)
    (hcard : p ^ n ≤ Nat.card E) :
    ∃ g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadPlus n F)
        (nondegenerate_polarBilin_quadPlus n F),
      ∀ x ∈ E, ∀ k : Fin n ⊕ Fin n, ∃ c : F,
        (g * spinAction (quadPlus n F) x * g⁻¹) (Pi.single k 1) =
          c • (Pi.single k 1 : Fin n ⊕ Fin n → F) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hnd := nondegenerate_polarBilin_quadPlus n F
  have : Finite Fˣ := Finite.of_injective (fun u : Fˣ => (u : F)) Units.val_injective
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
  have := GGOppRadOmega.finite_spinGroup_quadPlus (n := n) (K := F)
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hE.1.is_comm.comm }
  obtain ⟨g, hgO, χ, he, hf, -, -⟩ := TableBOrth.exists_orth_conj_weights hnd hp2 hζ
    (fun T hT => TableBOrth.finrank_le_of_singular_qPlus T hT)
    (TableBOrth.isHypFamily_single (fun k => TableBOrth.isHypCoord_qPlusForm k) Sum.inr_injective
      fun _ _ => Sum.inl_ne_inr)
    ((spinAction (quadPlus n F)).comp E.subtype)
    (fun x => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ x.1))
    (RootCentOmega.spinAction_quadPlus_injective.comp Subtype.val_injective)
    (fun x => Subtype.ext (hE.2 x x.2)) hcard
  have hdiag : ∀ x ∈ E, ∀ k : Fin n ⊕ Fin n, ∃ c : F,
      (g * spinAction (quadPlus n F) x * g⁻¹) (Pi.single k 1) =
        c • (Pi.single k 1 : Fin n ⊕ Fin n → F) := by
    rintro x hx (k | k)
    · exact ⟨_, he ⟨x, hx⟩ k⟩
    · exact ⟨_, hf ⟨x, hx⟩ k⟩
  set D := CFSG.RankThree.OrthogonalInvolutions.dicksonHom (quadPlus n F) hnd
  have hker : ∀ y : TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F), D y = 1 →
      (y : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) ∈
        CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadPlus n F) hnd := by
    intro y hy
    have h : y ∈ D.ker := hy
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker] at h
    exact h
  have hval : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by
    intro z
    rcases (show ∀ y : ZMod 2, y = 0 ∨ y = 1 by decide) (Multiplicative.toAdd z) with h | h
    · exact Or.inl (by simpa using congrArg Multiplicative.ofAdd h)
    · exact Or.inr (by simpa using congrArg Multiplicative.ofAdd h)
  rcases hval (D ⟨g, hgO⟩) with h1 | h1
  · exact ⟨g, hker _ h1, hdiag⟩
  set k₀ : Fin n := ⟨0, by omega⟩
  set a : Fin n ⊕ Fin n → F := Pi.single (.inl k₀) 1 + Pi.single (.inr k₀) 1 with ha
  have hQa : quadPlus n F a = 1 := (TableBOrth.isHypCoord_qPlusForm k₀).map_single_add
  have hQa0 : quadPlus n F a ≠ 0 := by rw [hQa]; exact one_ne_zero
  have hneg : ∀ v : Fin n ⊕ Fin n → F, -v = v := fun v =>
    neg_eq_of_add_eq_zero_right (by rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul])
  have hr : ∀ k : Fin n ⊕ Fin n, ∃ k' : Fin n ⊕ Fin n,
      reflect (quadPlus n F) a (Pi.single k 1) = Pi.single k' 1 := by
    rintro (j | j) <;> by_cases hj : j = k₀
    · refine ⟨.inr k₀, ?_⟩
      rw [hj, reflect_apply hQa0, polar_quadPlus_single_inl, hQa, ha]
      simp [sub_add_cancel_left, hneg]
    · refine ⟨.inl j, reflect_apply_of_polar_eq_zero ?_⟩
      rw [polar_quadPlus_single_inl, ha]
      simp [hj]
    · refine ⟨.inl k₀, ?_⟩
      rw [hj, reflect_apply hQa0, polar_quadPlus_single_inr, hQa, ha]
      simp [sub_add_cancel_right, hneg]
    · refine ⟨.inr j, reflect_apply_of_polar_eq_zero ?_⟩
      rw [polar_quadPlus_single_inr, ha]
      simp [hj]
  have hrr : ∀ v, reflect (quadPlus n F) a (reflect (quadPlus n F) a v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, reflect_mul_self]
    rfl
  set r : TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) :=
    ⟨reflect (quadPlus n F) a, reflect_mem_orthogonalGroup (quadPlus n F) a⟩
  have hDr : D r = Multiplicative.ofAdd 1 :=
    CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_reflect hnd hQa0
  refine ⟨reflect (quadPlus n F) a * g, hker (r * ⟨g, hgO⟩) ?_, fun x hx k => ?_⟩
  · rw [map_mul, hDr, h1, ← ofAdd_add]
    decide
  obtain ⟨k', hk'⟩ := hr k
  obtain ⟨c, hc⟩ := hdiag x hx k'
  refine ⟨c, ?_⟩
  have e1 : reflect (quadPlus n F) a * g * spinAction (quadPlus n F) x *
      (reflect (quadPlus n F) a * g)⁻¹ =
        reflect (quadPlus n F) a * (g * spinAction (quadPlus n F) x * g⁻¹) *
          reflect (quadPlus n F) a := by
    rw [mul_inv_rev, reflect_inv]
    simp only [mul_assoc]
  rw [e1, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hk', hc, map_smul, ← hk', hrr]

theorem exists_conj_le_ggTorus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {E : Subgroup (spinGroup (quadPlus n F))} (hE : IsElemAbelian p E)
    (hcard : p ^ n ≤ Nat.card E) :
    ∃ g : spinGroup (quadPlus n F),
      E.map (MulAut.conj g).toMonoidHom ≤ ggTorus (plusDatum n F hn) := by
  obtain ⟨g, hgΩ, hg⟩ := exists_omega_lines hn hp hp2 hpF hE hcard
  obtain ⟨h, hh⟩ := GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus hn hgΩ
  refine ⟨h, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine mem_ggTorus_of_lines hn fun k => ?_
  obtain ⟨c, hc⟩ := hg x hx k
  refine ⟨c, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, hh]
  exact hc

end StdPosD

end CFSG.StandardType

end

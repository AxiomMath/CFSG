module

public import CFSG.RankThree.LocalRank.ThetaPlaneCentralLine
public import CFSG.RankThree.Theta.PlaneAlphaHyperplaneIndependence
public import CFSG.RankThree.Theta.ThreeCoreComponentNormalization

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree.LocalRank Subgroup
open CFSG.Assembly.RankThreeEven (aschCore)

variable {X : Type*} [Group X]

theorem conjugate_inv_le_of_mem_normalizer {V : Subgroup X} {g : X}
    (hg : g ∈ normalizer (V : Set X)) : conjugate V g⁻¹ ≤ V := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact (mem_normalizer_iff.1 hg v).1 hv

variable [Finite X]

theorem card_eq_or_eq_of_two_le_pRank {p : ℕ} (hp : p.Prime) {A U : Subgroup X}
    (hAcard : Nat.card A = p ^ 3) (hUA : U ≤ A) (hU : 2 ≤ Assembly.pRank p U) :
    Nat.card U = p ^ 2 ∨ U = A := by
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hp).1 (hAcard ▸ card_dvd_of_le hUA)
  have hj2 : 2 ≤ j := by
    by_contra h
    have hle : Assembly.pRank p U ≤ 1 := SectionRank.pRank_le hp.one_lt fun E hEU _ =>
      calc Nat.card E ≤ Nat.card U := card_le_of_le hEU
        _ = p ^ j := hj
        _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  interval_cases j
  · exact Or.inl hj
  · exact Or.inr (eq_of_le_of_card_ge hUA (by rw [hj, hAcard]))

theorem part_two_local_quotient_alpha_normalizer {p : ℕ} (hp : p.Prime) (A : Subgroup X)
    (hA : CFSG.Assembly.IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hquot : ∀ a ∈ A, a ≠ 1 →
      thetaAlpha p ((A.subgroupOf (centralizer ({a} : Set X))).map
          (QuotientGroup.mk' (centralLine a))) ≤
        aschbacherSolvableCore p (centralizer ({a} : Set X) ⧸ centralLine a)) :
    (∀ B D : Subgroup X, B ≤ A → Nat.card B = p ^ 2 → D ≤ A → Nat.card D = p ^ 2 →
      thetaAlpha p B = thetaAlpha p D) ∧
    ∀ B : Subgroup X, B ≤ A → Nat.card B = p ^ 2 →
      aschCore 2 p A ≤ normalizer (thetaAlpha p B : Set X) := by
  have hlocal := (theta_plane_alpha_central_line_quotient_lifting hp A hA hAcard hquot).1
  have hind : ∀ B D : Subgroup X, B ≤ A → Nat.card B = p ^ 2 → D ≤ A → Nat.card D = p ^ 2 →
      thetaAlpha p B = thetaAlpha p D := fun B D hBA hB hDA hD =>
    theta_plane_alpha_hyperplane_independence hp A hA hAcard hlocal hBA hB hDA hD
  refine ⟨hind, fun B hBA hB => sSup_le ?_⟩
  have key : ∀ g : X, ∀ E : Subgroup X, E ≤ A → Nat.card E = p ^ 2 → conjugate E g ≤ A →
      g⁻¹ ∈ normalizer (thetaAlpha p B : Set X) := by
    intro g E hEA hE hEgA
    have hEg : Nat.card (conjugate E g) = p ^ 2 := by
      rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hE]
    have h : conjugate (thetaAlpha p B) g = thetaAlpha p B :=
      calc conjugate (thetaAlpha p B) g = conjugate (thetaAlpha p E) g := by
            rw [hind B E hBA hB hEA hE]
        _ = thetaAlpha p (conjugate E g) := thetaAlpha_conjugate hp E g
        _ = thetaAlpha p B := hind _ B hEgA hEg hBA hB
    exact mem_normalizer_of_map_conj_eq_self h
  rintro _ ⟨U, hUA, hU2, -, rfl⟩ g hg
  rcases card_eq_or_eq_of_two_le_pRank hp hAcard hUA hU2 with hUc | hUeq
  · have h := key g⁻¹ U hUA hUc ((conjugate_inv_le_of_mem_normalizer hg).trans hUA)
    rwa [inv_inv] at h
  · rw [hUeq] at hg
    have h := key g⁻¹ B hBA hB ((map_mono hBA).trans (conjugate_inv_le_of_mem_normalizer hg))
    rwa [inv_inv] at h

end CFSG.RankThree.Theta

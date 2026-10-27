module

public import CFSG.RankThree.PartOne.KF.R3Aux
public import CFSG.RankThree.PartOne.KF.G2Ctx

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {G : Type} [Group G]

namespace KFU

variable {p : ℕ} {K : Type} [Field K]

@[expose] def d4a0 : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩

@[expose] def d4a1 : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩

theorem fin_orbit_D4_cases (a : Fin TwistTag.D4.foldedTag.rank) : a = d4a0 ∨ a = d4a1 := by
  revert a
  decide

@[expose] noncomputable def d4tau (p : ℕ) (K : Type) [Field K]
    (a : Fin TwistTag.D4.foldedTag.rank) : MulAut (G2V p K) :=
  if a = d4a0 then g2s1 p K else g2s0 p K

theorem d4tau_zero : d4tau p K d4a0 = g2s1 p K := by simp [d4tau]

theorem d4tau_one : d4tau p K d4a1 = g2s0 p K := by
  have h : d4a1 ≠ d4a0 := by decide
  simp [d4tau, h]

theorem range_d4tau : Set.range (d4tau p K) = {g2s0 p K, g2s1 p K} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rcases fin_orbit_D4_cases a with rfl | rfl
    · exact Or.inr d4tau_zero
    · exact Or.inl d4tau_one
  · rintro (rfl | rfl)
    · exact ⟨d4a1, d4tau_one⟩
    · exact ⟨d4a0, d4tau_zero⟩

theorem closure_range_d4tau : Subgroup.closure (Set.range (d4tau p K)) = g2Dih p K := by
  rw [range_d4tau]
  rfl

theorem tp3Hom_d4tau
    (a : Fin TwistTag.D4.foldedTag.rank) (b : G2V p K) :
    tp3Hom p K (d4tau p K a b) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
        tp3Hom p K b * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection a))⁻¹ := by
  rcases fin_orbit_D4_cases a with rfl | rfl
  · have h1 := canonicalRep_orbit_zero_conj (K := K) ((b 1 : rootsOfUnity p K) : Kˣ)
      ((b 0 : rootsOfUnity p K) : Kˣ)
    rw [d4tau_zero]
    refine Eq.trans ?_ h1.symm
    show rootDiagUnit TwistTag.D4.tag (d4Tuple ((g2s1 p K b 1 : rootsOfUnity p K) : Kˣ)
      ((g2s1 p K b 0 : rootsOfUnity p K) : Kˣ)) = _
    congr 2
    show ((b 0 * b 1 ^ 3 : rootsOfUnity p K) : Kˣ) = _
    rw [mul_comm]
    rfl
  · have h1 := canonicalRep_orbit_one_conj (K := K) ((b 1 : rootsOfUnity p K) : Kˣ)
      ((b 0 : rootsOfUnity p K) : Kˣ)
    rw [d4tau_one]
    exact h1.symm

end KFU

theorem exists_r3ctx
    [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : RowModel p L 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (G2Ctx p K L F) := by
  obtain ⟨f, K, hKf, σ, hP, hζ, hall⟩ := exists_r3ctx_aux h hmodel
  have hfin := hP.finite
  refine ⟨K, hKf, hfin, hζ, ?_⟩
  have h1 : Nonempty (WCtx (Subgroup.closure (Set.range (d4tau p K))).subtype L F) :=
    hall (d4tau p K) (fun a b => tp3Hom_d4tau a b)
  rw [closure_range_d4tau] at h1
  exact h1

theorem kf123Row3 :
    KF123Row 3 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r3ctx h hmodel
  exact S.rowData h.prime h.five_le hζ (Or.inr rfl) hmodel

theorem kf123NTRow3 :
    KF123NTRow 3 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r3ctx h hmodel
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection h.prime h.five_le hζ hpowF hyL hyF

end CFSG.RankThree.PartOne

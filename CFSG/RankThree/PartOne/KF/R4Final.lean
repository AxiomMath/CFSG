module

public import CFSG.RankThree.PartOne.KF.R4Aux
public import CFSG.RankThree.PartOne.KF.F4Ctx

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.SectionRank.LargeRee

variable {G : Type} [Group G]

namespace KFU

variable {p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def f4tau (p : ℕ) (K : Type) [Field K] (θ : ℕ) :
    Fin 2 → MulAut (G2V p K) :=
  ![f4s1 p K, f4s2 p K θ]

theorem range_f4tau (θ : ℕ) : Set.range (f4tau p K θ) = {f4s1 p K, f4s2 p K θ} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem closure_range_f4tau (θ : ℕ) :
    Subgroup.closure (Set.range (f4tau p K θ)) = f4Dih p K θ := by
  rw [range_f4tau]
  rfl

theorem tp4Hom_f4tau
    {a : ℕ} [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (i : Fin 2) (b : G2V p K) :
    tp4Hom p a K (f4tau p K (2 ^ a) i b) =
      ((nGamma (blockGen i) : ↥(F4.reeGamma K a)) : ModGL F4.tag K) * tp4Hom p a K b *
        ((nGamma (blockGen i) : ↥(F4.reeGamma K a)) : ModGL F4.tag K)⁻¹ := by
  fin_cases i
  · exact (tp4Hom_conj_zero hK b).symm
  · have h1 := tp4Hom_conj_one (p := p) hK b
    have h2 : (((b 0 : rootsOfUnity p K) : Kˣ)) ^ (2 + 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ)) =
        (((b 0 : rootsOfUnity p K) : Kˣ)) ^ (2 * 2 ^ a + 2) := by
      rw [← zpow_natCast]
      congr 1
      push_cast
      change (2 : ℤ) + 2 * (2 : ℤ) ^ a = 2 * 2 ^ a + 2
      ring
    rw [h2] at h1
    exact h1.symm

end KFU

theorem exists_r4ctx
    [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : RowModel p L 4) :
    ∃ (a : ℕ) (K : Type) (_ : Field K), F4Param p a K ∧ (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (F4Ctx p K (2 ^ a) L F) := by
  obtain ⟨a, K, hKf, hKfin, hchar, hP, hζ, hall⟩ := exists_r4ctx_aux h hmodel
  refine ⟨a, K, hKf, hP, hζ, ?_⟩
  have h1 : Nonempty (WCtx (Subgroup.closure (Set.range (f4tau p K (2 ^ a)))).subtype L F) :=
    hall (f4tau p K (2 ^ a)) (fun i b => tp4Hom_f4tau hP.card i b)
  rw [closure_range_f4tau] at h1
  exact h1

theorem kf123Row4 :
    KF123Row 4 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨a, K, hKf, hP, hζ, ⟨S⟩⟩ := exists_r4ctx h hmodel
  exact S.rowData h.prime h.five_le hζ hP.theta_dvd hmodel

theorem kf123NTRow4 :
    KF123NTRow 4 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨a, K, hKf, hP, hζ, ⟨S⟩⟩ := exists_r4ctx h hmodel
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection h.prime h.five_le hζ hP.theta_dvd hpowF hyL hyF

end CFSG.RankThree.PartOne

module

public import CFSG.RankThree.PartOne.KF.R2Aux
public import CFSG.RankThree.PartOne.KF.G2Ctx

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog

variable {G : Type} [Group G]

namespace KFU

variable {p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def g2sigma (p : ℕ) (K : Type) [Field K] (i : Fin Tag.G2.rank) :
    MulAut (G2V p K) :=
  if i = g2ia then g2s0 p K else g2s1 p K

theorem g2sigma_ia : g2sigma p K g2ia = g2s0 p K := by simp [g2sigma]

theorem g2sigma_ir : g2sigma p K g2ir = g2s1 p K := by
  have h : g2ir ≠ g2ia := by decide
  simp [g2sigma, h]

theorem range_g2sigma : Set.range (g2sigma p K) = {g2s0 p K, g2s1 p K} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases CFSG.RankThree.Chevalley.fin_G2_cases i with rfl | rfl
    · exact Or.inl (g2sigma_ia (p := p) (K := K))
    · exact Or.inr (g2sigma_ir (p := p) (K := K))
  · rintro (rfl | rfl)
    · exact ⟨g2ia, g2sigma_ia⟩
    · exact ⟨g2ir, g2sigma_ir⟩

theorem closure_range_g2sigma : Subgroup.closure (Set.range (g2sigma p K)) = g2Dih p K := by
  rw [range_g2sigma]
  rfl

theorem tpHom_g2sigma
    (i : Fin Tag.G2.rank) (b : G2V p K) :
    tpHom p K (g2sigma p K i b) =
      weylElt .G2 K i 1 * tpHom p K b * (weylElt .G2 K i 1)⁻¹ := by
  rcases CFSG.RankThree.Chevalley.fin_G2_cases i with rfl | rfl
  · have h1 := weylElt_ia_conj_rootDiagUnit (K := K) (fun j => ((b j : rootsOfUnity p K) : Kˣ))
    rw [g2sigma_ia]
    refine Eq.trans ?_ h1.symm
    show rootDiagUnit .G2 (fun j => ((g2s0 p K b j : rootsOfUnity p K) : Kˣ)) = _
    congr 1
    funext j
    rcases CFSG.RankThree.Chevalley.fin_G2_cases j with rfl | rfl
    · rw [g2Tuple_ia]
      rfl
    · rw [g2Tuple_ir]
      rfl
  · have h1 := weylElt_ir_conj_rootDiagUnit (K := K) (fun j => ((b j : rootsOfUnity p K) : Kˣ))
    rw [g2sigma_ir]
    refine Eq.trans ?_ h1.symm
    show rootDiagUnit .G2 (fun j => ((g2s1 p K b j : rootsOfUnity p K) : Kˣ)) = _
    congr 1
    funext j
    rcases CFSG.RankThree.Chevalley.fin_G2_cases j with rfl | rfl
    · rw [g2Tuple_ia]
      rfl
    · rw [g2Tuple_ir]
      rfl

end KFU

theorem exists_r2ctx
    [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : RowModel p L 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (G2Ctx p K L F) := by
  obtain ⟨K, hKf, hKfin, hζ, hpK, hall⟩ := exists_r2ctx_aux h hmodel
  refine ⟨K, hKf, hKfin, hζ, ?_⟩
  have h1 : Nonempty (WCtx (Subgroup.closure (Set.range (g2sigma p K))).subtype L F) :=
    hall (g2sigma p K) (fun i b => tpHom_g2sigma i b)
  rw [closure_range_g2sigma] at h1
  exact h1

theorem kf123Row2 :
    KF123Row 2 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r2ctx h hmodel
  exact S.rowData h.prime h.five_le hζ (Or.inl rfl) hmodel

theorem kf123NTRow2 :
    KF123NTRow 2 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r2ctx h hmodel
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection h.prime h.five_le hζ hpowF hyL hyF

end CFSG.RankThree.PartOne

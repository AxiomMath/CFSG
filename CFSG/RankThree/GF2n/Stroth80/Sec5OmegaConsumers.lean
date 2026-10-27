module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SpConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_hypPlane_orth (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hnatSO : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z) {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)}
    {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (hsing : NatSingular hc t Q' X)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    ∃ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t ∧
      Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B)) := by
  obtain ⟨φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hnat
  obtain ⟨u, hQu, hu0, -, -, hL, hr'⟩ := hc.omega_points_core h34 hRoot hs hnatSO hK E hQ h3 hX
    φ hφ hker ψ hψ (hsing φ hφ hker ψ hψ)
  obtain ⟨P, hPe⟩ := exists_hypPair hQ hQu hu0
  have hPf0 : P.f ≠ 0 := fun h0 => by
    have := P.polar_ef
    rw [h0, polar_zero_right] at this
    exact zero_ne_one this
  obtain ⟨w, hw, hQw⟩ := exists_perp_vector_map_ne_zero hQ h3 hPf0
  have hw' : polar Q' P.f w = 0 := hw
  set g : Gom Q' := eichlerG Q' P.f w with hg
  set A : X := E.equiv.symm g with hA
  obtain ⟨r, hr⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = (A : GL ι K) := by
    have : (A : GL ι K) ∈ φ.range := by rw [hφ]; exact A.2
    exact MonoidHom.mem_range.mp this
  have hrv : (φ r : Matrix ι ι K) *ᵥ u = eichler Q' P.f w u := by
    have h1 := E.app A u
    rw [hA, MulEquiv.apply_symm_apply] at h1
    rw [hr]
    exact h1.symm
  have hne : polar Q' u ((φ r : Matrix ι ι K) *ᵥ u) ≠ 0 := by
    rw [hrv, ← hPe, polar_eichler_apply_left P.Q_e P.Q_f hw', P.polar_ef]
    simpa using hQw
  have hr1 := hr' r
  refine ⟨r, r.2, hr1.1.mpr hne, ?_⟩
  have hL2 := hr1.2
  rw [← hc.LB_conj (hc.Rt_le_M t r.2)] at hL2
  have hrX : (φ r : GL ι K) ∈ X := hφ ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩
  have hQu' : Q' ((φ r : Matrix ι ι K) *ᵥ u) = 0 := by rw [E.quad_mulVec hrX]; exact hQu
  exact le_sup_secOmega E hQ φ hφ hker hQu hQu' hne hL hL2


theorem sec7AExists_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Sec7AExistsStatement := by
  intro G _ _ M Q Z B hc n t hs7
  have hs := hs7.toSec5
  obtain ⟨m, hm, hpm⟩ := hs7.orth
  rcases hpm with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have : m = 2 := by omega
      subst this
      exact hs7.notPlus4 ⟨K, fK, finK, hK, hnat⟩
    have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm3, hnat⟩⟩
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
    obtain ⟨r, hr, hplane, hgen⟩ := hc.exists_hypPlane_orth h34 hRoot hs hnatSO hK
      (ElemMatrixIso.plus hm3) (nondegenerate_polarBilin_quadPlus m K) h3
      (addCommutantScalar_statedOmegaPlus hm3)
      (hc.natSingular_of h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm3)
        (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm3)) hnat
    exact ⟨r, ⟨hr, hplane, hc.Rt_eq_sup_of_51 h51 hs hnatSO hr hplane hgen⟩⟩
  · have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]; omega
    obtain ⟨r, hr, hplane, hgen⟩ := hc.exists_hypPlane_orth h34 hRoot hs hnatSO hK
      (ElemMatrixIso.minus hm hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus hm hirr)
      (hc.natSingular_of h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hm hirr)
        (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
        (addCommutantScalar_statedOmegaMinus hm hirr)) hnat
    exact ⟨r, ⟨hr, hplane, hc.Rt_eq_sup_of_51 h51 hs hnatSO hr hplane hgen⟩⟩

theorem sec5NatPointsOmega_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) :
    Sec5NatPointsOmegaStatement := by
  intro G _ _ M Q Z B hc n t hs hnat r hr hplane
  have hnatSO : SpNat hc t ∨ OmegaNat hc t := Or.inr hnat
  obtain ⟨K, fK, finK, hK, hcase⟩ := hnat
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  refine ⟨K, fK, finK, inferInstance, hK, ?_⟩
  rcases hcase with ⟨m, hm, hnat'⟩ | ⟨m, b, c, hm, hirr, hnat'⟩
  · haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat'
    obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
    haveI := hn
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
    obtain ⟨u, hQu, hu0, -, -, hL, hr'⟩ := hc.omega_points_core h34 hRoot hs hnatSO hK
      (ElemMatrixIso.plus hm) (nondegenerate_polarBilin_quadPlus m K) h3
      (addCommutantScalar_statedOmegaPlus hm) φ hφ hker ψ hψ
      (hc.omega_singular h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm)
        (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm)
        φ hφ ψ hψ)
    have h1 := hr' ⟨r, hr⟩
    have hne := h1.1.mp hplane
    have hrX : (φ ⟨r, hr⟩ : GL (Fin m ⊕ Fin m) K) ∈ StatedOmega (StatedQuadPlus m K) :=
      hφ ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hQu' : quadPlus m K ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) = 0 := by
      rw [(ElemMatrixIso.plus hm).quad_mulVec hrX]; exact hQu
    refine Or.inl ⟨m, hm, φ, u, (φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u,
      hQu, hQu', hu0, fun h0 => hne (by rw [h0]; simp [polar]), hne, hφ, hker,
      ⟨hnorm, hn, ψ, hψ⟩, ?_, ?_⟩
    · rw [← ElemMatrixIso.LomGL_plus hm]; exact hL
    · rw [← ElemMatrixIso.LomGL_plus hm]; exact h1.2
  · haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat'
    obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
    haveI := hn
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]; omega
    obtain ⟨u, hQu, hu0, -, -, hL, hr'⟩ := hc.omega_points_core h34 hRoot hs hnatSO hK
      (ElemMatrixIso.minus hm hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus hm hirr) φ hφ hker ψ hψ
      (hc.omega_singular h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hm hirr)
        (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
        (addCommutantScalar_statedOmegaMinus hm hirr) φ hφ ψ hψ)
    have h1 := hr' ⟨r, hr⟩
    have hne := h1.1.mp hplane
    have hrX : (φ ⟨r, hr⟩ : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) ∈
        StatedOmega (StatedQuadMinus m K b c) := hφ ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hQu' : quadMinus m K b c ((φ ⟨r, hr⟩ : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
        (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ u) = 0 := by
      rw [(ElemMatrixIso.minus hm hirr).quad_mulVec hrX]; exact hQu
    refine Or.inr ⟨m, b, c, hm, hirr, φ, u, (φ ⟨r, hr⟩ : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ u,
      hQu, hQu', hu0, fun h0 => hne (by rw [h0]; simp [polar]), hne, hφ, hker,
      ⟨hnorm, hn, ψ, hψ⟩, ?_, ?_⟩
    · rw [← ElemMatrixIso.LomGL_minus hm hirr]; exact hL
    · rw [← ElemMatrixIso.LomGL_minus hm hirr]; exact h1.2

end CFSG.RankThree.GF2n.Stroth80

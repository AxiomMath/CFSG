module

public import CFSG.LocalAnalysis.StandardType.PhanEAssembly
public import CFSG.LocalAnalysis.StandardType.PhanEStdChoice
public import CFSG.LocalAnalysis.StandardType.PhanEMatchFinal
public import CFSG.LocalAnalysis.StandardType.PhanEResCharts
public import CFSG.LocalAnalysis.StandardType.PhanEResField

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.CosetBuilding CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeE simplyLacedLevis_e6 simplyLacedLevis_e7 simplyLacedLevis_e8)

section Transport

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {G : Type} [Group G]

theorem PhanEConfig.classified_ofEq {n : ℕ} {M M' : CoxeterMatrix (Fin n)} (h : M = M')
    (c : PhanEConfig K f M G) : (c.ofEq h).Classified ↔ c.Classified := by
  subst h
  rfl

end Transport

section Std

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem StdInput.config_classified (S : StdInput D n H) {G : Type} [Group G]
    (eG : G ≃* frobFix S.F) {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2]
    (κ : Kf ≃+* S.L.Fld) (hκ : ∀ c, κ (unitaryInvolution Kf 2 f c) = S.L.θ (κ c))
    (hK : Nat.card Kf = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (M : ChevModel2 D n H Kf)
    (PC : M.PhiCompat S.F (sg Kf f : Kf →+* Kf)) (hred : D.divisible = ∅)
    (charts : ∀ (m : ℕ) (e : Fin m → Fin D.rank), 1 ≤ m → m ≤ 3 → Function.Injective e →
      (∀ k l : Fin m, D.cartan (e k) (e l) =
        if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) →
      ∃ L : Res.SLPath M m, L.e = e) :
    (S.config eG κ hκ).Classified :=
  phanEClassifiedAt_of_residueModels Kf f _ _ _
    (Match.phanEResidueModels_of_charts S.hct S.hext S.F S.hw₀ S.hsq S.stdPanel hK hq M _ PC rfl
      hred S.hsl charts)

end Std

theorem edgeE_or_of_cartanE_eq_neg_one (r : ℕ) (a b : Fin r) (h : Tag.cartanE r a b = -1) :
    edgeE r a b ∨ edgeE r b a := by
  unfold Tag.cartanE at h
  simp only [edgeE]
  split_ifs at h with h1 h2 <;> omega

theorem not_edgeE_of_cartanE_eq_zero (r : ℕ) (a b : Fin r) (h : Tag.cartanE r a b = 0) :
    ¬ edgeE r a b := by
  unfold Tag.cartanE at h
  simp only [edgeE]
  split_ifs at h with h1 h2 <;> omega

section E6


variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem e6StdConfig_classified (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e6StdConfig K f hK (one_le_of_four_le_two_pow hq)).Classified := by
  have hf := one_le_of_four_le_two_pow hq
  refine (PhanEConfig.classified_ofEq _ _).2 ?_
  exact StdInput.config_classified _ _ _ _ hK hq
    ((minChevModel e6Data_valid isFiniteType_cartan_E6 (GaloisField 2 (2 * f))).mapField
      (e6Kappa hK hf))
    ((e6PhiCompat (Exceptional.frobQ 2 f) (Exceptional.frobQ_frobQ 2 f hf)).mapField
      (e6Kappa hK hf) (e6Kappa_spec hK hf))
    rfl
    (Res.exists_slPath_mapField (e6Kappa hK hf)
      (Res.exists_slPath_of_levis _ (simplyLacedLevis_e6 (GaloisField 2 (2 * f)))
        (fun a b => edgeE_or_of_cartanE_eq_neg_one 6 a b)
        (fun a b => not_edgeE_of_cartanE_eq_zero 6 a b)))

end E6

section E7


variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem e7StdConfig_classified (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e7StdConfig K f hK (one_le_of_four_le_two_pow hq)).Classified := by
  refine (PhanEConfig.classified_ofEq _ _).2 ?_
  exact StdInput.config_classified _ _ _ _ hK hq
    (minChevModel e7Data_valid isFiniteType_cartan_E7 K)
    (e7PhiCompat (unitaryInvolution K 2 f : K →+* K) (unitaryInvolution_involutive hK)) rfl
    (Res.exists_slPath_of_levis _ (simplyLacedLevis_e7 K)
      (fun a b => edgeE_or_of_cartanE_eq_neg_one 7 a b)
      (fun a b => not_edgeE_of_cartanE_eq_zero 7 a b))

end E7

section E8


variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem e8StdConfig_classified (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e8StdConfig K f hK (one_le_of_four_le_two_pow hq)).Classified := by
  refine (PhanEConfig.classified_ofEq _ _).2 ?_
  exact StdInput.config_classified _ _ _ _ hK hq
    (adjChevModel (CFSG.LieType.Chevalley.rootOperatorFamily .E8) K)
    (e8PhiCompat (unitaryInvolution K 2 f : K →+* K) (unitaryInvolution_involutive hK)) rfl
    (Res.exists_slPath_of_levis _ (simplyLacedLevis_e8 K)
      (fun a b => edgeE_or_of_cartanE_eq_neg_one 8 a b)
      (fun a b => not_edgeE_of_cartanE_eq_zero 8 a b))

end E8

section Choice


theorem phanEClassified_stdChoice : PhanEClassified stdChoice := fun K _ _ f _ hK hq =>
  ⟨e6StdConfig_classified K f hK hq, e7StdConfig_classified K f hK hq,
    e8StdConfig_classified K f hK hq⟩

theorem phanEInput2_holds : PhanEInput2 :=
  phanEInput2_of_stdClassified phanEClassified_stdChoice

end Choice

end CFSG.ClassicalInvolution.Phan.PhanE

end

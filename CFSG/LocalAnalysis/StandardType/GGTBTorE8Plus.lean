module

public import CFSG.LocalAnalysis.StandardType.GGTorusScalar
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Cover
public import CFSG.LocalAnalysis.StandardType.GGTorusE8Scalar
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4Thm

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.RootSystem

theorem ggTorusTorData_E8_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E8 K))
    (hE : IsElemAbelian p E) (hcard : p ^ 7 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    GGTorusTorData (Nat.card K + 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (adjointGroup .E8 K) (E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F, Fr, ζ, hζ, ι, n, hFr, hΦ, hw, hζo, hι, hrange, hbase, hnb, hact, hnorm⟩ :=
    E8ScalarTorus.exists_frame_of_selfCentralizing hp hp2 hq E hE hcard hSC
  let μ := rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)
  let φ := E8ScalarTorus.coordHom F.D Fr hFr hΦ F.n_eq hw
  have hφ : Function.Injective φ := E8ScalarTorus.coordHom_injective F.D Fr hFr hΦ F.n_eq hw
  obtain ⟨l⟩ := E8ScalarTorus.exists_rootValue_equiv (K := K)
  have hζm : ζ ^ (Nat.card K + 1) = 1 := by
    obtain ⟨k, hk⟩ := hq
    rw [hk, pow_mul, hζ, one_pow]
  let z : μ := ⟨ζ, (mem_rootsOfUnity _ _).mpr hζm⟩
  have hz : z ^ p = 1 := Subtype.ext hζ
  have hz1 : z ≠ 1 := by
    intro h
    have hζ1 : ζ = 1 := congrArg Subtype.val h
    rw [hζ1, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hC : Tag.E8.cartan = CartanMatrix.E₈ := cartanE_eq 8
  have hM : coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    FrameRoute.coxeterE8_eq.symm
  suffices h : GGTorusTorData (Nat.card K + 1) Tag.E8.rank Tag.E8.cartan
      (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8))
      (adjointGroup .E8 K) (E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))) by
    rw [hM] at h
    simpa only [hC, Tag.rank] using h
  have hBC : cartanInvE8 * Tag.E8.cartan = 1 := cartanInvE8_mul
  have hCB : Tag.E8.cartan * cartanInvE8 = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin Tag.E8.rank))).mp hBC
  have hCsymm : (Tag.E8.cartan).IsSymm := by
    exact hC.symm ▸ CartanMatrix.E_isSymm 8
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι hι hrange n hact hnorm

  apply ggTorusTorData_of_scalarRootCoordinates l φ hφ Tag.E8.cartan cartanInvE8 hCB hBC hCsymm
    center_adjointGroup_eq_bot E (fun g => E8ScalarTorus.mem_primeSubgroup_iff F Fr hFr hΦ hw g)
    z hz hz1 n hnA _ _ (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)) ρ hρ hρrange hρsimple
  · intro k a
    have h := E8ScalarTorus.simple_conj_coordHom F.D Fr hFr hΦ F.n_eq hw k (n k) (hnb k) a
    change n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple Tag.E8.cartan k (a k)))⁻¹
    have hcor : E8ScalarTorus.corootHom F.D Fr hFr hΦ F.n_eq hw k (a k) =
        φ (corTuple Tag.E8.cartan k (a k)) := rfl
    rw [hcor] at h
    exact h
  · have hlong : ExcIsLongest .E8 F.w := by
      intro α hα hpos i
      rw [hw, Pi.neg_apply]
      exact neg_nonpos.mpr (hpos i)
    exact E8ScalarTorus.centralizer_le_range hp hp2 F Fr hFr hΦ hq hlong hw

theorem ggTorusTorW_recipe_E8_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K + 1) :
    GGTorusTorW p 7 (Nat.card K + 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  intro L _ _ ψ A hTB
  obtain ⟨e, -, E, hE, hcard, hSC, hA⟩ := exists_e8_model_of_tableB ψ A hTB
  have hr : p ^ 7 ≤ Nat.card E := by rw [hcard]; exact hTB.2.2.2.2.2.1
  exact torData_of_e8_model e hA (ggTorusTorData_E8_plus hp hp2 hq E hE hr hSC)

theorem ggTorusTorW_recipe_E8_three_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 3 ∣ Nat.card K + 1) :
    GGTorusTorW 3 7 (Nat.card K + 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  exact ggTorusTorW_recipe_E8_plus Nat.prime_three (by norm_num) hq

end CFSG.StandardType

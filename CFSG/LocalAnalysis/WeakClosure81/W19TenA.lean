module

public import CFSG.LocalAnalysis.WeakClosure81.W19Chief
public import CFSG.LocalAnalysis.WeakClosure81.W19SixSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_centralizerQuot {H E F : Subgroup G} (hE : H ≤ normalizer (E : Set G))
    (hF : H ≤ normalizer (F : Set G)) :
    H ≤ normalizer (centralizerQuot H E F : Set G) := by
  have key : ∀ h ∈ H, ∀ y ∈ centralizerQuot H E F, h * y * h⁻¹ ∈ centralizerQuot H E F := by
    intro h hh y hy
    obtain ⟨hyH, hyF, hyE⟩ := hy
    refine ⟨H.mul_mem (H.mul_mem hh hyH) (H.inv_mem hh), ?_, fun e he => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hF hh) hyF) (Subgroup.inv_mem _ (hF hh))
    · have he' : h⁻¹ * e * h⁻¹⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.1 (hE (H.inv_mem hh)) e).1 he
      have h1 := hyE _ he'
      have eq : ⁅h * y * h⁻¹, e⁆ = h * ⁅y, h⁻¹ * e * h⁻¹⁻¹⁆ * h⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [eq]
      exact (Subgroup.mem_normalizer_iff.1 (hF hh) _).1 h1
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have h1 := key h⁻¹ (H.inv_mem hh) _ hy
  have e : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem le_centralizerQuot_of_comm_le {H E F A : Subgroup G} (hAH : A ≤ H)
    (hF : H ≤ normalizer (F : Set G)) (h : ⁅A, E⁆ ≤ F) : A ≤ centralizerQuot H E F :=
  fun a ha => ⟨hAH ha, hF (hAH ha), fun _ he => h (Subgroup.commutator_mem_commutator ha he)⟩

theorem le_sup_of_isE {H T A K C : Subgroup G} (hK : E1.IsE 1 H T A K) (hAC : A ≤ C)
    (hC : H ≤ normalizer (C : Set G)) : K ≤ T ⊔ C := by
  have hKH : K ≤ H := hK.1
  have hTK : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K) K := hK.2.2.1
  have hsup : (T ⊓ K) ⊔ twoResidual K = K := sup_twoResidual_eq hTK
  have hres : twoResidual K ≤ C := by
    refine (E1.twoResidual_le_conjClosure ⟨1, hK⟩).trans (conjClosure_le fun h hh z hz => ?_)
    exact (Subgroup.mem_normalizer_iff.1 (hC (hKH hh)) z).1 (hAC hz)
  calc K = (T ⊓ K) ⊔ twoResidual K := hsup.symm
    _ ≤ T ⊔ C := sup_le_sup inf_le_left hres

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem exists_conj_not_comm_le (c : MinCex193 D V₀ V p X) (h4 : Card196Four D V p X)
    {E F : Subgroup G} (hE : Hyp198 D X E F) (hXE : ¬ ⁅X, E⁆ ≤ F) :
    ∃ g : G, conjSubgroup V g ≤ D.T ∧ ¬ ⁅conjSubgroup V g, E⁆ ≤ F := by
  by_contra hno
  have hno' : ∀ g : G, conjSubgroup V g ≤ D.T → ⁅conjSubgroup V g, E⁆ ≤ F := fun g hg =>
    not_not.1 fun h => hno ⟨g, hg, h⟩
  have hCn : X ⊔ D.T ≤ normalizer (centralizerQuot (X ⊔ D.T) E F : Set G) :=
    le_normalizer_centralizerQuot hE.normalizer_E hE.normalizer_F
  have hAC : ∀ g : G, conjSubgroup V g ≤ D.T → conjSubgroup V g ≤ centralizerQuot (X ⊔ D.T) E F :=
    fun g hg => le_centralizerQuot_of_comm_le (hg.trans le_sup_right) hE.normalizer_F (hno' g hg)
  have hHeq : E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ⊔ D.T = X ⊔ D.T :=
    c.sup_eq_eGen_sup_of_card h4
  have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup c.setting.isElemAbelian
  have hEG : E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ≤
      D.T ⊔ centralizerQuot (X ⊔ D.T) E F := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    obtain ⟨-, g, hAg, hm⟩ := hA
    have hAeq : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) hAg).1 hm
    rw [hAeq] at hAT hK
    exact le_sup_of_isE hK (hAC g hAT) hCn
  have hHle : X ⊔ D.T ≤ D.T ⊔ centralizerQuot (X ⊔ D.T) E F :=
    hHeq.ge.trans (sup_le hEG le_sup_left)
  have hXC : X ≤ centralizerQuot (X ⊔ D.T) E F := by
    intro x hx
    have hxH : x ∈ D.T ⊔ centralizerQuot (X ⊔ D.T) E F := hHle (Subgroup.mem_sup_left hx)
    obtain ⟨e, he⟩ := exists_pow_mem_of_mem_sup_pGroup c.hyp.isSylowIn_T.isPGroup
      (le_sup_right.trans hCn) hxH
    have hxp : x ^ p ^ 1 = 1 := by rw [pow_one]; exact c.hyp.exponent x hx
    exact E1.mem_of_pow_mem_two_p c.hyp.prime c.hyp.odd (k := 1)
      (by rw [hxp]; exact Subgroup.one_mem _) he
  exact hXE (Subgroup.commutator_le.2 fun x hx e he => (hXC hx).2.2 e he)

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end

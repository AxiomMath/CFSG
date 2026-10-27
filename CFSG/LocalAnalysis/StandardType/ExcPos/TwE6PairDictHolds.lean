module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairOneAssembly
public import Certificates.Certificate1952
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGFamLabelIndex
import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
import CFSG.LocalAnalysis.StandardType.GGFamTame
import CFSG.LocalAnalysis.StandardType.GGFamComponent

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section


theorem twE6PairDict_holds : TwE6PairDict := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos B hB hb
  have hpos' := hpos
  obtain ⟨hψr, -, -, -, hp, hp2, -, -, -, -, hDB1, -, -, -, hJc, -, hx, -, hLG0, -, -,
    hDnotc, -, -, -, -, -, -, -, -, -⟩ := hpos
  have hf : 1 ≤ f := B.one_le_f
  have hq2 : B.Δ.q = 2 ^ f := by
    rw [B.hq]
    exact GaloisField.card 2 f (by omega)
  haveI : CharP GGL 2 := inferInstance
  obtain ⟨S, hSD, hSρ⟩ := LieCore.exists_langSetup_of_datum B.Δ B.ρ B.frob B.finite hf hq2
  let a : Fin 2 → Fin Tag.E6.rank → GGLˣ := ![B.coord x, B.coord B.d]
  have hT : ∀ u : Fin 2, rootDiagUnit Tag.E6 (a u) ∈ S.D.torus := by
    intro u
    rw [hSD]
    fin_cases u
    · simpa [a] using B.coord_torus x hx
    · simpa [a] using B.coord_torus B.d B.d_mem
  have hap : ∀ u j, a u j ^ p = 1 := by
    intro u
    fin_cases u
    · simpa [a] using B.coord_pow x hx
    · simpa [a] using B.coord_pow B.d B.d_mem
  have h1 : ∃ u : Fin 2, rootDiagUnit Tag.E6 (a u) ≠ 1 := by
    rcases twE6_coord_ne_one B hDB1 hLG0 hDnotc hx with h | h
    · exact ⟨0, by simpa [a] using h⟩
    · exact ⟨1, by simpa [a] using h⟩
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  have hTame : ∀ i : KernelComponent (TableCRes.famCharHom a),
      CFSG.IsQuasisimple (TableCRes.rationalComponentM S.ρ S.Γ (TableCRes.famCharHom a) i) ∨
        Group.IsSolvable (TableCRes.rationalComponentM S.ρ S.Γ (TableCRes.famCharHom a) i) :=
    fun i => TableCRes.langFamTame_of_prime hτ S hp hp2 hT hap h1 i
  have hJ' : CFSG.Open.IsComponentOf ((J.subgroupOf G₀).map B.η)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u : Fin 2 => rootDiagUnit Tag.E6 (a u))) := by
    rw [← CFSG.Assembly.isComponentOf_iff_open]
    have hJ := B.attach_J
    change CFSG.Assembly.IsComponentOf ((J.subgroupOf G₀).map B.η)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u : Fin 2 =>
        rootDiagUnit Tag.E6 (![B.coord x, B.coord B.d] u)))
    rw [LangSetup.Γ, hSD]
    rw [← LieCore.centralizer_closure_pair_eq_range (τ := Tag.E6) (B.coord x) (B.coord B.d)]
    rw [Subgroup.centralizer_closure]
    exact hJ
  obtain ⟨i', hi', -⟩ := TableCRes.exists_eq_rationalComponentM_of_isComponentOf
    S hp hτ hp2 hT hap h1 hTame hJ'
  obtain ⟨j, hj⟩ := LieCore.exists_famComponent_of_jointChar (B.coord x) (B.coord B.d) B.iJ
  have hJG : J ≤ G₀ := hJc.1.trans inf_le_left
  have hQ : CFSG.IsQuasisimple ↥((J.subgroupOf G₀).map B.η) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr
      (isQuasisimple_map_eta B.η B.ker_η hJG hJc.2.2)
  have hspan : ∀ i : KernelComponent (TableCRes.famCharHom a),
      TableCRes.rationalComponentM S.ρ S.Γ (TableCRes.famCharHom a) i ≤
        rootSpan Tag.E6 GGL (TableCRes.rationalRootsM S.ρ (TableCRes.famCharHom a) i) := by
    intro i
    exact Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁.1 h₂.1)
        (Subgroup.inv_mem _ h₁.1)) (Subgroup.inv_mem _ h₂.1)
  have hle_i : (J.subgroupOf G₀).map B.η ≤
      rootSpan Tag.E6 GGL (TableCRes.rationalRootsM S.ρ (TableCRes.famCharHom a) i') := by
    rw [hi']
    exact hspan i'
  have hrr : TableCRes.rationalRootsM S.ρ (TableCRes.famCharHom a) j =
      LieCore.ratOrbit B.ρ B.rootsJ := by
    rw [hSρ]
    unfold ExcBase.rootsJ
    rw [hj]
    rfl
  have hle_j : (J.subgroupOf G₀).map B.η ≤
      rootSpan Tag.E6 GGL (TableCRes.rationalRootsM S.ρ (TableCRes.famCharHom a) j) := by
    rw [hrr]
    exact B.map_J_le
  have hor := TableCRes.rationalRootsM_eq_of_quasisimple_le_rootSpan S hT i' j hQ hle_i hle_j
  rw [hi']
  unfold TableCRes.rationalComponentM TableCRes.rationalSpanM LieCore.ratComp
  rw [hor, hrr, LangSetup.Γ, hSD]

end

end CFSG.StandardType.LieKnownR2.ExcPos

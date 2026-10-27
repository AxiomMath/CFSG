module

public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
import CFSG.LocalAnalysis.StandardType.GGFamLabelIndex
import CFSG.LocalAnalysis.StandardType.GGFamCentralizerBridge

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LayerSixE
  CFSG.RankThree.PartOne.KE8F


private theorem famKernel_range_eq_kernelRoots {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) :
    kernelRoots (famCharHom a) = famKernel (Set.range a) := by
  ext γ
  rw [mem_kernelRoots_famChar]
  simp only [famKernel, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun h => ⟨h.1, fun b hb => by obtain ⟨u, rfl⟩ := hb; exact h.2 u⟩,
    fun h => ⟨h.1, fun u => h.2 (a u) ⟨u, rfl⟩⟩⟩

private theorem famSubnormal_rootSpan_le_normalizer_of_closed {τ : Tag} {L : Type} [Field L]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : Ψ ⊆ kernelRoots χ)
    (hcl : ∀ γ (hγ : γ ∈ Ψ) β (hβ : β ∈ kernelRoots χ),
      (⟦⟨β, hβ⟩⟧ : KernelComponent χ) = ⟦⟨γ, hΨ hγ⟩⟧ → β ∈ Ψ) :
    rootSpan τ L (kernelRoots χ) ≤
      Subgroup.normalizer (rootSpan τ L Ψ : Set (ModGL τ L)) := by
  refine iSup₂_le fun β hβ => ?_
  by_cases hβΨ : β ∈ Ψ
  · exact (le_iSup₂_of_le (f := fun α (_ : α ∈ Ψ) => rootSubgroup τ L α) β hβΨ le_rfl).trans
      Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (rootSpan τ L Ψ : Set (ModGL τ L)))
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun γ hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hne : (⟦⟨γ, hΨ hγ⟩⟧ : KernelComponent χ) ≠ ⟦⟨β, hβ⟩⟧ := fun h =>
      hβΨ (hcl γ hγ β hβ h.symm)
    exact (commute_of_mk_ne hne L x hx y hy).eq

private theorem famSubnormal_mem_map_famCentralizer_range {τ : Tag} {L : Type} [Field L]
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) {x : ModGL τ L} :
    x ∈ (CFSG.StandardType.LayerSixE.famCentralizer (Set.range a)).map
        (adjointGroup τ L).subtype ↔
      x ∈ adjointGroup τ L ∧
        x ∈ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) := by
  constructor
  · intro hx
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 hx
    rw [← hgx]
    refine ⟨g.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have h := (CFSG.StandardType.LayerSixE.mem_famCentralizer.1 hg) (a u) ⟨u, rfl⟩
    calc rootDiagUnit τ (a u) * (g : ModGL τ L) =
          (rootDiagUnit τ (a u) * (g : ModGL τ L) * (rootDiagUnit τ (a u))⁻¹) *
            rootDiagUnit τ (a u) := by group
      _ = (g : ModGL τ L) * rootDiagUnit τ (a u) := by rw [h]
  · rintro ⟨hxadj, hxc⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hxadj⟩, ?_, rfl⟩
    rw [CFSG.StandardType.LayerSixE.mem_famCentralizer]
    intro b hb
    obtain ⟨u, rfl⟩ := hb
    have h : rootDiagUnit τ (a u) * x = x * rootDiagUnit τ (a u) :=
      Subgroup.mem_centralizer_iff.1 hxc _ ⟨u, rfl⟩
    rw [h]
    group

theorem langFamSubnormal_of_mem_torus {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (i : KernelComponent (famCharHom a)) :
    rationalComponentM S.ρ S.Γ (famCharHom a) i ≤
        S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) ∧
      ((rationalComponentM S.ρ S.Γ (famCharHom a) i).subgroupOf
        (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)))).IsSubnormal := by
  classical
  have hker : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hΨ : rationalRootsM S.ρ (famCharHom a) i ⊆ kernelRoots (famCharHom a) :=
    famComp_rationalRootsM_subset_kernelRoots hker i
  have hcl : ∀ γ (hγ : γ ∈ rationalRootsM S.ρ (famCharHom a) i) β
      (hβ : β ∈ kernelRoots (famCharHom a)),
      (⟦⟨β, hβ⟩⟧ : KernelComponent (famCharHom a)) = ⟦⟨γ, hΨ hγ⟩⟧ →
        β ∈ rationalRootsM S.ρ (famCharHom a) i :=
    fun γ hγ β hβ h => famLabelIndex_rationalRootsM_closed hker S.frob.iform_eq i hγ hβ h
  have hΓ : S.Γ ≤ adjointGroup τ L :=
    (commutator_le_self_of_subgroup S.D.model).trans inf_le_left
  have hcent : rootSpan τ L (rationalRootsM S.ρ (famCharHom a) i) ≤
      Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have hsub : rationalRootsM S.ρ (famCharHom a) i ⊆ rootCharKernel (a u) := by
      intro γ hγ
      have hγ' := (mem_kernelRoots_famChar a).1 (hΨ hγ)
      exact ⟨hγ'.1, hγ'.2 u⟩
    exact Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer (a u) hsub hx) _ rfl
  have hN : rationalSpanM S.ρ S.Γ (famCharHom a) i ≤
      S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) :=
    fun x hx => Subgroup.mem_inf.2
      ⟨(Subgroup.mem_inf.1 hx).2, hcent (Subgroup.mem_inf.1 hx).1⟩
  refine ⟨(commutator_le_self_of_subgroup _).trans hN, ?_⟩
  let H : Subgroup (ModGL τ L) :=
    (CFSG.StandardType.LayerSixE.famCentralizer (Set.range a)).map
      (adjointGroup τ L).subtype
  let Q : Subgroup (ModGL τ L) :=
    torusGroup τ L ⊔ rootSpan τ L (famKernel (Set.range a))
  have hQH : Q ≤ H :=
    CFSG.StandardType.LayerSixE.torus_sup_rootSpan_le_map_famCentralizer (Set.range a)
  have hHN : H ≤ Subgroup.normalizer (Q : Set (ModGL τ L)) :=
    CFSG.StandardType.LayerSixE.map_famCentralizer_le_normalizer (Set.range a)
  have hQn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hHN
  have hΨQ : rootSpan τ L (rationalRootsM S.ρ (famCharHom a) i) ≤ Q := by
    refine (rootSpan_mono ?_).trans le_sup_right
    intro γ hγ
    rw [← famKernel_range_eq_kernelRoots]
    exact hΨ hγ
  have hNQ : Q ≤ Subgroup.normalizer
      (rootSpan τ L (rationalRootsM S.ρ (famCharHom a) i) : Set (ModGL τ L)) := by
    refine sup_le ?_ ?_
    · exact torusGroup_le_normalizer_rootSpan (fun α hα => (hΨ hα).1)
    · rw [← famKernel_range_eq_kernelRoots]
      exact famSubnormal_rootSpan_le_normalizer_of_closed hΨ hcl
  have hUn : ((rootSpan τ L (rationalRootsM S.ρ (famCharHom a) i)).subgroupOf H).IsSubnormal :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isSubnormal_subgroupOf_step hΨQ hQn.isSubnormal
      fun y hy r hr => (Subgroup.mem_normalizer_iff.1 (hNQ hy) r).1 hr
  have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.isSubnormal_inf_subgroupOf hUn S.Γ
  have hHC : H ⊓ S.Γ = S.Γ ⊓
      Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, famSubnormal_mem_map_famCentralizer_range]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hΓ h.1, h.2⟩, h.1⟩⟩
  rw [hHC] at h2
  exact CFSG.HardMathSupport.Timmesfeld.LangTorus.isSubnormal_commutator_subgroupOf h2

end CFSG.StandardType.TableCRes

end

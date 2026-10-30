module

public import CFSG.LocalAnalysis.StandardType.GGTBJXDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTBJLift
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem ggTBJ_class_fix
    {τ : Tag} {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL τ K}
    (hker : ψ.ker ≤ Subgroup.center L') (hψ : ψ.range = adjointGroup τ K) (a : Fin τ.rank → Kˣ)
    (ha : ∀ i, a i ^ p = 1)
    (y : MulAut L') (hy : ∀ l, ψ (y l) = rootDiagUnit τ a * ψ l * (rootDiagUnit τ a)⁻¹)
    {J : Subgroup L'} (hJ : IsComponentOf J (fixSubgroup y)) :
    ∃ i : KernelComponent (rootCharHom a), J.map ψ = componentRootSpan K (rootCharHom a) i := by
  have hCX : ∀ c ∈ fixSubgroup y, ψ c ∈ toralCentralizer τ K a := by
    intro c hc
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← hψ]
      exact ⟨c, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hc' : ψ c = rootDiagUnit τ a * ψ c * (rootDiagUnit τ a)⁻¹ := by
        rw [← hy c, show y c = c from hc]
      nth_rewrite 1 [hc']
      group
  by_contra hall
  push Not at hall
  have hcomm : ∀ i : KernelComponent (rootCharHom a), componentRootSpan K (rootCharHom a) i ≤
      Subgroup.centralizer (J.map ψ : Set (ModGL τ K)) := by
    intro i
    have hS : IsComponentOf (componentRootSpan K (rootCharHom a) i) (toralCentralizer τ K a) :=
      ggTBJ_isComponentOf_componentRootSpan τ hK a i
    have hSr : componentRootSpan K (rootCharHom a) i ≤ ψ.range := by
      rw [hψ]
      exact (componentRootSpan_le K i).trans
        (rootSpan_le_adjointGroup K (kernelRoots (rootCharHom a)))
    obtain ⟨Q, hQ, hQmap⟩ := ggTBJ_exists_component_lift_fix ψ hker y (rootDiagUnit τ a) hy hS
      hSr (hS.1.trans inf_le_right) hCX
    have hJQ : J ≠ Q := fun h => hall i (by rw [h, hQmap])
    have hc : ⁅J, Q⁆ = ⊥ :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute
        (CFSG.Assembly.isComponentOf_iff_open.2 hJ)
        (CFSG.Assembly.isComponentOf_iff_open.2 hQ)).resolve_left hJQ
    rw [← hQmap, ← Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.map_commutator,
      Subgroup.commutator_comm, hc, Subgroup.map_bot]
  have hP : J.map ψ ≤ toralCentralizer τ K a := by
    rintro x ⟨c, hc, rfl⟩
    exact hCX c (hJ.1 hc)
  have hperfmap : ⁅J.map ψ, J.map ψ⁆ = J.map ψ := by
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp ⟨hJ.2.2.1⟩]
  have hP' : J.map ψ ≤ rootSpan τ K (kernelRoots (rootCharHom a)) :=
    ggTBJ_perfect_le_rootSpan τ hK hp a ha (J.map ψ) hP hperfmap
  rw [← iSup_componentRootSpan] at hP'
  have hab : ⁅J.map ψ, J.map ψ⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hP'.trans (iSup_le hcomm))
  have hbot : J.map ψ = ⊥ := hperfmap.symm.trans hab
  have hJleker : J ≤ ψ.ker := (Subgroup.map_eq_bot_iff (H := J) (f := ψ)).mp hbot
  have hJcen : J ≤ Subgroup.center L' := hJleker.trans hker
  have hcenter : Subgroup.center J = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hJcen x.2) (y : L'))
  have hsub : Subsingleton (J ⧸ Subgroup.center J) := by
    rw [hcenter]
    exact QuotientGroup.subsingleton_quotient_top
  haveI := hsub
  obtain ⟨x, y, hxy⟩ := (hJ.2.2.2.toNontrivial : Nontrivial (J ⧸ Subgroup.center J))
  exact hxy (Subsingleton.elim x y)

theorem ggTBJ_fix_of_kernel
    {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M] {L' : Type} [Group L']
    {ψ : L' →* ModGL τ K} (hker : ψ.ker ≤ Subgroup.center L')
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) {J : Subgroup L'}
    (hJ : J.map ψ = componentRootSpan K χ i) (hJperf : ⁅J, J⁆ = J) (b : Fin τ.rank → Kˣ)
    (hb : ∀ γ ∈ componentRoots χ i, rootChar b γ = 1) (z : MulAut L')
    (hz : ∀ l, ψ (z l) = rootDiagUnit τ b * ψ l * (rootDiagUnit τ b)⁻¹) :
    ∀ j ∈ J, z j = j := by
  have hS : componentRootSpan K χ i ≤
      Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ K)) := by
    rw [show componentRootSpan K χ i = rootSpan τ K (componentRoots χ i) from rfl]
    exact rootSpan_le_centralizer b fun α hα => ⟨hα.1.1, hb α hα⟩
  have hle : J ≤ fixSubgroup z := by
    rw [← hJperf, Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    refine CFSG.HardMathSupport.Solomon.Coordinator.comm_mem_fixSubgroup
      ψ hker z (MulAut.conj (rootDiagUnit τ b)) ?_ ?_ ?_
    · intro k
      rw [hz k, MulAut.conj_apply]
    · rw [ggTBJ_fixSubgroup_conj]
      exact hS (by rw [← hJ]; exact Subgroup.mem_map_of_mem ψ hk₁)
    · rw [ggTBJ_fixSubgroup_conj]
      exact hS (by rw [← hJ]; exact Subgroup.mem_map_of_mem ψ hk₂)
  intro j hj
  exact hle hj

theorem ggTBJX_class
    {τ : Tag} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    {ζ : Kˣ} {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL τ K}
    {σ : Multiplicative (Fin τ.rank → ZMod p) →* L'} (hstd : GGTBJXStd p τ ζ ψ σ)
    (f₀ : Multiplicative (Fin τ.rank → ZMod p)) {J : Subgroup L'}
    (hJ : IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L'))) :
    ∃ i : KernelComponent (rootCharHom (ggTBJXa p τ ζ f₀)),
      J.map ψ = componentRootSpan K (rootCharHom (ggTBJXa p τ ζ f₀)) i := by
  have hp : p.Prime := Fact.out
  have hζ : orderOf ζ = p := hstd.2.2.1
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hK : 4 ≤ Nat.card K := by
    have h1 : orderOf ζ ≤ Nat.card Kˣ := orderOf_le_card
    rw [hζ, Nat.card_units] at h1
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    omega
  have ha : ∀ i : Fin τ.rank, ggTBJXa p τ ζ f₀ i ^ p = 1 := by
    intro i
    show (ζ ^ (Multiplicative.toAdd f₀ i).val) ^ p = 1
    rw [← pow_mul, pow_mul', hζp, one_pow]
  have hy : ∀ l, ψ (MulAut.conj (σ f₀) l) =
      rootDiagUnit τ (ggTBJXa p τ ζ f₀) * ψ l * (rootDiagUnit τ (ggTBJXa p τ ζ f₀))⁻¹ := by
    intro l
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hstd.2.2.2 f₀]
  refine ggTBJ_class_fix hp hK hstd.1 hstd.2.1 (ggTBJXa p τ ζ f₀) ha
    (MulAut.conj (σ f₀)) hy ?_
  rwa [ggTBJ_fixSubgroup_conj]

end CFSG.StandardType

end

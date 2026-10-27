module

public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreRank
public import CFSG.RankThree.PartOne.KE6.EqpOpp
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.LieType.Chevalley.RootComponentType
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDAll
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import Certificates.Certificate10050
public import Certificates.Certificate13660

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootTorus CFSG.StandardType.LangRat
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.RankThree.Chevalley.EvenF4QPlus CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped commutatorElement MatrixGroups

theorem tw1w_rootSL2_WSL_neg
    {L : Type} [Field L] [CharP L 2] {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    rootSL2 Tag.E6 L (-γ) WSL = rootSL2 Tag.E6 L γ WSL := by
  have h1 : rootSL2 Tag.E6 L (-γ) WSL = rootWeylSL2 Tag.E6 L (-γ) 1 := by
    rw [rootWeylSL2, nSL_one]
  have h2 : rootSL2 Tag.E6 L γ WSL = rootWeylSL2 Tag.E6 L γ 1 := by
    rw [rootWeylSL2, nSL_one]
  rw [h1, h2, rootWeylSL2_one_eq_canonicalRep_of_charTwo (M := L) (IsRoot.neg hγ),
    rootWeylSL2_one_eq_canonicalRep_of_charTwo (M := L) hγ, rootReflection_neg hγ]

theorem tw1w_rootSL2_WSL_conj
    {L : Type} [Field L] [CharP L 2] {γ δ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ) :
    rootSL2 Tag.E6 L δ WSL * rootSL2 Tag.E6 L γ WSL * (rootSL2 Tag.E6 L δ WSL)⁻¹ =
      rootSL2 Tag.E6 L (rootReflection δ • γ) WSL := by
  have h1 : rootSL2 Tag.E6 L δ WSL = rootWeylSL2 Tag.E6 L δ 1 := by
    rw [rootWeylSL2, nSL_one]
  rw [h1, rootWeylSL2_one_eq_canonicalRep_of_charTwo (M := L) hδ]
  exact canonicalRep_conj_rootSL2 (rootReflection δ) hγ WSL

theorem tw1w_conj_mem_commutator_self {G : Type*} [Group G] {H : Subgroup G} {c : G}
    (hc : c ∈ H) {y : G} (hy : y ∈ ⁅H, H⁆) : c * y * c⁻¹ ∈ ⁅H, H⁆ := by
  have hmapH : H.map (MulAut.conj c).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        H.mul_mem (H.mul_mem hc hz) (H.inv_mem hc)
    · intro hx
      refine ⟨c⁻¹ * x * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hx) hc, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hmap : (⁅H, H⁆).map (MulAut.conj c).toMonoidHom = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, hmapH]
  have hmem : (MulAut.conj c) y ∈ (⁅H, H⁆).map (MulAut.conj c).toMonoidHom := ⟨y, hy, rfl⟩
  rw [hmap] at hmem
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

theorem tw1w_class_connected {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {γ γ' : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) (hγ' : γ' ∈ Ψ) :
    Relation.ReflTransGen (fun x y => x ∈ Ψ ∧ y ∈ Ψ ∧ iform x y ≠ 0) γ γ' := by
  classical
  set S : Set (Fin τ.rank → ℤ) :=
    {α | Relation.ReflTransGen (fun x y => x ∈ Ψ ∧ y ∈ Ψ ∧ iform x y ≠ 0) γ α} with hS
  have hγS : γ ∈ S := Relation.ReflTransGen.refl
  have hSsub : S ⊆ Ψ := by
    intro α hα
    induction hα with
    | refl => exact hγ
    | tail _ hstep _ => exact hstep.2.1
  have hSorth : ∀ α ∈ S, ∀ β ∈ Ψ, β ∉ S → iform α β = 0 := by
    intro α hα β hβ hβS
    by_contra h
    exact hβS (Relation.ReflTransGen.tail hα ⟨hSsub hα, hβ, h⟩)
  rcases hΨ.irreducible S hSsub hSorth with h | h
  · exact absurd hγS (by rw [h]; exact Set.notMem_empty γ)
  · have hmem : γ' ∈ S := by rw [h]; exact hγ'
    simpa [hS] using hmem

theorem tw1w_rootReflection_add_eq_neg
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ)
    (h : iform γ δ = -1) : rootReflection (γ + δ) • γ = -δ := by
  have hsym : ∀ j : Fin Tag.E6.rank, Tag.E6.symmetrizer j j = 1 := by decide
  have hne : γ ≠ -δ := by
    intro hh
    rw [hh, iform_neg_left,
      CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hsym hδ] at h
    norm_num at h
  have hsum : IsRoot Tag.E6 (γ + δ) :=
    isRoot_add_of_iform_neg hγ hδ hne (by omega)
  rw [rootReflection_smul hsum γ,
    corootPair_eq_iform_of_simplyLaced (Or.inr (Or.inl rfl)) hsum γ]
  have h1 : iform (γ + δ) γ = 1 := by
    rw [iform_add_left,
      CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hsym hγ,
      iform_comm δ γ, h]
    norm_num
  rw [h1, one_smul]
  abel

theorem tw1w_rootSL2_WSL_mem_rationalSpan
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, S.ρ γ = -γ) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ componentRoots (rootCharHom a) i) :
    rootSL2 Tag.E6 L δ WSL ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hδroot : IsRoot Tag.E6 δ := hδ.1.1
  have hrat : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i :=
    rationalRoots_eq_of_rho_neg S (fun γ _ => hρ γ) i
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [hrat]
    refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) hδroot WSL)
    intro x hx
    rcases hx with rfl | rfl
    · exact hδ
    · exact hΨ.neg_mem δ hδ
  · exact QTwoCav.rootWeylSL2_mem_Γ_of_rho_neg S (Or.inr (Or.inl rfl))
      (f := 1) (by rw [hq2]; norm_num) hAlg hδroot (hρ δ)

theorem tw1w_reflection_mem_of_mem
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, S.ρ γ = -γ) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {δ γ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ componentRoots (rootCharHom a) i)
    (hγ : IsRoot Tag.E6 γ)
    (hγR : rootSL2 Tag.E6 L γ WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    rootSL2 Tag.E6 L (rootReflection δ • γ) WSL ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hδroot : IsRoot Tag.E6 δ := hδ.1.1
  have hδspan := tw1w_rootSL2_WSL_mem_rationalSpan S hq2 hAlg hρ hT i hδ
  have hconj := tw1w_conj_mem_commutator_self hδspan hγR
  rw [tw1w_rootSL2_WSL_conj hγ hδroot] at hconj
  simpa only [rationalComponent] using hconj

theorem tw1w_weyl_mem_of_adj
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, S.ρ γ = -γ) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {b c : Fin Tag.E6.rank → ℤ} (hb : b ∈ componentRoots (rootCharHom a) i)
    (hc : c ∈ componentRoots (rootCharHom a) i) (hadj : iform b c ≠ 0)
    (hbR : rootSL2 Tag.E6 L b WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    rootSL2 Tag.E6 L c WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hbr : IsRoot Tag.E6 b := hb.1.1
  have hcr : IsRoot Tag.E6 c := hc.1.1
  by_cases hbc0 : b = c
  · rw [← hbc0]; exact hbR
  by_cases hbc' : b = -c
  · have hcb : c = -b := by rw [hbc', neg_neg]
    rw [hcb, tw1w_rootSL2_WSL_neg hbr]
    exact hbR
  · have hsym : ∀ j : Fin Tag.E6.rank, Tag.E6.symmetrizer j j = 1 := by decide
    have hmem := CFSG.LieType.Chevalley.SimplyLacedCover.iform_mem hsym hbr hcr hbc0 hbc'
    rcases hmem with h | h | h
    · have hsumroot : IsRoot Tag.E6 (b + c) :=
        isRoot_add_of_iform_neg hbr hcr hbc' (by omega)
      have hsummem : b + c ∈ componentRoots (rootCharHom a) i :=
        hΨ.add_mem b hb c hc hsumroot
      have hreflect : rootReflection (b + c) • b = -c :=
        tw1w_rootReflection_add_eq_neg hbr hcr h
      have hstep := tw1w_reflection_mem_of_mem S hq2 hAlg hρ hT i hsummem hbr hbR
      rw [hreflect] at hstep
      rwa [tw1w_rootSL2_WSL_neg hcr] at hstep
    · exact absurd h hadj
    · have hneg : iform b (-c) = -1 := by rw [iform_neg_right, h]
      have hne : b ≠ -(-c) := by rwa [neg_neg]
      have hsumroot : IsRoot Tag.E6 (b + (-c)) :=
        isRoot_add_of_iform_neg hbr (IsRoot.neg hcr) hne (by omega)
      have hnegmem : -c ∈ componentRoots (rootCharHom a) i := hΨ.neg_mem c hc
      have hsummem : b + (-c) ∈ componentRoots (rootCharHom a) i :=
        hΨ.add_mem b hb (-c) hnegmem hsumroot
      have hreflect : rootReflection (b + (-c)) • b = c := by
        have hh := tw1w_rootReflection_add_eq_neg hbr (IsRoot.neg hcr) hneg
        rwa [neg_neg] at hh
      have hstep := tw1w_reflection_mem_of_mem S hq2 hAlg hρ hT i hsummem hbr hbR
      rwa [hreflect] at hstep

theorem tw1w_ncard_eq_two_or_six
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty)
    (h2 : compRank Ψ ≤ 2) : Ψ.ncard = 2 ∨ Ψ.ncard = 6 := by
  obtain ⟨t, e, ht, hsl, hcart, hcardΔ, hN⟩ := exists_dynkinType hτ hΨ hne
  have hrank : t.rank ≤ 2 := by
    rw [← hcardΔ, ← compRank_eq_card hΨ]
    exact h2
  rcases t with n | n | n | n | _ | _ | _ | _ | _
  · simp only [TauCeti.DynkinType.rank_A] at hrank
    interval_cases n
    · exfalso
      have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
      have hpos : 0 < Ψ.ncard := (Set.ncard_pos hfin).2 hne
      simp only [TauCeti.DynkinType.numRoots_A] at hN
      omega
    · left
      simp only [TauCeti.DynkinType.numRoots_A] at hN
      norm_num at hN
      exact hN
    · right
      simp only [TauCeti.DynkinType.numRoots_A] at hN
      norm_num at hN
      exact hN
  · exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_B n)
  · exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_C n)
  · have hn : 4 ≤ n := TauCeti.DynkinType.valid_D.1 ht
    simp only [TauCeti.DynkinType.rank_D] at hrank
    omega
  · simp only [TauCeti.DynkinType.rank_E6] at hrank
    omega
  · simp only [TauCeti.DynkinType.rank_E7] at hrank
    omega
  · simp only [TauCeti.DynkinType.rank_E8] at hrank
    omega
  · exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_F4
  · exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_G2

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.ExcPos.ContainingComponent
public import CFSG.LocalAnalysis.StandardType.ExcPos.RankOneWeyl
public import CFSG.LocalAnalysis.StandardType.ExcPos.RankOneInner
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RootSpanMap
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart14
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ratOrbit_eq_union_of_two_period {τ : Tag}
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (hperiod : ρ '' (ρ '' Ψ) = Ψ) :
    CFSG.StandardType.LieCore.ratOrbit ρ Ψ = Ψ ∪ ρ '' Ψ := by
  have hstable : ρ '' (Ψ ∪ ρ '' Ψ) ⊆ Ψ ∪ ρ '' Ψ := by
    rw [Set.image_union, hperiod, Set.union_comm]
  have hiter : ∀ (k : ℕ) (α : Fin τ.rank → ℤ), α ∈ Ψ → ρ^[k] α ∈ Ψ ∪ ρ '' Ψ := by
    intro k
    induction k with
    | zero => intro α hα; exact Or.inl hα
    | succ k ih =>
      intro α hα
      rw [Function.iterate_succ_apply']
      exact hstable (Set.mem_image_of_mem ρ (ih α hα))
  apply Set.Subset.antisymm
  · rintro α ⟨k, β, hβ, rfl⟩
    exact hiter k β hβ
  · intro α hα
    rcases hα with hα | ⟨β, hβ, rfl⟩
    · exact ⟨0, α, hα, rfl⟩
    · exact ⟨1, β, hβ, rfl⟩


theorem root_eq_or_neg_of_fixed_family_bruhat
    {τ : Tag} {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
    {I : Type} (a : I → Fin τ.rank → Lˣ) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (hkernel : kernelRoots χ = familyKernel a) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpair : componentRoots χ i = {γ, -γ})
    (D : LangDatum τ L) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (hkerρ : Set.MapsTo ρ (kernelRoots χ) (kernelRoots χ))
    (hperiod : ρ '' (ρ '' componentRoots χ i) = componentRoots χ i)
    (K : Subgroup (ModGL τ L)) (hKmodel : K ≤ D.model)
    (hK : K ≤ rootSpan τ L (CFSG.StandardType.LieCore.ratOrbit ρ (componentRoots χ i)))
    (hKnoncomm : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x)
    {g m : ModGL τ L} {w : WeylGroup τ}
    (hm : m ∈ familyGroup (K := L) a) (hw : w ∈ familyStabilizer a)
    (hg : g = m * canonicalRep (coxeterSystem τ) L w)
    (hfix : D.step g = g) (hNg : g ∈ Subgroup.normalizer (K : Set (ModGL τ L)))
    (hodd : Odd (orderOf (MulAut.conj g))) : w • γ = γ ∨ w • γ = -γ := by
  classical
  let σ : Equiv.Perm (Fin τ.rank → ℤ) := MulAction.toPerm w
  have hσker : Set.MapsTo σ (kernelRoots χ) (kernelRoots χ) := by
    intro δ hδ
    change w • δ ∈ kernelRoots χ
    rw [hkernel] at hδ ⊢
    exact (image_familyKernel hw).subset ⟨δ, hδ, rfl⟩
  have hσform : ∀ α β, iform (σ α) (σ β) = iform α β := fun α β => iform_smul w α β
  obtain ⟨j, hj⟩ := exists_image_componentRoots hσker hσform i
  have hpairj : componentRoots χ j = {w • γ, -(w • γ)} := by
    rw [← hj, hpair]
    simp only [Set.image_pair, σ, MulAction.toPerm_apply, smul_neg]
  let H := componentRootSpan L χ i
  let H' := componentRootSpan L χ j
  let H₂ := H.map D.step
  have hmconn : m ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) := by
    simpa only [familyGroup, hkernel] using hm
  have hmH' : m ∈ H' ⊔ Subgroup.centralizer (H' : Set (ModGL τ L)) :=
    torus_sup_kernelRootSpan_le_component_sup_centralizer_of_pair χ j
      (CFSG.LieType.Chevalley.IsRoot.smul hγ w) hpairj hmconn
  have hmN : m ∈ Subgroup.normalizer (H' : Set (ModGL τ L)) :=
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)) hmH'
  have hmapm : H'.map (MulAut.conj m).toMonoidHom = H' :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hmN
  have hmapw : H.map (MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom = H' := by
    change (rootSpan τ L (componentRoots χ i)).map _ = rootSpan τ L (componentRoots χ j)
    rw [(canonical_weyl_root_transport τ L).1 w _ (fun δ hδ => hδ.1.1)]
    rw [← hj]
    rfl
  have hconj : (MulAut.conj g).toMonoidHom =
      (MulAut.conj m).toMonoidHom.comp
        (MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom := by
    rw [hg, map_mul]
    rfl
  have hmapg : H.map (MulAut.conj g).toMonoidHom = H' := by
    rw [hconj, ← Subgroup.map_map, hmapw, hmapm]
  obtain ⟨i₂, hi₂⟩ := exists_image_componentRoots hkerρ hρ.iform_eq i
  have hH₂ : H₂ = componentRootSpan L χ i₂ := by
    change (rootSpan τ L (componentRoots χ i)).map D.step = _
    rw [FrobRootMap.map_rootSpan hρ _ (fun δ hδ => hδ.1.1), hi₂]
    rfl
  have hH₂F : H₂.map D.step = H := by
    change ((rootSpan τ L (componentRoots χ i)).map D.step).map D.step = _
    rw [FrobRootMap.map_rootSpan hρ _ (fun δ hδ => hδ.1.1)]
    rw [FrobRootMap.map_rootSpan hρ _ (by
      rintro δ ⟨α, hα, rfl⟩
      exact (hρ.isRoot_iff α).2 hα.1.1), hperiod]
    rfl
  have hU : rootSpan τ L (CFSG.StandardType.LieCore.ratOrbit ρ (componentRoots χ i)) = H ⊔ H₂ := by
    rw [ratOrbit_eq_union_of_two_period ρ _ hperiod,
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.rootSpan_union_eq]
    rw [← FrobRootMap.map_rootSpan hρ _ (fun δ hδ => hδ.1.1)]
    rfl
  have hKsup : K ≤ H ⊔ H₂ := by simpa only [hU] using hK
  have hKmap : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hNg
  have hjcases : j = i ∨ j = i₂ := by
    by_contra hjbad
    have hji : j ≠ i := fun h => hjbad (Or.inl h)
    have hji₂ : j ≠ i₂ := fun h => hjbad (Or.inr h)
    have hH'K : ∀ u ∈ H', ∀ v ∈ K, u * v = v * u := by
      intro u hu v hv
      have hCH : H ≤ Subgroup.centralizer ({u} : Set (ModGL τ L)) := by
        intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commute_of_mem_componentRootSpan hji hu hz).eq.symm
      have hCH₂ : H₂ ≤ Subgroup.centralizer ({u} : Set (ModGL τ L)) := by
        rw [hH₂]
        intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commute_of_mem_componentRootSpan hji₂ hu hz).eq.symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hCH hCH₂) (hKsup hv))).symm
    have hHK : ∀ v ∈ K, H ≤ Subgroup.centralizer ({v} : Set (ModGL τ L)) := by
      intro v hv u hu
      have hgu : (MulAut.conj g) u ∈ H' := by
        rw [← hmapg]
        exact ⟨u, hu, rfl⟩
      have hgv : (MulAut.conj g) v ∈ K := by
        rw [← hKmap]
        exact ⟨v, hv, rfl⟩
      have hcomm := hH'K _ hgu _ hgv
      have heq : (MulAut.conj g) (u * v) = (MulAut.conj g) (v * u) := by
        simpa only [map_mul] using hcomm
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (MulAut.conj g).injective heq
    obtain ⟨v, hv, z, hz, hvz⟩ := hKnoncomm
    have hvF : D.step v = v := ((LangDatum.mem_model (D := D)).mp (hKmodel hv)).2
    have hUC := CFSG.StandardType.F4ExplicitPos.OrbitKernel.rootSpan_ratOrbit_le_centralizer_of_fixed
      D ρ hρ (fun δ hδ => hδ.1.1) hvF (hHK v hv)
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hUC (hK hz))
    exact hvz hcomm.symm
  have hP : H.map (MulAut.conj g).toMonoidHom = H ∨
      H.map (MulAut.conj g).toMonoidHom = H₂ := by
    rcases hjcases with hji | hji₂
    · left
      simpa only [H, H', hji] using hmapg
    · right
      simpa only [H', hji₂, hH₂] using hmapg
  have hQ : H₂.map (MulAut.conj g).toMonoidHom = H ∨
      H₂.map (MulAut.conj g).toMonoidHom = H₂ := by
    have hcommmap : H₂.map (MulAut.conj g).toMonoidHom =
        (H.map (MulAut.conj g).toMonoidHom).map D.step := by
      simpa only [hfix] using (Subgroup.map_map_conj H D.step g).symm
    rw [hcommmap]
    rcases hP with hP | hP
    · right
      rw [hP]
    · left
      rw [hP, hH₂F]
  have hfixedH : H.map (MulAut.conj g).toMonoidHom = H := by
    by_cases heq : H = H₂
    · rcases hP with hP | hP
      · exact hP
      · exact hP.trans heq.symm
    · exact (CFSG.QuasithinUnique.B113Lie.map_eq_self_of_odd_of_pair hodd heq hP hQ).1
  have hH'eq : H' = H := hmapg.symm.trans hfixedH
  have hZH : Subgroup.center H = ⊥ := by
    have hHpair : H = rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ) :=
      (congrArg (rootSpan τ L) hpair).trans (CFSG.LieType.HighestRoot.rootSpan_pair_eq γ)
    let e : SL2 L ≃* H := (rootSL2Equiv hγ).trans (MulEquiv.subgroupCongr hHpair.symm)
    rw [← Subgroup.map_center_eq e,
      CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot_of_two_eq_zero CharTwo.two_eq_zero,
      Subgroup.map_bot]
  have hji : j = i := by
    by_contra hji
    have hHbot : H = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      let zH : H := ⟨z, hz⟩
      have hzC : zH ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro u
        apply Subtype.ext
        have hz' : z ∈ H' := by rw [hH'eq]; exact hz
        exact (commute_of_mem_componentRootSpan (fun hij : i = j => hji hij.symm) u.2 hz').eq
      have hz1 : zH = 1 := by simpa only [hZH, Subgroup.mem_bot] using hzC
      exact congrArg (fun z : H => (z : ModGL τ L)) hz1
    have hKbot : K ≤ ⊥ := by simpa only [H₂, hHbot, Subgroup.map_bot, sup_idem] using hKsup
    obtain ⟨v, hv, z, hz, hvz⟩ := hKnoncomm
    have hv1 : v = 1 := Subgroup.mem_bot.mp (hKbot hv)
    have hz1 : z = 1 := Subgroup.mem_bot.mp (hKbot hz)
    exact hvz (by rw [hv1, hz1])
  have hγi : w • γ ∈ componentRoots χ j := by
    rw [← hj]
    exact Set.mem_image_of_mem σ (by rw [hpair]; simp)
  rw [hji, hpair] at hγi
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hγi

end CFSG.StandardType.LieKnownR2.ExcPos

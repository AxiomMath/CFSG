module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralFixedBruhat
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRoots
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRankOne

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TrialityFold
open scoped Pointwise

section Generic

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem map_conj_rootSpan_of_mem_torusGroup {τ : Tag} {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    (rootSpan τ K S).map (MulAut.conj h).toMonoidHom = rootSpan τ K S := by
  simp only [rootSpan, Subgroup.map_iSup]
  exact iSup_congr fun α => iSup_congr fun hα =>
    map_conj_rootSubgroup_of_mem_torusGroup hh (hS α hα)

theorem conj_mem_graphFixedRootPair {O : Set (Fin t.tag.rank → ℤ)}
    (hO : ∀ α ∈ O, IsRoot t.tag α) {h : ModGL t.tag K} (hh : h ∈ graphFixedRootTorus t K σ)
    {x : ModGL t.tag K} (hx : x ∈ graphFixedRootPair t K σ O) :
    h * x * h⁻¹ ∈ graphFixedRootPair t K σ O := by
  have hT : h ∈ torusGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
  have hΓ : h ∈ twistedFixedGroup t K σ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).2
  have hO' : ∀ α ∈ -O, IsRoot t.tag α := fun α hα => by
    have := IsRoot.neg (hO _ (Set.mem_neg.1 hα))
    rwa [neg_neg] at this
  have hΓmap : (twistedFixedGroup t K σ).map (MulAut.conj h).toMonoidHom ≤
      twistedFixedGroup t K σ := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hΓ hy) (inv_mem hΓ)
  have hle : (graphFixedRootPair t K σ O).map (MulAut.conj h).toMonoidHom ≤
      graphFixedRootPair t K σ O := by
    rw [graphFixedRootPair, Subgroup.map_sup]
    refine sup_le_sup ((Subgroup.map_inf_le _ _ _).trans (inf_le_inf ?_ hΓmap))
      ((Subgroup.map_inf_le _ _ _).trans (inf_le_inf ?_ hΓmap))
    · rw [map_conj_rootSpan_of_mem_torusGroup hT hO]
    · rw [map_conj_rootSpan_of_mem_torusGroup hT hO']
  exact hle ⟨x, hx, rfl⟩

theorem graphFixedRootTorus_le_normalizer {O : Set (Fin t.tag.rank → ℤ)}
    (hO : ∀ α ∈ O, IsRoot t.tag α) :
    graphFixedRootTorus t K σ ≤
      Subgroup.normalizer (graphFixedRootPair t K σ O : Set (ModGL t.tag K)) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_graphFixedRootPair hO hh, fun hx => ?_⟩
  have := conj_mem_graphFixedRootPair hO (inv_mem hh) hx
  rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this

end Generic

section Triality

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem isRoot_of_mem_fixedOrbitImage {t : TwistTag} {v : WeylGroup t.tag}
    {b : Fin t.foldedTag.rank} {β : Fin t.tag.rank → ℤ} (hβ : β ∈ fixedOrbitImage t v b) :
    IsRoot t.tag β := by
  obtain ⟨i, -, rfl⟩ := hβ
  exact IsRoot.smul (isRoot_single t.tag i) v

theorem triality_toral_centralizer_cases {a : Fin TwistTag.D4.tag.rank → Kˣ} {A B : Kˣ}
    (h0 : a i0 = A) (h1 : a i1 = A) (h2 : a i2 = B) (h3 : a i3 = A) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hA : A ^ p = 1) (hB : B ^ p = 1) (hAB : ¬(A = 1 ∧ B = 1)) :
    (rootCharKernel a = ∅ ∧
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
          Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} =
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom) ∨
    (∃ v ∈ relWeylTwist TwistTag.D4, ∃ b : Fin TwistTag.D4.foldedTag.rank,
      rootCharKernel a = fixedOrbitImage TwistTag.D4 v b ∪ -fixedOrbitImage TwistTag.D4 v b ∧
      (∀ β ∈ fixedOrbitImage TwistTag.D4 v b, 0 < height β) ∧
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
          Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} =
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
          graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b) ∧
      ((graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
          Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} : Subgroup _) :
            Set (ModGL TwistTag.D4.tag K)) =
        (graphFixedRootTorus TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) *
          (graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b) :
            Set (ModGL TwistTag.D4.tag K))) := by
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hH
  set d := rootDiagUnit TwistTag.D4.tag a with hd
  have hHle : H ≤ C ⊓ Subgroup.centralizer {d} := fun h hh =>
    Subgroup.mem_inf.2 ⟨graphFixedRootTorus_le _ _ _ hh, conj_eq_iff_mem_centralizer.1
      (conj_rootDiagUnit_of_mem_torusGroup a
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1)⟩
  rcases rootCharKernel_cases h0 h1 h2 h3 hp hp3 hA hB hAB with hker | ⟨α, hαr, hαpos, hker⟩
  ·
    refine Or.inl ⟨hker, le_antisymm (fun g hg => ?_) hHle⟩
    obtain ⟨w, hwρ, hwa, h, hh, u, hu, v, hv, rfl⟩ :=
      graphFixed_toral_centralizer_Bruhat_factors TwistTag.D4 K σ a (Subgroup.mem_inf.1 hg).1
        (Subgroup.mem_inf.1 hg).2
    have hw1 : w = 1 := by
      rcases rootCharStabilizer_cases h0 h1 h2 h3 hp hp3 hA hB hAB hwρ hwa with h1' | ⟨hne, -⟩
      · exact h1'
      · exact absurd hker (Set.nonempty_iff_ne_empty.1 hne)
    have hbot : ∀ S : Set (Fin TwistTag.D4.tag.rank → ℤ),
        rootSpan TwistTag.D4.tag K (rootCharKernel a ∩ S) = ⊥ := fun S => by
      rw [hker, Set.empty_inter]
      simp [rootSpan]
    rw [hbot, bot_inf_eq, Subgroup.mem_bot] at hu hv
    rw [hu, hv, hw1, canonicalRep_one, mul_one, mul_one, mul_one]
    exact hh
  ·
    right
    obtain ⟨v₀, hv₀, b, hO⟩ := TwistTag.D4.exists_diagramOrbit_eq hαr
    have hOset : (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
        fixedOrbitImage TwistTag.D4 v₀ b := by
      rw [hO, Finset.coe_image]
      rfl
    rw [hOset] at hker
    set O := fixedOrbitImage TwistTag.D4 v₀ b with hOdef
    set Q := graphFixedRootPair TwistTag.D4 K σ.toRingHom O with hQdef
    have hOpos : ∀ β ∈ O, 0 < height β := fun β hβ => by
      rw [← hOset] at hβ
      rw [TwistTag.D4.height_of_mem_diagramOrbit hβ]
      exact hαpos
    have hOroot : ∀ β ∈ O, IsRoot TwistTag.D4.tag β := fun β hβ =>
      isRoot_of_mem_fixedOrbitImage hβ
    have hOker : O ⊆ rootCharKernel a := fun β hβ => by
      rw [hker]
      exact Or.inl hβ
    have hnegOker : -O ⊆ rootCharKernel a := fun β hβ => by
      rw [hker]
      exact Or.inr hβ
    have hQrange := range_orbitConjRankOneHom (K := K) (σ := σ.toRingHom) hv₀ b
    have hQC : Q ≤ C := by
      rw [hQdef, ← hQrange]
      rintro _ ⟨g, rfl⟩
      exact orbitConjRankOneHom_mem_graphFixedRootGroup hv₀ b g
    have hQd : Q ≤ Subgroup.centralizer {d} :=
      sup_le (inf_le_left.trans (rootSpan_le_centralizer a hOker))
        (inf_le_left.trans (rootSpan_le_centralizer a hnegOker))
    have hpos : ∀ S : Set (Fin TwistTag.D4.tag.rank → ℤ),
        S ⊆ {β | IsRoot TwistTag.D4.tag β ∧ 0 < height β} → rootCharKernel a ∩ S ⊆ O := by
      intro S hS β ⟨hβk, hβS⟩
      rw [hker] at hβk
      rcases hβk with h | h
      · exact h
      · exfalso
        have h1 := hOpos _ (Set.mem_neg.1 h)
        have h2 := (hS hβS).2
        rw [height_neg] at h1
        omega
    have hle : C ⊓ Subgroup.centralizer {d} ≤ H ⊔ Q := by
      intro g hg
      obtain ⟨w, hwρ, hwa, h, hh, u, hu, v, hv, rfl⟩ :=
        graphFixed_toral_centralizer_Bruhat_factors TwistTag.D4 K σ a (Subgroup.mem_inf.1 hg).1
          (Subgroup.mem_inf.1 hg).2
      have huQ : u ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_inf.2
        ⟨rootSpan_mono (hpos _ fun β hβ => hβ) (Subgroup.mem_inf.1 hu).1,
          (Subgroup.mem_inf.1 hu).2⟩)
      have hvQ : v ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_inf.2
        ⟨rootSpan_mono (hpos _ fun β hβ => ⟨hβ.1, hβ.2.1⟩) (Subgroup.mem_inf.1 hv).1,
          (Subgroup.mem_inf.1 hv).2⟩)
      have hnw : canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∈ H ⊔ Q := by
        rcases rootCharStabilizer_cases h0 h1 h2 h3 hp hp3 hA hB hAB hwρ hwa with hw1 | ⟨-, hw⟩
        · rw [hw1, canonicalRep_one]
          exact one_mem _
        · rw [hw v₀ hv₀ b fun i hi => hOker ⟨i, hi, rfl⟩]
          obtain ⟨h', hh', he⟩ := exists_canonicalRep_eq_mul_orbitConjRankOneHom
            (K := K) (σ := σ.toRingHom) hv₀ b
          rw [he]
          refine mul_mem (Subgroup.mem_sup_left hh') (Subgroup.mem_sup_right ?_)
          rw [hQdef, ← hQrange]
          exact ⟨_, rfl⟩
      exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right huQ))
        hnw) (Subgroup.mem_sup_right hvQ)
    have heq : C ⊓ Subgroup.centralizer {d} = H ⊔ Q :=
      le_antisymm hle (sup_le hHle (le_inf hQC hQd))
    refine ⟨v₀, hv₀, b, hker, hOpos, heq, ?_⟩
    rw [heq]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (graphFixedRootTorus_le_normalizer hOroot)

end Triality

end CFSG.RankThree.Chevalley

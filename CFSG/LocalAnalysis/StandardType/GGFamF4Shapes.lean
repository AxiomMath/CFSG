module

public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddShapesPart2
import CFSG.LocalAnalysis.StandardType.GGFamF4Isolate

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KF4 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.F4Pilot CFSG.LieType.Chevalley

@[expose] def FamF4PairShape (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  ∃ (w : WeylGroup Tag.F4) (j : Fin Tag.F4.rank),
    Ψ = (fun α => w • α) '' ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))

@[expose] def FamF4LongA2Shape (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.F4, Ψ = (fun α => w • α) '' parabolicRoots Tag.F4 f4LongSupport

@[expose] def FamF4ShortA2Shape (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.F4, Ψ = (fun α => w • α) '' parabolicRoots Tag.F4 f4ShortSupport

@[expose] def FamF4B2Shape (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.F4, Ψ = (fun α => w • α) '' b2LeviRoots

@[expose] def FamF4B3Shape (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.F4, Ψ = (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviB3

@[expose] def FamF4C3Shape (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.F4, Ψ = (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviC3

private theorem l10lH1_single_ne_neg (j : Fin Tag.F4.rank) :
    (Pi.single j (1 : ℤ) : Fin Tag.F4.rank → ℤ) ≠ -Pi.single j (1 : ℤ) := by
  intro h
  have h1 : ((Pi.single j (1 : ℤ) : Fin Tag.F4.rank → ℤ) j) = 1 := by simp
  have h2 : ((-Pi.single j (1 : ℤ) : Fin Tag.F4.rank → ℤ) j) = -1 := by simp
  rw [h] at h1
  rw [h2] at h1
  norm_num at h1

private theorem l10lH1_compRank_pair (j : Fin Tag.F4.rank) :
    compRank ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) = 1 := by
  have hset : (fun γ (i : Fin Tag.F4.rank) => (γ i : ℚ)) ''
      ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) =
      ({Pi.single j (1 : ℚ), -Pi.single j (1 : ℚ)} : Set (Fin Tag.F4.rank → ℚ)) := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rcases hγ with rfl | rfl
      · left
        funext i
        by_cases h : i = j <;> simp [h]
      · right
        funext i
        by_cases h : i = j <;> simp [h]
    · rintro (rfl | rfl)
      · exact ⟨Pi.single j 1, Or.inl rfl, by
          funext i
          by_cases h : i = j <;> simp [h]⟩
      · exact ⟨-Pi.single j 1, Or.inr rfl, by
          funext i
          by_cases h : i = j <;> simp [h]⟩
  have hspan : Submodule.span ℚ
      ({Pi.single j (1 : ℚ), -Pi.single j (1 : ℚ)} : Set (Fin Tag.F4.rank → ℚ)) =
      Submodule.span ℚ {Pi.single j (1 : ℚ)} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Submodule.subset_span (by simp)
  have hv : (Pi.single j (1 : ℚ) : Fin Tag.F4.rank → ℚ) ≠ 0 := by
    intro hz
    have := congrFun hz j
    simp at this
  rw [compRank, hset, hspan, finrank_span_singleton hv]

private theorem l10lH1_sixShape_disj {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (h : l10lH1_SixShape Ψ) :
    FamF4PairShape Ψ ∨ FamF4LongA2Shape Ψ ∨ FamF4ShortA2Shape Ψ ∨ FamF4B2Shape Ψ ∨
      FamF4B3Shape Ψ ∨ FamF4C3Shape Ψ := by
  unfold FamF4PairShape FamF4LongA2Shape FamF4ShortA2Shape FamF4B2Shape FamF4B3Shape FamF4C3Shape
  rcases h with ⟨w, hA | hlong | hshort | hb2 | hb3 | hc3⟩
  · rcases hA with ⟨j, hj⟩
    exact Or.inl ⟨w, j, hj⟩
  · exact Or.inr (Or.inl ⟨w, hlong⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨w, hshort⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, hb2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨w, hb3⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hc3⟩))))

theorem famF4_shape
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a)) :
    FamF4PairShape (componentRoots (famCharHom a) i) ∨
      FamF4LongA2Shape (componentRoots (famCharHom a) i) ∨
      FamF4ShortA2Shape (componentRoots (famCharHom a) i) ∨
      FamF4B2Shape (componentRoots (famCharHom a) i) ∨
      FamF4B3Shape (componentRoots (famCharHom a) i) ∨
      FamF4C3Shape (componentRoots (famCharHom a) i) := by
  classical
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  obtain ⟨u₀, hu₀⟩ := h1
  let T := {γ : Fin Tag.F4.rank → ℤ // IsRoot Tag.F4 γ ∧ γ ∉ kernelRoots (famCharHom a)}
  have hfinT : Finite T :=
    ((finite_setOf_isRoot Tag.F4).subset
      fun γ (hγ : IsRoot Tag.F4 γ ∧ γ ∉ kernelRoots (famCharHom a)) => hγ.1).to_subtype
  let : Fintype T := Fintype.ofFinite T
  have hch : ∀ γ : T, ∃ u : ι, rootChar (a u) γ.1 ≠ 1 := by
    intro γ
    by_contra h
    simp only [not_exists, not_not] at h
    exact γ.2.2 ((mem_kernelRoots_famChar a).2 ⟨γ.2.1, h⟩)
  let f : T → Fin Tag.F4.rank → Lˣ := fun γ => a (Classical.choose (hch γ))
  have hf : ∀ γ : T, f γ = a (Classical.choose (hch γ)) := fun γ => rfl
  let F : Finset (Fin Tag.F4.rank → Lˣ) := insert (a u₀) (Finset.univ.image f)
  have hF_ptor : ∀ b ∈ F, ∀ i, b i ^ p = 1 := by
    intro b hb i
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hap u₀ i
    · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.1 hb
      rw [hf]
      exact hap (Classical.choose (hch γ)) i
  have hF_ne : ∃ b ∈ F, rootDiagUnit Tag.F4 b ≠ 1 :=
    ⟨a u₀, Finset.mem_insert_self _ _, hu₀⟩
  have hFker : kernelRoots (famCharHom (fun b : ↥F => (b : Fin Tag.F4.rank → Lˣ))) =
      kernelRoots (famCharHom a) := by
    ext γ
    simp only [mem_kernelRoots_famChar]
    constructor
    · rintro ⟨hroot, hall⟩
      refine ⟨hroot, fun u => ?_⟩
      by_contra hneu
      have hnotK : γ ∉ kernelRoots (famCharHom a) := by
        intro hK
        exact hneu (((mem_kernelRoots_famChar a).1 hK).2 u)
      have hmem : f ⟨γ, hroot, hnotK⟩ ∈ F :=
        Finset.mem_insert.2
          (Or.inr (Finset.mem_image.2 ⟨⟨γ, hroot, hnotK⟩, Finset.mem_univ _, rfl⟩))
      have h1' : rootChar (f ⟨γ, hroot, hnotK⟩) γ = 1 :=
        hall ⟨f ⟨γ, hroot, hnotK⟩, hmem⟩
      rw [hf] at h1'
      exact (Classical.choose_spec (hch ⟨γ, hroot, hnotK⟩)) h1'
    · rintro ⟨hroot, hall⟩
      refine ⟨hroot, fun b => ?_⟩
      rcases Finset.mem_insert.1 b.2 with hb | hb
      · rw [hb]; exact hall u₀
      · obtain ⟨γ, -, hb'⟩ := Finset.mem_image.1 hb
        rw [← hb']
        exact hall (Classical.choose (hch γ))
  let χF : Multiplicative (Fin Tag.F4.rank → ℤ) →* (↥F → Lˣ) :=
    famCharHom (fun b : ↥F => (b : Fin Tag.F4.rank → Lˣ))
  obtain ⟨⟨γ₀, hγ₀⟩, rfl⟩ := Quotient.exists_rep i
  have hγ₀F : γ₀ ∈ kernelRoots χF := hFker.ge hγ₀
  have hshape : l10lH1_SixShape (componentRoots χF (⟦⟨γ₀, hγ₀F⟩⟧ : KernelComponent χF)) :=
    l10lH1_shape_finset hp.pos hpodd F hF_ptor hF_ne (⟦⟨γ₀, hγ₀F⟩⟧ : KernelComponent χF)
  have heq : componentRoots (famCharHom a) (⟦⟨γ₀, hγ₀⟩⟧ : KernelComponent (famCharHom a)) =
      componentRoots χF (⟦⟨γ₀, hγ₀F⟩⟧ : KernelComponent χF) :=
    OddToralOrdinary.componentRoots_eq_of_kernelRoots_eq hFker.symm hγ₀ hγ₀F
  exact l10lH1_sixShape_disj (heq.symm ▸ hshape)

theorem famF4_pairShape_rankCard {Ψ : Set (Fin Tag.F4.rank → ℤ)} (h : FamF4PairShape Ψ) :
    compRank Ψ = 1 ∧ Ψ.ncard = 2 := by
  rw [FamF4PairShape] at h
  obtain ⟨w, j, hΨ⟩ := h
  constructor
  · rw [hΨ, compRank_image, l10lH1_compRank_pair j]
  · rw [hΨ, ncard_image_smul, Set.ncard_pair (l10lH1_single_ne_neg j)]

end CFSG.StandardType.TableCRes

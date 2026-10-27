module

public import CFSG.Timmesfeld.RankTwo.Levi

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace Levi

theorem exists_hom_of_relationsHold {I : Type*} {K : Type*} [Group K]
    {X : (I → ℤ) → Subgroup K} {S : Set (I → ℤ)} {G : Type*} [Group G] {ψ : ∀ γ, X γ → G}
    (h : CurtisTits.RelationsHold X S ψ) :
    ∃ θ : ↥(⨆ γ ∈ S, X γ) →* G, ∀ γ ∈ S, ∀ (x : X γ) (hx : (x : K) ∈ ⨆ γ ∈ S, X γ),
      θ ⟨x, hx⟩ = ψ γ x := by
  let T := {p : Σ γ : I → ℤ, X γ // p.1 ∈ S}
  let π : FreeGroup T →* K := FreeGroup.lift fun t => (t.1.2 : K)
  let φ : FreeGroup T →* G := FreeGroup.lift fun t => ψ t.1.1 t.1.2
  have hinv : ∀ γ ∈ S, ∀ x : X γ, ψ γ x⁻¹ = (ψ γ x)⁻¹ := fun γ hγ x => by
    have := h [⟨γ, x⟩, ⟨γ, x⁻¹⟩] (by simp [hγ]) (by simp)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact eq_inv_of_mul_eq_one_right this
  have hlist : ∀ w : FreeGroup T, ∃ l : List (Σ γ : I → ℤ, X γ), (∀ p ∈ l, p.1 ∈ S) ∧
      π w = (l.map fun p => (p.2 : K)).prod ∧ φ w = (l.map fun p => ψ p.1 p.2).prod := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => exact ⟨[], by simp, by simp, by simp⟩
    | of t => exact ⟨[t.1], by simpa using t.2, by simp [π], by simp [φ]⟩
    | inv_of t _ =>
      refine ⟨[⟨t.1.1, t.1.2⁻¹⟩], by simpa using t.2, by simp [π], ?_⟩
      simp [φ, hinv _ t.2]
    | mul x y hx hy =>
      obtain ⟨l, hl, h1, h2⟩ := hx
      obtain ⟨l', hl', h1', h2'⟩ := hy
      refine ⟨l ++ l', fun p hp => ?_, by simp [h1, h1'], by simp [h2, h2']⟩
      rcases List.mem_append.mp hp with hp | hp
      exacts [hl p hp, hl' p hp]
  have hker : π.rangeRestrict.ker ≤ φ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro w hw
    obtain ⟨l, hl, h1, h2⟩ := hlist w
    rw [MonoidHom.mem_ker, h2]
    exact h l hl (h1 ▸ hw)
  have hle : ⨆ γ ∈ S, X γ ≤ π.range := by
    refine iSup₂_le fun γ hγ x hx => ⟨FreeGroup.of ⟨⟨γ, ⟨x, hx⟩⟩, hγ⟩, ?_⟩
    simp [π]
  let θ₀ : π.range →* G := π.rangeRestrict.liftOfRightInverse
    (Function.surjInv π.rangeRestrict_surjective)
    (Function.rightInverse_surjInv π.rangeRestrict_surjective) ⟨φ, hker⟩
  refine ⟨θ₀.comp (Subgroup.inclusion hle), fun γ hγ x hx => ?_⟩
  have hx' : (Subgroup.inclusion hle ⟨x, hx⟩ : π.range) =
      π.rangeRestrict (FreeGroup.of ⟨⟨γ, x⟩, hγ⟩) := Subtype.ext (by simp [π])
  rw [MonoidHom.comp_apply, hx', MonoidHom.liftOfRightInverse_comp_apply]
  simp [φ]

theorem hom_ext_of_le_sup {K G : Type*} [Group K] [Group G] {A B C : Subgroup K}
    (hAC : A ≤ C) (hBC : B ≤ C) (hC : C ≤ A ⊔ B) {θ θ' : ↥C →* G}
    (hA : ∀ (x : K) (hx : x ∈ A), θ ⟨x, hAC hx⟩ = θ' ⟨x, hAC hx⟩)
    (hB : ∀ (x : K) (hx : x ∈ B), θ ⟨x, hBC hx⟩ = θ' ⟨x, hBC hx⟩) : θ = θ' := by
  ext ⟨y, hy⟩
  have hle : A ⊔ B ≤ (MonoidHom.eqLocus θ θ').map C.subtype :=
    sup_le (fun x hx => ⟨⟨x, hAC hx⟩, hA x hx, rfl⟩) (fun x hx => ⟨⟨x, hBC hx⟩, hB x hx, rfl⟩)
  obtain ⟨z, hz, hzy⟩ := hle (hC hy)
  obtain rfl : z = ⟨y, hy⟩ := Subtype.ext hzy
  exact hz

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

theorem single_mem_pairRoots {i j k : Fin D.rank} (hk : k = i ∨ k = j) :
    Pi.single k 1 ∈ pairRoots D i j ∧ -Pi.single k 1 ∈ pairRoots D i j := by
  have hΦ := RootSystem.isCTRootSystem D.isFiniteType D.divisible
  have hneg : -Pi.single k 1 ∈ D.roots := by
    have := hΦ.smul_mem ((RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k) _
      (hΦ.single_mem k)
    rwa [hΦ.simple_single] at this
  have hz : ∀ l, l ≠ i → l ≠ j → (Pi.single k 1 : Fin D.rank → ℤ) l = 0 := fun l hi hj =>
    Pi.single_eq_of_ne (by rintro rfl; rcases hk with rfl | rfl <;> simp_all) _
  exact ⟨⟨hΦ.single_mem k, hz⟩, ⟨hneg, fun l hi hj => by simp [hz l hi hj]⟩⟩

theorem rootGroup_single_le_rankOne (k : Fin D.rank) :
    D.rootGroup (Pi.single k 1) ≤ CurtisTits.rankOne D.rootGroup k := le_sup_left

theorem rootGroup_neg_single_le_rankOne (k : Fin D.rank) :
    D.rootGroup (-Pi.single k 1) ≤ CurtisTits.rankOne D.rootGroup k := le_sup_right

theorem levi_le_iSup_pairRoots (i j : Fin D.rank) :
    CurtisTits.levi D.rootGroup {i, j} ≤ ⨆ γ ∈ pairRoots D i j, D.rootGroup γ := by
  refine iSup₂_le fun k hk => sup_le ?_ ?_
  · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ pairRoots D i j) => D.rootGroup γ) _
      (single_mem_pairRoots (by simpa using hk)).1 le_rfl
  · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ pairRoots D i j) => D.rootGroup γ) _
      (single_mem_pairRoots (by simpa using hk)).2 le_rfl

theorem exists_pairCompatible_of_frame (hL : LeviConePresented D) {H : Type} [Group H]
    (ψ : ∀ γ, D.rootGroup γ → H)
    (hcone : ∀ i j, ∀ α ∈ pairRoots D i j, ∀ β ∈ pairRoots D i j,
      ¬ Universal.IsNegMultiple α β →
      ExtendsToHom D.rootGroup (D.cone α β ∩ pairRoots D i j) ψ)
    (hrank : ∀ k, ExtendsToHom D.rootGroup {Pi.single k 1, -Pi.single k 1} ψ) :
    ∃ (φ₁ : ∀ k, CurtisTits.rankOne D.rootGroup k →* H)
      (φ₂ : ∀ i j, CurtisTits.levi D.rootGroup {i, j} →* H), PairCompatible φ₁ φ₂ ∧
      (∀ i j, ∀ γ ∈ pairRoots D i j, ∀ (x : D.rootGroup γ)
        (hx : (x : K) ∈ CurtisTits.levi D.rootGroup {i, j}), φ₂ i j ⟨x, hx⟩ = ψ γ x) ∧
      ∀ k γ, (γ = Pi.single k 1 ∨ γ = -Pi.single k 1) → ∀ (x : D.rootGroup γ)
        (hx : (x : K) ∈ CurtisTits.rankOne D.rootGroup k), φ₁ k ⟨x, hx⟩ = ψ γ x := by
  have hrel : ∀ i j, CurtisTits.RelationsHold D.rootGroup (pairRoots D i j) ψ :=
    fun i j => hL i j H ψ (hcone i j) fun k _ => hrank k
  choose θ hθ using fun i j => exists_hom_of_relationsHold (hrel i j)
  let φ₂ : ∀ i j, CurtisTits.levi D.rootGroup {i, j} →* H :=
    fun i j => (θ i j).comp (Subgroup.inclusion (levi_le_iSup_pairRoots i j))
  have hφ₂ : ∀ i j γ, γ ∈ pairRoots D i j → ∀ (x : D.rootGroup γ)
      (hx : (x : K) ∈ CurtisTits.levi D.rootGroup {i, j}), φ₂ i j ⟨x, hx⟩ = ψ γ x :=
    fun i j γ hγ x hx => hθ i j γ hγ x _
  have hk : ∀ k : Fin D.rank, k ∈ ({k, k} : Finset (Fin D.rank)) := fun k => by simp
  let φ₁ : ∀ k, CurtisTits.rankOne D.rootGroup k →* H :=
    fun k => (φ₂ k k).comp (Subgroup.inclusion (CurtisTits.rankOne_le_levi D.rootGroup (hk k)))
  have hφ₁ : ∀ k γ, (γ = Pi.single k 1 ∨ γ = -Pi.single k 1) → ∀ (x : D.rootGroup γ)
      (hx : (x : K) ∈ CurtisTits.rankOne D.rootGroup k), φ₁ k ⟨x, hx⟩ = ψ γ x := by
    rintro k γ hγ x hx
    refine hφ₂ k k γ ?_ x _
    rcases hγ with rfl | rfl
    exacts [(single_mem_pairRoots (Or.inl rfl)).1, (single_mem_pairRoots (Or.inl rfl)).2]
  refine ⟨φ₁, φ₂, fun i j k hkij x hx hx' => ?_, hφ₂, hφ₁⟩
  have hle : CurtisTits.rankOne D.rootGroup k ≤ CurtisTits.levi D.rootGroup {i, j} :=
    CurtisTits.rankOne_le_levi D.rootGroup (by rcases hkij with rfl | rfl <;> simp)
  have key : (φ₂ i j).comp (Subgroup.inclusion hle) = φ₁ k := by
    refine hom_ext_of_le_sup (rootGroup_single_le_rankOne k)
      (rootGroup_neg_single_le_rankOne k) le_rfl (fun y hy => ?_) (fun y hy => ?_)
    · exact (hφ₂ i j _ (single_mem_pairRoots hkij).1 ⟨y, hy⟩ _).trans
        (hφ₁ k _ (Or.inl rfl) ⟨y, hy⟩ _).symm
    · exact (hφ₂ i j _ (single_mem_pairRoots hkij).2 ⟨y, hy⟩ _).trans
        (hφ₁ k _ (Or.inr rfl) ⟨y, hy⟩ _).symm
  rw [← key]
  rfl

theorem iSup_range_eq_top_of_frame {H : Type} [Group H] {ψ : ∀ γ, D.rootGroup γ → H}
    {φ₁ : ∀ k, CurtisTits.rankOne D.rootGroup k →* H}
    (hφ₁ : ∀ k γ, (γ = Pi.single k 1 ∨ γ = -Pi.single k 1) → ∀ (x : D.rootGroup γ)
      (hx : (x : K) ∈ CurtisTits.rankOne D.rootGroup k), φ₁ k ⟨x, hx⟩ = ψ γ x)
    (hgen : Subgroup.closure (⋃ k, Set.range (ψ (Pi.single k 1)) ∪
      Set.range (ψ (-Pi.single k 1))) = ⊤) : ⨆ k, (φ₁ k).range = ⊤ := by
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨_, ⟨k, rfl⟩, hy⟩
  rcases hy with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact Subgroup.mem_iSup_of_mem k ⟨⟨x, rootGroup_single_le_rankOne k x.2⟩,
      hφ₁ k _ (Or.inl rfl) x _⟩
  · exact Subgroup.mem_iSup_of_mem k ⟨⟨x, rootGroup_neg_single_le_rankOne k x.2⟩,
      hφ₁ k _ (Or.inr rfl) x _⟩

end Levi

variable {K : Type} [Group K] {D : UniversalRootDatum K}

theorem exists_surjective_of_frame {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    {H : Type} [Group H] (ψ : ∀ γ, D.rootGroup γ → H)
    (hcone : ∀ i j, ∀ α ∈ pairRoots D i j, ∀ β ∈ pairRoots D i j,
      ¬ Universal.IsNegMultiple α β →
      ExtendsToHom D.rootGroup (D.cone α β ∩ pairRoots D i j) ψ)
    (hrank : ∀ k, ExtendsToHom D.rootGroup {Pi.single k 1, -Pi.single k 1} ψ)
    (hgen : Subgroup.closure (⋃ k, Set.range (ψ (Pi.single k 1)) ∪
      Set.range (ψ (-Pi.single k 1))) = ⊤)
    (hnt : ∃ k, ∃ x, ψ (Pi.single k 1) x ≠ 1) :
    ∃ Ψ : K →* H, (∀ k (x : D.rootGroup (Pi.single k 1)), Ψ x = ψ _ x) ∧
      (∀ k (x : D.rootGroup (-Pi.single k 1)), Ψ x = ψ _ x) ∧ Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple H ∧
      Subgroup.center H = (Subgroup.center K).map Ψ ∧
      LieModel (H ⧸ Subgroup.center H) t n p f := by
  obtain ⟨φ₁, φ₂, hpc, -, hφ₁⟩ := Levi.exists_pairCompatible_of_frame hL ψ hcone hrank
  have hsingle : ∀ k, ({k} : Finset (Fin D.rank)).card ≤ 2 := fun k => by simp
  have hmem : ∀ k, ∀ x ∈ CurtisTits.rankOne D.rootGroup k, x ∈ CurtisTits.levi D.rootGroup {k} :=
    fun k x hx => by rw [CurtisTits.levi_singleton]; exact hx
  have hfam : ∀ k γ, (γ = Pi.single k 1 ∨ γ = -Pi.single k 1) → ∀ (x : D.rootGroup γ)
      (hx : (x : K) ∈ CurtisTits.rankOne D.rootGroup k),
      pairFamily φ₂ ⟨{k}, hsingle k⟩ ⟨x, hmem k x hx⟩ = ψ γ x := fun k γ hγ x hx =>
    (hpc.pairFamily_singleton k (hsingle k) x (hmem k x hx) hx).trans (hφ₁ k γ hγ x hx)
  have hgen' : ⨆ J, (pairFamily φ₂ J).range = ⊤ := by
    rw [eq_top_iff, ← Levi.iSup_range_eq_top_of_frame hφ₁ hgen]
    refine iSup_le fun k => ?_
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_iSup_of_mem (⟨{k}, hsingle k⟩ : {J : Finset (Fin D.rank) // J.card ≤ 2})
      ⟨_, hpc.pairFamily_singleton k (hsingle k) x.1 (hmem k x.1 x.2) x.2⟩
  have hnt' : ∃ J, ∃ x, pairFamily φ₂ J x ≠ 1 := by
    obtain ⟨k, x, hx⟩ := hnt
    exact ⟨⟨{k}, hsingle k⟩, _, (hfam k _ (Or.inl rfl) x
      (Levi.rootGroup_single_le_rankOne k x.2)).trans_ne hx⟩
  obtain ⟨Ψ, hΨ, hsurj, hker, hHq, hZH, -, hmodel⟩ :=
    hCT.2.2.1 H (pairFamily φ₂) hpc.isCompatible hgen' hnt'
  refine ⟨Ψ, fun k x => ?_, fun k x => ?_, hsurj, hker, hHq, hZH, hmodel⟩
  · exact (hΨ ⟨{k}, hsingle k⟩ ⟨x, hmem k x (Levi.rootGroup_single_le_rankOne k x.2)⟩).trans
      (hfam k _ (Or.inl rfl) x (Levi.rootGroup_single_le_rankOne k x.2))
  · exact (hΨ ⟨{k}, hsingle k⟩ ⟨x, hmem k x (Levi.rootGroup_neg_single_le_rankOne k x.2)⟩).trans
      (hfam k _ (Or.inr rfl) x (Levi.rootGroup_neg_single_le_rankOne k x.2))

theorem lieModel_of_frame {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    {H : Type} [Group H] (hZ : Subgroup.center H = ⊥) (ψ : ∀ γ, D.rootGroup γ → H)
    (hcone : ∀ i j, ∀ α ∈ pairRoots D i j, ∀ β ∈ pairRoots D i j,
      ¬ Universal.IsNegMultiple α β →
      ExtendsToHom D.rootGroup (D.cone α β ∩ pairRoots D i j) ψ)
    (hrank : ∀ k, ExtendsToHom D.rootGroup {Pi.single k 1, -Pi.single k 1} ψ)
    (hgen : Subgroup.closure (⋃ k, Set.range (ψ (Pi.single k 1)) ∪
      Set.range (ψ (-Pi.single k 1))) = ⊤)
    (hnt : ∃ k, ∃ x, ψ (Pi.single k 1) x ≠ 1) :
    LieModel H t n p f := by
  obtain ⟨-, -, -, -, -, -, -, hmodel⟩ :=
    exists_surjective_of_frame hCT hL ψ hcone hrank hgen hnt
  exact lieModel_of_center_eq_bot hZ hmodel

end CFSG.Timmesfeld

module

public import CFSG.Timmesfeld.ARS.CaseMFrame
public import CFSG.Timmesfeld.ARS.CaseMLieInputs
public import CFSG.Timmesfeld.ARS.CaseERoots

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.RootSystem
open CFSG.Blueprint CFSG.Timmesfeld CFSG.LieType.CurtisTits Matrix

namespace CaseM

@[expose] def edge01Roots : Set (Fin 4 → ℤ) :=
  {![1, 0, 0, 0], -![1, 0, 0, 0], ![0, 1, 0, 0], -![0, 1, 0, 0], ![1, 1, 0, 0], -![1, 1, 0, 0]}

@[expose] def edge0Roots (j : Fin 4) : Set (Fin 4 → ℤ) :=
  {![1, 0, 0, 0], -![1, 0, 0, 0], Pi.single j 1, -Pi.single j 1}

theorem mem_c3PairRoots_iff (γ : Fin 4 → ℤ) : γ ∈ c3PairRoots ↔
    γ = ![0, 1, 0, 0] ∨ γ = ![0, 0, 1, 0] ∨ γ = ![0, 0, 0, 1] ∨ γ = ![0, 1, 1, 0] ∨
      γ = ![0, 1, 2, 0] ∨ γ = ![0, 0, 1, 1] ∨ γ = -![0, 1, 0, 0] ∨ γ = -![0, 0, 1, 0] ∨
      γ = -![0, 0, 0, 1] ∨ γ = -![0, 1, 1, 0] ∨ γ = -![0, 1, 2, 0] ∨ γ = -![0, 0, 1, 1] := by
  simp only [c3PairRoots, c3PosRoots, Set.image_insert_eq, Set.image_singleton, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

abbrev f4RootDatum : UniversalRootDatum Unit where
  rank := 4
  cartan := CFSG.Blueprint.Chevalley.Tag.cartan .F4
  isFiniteType := (Adjoint.f4Datum (ZMod 2)).isFiniteType
  divisible := ∅
  rootGroup _ := ⊥

private def zA2' : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}

private def zA1A1' : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

private def zB2 : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, 2), (-1, -2)}

private theorem pairRoots_subset_of {K : Type*} [Group K] {D : UniversalRootDatum K}
    {i j : Fin D.rank} {Z : Finset (ℤ × ℤ)} {T : Set (Fin D.rank → ℤ)}
    (hsub : pairRoots D i j ⊆ pair i j '' Z)
    (hZ : ∀ z ∈ Z, z.1 • Pi.single i 1 + z.2 • Pi.single j 1 ∈ T) : pairRoots D i j ⊆ T := by
  intro γ hγ
  obtain ⟨z, hz, rfl⟩ := hsub hγ
  rw [pair_apply]
  exact hZ z hz

private theorem pairRoots_self_subset {K : Type*} [Group K] {D : UniversalRootDatum K}
    (i j : Fin D.rank) : pairRoots D i i ⊆ pairRoots D i j :=
  fun _ hγ => ⟨hγ.1, fun k hi _ => hγ.2 k hi hi⟩

theorem f4_pairRoots_subset (i j : Fin 4) :
    pairRoots f4RootDatum i j ⊆ c3PairRoots ∨
      pairRoots f4RootDatum i j ⊆ edge01Roots ∨
      pairRoots f4RootDatum i j ⊆ edge0Roots 2 ∨
      pairRoots f4RootDatum i j ⊆ edge0Roots 3 := by
  have h01 : pairRoots f4RootDatum (0 : Fin 4) (1 : Fin 4) ⊆ edge01Roots :=
    pairRoots_subset_of (LevisExtras.pairRoots_subset_pair (D := f4RootDatum) (i := 0) (j := 1) rfl
      (Z := zA2') (by decide)
      (by decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA2' → (-z.1 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (0 : Fin 4) (1 : Fin 4)) * z.2, z.2) ∈ zA2'
        decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA2' → (z.1, -z.2 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (1 : Fin 4) (0 : Fin 4)) * z.1) ∈ zA2'
        decide))
      (by
        change ∀ z : ℤ × ℤ, z ∈ zA2' →
          z.1 • (Pi.single (0 : Fin 4) (1 : ℤ)) +
            z.2 • (Pi.single (1 : Fin 4) (1 : ℤ)) ∈ edge01Roots
        simp only [edge01Roots, Set.mem_insert_iff, Set.mem_singleton_iff]
        decide)
  have h02 : pairRoots f4RootDatum (0 : Fin 4) (2 : Fin 4) ⊆ edge0Roots 2 :=
    pairRoots_subset_of (LevisExtras.pairRoots_subset_pair (D := f4RootDatum) (i := 0) (j := 2) rfl
      (Z := zA1A1') (by decide)
      (by decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' → (-z.1 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (0 : Fin 4) (2 : Fin 4)) * z.2, z.2) ∈ zA1A1'
        decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' → (z.1, -z.2 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (2 : Fin 4) (0 : Fin 4)) * z.1) ∈ zA1A1'
        decide))
      (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' →
          z.1 • (Pi.single (0 : Fin 4) (1 : ℤ)) +
            z.2 • (Pi.single (2 : Fin 4) (1 : ℤ)) ∈ edge0Roots 2
        simp only [edge0Roots, Set.mem_insert_iff, Set.mem_singleton_iff]
        decide)
  have h03 : pairRoots f4RootDatum (0 : Fin 4) (3 : Fin 4) ⊆ edge0Roots 3 :=
    pairRoots_subset_of (LevisExtras.pairRoots_subset_pair (D := f4RootDatum) (i := 0) (j := 3) rfl
      (Z := zA1A1') (by decide)
      (by decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' → (-z.1 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (0 : Fin 4) (3 : Fin 4)) * z.2, z.2) ∈ zA1A1'
        decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' → (z.1, -z.2 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (3 : Fin 4) (0 : Fin 4)) * z.1) ∈ zA1A1'
        decide))
      (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' →
          z.1 • (Pi.single (0 : Fin 4) (1 : ℤ)) +
            z.2 • (Pi.single (3 : Fin 4) (1 : ℤ)) ∈ edge0Roots 3
        simp only [edge0Roots, Set.mem_insert_iff, Set.mem_singleton_iff]
        decide)
  have h12 : pairRoots f4RootDatum (1 : Fin 4) (2 : Fin 4) ⊆ c3PairRoots :=
    pairRoots_subset_of (LevisExtras.pairRoots_subset_pair (D := f4RootDatum) (i := 1) (j := 2) rfl
      (Z := zB2) (by decide)
      (by decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zB2 → (-z.1 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (1 : Fin 4) (2 : Fin 4)) * z.2, z.2) ∈ zB2
        decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zB2 → (z.1, -z.2 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (2 : Fin 4) (1 : Fin 4)) * z.1) ∈ zB2
        decide))
      (by
        change ∀ z : ℤ × ℤ, z ∈ zB2 →
          z.1 • (Pi.single (1 : Fin 4) (1 : ℤ)) +
            z.2 • (Pi.single (2 : Fin 4) (1 : ℤ)) ∈ c3PairRoots
        simp only [mem_c3PairRoots_iff]
        decide)
  have h13 : pairRoots f4RootDatum (1 : Fin 4) (3 : Fin 4) ⊆ c3PairRoots :=
    pairRoots_subset_of (LevisExtras.pairRoots_subset_pair (D := f4RootDatum) (i := 1) (j := 3) rfl
      (Z := zA1A1') (by decide)
      (by decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' → (-z.1 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (1 : Fin 4) (3 : Fin 4)) * z.2, z.2) ∈ zA1A1'
        decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' → (z.1, -z.2 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (3 : Fin 4) (1 : Fin 4)) * z.1) ∈ zA1A1'
        decide))
      (by
        change ∀ z : ℤ × ℤ, z ∈ zA1A1' →
          z.1 • (Pi.single (1 : Fin 4) (1 : ℤ)) +
            z.2 • (Pi.single (3 : Fin 4) (1 : ℤ)) ∈ c3PairRoots
        simp only [mem_c3PairRoots_iff]
        decide)
  have h23 : pairRoots f4RootDatum (2 : Fin 4) (3 : Fin 4) ⊆ c3PairRoots :=
    pairRoots_subset_of (LevisExtras.pairRoots_subset_pair (D := f4RootDatum) (i := 2) (j := 3) rfl
      (Z := zA2') (by decide)
      (by decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA2' → (-z.1 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (2 : Fin 4) (3 : Fin 4)) * z.2, z.2) ∈ zA2'
        decide) (by
        change ∀ z : ℤ × ℤ, z ∈ zA2' → (z.1, -z.2 - (CFSG.Blueprint.Chevalley.Tag.cartan .F4 (3 : Fin 4) (2 : Fin 4)) * z.1) ∈ zA2'
        decide))
      (by
        change ∀ z : ℤ × ℤ, z ∈ zA2' →
          z.1 • (Pi.single (2 : Fin 4) (1 : ℤ)) +
            z.2 • (Pi.single (3 : Fin 4) (1 : ℤ)) ∈ c3PairRoots
        simp only [mem_c3PairRoots_iff]
        decide)
  have hc : ∀ i j : Fin 4, pairRoots f4RootDatum i j = pairRoots f4RootDatum j i :=
    fun i j => pairRoots_comm (D := f4RootDatum) i j
  have hs : ∀ i j : Fin 4, pairRoots f4RootDatum i i ⊆ pairRoots f4RootDatum i j :=
    fun i j => pairRoots_self_subset (D := f4RootDatum) i j
  fin_cases i <;> fin_cases j
  exacts [Or.inr (Or.inl ((hs 0 1).trans h01)), Or.inr (Or.inl h01), Or.inr (Or.inr (Or.inl h02)),
    Or.inr (Or.inr (Or.inr h03)), Or.inr (Or.inl (hc 1 0 ▸ h01)), Or.inl ((hs 1 2).trans h12),
    Or.inl h12, Or.inl h13, Or.inr (Or.inr (Or.inl (hc 2 0 ▸ h02))), Or.inl (hc 2 1 ▸ h12),
    Or.inl ((hs 2 3).trans h23), Or.inl h23, Or.inr (Or.inr (Or.inr (hc 3 0 ▸ h03))),
    Or.inl (hc 3 1 ▸ h13), Or.inl (hc 3 2 ▸ h23), Or.inl ((hs 3 2).trans (hc 3 2 ▸ h23))]

section Block

variable {F : Type} [Field F]

private theorem transvection_zero_one (c : F) :
    Matrix.transvection (0 : Fin 2) 1 c = !![1, c; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.transvection]

private theorem transvection_one_zero (c : F) :
    Matrix.transvection (1 : Fin 2) 0 c = !![1, 0; c, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.transvection]

theorem blockHom_tv_upper (i : Fin 2) (c : F) :
    SL.blockHom F i (tv 0 1 c) = tv i.castSucc i.succ c := by
  rw [tv_of_ne (by decide), tv_of_ne (Fin.castSucc_lt_succ (i := i)).ne]
  apply Subtype.ext
  change SL.blockMat i (Matrix.transvection 0 1 c) = Matrix.transvection _ _ c
  rw [transvection_zero_one, SL.blockMat_transvection_upper]

theorem blockHom_tv_lower (i : Fin 2) (c : F) :
    SL.blockHom F i (tv 1 0 c) = tv i.succ i.castSucc c := by
  rw [tv_of_ne (by decide), tv_of_ne (Fin.castSucc_lt_succ (i := i)).ne']
  apply Subtype.ext
  change SL.blockMat i (Matrix.transvection 1 0 c) = Matrix.transvection _ _ c
  rw [transvection_one_zero, SL.blockMat_transvection_lower]

end Block

section Maps

variable {K : Type} [Group K] {G : Type} [Group G]

theorem sl2_mem_of_tv {k : Type} [Field k] (ρ : SpecialLinearGroup (Fin 2) k →* G)
    {H : Subgroup G} (h1 : ∀ c, ρ (tv 0 1 c) ∈ H) (h2 : ∀ c, ρ (tv 1 0 c) ∈ H)
    (g : SpecialLinearGroup (Fin 2) k) : ρ g ∈ H := by
  have : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) k)) ≤ H.comap ρ := by
    rw [← closure_tv_two, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [h1 c, h2 c]
  exact this (Subgroup.mem_top g)

theorem iSup_rankOne_eq_top {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hdiv : D.divisible = ∅) :
    ⨆ k, (D.rootGroup (Pi.single k 1) ⊔ D.rootGroup (-Pi.single k 1)) = ⊤ := by
  set L := ⨆ k, (D.rootGroup (Pi.single k 1) ⊔ D.rootGroup (-Pi.single k 1)) with hL
  have hk : ∀ k, D.rootGroup (Pi.single k 1) ⊔ D.rootGroup (-Pi.single k 1) ≤ L := fun k =>
    le_iSup (fun k => D.rootGroup (Pi.single k 1) ⊔ D.rootGroup (-Pi.single k 1)) k
  have hw : ∀ w, Steinberg.nrep hct w ∈ L := fun w =>
    posLift_mem _ _ _ L (fun k => hk k (hct.n_mem k)) w
  rw [eq_top_iff, ← hct.iSup_eq_top]
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single hdiv hγ
  rw [← actsAs_nrep hct w _
    ((Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)]
  rintro _ ⟨x, hx, rfl⟩
  exact L.mul_mem (L.mul_mem (hw w) (hk i (Subgroup.mem_sup_left hx))) (L.inv_mem (hw w))

theorem isCTFrame_of_cover {D : UniversalRootDatum K} {ι : Type*}
    (S : ι → Set (Fin D.rank → ℤ)) {ψ : ∀ γ, D.rootGroup γ → G}
    (hS : ∀ t, ExtendsToHom D.rootGroup (S t) ψ) (hcover : ∀ i j, ∃ t, pairRoots D i j ⊆ S t)
    (hgen : Subgroup.closure
      (⋃ k, Set.range (ψ (Pi.single k 1)) ∪ Set.range (ψ (-Pi.single k 1))) = ⊤)
    (hnt : ∃ k, ∃ x, ψ (Pi.single k 1) x ≠ 1) : IsCTFrame D G ψ := by
  refine ⟨fun i j α _ β _ _ => ?_, fun k => ?_, hgen, hnt⟩
  · obtain ⟨t, ht⟩ := hcover i j
    exact (hS t).mono (Set.inter_subset_right.trans ht)
  · obtain ⟨t, ht⟩ := hcover k k
    have h := Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (k := k) (Or.inl rfl)
    refine (hS t).mono ?_
    rintro γ (rfl | rfl)
    · exact ht h.1
    · exact ht h.2

end Maps

section F4Maps

variable {K : Type} [Group K] {G : Type} [Group G]

theorem single_mem_c3PairRoots {j : Fin 4} (hj : j ≠ 0) :
    Pi.single j 1 ∈ c3PairRoots ∧ -Pi.single j 1 ∈ c3PairRoots := by
  rw [mem_c3PairRoots_iff, mem_c3PairRoots_iff]
  fin_cases j
  · exact absurd rfl hj
  all_goals decide

theorem apply_zero_of_mem_c3PairRoots {γ : Fin 4 → ℤ} (hγ : γ ∈ c3PairRoots) : γ 0 = 0 := by
  rw [mem_c3PairRoots_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem exists_f4Maps (X : (Fin 4 → ℤ) → Subgroup K) {k k' : Type} [Field k] [Field k']
    {HV : Subgroup K} (θV : HV →* G) (hXV : ∀ γ ∈ c3PairRoots, X γ ≤ HV)
    {l : SpecialLinearGroup (Fin 3) k →* K} (hl : Function.Injective l)
    (hl1 : (X ![1, 0, 0, 0] : Set K) = Set.range (fun c => l (tv 0 1 c)))
    (hl2 : (X (-![1, 0, 0, 0]) : Set K) = Set.range (fun c => l (tv 1 0 c)))
    (hl3 : (X ![0, 1, 0, 0] : Set K) = Set.range (fun c => l (tv 1 2 c)))
    (hl4 : (X (-![0, 1, 0, 0]) : Set K) = Set.range (fun c => l (tv 2 1 c)))
    (hl5 : (X ![1, 1, 0, 0] : Set K) = Set.range (fun c => l (tv 0 2 c)))
    (hl6 : (X (-![1, 1, 0, 0]) : Set K) = Set.range (fun c => l (tv 2 0 c)))
    (m : Fin 4 → SpecialLinearGroup (Fin 2) k × SpecialLinearGroup (Fin 2) k' →* K)
    (hm : ∀ j : Fin 4, (j = 2 ∨ j = 3) → Function.Injective (m j) ∧
      (X (Pi.single j 1) : Set K) = Set.range (fun c => m j (1, tv 0 1 c)) ∧
      (X (-Pi.single j 1) : Set K) = Set.range (fun c => m j (1, tv 1 0 c)) ∧
      ∀ c, m j (tv 0 1 c, 1) = l (tv 0 1 c) ∧ m j (tv 1 0 c, 1) = l (tv 1 0 c))
    (ψE : SpecialLinearGroup (Fin 3) k →* G)
    (hψE : ∀ c (h : l (tv 1 2 c) ∈ HV), ψE (tv 1 2 c) = θV ⟨_, h⟩)
    (hψE' : ∀ c (h : l (tv 2 1 c) ∈ HV), ψE (tv 2 1 c) = θV ⟨_, h⟩)
    (hcomm : ∀ j : Fin 4, (j = 2 ∨ j = 3) → ∀ x (hx : x ∈ HV),
      (x ∈ X (Pi.single j 1) ∨ x ∈ X (-Pi.single j 1)) →
        ∀ c, Commute (ψE (tv 0 1 c)) (θV ⟨x, hx⟩) ∧ Commute (ψE (tv 1 0 c)) (θV ⟨x, hx⟩)) :
    ∃ ψ : ∀ γ, X γ → G, ExtendsToHom X c3PairRoots ψ ∧ ExtendsToHom X edge01Roots ψ ∧
      ExtendsToHom X (edge0Roots 2) ψ ∧ ExtendsToHom X (edge0Roots 3) ψ ∧
      (∀ γ (hγ : γ ∈ c3PairRoots) (x : X γ), ψ γ x = θV ⟨x, hXV γ hγ x.2⟩) ∧
      Set.range (ψ (Pi.single 0 1)) = Set.range (fun c => ψE (tv 0 1 c)) ∧
      Set.range (ψ (-Pi.single 0 1)) = Set.range (fun c => ψE (tv 1 0 c)) := by
  classical
  have hmem : ∀ {γ : Fin 4 → ℤ} {ι' : Type} {f : ι' → K}, (X γ : Set K) = Set.range f →
      ∀ x ∈ X γ, ∃ c, f c = x := fun h x hx => by
    rw [← SetLike.mem_coe, h] at hx
    exact hx
  have hmem' : ∀ {γ : Fin 4 → ℤ} {ι' : Type} {f : ι' → K}, (X γ : Set K) = Set.range f →
      ∀ c, f c ∈ X γ :=
    fun h c => by
      rw [← SetLike.mem_coe, h]
      exact ⟨c, rfl⟩
  let θE : l.range →* G := ψE.comp (MonoidHom.ofInjective hl).symm.toMonoidHom
  have hθE : ∀ g (h : l g ∈ l.range), θE ⟨l g, h⟩ = ψE g := by
    intro g h
    change ψE ((MonoidHom.ofInjective hl).symm ⟨l g, h⟩) = ψE g
    congr 1
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (MonoidHom.ofInjective_apply hl).symm
  let ψ : ∀ γ, X γ → G := fun γ x =>
    if γ 0 = 0 then (if h : (x : K) ∈ HV then θV ⟨x, h⟩ else 1)
    else (if h : (x : K) ∈ l.range then θE ⟨x, h⟩ else 1)
  have hψV : ∀ γ, γ 0 = 0 → ∀ (x : X γ) (h : (x : K) ∈ HV), ψ γ x = θV ⟨x, h⟩ := by
    intro γ hγ x h
    simp only [ψ, hγ, h, ↓reduceIte, ↓reduceDIte]
  have hψE₀ : ∀ γ, γ 0 ≠ 0 → ∀ (x : X γ) (h : (x : K) ∈ l.range), ψ γ x = θE ⟨x, h⟩ := by
    intro γ hγ x h
    simp only [ψ, hγ, h, ↓reduceIte, ↓reduceDIte]
  have h1V : ∀ x ∈ X ![0, 1, 0, 0], x ∈ HV := fun x hx =>
    hXV _ (by rw [mem_c3PairRoots_iff]; decide) hx
  have h1V' : ∀ x ∈ X (-![0, 1, 0, 0]), x ∈ HV := fun x hx =>
    hXV _ (by rw [mem_c3PairRoots_iff]; decide) hx
  have e1 : ExtendsToHom X c3PairRoots ψ :=
    ⟨HV, θV, fun γ hγ x => ⟨hXV γ hγ x.2,
      (hψV γ (apply_zero_of_mem_c3PairRoots hγ) x _).symm⟩⟩
  have e2 : ExtendsToHom X edge01Roots ψ := by
    refine ⟨l.range, θE, fun γ hγ x => ?_⟩
    obtain ⟨x, hx⟩ := x
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨c, rfl⟩ := hmem hl1 _ hx
      exact ⟨MonoidHom.mem_range.2 ⟨_, rfl⟩, (hψE₀ _ (by decide) _ _).symm⟩
    · obtain ⟨c, rfl⟩ := hmem hl2 _ hx
      exact ⟨MonoidHom.mem_range.2 ⟨_, rfl⟩, (hψE₀ _ (by decide) _ _).symm⟩
    · obtain ⟨c, rfl⟩ := hmem hl3 _ hx
      refine ⟨MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
      rw [hψV _ (by decide) _ (h1V _ hx)]
      exact (hθE (tv 1 2 c) _).trans (hψE c _)
    · obtain ⟨c, rfl⟩ := hmem hl4 _ hx
      refine ⟨MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
      rw [hψV _ (by decide) _ (h1V' _ hx)]
      exact (hθE (tv 2 1 c) _).trans (hψE' c _)
    · obtain ⟨c, rfl⟩ := hmem hl5 _ hx
      exact ⟨MonoidHom.mem_range.2 ⟨_, rfl⟩, (hψE₀ _ (by decide) _ _).symm⟩
    · obtain ⟨c, rfl⟩ := hmem hl6 _ hx
      exact ⟨MonoidHom.mem_range.2 ⟨_, rfl⟩, (hψE₀ _ (by decide) _ _).symm⟩
  have e3 : ∀ j : Fin 4, (j = 2 ∨ j = 3) → ExtendsToHom X (edge0Roots j) ψ := by
    intro j hj
    obtain ⟨hmj, hmj1, hmj2, hmj3⟩ := hm j hj
    have hj0 : j ≠ 0 := by rcases hj with rfl | rfl <;> decide
    obtain ⟨hsj, hsj'⟩ := single_mem_c3PairRoots hj0
    have hjV : ∀ b, m j (1, b) ∈ HV := sl2_mem_of_tv ((m j).comp (MonoidHom.inr _ _))
      (fun c => hXV _ hsj (hmem' hmj1 c)) (fun c => hXV _ hsj' (hmem' hmj2 c))
    let ρj : SpecialLinearGroup (Fin 2) k' →* G :=
      θV.comp (((m j).comp (MonoidHom.inr _ _)).codRestrict HV hjV)
    have hρj : ∀ b, ρj b = θV ⟨m j (1, b), hjV b⟩ := fun b => rfl
    let ρEj : SpecialLinearGroup (Fin 2) k →* G := ψE.comp (SL.blockHom k (0 : Fin 2))
    have hρEj1 : ∀ c, ρEj (tv 0 1 c) = ψE (tv 0 1 c) := fun c => by
      change ψE (SL.blockHom k (0 : Fin 2) (tv 0 1 c)) = _
      rw [blockHom_tv_upper]
      rfl
    have hρEj2 : ∀ c, ρEj (tv 1 0 c) = ψE (tv 1 0 c) := fun c => by
      change ψE (SL.blockHom k (0 : Fin 2) (tv 1 0 c)) = _
      rw [blockHom_tv_lower]
      rfl
    have hgen : ∀ c b, Commute (ψE (tv 0 1 c)) (ρj b) ∧ Commute (ψE (tv 1 0 c)) (ρj b) := by
      intro c b
      have key := sl2_mem_of_tv ρj
        (H := Subgroup.centralizer ({ψE (tv 0 1 c), ψE (tv 1 0 c)} : Set G)) (fun d => ?_)
        (fun d => ?_) b
      · rw [Subgroup.mem_centralizer_iff] at key
        exact ⟨key _ (Set.mem_insert _ _), key _ (Set.mem_insert_of_mem _ rfl)⟩
      · rw [Subgroup.mem_centralizer_iff]
        obtain ⟨h1, h2⟩ := hcomm j hj _ (hjV _) (Or.inl (hmem' hmj1 d)) c
        rintro _ (rfl | rfl)
        exacts [h1, h2]
      · rw [Subgroup.mem_centralizer_iff]
        obtain ⟨h1, h2⟩ := hcomm j hj _ (hjV _) (Or.inr (hmem' hmj2 d)) c
        rintro _ (rfl | rfl)
        exacts [h1, h2]
    have hcommj : ∀ a b, Commute (ρEj a) (ρj b) := by
      intro a b
      have key := sl2_mem_of_tv ρEj (H := Subgroup.centralizer ({ρj b} : Set G))
        (fun c => by
          rw [Subgroup.mem_centralizer_iff, hρEj1]
          rintro _ rfl
          exact ((hgen c b).1).symm)
        (fun c => by
          rw [Subgroup.mem_centralizer_iff, hρEj2]
          rintro _ rfl
          exact ((hgen c b).2).symm) a
      rw [Subgroup.mem_centralizer_iff] at key
      exact (key _ rfl).symm
    let θ0j : (m j).range →* G :=
      (MonoidHom.noncommCoprod ρEj ρj hcommj).comp (MonoidHom.ofInjective hmj).symm.toMonoidHom
    have hθ0j : ∀ p (x : K) (hxp : m j p = x) (h : x ∈ (m j).range),
        θ0j ⟨x, h⟩ = ρEj p.1 * ρj p.2 := by
      rintro p _ rfl h
      change MonoidHom.noncommCoprod ρEj ρj hcommj ((MonoidHom.ofInjective hmj).symm ⟨m j p, h⟩) =
        _
      rw [show (MonoidHom.ofInjective hmj).symm ⟨m j p, h⟩ = p by
        rw [MulEquiv.symm_apply_eq]
        exact Subtype.ext (MonoidHom.ofInjective_apply hmj).symm]
      rfl
    refine ⟨(m j).range, θ0j, fun γ hγ x => ?_⟩
    obtain ⟨x, hx⟩ := x
    rcases hγ with rfl | rfl | rfl | rfl
    · obtain ⟨c, rfl⟩ := hmem hl1 _ hx
      refine ⟨MonoidHom.mem_range.2 ⟨_, (hmj3 c).1⟩, (hθ0j _ _ (hmj3 c).1 _).trans ?_⟩
      rw [map_one, mul_one, hρEj1, hψE₀ _ (by decide) _ ⟨_, rfl⟩]
      exact (hθE _ _).symm
    · obtain ⟨c, rfl⟩ := hmem hl2 _ hx
      refine ⟨MonoidHom.mem_range.2 ⟨_, (hmj3 c).2⟩, (hθ0j _ _ (hmj3 c).2 _).trans ?_⟩
      rw [map_one, mul_one, hρEj2, hψE₀ _ (by decide) _ ⟨_, rfl⟩]
      exact (hθE _ _).symm
    · obtain ⟨c, rfl⟩ := hmem hmj1 _ hx
      refine ⟨MonoidHom.mem_range.2 ⟨_, rfl⟩, (hθ0j _ _ rfl _).trans ?_⟩
      rw [map_one, one_mul, hρj, hψV _ (Pi.single_eq_of_ne (Ne.symm hj0) _) _ (hjV _)]
    · obtain ⟨c, rfl⟩ := hmem hmj2 _ hx
      refine ⟨MonoidHom.mem_range.2 ⟨_, rfl⟩, (hθ0j _ _ rfl _).trans ?_⟩
      rw [map_one, one_mul, hρj, hψV _ (by rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hj0),
        neg_zero]) _ (hjV _)]
  have r1 : Set.range (ψ (Pi.single 0 1)) = Set.range (fun c => ψE (tv 0 1 c)) := by
    have e : (Pi.single 0 1 : Fin 4 → ℤ) = ![1, 0, 0, 0] := by decide
    rw [e]
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨c, rfl⟩ := hmem hl1 _ hx
      exact ⟨c, by rw [hψE₀ _ (by decide) _ ⟨_, rfl⟩]; exact (hθE _ _).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨⟨_, hmem' hl1 c⟩, by rw [hψE₀ _ (by decide) _ ⟨_, rfl⟩]; exact hθE _ _⟩
  have r2 : Set.range (ψ (-Pi.single 0 1)) = Set.range (fun c => ψE (tv 1 0 c)) := by
    have e : (-Pi.single 0 1 : Fin 4 → ℤ) = -![1, 0, 0, 0] := by decide
    rw [e]
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨c, rfl⟩ := hmem hl2 _ hx
      exact ⟨c, by rw [hψE₀ _ (by decide) _ ⟨_, rfl⟩]; exact (hθE _ _).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨⟨_, hmem' hl2 c⟩, by rw [hψE₀ _ (by decide) _ ⟨_, rfl⟩]; exact hθE _ _⟩
  exact ⟨ψ, e1, e2, e3 2 (Or.inl rfl), e3 3 (Or.inr rfl),
    fun γ hγ x => hψV γ (apply_zero_of_mem_c3PairRoots hγ) x _, r1, r2⟩

end F4Maps

end CaseM

end CFSG.Timmesfeld.ARS

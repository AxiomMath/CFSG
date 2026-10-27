module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitTorus
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccursDict

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.QTwoCav CFSG.StandardType.TableCRes CFSG.LieType.Steinberg.Adjoint

noncomputable section

private def e6SplitOrbitVec (i : ExcRaw.Root 1) : Fin 4 → (Fin Tag.E6.rank → ℤ) :=
  ![e6SplitRoot i, -e6SplitRoot i,
    permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i),
    -permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)]

private theorem mem_e6SplitCodeRoots_singleton_iff {i : ExcRaw.Root 1}
    {δ : Fin Tag.E6.rank → ℤ} :
    δ ∈ e6SplitCodeRoots {i} ↔ ∃ a : Fin 4, e6SplitOrbitVec i a = δ := by
  constructor
  · rintro ⟨k, hk, h⟩
    rw [Finset.mem_singleton] at hk
    subst hk
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨a, rfl⟩
    fin_cases a
    · exact ⟨i, Finset.mem_singleton_self i, Or.inl rfl⟩
    · exact ⟨i, Finset.mem_singleton_self i, Or.inr (Or.inl rfl)⟩
    · exact ⟨i, Finset.mem_singleton_self i, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨i, Finset.mem_singleton_self i, Or.inr (Or.inr (Or.inr rfl))⟩

private theorem e6SplitPerm_invol (v : Fin Tag.E6.rank → ℤ) :
    permLattice (τ := .E6) TwistTag.E6.perm (permLattice (τ := .E6) TwistTag.E6.perm v) = v := by
  have hπ : TwistTag.E6.perm.symm = TwistTag.E6.perm := by decide
  nth_rewrite 1 [← hπ]
  exact permLattice_symm_permLattice (τ := .E6) TwistTag.E6.perm v

private theorem e6SplitOrbitVec_cases :
    ∀ (i : ExcRaw.Root 1) (a b : Fin 4),
      e6SplitOrbitVec i b = e6SplitOrbitVec i a ∨
        e6SplitOrbitVec i b = -e6SplitOrbitVec i a ∨
        e6SplitOrbitVec i b =
          permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec i a) ∨
        e6SplitOrbitVec i b =
          -permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec i a) := by
  decide +kernel

private theorem e6SplitOrbitVec_neg_index :
    ∀ (i : ExcRaw.Root 1) (a : Fin 4),
      ∃ b : Fin 4, e6SplitOrbitVec i b = -e6SplitOrbitVec i a := by
  decide +kernel

private theorem e6SplitOrbitVec_perm_index :
    ∀ (i : ExcRaw.Root 1) (a : Fin 4),
      ∃ b : Fin 4,
        e6SplitOrbitVec i b =
          permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec i a) := by
  decide +kernel

private theorem e6SplitOrbitVec_iform_perm :
    ∀ (i j : ExcRaw.Root 1) (a b : Fin 4),
      iform (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec i a))
        (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec j b)) =
      iform (e6SplitOrbitVec i a) (e6SplitOrbitVec j b) := by
  decide +kernel

private theorem e6Split_adj_iform :
    ∀ (i j : ExcRaw.Root 1),
      (ExcRaw.pairing 1 i j ≠ 0 ∨ ExcRaw.pairing 1 j i ≠ 0) →
      ∃ a b : Fin 4, iform (e6SplitOrbitVec i a) (e6SplitOrbitVec j b) ≠ 0 := by
  decide +kernel

private theorem e6Split_iform_adj_or :
    ∀ (i j : ExcRaw.Root 1),
      (∃ a b : Fin 4, iform (e6SplitOrbitVec i a) (e6SplitOrbitVec j b) ≠ 0) →
      (ExcRaw.pairing 1 i j ≠ 0 ∨ ExcRaw.pairing 1 j i ≠ 0) ∨
        ∃ k : ExcRaw.Root 1,
          (ExcRaw.pairing 1 i k ≠ 0 ∨ ExcRaw.pairing 1 k i ≠ 0) ∧
          (ExcRaw.pairing 1 k j ≠ 0 ∨ ExcRaw.pairing 1 j k ≠ 0) ∧
          ∀ v : ExcRaw.V 1, ExcRaw.root 1 i v = 0 → ExcRaw.root 1 j v = 0 →
            ExcRaw.root 1 k v = 0 := by
  decide +kernel


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}
  {T₀ : Subgroup (ModGL .E6 L)}

private theorem rootChar_e6SplitOrbit_eq_one_iff (hS : E6SplitLangTwo S)
    {b : Fin Tag.E6.rank → Lˣ} (hb : rootDiagUnit .E6 b ∈ fullThreeTorus S)
    (i : ExcRaw.Root 1) (a : Fin 4) :
    rootChar b (e6SplitOrbitVec i a) = 1 ↔ rootChar b (e6SplitRoot i) = 1 := by
  have hσ : rootChar b (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) =
      rootChar b (e6SplitRoot i) :=
    rootChar_permLattice_of_mem_fullThreeTorus hS hb (e6SplitRoot i)
  have hneg : ∀ v : Fin Tag.E6.rank → ℤ, rootChar b (-v) = (rootChar b v)⁻¹ := by
    intro v
    rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]
  fin_cases a
  · rfl
  · change rootChar b (-e6SplitRoot i) = 1 ↔ rootChar b (e6SplitRoot i) = 1
    rw [hneg, inv_eq_one]
  · change rootChar b (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) = 1 ↔
      rootChar b (e6SplitRoot i) = 1
    rw [hσ]
  · change rootChar b (-permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) = 1 ↔
      rootChar b (e6SplitRoot i) = 1
    rw [hneg, hσ, inv_eq_one]

theorem E6SplitDatum.rootChar_family_eq_one_iff (d : E6SplitDatum S T₀)
    {A : Subgroup (ModGL .E6 L)} (hA : A ≤ T₀) {a : ↥A → Fin Tag.E6.rank → Lˣ}
    (ha : ∀ u, rootDiagUnit .E6 (a u) = u) (i : ExcRaw.Root 1) :
    (∀ u, rootChar (a u) (e6SplitRoot i) = 1) ↔
      ExcRaw.Vanish 1 (ggLinImage (p := 3) d.coord A) i := by
  have hord : orderOf d.ζ = 3 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf d.ζ)
      (orderOf_dvd_of_pow_eq_one d.ζ_pow_three) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) d.ζ_ne_one
    · exact h
  have hζ : ∀ k : ZMod 3, d.ζ ^ k.val = 1 ↔ k = 0 := by
    intro k
    rw [← orderOf_dvd_iff_pow_eq_one, hord, ← ZMod.val_eq_zero]
    exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt k), fun h => by
      rw [h]
      exact dvd_zero 3⟩
  constructor
  · intro h v hv
    let t : ↥T₀ := Additive.toMul (d.coord.symm v)
    have hvA : (t : ModGL .E6 L) ∈ A := (mem_ggLinImage d.coord A v).1 hv
    let u : ↥A := ⟨t, hvA⟩
    have htu : (t : ModGL .E6 L) = rootDiagUnit .E6 (a u) := (ha u).symm
    have htv : d.coord (Additive.ofMul t) = v := by simp [t]
    have h1 := d.rootChar_eq t (a u) htu i
    have h2 : d.ζ ^ (ExcRaw.root 1 i v).val = 1 := by
      rw [← htv, ← h1]
      exact h u
    exact (hζ (ExcRaw.root 1 i v)).1 h2
  · intro h u
    let t : ↥T₀ := ⟨u, hA u.2⟩
    have htu : (t : ModGL .E6 L) = rootDiagUnit .E6 (a u) := (ha u).symm
    have hmem : d.coord (Additive.ofMul t) ∈ ggLinImage (p := 3) d.coord A :=
      (ofMul_mem_ggLinImage (p := 3) d.coord A t).2 (by
        show (t : ModGL .E6 L) ∈ A
        exact u.2)
    rw [d.rootChar_eq t (a u) htu i, h (d.coord (Additive.ofMul t)) hmem]
    exact (hζ 0).2 rfl

theorem E6SplitDatum.mem_kernelRoots_family_iff (hS : E6SplitLangTwo S) (d : E6SplitDatum S T₀)
    {A : Subgroup (ModGL .E6 L)} (hA : A ≤ T₀) {a : ↥A → Fin Tag.E6.rank → Lˣ}
    (ha : ∀ u, rootDiagUnit .E6 (a u) = u) {δ : Fin Tag.E6.rank → ℤ} :
    δ ∈ kernelRoots (famCharHom a) ↔
      ∃ i, δ ∈ e6SplitCodeRoots {i} ∧ ExcRaw.Vanish 1 (ggLinImage (p := 3) d.coord A) i := by
  constructor
  · intro hδ
    obtain ⟨hroot, -⟩ := (mem_kernelRoots_famChar a).1 hδ
    obtain ⟨i, hi⟩ := exists_mem_e6SplitCodeRoots_singleton hroot
    refine ⟨i, hi, (E6SplitDatum.rootChar_family_eq_one_iff d hA ha i).1 ?_⟩
    intro u
    have hb : rootDiagUnit .E6 (a u) ∈ fullThreeTorus S := by
      rw [ha u]
      exact d.le_fullThreeTorus (hA u.2)
    have hδu : rootChar (a u) δ = 1 := congrFun hδ.2 u
    obtain ⟨a', rfl⟩ :=
      (mem_e6SplitCodeRoots_singleton_iff (i := i) (δ := δ)).1 hi
    exact (rootChar_e6SplitOrbit_eq_one_iff hS hb i a').1 hδu
  · rintro ⟨i, hi, hV⟩
    refine (mem_kernelRoots_famChar a).2 ⟨?_, ?_⟩
    · exact isRoot_of_mem_e6SplitCodeRoots hi
    · intro u
      have hb : rootDiagUnit .E6 (a u) ∈ fullThreeTorus S := by
        rw [ha u]
        exact d.le_fullThreeTorus (hA u.2)
      obtain ⟨a', rfl⟩ :=
        (mem_e6SplitCodeRoots_singleton_iff (i := i) (δ := δ)).1 hi
      exact (rootChar_e6SplitOrbit_eq_one_iff hS hb i a').2
        ((E6SplitDatum.rootChar_family_eq_one_iff d hA ha i).2 hV u)

theorem E6SplitDatum.exists_occurs_of_kernelComponent (hS : E6SplitLangTwo S)
    (d : E6SplitDatum S T₀) {A : Subgroup (ModGL .E6 L)} (hA : A ≤ T₀)
    {a : ↥A → Fin Tag.E6.rank → Lˣ} (ha : ∀ u, rootDiagUnit .E6 (a u) = u)
    (j : KernelComponent (famCharHom a)) :
    ∃ c : Finset (ExcRaw.Root 1), ExcRaw.occurs 1 (ggLinImage (p := 3) d.coord A) c ∧
      TableCRes.rationalRootsM S.ρ (famCharHom a) j = e6SplitCodeRoots c := by
  classical
  let χ := famCharHom a
  let U : Submodule (ZMod 3) (ExcRaw.V 1) := ggLinImage (p := 3) d.coord A
  let C : Set (Fin Tag.E6.rank → ℤ) := componentRoots χ j
  let D : Set (Fin Tag.E6.rank → ℤ) :=
    (fun v => permLattice (τ := .E6) TwistTag.E6.perm v) '' C
  let c : Finset (ExcRaw.Root 1) :=
    Finset.univ.filter (fun i => ∃ t : Fin 4, e6SplitOrbitVec i t ∈ C)
  have hmem : ∀ i : ExcRaw.Root 1, i ∈ c ↔ ∃ t : Fin 4, e6SplitOrbitVec i t ∈ C := by
    intro i
    simp [c]
  have hkerC : ∀ {x : Fin Tag.E6.rank → ℤ}, x ∈ C → x ∈ kernelRoots χ :=
    fun hx => hx.1
  have hrootC : ∀ {x : Fin Tag.E6.rank → ℤ}, x ∈ C → IsRoot .E6 x := by
    rintro x hx
    exact (isRootComponent_componentRoots (χ := χ) j).isRoot x hx
  have hnegC : ∀ {x : Fin Tag.E6.rank → ℤ}, x ∈ C → -x ∈ C := by
    rintro x hx
    exact (isRootComponent_componentRoots (χ := χ) j).neg_mem x hx
  have hσneg : ∀ v : Fin Tag.E6.rank → ℤ,
      permLattice (τ := .E6) TwistTag.E6.perm (-v) =
        -permLattice (τ := .E6) TwistTag.E6.perm v := fun _ => rfl
  have hnegD : ∀ {x : Fin Tag.E6.rank → ℤ}, x ∈ D → -x ∈ D := by
    rintro x ⟨y, hyC, rfl⟩
    exact ⟨-y, hnegC hyC, (hσneg y).symm⟩
  have hrootD : ∀ {x : Fin Tag.E6.rank → ℤ}, x ∈ D → IsRoot .E6 x := by
    rintro x ⟨y, hyC, rfl⟩
    exact (hrootC hyC).permLattice (TwistTag.cartan_perm .E6)
  have hclassC : ∀ {x y : Fin Tag.E6.rank → ℤ}, x ∈ C → y ∈ kernelRoots χ →
      iform x y ≠ 0 → y ∈ C := by
    intro x y hx hy hxy
    rcases hx with ⟨hxK, hxj⟩
    exact ⟨hy, (mk_eq_of_iform_ne_zero (α := ⟨x, hxK⟩) (β := ⟨y, hy⟩) hxy).symm.trans hxj⟩
  have hρroot : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      S.ρ γ = -permLattice (τ := .E6) TwistTag.E6.perm γ :=
    fun γ hγ => hS.2.2 γ hγ
  have hρ_mem : ∀ {x : Fin Tag.E6.rank → ℤ}, x ∈ C ∪ D → S.ρ x ∈ C ∪ D := by
    intro x hx
    rcases hx with hxC | hxD
    · have hxroot := hrootC hxC
      rw [hρroot x hxroot]
      exact Or.inr ⟨-x, hnegC hxC, (hσneg x).symm⟩
    · obtain ⟨y, hyC, rfl⟩ := hxD
      have hxroot : IsRoot .E6 (permLattice (τ := .E6) TwistTag.E6.perm y) :=
        hrootD ⟨y, hyC, rfl⟩
      rw [hρroot _ hxroot, e6SplitPerm_invol y]
      exact Or.inl (hnegC hyC)
  have hrat : TableCRes.rationalRootsM S.ρ χ j = C ∪ D := by
    ext x
    constructor
    · rintro ⟨k, δ, hδC, rfl⟩
      have hstep : ∀ (k : ℕ) (δ : Fin Tag.E6.rank → ℤ), δ ∈ C →
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k]) δ ∈ C ∪ D := by
        intro k
        induction k with
        | zero => intro δ hδ; simpa using Or.inl hδ
        | succ k ih =>
            intro δ hδ
            rw [Function.iterate_succ_apply']
            exact hρ_mem (ih δ hδ)
      exact hstep k δ hδC
    · intro hx
      rcases hx with hxC | hxD
      · exact ⟨0, x, hxC, by simp⟩
      · obtain ⟨y, hyC, rfl⟩ := hxD
        refine ⟨1, -y, hnegC hyC, ?_⟩
        have hyroot := hrootC hyC
        rw [Function.iterate_one, hρroot (-y) (IsRoot.neg hyroot)]
        rw [hσneg y]
        simp
  have hCD : C ∪ D = e6SplitCodeRoots c := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro x (hxC | hxD)
      · obtain ⟨i, hiR⟩ := exists_mem_e6SplitCodeRoots_singleton (hrootC hxC)
        have hic : i ∈ c := by
          obtain ⟨t, ht⟩ :=
            (mem_e6SplitCodeRoots_singleton_iff (i := i) (δ := x)).1 hiR
          exact (hmem i).2 ⟨t, by rw [ht]; exact hxC⟩
        exact (mem_e6SplitCodeRoots_iff hiR).2 hic
      · obtain ⟨y, hyC, rfl⟩ := hxD
        obtain ⟨i, hiR⟩ := exists_mem_e6SplitCodeRoots_singleton (hrootC hyC)
        obtain ⟨t, ht⟩ := (mem_e6SplitCodeRoots_singleton_iff (i := i) (δ := y)).1 hiR
        have hic : i ∈ c := (hmem i).2 ⟨t, by rw [ht]; exact hyC⟩
        obtain ⟨s, hs⟩ := e6SplitOrbitVec_perm_index i t
        have hσR : permLattice (τ := .E6) TwistTag.E6.perm y ∈
            e6SplitCodeRoots {i} := by
          rw [mem_e6SplitCodeRoots_singleton_iff]
          exact ⟨s, by rw [hs, ht]⟩
        exact (mem_e6SplitCodeRoots_iff hσR).2 hic
    · intro x hx
      rcases hx with ⟨i, hi, hxi⟩
      obtain ⟨t, htC⟩ := (hmem i).1 hi
      have hxiR : x ∈ e6SplitCodeRoots {i} := ⟨i, Finset.mem_singleton_self i, hxi⟩
      obtain ⟨s, hs⟩ := (mem_e6SplitCodeRoots_singleton_iff (i := i) (δ := x)).1 hxiR
      rcases e6SplitOrbitVec_cases i t s with h | h | h | h
      · exact Or.inl (by rw [← hs, h]; exact htC)
      · exact Or.inl (by rw [← hs, h]; exact hnegC htC)
      · exact Or.inr ⟨e6SplitOrbitVec i t, htC, by
          change permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec i t) = x
          rw [← h, ← hs]⟩
      · exact Or.inr ⟨-e6SplitOrbitVec i t, hnegC htC, by
          change -permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec i t) = x
          rw [← h, ← hs]⟩
  have hne : c.Nonempty := by
    obtain ⟨α, hαj⟩ := Quotient.exists_rep j
    obtain ⟨i, hiR⟩ := exists_mem_e6SplitCodeRoots_singleton α.2.1
    obtain ⟨t, ht⟩ := (mem_e6SplitCodeRoots_singleton_iff (i := i) (δ := α.1)).1 hiR
    exact ⟨i, (hmem i).2 ⟨t, by rw [ht]; exact ⟨α.2, hαj⟩⟩⟩
  have hsub : ∀ i ∈ c, ExcRaw.Vanish 1 U i := by
    intro i hi
    obtain ⟨t, htC⟩ := (hmem i).1 hi
    have hker : e6SplitOrbitVec i t ∈ kernelRoots χ := hkerC htC
    have hR : e6SplitOrbitVec i t ∈ e6SplitCodeRoots {i} := by
      rw [mem_e6SplitCodeRoots_singleton_iff]
      exact ⟨t, rfl⟩
    obtain ⟨i', hi'R, hi'V⟩ :=
      (E6SplitDatum.mem_kernelRoots_family_iff hS d hA ha).1 hker
    have hii : i' = i := eq_of_mem_e6SplitCodeRoots_singleton hi'R hR
    rwa [hii] at hi'V
  have hclosed : ∀ i ∈ c, ∀ j' : ExcRaw.Root 1, ExcRaw.Vanish 1 U j' →
      ExcRaw.Adj 1 i j' → j' ∈ c := by
    intro i hi j' hV' hadj
    obtain ⟨t, htC⟩ := (hmem i).1 hi
    have hnon : ∃ s u : Fin 4,
        iform (e6SplitOrbitVec i s) (e6SplitOrbitVec j' u) ≠ 0 :=
      e6Split_adj_iform i j' hadj
    obtain ⟨s, u, hsu⟩ := hnon
    have hδR : e6SplitOrbitVec i s ∈ e6SplitCodeRoots {i} := by
      rw [mem_e6SplitCodeRoots_singleton_iff]
      exact ⟨s, rfl⟩
    have hεR : e6SplitOrbitVec j' u ∈ e6SplitCodeRoots {j'} := by
      rw [mem_e6SplitCodeRoots_singleton_iff]
      exact ⟨u, rfl⟩
    have hδK : e6SplitOrbitVec i s ∈ kernelRoots χ :=
      (E6SplitDatum.mem_kernelRoots_family_iff hS d hA ha).2 ⟨i, hδR, hsub i hi⟩
    have hεK : e6SplitOrbitVec j' u ∈ kernelRoots χ :=
      (E6SplitDatum.mem_kernelRoots_family_iff hS d hA ha).2 ⟨j', hεR, hV'⟩
    rcases e6SplitOrbitVec_cases i t s with h | h | h | h
    · have hδC : e6SplitOrbitVec i s ∈ C := by rw [h]; exact htC
      have hεC : e6SplitOrbitVec j' u ∈ C := hclassC hδC hεK hsu
      exact (hmem j').2 ⟨u, hεC⟩
    · have hδC : e6SplitOrbitVec i s ∈ C := by rw [h]; exact hnegC htC
      have hεC : e6SplitOrbitVec j' u ∈ C := hclassC hδC hεK hsu
      exact (hmem j').2 ⟨u, hεC⟩
    · have hδ'C : e6SplitOrbitVec i t ∈ C := htC
      have hy : e6SplitOrbitVec i s =
          permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec i t) := h
      have hσεK : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec j' u) ∈
          kernelRoots χ := by
        refine (E6SplitDatum.mem_kernelRoots_family_iff hS d hA ha).2 ⟨j', ?_, hV'⟩
        rw [mem_e6SplitCodeRoots_singleton_iff]
        obtain ⟨s', hs'⟩ := e6SplitOrbitVec_perm_index j' u
        exact ⟨s', hs'⟩
      obtain ⟨s', hs'⟩ := e6SplitOrbitVec_perm_index j' u
      have hif := e6SplitOrbitVec_iform_perm i j' t s'
      have hif' : iform (e6SplitOrbitVec i s) (e6SplitOrbitVec j' u) =
          iform (e6SplitOrbitVec i t)
            (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec j' u)) := by
        rw [← hy, hs', e6SplitPerm_invol (e6SplitOrbitVec j' u)] at hif
        exact hif
      have hσεC : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec j' u) ∈ C :=
        hclassC hδ'C hσεK (fun h0 => hsu (hif'.trans h0))
      exact (hmem j').2 ⟨s', by rw [hs']; exact hσεC⟩
    · have hδ'C : -e6SplitOrbitVec i t ∈ C := hnegC htC
      have hy : e6SplitOrbitVec i s =
          permLattice (τ := .E6) TwistTag.E6.perm (-e6SplitOrbitVec i t) := by
        rw [h, hσneg]
      have hσεK : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec j' u) ∈
          kernelRoots χ := by
        refine (E6SplitDatum.mem_kernelRoots_family_iff hS d hA ha).2 ⟨j', ?_, hV'⟩
        rw [mem_e6SplitCodeRoots_singleton_iff]
        obtain ⟨s', hs'⟩ := e6SplitOrbitVec_perm_index j' u
        exact ⟨s', hs'⟩
      obtain ⟨r, hr⟩ := e6SplitOrbitVec_neg_index i t
      obtain ⟨s', hs'⟩ := e6SplitOrbitVec_perm_index j' u
      have hif := e6SplitOrbitVec_iform_perm i j' r s'
      have hif' : iform (e6SplitOrbitVec i s) (e6SplitOrbitVec j' u) =
          iform (-e6SplitOrbitVec i t)
            (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec j' u)) := by
        rw [hr, ← hy, hs', e6SplitPerm_invol (e6SplitOrbitVec j' u)] at hif
        exact hif
      have hσεC : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitOrbitVec j' u) ∈ C :=
        hclassC hδ'C hσεK (fun h0 => hsu (hif'.trans h0))
      exact (hmem j').2 ⟨s', by rw [hs']; exact hσεC⟩
  have hmin : ∀ T ⊆ c, T.Nonempty →
      (∀ i ∈ T, ∀ j' ∈ c, ExcRaw.Adj 1 i j' → j' ∈ T) → T = c := by
    intro T hTsub hTne hTclosed
    refine Finset.Subset.antisymm hTsub ?_
    intro i' hi'
    obtain ⟨i0, hi0⟩ := hTne
    obtain ⟨t0, ht0C⟩ := (hmem i0).1 (hTsub hi0)
    obtain ⟨t', ht'C⟩ := (hmem i').1 hi'
    let x0 : Fin Tag.E6.rank → ℤ := e6SplitOrbitVec i0 t0
    let x' : Fin Tag.E6.rank → ℤ := e6SplitOrbitVec i' t'
    have hx0R : x0 ∈ e6SplitCodeRoots {i0} := by
      rw [mem_e6SplitCodeRoots_singleton_iff]
      exact ⟨t0, rfl⟩
    have hx'R : x' ∈ e6SplitCodeRoots {i'} := by
      rw [mem_e6SplitCodeRoots_singleton_iff]
      exact ⟨t', rfl⟩
    have hx0C : x0 ∈ C := ht0C
    have hx'C : x' ∈ C := ht'C
    have hx0K : x0 ∈ kernelRoots χ := hkerC hx0C
    have hx'K : x' ∈ kernelRoots χ := hkerC hx'C
    have hrel : (kernelRootSetoid χ).r ⟨x0, hx0K⟩ ⟨x', hx'K⟩ :=
      Quotient.exact (hx0C.2.trans hx'C.2.symm)
    let memT : (Fin Tag.E6.rank → ℤ) → Prop :=
      fun v => ∀ k : ExcRaw.Root 1, v ∈ e6SplitCodeRoots {k} → k ∈ T
    have hidxT : memT x0 := by
      intro k hk
      have hk0 : k = i0 := eq_of_mem_e6SplitCodeRoots_singleton hk hx0R
      rwa [hk0]
    have hstep : ∀ x y : kernelRoots χ, iform (x : Fin Tag.E6.rank → ℤ) y ≠ 0 →
        memT (x : Fin Tag.E6.rank → ℤ) → memT (y : Fin Tag.E6.rank → ℤ) := by
      intro x y hxy hxT
      obtain ⟨k₂, hk₂R⟩ := exists_mem_e6SplitCodeRoots_singleton y.2.1
      obtain ⟨k₁, hk₁R⟩ := exists_mem_e6SplitCodeRoots_singleton x.2.1
      have hk₁T : k₁ ∈ T := hxT k₁ hk₁R
      have hV₁ : ExcRaw.Vanish 1 U k₁ := hsub k₁ (hTsub hk₁T)
      have hV₂ : ExcRaw.Vanish 1 U k₂ := by
        obtain ⟨i, hiR, hiV⟩ :=
          (E6SplitDatum.mem_kernelRoots_family_iff hS d hA ha).1 y.2
        have hik : i = k₂ := eq_of_mem_e6SplitCodeRoots_singleton hiR hk₂R
        rwa [hik] at hiV
      have hnon : ∃ s u : Fin 4,
          iform (e6SplitOrbitVec k₁ s) (e6SplitOrbitVec k₂ u) ≠ 0 := by
        obtain ⟨s, hs⟩ :=
          (mem_e6SplitCodeRoots_singleton_iff (i := k₁) (δ := x.1)).1 hk₁R
        obtain ⟨u, hu⟩ :=
          (mem_e6SplitCodeRoots_singleton_iff (i := k₂) (δ := y.1)).1 hk₂R
        refine ⟨s, u, ?_⟩
        rwa [hs, hu]
      have hk₂T : k₂ ∈ T := by
        rcases e6Split_iform_adj_or k₁ k₂ hnon with hadj | ⟨k, hk1, hk2, hvan⟩
        · have hk₂c : k₂ ∈ c :=
            hclosed k₁ (hTsub hk₁T) k₂ hV₂ (show ExcRaw.Adj 1 k₁ k₂ from hadj)
          exact hTclosed k₁ hk₁T k₂ hk₂c (show ExcRaw.Adj 1 k₁ k₂ from hadj)
        · have hVk : ExcRaw.Vanish 1 U k := fun v hv => hvan v (hV₁ v hv) (hV₂ v hv)
          have hk1' : ExcRaw.Adj 1 k₁ k := hk1
          have hk2' : ExcRaw.Adj 1 k k₂ := hk2
          have hkc : k ∈ c := hclosed k₁ (hTsub hk₁T) k hVk hk1'
          have hkT : k ∈ T := hTclosed k₁ hk₁T k hkc hk1'
          have hk₂c : k₂ ∈ c := hclosed k hkc k₂ hV₂ hk2'
          exact hTclosed k hkT k₂ hk₂c hk2'
      intro k hk
      rwa [eq_of_mem_e6SplitCodeRoots_singleton hk hk₂R]
    have key : ∀ x y : kernelRoots χ, (kernelRootSetoid χ).r x y →
        (memT (x : Fin Tag.E6.rank → ℤ) ↔ memT (y : Fin Tag.E6.rank → ℤ)) := by
      intro x y hxy
      induction hxy with
      | rel x y hrel =>
          rw [dotProduct_mulVec_eq_iform] at hrel
          exact ⟨hstep x y hrel, fun hy => hstep y x (by rwa [iform_comm]) hy⟩
      | refl x => exact Iff.rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have hx'T : memT x' := (key ⟨x0, hx0K⟩ ⟨x', hx'K⟩ hrel).1 hidxT
    exact hx'T i' hx'R
  have hocc : ExcRaw.occurs 1 U c := ⟨hne, hsub, hclosed, hmin⟩
  exact ⟨c, hocc, hrat.trans hCD⟩

theorem E6SplitDatum.exists_kernelComponent_of_occurs (hS : E6SplitLangTwo S)
    (d : E6SplitDatum S T₀) {A : Subgroup (ModGL .E6 L)} (hA : A ≤ T₀)
    {a : ↥A → Fin Tag.E6.rank → Lˣ} (ha : ∀ u, rootDiagUnit .E6 (a u) = u)
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 (ggLinImage (p := 3) d.coord A) c) :
    ∃ j : KernelComponent (famCharHom a),
      TableCRes.rationalRootsM S.ρ (famCharHom a) j = e6SplitCodeRoots c := by
  classical
  let χ := famCharHom a
  let U : Submodule (ZMod 3) (ExcRaw.V 1) := ggLinImage (p := 3) d.coord A
  obtain ⟨i, hi⟩ := hc.1
  have hV : ExcRaw.Vanish 1 U i := hc.2.1 i hi
  have hiR : e6SplitRoot i ∈ e6SplitCodeRoots {i} :=
    ⟨i, Finset.mem_singleton_self i, Or.inl rfl⟩
  have hiK : e6SplitRoot i ∈ kernelRoots χ :=
    (E6SplitDatum.mem_kernelRoots_family_iff hS d hA ha).2 ⟨i, hiR, hV⟩
  let j : KernelComponent χ := ⟦⟨e6SplitRoot i, hiK⟩⟧
  obtain ⟨c', hocc', hrat'⟩ :=
    E6SplitDatum.exists_occurs_of_kernelComponent hS d hA ha j
  have hiC : e6SplitRoot i ∈ e6SplitCodeRoots c := by
    rw [mem_e6SplitCodeRoots_iff hiR]
    exact hi
  have hiComp : e6SplitRoot i ∈ componentRoots χ j := ⟨hiK, rfl⟩
  have hiRat : e6SplitRoot i ∈ TableCRes.rationalRootsM S.ρ χ j :=
    ⟨0, e6SplitRoot i, hiComp, by simp⟩
  have hiC' : e6SplitRoot i ∈ e6SplitCodeRoots c' := by
    rwa [hrat'] at hiRat
  have hi' : i ∈ c' := (mem_e6SplitCodeRoots_iff hiR).1 hiC'
  have hcc : c = c' := ExcRaw.IsComp.eq_of_mem hc hocc' hi hi'
  refine ⟨j, ?_⟩
  rw [hcc]
  exact hrat' 

theorem rationalComponentM_eq_e6SplitComponent {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} (j : KernelComponent χ)
    {c : Finset (ExcRaw.Root 1)} (hc : TableCRes.rationalRootsM S.ρ χ j = e6SplitCodeRoots c) :
    TableCRes.rationalComponentM S.ρ S.Γ χ j = e6SplitComponent S c := by
  simp only [TableCRes.rationalComponentM, TableCRes.rationalSpanM, e6SplitComponent, hc]

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end


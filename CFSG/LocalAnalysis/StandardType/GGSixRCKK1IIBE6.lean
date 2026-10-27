module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILongRootConj
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LieType.HighestRoot.Gen
public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.HighestRoot CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley CFSG.SeitzReduction
open scoped commutatorElement

private theorem rckp6_card_rootGroup_E6
    {K : Type} [Field K] [Fintype K]
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    Nat.card ((e6Datum K).rootGroup γ) = Nat.card K := by
  have hinj : Function.Injective (e6Data_valid.xHom K γ) := by
    intro a b hab
    have h : e6Data_valid.xm K γ a.toAdd = e6Data_valid.xm K γ b.toAdd := hab
    exact Multiplicative.ext (e6Data_valid.xm_injective K hγ h)
  change Nat.card (e6Data_valid.rootGroup K γ) = Nat.card K
  change Nat.card ((e6Data_valid.rootGroup K γ) : Set (e6Data_valid.minGroup K)) = Nat.card K
  rw [Nat.card_coe_set_eq]
  change (Set.range (e6Data_valid.xHom K γ)).ncard = Nat.card K
  rw [Set.ncard_range_of_injective hinj]
  exact (Nat.card_congr (Multiplicative.ofAdd)).symm

private theorem rckp6_mul_mem_four {G : Type*} [Group G] {x y : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) :
    ∀ {a b : G}, a ∈ ({1, x, y, x * y} : Set G) → b ∈ ({1, x, y, x * y} : Set G) →
      a * b ∈ ({1, x, y, x * y} : Set G) := by
  have hxy' : y * x = x * y := hxy.symm
  have hxxy : x * (x * y) = y := by rw [← mul_assoc, hx2, one_mul]
  have hxyx : (x * y) * x = y := by rw [mul_assoc, hxy', ← mul_assoc, hx2, one_mul]
  have hyxy : y * (x * y) = x := by rw [← mul_assoc, hxy', mul_assoc, hy2, mul_one]
  have hxyy : (x * y) * y = x := by rw [mul_assoc, hy2, mul_one]
  have hxyxy : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy']
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  intro a b ha hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, hx2, hy2, hxy', hxxy, hxyx, hyxy, hxyy, hxyxy,
      Set.mem_insert_iff, Set.mem_singleton_iff] <;>
    tauto

private theorem rckp6_inv_mem_four {G : Type*} [Group G] {x y : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) :
    ∀ {a : G}, a ∈ ({1, x, y, x * y} : Set G) → a⁻¹ ∈ ({1, x, y, x * y} : Set G) := by
  have hxyxy : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy.symm]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl | rfl | rfl | rfl
  · simp
  · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hx2))
  · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hy2)))
  · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right hxyxy)))

private theorem rckp6_closure_pair_eq {G : Type*} [Group G] {x y : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) :
    (Subgroup.closure ({x, y} : Set G) : Set G) = {1, x, y, x * y} := by
  let T : Subgroup G :=
    { carrier := {1, x, y, x * y}
      mul_mem' := rckp6_mul_mem_four hx2 hy2 hxy
      one_mem' := by simp
      inv_mem' := rckp6_inv_mem_four hx2 hy2 hxy }
  have hxT : x ∈ T := by simp [T]
  have hyT : y ∈ T := by simp [T]
  have hVT : Subgroup.closure ({x, y} : Set G) = T := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact hxT
      · exact hyT
    · intro z hz
      have hz' : z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by simpa [T] using hz
      rcases hz' with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  rw [hVT]
  rfl

private theorem rckp6_mem_closure_iff {G : Type*} [Group G] {x y z : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) :
    z ∈ ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) ↔
      z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
  rw [rckp6_closure_pair_eq hx2 hy2 hxy]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

private theorem rckp6_mem_closure_iff' {G : Type*} [Group G] {x y z : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) :
    z ∈ Subgroup.closure ({x, y} : Set G) ↔ z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
  change z ∈ ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) ↔ _
  exact rckp6_mem_closure_iff hx2 hy2 hxy

private theorem rckp6_mul_self_mem_closure {G : Type*} [Group G] {x y : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) :
    ∀ {z : G}, z ∈ Subgroup.closure ({x, y} : Set G) → z * z = 1 := by
  intro z hz
  rw [rckp6_mem_closure_iff' hx2 hy2 hxy] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [one_mul]
  · exact hx2
  · exact hy2
  · calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy.symm]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]

private theorem rckp6_comm_mem_closure {G : Type*} [Group G] {x y a b : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (ha : a ∈ Subgroup.closure ({x, y} : Set G)) (hb : b ∈ Subgroup.closure ({x, y} : Set G)) :
    a * b = b * a := by
  have hxy' : y * x = x * y := hxy.symm
  have hxxy : x * (x * y) = y := by rw [← mul_assoc, hx2, one_mul]
  have hxyx : (x * y) * x = y := by rw [mul_assoc, hxy', ← mul_assoc, hx2, one_mul]
  have hyxy : y * (x * y) = x := by rw [← mul_assoc, hxy', mul_assoc, hy2, mul_one]
  have hxyy : (x * y) * y = x := by rw [mul_assoc, hy2, mul_one]
  have hxyxy : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy']
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  rw [rckp6_mem_closure_iff' hx2 hy2 hxy] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, hxy', hxxy, hxyx, hyxy, hxyy, hxyxy]

private theorem rckp6_card_closure_pair {G : Type*} [Group G] {x y : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxyne : x ≠ y)
    (hxy : x * y = y * x) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 4 := by
  classical
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hxyne
    have h1 : y = x⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
    rw [h1, inv_eq_of_mul_eq_one_right hx2]
  have hxyx1 : x * y ≠ x := by
    intro h
    apply hy1
    have := congrArg (fun w => x⁻¹ * w) h
    simpa only [mul_one, ← mul_assoc, hx2, inv_mul_cancel, one_mul] using this
  have hxyy1 : x * y ≠ y := by
    intro h
    apply hx1
    have := congrArg (fun w => w * y⁻¹) h
    simpa only [mul_one, mul_assoc, hy2, mul_inv_cancel, mul_one] using this
  let s : Finset G := {1, x, y, x * y}
  have H : ∀ z, z ∈ s ↔ z ∈ (Subgroup.closure ({x, y} : Set G) : Set G) := by
    intro z
    rw [rckp6_mem_closure_iff hx2 hy2 hxy]
    simp only [s, Finset.mem_insert, Finset.mem_singleton]
  letI : Fintype ↑(Subgroup.closure ({x, y} : Set G) : Set G) := Fintype.ofFinset s H
  rw [show Nat.card (Subgroup.closure ({x, y} : Set G)) =
      Nat.card ↑(Subgroup.closure ({x, y} : Set G) : Set G) from rfl]
  rw [Nat.card_eq_fintype_card, Fintype.card_ofFinset s H]
  have h1mem : 1 ∉ insert x (insert y ({x * y} : Finset G)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact hx1 h.symm
    · exact hy1 h.symm
    · exact hxy1 h.symm
  have hxmem : x ∉ insert y ({x * y} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hxyne h
    · exact hxyx1 h.symm
  have hymem : y ∉ ({x * y} : Finset G) := by
    simp only [Finset.mem_singleton]
    exact fun h => hxyy1 h.symm
  rw [show s = insert 1 (insert x (insert y ({x * y} : Finset G))) from rfl,
    Finset.card_insert_of_notMem h1mem, Finset.card_insert_of_notMem hxmem,
    Finset.card_insert_of_notMem hymem, Finset.card_singleton]

theorem rckIIPair_E6
    (n : ℕ) (hadm : StatedLieAdmissible .E6 n 2 1) : RCKIIPair .E6 n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Type := GaloisField 2 1
  let i : Fin (Tag.rank .E6) := ⟨1, by decide⟩
  let θ : Fin (Tag.rank .E6) → ℤ := highRoot .E6
  let α : Fin (Tag.rank .E6) → ℤ := Pi.single i 1
  let x : (ggU .E6 n 1).K := e6Data_valid.xm K θ 1
  let y : (ggU .E6 n 1).K := e6Data_valid.xm K α 1
  let V : Subgroup (ggU .E6 n 1).K := Subgroup.closure ({x, y} : Set _)
  haveI : Finite ↥(e6Data_valid.minGroup K) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid K
  haveI : Finite (ggU .E6 n 1).K := by
    change Finite ↥(e6Data_valid.minGroup K)
    infer_instance
  haveI : Fintype K := Fintype.ofFinite K
  have hθroot : IsRoot .E6 θ := by simpa only [θ] using isRoot_highRoot .E6
  have hαroot : IsRoot .E6 α := by
    simp only [α]; exact IsRoot.basis i
  have hθmem : θ ∈ (ggU .E6 n 1).D.roots := by
    change θ ∈ (e6Datum K).roots
    rw [MinData.Valid.minDatum_roots]; exact hθroot
  have hαmem : α ∈ (ggU .E6 n 1).D.roots := by
    change α ∈ (e6Datum K).roots
    rw [MinData.Valid.minDatum_roots]; exact hαroot
  have hsym : ∀ i j, (ggU .E6 n 1).D.cartan i j = (ggU .E6 n 1).D.cartan j i :=
    cartanE_symm 6
  have hlongθ : GGLongRoot (ggU .E6 n 1).D θ :=
    ggLongRoot_of_symmetric isIrreducible_E6 hsym rfl hθmem
  have hlongα : GGLongRoot (ggU .E6 n 1).D α :=
    ggLongRoot_of_symmetric isIrreducible_E6 hsym rfl hαmem
  have hx2 : x * x = 1 := by
    show e6Data_valid.xm K θ 1 * e6Data_valid.xm K θ 1 = 1
    rw [← e6Data_valid.xm_add K θ 1 1, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero K θ]
  have hy2 : y * y = 1 := by
    show e6Data_valid.xm K α 1 * e6Data_valid.xm K α 1 = 1
    rw [← e6Data_valid.xm_add K α 1 1, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero K α]
  have hx1 : x ≠ 1 := by
    intro h
    have h' : e6Data_valid.xm K θ (1 : K) = e6Data_valid.xm K θ 0 := by
      rw [show e6Data_valid.xm K θ (1 : K) = x from rfl, h, e6Data_valid.xm_zero K θ]
      rfl
    have h10 : (1 : K) = 0 := e6Data_valid.xm_injective K hθroot h'
    exact one_ne_zero h10
  have hy1 : y ≠ 1 := by
    intro h
    have h' : e6Data_valid.xm K α (1 : K) = e6Data_valid.xm K α 0 := by
      rw [show e6Data_valid.xm K α (1 : K) = y from rfl, h, e6Data_valid.xm_zero K α]
      rfl
    have h10 : (1 : K) = 0 := e6Data_valid.xm_injective K hαroot h'
    exact one_ne_zero h10
  have hxy : x * y = y * x := by
    have hne : θ + α ≠ 0 := by
      intro h
      have h0 : (θ + α) i = 0 := by rw [h]; rfl
      have h3 : (θ + α) i = 3 := by decide +kernel
      omega
    have hnr : ¬ IsRoot .E6 (θ + α) := by
      have h := not_isRoot_nsmul_add_nsmul_highRoot (τ := .E6) (β := α)
        (by decide +kernel : 0 < height α) (a := 1) (b := 1) (le_refl 1) (le_refl 1)
      simpa only [one_smul, add_comm] using h
    have hc := (e6Data_valid.commutator_xm K hθroot hαroot hne).2 hnr 1 1
    exact commutatorElement_eq_one_iff_commute.1 hc
  have hcardθ : Nat.card ((ggU .E6 n 1).D.rootGroup θ) = 2 := by
    change Nat.card ((e6Datum K).rootGroup θ) = 2
    rw [rckp6_card_rootGroup_E6 (K := K) hθroot, GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hcardα : Nat.card ((ggU .E6 n 1).D.rootGroup α) = 2 := by
    change Nat.card ((e6Datum K).rootGroup α) = 2
    rw [rckp6_card_rootGroup_E6 (K := K) hαroot, GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hxmemθ : x ∈ (ggU .E6 n 1).D.rootGroup θ := by
    show e6Data_valid.xm K θ 1 ∈ (ggU .E6 n 1).D.rootGroup θ
    exact e6Data_valid.xm_mem_rootGroup K θ 1
  have hymemα : y ∈ (ggU .E6 n 1).D.rootGroup α := by
    show e6Data_valid.xm K α 1 ∈ (ggU .E6 n 1).D.rootGroup α
    exact e6Data_valid.xm_mem_rootGroup K α 1
  have horderx : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
  have hordery : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  have hzpowx : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [show Nat.card (Subgroup.zpowers x) = orderOf x from Nat.card_zpowers x, horderx]
  have hzpowy : Nat.card (Subgroup.zpowers y) = 2 := by
    rw [show Nat.card (Subgroup.zpowers y) = orderOf y from Nat.card_zpowers y, hordery]
  have hzθ : (ggU .E6 n 1).D.rootGroup θ = Subgroup.zpowers x := by
    change (e6Datum K).rootGroup θ = Subgroup.zpowers x
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxmemθ) ?_).symm
    rw [hzpowx]
    exact hcardθ.le
  have hzα : (ggU .E6 n 1).D.rootGroup α = Subgroup.zpowers y := by
    change (e6Datum K).rootGroup α = Subgroup.zpowers y
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hymemα) ?_).symm
    rw [hzpowy]
    exact hcardα.le
  have hHighest : IsHighestRoot (ggU .E6 n 1).D θ := by
    change IsHighestRoot (e6Datum K) θ
    have hsingle : ∀ k : Fin (Tag.rank .E6), IsLongestRoot (e6Datum K) (Pi.single k 1) :=
      fun k => isLongestRoot_single .E6 n 2 1 Nat.prime_two (by trivial) hadm k trivial
    have hlong : IsLongestRoot (e6Datum K) θ :=
      isLongestRoot_of_mem_roots_of_forall_single _ rfl hsingle hθmem
    refine ⟨hθmem, ?_, ?_, ?_⟩
    · intro δ hδ
      exact hlong.2 δ hδ
    · intro δ hδ
      have hδroot : IsRoot .E6 δ := by
        rw [MinData.Valid.minDatum_roots] at hδ; exact hδ
      simpa only [ht, height] using height_le_height_highRoot hδroot
    · exact isDominant_of_ht_le _ (fun k => by
        rw [weylAction_simple_eq]
        change ht (reflect .E6 k θ) ≤ ht θ
        simpa only [ht, height] using height_le_height_highRoot (IsRoot.reflect k hθroot))
  have hX : ∀ γ ∈ (ggU .E6 n 1).D.roots, IsPGroup 2 ((ggU .E6 n 1).D.rootGroup γ) := by
    intro γ hγ
    change γ ∈ (e6Datum K).roots at hγ
    have hγroot : IsRoot .E6 γ := by
      rw [MinData.Valid.minDatum_roots] at hγ; exact hγ
    show IsPGroup 2 (e6Data_valid.rootGroup K γ)
    exact isPGroup_two_range_of_charTwo (e6Data_valid.xHom K γ)
  have hθθ : 0 < rootForm (ggU .E6 n 1).D θ θ := by
    change 0 < rootForm (e6Datum K) θ θ
    rw [rootForm]
    exact form_pos _ (fun h =>
      ne_zero_of_mem_roots _ _ hθmem (toRat_injective (h.trans (map_zero toRat).symm)))
  have hαθ : 0 < rootForm (ggU .E6 n 1).D α θ := by
    change 0 < rootForm (e6Datum K) α θ
    rw [rootForm]
    rw [show α = Pi.single i 1 from rfl]
    rw [form_single_eq_coroot]
    have hrow : coroot (Tag.cartan .E6) i θ = 1 := by decide +kernel
    rw [hrow, Int.cast_one, mul_one]
    exact symmetrizer_pos _ i
  have hVQ : V ≤ highestRootRadical (ggU .E6 n 1).D θ := by
    rw [show V = Subgroup.closure ({x, y} : Set _) from rfl]
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact rootGroup_le_highestRootRadical hθmem hθθ hxmemθ
    · exact rootGroup_le_highestRootRadical hαmem hαθ hymemα
  have hQpc : highestRootRadical (ggU .E6 n 1).D θ ≤
      pCoreOf 2 (Subgroup.normalizer (((ggU .E6 n 1).D.rootGroup θ :
        Subgroup (ggU .E6 n 1).K) : Set (ggU .E6 n 1).K)) := by
    have hct : IsCTGroupDatum (coxeterMatrix (ggU .E6 n 1).D.isFiniteType).toCoxeterSystem
        (weylAction (ggU .E6 n 1).D.isFiniteType) (ggU .E6 n 1).D.roots
        (ggU .E6 n 1).D.rootGroup (e6Data_valid.nm K) (e6Data_valid.torus K) :=
      e6Datum_isCTGroupDatum K
    have hext : SteinbergExtras (ggU .E6 n 1).D (e6Data_valid.nm K) (e6Data_valid.torus K) :=
      e6Datum_steinbergExtras K
    refine GGRootNorm.le_pCoreOf_of_normalized ?_ ?_ ?_
    · exact highestRootRadical_le_normalizer hct hext
        (divisibleNormalizes_of_divisible_eq_empty rfl) hHighest
    · exact isPGroup_highestRootRadical hext hX hHighest.dominant
    · intro m hm t ht
      exact (Subgroup.mem_normalizer_iff.mp
        (normalizer_rootGroup_le_normalizer_highestRootRadical hct hext
          (divisibleNormalizes_of_divisible_eq_empty rfl) hHighest hm) t).mp ht
  have hVpc := hVQ.trans hQpc
  have hconj : ∀ v ∈ V, v ≠ 1 → ∃ j : (ggU .E6 n 1).K, v = j * x * j⁻¹ := by
    intro v hv hv1
    change v ∈ Subgroup.closure ({x, y} : Set _) at hv
    rw [rckp6_mem_closure_iff' hx2 hy2 hxy] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact absurd rfl hv1
    · exact ⟨1, by simp⟩
    · obtain ⟨u, hu⟩ :=
        CFSG.StandardType.RCKK1I.rckK1I_longRootConj (t := .E6) (n := n) (f := 1)
          (by simp [GGPosTag]) hadm
          hθmem hlongθ hαmem hlongα
      refine ⟨u, ?_⟩
      have hux : u * x * u⁻¹ ∈ (ggU .E6 n 1).D.rootGroup α := by
        have : u * x * u⁻¹ ∈ ((ggU .E6 n 1).D.rootGroup θ).map
            (MulAut.conj u).toMonoidHom := Subgroup.mem_map.mpr ⟨x, hxmemθ, rfl⟩
        rwa [hu] at this
      rw [hzα] at hux
      have hux1 : u * x * u⁻¹ ≠ 1 := by
        intro h
        apply hx1
        rw [show x = u⁻¹ * (u * x * u⁻¹) * u from by group, h]
        group
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hux
      have hy_pow : y ^ m = 1 ∨ y ^ m = y := by
        rw [zpow_eq_zpow_emod m (n := (2 : ℤ)) (by rwa [pow_two] : y ^ 2 = 1)]
        rcases Int.emod_two_eq_zero_or_one m with h | h <;> rw [h] <;> simp
      rcases hy_pow with h | h
      · exact absurd (hm.symm.trans h) hux1
      · rw [← hm, h]
    · let z : (ggU .E6 n 1).K := e6Data_valid.xm K (α - θ) 1
      have hαθroot : IsRoot .E6 (α - θ) := by
        have h : α - θ = -reflect .E6 i θ := by
          rw [reflect]
          have hrow : (∑ j, Tag.cartan .E6 i j * θ j) = 1 := by decide +kernel
          rw [hrow, one_smul]; abel
        rw [h]
        exact IsRoot.neg (IsRoot.reflect i hθroot)
      have hsumroot : IsRoot .E6 ((α - θ) + θ) := by
        have h : (α - θ) + θ = α := by abel
        rw [h]; exact hαroot
      have hne : (α - θ) + θ ≠ 0 := by
        have h : (α - θ) + θ = α := by abel
        rw [h]
        intro h0
        have h1 : α i = (0 : Fin (Tag.rank .E6) → ℤ) i := by rw [← h0]
        simp only [α, Pi.single_eq_same, Pi.zero_apply] at h1
        exact one_ne_zero h1
      have hc := e6Data_valid.commutator_xm_commSign K hαθroot hθroot hne hsumroot
        (1 : K) (1 : K)
      have hsum : (α - θ) + θ = α := by abel
      have hsign : ((e6Data_valid.commSign K (α - θ) θ : ℤ) : K) = (1 : K) := by
        rcases e6Data_valid.commSign_eq_one_or K (α - θ) θ with h | h
        · rw [h, Int.cast_one]
        · rw [h, Int.cast_neg, Int.cast_one]
          exact neg_eq_iff_add_eq_zero.mpr (CharTwo.add_self_eq_zero (1 : K))
      rw [hsum, hsign, mul_one, mul_one] at hc
      have hzx : z * x * z⁻¹ = x * y := by
        rw [CFSG.LieType.Steinberg.conj_eq_commutatorElement_mul,
          show ⁅z, x⁆ = e6Data_valid.xm K α 1 from hc]
        change y * x = x * y
        exact hxy.symm
      exact ⟨z, hzx.symm⟩
  have hxyne : x ≠ y := by
    intro hxy_eq
    have hsingle : ∀ k : Fin (ggU .E6 n 1).D.rank,
        IsLongestRoot (ggU .E6 n 1).D (Pi.single k 1) :=
      fun k => isLongestRoot_single .E6 n 2 1 Nat.prime_two (by trivial) hadm k trivial
    have hsinθ : IsLongestRoot (ggU .E6 n 1).D θ :=
      isLongestRoot_of_mem_roots_of_forall_single _ rfl hsingle hθmem
    have hsinα : IsLongestRoot (ggU .E6 n 1).D α :=
      isLongestRoot_of_mem_roots_of_forall_single _ rfl hsingle hαmem
    have hlen : lenSq (ggU .E6 n 1).D.isFiniteType θ =
        lenSq (ggU .E6 n 1).D.isFiniteType α :=
      IsLongest.lenSq_eq hsinθ hsinα
    obtain ⟨w, hw⟩ := exists_weylAction_eq_of_lenSq_eq (ggU .E6 n 1).D.isFiniteType
      isIrreducible_E6 hθmem hαmem hlen
    have hct : IsCTGroupDatum (coxeterMatrix (ggU .E6 n 1).D.isFiniteType).toCoxeterSystem
        (weylAction (ggU .E6 n 1).D.isFiniteType) (ggU .E6 n 1).D.roots
        (ggU .E6 n 1).D.rootGroup (e6Data_valid.nm K) (e6Data_valid.torus K) :=
      e6Datum_isCTGroupDatum K
    have hext : SteinbergExtras (ggU .E6 n 1).D (e6Data_valid.nm K) (e6Data_valid.torus K) :=
      e6Datum_steinbergExtras K
    have hXeq : (ggU .E6 n 1).D.rootGroup (weylAction (ggU .E6 n 1).D.isFiniteType w θ) =
        (ggU .E6 n 1).D.rootGroup θ := by
      rw [hw, hzα, hzθ, hxy_eq]
    have hfix : weylAction (ggU .E6 n 1).D.isFiniteType w θ = θ :=
      weylAction_eq_of_rootGroup_eq hct hext hθmem hXeq
    have hθα : θ = α := by rw [← hw, hfix]
    have h2 : θ i = 2 := by decide +kernel
    have h1 : α i = 1 := by decide +kernel
    have hcontra : θ i = α i := congrFun hθα i
    rw [h2, h1] at hcontra
    norm_num at hcontra
  refine ⟨θ, x, V, hθmem, hlongθ, hzθ, hx2, hx1, Subgroup.subset_closure (by simp), ?_,
    rckp6_card_closure_pair hx2 hy2 hx1 hy1 hxyne hxy, hVpc, hconj⟩
  change IsMulCommutative V ∧ ∀ v ∈ V, v ^ 2 = 1
  constructor
  · refine ⟨⟨?_⟩⟩
    intro a b
    apply Subtype.ext
    exact rckp6_comm_mem_closure hx2 hy2 hxy a.2 b.2
  · intro v hv
    exact rckp6_mul_self_mem_closure hx2 hy2 hxy hv

end CFSG.StandardType.RCKK1II

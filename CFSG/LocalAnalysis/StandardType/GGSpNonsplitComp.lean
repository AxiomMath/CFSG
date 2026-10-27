module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitCompBasic
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank Matrix Polynomial CFSG.RankThree.PartOne CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace SpNonsplitComp

variable {F : Type} [Field F] {n e s r p : ℕ}
  {A₀ : GL (Fin n ⊕ Fin n) F} {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r}
  {C : Matrix (Fin e) (Fin e) F}

theorem truncExp_mem_spFixedFactor (hCp : C ^ p = 1) {x y' : StatedSp n F} {k k' : Fin s → ℕ}
    (hx : RootPlaneSp.SpBlockMat A₀ ε C x k)
    (hy' : RootPlaneSp.SpBlockMat A₀ ε C y' (truncExp p k k'))
    (hmem1 : (X - 1 : F[X]) ∈ primaryFactors (spEnd x)) : y' ∈ spFixedFactor x := by
  change y' ∈ spSupported x {X - 1}
  rw [mem_spSupported]
  refine ⟨commute_of_spBlockMat hy' hx, fun h hh hne v hv => ?_⟩
  have hne' : h ≠ X - 1 := hne
  obtain ⟨a, b, hab⟩ := isCoprime_of_mem_primaryFactors hh hmem1 hne'
  rw [mul_comm b] at hab
  set w := aeval (spEnd x) b v with hw
  have hvw : v = spEnd x w - w := by
    have h1 := congrArg (fun q => aeval (spEnd x) q v) hab
    simp only [map_add, map_mul, map_one, Module.End.mul_apply, Module.End.one_apply, map_sub,
      aeval_X, LinearMap.add_apply, LinearMap.sub_apply] at h1
    rw [mem_primaryComponent.mp hv, map_zero, zero_add] at h1
    exact h1.symm
  have hid : mat n F y' * (mat n F x - 1) = mat n F x - 1 := by
    rw [mat_eq_of_spBlockMat hy', mat_eq_of_spBlockMat hx, ← map_one (frameRing A₀ ε),
      ← map_sub, ← map_mul, nsCore_truncExp_mul_sub_one hCp]
  have h2 := congrArg (fun M => M *ᵥ w) hid
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec] at h2
  rw [hvw, map_sub, spEnd_apply, spEnd_apply, spEnd_apply]
  exact h2

theorem commute_truncExp [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) (hCp : C ^ p = 1)
    (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {x y y' g : StatedSp n F}
    {k k' : Fin s → ℕ} (hx : RootPlaneSp.SpBlockMat A₀ ε C x k)
    (hy : RootPlaneSp.SpBlockMat A₀ ε C y k')
    (hy' : RootPlaneSp.SpBlockMat A₀ ε C y' (truncExp p k k')) (hgx : g * x = x * g)
    (hgy : g * y = y * g) : g * y' = y' * g := by
  apply mat_injective
  rw [map_mul, map_mul]
  have hcx : Commute (mat n F g) (mat n F x) := by
    have h1 := congrArg (mat n F) hgx
    rwa [map_mul, map_mul] at h1
  have hcy : Commute (mat n F g) (mat n F y) := by
    have h1 := congrArg (mat n F) hgy
    rwa [map_mul, map_mul] at h1
  have hy'eq : mat n F y' = mat n F y * (∑ i ∈ Finset.range p, mat n F x ^ i) + 1 -
      ∑ i ∈ Finset.range p, mat n F x ^ i := by
    rw [mat_eq_of_spBlockMat hy', mat_eq_of_spBlockMat hx, mat_eq_of_spBlockMat hy,
      nsCore_truncExp hp hp2 hCp hcunit k k', map_sub, map_add, map_mul, map_one, map_sum]
    simp only [map_pow]
  have hE : Commute (mat n F g) (∑ i ∈ Finset.range p, mat n F x ^ i) :=
    Commute.sum_right _ _ _ fun i _ => hcx.pow_right i
  rw [hy'eq]
  exact (((hcy.mul_right hE).add_right (Commute.one_right _)).sub_right hE).eq

theorem dvd_of_truncExp_eq_one (he : 1 ≤ e)
    (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {Y' : StatedSp n F}
    {k k' : Fin s → ℕ} (hY' : RootPlaneSp.SpBlockMat A₀ ε C Y' (truncExp p k k'))
    (hY'1 : Y' = 1) {i : Fin s} (hki : k i = 0) : p ∣ k' i := by
  classical
  by_contra hndvd
  have h1 : SLNS.nsCore (r := r) C (truncExp p k k') = 1 := by
    have h2 := congrArg (mat n F) hY'1
    rw [map_one, mat_eq_of_spBlockMat hY', ← map_one (frameRing A₀ ε)] at h2
    exact frameRing_injective A₀ ε h2
  have h2 : C ^ k' i = 1 := by
    ext a b
    have h3 := congrFun (congrFun h1 (Sum.inl (a, i))) (Sum.inl (b, i))
    simp only [SLNS.nsCore, fromBlocks_apply₁₁, blockDiagonal_apply_eq, truncExp, hki,
      dvd_zero, ite_true, Matrix.one_apply, Sum.inl.injEq, Prod.mk.injEq, and_true] at h3
    rw [Matrix.one_apply]
    exact h3
  have hu := hcunit (k' i) hndvd 1
  rw [h2, one_smul, sub_self] at hu
  have : Nonempty (Fin e) := ⟨⟨0, by omega⟩⟩
  exact not_isUnit_zero hu

theorem dvd_of_mem_centralizer [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hCp : C ^ p = 1) (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1))
    (hreal : ∀ k : Fin s → ℕ, ∃ X : StatedSp n F, RootPlaneSp.SpBlockMat A₀ ε C X k)
    {x : StatedSp n F} {k : Fin s → ℕ} (hx : RootPlaneSp.SpBlockMat A₀ ε C x k)
    (hk : RootPlaneSp.PlaneSupp k) (hmem1 : (X - 1 : F[X]) ∈ primaryFactors (spEnd x))
    {L : Subgroup (StatedSp n F)} (hLx : L ≤ spFixedFactor x)
    (hin : ∀ z ∈ spFixedFactor x, z ^ p = 1 → z ∈ L)
    (hZ : ∀ z ∈ L, (∀ g ∈ L, g * z = z * g) → z = 1) {y : StatedSp n F} {k' : Fin s → ℕ}
    (hy : RootPlaneSp.SpBlockMat A₀ ε C y k')
    (hyL : y ∈ Subgroup.centralizer (L : Set (StatedSp n F))) (i : Fin s) (hi : 2 ≤ (i : ℕ)) :
    p ∣ k' i := by
  obtain ⟨y', hy'⟩ := hreal (truncExp p k k')
  have hy'L : y' ∈ L :=
    hin y' (truncExp_mem_spFixedFactor hCp hx hy' hmem1) (pow_p_eq_one hCp hy')
  have hy'c : ∀ g ∈ L, g * y' = y' * g := fun g hg =>
    commute_truncExp hp hp2 hCp hcunit hx hy hy'
      (Subgroup.mem_centralizer_singleton_iff.mp (spFixedFactor_le_centralizer x (hLx hg)))
      (Subgroup.mem_centralizer_iff.mp hyL g hg)
  exact dvd_of_truncExp_eq_one he hcunit hy' (hZ y' hy'L hy'c) (hk i hi)

theorem eq_one_of_mem_of_mulEquiv {G H : Type*} [Group G] [Group H] {L : Subgroup G}
    (eL : L ≃* H) (hZ : Subgroup.center H = ⊥) {z : G} (hz : z ∈ L)
    (hc : ∀ g ∈ L, g * z = z * g) : z = 1 := by
  have hmem : (⟨z, hz⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  have h1 : eL ⟨z, hz⟩ ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := eL.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hmem g]
  rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
  exact congrArg Subtype.val h1

theorem isComponentOf_of_normalizes {G : Type*} [Group G] {L K : Subgroup G} (hLK : L ≤ K)
    (hn : ∀ m ∈ K, ∀ g ∈ L, m * g * m⁻¹ ∈ L) (hq : CFSG.IsQuasisimple L) :
    CFSG.Assembly.IsComponentOf L K := by
  refine ⟨hLK, CFSG.Assembly.IsSubnormal.step hLK ?_ (CFSG.Assembly.IsSubnormal.refl K),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).2 hq⟩
  rw [Subgroup.normal_subgroupOf_iff hLK]
  intro g m hg hm
  exact hn m hm g hg

theorem normalized_commutator {G : Type*} [Group G] {M P : Subgroup G}
    (h : ∀ m ∈ M, ∀ g ∈ P, m * g * m⁻¹ ∈ P) : ∀ m ∈ M, ∀ g ∈ ⁅P, P⁆, m * g * m⁻¹ ∈ ⁅P, P⁆ := by
  intro m hm g hg
  have hle : P.map (MulAut.conj m).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact h m hm y hy
  have h1 : (MulAut.conj m) g ∈ (⁅P, P⁆).map (MulAut.conj m).toMonoidHom := ⟨g, hg, rfl⟩
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hle hle h1

end SpNonsplitComp


open SpNonsplitComp in
theorem ggSpNonsplitCompInput_holds : GGSpNonsplitCompInput := by
  intro F _ _ _ n e s r p hp hp2 _ he hs C ε A₀ hCp hcunit hreal x k hk hx hx1
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hf1, hK⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f := by
    obtain ⟨f, -, hf⟩ := FiniteField.card F 2
    exact ⟨f, f.pos, by rw [Nat.card_eq_fintype_card, hf]⟩
  have hcardn : n + n = e * s + r := by
    have := Fintype.card_congr ε
    simpa [Fintype.card_sum, Fintype.card_prod, mul_comm] using this
  have h8 : 2 * 4 ≤ e * s := Nat.mul_le_mul he hs
  have hn : 1 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have hxp : x ^ p = 1 := pow_p_eq_one hCp hx
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hinj : Function.Injective (proj n F) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact le_antisymm
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center.trans
        AutPSp.center_eq_bot.le) bot_le
  have hxop : orderOf (proj n F x) = p := by rw [orderOf_injective _ hinj x, hxo]
  have blocks := ((symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf1 hK hp hp2
    hp2 hn _ hxop).2) x rfl hxo
  have hdim : 4 ≤ spFixedDim x := by
    unfold spFixedDim
    rw [blocks.fixed_eq]
    refine four_le_finrank_of_fix he hs hx hk fun v hv => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, spEnd_apply, sub_eq_zero]
    exact hv
  have hmem1 := X_sub_one_mem_primaryFactors x (by omega)
  have he1 : 1 ≤ e := by omega
  by_cases h42 : spFixedDim x = 4 ∧ Nat.card F = 2
  ·
    obtain ⟨hq, hodd⟩ := spFixed_four_two h42.2 blocks h42.1
    obtain ⟨⟨eA⟩, -⟩ := spFixed_four_two_alt h42.2 blocks h42.1
    refine ⟨⁅spFixedFactor x, spFixedFactor x⁆,
      isComponentOf_of_normalizes ((commutator_le_self _).trans (spFixedFactor_le_centralizer x))
        (normalized_commutator (spFixedFactor_normalized x)) hq, ?_⟩
    intro y k' hy hyL i hi
    refine dvd_of_mem_centralizer hp hp2 he1 hCp hcunit hreal hx hk hmem1 (commutator_le_self _)
      (fun z hz hzp => hodd hp hp2 z hz hzp)
      (fun z hz hc => eq_one_of_mem_of_mulEquiv eA ?_ hz hc) hy hyL i hi
    exact alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  ·
    have hlist : SpFixedListed x := ⟨by omega, fun h => by omega⟩
    have hq := spFixedFactor_isQuasisimple hK Nat.prime_two hf1 blocks hlist h42
    obtain ⟨φ, -⟩ := blocks.fixedFactor hmem1
    have hB : ((spForm n F).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
      fun v => spForm_isAlt (v : Fin n ⊕ Fin n → F)
    obtain ⟨s', hs', ⟨eS⟩⟩ :=
      exists_mulEquiv_sesqUnitaryGroup_statedSp hB blocks.fixed_nondegenerate
    have : NeZero s' := ⟨by
      have h2 : spFixedDim x = 2 * s' := hs'
      omega⟩
    refine ⟨spFixedFactor x, isComponentOf_of_normalizes (spFixedFactor_le_centralizer x)
      (spFixedFactor_normalized x) hq, ?_⟩
    intro y k' hy hyL i hi
    exact dvd_of_mem_centralizer hp hp2 he1 hCp hcunit hreal hx hk hmem1 le_rfl
      (fun z hz _ => hz)
      (fun z hz hc => eq_one_of_mem_of_mulEquiv (L := spFixedFactor x) (φ.trans eS)
        AutPSp.center_eq_bot hz hc) hy hyL i hi

theorem ggSpNonsplitPlaneInput_holds : GGSpNonsplitPlaneInput :=
  ggSpNonsplitPlaneInput_of_comp ggSpNonsplitCompInput_holds

section Inputs

theorem ggRootPlaneInputOn_PSpNonsplit_of_spFrame (hF : GGSpNonsplitFrameInput) :
    GGRootPlaneInputOn GGPSpNonsplit :=
  ggRootPlaneInputOn_PSpNonsplit_of_frame hF ggSpNonsplitPlaneInput_holds

theorem ggRootPlaneAt_PSp_of_spFrame (hF : GGSpNonsplitFrameInput) : GGRootPlaneAt .PSp :=
  ggRootPlaneAt_PSp_of_frame_plane hF ggSpNonsplitPlaneInput_holds

end Inputs

end CFSG.StandardType

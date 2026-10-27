module

public import CFSG.ClassicalInvolution.WeakCT.Symplectic

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open scoped commutatorElement MatrixGroups

section Inj

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

theorem center_sp_eq_one_of_charTwo [CharP F 2] {g : StatedSp 2 F}
    (hg : g ∈ Subgroup.center (StatedSp 2 F)) : g = 1 := by
  obtain ⟨c, hc, hmat⟩ := center_sp_scalar hg
  have h2 : ((c : F) + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, hc, one_pow, CharTwo.add_self_eq_zero]
  have h3 : (c : F) + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
  have hc1 : (c : F) = 1 := by
    rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]
  refine Subtype.ext (Units.ext ?_)
  rw [hmat, hc1]
  simp

theorem hom_injective_of_long_even [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) {G : Type*}
    [Group G] {φ : StatedSp 2 F →* G} (hl : Function.Injective (φ.comp (spBlock F 1))) :
    Function.Injective φ := by
  have hφ1 : (φ.comp (spBlock F 1)) (tv 0 1 (1 : F)) ≠ 1 :=
    fun h => tv_zero_one_one_ne_one (hl (h.trans (map_one _).symm))
  have hq : IsQuasisimple (StatedSp 2 F) :=
    Symplectic.isQuasisimple 2 F (by norm_num) (Or.inl (Or.inr hF))
  have hker : φ.ker ≤ Subgroup.center (StatedSp 2 F) :=
    CurtisTits.ker_le_center_of_isQuasisimple hq ⟨_, hφ1⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  exact center_sp_eq_one_of_charTwo (hker hg)

theorem exists_b2Levi_of_longInj [Finite F]
    (hinj : ∀ φ : StatedSp 2 F →* K, Function.Injective (φ.comp (spBlock F 1)) →
      Function.Injective φ)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    ∃ φ : StatedSp 2 F →* K, Function.Injective φ ∧
      (∀ γ ∈ pairRoots D s l, ∀ g ∈ D.rootGroup γ, g ∈ φ.range) ∧
      (∀ c, φ (spBlock F 0 (tv 0 1 c)) = x (sroot s) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = x (-sroot s) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = x (sroot l) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = x (-sroot l) c) := by
  obtain ⟨φ, e, hesq, he1, he2, he3, he4, hφ⟩ := exists_b2Hom hE hdiv hcsl hcls
  have hs : ∃ ρ : SL(2, F) →* K, ∀ c, ρ (tv 0 1 c) = x (sroot s) c ∧
      ρ (tv 1 0 c) = x (-sroot s) c := by
    obtain ⟨ρ, -, hu, hl⟩ := hE.rankOne s
    exact ⟨ρ, fun c => ⟨by rw [tv01_eq_sl2Upper, hu], by rw [tv10_eq_sl2Lower, hl]⟩⟩
  have hl : ∃ ρ : SL(2, F) →* K, Function.Injective ρ ∧
      ∀ c, ρ (tv 0 1 c) = x (sroot l) c ∧
        ρ (tv 1 0 c) = x (-sroot l) c := by
    obtain ⟨ρ, hρ, hu, hl⟩ := hE.rankOne l
    exact ⟨ρ, hρ, fun c => ⟨by rw [tv01_eq_sl2Upper, hu], by rw [tv10_eq_sl2Lower, hl]⟩⟩
  obtain ⟨ρs, hρs⟩ := hs
  obtain ⟨ρl, hρlinj, hρl⟩ := hl
  obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ hρs hρl
  have hinjφ : Function.Injective φ := by
    apply hinj
    rw [hb1]
    exact hρlinj
  refine ⟨φ, hinjφ, fun γ hγ g hg => ?_, fun c => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := pairRoots_subset_zB2 hdiv hcsl hcls hγ
    obtain ⟨c, rfl⟩ := ((hE.param _ (pair_mem_roots_zB2 hcsl hcls z hz)).1 g).1 hg
    refine ⟨Steinberg.Sp.x 2 F (pair (spS (F := F)) spL z) (e z * c), ?_⟩
    rw [hφ _ (pair_mem_sp_roots hz), sp_coords_pair, ← mul_assoc, hesq z hz, one_mul]
  · have h1 := congrArg (fun f : SL(2, F) →* K => f (tv 0 1 c)) hb0
    have h2 := congrArg (fun f : SL(2, F) →* K => f (tv 1 0 c)) hb0
    have h3 := congrArg (fun f : SL(2, F) →* K => f (tv 0 1 c)) hb1
    have h4 := congrArg (fun f : SL(2, F) →* K => f (tv 1 0 c)) hb1
    simp only [MonoidHom.comp_apply] at h1 h2 h3 h4
    exact ⟨h1.trans (hρs c).1, h2.trans (hρs c).2, h3.trans (hρl c).1, h4.trans (hρl c).2⟩

theorem exists_sp4Levi_of_longInj [Finite F]
    (hinj : ∀ φ : StatedSp 2 F →* K, Function.Injective (φ.comp (spBlock F 1)) →
      Function.Injective φ)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) {i j : Fin D.rank}
    (hcij : D.cartan i j = -2) (hcji : D.cartan j i = -1) :
    ∃ φ : StatedSp 2 F →* K, Function.Injective φ ∧
      (∀ γ ∈ pairRoots D i j, D.rootGroup γ ≤ φ.range) ∧
      ∀ c, φ (spBlock F 0 (tv 0 1 c)) = x (sroot i) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = x (-sroot i) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = x (sroot j) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = x (-sroot j) c := by
  obtain ⟨φ, hφ, hle, hv⟩ := exists_b2Levi_of_longInj hinj hE hdiv hcij hcji
  exact ⟨φ, hφ, fun γ hγ g hg => hle γ hγ g hg, hv⟩

theorem exists_sp4Levi_even [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) {i j : Fin D.rank}
    (hcij : D.cartan i j = -2) (hcji : D.cartan j i = -1) :
    ∃ φ : StatedSp 2 F →* K, Function.Injective φ ∧
      (∀ γ ∈ pairRoots D i j, D.rootGroup γ ≤ φ.range) ∧
      ∀ c, φ (spBlock F 0 (tv 0 1 c)) = x (sroot i) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = x (-sroot i) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = x (sroot j) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = x (-sroot j) c :=
  exists_sp4Levi_of_longInj (fun _ h => hom_injective_of_long_even hF h) hE hdiv hcij hcji

end Inj

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

private theorem single_pairRoots_param (hE : Steinberg.ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {k : Fin D.rank} {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ pairRoots D k k) {g : K} (hg : g ∈ D.rootGroup γ) :
    ∃ c, (γ = sroot k ∧ g = x (sroot k) c) ∨ (γ = -sroot k ∧ g = x (-sroot k) c) := by
  obtain ⟨c, rfl⟩ := ((hE.param γ hγ.1).1 g).1 hg
  refine ⟨c, ?_⟩
  have hγ' := pairRoots_self_subset hdiv k hγ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ'
  rcases hγ' with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

private theorem exists_leviEmbedding_node
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X} (k : Fin D.rank) :
    ∃ (E : LeviEmbedding D k k) (φ : E.L →* X), ∀ k', (k' = k ∨ k' = k) → ∀ c,
      φ (E.preimage (x (sroot k') c)) = ρ k' (tv 0 1 c) ∧
        φ (E.preimage (x (-sroot k') c)) = ρ k' (tv 1 0 c) := by
  obtain ⟨emb, hinj, hle, hv⟩ := exists_sl2Levi hE hdiv k
  refine ⟨⟨SL(2, F), emb, hinj, hle⟩, ρ k, fun k' hk c => ?_⟩
  have hk' : k' = k := by rcases hk with h | h <;> exact h
  subst hk'
  exact ⟨by rw [preimage_eq_of_emb (E := ⟨SL(2, F), emb, hinj, hle⟩) (hv c).1],
    by rw [preimage_eq_of_emb (E := ⟨SL(2, F), emb, hinj, hle⟩) (hv c).2]⟩

private theorem exists_leviEmbedding_doubleBond_longShort [Finite F]
    (hinj : ∀ φ : StatedSp 2 F →* K, Function.Injective (φ.comp (spBlock F 1)) →
      Function.Injective φ)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {a b : Fin D.rank} (hcba : D.cartan b a = -2) (hcab : D.cartan a b = -1)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X} {ψ4 : StatedSp 2 F →* X}
    (hψ41 : ψ4.comp (spBlock F 1) = ρ a) (hψ40 : ψ4.comp (spBlock F 0) = ρ b) :
    ∃ (E : LeviEmbedding D a b) (φ : E.L →* X), ∀ k, (k = a ∨ k = b) → ∀ c,
      φ (E.preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
        φ (E.preimage (x (-sroot k) c)) = ρ k (tv 1 0 c) := by
  obtain ⟨φ, hφinj, hφle, hφv⟩ := exists_sp4Levi_of_longInj hinj hE hdiv hcba hcab
  refine ⟨⟨StatedSp 2 F, φ, hφinj, fun γ hγ => hφle γ (by rwa [pairRoots_comm] at hγ)⟩,
    ψ4, fun k hk c => ?_⟩
  rcases hk with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hφv c).2.2.1]
      exact DFunLike.congr_fun hψ41 (tv 0 1 c)
    · rw [preimage_eq_of_emb (hφv c).2.2.2]
      exact DFunLike.congr_fun hψ41 (tv 1 0 c)
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hφv c).1]
      exact DFunLike.congr_fun hψ40 (tv 0 1 c)
    · rw [preimage_eq_of_emb (hφv c).2.1]
      exact DFunLike.congr_fun hψ40 (tv 1 0 c)

private theorem exists_leviEmbedding_doubleBond_shortLong [Finite F]
    (hinj : ∀ φ : StatedSp 2 F →* K, Function.Injective (φ.comp (spBlock F 1)) →
      Function.Injective φ)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {a b : Fin D.rank} (hcba : D.cartan b a = -2) (hcab : D.cartan a b = -1)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X} {ψ4 : StatedSp 2 F →* X}
    (hψ41 : ψ4.comp (spBlock F 1) = ρ a) (hψ40 : ψ4.comp (spBlock F 0) = ρ b) :
    ∃ (E : LeviEmbedding D b a) (φ : E.L →* X), ∀ k, (k = b ∨ k = a) → ∀ c,
      φ (E.preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
        φ (E.preimage (x (-sroot k) c)) = ρ k (tv 1 0 c) := by
  obtain ⟨φ, hφinj, hφle, hφv⟩ := exists_sp4Levi_of_longInj hinj hE hdiv hcba hcab
  refine ⟨⟨StatedSp 2 F, φ, hφinj, hφle⟩, ψ4, fun k hk c => ?_⟩
  rcases hk with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hφv c).1]
      exact DFunLike.congr_fun hψ40 (tv 0 1 c)
    · rw [preimage_eq_of_emb (hφv c).2.1]
      exact DFunLike.congr_fun hψ40 (tv 1 0 c)
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hφv c).2.2.1]
      exact DFunLike.congr_fun hψ41 (tv 0 1 c)
    · rw [preimage_eq_of_emb (hφv c).2.2.2]
      exact DFunLike.congr_fun hψ41 (tv 1 0 c)

private theorem exists_leviEmbedding_singleBond [Finite F]
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {i j k : Fin D.rank} (hij : i ≠ j) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) (hk : ¬ (3 : ℤ) ∣ D.cartan i k + 2 * D.cartan j k)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X} {ψ : SL(3, F) →* X}
    (hψ0 : ψ.comp (blk F 0) = ρ i) (hψ1 : ψ.comp (blk F 1) = ρ j) :
    ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k', (k' = i ∨ k' = j) → ∀ c,
      φ (E.preimage (x (sroot k') c)) = ρ k' (tv 0 1 c) ∧
        φ (E.preimage (x (-sroot k') c)) = ρ k' (tv 1 0 c) := by
  obtain ⟨emb, hinj, hle, hv⟩ := exists_sl3Levi hE hdiv hij hcij hcji hk
  refine ⟨⟨SL(3, F), emb, hinj, hle⟩, ψ, fun k' hk' c => ?_⟩
  rcases hk' with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hv c).1]
      have := DFunLike.congr_fun hψ0 (tv 0 1 c)
      rw [MonoidHom.comp_apply, blk_zero_tv01] at this
      exact this
    · rw [preimage_eq_of_emb (hv c).2.1]
      have := DFunLike.congr_fun hψ0 (tv 1 0 c)
      rw [MonoidHom.comp_apply, blk_zero_tv10] at this
      exact this
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hv c).2.2.1]
      have := DFunLike.congr_fun hψ1 (tv 0 1 c)
      rw [MonoidHom.comp_apply, blk_one_tv01] at this
      exact this
    · rw [preimage_eq_of_emb (hv c).2.2.2]
      have := DFunLike.congr_fun hψ1 (tv 1 0 c)
      rw [MonoidHom.comp_apply, blk_one_tv10] at this
      exact this

private theorem exists_leviEmbedding_singleBond_comm [Finite F]
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {i j k : Fin D.rank} (hji : j ≠ i) (hcji : D.cartan j i = -1)
    (hcij : D.cartan i j = -1) (hk : ¬ (3 : ℤ) ∣ D.cartan j k + 2 * D.cartan i k)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X} {ψ : SL(3, F) →* X}
    (hψ0 : ψ.comp (blk F 0) = ρ j) (hψ1 : ψ.comp (blk F 1) = ρ i) :
    ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k', (k' = i ∨ k' = j) → ∀ c,
      φ (E.preimage (x (sroot k') c)) = ρ k' (tv 0 1 c) ∧
        φ (E.preimage (x (-sroot k') c)) = ρ k' (tv 1 0 c) := by
  obtain ⟨emb, hinj, hle, hv⟩ := exists_sl3Levi hE hdiv hji hcji hcij hk
  refine ⟨⟨SL(3, F), emb, hinj, fun γ hγ => hle γ (by rwa [pairRoots_comm] at hγ)⟩, ψ,
    fun k' hk' c => ?_⟩
  rcases hk' with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hv c).2.2.1]
      have := DFunLike.congr_fun hψ1 (tv 0 1 c)
      rw [MonoidHom.comp_apply, blk_one_tv01] at this
      exact this
    · rw [preimage_eq_of_emb (hv c).2.2.2]
      have := DFunLike.congr_fun hψ1 (tv 1 0 c)
      rw [MonoidHom.comp_apply, blk_one_tv10] at this
      exact this
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hv c).1]
      have := DFunLike.congr_fun hψ0 (tv 0 1 c)
      rw [MonoidHom.comp_apply, blk_zero_tv01] at this
      exact this
    · rw [preimage_eq_of_emb (hv c).2.1]
      have := DFunLike.congr_fun hψ0 (tv 1 0 c)
      rw [MonoidHom.comp_apply, blk_zero_tv10] at this
      exact this

private theorem exists_leviEmbedding_orthogonal
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {i j : Fin D.rank} (hij : i ≠ j) (hcij : D.cartan i j = 0)
    (hcji : D.cartan j i = 0) {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {adj : Fin D.rank → Fin D.rank → Prop} {X : Type} [Group X]
    {U : Fin D.rank → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* X}
    (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hnij : ¬ adj i j) (hnji : ¬ adj j i) :
    ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) → ∀ c,
      φ (E.preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
        φ (E.preimage (x (-sroot k) c)) = ρ k (tv 1 0 c) := by
  obtain ⟨l, hl, hle, hv⟩ := exists_sl2sl2Levi hE hdiv hij hcij hcji hind hsq
  have hc : ∀ u v, Commute (ρ i u) (ρ j v) := fun u v =>
    hcomm i j hij hnij hnji (ρ i u) (by rw [← (hρ i).2]; exact ⟨u, rfl⟩) (ρ j v)
      (by rw [← (hρ j).2]; exact ⟨v, rfl⟩)
  refine ⟨⟨SL(2, F) × SL(2, F), l, hl, hle⟩, (ρ i).noncommCoprod (ρ j) hc,
    fun k hk c => ?_⟩
  rcases hk with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hv c).1, MonoidHom.noncommCoprod_apply, map_one, mul_one]
    · rw [preimage_eq_of_emb (hv c).2.1, MonoidHom.noncommCoprod_apply, map_one, mul_one]
  · refine ⟨?_, ?_⟩
    · rw [preimage_eq_of_emb (hv c).2.2.1, MonoidHom.noncommCoprod_apply, map_one, one_mul]
    · rw [preimage_eq_of_emb (hv c).2.2.2, MonoidHom.noncommCoprod_apply, map_one, one_mul]

private theorem exists_leviEmbedding_of_lt [Finite F]
    (hinj : ∀ φ : StatedSp 2 F →* K, Function.Injective (φ.comp (spBlock F 1)) →
      Function.Injective φ)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* X}
    (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j)
    {ψ4 : StatedSp 2 F →* X}
    (hψ41 : ψ4.comp (spBlock F 1) = ρ a) (hψ40 : ψ4.comp (spBlock F 0) = ρ b)
    {i j : Fin D.rank} (hlt : i < j) :
    ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) → ∀ c,
      φ (E.preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
        φ (E.preimage (x (-sroot k) c)) = ρ k (tv 1 0 c) := by
  obtain ⟨-, hcba, hcab, hadj, hnadj, hnb⟩ := hdiag
  by_cases hij : adj i j
  · by_cases hd : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hd
      exact exists_leviEmbedding_doubleBond_longShort hinj hE hdiv hcba hcab hψ41 hψ40
    · obtain ⟨hc1, hc2⟩ := hadj i j hij hd
      obtain ⟨k', hk'⟩ := hnb i j hij hd
      obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij hd
      exact exists_leviEmbedding_singleBond hE hdiv hlt.ne hc1 hc2 hk' hψ0 hψ1
  · by_cases hji : adj j i
    · by_cases hd : j = a ∧ i = b
      · obtain ⟨rfl, rfl⟩ := hd
        exact exists_leviEmbedding_doubleBond_shortLong hinj hE hdiv hcba hcab hψ41 hψ40
      · obtain ⟨hc1, hc2⟩ := hadj j i hji hd
        obtain ⟨k', hk'⟩ := hnb j i hji hd
        obtain ⟨ψ, hψ0, hψ1⟩ := hψ j i hji hd
        exact exists_leviEmbedding_singleBond_comm hE hdiv hlt.ne' hc1 hc2 hk' hψ0 hψ1
    · obtain ⟨hc1, hc2⟩ := hnadj i j hlt.ne hij hji
      exact exists_leviEmbedding_orthogonal hE hdiv hlt.ne hc1 hc2 hind hsq hcomm hρ hij hji

private theorem exists_leviEmbedding_pair [Finite F]
    (hinj : ∀ φ : StatedSp 2 F →* K, Function.Injective (φ.comp (spBlock F 1)) →
      Function.Injective φ)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* X}
    (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j)
    {ψ4 : StatedSp 2 F →* X}
    (hψ41 : ψ4.comp (spBlock F 1) = ρ a) (hψ40 : ψ4.comp (spBlock F 0) = ρ b) :
    ∀ i j (_ : i ≤ j), ∃ (E : LeviEmbedding D i j) (φ : E.L →* X),
      ∀ k, (k = i ∨ k = j) → ∀ c,
        φ (E.preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
          φ (E.preimage (x (-sroot k) c)) = ρ k (tv 1 0 c) := by
  intro i j h
  rcases h.eq_or_lt with rfl | hlt
  · exact exists_leviEmbedding_node hE hdiv i
  · exact exists_leviEmbedding_of_lt hinj hE hdiv hdiag hind hsq hcomm hρ hψ hψ41 hψ40 hlt

private theorem compatible_on_nodes
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X}
    {E : ∀ i j, i ≤ j → LeviEmbedding D i j}
    {φ : ∀ i j (h : i ≤ j), (E i j h).L →* X}
    (hspec : ∀ (i j : Fin D.rank) (h : i ≤ j) (k : Fin D.rank), (k = i ∨ k = j) → ∀ c,
      φ i j h ((E i j h).preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
        φ i j h ((E i j h).preimage (x (-sroot k) c)) = ρ k (tv 1 0 c)) :
    ∀ i j (h : i ≤ j) k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots D k k, ∀ g ∈ D.rootGroup γ,
      φ i j h ((E i j h).preimage g) = φ k k le_rfl ((E k k le_rfl).preimage g) := by
  intro i j h k hk γ hγ g hg
  obtain ⟨c, hc⟩ := single_pairRoots_param hE hdiv hγ hg
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [(hspec i j h k hk c).1, (hspec k k le_rfl k (Or.inl rfl) c).1]
  · rw [(hspec i j h k hk c).2, (hspec k k le_rfl k (Or.inl rfl) c).2]

private theorem frameMap_single
    (hE : Steinberg.ChevalleyExtras D F x C O)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X}
    {E : ∀ i j, i ≤ j → LeviEmbedding D i j}
    {φ : ∀ i j (h : i ≤ j), (E i j h).L →* X}
    (hspec : ∀ (i j : Fin D.rank) (h : i ≤ j) (k : Fin D.rank), (k = i ∨ k = j) → ∀ c,
      φ i j h ((E i j h).preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
        φ i j h ((E i j h).preimage (x (-sroot k) c)) = ρ k (tv 1 0 c))
    (k : Fin D.rank) (c : F) :
    frameMap E φ (Pi.single k 1) ⟨x (sroot k) c, x_mem hE (single_mem_roots k) c⟩ =
      ρ k (tv 0 1 c) := by
  rw [frameMap_of_mem_self (Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (k := k)
    (Or.inl rfl)).1]
  exact (hspec k k le_rfl k (Or.inl rfl) c).1

private theorem frameMap_neg_single
    (hE : Steinberg.ChevalleyExtras D F x C O)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X}
    {E : ∀ i j, i ≤ j → LeviEmbedding D i j}
    {φ : ∀ i j (h : i ≤ j), (E i j h).L →* X}
    (hspec : ∀ (i j : Fin D.rank) (h : i ≤ j) (k : Fin D.rank), (k = i ∨ k = j) → ∀ c,
      φ i j h ((E i j h).preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
        φ i j h ((E i j h).preimage (x (-sroot k) c)) = ρ k (tv 1 0 c))
    (k : Fin D.rank) (c : F) :
    frameMap E φ (-Pi.single k 1)
        ⟨x (-sroot k) c, x_mem hE (neg_mem_roots (single_mem_roots k)) c⟩ =
      ρ k (tv 1 0 c) := by
  rw [frameMap_of_mem_self (Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (k := k)
    (Or.inl rfl)).2]
  exact (hspec k k le_rfl k (Or.inl rfl) c).2

private theorem frameMap_closure_eq_top
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X}
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hE : Steinberg.ChevalleyExtras D F x C O)
    {E : ∀ i j, i ≤ j → LeviEmbedding D i j}
    {φ : ∀ i j (h : i ≤ j), (E i j h).L →* X}
    (hfmu : ∀ k c, frameMap E φ (Pi.single k 1)
      ⟨x (sroot k) c, x_mem hE (single_mem_roots k) c⟩ = ρ k (tv 0 1 c))
    (hfmv : ∀ k c, frameMap E φ (-Pi.single k 1)
      ⟨x (-sroot k) c, x_mem hE (neg_mem_roots (single_mem_roots k)) c⟩ = ρ k (tv 1 0 c))
    (hgen : ⨆ k, U k = ⊤) :
    Subgroup.closure (⋃ k, Set.range (frameMap E φ (Pi.single k 1)) ∪
      Set.range (frameMap E φ (-Pi.single k 1))) = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun k => ?_
  rw [← (hρ k).2]
  refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
  · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl
      ⟨⟨x (sroot k) c, x_mem hE (single_mem_roots k) c⟩, hfmu k c⟩⟩)
  · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr
      ⟨⟨x (-sroot k) c, x_mem hE (neg_mem_roots (single_mem_roots k)) c⟩, hfmv k c⟩⟩)

private theorem frameMap_exists_ne_one
    (hE : Steinberg.ChevalleyExtras D F x C O)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X} {a : Fin D.rank}
    (hρa : Function.Injective (ρ a))
    {E : ∀ i j, i ≤ j → LeviEmbedding D i j}
    {φ : ∀ i j (h : i ≤ j), (E i j h).L →* X}
    (hfmu : ∀ k c, frameMap E φ (Pi.single k 1)
      ⟨x (sroot k) c, x_mem hE (single_mem_roots k) c⟩ = ρ k (tv 0 1 c)) :
    ∃ k, ∃ y, frameMap E φ (Pi.single k 1) y ≠ 1 := by
  refine ⟨a, ⟨x (sroot a) 1, x_mem hE (single_mem_roots a) 1⟩, ?_⟩
  rw [hfmu]
  intro h
  exact tv_zero_one_one_ne_one (hρa (h.trans (map_one _).symm))

private theorem map_on_sroot
    (hE : Steinberg.ChevalleyExtras D F x C O)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X}
    {E : ∀ i j, i ≤ j → LeviEmbedding D i j}
    {φ : ∀ i j (h : i ≤ j), (E i j h).L →* X} {Ψ : K →* X}
    (hΨu : ∀ k (g : D.rootGroup (Pi.single k 1)), Ψ g = frameMap E φ _ g)
    (hfmu : ∀ k c, frameMap E φ (Pi.single k 1)
      ⟨x (sroot k) c, x_mem hE (single_mem_roots k) c⟩ = ρ k (tv 0 1 c)) :
    ∀ k c, Ψ (x (sroot k) c) = ρ k (tv 0 1 c) := fun k c => by
  have := hΨu k ⟨x (sroot k) c, x_mem hE (single_mem_roots k) c⟩
  rw [hfmu] at this
  exact this

private theorem map_on_neg_sroot
    (hE : Steinberg.ChevalleyExtras D F x C O)
    {X : Type} [Group X] {ρ : Fin D.rank → SL(2, F) →* X}
    {E : ∀ i j, i ≤ j → LeviEmbedding D i j}
    {φ : ∀ i j (h : i ≤ j), (E i j h).L →* X} {Ψ : K →* X}
    (hΨv : ∀ k (g : D.rootGroup (-Pi.single k 1)), Ψ g = frameMap E φ _ g)
    (hfmv : ∀ k c, frameMap E φ (-Pi.single k 1)
      ⟨x (-sroot k) c, x_mem hE (neg_mem_roots (single_mem_roots k)) c⟩ = ρ k (tv 1 0 c)) :
    ∀ k c, Ψ (x (-sroot k) c) = ρ k (tv 1 0 c) := fun k c => by
  have := hΨv k ⟨x (-sroot k) c, x_mem hE (neg_mem_roots (single_mem_roots k)) c⟩
  rw [hfmv] at this
  exact this

private theorem rankOne_map_eq
    (hE : Steinberg.ChevalleyExtras D F x C O)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X}
    {ρ : Fin D.rank → SL(2, F) →* X} {k : Fin D.rank} (hU : (ρ k).range = U k)
    {Ψ : K →* X}
    (hΨu : ∀ i c, Ψ (x (sroot i) c) = ρ i (tv 0 1 c))
    (hΨv : ∀ i c, Ψ (x (-sroot i) c) = ρ i (tv 1 0 c)) :
    (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  have hρU : ∀ c, ρ k (tv 0 1 c) ∈ U k ∧ ρ k (tv 1 0 c) ∈ U k := fun c => by
    rw [← hU]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  rw [CurtisTits.rankOne, Subgroup.map_sup]
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := ((hE.param _ (single_mem_roots k)).1 g).1 hg
      rw [hΨu k c]
      exact (hρU c).1
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := ((hE.param _ (neg_mem_roots (single_mem_roots k))).1 g).1 hg
      rw [hΨv k c]
      exact (hρU c).2
  · rw [← hU]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · exact Subgroup.mem_sup_left ⟨x (sroot k) c, x_mem hE (single_mem_roots k) c, hΨu k c⟩
    · exact Subgroup.mem_sup_right
        ⟨x (-sroot k) c, x_mem hE (neg_mem_roots (single_mem_roots k)) c, hΨv k c⟩

theorem weakCT_of_frame_dl_of_longInj [Finite F]
    (hinj : ∀ φ : StatedSp 2 F →* K, Function.Injective (φ.comp (spBlock F 1)) →
      Function.Injective φ)
    {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j)
    (hψ4 : ∃ ψ : StatedSp 2 F →* X, ψ.comp (spBlock F 1) = ρ a ∧ ψ.comp (spBlock F 0) = ρ b) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  classical
  obtain ⟨ψ4, hψ41, hψ40⟩ := hψ4
  have hloc := exists_leviEmbedding_pair hinj hE hdiv hdiag hind hsq hcomm hρ hψ hψ41 hψ40
  choose E φ hspec using hloc
  have hcompat := compatible_on_nodes hE hdiv hspec
  have hfmu := frameMap_single hE hspec
  have hfmv := frameMap_neg_single hE hspec
  have hgen' := frameMap_closure_eq_top hρ hE hfmu hfmv hgen
  have hnt := frameMap_exists_ne_one hE (hρ a).1 hfmu
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩ :=
    CFSG.WeakCTLevi.exists_surjective_of_leviEmbeddings hCT hL E φ hcompat hgen' hnt
  refine ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ?_⟩
  exact rankOne_map_eq hE (hρ k).2 (map_on_sroot hE hΨu hfmu) (map_on_neg_sroot hE hΨv hfmv)

theorem weakCT_of_frame_dl_even [Finite F] [CharP F 2] {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hF : 4 ≤ Nat.card F)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j)
    (hψ4 : ∃ ψ : StatedSp 2 F →* X, ψ.comp (spBlock F 1) = ρ a ∧ ψ.comp (spBlock F 0) = ρ b) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k :=
  weakCT_of_frame_dl_of_longInj (fun _ h => hom_injective_of_long_even hF h)
    hCT hL hE hdiv hdiag hind hsq hgen hcomm hρ hψ hψ4

theorem weakCT_doublyLaced_even [CharP F 2] {F₀ : Type} [Field F₀] [Finite F₀]
    (e : F₀ ≃+* F) {t : StatedLieTag}
    {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hF : 4 ≤ Nat.card F₀)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {par : Fin D.rank → Fin D.rank} {dep : Fin D.rank → ℕ} {k₀ : Fin D.rank}
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀) (hpar : par b = a)
    (hb0 : b ≠ k₀) {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hpair : ∀ i j, adj i j → ¬ (i = a ∧ j = b) →
      ∃ W, LinearBlockStandardPair F₀ W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair F₀ W (U a) (U b)) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  have : Finite F := Finite.of_equiv F₀ e.toEquiv
  have hF' : 4 ≤ Nat.card F := by rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨ρ, hρ, hψ, ψ4, -, hψ41, hψ40⟩ :=
    exists_frame_of_tree_sp hF hT hroot hdiag.adj_ab hpar hb0 hcomm hpair hsp
  obtain ⟨Φ, hΦ⟩ := exists_spMap (F := F) e.symm.toRingHom
  let φ₂ : SL(2, F) →* SL(2, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let φ₃ : SL(3, F) →* SL(3, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rwa [map_symm_map, map_symm_map] at this
  have hφ₂surj : ∀ A : SL(2, F₀), ∃ B : SL(2, F), φ₂ B = A := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.toRingHom A, map_map_symm e A⟩
  refine weakCT_of_frame_dl_even hCT hL hE hdiv hF' hdiag hind hsq hgen hcomm
    (ρ := fun k => (ρ k).comp φ₂) (fun k => ⟨(hρ k).1.comp hφ₂inj, ?_⟩) (fun i j hij hne => ?_)
    ⟨ψ4.comp Φ, ?_, ?_⟩
  · rw [← (hρ k).2]
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨φ₂ B, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  · obtain ⟨ψ', hψ0, hψ1⟩ := hψ i j hij hne
    refine ⟨ψ'.comp φ₃, ?_, ?_⟩
    · ext A
      show ψ' (φ₃ (blk F 0 A)) = ρ i (φ₂ A)
      rw [← hψ0, MonoidHom.comp_apply]
      exact congrArg ψ' (map_blk e.symm.toRingHom 0 A)
    · ext A
      show ψ' (φ₃ (blk F 1 A)) = ρ j (φ₂ A)
      rw [← hψ1, MonoidHom.comp_apply]
      exact congrArg ψ' (map_blk e.symm.toRingHom 1 A)
  · rw [MonoidHom.comp_assoc, spMap_comp_spBlock e.symm.toRingHom hΦ 1, ← MonoidHom.comp_assoc,
      hψ41]
  · rw [MonoidHom.comp_assoc, spMap_comp_spBlock e.symm.toRingHom hΦ 0, ← MonoidHom.comp_assoc,
      hψ40]

end Recognition

section Symplectic

theorem weakCT_symplectic_even {n f : ℕ} (hadm : StatedLieAdmissible .PSp n 2 f) (hn : 3 ≤ n)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (hq : 4 ≤ Nat.card F) {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (StatedSp n F)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSp n 2 f ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup k).map Ψ = U k := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Symplectic.rootDatum n F).isFiniteType
    (Dv := (Symplectic.rootDatum n F).divisible) rfl
  have hE := Steinberg.Sp.chevalleyExtras (by omega : 2 ≤ n) O Steinberg.Sp.commC
    (Steinberg.Sp.commutatorFormula O)
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a.val + 1 = n := ⟨⟨n - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b.val + 2 = n := ⟨⟨n - 2, by omega⟩, by simp only; omega⟩
  have hsq : ∀ k : Fin n,
      Steinberg.weylElement (Steinberg.Sp.x n F) k 1 ^ 2 ∈ Symplectic.torus n F k := by
    intro k
    rw [weylElement_sp_one]
    exact (Symplectic.isCTGroupDatum n F).sq_mem k
  have hroot : ∃ c : Fin n, edgeDown n ⟨n - 1, by omega⟩ c ∨ edgeDown n c ⟨n - 1, by omega⟩ :=
    ⟨⟨n - 2, by omega⟩, Or.inl (by simp only [edgeDown]; omega)⟩
  have hpar : parentDown n b = a := Fin.ext (by simp only [parentDown]; omega)
  have hb0 : b ≠ ⟨n - 1, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp only at this
    omega
  have hcomm' : ∀ i j : Fin n, i ≠ j → ¬ edgeDown n i j → ¬ edgeDown n j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hne h1 h2' u hu v hv
    simp only [edgeDown] at h1 h2'
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm i j (by omega) u hu v hv
    · exact (hcomm j i (by omega) v hv u hu).symm
  have hpair' : ∀ i j : Fin n, edgeDown n i j → ¬ (i = a ∧ j = b) →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hn'
    simp only [edgeDown] at hij
    obtain ⟨W, hW⟩ := hpair j i hij (by
      have := i.2
      by_contra hc
      exact hn' ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
    exact ⟨W, hW.symm⟩
  exact weakCT_doublyLaced_even (RingEquiv.refl F)
    (CurtisTits.curtisTitsConclusion_symplectic hadm hF hn)
    (leviConePresented_symplectic n F) hE rfl hq (doubleBondDiagram_cartanC hn ha hb)
    (Symplectic.steinbergExtras n F).torus_iSupIndep hsq (rootedTree_edgeDown (n := n) (by omega))
    hroot hpar hb0 hgen hcomm' hpair' (hsp a b ha hb)

end Symplectic

end CFSG.RankThree.PartOne.CTP

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.LieType
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.Timmesfeld
open scoped MatrixGroups

section TagPairAD

private theorem linearBlockStandardPair_map_of_chevalleyExtras
    {K G : Type} [Group K] [Group G] {F : Type} [Field F] [Finite F]
    {D : UniversalRootDatum K}
    {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) {i j k : Fin D.rank}
    (hij : i ≠ j) (hcij : D.cartan i j = -1) (hcji : D.cartan j i = -1)
    (hk : ¬ (3 : ℤ) ∣ D.cartan i k + 2 * D.cartan j k)
    (ψ : K →* G) (hψ : ψ.ker ≤ Subgroup.center K) :
    ∃ W, LinearBlockStandardPair F W ((ggRootLevi D (Pi.single i 1)).map ψ)
      ((ggRootLevi D (Pi.single j 1)).map ψ) := by
  obtain ⟨emb, hinj, -, hx⟩ := exists_sl3Levi hE hdiv hij hcij hcji hk
  have hset : ∀ γ ∈ D.roots, ((D.rootGroup γ).map ψ : Set G) = Set.range (ψ ∘ x γ) := by
    intro γ hγ
    have hγ' : (D.rootGroup γ : Set K) = Set.range (x γ) :=
      Set.ext fun g => (hE.param γ hγ).1 g
    rw [Subgroup.coe_map, hγ', Set.range_comp]
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hneg : ∀ l : Fin D.rank, -Pi.single l 1 ∈ D.roots := fun l =>
    Steinberg.OfCartan.neg_mem_roots D.isFiniteType (hΦ.single_mem l)
  have hcomm : ∀ c, (ψ.comp emb) (tv 0 1 c) = (ψ ∘ x (Pi.single i 1)) c ∧
      (ψ.comp emb) (tv 1 0 c) = (ψ ∘ x (-Pi.single i 1)) c ∧
      (ψ.comp emb) (tv 1 2 c) = (ψ ∘ x (Pi.single j 1)) c ∧
      (ψ.comp emb) (tv 2 1 c) = (ψ ∘ x (-Pi.single j 1)) c := by
    intro c
    obtain ⟨h1, h2, h3, h4⟩ := hx c
    exact ⟨by simpa using congrArg ψ h1, by simpa using congrArg ψ h2,
      by simpa using congrArg ψ h3, by simpa using congrArg ψ h4⟩
  have hker : (ψ.comp emb).ker ≤ Subgroup.center (SL(3, F)) := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzK : emb z ∈ Subgroup.center K := by
      apply hψ
      rw [MonoidHom.mem_ker]
      simpa using hz
    rw [Subgroup.mem_center_iff] at hzK
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    rw [map_mul, map_mul]
    exact hzK (emb g)
  have hUi : rankOne (fun γ => (D.rootGroup γ).map ψ) i =
      (ggRootLevi D (Pi.single i 1)).map ψ := by
    change (D.rootGroup (Pi.single i 1)).map ψ ⊔ (D.rootGroup (-Pi.single i 1)).map ψ =
      (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).map ψ
    rw [Subgroup.map_sup]
  have hUj : rankOne (fun γ => (D.rootGroup γ).map ψ) j =
      (ggRootLevi D (Pi.single j 1)).map ψ := by
    change (D.rootGroup (Pi.single j 1)).map ψ ⊔ (D.rootGroup (-Pi.single j 1)).map ψ =
      (D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1)).map ψ
    rw [Subgroup.map_sup]
  have hpair := linearBlockStandardPair_rankOne (K := G) (F := F)
    (X := fun γ => (D.rootGroup γ).map ψ) (x := fun γ => ψ ∘ x γ)
    (hset _ (hΦ.single_mem i)) (hset _ (hneg i))
    (hset _ (hΦ.single_mem j)) (hset _ (hneg j))
    (ψ.comp emb) hker hcomm
  refine ⟨(ψ.comp emb).range, ?_⟩
  rw [hUi, hUj] at hpair
  exact hpair

theorem ggTagAD_adjStdPair {t : StatedLieTag} {n f : ℕ} (ht : t = .PSL ∨ t = .POmegaPlus)
    (hadm : StatedLieAdmissible t n 2 f) (h3 : 3 ≤ bnRank t n) :
    ∃ a b : Fin (ggU t n f).D.rank,
      (coxeterMatrix (ggU t n f).D.isFiniteType).M a b = 3 ∧
        ∀ {G : Type} [Group G] (ψ : (ggU t n f).K →* G),
          ψ.ker ≤ Subgroup.center (ggU t n f).K →
            ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W
              ((ggRootLevi (ggU t n f).D (Pi.single a 1)).map ψ)
              ((ggRootLevi (ggU t n f).D (Pi.single b 1)).map ψ) := by
  rcases ht with rfl | rfl
  ·
    have hn : 4 ≤ n := by simp only [bnRank] at h3; omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm3 : 3 ≤ m := by omega
    have hm2 : 2 ≤ m := by omega
    have hm0 : 0 < m := by omega
    have hm1 : 1 < m := by omega
    have hm2' : 2 < m := by omega
    have h01 : (⟨0, hm0⟩ : Fin m) ≠ ⟨1, hm1⟩ := by
      rw [ne_eq, Fin.ext_iff]
      simp
    have hcij : (SpecialLinear.rootDatum m (GaloisField 2 f)).cartan
        ⟨0, hm0⟩ ⟨1, hm1⟩ = -1 := by
      show CartanMatrix.A m ⟨0, hm0⟩ ⟨1, hm1⟩ = -1
      simp [CartanMatrix.A]
    have hcji : (SpecialLinear.rootDatum m (GaloisField 2 f)).cartan
        ⟨1, hm1⟩ ⟨0, hm0⟩ = -1 := by
      show CartanMatrix.A m ⟨1, hm1⟩ ⟨0, hm0⟩ = -1
      simp [CartanMatrix.A]
    have hk : ¬ (3 : ℤ) ∣ (SpecialLinear.rootDatum m (GaloisField 2 f)).cartan
          ⟨0, hm0⟩ ⟨2, hm2'⟩ +
        2 * (SpecialLinear.rootDatum m (GaloisField 2 f)).cartan ⟨1, hm1⟩ ⟨2, hm2'⟩ := by
      show ¬ (3 : ℤ) ∣ CartanMatrix.A m ⟨0, hm0⟩ ⟨2, hm2'⟩ +
        2 * CartanMatrix.A m ⟨1, hm1⟩ ⟨2, hm2'⟩
      simp only [CartanMatrix.A]
      norm_num
    have hM : (coxeterMatrix (ggU .PSL (m + 1) f).D.isFiniteType).M
        ⟨0, hm0⟩ ⟨1, hm1⟩ = 3 := by
      change (coxeterMatrix (SpecialLinear.rootDatum m (GaloisField 2 f)).isFiniteType).M
        ⟨0, hm0⟩ ⟨1, hm1⟩ = 3
      rw [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
      rw [hcij, hcji, show (-1 : ℤ) * -1 = 1 by norm_num]
      exact TauCeti.coxeterOrder_one
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (SpecialLinear.rootDatum m (GaloisField 2 f)).isFiniteType
      (Dv := (SpecialLinear.rootDatum m (GaloisField 2 f)).divisible) rfl
    have hE := Steinberg.SL.chevalleyExtras hm2 O _ (Steinberg.SL.commutatorFormula O)
    have hdiv : (SpecialLinear.rootDatum m (GaloisField 2 f)).divisible = ∅ := rfl
    refine ⟨⟨0, hm0⟩, ⟨1, hm1⟩, hM, ?_⟩
    intro G _ ψ hψ
    exact linearBlockStandardPair_map_of_chevalleyExtras hE hdiv h01 hcij hcji hk ψ hψ
  ·
    have hn3 : 3 ≤ n := by simpa only [bnRank] using h3
    have hn4 : 4 ≤ n := hadm.2.2
    have h0 : 0 < n := by omega
    have h1 : 1 < n := by omega
    have h2 : 2 < n := by omega
    have h01 : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
      rw [ne_eq, Fin.ext_iff]
      simp
    have hU : ggU .POmegaPlus n f =
        ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
      simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
    rw [hU]
    have hcij : (Spin.plusDatum n (GaloisField 2 f) hn3).cartan ⟨0, h0⟩ ⟨1, h1⟩ = -1 := by
      show Spin.cartanD n ⟨0, h0⟩ ⟨1, h1⟩ = -1
      simp [Spin.cartanD, Fin.ext_iff]
      omega
    have hcji : (Spin.plusDatum n (GaloisField 2 f) hn3).cartan ⟨1, h1⟩ ⟨0, h0⟩ = -1 := by
      show Spin.cartanD n ⟨1, h1⟩ ⟨0, h0⟩ = -1
      simp [Spin.cartanD, Fin.ext_iff]
      omega
    have hk : ¬ (3 : ℤ) ∣ (Spin.plusDatum n (GaloisField 2 f) hn3).cartan ⟨0, h0⟩ ⟨2, h2⟩ +
        2 * (Spin.plusDatum n (GaloisField 2 f) hn3).cartan ⟨1, h1⟩ ⟨2, h2⟩ := by
      show ¬ (3 : ℤ) ∣ Spin.cartanD n ⟨0, h0⟩ ⟨2, h2⟩ +
        2 * Spin.cartanD n ⟨1, h1⟩ ⟨2, h2⟩
      simp [Spin.cartanD, Fin.ext_iff]
      omega
    have hM : (coxeterMatrix (Spin.plusDatum n (GaloisField 2 f) hn3).isFiniteType).M
        ⟨0, h0⟩ ⟨1, h1⟩ = 3 := by
      change (coxeterMatrix (Spin.isFiniteType_cartanD n)).M ⟨0, h0⟩ ⟨1, h1⟩ = 3
      rw [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
      have h1' : Spin.cartanD n ⟨0, h0⟩ ⟨1, h1⟩ = -1 := by
        simp [Spin.cartanD, Fin.ext_iff]
        omega
      have h2' : Spin.cartanD n ⟨1, h1⟩ ⟨0, h0⟩ = -1 := by
        simp [Spin.cartanD, Fin.ext_iff]
        omega
      rw [h1', h2', show (-1 : ℤ) * -1 = 1 by norm_num]
      exact TauCeti.coxeterOrder_one
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (Spin.plusDatum n (GaloisField 2 f) hn3).isFiniteType
      (Dv := (Spin.plusDatum n (GaloisField 2 f) hn3).divisible) rfl
    have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
      (Steinberg.SpinPlus.commutatorFormula hn3 O)
    have hdiv : (Spin.plusDatum n (GaloisField 2 f) hn3).divisible = ∅ := rfl
    refine ⟨⟨0, h0⟩, ⟨1, h1⟩, hM, ?_⟩
    intro G _ ψ hψ
    exact linearBlockStandardPair_map_of_chevalleyExtras hE hdiv h01 hcij hcji hk ψ hψ

end TagPairAD

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupOrb
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpLeaf
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitWeylEquiv
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitD4
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDNoSameSupp_of_not_orbPair {G : Type} [Group G] {L Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hno : ¬ GGOrbPair L Bs 𝒦 M e (σ ⟨k - 2, by omega⟩) (σ ⟨k - 1, by omega⟩)) :
    GGDNoSameSupp e φ := by
  rintro X hX a b hab ⟨⟨t, ht, htX⟩, t', ht', ht'X⟩
  exact hno ((ggDk_orbPair_of_member hk φ hφ hX htX ht'X).1 ⟨a, b, 1, hab, Or.inl rfl, ht, ht'⟩)

private theorem fork_row {k : ℕ} (hk : 4 ≤ k) (z : Fin k) (h1 : z.val ≠ k - 2)
    (h2 : z.val ≠ k - 1) :
    ggCoxeterMatrixD k ⟨k - 2, by omega⟩ z = ggCoxeterMatrixD k ⟨k - 1, by omega⟩ z := by
  by_cases h3 : z.val + 3 = k
  · rw [(ggCoxeterMatrixD k).symmetric _ z, (ggCoxeterMatrixD k).symmetric _ z,
      ggCoxeterMatrixD_eq_three hk z ⟨k - 2, by omega⟩
        (Or.inl ⟨show z.val + 1 = k - 2 by omega, show k - 2 + 1 < k by omega⟩),
      ggCoxeterMatrixD_eq_three hk z ⟨k - 1, by omega⟩ (Or.inr ⟨h3, show k - 1 + 1 = k by omega⟩)]
  · rw [ggCoxeterMatrixD_eq_two hk ⟨k - 2, by omega⟩ z (fun h => h1 (by rw [← h]))
        (by simp only [CFSG.Timmesfeld.edgeD]; omega)
        (by simp only [CFSG.Timmesfeld.edgeD]; omega),
      ggCoxeterMatrixD_eq_two hk ⟨k - 1, by omega⟩ z (fun h => h2 (by rw [← h]))
        (by simp only [CFSG.Timmesfeld.edgeD]; omega)
        (by simp only [CFSG.Timmesfeld.edgeD]; omega)]

private theorem swap_invariant_of_rows {k : ℕ} (N : CoxeterMatrix (Fin k)) {c d : Fin k}
    (hrow : ∀ z, z ≠ c → z ≠ d → N c z = N d z) (x y : Fin k) :
    N (Equiv.swap c d x) (Equiv.swap c d y) = N x y := by
  have hrow' : ∀ z, z ≠ c → z ≠ d → N z c = N z d := fun z hzc hzd => by
    rw [N.symmetric z c, N.symmetric z d, hrow z hzc hzd]
  rcases eq_or_ne x c with hxc | hxc
  · rw [hxc, Equiv.swap_apply_left]
    rcases eq_or_ne y c with hyc | hyc
    · rw [hyc, Equiv.swap_apply_left, N.diagonal, N.diagonal]
    rcases eq_or_ne y d with hyd | hyd
    · rw [hyd, Equiv.swap_apply_right, N.symmetric]
    · rw [Equiv.swap_apply_of_ne_of_ne hyc hyd, hrow y hyc hyd]
  rcases eq_or_ne x d with hxd | hxd
  · rw [hxd, Equiv.swap_apply_right]
    rcases eq_or_ne y c with hyc | hyc
    · rw [hyc, Equiv.swap_apply_left, N.symmetric]
    rcases eq_or_ne y d with hyd | hyd
    · rw [hyd, Equiv.swap_apply_right, N.diagonal, N.diagonal]
    · rw [Equiv.swap_apply_of_ne_of_ne hyc hyd, hrow y hyc hyd]
  rw [Equiv.swap_apply_of_ne_of_ne hxc hxd]
  rcases eq_or_ne y c with hyc | hyc
  · rw [hyc, Equiv.swap_apply_left, hrow' x hxc hxd]
  rcases eq_or_ne y d with hyd | hyd
  · rw [hyd, Equiv.swap_apply_right, hrow' x hxc hxd]
  · rw [Equiv.swap_apply_of_ne_of_ne hyc hyd]

private theorem fork_swap {k : ℕ} (hk : 4 ≤ k) (x y : Fin k) :
    ggCoxeterMatrixD k (Equiv.swap ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ x)
      (Equiv.swap ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ y) = ggCoxeterMatrixD k x y :=
  swap_invariant_of_rows _ (fun z hzc hzd => fork_row hk z (fun h => hzc (Fin.ext h))
    (fun h => hzd (Fin.ext h))) x y

theorem ggDk_fork_of_disjPair {G : Type} [Group G] {L Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) {i j : ι} (hij : i ≠ j) (h2 : M.M i j = 2)
    (hno : ¬ GGOrbPair L Bs 𝒦 M e i j)
    (hdisj : 5 ≤ k → ∀ φ : M.Group ≃* ggWeylD k,
      (∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a) →
      ∃ t t' : M.Group, GGDDisjSupp k (φ t) (φ t') ∧
        ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs ∧
        ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs) :
    ∃ σ' : Fin k ≃ ι, M = (ggCoxeterMatrixD k).reindex σ' ∧ σ' ⟨k - 2, by omega⟩ = i ∧
      σ' ⟨k - 1, by omega⟩ = j := by
  rcases (show k = 4 ∨ 5 ≤ k by omega) with rfl | hk5
  · exact ggD4_fork_numbering hM hij h2
  have h2' : ggCoxeterMatrixD k (σ.symm i) (σ.symm j) = 2 := by
    rw [hM, CoxeterMatrix.reindex_apply] at h2
    exact h2
  have hval : ∀ (n : ℕ) (hn : n < k) (a : Fin k), a.val = n → (⟨n, hn⟩ : Fin k) = a :=
    fun n hn a h => Fin.ext h.symm
  by_cases hf : (σ.symm i).val + 2 = k ∧ (σ.symm j).val + 1 = k
  · refine ⟨σ, hM, ?_, ?_⟩
    · rw [hval (k - 2) (by omega) (σ.symm i) (by omega), Equiv.apply_symm_apply]
    · rw [hval (k - 1) (by omega) (σ.symm j) (by omega), Equiv.apply_symm_apply]
  by_cases hf' : (σ.symm i).val + 1 = k ∧ (σ.symm j).val + 2 = k
  · refine ⟨(Equiv.swap ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩).trans σ, ?_, ?_, ?_⟩
    · rw [hM]
      ext y z
      rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply, Equiv.symm_trans_apply,
        Equiv.symm_trans_apply, Equiv.symm_swap, fork_swap hk]
    · rw [Equiv.trans_apply, Equiv.swap_apply_left, hval (k - 1) (by omega) (σ.symm i) (by omega),
        Equiv.apply_symm_apply]
    · rw [Equiv.trans_apply, Equiv.swap_apply_right,
        hval (k - 2) (by omega) (σ.symm j) (by omega), Equiv.apply_symm_apply]
  obtain ⟨φ, hφ⟩ := ggDk_weylEquiv hM
  obtain ⟨t, t', hd, ht, ht'⟩ := hdisj hk5 φ hφ
  have h := (ggDk_orbPair_of_member hk φ hφ (Or.inl rfl) ht ht').2 hk5 hd
    (σ.symm.injective.ne hij) h2' hf hf'
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact absurd h hno

theorem ggDk_fork_of_not_orbPair
    (hpos : GGSecFiveKGPosInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) {i j : ι} (hij : i ≠ j) (h2 : M.M i j = 2)
    (hno : ¬ GGOrbPair L Bs 𝒦 M e i j) :
    ∃ σ' : Fin k ≃ ι, M = (ggCoxeterMatrixD k).reindex σ' ∧ σ' ⟨k - 2, by omega⟩ = i ∧
      σ' ⟨k - 1, by omega⟩ = j :=
  ggDk_fork_of_disjPair hk hM hij h2 hno fun hk5 φ hφ =>
    ggDk_memberRoots_L_disjSupp hpos hcfg hsplit hpres hle3 hk5 hM φ hφ

end CFSG.StandardType

end

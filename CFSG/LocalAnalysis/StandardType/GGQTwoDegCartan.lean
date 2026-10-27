module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

private def qTwoDegB_permCongrMulEquiv {α β : Type*} (f : α ≃ β) :
    Equiv.Perm α ≃* Equiv.Perm β where
  toFun σ := f.symm.trans (σ.trans f)
  invFun σ := f.trans (σ.trans f.symm)
  left_inv σ := by
    ext x
    simp
  right_inv σ := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp

private theorem qTwoDegB_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ≃ β) (a b : α) :
    qTwoDegB_permCongrMulEquiv f (Equiv.swap a b) = Equiv.swap (f a) (f b) := by
  classical
  ext x
  change f ((Equiv.swap a b) (f.symm x)) = (Equiv.swap (f a) (f b)) x
  by_cases h : x = f a
  · subst h
    simp
  · by_cases h2 : x = f b
    · subst h2
      simp [h]
    · have hx : f.symm x ≠ a := fun hh =>
        h ((f.apply_symm_apply x).symm.trans (congrArg f hh))
      have hx2 : f.symm x ≠ b := fun hh =>
        h2 ((f.apply_symm_apply x).symm.trans (congrArg f hh))
      simp [Equiv.swap_apply_def, h, h2, hx, hx2]

theorem qTwoDeg_cartan_of_pres
    (hCart : GGCartanRankLe)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} (hN : 6 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e') :
    3 ^ (N - 1 - (if 3 ∣ N then 1 else 0)) ≤ Nat.card Bs := by
  classical
  subst hM
  generalize hd : N - 1 = d at *
  have hd1 : d + 1 = N := by omega
  have hd0 : 0 < d := by omega
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm d
  let f : Fin N ≃ Fin (d + 1) := finCongr hd1.symm
  let pc : Equiv.Perm (Fin N) ≃* Equiv.Perm (Fin (d + 1)) := qTwoDegB_permCongrMulEquiv f
  let eb : (CoxeterMatrix.A d).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦) :=
    (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A d) e').symm.trans e
  let ρeq : Equiv.Perm (Fin N) ≃* ↥(ggAutomizerJoin L Bs 𝒦) := pc.trans (e0.symm.trans eb)
  let ρ : Equiv.Perm (Fin N) →* MulAut ↥Bs :=
    (Subgroup.subtype (ggAutomizerJoin L Bs 𝒦)).comp ρeq.toMonoidHom
  have hρinj : Function.Injective ρ := by
    intro a b hab
    exact ρeq.injective (Subtype.val_injective hab)
  have hρrefl : ∀ a b : Fin N, a ≠ b → GGIsReflection 3 (ρ (Equiv.swap a b)) := by
    let i0 : Fin d := ⟨0, hd0⟩
    let E2 : Equiv.Perm (Fin (d + 1)) →* MulAut ↥Bs := ρ.comp pc.symm.toMonoidHom
    have hfix : GGIsReflection 3 (E2 (Equiv.swap i0.castSucc i0.succ)) := by
      have hsimple : e0.symm (Equiv.swap i0.castSucc i0.succ) = (CoxeterMatrix.A d).simple i0 := by
        rw [← he0 i0, MulEquiv.symm_apply_apply]
      have hE : (E2 (Equiv.swap i0.castSucc i0.succ) : MulAut ↥Bs) =
          ((eb ((CoxeterMatrix.A d).simple i0) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
        simp [E2, ρ, ρeq, hsimple]
      have hsym : (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A d) e').symm
          ((CoxeterMatrix.A d).simple i0) =
            (CoxeterMatrix.reindex e' (CoxeterMatrix.A d)).simple (e' i0) := by
        rw [MulEquiv.symm_apply_eq, CoxeterMatrix.reindexGroupEquiv_apply_simple]
        simp
      rw [hE]
      have hEb : ((eb ((CoxeterMatrix.A d).simple i0) : ↥(ggAutomizerJoin L Bs 𝒦)) :
            MulAut ↥Bs) =
          ((e ((CoxeterMatrix.reindex e' (CoxeterMatrix.A d)).simple (e' i0)) :
            ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
        simp [eb, hsym]
      rw [hEb]
      exact hP.2 (e' i0)
    intro a b hab
    let u : Fin (d + 1) := f a
    let v : Fin (d + 1) := f b
    have huv : u ≠ v := by
      intro h
      exact hab (f.injective (by simpa [u, v] using h))
    have hswap : pc.symm (Equiv.swap u v) = Equiv.swap a b := by
      have h1 : pc (Equiv.swap a b) = Equiv.swap u v := by
        simpa [pc, u, v] using qTwoDegB_permCongr_swap f a b
      rw [← h1, MulEquiv.symm_apply_apply]
    have hr := ggIsReflection_swap_of_swap (p := 3) E2 (a := i0.castSucc) (b := i0.succ)
      (by exact Fin.castSucc_lt_succ.ne) hfix (x := u) (y := v) huv
    simpa [E2, hswap] using hr
  have hρnotr : ∀ g, ¬ GGIsTransvection 3 (ρ g) := by
    intro g htr
    have hmemAut : (ρ g : MulAut ↥Bs) ∈ ggAutomizer (⊤ : Subgroup G) Bs := by
      have hjoin : (ρ g : MulAut ↥Bs) ∈ ggAutomizerJoin L Bs 𝒦 := (ρeq g).2
      have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (⊤ : Subgroup G) Bs := by
        unfold ggAutomizerJoin
        refine sup_le (ggAutomizer_mono Bs le_top) ?_
        refine iSup₂_le fun K hK => ggAutomizer_mono Bs le_top
      exact hle hjoin
    have hmemInd : (ρ g : MulAut ↥Bs) ∈ ggInduced (⊤ : Subgroup G) Bs :=
      mem_ggAutomizer_iff.mp hmemAut
    exact hcfg.1.2.2.2.1 (ρ g) hmemInd htr
  simpa [hd] using hCart Nat.prime_three (by norm_num)
    hcfg.1.1.2.1.2.1 ρ hρinj hρrefl hρnotr

theorem qTwoDeg_cartan_bound_le {Bs L : Subgroup G} {x : G} {k : QTwoRowKind} {m d c : ℕ}
    (hrow : QTwoRowData k m d c Bs L x) {N : ℕ}
    (hCartan : 3 ^ (N - 1 - (if 3 ∣ N then 1 else 0)) ≤ Nat.card Bs) :
    N - 1 - (if 3 ∣ N then 1 else 0) ≤ d := by
  have hpow : 3 ^ (N - 1 - (if 3 ∣ N then 1 else 0)) ≤ 3 ^ d := by
    rw [hrow.card] at hCartan
    exact hCartan
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow

end CFSG.StandardType.QTwo

end

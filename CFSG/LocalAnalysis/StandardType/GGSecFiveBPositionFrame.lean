module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBMaxToPair
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGSpFrameIsoCoord
public import CFSG.LocalAnalysis.StandardType.GGSpFrameClosure
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic

private theorem exists_frame_coords_B {G : Type} [Group G] {Bs : Subgroup G} [Finite Bs]
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hm : 1 ≤ m)
    (hrank : Nat.card Bs = p ^ (m + 1)) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A) :
    ∃ (e : (coxeterMatrix (isFiniteType_cartanC (m + 1))).Group ≃* ↥A)
      (Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      ∀ (k : Fin (m + 1)) (a : Fin (m + 1) → Multiplicative (ZMod p)),
        ((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).simple k) : ↥A) : MulAut ↥Bs)
          (Φ a) = Φ (SpJoin.spReflPerm (m + 1) p k a) := by
  have hW' : GGWeylOfType p (coxeterMatrix (isFiniteType_cartanC (m + 1))) A := by
    rw [coxeterMatrix_cartanC_eq_B]
    exact hW
  obtain ⟨e, he⟩ := hW'
  exact ⟨e, SpFrame.exists_frame_coords hp hp2 hBs hm hrank e he⟩

private theorem map_congr_eq_bSignedFull {H : Type*} [Group H] {Bs : Subgroup H}
    {p N : ℕ} {A : Subgroup (MulAut ↥Bs)}
    (e : (coxeterMatrix (isFiniteType_cartanC N)).Group ≃* ↥A)
    (Φ : (Fin N → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hΦ : ∀ (k : Fin N) (a : Fin N → Multiplicative (ZMod p)),
      ((e ((coxeterMatrix (isFiniteType_cartanC N)).simple k) : ↥A) : MulAut ↥Bs) (Φ a) =
        Φ (SpJoin.spReflPerm N p k a)) :
    Subgroup.map (MulAut.congr Φ.symm).toMonoidHom A = bSignedFull N p := by
  let F : MulAut ↥Bs →* MulAut (Fin N → Multiplicative (ZMod p)) :=
    (MulAut.congr Φ.symm).toMonoidHom
  let s : Fin N → MulAut ↥Bs :=
    fun k => ((e ((coxeterMatrix (isFiniteType_cartanC N)).simple k) : ↥A) : MulAut ↥Bs)
  let u : Fin N → MulAut (Fin N → Multiplicative (ZMod p)) := fun k => F (s k)
  have hu : ∀ (k : Fin N) (a : Fin N → Multiplicative (ZMod p)),
      u k a = SpJoin.spReflPerm N p k a := by
    intro k a
    show MulAut.congr Φ.symm (s k) a = SpJoin.spReflPerm N p k a
    simpa [MulAut.congr_apply] using congrArg Φ.symm (hΦ k a)
  have hArange : (A.subtype.comp e.toMonoidHom).range = A := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hgen := map_closure_range_eq_of_simple (coxeterMatrix (isFiniteType_cartanC N)) F s
    (F.comp (A.subtype.comp e.toMonoidHom)) (fun _ => rfl)
  calc Subgroup.map F A
      = (F.comp (A.subtype.comp e.toMonoidHom)).range := by
        rw [MonoidHom.range_comp, hArange]
    _ = Subgroup.map F (Subgroup.closure (Set.range s)) := hgen.symm
    _ = Subgroup.closure (F '' Set.range s) := MonoidHom.map_closure F _
    _ = Subgroup.closure (Set.range u) := by
        rw [← Set.range_comp]
        rfl
    _ = bSignedFull N p := closure_spReflPerm_eq_bSignedFull u hu

theorem GGWeylOfType.exists_bSignedFull_coords
    {G : Type} [Group G] {Bs : Subgroup G} [Finite Bs] {p m : ℕ}
    {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A)
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hm : 1 ≤ m)
    (hrank : Nat.card Bs = p ^ (m + 1)) :
    ∃ eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)),
      A.map (MulAut.congr eta).toMonoidHom = bSignedFull (m + 1) p ∧
      ∀ h ∈ SpJoin.spSignedGroup (m + 1) p, ∃ ψ ∈ A,
        ∀ a, ψ (eta.symm a) = eta.symm (h a) := by
  obtain ⟨e, Φ, hΦ⟩ := exists_frame_coords_B hp hp2 hBs hm hrank hW
  exact ⟨Φ.symm, map_congr_eq_bSignedFull e Φ hΦ,
    SpFrame.exists_induced_of_spSignedGroup Φ fun k =>
      ⟨_, (e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).simple k)).2, hΦ k⟩⟩

private theorem ggIsWeylMatrix_B {n : ℕ} (hn : 2 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.B n) :=
  Or.inl ⟨n, Equiv.refl _, by omega,
    Or.inr (Or.inl ⟨hn, CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)⟩)⟩

theorem GGCoxeterPres.of_reindex_B {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {ι : Type} {n : ℕ} {e' : Fin n ≃ ι} {A : Subgroup (MulAut ↥Bs)}
    {e : ((CoxeterMatrix.B n).reindex e').Group ≃* ↥A} (hn : 2 ≤ n)
    (hP : GGCoxeterPres p A ((CoxeterMatrix.B n).reindex e') e) :
    GGCoxeterPres p A (CoxeterMatrix.B n)
      (((CoxeterMatrix.B n).reindexGroupEquiv e').symm.trans e) := by
  refine ⟨ggIsWeylMatrix_B hn, fun i => ?_⟩
  have hEi : (((CoxeterMatrix.B n).reindexGroupEquiv e').symm.trans e)
      ((CoxeterMatrix.B n).simple i) =
      e (((CoxeterMatrix.B n).reindex e').simple (e' i)) := by
    rw [MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
  have h := hP.2 (e' i)
  rw [← hEi] at h
  exact h

theorem GGSecFiveRouteCfg.exists_bSignedFull_coords {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {n : ℕ} (hn : 2 ≤ n) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) :
    4 ≤ n ∧ ∃ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p := by
  classical
  obtain ⟨hp, hBs, -, -, h4⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hM : GGIsWeylMatrixB (CoxeterMatrix.B (m + 1)) :=
    ⟨m + 1, Equiv.refl _, by omega, (ggCoxeterMatrix_reindex_refl _).symm⟩
  have hW : GGWeylOfType p (CoxeterMatrix.B (m + 1)) (ggAutomizerJoin L Bs 𝒦) :=
    ⟨e, hP.2⟩
  obtain ⟨y, K, hN, hsup⟩ := hR.exists_join_eq_of_typeB hTBF hWI e hP hM
  have hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ b = b) → b = 1 := by
    intro b hb
    refine GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hR.1 hR.2.1 hN b ?_
    intro φ hφ
    exact hb φ (hsup ▸ hφ)
  have hcardle : Nat.card Bs ≤ p ^ (m + 1) := by
    simpa using SpJoinRefl.card_le_pow_of_weylOfType hW hfix
  have hcardge : p ^ (m + 1) ≤ Nat.card Bs :=
    pow_le_card_of_weylOfType_B hp hp2 hBs (by omega) hW
  have hrank : Nat.card Bs = p ^ (m + 1) := le_antisymm hcardle hcardge
  have h4n : 4 ≤ m + 1 := by
    refine (Nat.pow_le_pow_iff_right hp.one_lt).mp ?_
    rw [← hrank]
    exact h4
  obtain ⟨eta, heta, -⟩ := hW.exists_bSignedFull_coords hp hp2 hBs hm hrank
  exact ⟨h4n, eta, heta⟩

end CFSG.StandardType

end

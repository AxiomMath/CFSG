module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRep
public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Nat
import CFSG.LieType.SpecialLinear.ExteriorModel.AdjointHeart
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.Quasithin
open CFSG.Open
open CFSG.LieType.SpecialLinear
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.QuasithinUnique.Setup.Layer
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

private noncomputable def c2slnat_mulEquivVAdd (V : Type) [CommGroup V] :
    V ≃* Multiplicative (Additive V) where
  toFun v := Multiplicative.ofAdd (Additive.ofMul v)
  invFun w := Additive.toMul w.toAdd
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem c2slnat_binPsi_mulEquivVAdd {W : Type} [CommGroup W]
    [Module (ZMod 2) (Additive W)] (φ : MulAut W) (w : Additive W) :
    binPsi (c2slnat_mulEquivVAdd W) φ w = mulAutLinear φ w := rfl

private theorem c2slnat_coe_ofSingleton {n : ℕ} (a : Fin n) :
    ((Set.powersetCard.ofSingleton a : Set.powersetCard (Fin n) 1) : Finset (Fin n)) = {a} := rfl

private noncomputable def c2slnat_complsEquiv (n : ℕ) (hn : 2 ≤ n) :
    Fin n ≃ Set.powersetCard (Fin n) (n - 1) :=
  Equiv.ofBijective (fun a => ⟨{a}ᶜ, by simp [Finset.card_compl]⟩)
    ⟨fun a b h => Finset.singleton_injective (compl_injective (congrArg Subtype.val h)),
      fun s => by
        have hc : (s : Finset (Fin n))ᶜ.card = 1 := by
          rw [Finset.card_compl, s.2, Fintype.card_fin]
          omega
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
        refine ⟨a, Subtype.ext ?_⟩
        show ({a}ᶜ : Finset (Fin n)) = s
        rw [← ha, compl_compl]⟩

private theorem c2slnat_extTwist_one {K : Type} [Field K] [Fintype K] [CharP K 2]
    (n r : ℕ) (g : SpecialLinearGroup (Fin n) K) (a b : Fin n) :
    extTwist n 1 r K g (Set.powersetCard.ofSingleton a) (Set.powersetCard.ofSingleton b) =
      ((slFrobAut n r K g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b := by
  rw [coe_slFrobAut]
  exact AdjointHeartModel.minor_singleton rfl _ _ _ (c2slnat_coe_ofSingleton a)
    (c2slnat_coe_ofSingleton b)

private theorem c2slnat_extTwist_compl {K : Type} [Field K] [Fintype K] [CharP K 2]
    (n r : ℕ) (hn : 2 ≤ n) (g : SpecialLinearGroup (Fin n) K) (a b : Fin n) :
    extTwist n (n - 1) r K g (c2slnat_complsEquiv n hn a) (c2slnat_complsEquiv n hn b) =
      ((slTransposeInvAut n K (slFrobAut n r K g) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) a b := by
  rw [coe_slTransposeInvAut, coe_slFrobAut, Matrix.transpose_apply]
  exact AdjointHeartModel.minor_compl_eq_adjugate (n := n) (by omega) _ a b

private theorem c2slnat_extTwist_eq_one_of_fixed {K : Type} [Field K] [CharP K 2]
    (n j r : ℕ) (z : SpecialLinearGroup (Fin n) K)
    (hfix : ∀ v : Set.powersetCard (Fin n) j → K, extTwist n j r K z *ᵥ v = v) :
    extTwist n j r K z = 1 := by
  ext s t
  have h := congrFun (hfix (Pi.single t 1)) s
  rw [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply, Pi.single_apply] at h
  rw [Matrix.one_apply]
  exact h

private theorem c2slnat_eq_one_of_extTwist_one {K : Type} [Field K] [Fintype K] [CharP K 2]
    (n r : ℕ) (z : SpecialLinearGroup (Fin n) K) (hM : extTwist n 1 r K z = 1) : z = 1 := by
  have hmat : ((slFrobAut n r K z : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    ext a b
    rw [← c2slnat_extTwist_one n r z a b]
    have h := congrFun (congrFun hM (Set.powersetCard.ofSingleton a))
      (Set.powersetCard.ofSingleton b)
    rw [h, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · have he : ¬ (Set.powersetCard.ofSingleton a = Set.powersetCard.ofSingleton b) :=
        fun hh => hab (Set.powersetCard.ofSingleton.injective hh)
      rw [if_neg hab, if_neg he]
  have h1 : slFrobAut n r K z = 1 := Subtype.ext hmat
  exact (slFrobAut n r K).injective (by rw [h1, map_one])

private theorem c2slnat_eq_one_of_extTwist_compl {K : Type} [Field K] [Fintype K] [CharP K 2]
    (n r : ℕ) (hn : 2 ≤ n) (z : SpecialLinearGroup (Fin n) K)
    (hM : extTwist n (n - 1) r K z = 1) : z = 1 := by
  have hmat : ((slTransposeInvAut n K (slFrobAut n r K z) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    ext a b
    rw [← c2slnat_extTwist_compl n r hn z a b]
    have h := congrFun (congrFun hM (c2slnat_complsEquiv n hn a))
      (c2slnat_complsEquiv n hn b)
    rw [h, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · have he : ¬ (c2slnat_complsEquiv n hn a = c2slnat_complsEquiv n hn b) :=
        fun hh => hab ((c2slnat_complsEquiv n hn).injective hh)
      rw [if_neg hab, if_neg he]
  have hA : slTransposeInvAut n K (slFrobAut n r K z) = 1 := Subtype.ext hmat
  have h1 : slFrobAut n r K z = 1 :=
    (slTransposeInvAut n K).injective (by rw [hA, map_one])
  exact (slFrobAut n r K).injective (by rw [h1, map_one])

private theorem c2slnat_isSLn {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {n f : ℕ}
    {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ f)
    (ψ : ↥L ≃* SpecialLinearGroup (Fin n) K) : IsSLn ↥L n f :=
  ⟨K, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hK],
    ⟨ψ.trans (specialLinearGroupEquivStatedSL n K)⟩⟩

private theorem c2slnat_binaryNaturalSL_one {W : Type} [CommGroup W]
    [Module (ZMod 2) (Additive W)] {L : Subgroup (MulAut W)} {n f : ℕ}
    {K : Type} [Field K] [Fintype K] [CharP K 2] (hK : Fintype.card K = 2 ^ f)
    (ψ : ↥L ≃* SpecialLinearGroup (Fin n) K) (r : ℕ)
    (β : Additive W ≃+ (Set.powersetCard (Fin n) 1 → K))
    (hβ : ∀ (l : ↥L) (w : Additive W),
      β (binPsi (c2slnat_mulEquivVAdd W) (l : MulAut W) w) =
        extTwist n 1 r K (ψ l) *ᵥ β w) :
    BinaryNaturalSL L ⊤ ⊥ n f := by
  classical
  refine ⟨K, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hK], ?_⟩
  let Θ : ↥L ≃* ↥(StatedSL n K) :=
    (ψ.trans (slFrobAut n r K)).trans (specialLinearGroupEquivStatedSL n K)
  let e : Fin n ≃ Set.powersetCard (Fin n) 1 := Set.powersetCard.ofSingleton
  let β' : Additive W ≃+ (Fin n → K) :=
    β.trans (LinearEquiv.funCongrLeft K K e).toAddEquiv
  refine realizes_nat_of_equiv (c2slnat_mulEquivVAdd W) Θ β' fun l w => ?_
  funext a
  have hl : ((Θ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((slFrobAut n r K (ψ l) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := rfl
  change (β (binPsi (c2slnat_mulEquivVAdd W) (l : MulAut W) w)) (e a) =
    (((Θ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun b => β w (e b)) a
  rw [hβ l w, hl, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [c2slnat_extTwist_one]

private theorem c2slnat_binaryNaturalSL_compl {W : Type} [CommGroup W]
    [Module (ZMod 2) (Additive W)] {L : Subgroup (MulAut W)} {n f : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Fintype K] [CharP K 2] (hK : Fintype.card K = 2 ^ f)
    (ψ : ↥L ≃* SpecialLinearGroup (Fin n) K) (r : ℕ)
    (β : Additive W ≃+ (Set.powersetCard (Fin n) (n - 1) → K))
    (hβ : ∀ (l : ↥L) (w : Additive W),
      β (binPsi (c2slnat_mulEquivVAdd W) (l : MulAut W) w) =
        extTwist n (n - 1) r K (ψ l) *ᵥ β w) :
    BinaryNaturalSL L ⊤ ⊥ n f := by
  classical
  refine ⟨K, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hK], ?_⟩
  let Θ : ↥L ≃* ↥(StatedSL n K) :=
    ((ψ.trans (slFrobAut n r K)).trans (slTransposeInvAut n K)).trans
      (specialLinearGroupEquivStatedSL n K)
  let e : Fin n ≃ Set.powersetCard (Fin n) (n - 1) := c2slnat_complsEquiv n hn
  let β' : Additive W ≃+ (Fin n → K) :=
    β.trans (LinearEquiv.funCongrLeft K K e).toAddEquiv
  refine realizes_nat_of_equiv (c2slnat_mulEquivVAdd W) Θ β' fun l w => ?_
  funext a
  have hl : ((Θ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((slTransposeInvAut n K (slFrobAut n r K (ψ l)) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := rfl
  change (β (binPsi (c2slnat_mulEquivVAdd W) (l : MulAut W) w)) (e a) =
    (((Θ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun b => β w (e b)) a
  rw [hβ l w, hl, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [c2slnat_extTwist_compl n r hn]

theorem w135c2_psl_natural {W : Type} [CommGroup W] [Finite W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {n f : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2 ^ f) (φ : SpecialLinearGroup (Fin n) K →* ↥L)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    {j r : ℕ} (hj : j = 1 ∨ j + 1 = n) (β : Additive W ≃+ (Set.powersetCard (Fin n) j → K))
    (hβ : ∀ g w, β (pslRep φ g w) = extTwist n j r K g *ᵥ β w) : Chev2Natural W L := by
  classical
  rcases hj with rfl | hj
  · have hker_bot : φ.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hz1 : φ z = 1 := MonoidHom.mem_ker.mp hz
      have hfixβ : ∀ w : Additive W, pslRep φ z w = w := by
        intro w
        simp [pslRep_apply, hz1, mulAutLinear_one]
      have hM : extTwist n 1 r K z = 1 := by
        apply c2slnat_extTwist_eq_one_of_fixed
        intro v
        have h := hβ z (β.symm v)
        rw [hfixβ (β.symm v), AddEquiv.apply_symm_apply] at h
        exact h.symm
      exact c2slnat_eq_one_of_extTwist_one n r z hM
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker_bot
    let ψ : ↥L ≃* SpecialLinearGroup (Fin n) K := (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm
    have hψ_apply : ∀ l : ↥L, φ (ψ l) = l := fun l => by
      change (MulEquiv.ofBijective φ ⟨hinj, hφ⟩)
        ((MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm l) = l
      exact MulEquiv.apply_symm_apply _ l
    have hβ1 : ∀ (l : ↥L) (w : Additive W),
        β (binPsi (c2slnat_mulEquivVAdd W) (l : MulAut W) w) =
          extTwist n 1 r K (ψ l) *ᵥ β w := by
      intro l w
      have hpsl : pslRep φ (ψ l) = mulAutLinear (l : MulAut W) := by
        simp only [pslRep_apply, hψ_apply l]
      rw [c2slnat_binPsi_mulEquivVAdd, ← hpsl]
      exact hβ (ψ l) w
    exact Or.inl ⟨n, f, Or.inl ⟨c2slnat_isSLn hK ψ,
      c2slnat_binaryNaturalSL_one hK ψ r β hβ1⟩⟩
  · have hj' : j = n - 1 := by omega
    subst hj'
    have hker_bot : φ.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hz1 : φ z = 1 := MonoidHom.mem_ker.mp hz
      have hfixβ : ∀ w : Additive W, pslRep φ z w = w := by
        intro w
        simp [pslRep_apply, hz1, mulAutLinear_one]
      have hM : extTwist n (n - 1) r K z = 1 := by
        apply c2slnat_extTwist_eq_one_of_fixed
        intro v
        have h := hβ z (β.symm v)
        rw [hfixβ (β.symm v), AddEquiv.apply_symm_apply] at h
        exact h.symm
      exact c2slnat_eq_one_of_extTwist_compl n r hn z hM
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker_bot
    let ψ : ↥L ≃* SpecialLinearGroup (Fin n) K := (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm
    have hψ_apply : ∀ l : ↥L, φ (ψ l) = l := fun l => by
      change (MulEquiv.ofBijective φ ⟨hinj, hφ⟩)
        ((MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm l) = l
      exact MulEquiv.apply_symm_apply _ l
    have hβ1 : ∀ (l : ↥L) (w : Additive W),
        β (binPsi (c2slnat_mulEquivVAdd W) (l : MulAut W) w) =
          extTwist n (n - 1) r K (ψ l) *ᵥ β w := by
      intro l w
      have hpsl : pslRep φ (ψ l) = mulAutLinear (l : MulAut W) := by
        simp only [pslRep_apply, hψ_apply l]
      rw [c2slnat_binPsi_mulEquivVAdd, ← hpsl]
      exact hβ (ψ l) w
    exact Or.inl ⟨n, f, Or.inl ⟨c2slnat_isSLn hK ψ,
      c2slnat_binaryNaturalSL_compl hn hK ψ r β hβ1⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

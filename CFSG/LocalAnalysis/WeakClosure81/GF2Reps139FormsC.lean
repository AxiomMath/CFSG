module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private lemma w1369_zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private noncomputable def w1369_dotPerm (m : ℕ) :
    G6.PermMod m →* G6.PermMod m →* Multiplicative (ZMod 2) :=
  MonoidHom.mk' (fun x =>
    MonoidHom.mk' (fun y => Multiplicative.ofAdd
        ((Multiplicative.toAdd x) ⬝ᵥ (Multiplicative.toAdd y)))
      (by
        intro y z
        simp only [toAdd_mul, dotProduct_add, ofAdd_add]))
    (by
      intro x y
      apply MonoidHom.ext
      intro z
      show Multiplicative.ofAdd
        ((Multiplicative.toAdd x + Multiplicative.toAdd y) ⬝ᵥ Multiplicative.toAdd z) =
          Multiplicative.ofAdd ((Multiplicative.toAdd x) ⬝ᵥ Multiplicative.toAdd z) *
            Multiplicative.ofAdd ((Multiplicative.toAdd y) ⬝ᵥ Multiplicative.toAdd z)
      rw [add_dotProduct, ofAdd_add])

private noncomputable def w1369_dotCore (m : ℕ) :
    ↥(G6.coreMod m) →* ↥(G6.coreMod m) →* Multiplicative (ZMod 2) where
  toFun x := (w1369_dotPerm m (x : G6.PermMod m)).comp (G6.coreMod m).subtype
  map_one' := by
    change (w1369_dotPerm m (1 : G6.PermMod m)).comp (G6.coreMod m).subtype = 1
    rw [map_one]
    rfl
  map_mul' := by
    intro x y
    change (w1369_dotPerm m ((x : G6.PermMod m) * (y : G6.PermMod m))).comp
        (G6.coreMod m).subtype =
      ((w1369_dotPerm m (x : G6.PermMod m)).comp (G6.coreMod m).subtype) *
        ((w1369_dotPerm m (y : G6.PermMod m)).comp (G6.coreMod m).subtype)
    rw [map_mul]
    rfl

private lemma w1369_dotCore_apply (m : ℕ) (x y : ↥(G6.coreMod m)) :
    w1369_dotCore m x y = Multiplicative.ofAdd
      ((Multiplicative.toAdd (x : G6.PermMod m)) ⬝ᵥ
        (Multiplicative.toAdd (y : G6.PermMod m))) := rfl

private lemma w1369_dotCore_comm (m : ℕ) (x y : ↥(G6.coreMod m)) :
    w1369_dotCore m x y = w1369_dotCore m y x := by
  rw [w1369_dotCore_apply, w1369_dotCore_apply, dotProduct_comm]

private lemma w1369_dotCore_self (m : ℕ) (x : ↥(G6.coreMod m)) :
    w1369_dotCore m x x = 1 := by
  rw [w1369_dotCore_apply]
  have h : (Multiplicative.toAdd (x : G6.PermMod m)) ⬝ᵥ
      (Multiplicative.toAdd (x : G6.PermMod m)) = 0 := by
    rw [dotProduct]
    rw [show (∑ i, Multiplicative.toAdd (x : G6.PermMod m) i *
        Multiplicative.toAdd (x : G6.PermMod m) i) =
        ∑ i, Multiplicative.toAdd (x : G6.PermMod m) i by
      apply Finset.sum_congr rfl
      intro i _
      rcases w1369_zmod_two_eq_zero_or_one
        (Multiplicative.toAdd (x : G6.PermMod m) i) with h | h <;> rw [h] <;> ring]
    exact G6.mem_coreMod.mp x.2
  rw [h, ofAdd_zero]

private lemma w1369_dotPerm_permAct (m : ℕ) (σ : Equiv.Perm (Fin m))
    (x y : G6.PermMod m) :
    w1369_dotPerm m (G6.permAct m σ x) (G6.permAct m σ y) =
      w1369_dotPerm m x y := by
  show Multiplicative.ofAdd
      ((Multiplicative.toAdd (G6.permAct m σ x)) ⬝ᵥ
        (Multiplicative.toAdd (G6.permAct m σ y))) =
    Multiplicative.ofAdd ((Multiplicative.toAdd x) ⬝ᵥ (Multiplicative.toAdd y))
  congr 1
  have hx : Multiplicative.toAdd (G6.permAct m σ x) =
      Multiplicative.toAdd x ∘ σ.symm := by
    funext i
    rw [G6.permAct_apply]
    rfl
  have hy : Multiplicative.toAdd (G6.permAct m σ y) =
      Multiplicative.toAdd y ∘ σ.symm := by
    funext i
    rw [G6.permAct_apply]
    rfl
  rw [hx, hy, dotProduct, dotProduct]
  exact Equiv.sum_comp σ.symm
    (fun i => Multiplicative.toAdd x i * Multiplicative.toAdd y i)

private lemma w1369_dotCore_permAct (m : ℕ) (σ : Equiv.Perm (Fin m))
    (x y : ↥(G6.coreMod m)) :
    w1369_dotCore m
      ⟨G6.permAct m σ (x : G6.PermMod m), G6.permAct_mem_coreMod σ x.2⟩
      ⟨G6.permAct m σ (y : G6.PermMod m), G6.permAct_mem_coreMod σ y.2⟩ =
    w1369_dotCore m x y :=
  w1369_dotPerm_permAct m σ (x : G6.PermMod m) (y : G6.PermMod m)

private abbrev w1369_ker (m : ℕ) : Subgroup ↥(G6.coreMod m) :=
  (Subgroup.zpowers (G6.allOnes m) ⊓ G6.coreMod m).subgroupOf (G6.coreMod m)

private lemma w1369_mem_ker (m : ℕ) (n : ↥(G6.coreMod m)) :
    n ∈ w1369_ker m ↔ (n : G6.PermMod m) ∈ Subgroup.zpowers (G6.allOnes m) := by
  rw [w1369_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left n.2]

private lemma w1369_dotCore_zpowers_eq_one (m : ℕ) (x : ↥(G6.coreMod m))
    (n : ↥(G6.coreMod m)) (hn : (n : G6.PermMod m) ∈ Subgroup.zpowers (G6.allOnes m)) :
    w1369_dotCore m x n = 1 := by
  have h1 : w1369_dotCore m x n =
      w1369_dotPerm m (x : G6.PermMod m) (n : G6.PermMod m) := rfl
  rw [h1]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← hk]
  have hz : w1369_dotPerm m (x : G6.PermMod m) (G6.allOnes m) = 1 := by
    show Multiplicative.ofAdd
      ((Multiplicative.toAdd (x : G6.PermMod m)) ⬝ᵥ
        (Multiplicative.toAdd (G6.allOnes m))) = 1
    have h : (Multiplicative.toAdd (x : G6.PermMod m)) ⬝ᵥ
        (Multiplicative.toAdd (G6.allOnes m)) = 0 := by
      change (Multiplicative.toAdd (x : G6.PermMod m)) ⬝ᵥ
        (1 : Fin m → ZMod 2) = 0
      rw [dotProduct_one]
      exact G6.mem_coreMod.mp x.2
    rw [h, ofAdd_zero]
  rw [map_zpow, hz, one_zpow]

private noncomputable def w1369_formAux (m : ℕ) :
    ↥(G6.coreMod m) →*
      (↥(G6.coreMod m) ⧸ w1369_ker m →* Multiplicative (ZMod 2)) where
  toFun x := QuotientGroup.lift (w1369_ker m) (w1369_dotCore m x) (fun n hn => by
    rw [MonoidHom.mem_ker]
    exact w1369_dotCore_zpowers_eq_one m x n ((w1369_mem_ker m n).mp hn))
  map_one' := by
    refine MonoidHom.ext fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    show w1369_dotCore m 1 z = 1
    rw [map_one]
    rfl
  map_mul' := by
    intro x y
    refine MonoidHom.ext fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    show w1369_dotCore m (x * y) z = w1369_dotCore m x z * w1369_dotCore m y z
    rw [map_mul]
    rfl

private noncomputable def w1369_formQuot (m : ℕ) :
    (↥(G6.coreMod m) ⧸ w1369_ker m) →*
      (↥(G6.coreMod m) ⧸ w1369_ker m) →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift (w1369_ker m) (w1369_formAux m) (fun n hn => by
    change w1369_formAux m n = 1
    refine MonoidHom.ext fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    change w1369_dotCore m n z = 1
    exact (w1369_dotCore_comm m n z).trans
      (w1369_dotCore_zpowers_eq_one m z n ((w1369_mem_ker m n).mp hn)))

private lemma w1369_formQuot_mk (m : ℕ) (x y : ↥(G6.coreMod m)) :
    w1369_formQuot m (QuotientGroup.mk x) (QuotientGroup.mk y) =
      w1369_dotCore m x y := rfl

private lemma w1369_formQuot_nondegenerate (m : ℕ)
    (q : ↥(G6.coreMod m) ⧸ w1369_ker m)
    (hq : ∀ q' : ↥(G6.coreMod m) ⧸ w1369_ker m,
      w1369_formQuot m q q' = 1) : q = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [QuotientGroup.eq_one_iff, w1369_mem_ker]
  have hx0 : ∀ y : ↥(G6.coreMod m), w1369_dotCore m x y = 1 := by
    intro y
    have h := hq (QuotientGroup.mk y)
    rwa [w1369_formQuot_mk] at h
  by_cases h1 : (x : G6.PermMod m) = 1
  · rw [Subgroup.mem_zpowers_iff]
    exact ⟨0, by rw [zpow_zero]; exact h1.symm⟩
  · by_cases h2 : (x : G6.PermMod m) = G6.allOnes m
    · rw [Subgroup.mem_zpowers_iff]
      exact ⟨1, by rw [zpow_one]; exact h2.symm⟩
    · exfalso
      have hx_ne : (Multiplicative.toAdd (x : G6.PermMod m)) ≠ 0 := by
        intro h
        apply h1
        rw [← ofAdd_toAdd (x : G6.PermMod m), h,
          ofAdd_zero]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx_ne
      have hx_ne' : (Multiplicative.toAdd (x : G6.PermMod m)) ≠
          (fun _ : Fin m => (1 : ZMod 2)) := by
        intro h
        apply h2
        rw [← ofAdd_toAdd (x : G6.PermMod m), h]
        rfl
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hx_ne'
      have hj0 : Multiplicative.toAdd (x : G6.PermMod m) j = 0 := by
        rcases w1369_zmod_two_eq_zero_or_one
          (Multiplicative.toAdd (x : G6.PermMod m) j) with h | h
        · exact h
        · exact absurd h hj
      have hji : i ≠ j := by
        intro hij
        rw [hij, hj0] at hi
        exact hi rfl
      let yfun : Fin m → ZMod 2 := Pi.single i 1 + Pi.single j 1
      have hy_mem : Multiplicative.ofAdd yfun ∈ G6.coreMod m := by
        rw [G6.mem_coreMod]
        simp only [toAdd_ofAdd]
        rw [← dotProduct_one (v := yfun)]
        change (Pi.single i 1 + Pi.single j 1) ⬝ᵥ (1 : Fin m → ZMod 2) = 0
        simp only [add_dotProduct, single_dotProduct, Pi.one_apply, mul_one]
        decide
      let y : ↥(G6.coreMod m) := ⟨Multiplicative.ofAdd yfun, hy_mem⟩
      have hdot : w1369_dotCore m x y =
          Multiplicative.ofAdd (Multiplicative.toAdd (x : G6.PermMod m) i) := by
        rw [w1369_dotCore_apply]
        apply congrArg Multiplicative.ofAdd
        change Multiplicative.toAdd (x : G6.PermMod m) ⬝ᵥ
          (Pi.single i 1 + Pi.single j 1) = Multiplicative.toAdd (x : G6.PermMod m) i
        rw [dotProduct_add, dotProduct_single, dotProduct_single,
          mul_one, mul_one, hj0, add_zero]
      have hne : w1369_dotCore m x y ≠ 1 := by
        rw [hdot]
        intro h
        apply hi
        exact Multiplicative.ofAdd.injective (by simpa using h)
      exact hne (hx0 y)

theorem hasSympForm_of_alternatingNatural {K : Subgroup (MulAut W)} {m : ℕ}
    (h : AlternatingNatural K ⊤ ⊥ m) : HasSympForm K := by
  simp only [AlternatingNatural, FFModel.Realizes, FFModel.RealizesVia] at h
  obtain ⟨π, hπsurj, -, -, -, -, -, -, β, hβsurj, hβker, hβeq⟩ := h
  simp only [FFModel.altDn] at hβeq
  let topEquiv : W ≃* ↥(⊤ : Subgroup W) := (Subgroup.topEquiv (G := W)).symm
  let β' : W →* ↥(G6.coreMod m) ⧸ w1369_ker m := β.comp topEquiv.toMonoidHom
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hβker u).mp hu
    rw [Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hβ'inj : Function.Injective β' := hβinj.comp topEquiv.injective
  have hβ'surj : Function.Surjective β' := hβsurj.comp topEquiv.surjective
  let B : W →* W →* Multiplicative (ZMod 2) :=
    MonoidHom.mk' (fun w => (w1369_formQuot m (β' w)).comp β')
      (by
        intro a b
        ext u
        show w1369_formQuot m (β' (a * b)) (β' u) =
          w1369_formQuot m (β' a) (β' u) * w1369_formQuot m (β' b) (β' u)
        rw [map_mul, map_mul]
        rfl)
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x hx
    have hqx : ∀ q' : ↥(G6.coreMod m) ⧸ w1369_ker m,
        w1369_formQuot m (β' x) q' = 1 := by
      intro q'
      obtain ⟨y, rfl⟩ := hβ'surj q'
      exact hx y
    have hq1 : β' x = 1 := w1369_formQuot_nondegenerate m (β' x) hqx
    exact hβ'inj (by rw [hq1, map_one])
  · intro x
    obtain ⟨mx, hmx⟩ := QuotientGroup.mk_surjective (β' x)
    show w1369_formQuot m (β' x) (β' x) = 1
    rw [← hmx, w1369_formQuot_mk, w1369_dotCore_self]
  · intro k hk x y
    obtain ⟨γ, hγ⟩ := hπsurj ⟨k, hk⟩
    let γa : ↥(alternatingGroup (Fin m)) := γ
    have hk_eq : ((π γ : ↥K) : MulAut W) = k := congrArg Subtype.val hγ
    rw [← hk_eq]
    obtain ⟨mx, hmx⟩ := QuotientGroup.mk_surjective (β' x)
    obtain ⟨my, hmy⟩ := QuotientGroup.mk_surjective (β' y)
    have hmx_mem : G6.permAct m γa.1 (mx : G6.PermMod m) ∈ G6.coreMod m :=
      G6.permAct_mem_coreMod γa.1 mx.2
    have hmy_mem : G6.permAct m γa.1 (my : G6.PermMod m) ∈ G6.coreMod m :=
      G6.permAct_mem_coreMod γa.1 my.2
    have hx' : β' (((π γ : ↥K) : MulAut W) x) = QuotientGroup.mk (s := w1369_ker m)
        ⟨G6.permAct m γa.1 (mx : G6.PermMod m), hmx_mem⟩ := by
      have h := hβeq γ (topEquiv x) mx (Subgroup.mem_top _) hmx_mem hmx.symm
      exact h
    have hy' : β' (((π γ : ↥K) : MulAut W) y) = QuotientGroup.mk (s := w1369_ker m)
        ⟨G6.permAct m γa.1 (my : G6.PermMod m), hmy_mem⟩ := by
      have h := hβeq γ (topEquiv y) my (Subgroup.mem_top _) hmy_mem hmy.symm
      exact h
    show w1369_formQuot m (β' (((π γ : ↥K) : MulAut W) x))
      (β' (((π γ : ↥K) : MulAut W) y)) = w1369_formQuot m (β' x) (β' y)
    rw [hx', hy', ← hmx, ← hmy, w1369_formQuot_mk, w1369_formQuot_mk]
    exact w1369_dotCore_permAct m γa.1 mx my

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

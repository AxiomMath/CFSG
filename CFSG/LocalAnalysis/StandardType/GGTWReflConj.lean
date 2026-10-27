module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nR1_groupEquiv_of_eq {ι : Type*} {M M' : CoxeterMatrix ι} (h : M = M') :
    ∃ φ : M.Group ≃* M'.Group, ∀ i, φ (M.simple i) = M'.simple i := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

theorem ggTW_refl_conj_of_typeA {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 2 ≤ n) {G : Type}
    [Group G] [Finite G] {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {M : CoxeterMatrix Λ} (e : Fin n ≃ Λ)
    (hM : M = (CoxeterMatrix.A n).reindex e) (W : Subgroup (MulAut ↥Bs))
    (f : M.Group ≃* ↥W) (φ : Λ → MulAut ↥Bs) (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (s : MulAut ↥Bs) (hs : s ∈ W)
    (hr : GGIsReflection p s) : ∃ w ∈ W, ∃ i : Λ, s = w * φ i * w⁻¹ := by
  haveI : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  let A : CoxeterMatrix (Fin n) := CoxeterMatrix.A n
  obtain ⟨cA, hcA⟩ := l05nR1_groupEquiv_of_eq (coxeterMatrix_isFiniteType_A_eq n)
  obtain ⟨cM, hcM⟩ := l05nR1_groupEquiv_of_eq hM.symm
  let eA : Equiv.Perm (Fin (n + 1)) ≃* A.Group := (typeAWeylEquiv n).trans cA
  let Ê : Equiv.Perm (Fin (n + 1)) ≃* ↥W :=
    (eA.trans ((CoxeterMatrix.reindexGroupEquiv A e).symm.trans cM)).trans f
  let E : Equiv.Perm (Fin (n + 1)) →* MulAut ↥Bs := W.subtype.comp Ê.toMonoidHom
  have hEsimp : ∀ k : Fin n, E (Equiv.swap k.castSucc k.succ) = φ (e k) := by
    intro k
    have h1 : eA (Equiv.swap k.castSucc k.succ) = A.simple k := by
      change cA ((typeAWeylEquiv n) (Equiv.swap k.castSucc k.succ)) = A.simple k
      rw [typeAWeylEquiv_swap n k]
      exact hcA k
    have h2 : ((CoxeterMatrix.reindexGroupEquiv A e).symm) (A.simple k) =
        (A.reindex e).simple (e k) := by
      have h := CoxeterMatrix.reindexGroupEquiv_apply_simple A e (e k)
      rw [Equiv.symm_apply_apply] at h
      exact (MulEquiv.symm_apply_eq _).mpr h.symm
    have h3 : cM ((A.reindex e).simple (e k)) = M.simple (e k) := hcM (e k)
    have hÊ : Ê (Equiv.swap k.castSucc k.succ) = f (M.simple (e k)) := by
      simp only [Ê, MulEquiv.trans_apply]
      rw [h1, h2, h3]
    change ((Ê (Equiv.swap k.castSucc k.succ) : ↥W) : MulAut ↥Bs) = φ (e k)
    rw [hÊ]
    exact hf (e k)
  let k0 : Fin n := ⟨0, by omega⟩
  have hbase_hab : k0.castSucc ≠ k0.succ := ne_of_lt (Fin.castSucc_lt_succ (i := k0))
  have hbase : GGIsReflection p (E (Equiv.swap k0.castSucc k0.succ)) := by
    rw [hEsimp k0]
    exact hrefl (e k0)
  have hinj : Function.Injective E := by
    intro x y hxy
    apply Ê.injective
    apply Subtype.ext
    exact hxy
  have hsw : ∀ x y : Fin (n + 1), x ≠ y →
      GGIsReflection p (E (Equiv.swap x y)) := fun x y hxy =>
    ggIsReflection_swap_of_swap E hbase_hab hbase hxy
  let π : Equiv.Perm (Fin (n + 1)) := Ê.symm ⟨s, hs⟩
  have hEπ : E π = s := by
    change ((Ê π : ↥W) : MulAut ↥Bs) = s
    rw [show Ê π = ⟨s, hs⟩ from MulEquiv.apply_symm_apply Ê ⟨s, hs⟩]
  have hπswap : π.IsSwap := by
    refine isSwap_of_ggIsReflection hp2 hBs E hinj hsw (π := π) ?_
    rw [hEπ]
    exact hr
  obtain ⟨a, b, hab, hπab⟩ := hπswap
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hbase_hab hab)
  refine ⟨((Ê c : ↥W) : MulAut ↥Bs), (Ê c).2, e k0, ?_⟩
  calc
    s = E π := hEπ.symm
    _ = E (Equiv.swap a b) := by rw [hπab]
    _ = E (c * Equiv.swap k0.castSucc k0.succ * c⁻¹) := by rw [← hc]
    _ = E c * E (Equiv.swap k0.castSucc k0.succ) * (E c)⁻¹ := by
          simp only [map_mul, map_inv]
    _ = ((Ê c : ↥W) : MulAut ↥Bs) * φ (e k0) * (((Ê c : ↥W) : MulAut ↥Bs))⁻¹ := by
          rw [hEsimp k0]
          rfl

end CFSG.StandardType

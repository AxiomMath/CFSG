module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthNormal
public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulTypeA

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem owTA_linWeyl_of_typeA {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (c : ZMod p)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ} (hn : 3 ≤ n)
    (h : Fin n → U) (α : Fin n → U →ₗ[ZMod p] ZMod p)
    (hP : ∀ i j, α i (h j) = (CartanMatrix.A n i j : ZMod p))
    (s : Fin n → U ≃ₗ[ZMod p] U) (hs : ∀ i v, s i v = v - α i v • h i)
    (hs_mem : ∀ i, s i ∈ ClassRefl p Q c)
    (hgen : closure (Set.range s) = A) : LinWeyl p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hM : CoxeterMatrix.A n = (CoxeterMatrix.A n).reindex (Equiv.refl (Fin n)) := by
    ext i j; simp [CoxeterMatrix.reindex_apply]
  obtain ⟨f, hf⟩ := ggCoxeterIso_of_typeA_odd (e := Equiv.refl (Fin n))
    (M := CoxeterMatrix.A n) hM hn hp2 (C := CartanMatrix.A n)
    (ggIntCartan_A n) h α hP s hs
  refine ⟨Fin n, CoxeterMatrix.A n, ?_, f.trans (MulEquiv.subgroupCongr hgen), ?_⟩
  · exact Or.inl ⟨n, Equiv.refl (Fin n), by omega, Or.inl hM⟩
  · intro i
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      show (f ((CoxeterMatrix.A n).simple i) : U ≃ₗ[ZMod p] U) = s i from hf i]
    exact (hs_mem i).1

end CFSG.StandardType.ZS

end

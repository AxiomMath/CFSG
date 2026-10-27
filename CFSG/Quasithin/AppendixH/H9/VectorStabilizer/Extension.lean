module

public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Model

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

open CFSG.Quasithin CFSG.Open

variable {m : ℕ}

private theorem sq_eq_one_ofAdd (r : Multiplicative (Fin m → ZMod 2)) : r ^ 2 = 1 := by
  rw [pow_two]
  apply Multiplicative.ext
  rw [toAdd_mul, toAdd_one]
  funext i
  exact CharTwo.add_self_eq_zero _

private theorem isExtOf_map {G H Q : Type*} [Group G] [Group H] [Group Q]
    (φ : G →* H) (hφ : Function.Injective φ) (S N : Subgroup G) (hN : N ≤ S)
    (f : ↥S →* Q) (hf : Function.Surjective f) (hker : f.ker = N.subgroupOf S) :
    IsExtOf (S.map φ) (N.map φ) Q := by
  refine ⟨Subgroup.map_mono hN, ?_⟩
  let e := Subgroup.equivMapOfInjective S φ hφ
  refine ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
  change f (e.symm x) = 1 ↔ (x : H) ∈ N.map φ
  rw [Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨((e.symm x : ↥S) : G), ?_, ?_⟩
    · have hmem : e.symm x ∈ N.subgroupOf S := by
        rw [← hker, MonoidHom.mem_ker]
        exact h
      simpa [Subgroup.mem_subgroupOf] using hmem
    · rw [← Subgroup.coe_equivMapOfInjective_apply S φ hφ (e.symm x), e.apply_symm_apply]
  · rintro ⟨n, hn, hnφx⟩
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    have hxeq : ((e.symm x : ↥S) : G) = n := by
      apply hφ
      rw [hnφx, ← Subgroup.coe_equivMapOfInjective_apply S φ hφ (e.symm x), e.apply_symm_apply]
    rw [hxeq]
    exact hn

theorem exists_elemAbelian_isExtOf (m : ℕ) :
    ∃ E : Subgroup (MulAut (PairN (m + 1))), CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ m ∧
      IsExtOf (Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0))) E
        (GL (Fin m) (ZMod 2)) := by
  let f : Multiplicative (Fin m → ZMod 2) →* MulAut (PairN (m + 1)) :=
    (pairActN (m + 1)).comp (trHom m)
  have hf : Function.Injective f :=
    (pairActN_injective (n := m + 1)).comp (trHom_injective m)
  have hN : (trHom m).range ≤ stabGL m := by
    rintro - ⟨r, rfl⟩
    exact trHom_mem r
  have hker : (blockHom m).ker = ((trHom m).range).subgroupOf (stabGL m) := by
    ext A
    rw [mem_ker_blockHom_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    exact exists_congr fun r => eq_comm
  refine ⟨f.range, ?_, ?_, ?_⟩
  · change IsMulCommutative f.range ∧ ∀ x ∈ f.range, x ^ 2 = 1
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← map_pow, sq_eq_one_ofAdd, map_one]
  · have h1 : Nat.card (Multiplicative (Fin m → ZMod 2)) = Nat.card f.range :=
      Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    calc Nat.card f.range = Nat.card (Multiplicative (Fin m → ZMod 2)) := h1.symm
      _ = Nat.card (Fin m → ZMod 2) :=
        Nat.card_congr (Multiplicative.toAdd (α := Fin m → ZMod 2))
      _ = 2 ^ m := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · rw [Lg_inf_centSub_eq_map m, MonoidHom.range_comp]
    exact isExtOf_map (pairActN (m + 1)) (pairActN_injective (n := m + 1)) (stabGL m)
      (trHom m).range hN (blockHom m) (blockHom_surjective m) hker

end CFSG.ASVolI.ChH.VectorStabilizer

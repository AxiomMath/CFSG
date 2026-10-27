module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

namespace CFSG
end CFSG
open CFSG

/-!
# Subnormal `p`-subgroups lie in the `p`-core

This is the standard subnormal-chain extension of the defining maximality of
`O_p(B)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A subnormal `p`-subgroup of `B` lies in `O_p(B)`. -/
public theorem le_qCoreOf_of_isSubnormal_isPGroup
    {G : Type u} [Group G] [Finite G]
    (B S : Subgroup G) (p : ℕ)
    (hSB : S ≤ B) (hS : (S.subgroupOf B).IsSubnormal) (hSp : IsPGroup p S) :
    S ≤ qCoreOf B p := by
  rcases (Subgroup.IsSubnormal.isSubnormal_iff (G := ↑B) (H := S.subgroupOf B)).1 hS with
    ⟨n, f, hmono, hnorm, hf0, hfn⟩
  have hmain : ∀ i : ℕ, i ≤ n → S ≤ qCoreOf ((f i).map B.subtype) p := by
    intro i hi
    induction i with
    | zero =>
      have hK0 : (f 0).map B.subtype = S := by
        rw [hf0]
        exact Subgroup.map_subgroupOf_eq_of_le hSB
      have hSleK : S ≤ (f 0).map B.subtype := by rw [hK0]
      have hSnorm : IsNormalIn S ((f 0).map B.subtype) := by
        rw [hK0]
        refine ⟨le_rfl, ?_⟩
        intro a ha x hx
        exact S.mul_mem (S.mul_mem ha hx) (S.inv_mem ha)
      exact le_qCoreOf_of_normal_isPGroup ((f 0).map B.subtype) S p hSleK (by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSleK]
        exact le_normalizer_of_isNormalIn hSnorm) hSp
    | succ i ih =>
      have hKi : IsNormalIn ((f i).map B.subtype) ((f (i + 1)).map B.subtype) := by
        refine ⟨Subgroup.map_mono (f := B.subtype) (hmono (Nat.le_succ i)), ?_⟩
        intro b hb x hx
        rcases (Subgroup.mem_map).1 hx with ⟨x0, hx0, rfl⟩
        rcases (Subgroup.mem_map).1 hb with ⟨b0, hb0, rfl⟩
        have hconj : b0 * x0 * b0⁻¹ ∈ f i :=
          (Subgroup.normal_subgroupOf_iff (hmono (Nat.le_succ i))).mp (hnorm i)
            x0 b0 hx0 hb0
        exact Subgroup.mem_map.mpr ⟨b0 * x0 * b0⁻¹, hconj, by simp [mul_assoc]⟩
      have hQleK : S ≤ qCoreOf ((f i).map B.subtype) p :=
        ih (Nat.le_of_succ_le hi)
      have hQleN : qCoreOf ((f i).map B.subtype) p ≤
          qCoreOf ((f (i + 1)).map B.subtype) p :=
        qCoreOf_le_qCoreOf_of_isNormalIn
          ((f i).map B.subtype) ((f (i + 1)).map B.subtype) p hKi
      exact hQleK.trans hQleN
  have h := hmain n le_rfl
  have htop : (⊤ : Subgroup (↑B)).map B.subtype = B := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := B))
  rw [hfn] at h
  simpa [htop] using h

end CFSG.GorensteinWalter

module

public import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.CyclicPreimageSylow

variable {G H : Type*} [Group G] [Group H] {p : ℕ}

theorem exists_sylow_of_kernel_maximal (f : G →* H) (Q : Subgroup G)
    (hQker : Q ≤ f.ker)
    (hmax : ∀ B : Subgroup G, B ≤ f.ker → IsPGroup p B → B ≤ Q)
    (A : Subgroup G) (hA : IsPGroup p A) (hQA : Q ≤ A) (x : G) (hx : x ∈ A) :
    ∃ R : Sylow p ((Subgroup.zpowers (f x)).comap f),
      SylowPreimageNormalizer.ambient f (Subgroup.zpowers (f x)) R = Q ⊔ Subgroup.zpowers x := by
  let K := (Subgroup.zpowers (f x)).comap f
  let J := Q ⊔ Subgroup.zpowers x
  have hJA : J ≤ A := sup_le hQA (Subgroup.zpowers_le.mpr hx)
  have hJp : IsPGroup p J := hA.to_le hJA
  have hJK : J ≤ K := by
    apply sup_le
    · intro q hq
      change f q ∈ Subgroup.zpowers (f x)
      rw [MonoidHom.mem_ker.mp (hQker hq)]
      exact Subgroup.one_mem _
    · apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_zpowers (f x)
  have hJ'p : IsPGroup p (J.subgroupOf K) := hJp.of_injective
    (Subgroup.subgroupOfEquivOfLe hJK).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hJK).injective
  obtain ⟨R, hJR⟩ := hJ'p.exists_le_sylow
  let B := (R : Subgroup K).map K.subtype
  have hJB : J ≤ B := by
    intro j hj
    exact ⟨⟨j, hJK hj⟩, hJR hj, rfl⟩
  have hBK : B ≤ K := by
    rintro b ⟨r, hr, rfl⟩
    exact r.property
  have hBp : IsPGroup p B := R.isPGroup'.map K.subtype
  have hBker : B ⊓ f.ker ≤ Q := hmax (B ⊓ f.ker) inf_le_right hBp.to_inf_left
  refine ⟨R, le_antisymm ?_ hJB⟩
  intro b hb
  have hbK : f b ∈ Subgroup.zpowers (f x) := hBK hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbK
  have hxJ : x ∈ J := (show Subgroup.zpowers x ≤ J from le_sup_right) (Subgroup.mem_zpowers x)
  have hpowB : x ^ k ∈ B := B.zpow_mem (hJB hxJ) k
  have hdiffB : b * (x ^ k)⁻¹ ∈ B := B.mul_mem hb (B.inv_mem hpowB)
  have hdiffker : b * (x ^ k)⁻¹ ∈ f.ker := by
    change f (b * (x ^ k)⁻¹) = 1
    rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  have hdiffQ := hBker ⟨hdiffB, hdiffker⟩
  have hdiffJ : b * (x ^ k)⁻¹ ∈ J := (show Q ≤ J from le_sup_left) hdiffQ
  simpa only [inv_mul_cancel_right] using J.mul_mem hdiffJ (J.zpow_mem hxJ k)

end FiveTransitive.CyclicPreimageSylow

end CFSG

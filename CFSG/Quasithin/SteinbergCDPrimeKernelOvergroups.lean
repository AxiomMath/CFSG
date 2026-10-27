module

public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup

theorem normal_prime_kernel_overgroups_characteristic_prime {p : ℕ} (hp : p.Prime) {H : Type*}
    [Group H] [Finite H] (L : Subgroup H) [L.Normal] (hHL : IsPGroup p (H ⧸ L))
    (N : Subgroup H) [N.Normal] (hNp : IsPGroup p N)
    (hCL : L ⊓ centralizer (N : Set H) ≤ N) :
    ∀ V : Subgroup H, N ≤ V →
      ((V ⊓ centralizer (N : Set H)).subgroupOf V).Normal ∧
        IsPGroup p (V ⊓ centralizer (N : Set H) : Subgroup H) ∧
        V ⊓ centralizer (N : Set H) ≤ inSubgroup (pCore p) V ∧
        V ⊓ centralizer (inSubgroup (pCore p) V : Set H) ≤ inSubgroup (pCore p) V ∧
        IsCharacteristicP p V ∧ generalizedFitting V = pCore p V := by
  have : Fact p.Prime := ⟨hp⟩
  intro V hNV
  set C := V ⊓ centralizer (N : Set H) with hC
  have hCn : (C.subgroupOf V).Normal := by
    refine ⟨fun x hx v => ?_⟩
    rw [mem_subgroupOf, Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxV, hxN⟩ := hx
    refine ⟨V.mul_mem (V.mul_mem v.2 hxV) (V.inv_mem v.2), ?_⟩
    rw [mem_centralizer_iff]
    intro n hn
    have hn' : (v : H)⁻¹ * n * v ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem n hn (v : H)⁻¹
    have h1 := mem_centralizer_iff.mp hxN _ hn'
    simp only [coe_mul, coe_inv]
    calc n * ((v : H) * x * (v : H)⁻¹) = (v : H) * ((v : H)⁻¹ * n * v * x) * (v : H)⁻¹ := by
          group
      _ = (v : H) * (x * ((v : H)⁻¹ * n * v)) * (v : H)⁻¹ := by rw [h1]
      _ = (v : H) * x * (v : H)⁻¹ * n := by group
  have hCp : IsPGroup p C := by
    intro c
    obtain ⟨k, hk⟩ := hHL (QuotientGroup.mk' L c)
    have hcL : (c : H) ^ p ^ k ∈ L := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
      exact hk
    have hcC : (c : H) ^ p ^ k ∈ C := C.pow_mem c.2 _
    have hcN : (c : H) ^ p ^ k ∈ N := hCL ⟨hcL, hcC.2⟩
    obtain ⟨j, hj⟩ := hNp ⟨_, hcN⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have hj' : ((c : H) ^ p ^ k) ^ p ^ j = 1 := congrArg Subtype.val hj
    rw [SubmonoidClass.coe_pow, pow_add, pow_mul]
    exact hj'
  have hCV : C ≤ V := inf_le_left
  have hCO : C.subgroupOf V ≤ pCore p V :=
    le_sSup ⟨hCn, hCp.of_equiv (Subgroup.subgroupOfEquivOfLe hCV).symm⟩
  have hNO : N.subgroupOf V ≤ pCore p V :=
    le_sSup ⟨inferInstance, hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNV).symm⟩
  have hCO' : C ≤ inSubgroup (pCore p) V := fun x hx => ⟨⟨x, hCV hx⟩, hCO hx, rfl⟩
  have hNO' : N ≤ inSubgroup (pCore p) V := fun x hx => ⟨⟨x, hNV hx⟩, hNO hx, rfl⟩
  have hCOO : V ⊓ centralizer (inSubgroup (pCore p) V : Set H) ≤ inSubgroup (pCore p) V :=
    (inf_le_inf_left V (centralizer_le hNO')).trans hCO'
  have hchar : IsCharacteristicP p V := by
    intro x hx
    have hx' : (x : H) ∈ V ⊓ centralizer (inSubgroup (pCore p) V : Set H) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx y hy)
    obtain ⟨y, hy, hyx⟩ := hCOO hx'
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  exact ⟨hCn, hCp, hCO', hCOO, hchar,
    (isCharacteristicP_iff_generalizedFitting_eq_pCore V p).mp hchar⟩

end CFSG.Quasithin.SteinbergCD

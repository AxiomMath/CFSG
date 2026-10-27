module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Conj
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L511.KRadical

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T61

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup {H A : Subgroup G} (hAH : A ≤ Subgroup.normalizer (H : Set G))
    {x : G} (hx : x ∈ H ⊔ A) : ∃ h ∈ H, ∃ a ∈ A, x = h * a := by
  have hx' : x ∈ ((H ⊔ A : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H A hAH] at hx'
  obtain ⟨h, hh, a, ha, rfl⟩ := hx'
  exact ⟨h, hh, a, ha, rfl⟩

theorem commutator_mem_of_mem_sup {H A : Subgroup G} (hA : IsMulCommutative A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) {x y : G} (hx : x ∈ H ⊔ A) (hy : y ∈ H ⊔ A) :
    x * y * x⁻¹ * y⁻¹ ∈ H := by
  obtain ⟨h, hh, a, ha, rfl⟩ := exists_mul_of_mem_sup hAH hx
  obtain ⟨h', hh', a', ha', rfl⟩ := exists_mul_of_mem_sup hAH hy
  have hc : Commute a a' := by
    have := hA
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨a', ha'⟩)
  have hu : a * h' * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hAH ha) h').mp hh'
  have hv : a' * h * a'⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hAH ha') h).mp hh
  have e1 : a' * a⁻¹ = a⁻¹ * a' := hc.inv_left.eq.symm
  have key : h * a * (h' * a') * (h * a)⁻¹ * (h' * a')⁻¹ =
      (h * (a * h' * a⁻¹)) * (h' * (a' * h * a'⁻¹))⁻¹ := by
    calc h * a * (h' * a') * (h * a)⁻¹ * (h' * a')⁻¹
        = h * a * h' * (a' * a⁻¹) * h⁻¹ * a'⁻¹ * h'⁻¹ := by group
      _ = h * a * h' * (a⁻¹ * a') * h⁻¹ * a'⁻¹ * h'⁻¹ := by rw [e1]
      _ = (h * (a * h' * a⁻¹)) * (h' * (a' * h * a'⁻¹))⁻¹ := by group
  rw [key]
  exact mul_mem (mul_mem hh hu) (inv_mem (mul_mem hh' hv))

theorem le_of_le_sup_of_isSimpleGroup {H A L : Subgroup G} (hA : IsMulCommutative A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) (hL : L ≤ H ⊔ A) (hLs : IsSimpleGroup L)
    (hnc : ¬ IsMulCommutative L) : L ≤ H := by
  have hnorm : ((L ⊓ H).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro x l hx hl
    obtain ⟨hxL, hxH⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hl hxL) (inv_mem hl), ?_⟩
    have hl' : l ∈ Subgroup.normalizer (H : Set G) :=
      (sup_le Subgroup.le_normalizer hAH) (hL hl)
    exact (Subgroup.mem_normalizer_iff.mp hl' x).mp hxH
  have := hLs
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ H).subgroupOf L) with h0 | h1
  · exfalso
    refine hnc (isMulCommutative_iff.mpr fun x y => ?_)
    have hc : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ L ⊓ H :=
      Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem x.2 y.2) (inv_mem x.2)) (inv_mem y.2),
        commutator_mem_of_mem_sup hA hAH (hL x.2) (hL y.2)⟩
    have hmem : (⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹, (Subgroup.mem_inf.mp hc).1⟩ : L) ∈
        (L ⊓ H).subgroupOf L := hc
    rw [h0, Subgroup.mem_bot] at hmem
    have h2 : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val hmem
    have h3 : ⁅(x : G), (y : G)⁆ = 1 := by rw [commutatorElement_def]; exact h2
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h3)
  · intro x hx
    have hmem : (⟨x, hx⟩ : L) ∈ (L ⊓ H).subgroupOf L := by rw [h1]; trivial
    exact (Subgroup.mem_inf.mp hmem).2

theorem mem_lcal_of_isWreath {H A L N C : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) (hW : IsWreath (H ⊔ A) L A N C)
    (hLs : IsSimpleGroup L) (hnc : ¬ IsMulCommutative L) : L ∈ lcal H := by
  have hWH : H ⊔ A ≤ Subgroup.normalizer (H : Set G) := sup_le Subgroup.le_normalizer hAH
  have hLH : L ≤ H := le_of_le_sup_of_isSimpleGroup hW.isMulCommutative hAH hW.H_le hLs hnc
  have hNH : orbitClosure L (H ⊔ A) ≤ H := orbitClosure_le fun g hg => by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hWH hg) x).mp (hLH hx)
  have hWN : H ⊔ A ≤ Subgroup.normalizer ((orbitClosure L (H ⊔ A) : Subgroup G) : Set G) :=
    fun g hg => L514.mem_normalizer_orbitClosure hg
  have hLmem : L ∈ {K | ∃ g ∈ H ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} :=
    ⟨1, one_mem _, (L69.map_conj_one L).symm⟩
  have hNL : orbitClosure L (H ⊔ A) ≤ Subgroup.normalizer (L : Set G) :=
    hW.isDirectProduct.le_normalizer hLmem
  have hLN : L ≤ orbitClosure L (H ⊔ A) := le_orbitClosure L (H ⊔ A)
  refine mem_lcal_iff.mpr ⟨hLH, ?_, hLs, hnc⟩
  refine L511.isSubnormal_subgroupOf_of_normal_chain hLN hNH ?_ ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr (le_sup_left.trans hWN)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T61

module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylStruct
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTriality

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma triD4Line_conj_range_normal {n : ℕ} (K : Type) [Field K] :
    ((MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)).range).Normal := by
  refine Subgroup.Normal.mk ?_
  rintro _ ⟨a, rfl⟩ g
  exact ⟨g a, by ext x; simp [MulAut.mul_apply, MulAut.conj_apply]⟩

private lemma triD4Line_conj_injective {n : ℕ} (K : Type) [Field K]
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥) :
    Function.Injective (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) := by
  intro x y hxy
  have h : ∀ z, x * z * x⁻¹ = y * z * y⁻¹ := fun z => by
    have := congrArg (fun e : MulAut (GGTriD4R n K) => e z) hxy
    simpa [MulAut.conj_apply] using this
  have hcomm : ∀ z, z * (y⁻¹ * x) = (y⁻¹ * x) * z := by
    intro z
    have hz := h z
    calc z * (y⁻¹ * x) = y⁻¹ * (y * z * y⁻¹) * x := by group
      _ = y⁻¹ * (x * z * x⁻¹) * x := by rw [← hz]
      _ = (y⁻¹ * x) * z := by group
  have hmem : y⁻¹ * x ∈ Subgroup.center (GGTriD4R n K) := by
    rw [Subgroup.mem_center_iff]
    exact hcomm
  have h1 : y⁻¹ * x = 1 := by
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  calc x = y * (y⁻¹ * x) := by group
    _ = y := by rw [h1, mul_one]

private lemma triD4Line_outer_aux {n : ℕ} (K : Type) [Field K]
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥)
    (N : Subgroup (MulAut (GGTriD4R n K))) [N.Normal]
    (hN : N = (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)).range)
    (z₀ : GGTriD4R n K) (A : Subgroup (MulAut (GGTriD4R n K)))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hz : MulAut.conj z₀ ∈ A)
    (f : MulAut (GGTriD4R n K)) (hfA : f ∈ A)
    (β : MulAut (GGTriD4R n K)) (hβz : β z₀ = z₀)
    (hqf : (QuotientGroup.mk' N) f = (QuotientGroup.mk' N) β) :
    ∃ x : GGTriD4R n K, x ∈ Subgroup.centralizer {z₀} ∧ f = MulAut.conj x * β := by
  obtain ⟨x, hx⟩ : ∃ x, MulAut.conj x = f / β := by
    have hdiv : f / β ∈ N := QuotientGroup.eq_iff_div_mem.mp hqf
    rw [hN] at hdiv
    exact MonoidHom.mem_range.mp hdiv
  have hf : f = MulAut.conj x * β := by
    rw [hx, div_mul_cancel]
  have hfix : f * MulAut.conj z₀ * f⁻¹ = MulAut.conj z₀ := by
    have hcomm : f * MulAut.conj z₀ = MulAut.conj z₀ * f :=
      hAc f hfA (MulAut.conj z₀) hz
    calc f * MulAut.conj z₀ * f⁻¹ = (MulAut.conj z₀ * f) * f⁻¹ := by rw [hcomm]
      _ = MulAut.conj z₀ := by group
  have hβfix : β * MulAut.conj z₀ * β⁻¹ = MulAut.conj z₀ := by
    ext w; simp [MulAut.conj_apply, hβz]
  have hβ : MulAut.conj x * MulAut.conj z₀ * (MulAut.conj x)⁻¹ = MulAut.conj z₀ := by
    have h1 : MulAut.conj x * β * MulAut.conj z₀ * (MulAut.conj x * β)⁻¹ =
        MulAut.conj z₀ := by
      simpa [hf] using hfix
    calc MulAut.conj x * MulAut.conj z₀ * (MulAut.conj x)⁻¹
        = MulAut.conj x * (β * MulAut.conj z₀ * β⁻¹) * (MulAut.conj x)⁻¹ := by
          rw [hβfix]
      _ = MulAut.conj x * β * MulAut.conj z₀ * (MulAut.conj x * β)⁻¹ := by group
      _ = MulAut.conj z₀ := h1
  have hconj : MulAut.conj (x * z₀ * x⁻¹) = MulAut.conj z₀ := by
    rw [show MulAut.conj (x * z₀ * x⁻¹)
          = MulAut.conj x * MulAut.conj z₀ * (MulAut.conj x)⁻¹ by simp [map_mul]]
    exact hβ
  have hx_eq : x * z₀ * x⁻¹ = z₀ := triD4Line_conj_injective K hZ hconj
  refine ⟨x, ?_, hf⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * z₀ = (x * z₀ * x⁻¹) * x := by group
    _ = z₀ * x := by rw [hx_eq]

theorem triD4Line_outer_form
    {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (k : Type) [Field k] [Algebra k K] (D : TriD4LineKGXData n K k)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hz : MulAut.conj D.z₀ ∈ A) (f : MulAut (GGTriD4R n K)) (hfA : f ∈ A)
    (hfo : f ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)))
    (hf3 : f ^ 3 = 1) :
    ∃ x : GGTriD4R n K, x ∈ Subgroup.centralizer {D.z₀} ∧
      (f = MulAut.conj x * D.α ∨ f = MulAut.conj x * D.α⁻¹) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := triD4Line_center_bot hn K hK
  obtain ⟨φ₀, hφ₀⟩ := ggOutCyclic_triD4 hn K hK
  set N : Subgroup (MulAut (GGTriD4R n K)) :=
    (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)).range with hN
  haveI hNn : N.Normal := hN ▸ triD4Line_conj_range_normal K
  let q : MulAut (GGTriD4R n K) →* MulAut (GGTriD4R n K) ⧸ N := QuotientGroup.mk' N
  have hgen : ∀ x : MulAut (GGTriD4R n K) ⧸ N, x ∈ Subgroup.zpowers (q φ₀) := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hmem : α ∈ N ⊔ Subgroup.zpowers φ₀ := by
      rw [hN]
      exact hφ₀ α
    obtain ⟨y, hy, z, hz', hyz⟩ := (Subgroup.mem_sup_of_normal_left).mp hmem
    have hy1 : q y = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc (q φ₀) ^ k = q (φ₀ ^ k) := (map_zpow q φ₀ k).symm
      _ = q z := by rw [hk]
      _ = q (y * z) := by rw [map_mul, hy1, one_mul]
      _ = q α := by rw [hyz]
  haveI hcyc : IsCyclic (MulAut (GGTriD4R n K) ⧸ N) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨q φ₀, (Subgroup.eq_top_iff' _).mpr hgen⟩
  have hf3q : q f ^ 3 = 1 := by rw [← map_pow, hf3, map_one]
  have hα3 : D.α ^ 3 = 1 := by rw [← D.orderOf_α]; exact pow_orderOf_eq_one D.α
  have hα3q : q D.α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hfq_ne : q f ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN] at h
    exact hfo (MonoidHom.mem_range.mp h)
  have hαq_ne : q D.α ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN] at h
    exact D.α_outer (MonoidHom.mem_range.mp h)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hof : orderOf (q f) = 3 := orderOf_eq_prime hf3q hfq_ne
  have hoa : orderOf (q D.α) = 3 := orderOf_eq_prime hα3q hαq_ne
  haveI hfinf : Finite (Subgroup.zpowers (q f)) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hf3q⟩)
  haveI hfina : Finite (Subgroup.zpowers (q D.α)) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hα3q⟩)
  have hcardf : Nat.card (Subgroup.zpowers (q f)) = 3 := by rw [Nat.card_zpowers, hof]
  have hcarda : Nat.card (Subgroup.zpowers (q D.α)) = 3 := by rw [Nat.card_zpowers, hoa]
  have hsub : Subgroup.zpowers (q D.α) = Subgroup.zpowers (q f) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, hcarda, hcardf]
  have hmem : q f ∈ Subgroup.zpowers (q D.α) := by
    rw [hsub]; exact Subgroup.mem_zpowers (q f)
  obtain ⟨z, hzpow⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hz3 : q D.α ^ z = q D.α ^ (z % 3) := zpow_eq_zpow_emod z hα3q
  have hrem_ne : z % 3 ≠ 0 := by
    intro h0
    have : q f = 1 := by rw [← hzpow, hz3, h0, zpow_zero]
    exact hfq_ne this
  have hrem : z % 3 = 1 ∨ z % 3 = 2 := by
    have hlt : z % 3 < 3 := Int.emod_lt_of_pos z (by norm_num)
    have hnn : 0 ≤ z % 3 := Int.emod_nonneg z (by norm_num)
    omega
  have hα_inv_z : D.α⁻¹ D.z₀ = D.z₀ := by
    conv_lhs => rw [← D.α_z₀]
    exact MulAut.inv_apply_self (GGTriD4R n K) D.α D.z₀
  have hα2 : D.α ^ 2 = D.α⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc D.α * D.α ^ 2 = D.α ^ 3 := by group
      _ = 1 := hα3
  rcases hrem with h1 | h2
  · have hqf : (QuotientGroup.mk' N) f = (QuotientGroup.mk' N) D.α := by
      change q f = q D.α
      rw [← hzpow, hz3, h1, zpow_one]
    obtain ⟨x, hxcent, hxf⟩ :=
      triD4Line_outer_aux K hZ N hN D.z₀ A hAc hz f hfA D.α D.α_z₀ hqf
    exact ⟨x, hxcent, Or.inl hxf⟩
  · have hqf2 : (QuotientGroup.mk' N) f = (QuotientGroup.mk' N) (D.α ^ 2) := by
      change q f = q (D.α ^ 2)
      rw [← hzpow, hz3, h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
        zpow_natCast, ← map_pow]
    have hqf2' : (QuotientGroup.mk' N) f = (QuotientGroup.mk' N) D.α⁻¹ := by
      rw [hα2] at hqf2
      exact hqf2
    obtain ⟨x, hxcent, hxf⟩ :=
      triD4Line_outer_aux K hZ N hN D.z₀ A hAc hz f hfA D.α⁻¹ hα_inv_z hqf2'
    exact ⟨x, hxcent, Or.inr hxf⟩

end CFSG.StandardType

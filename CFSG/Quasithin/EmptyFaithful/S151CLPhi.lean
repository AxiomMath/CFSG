module

public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem exists_inner_central_element {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hTS : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G))
    (hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G))
    (hOut : ∀ α : MulAut ↥L,
      α ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)
    (hnab : ∃ a ∈ s1516 T Z₁, ∃ b ∈ s1516 T Z₁, a * b ≠ b * a) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧
      ∃ l ∈ L, ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hc.ctx.qtfe
  set S := s1516 T Z₁ with hS
  have hST : S ≤ T := s1516_le T Z₁
  have hT2 : IsPGroup 2 T := hq.sylow.1
  have hS2 : IsPGroup 2 S := hT2.to_le hST
  let ρ : ↥S →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hSN)
  have hρ : ∀ (s : ↥S) (x : ↥L), ((ρ s x : ↥L) : G) = (s : G) * (x : G) * (s : G)⁻¹ := fun s x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨(s : G), hSN s.2⟩ x
  let q : ↥S →* MulAut ↥L ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp ρ
  have hq2 : ∀ s : ↥S, q s ^ 2 = 1 := fun s => by
    have h := hOut (ρ s)
    change (QuotientGroup.mk (ρ s) : MulAut ↥L ⧸
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L) ^ 2 = 1
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 h
  let f : ↥S →* ↥q.range := q.rangeRestrict
  have hfpow : ∀ a : ↥q.range, a ^ 2 = 1 := by
    rintro ⟨_, ⟨s, rfl⟩⟩
    exact Subtype.ext (hq2 s)
  have hfcomm : ∀ a b : ↥q.range, a * b = b * a := by
    intro a b
    have h1 : a * b = (a * b)⁻¹ := by
      have := hfpow (a * b)
      rw [pow_two] at this
      exact eq_inv_of_mul_eq_one_left this
    have h2 : a⁻¹ = a := by
      have := hfpow a
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_right this
    have h3 : b⁻¹ = b := by
      have := hfpow b
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_right this
    rw [h1, mul_inv_rev, h2, h3]
  have hΦker : frattini ↥S ≤ f.ker :=
    CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 2) f hfcomm hfpow
  have hΦne : frattiniIn S ≠ ⊥ := by
    intro hΦ
    obtain ⟨⟨hcomm⟩, -⟩ := isElemAbelian_of_frattiniIn_eq_bot (p := 2) hS2 hΦ
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact hab (congrArg Subtype.val (hcomm.1 ⟨a, ha⟩ ⟨b, hb⟩))
  have hΦT : frattiniIn S ≤ T := by
    rintro _ ⟨y, -, rfl⟩
    exact hST y.2
  have hTΦ : T ≤ Subgroup.normalizer (frattiniIn S : Set G) :=
    hTS.trans (normalizer_le_normalizer_map_of_characteristic (H := S) (frattini S))
  obtain ⟨z, hzΦ, hz1, hzZ⟩ :=
    exists_ne_one_mem_omegaOneCenter_of_normalized hT2 hΦT hΦne hTΦ
  refine ⟨z, hzZ, hz1, ?_⟩
  obtain ⟨y, hy, hyz⟩ := hzΦ
  have hyker : f y = 1 := hΦker hy
  have hqy : q y = 1 := congrArg Subtype.val hyker
  have hinner : ρ y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
    (QuotientGroup.eq_one_iff _).1 hqy
  obtain ⟨g, hg⟩ := hinner
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hzZ
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz2)
  refine ⟨((g⁻¹ : ↥L) : G), (g⁻¹ : ↥L).2, fun x hx => ?_⟩
  have hyz' : (y : G) = z := hyz
  have h1 := hρ y ⟨x, hx⟩
  have h2 : ((ρ y ⟨x, hx⟩ : ↥L) : G) = (g : G) * x * (g : G)⁻¹ := by
    rw [← hg]
    rfl
  rw [h2, hyz'] at h1
  have h3 : (g : G) * x * (g : G)⁻¹ = z * x * z⁻¹ := h1
  rw [hzinv] at h3 ⊢
  simp only [Subgroup.coe_inv, inv_inv]
  exact h3.symm

end CFSG.Quasithin

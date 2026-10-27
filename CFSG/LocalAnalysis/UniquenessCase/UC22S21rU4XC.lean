module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XA
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

section Generic

variable {Q : Type} [Group Q] [Finite Q]

theorem u4x_conj_injective {X : Type*} [Group X] (hZ : center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro x y h
  have hc : y⁻¹ * x ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun σ : MulAut X => σ g) h
    simp only [MulAut.conj_apply] at h1
    calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
      _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [h1]
      _ = y⁻¹ * x * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem u4x_inner_part {F : Subgroup Q} (hZ : center ↥F = ⊥) {q : ℕ}
    (hinn : ∀ α : MulAut ↥F, α ^ q = 1 → α ∈ (MulAut.conj : ↥F →* MulAut ↥F).range)
    {β : Q} (hβ : β ∈ normalizer (F : Set Q)) (hβq : β ^ q = 1) :
    ∃ x ∈ F, x ^ q = 1 ∧ ∀ f ∈ F, β * f * β⁻¹ = x * f * x⁻¹ := by
  have hαq : (F.normalizerMonoidHom ⟨β, hβ⟩) ^ q = 1 := by
    rw [← map_pow]
    have h1 : (⟨β, hβ⟩ : ↥(normalizer (F : Set Q))) ^ q = 1 := Subtype.ext (by simp [hβq])
    rw [h1, map_one]
  obtain ⟨y, hy⟩ := hinn _ hαq
  have hconj : ∀ f ∈ F, β * f * β⁻¹ = (y : Q) * f * (y : Q)⁻¹ := by
    intro f hf
    have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe F ⟨β, hβ⟩ ⟨f, hf⟩
    rw [← hy] at h1
    simpa [MulAut.conj_apply] using h1.symm
  refine ⟨y, y.2, ?_, hconj⟩
  have h2 : MulAut.conj (y ^ q) = MulAut.conj (1 : ↥F) := by
    rw [map_pow, hy, hαq, map_one]
  simpa using congrArg Subtype.val (u4x_conj_injective hZ h2)

theorem u4x_mul_inv_mem_centralizer {F₀ F₁ : Subgroup Q}
    (hcomm : ∀ x ∈ F₀, ∀ y ∈ F₁, x * y = y * x) {β x₀ x₁ : Q} (hx₀ : x₀ ∈ F₀) (hx₁ : x₁ ∈ F₁)
    (h₀ : ∀ f ∈ F₀, β * f * β⁻¹ = x₀ * f * x₀⁻¹) (h₁ : ∀ f ∈ F₁, β * f * β⁻¹ = x₁ * f * x₁⁻¹) :
    β * (x₀ * x₁)⁻¹ ∈ centralizer ((F₀ ⊔ F₁ : Subgroup Q) : Set Q) := by
  have k₀ : ∀ f ∈ F₀, f * (β * (x₀ * x₁)⁻¹) = β * (x₀ * x₁)⁻¹ * f := by
    intro f hf
    have hg : x₀⁻¹ * f * x₀ ∈ F₀ := F₀.mul_mem (F₀.mul_mem (F₀.inv_mem hx₀) hf) hx₀
    have e1 : β * (x₀⁻¹ * f * x₀) * β⁻¹ = f := by rw [h₀ _ hg]; group
    have e2 := hcomm _ hg x₁ hx₁
    calc f * (β * (x₀ * x₁)⁻¹) = β * (x₀⁻¹ * f * x₀) * β⁻¹ * (β * (x₀ * x₁)⁻¹) := by rw [e1]
      _ = β * x₁⁻¹ * (x₁ * (x₀⁻¹ * f * x₀)) * x₁⁻¹ * x₀⁻¹ := by group
      _ = β * x₁⁻¹ * (x₀⁻¹ * f * x₀ * x₁) * x₁⁻¹ * x₀⁻¹ := by rw [e2]
      _ = β * (x₀ * x₁)⁻¹ * f := by group
  have k₁ : ∀ f ∈ F₁, f * (β * (x₀ * x₁)⁻¹) = β * (x₀ * x₁)⁻¹ * f := by
    intro f hf
    have hg : x₁⁻¹ * f * x₁ ∈ F₁ := F₁.mul_mem (F₁.mul_mem (F₁.inv_mem hx₁) hf) hx₁
    have e1 : β * (x₁⁻¹ * f * x₁) * β⁻¹ = f := by rw [h₁ _ hg]; group
    have e2 := hcomm x₀ hx₀ f hf
    have e3 : f * x₀⁻¹ = x₀⁻¹ * f := by
      calc f * x₀⁻¹ = x₀⁻¹ * (x₀ * f) * x₀⁻¹ := by group
        _ = x₀⁻¹ * (f * x₀) * x₀⁻¹ := by rw [e2]
        _ = x₀⁻¹ * f := by group
    calc f * (β * (x₀ * x₁)⁻¹) = β * (x₁⁻¹ * f * x₁) * β⁻¹ * (β * (x₀ * x₁)⁻¹) := by rw [e1]
      _ = β * x₁⁻¹ * (f * x₀⁻¹) := by group
      _ = β * x₁⁻¹ * (x₀⁻¹ * f) := by rw [e3]
      _ = β * (x₀ * x₁)⁻¹ * f := by group
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨f₀, hf₀, f₁, hf₁, rfl⟩ := u4x_mem_sup hcomm hh
  rw [mul_assoc, k₁ f₁ hf₁, ← mul_assoc, k₀ f₀ hf₀, mul_assoc]

theorem u4x_commute_of_conj {F : Subgroup Q} {β x : Q} (hx : x ∈ F)
    (h : ∀ f ∈ F, β * f * β⁻¹ = x * f * x⁻¹) : Commute β x := by
  have h1 := h x hx
  calc β * x = β * x * β⁻¹ * β := by group
    _ = x * x * x⁻¹ * β := by rw [h1]
    _ = x * β := by group

theorem u4x_pow_eq_one {F₀ F₁ : Subgroup Q} (hcomm : ∀ x ∈ F₀, ∀ y ∈ F₁, x * y = y * x)
    {β x₀ x₁ : Q} (hx₀ : x₀ ∈ F₀) (hx₁ : x₁ ∈ F₁) (h₀ : ∀ f ∈ F₀, β * f * β⁻¹ = x₀ * f * x₀⁻¹)
    (h₁ : ∀ f ∈ F₁, β * f * β⁻¹ = x₁ * f * x₁⁻¹) {q : ℕ} (hβ : β ^ q = 1) (h0 : x₀ ^ q = 1)
    (h1 : x₁ ^ q = 1) : (β * (x₀ * x₁)⁻¹) ^ q = 1 := by
  have c0 := u4x_commute_of_conj hx₀ h₀
  have c1 := u4x_commute_of_conj hx₁ h₁
  have c01 : Commute x₀ x₁ := hcomm x₀ hx₀ x₁ hx₁
  rw [((c0.mul_right c1).inv_right).mul_pow, hβ, one_mul, inv_pow, c01.mul_pow, h0, h1, one_mul,
    inv_one]

theorem u4x_dvd_of_borel {F S : Subgroup Q} {n : ℕ}
    (hF : IsL2 ↥F n ∨ IsSz ↥F n) (hS : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ F) F) {x : Q}
    (hxF : x ∈ F) (hx1 : x ≠ 1) (hxN : ∀ s ∈ S ⊓ F, x * s * x⁻¹ ∈ S) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hxq : x ^ q = 1) : q ∣ 2 ^ n - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have e1 : ((S ⊓ F).subgroupOf F).map F.subtype = S ⊓ F := by
    rw [Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have e2 : (⊤ : Subgroup ↥F).map F.subtype = F := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 ((S ⊓ F).subgroupOf F) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff F).1 (by rw [e1, e2]; exact hS)
  have hxN' : (⟨x, hxF⟩ : ↥F) ∈ normalizer (((S ⊓ F).subgroupOf F : Subgroup ↥F) : Set ↥F) := by
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hs ⊢
    exact ⟨hxN _ hs, F.mul_mem (F.mul_mem hxF hs.2) (F.inv_mem hxF)⟩
  have ho : orderOf (⟨x, hxF⟩ : ↥F) = q :=
    orderOf_eq_prime (Subtype.ext (by simpa using hxq)) fun h => hx1 (congrArg Subtype.val h)
  have hdvd : q ∣ Nat.card ↥(normalizer (((S ⊓ F).subgroupOf F : Subgroup ↥F) : Set ↥F)) := by
    have h5 : orderOf (⟨⟨x, hxF⟩, hxN'⟩ : ↥(normalizer
        (((S ⊓ F).subgroupOf F : Subgroup ↥F) : Set ↥F))) = q := by
      rw [Subgroup.orderOf_mk]
      exact ho
    exact h5 ▸ orderOf_dvd_natCard _
  rcases hF with h | h
  · exact uc22p2214_borel_prime_L2 h hS' hq hq2 hdvd
  · exact uc22p2214_borel_prime_Sz h hS' hq hq2 hdvd

theorem u4x_isSylowOf_inf {F₀ F₁ T : Subgroup Q} (hcomm : ∀ x ∈ F₀, ∀ y ∈ F₁, x * y = y * x)
    (hN : (F₀ ⊔ F₁).Normal) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ F₀) F₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hT.inf_of_le_normalizer le_top (u4x_top_le_normalizer hN)
  have hle : F₀ ⊔ F₁ ≤ normalizer (F₀ : Set Q) := sup_le Subgroup.le_normalizer fun y hy =>
    Subgroup.mem_normalizer_iff.2 fun f => by
      constructor
      · intro hf
        rw [← hcomm f hf y hy, mul_inv_cancel_right]
        exact hf
      · intro hf
        have h2 := hcomm _ hf y hy
        have h3 : f = y * f * y⁻¹ := by
          calc f = y⁻¹ * (y * f * y⁻¹ * y) := by group
            _ = y⁻¹ * (y * (y * f * y⁻¹)) := by rw [h2]
            _ = y * f * y⁻¹ := by group
        rw [h3]
        exact hf
  have h4 := h1.inf_of_le_normalizer le_sup_left hle
  rwa [inf_assoc, inf_eq_right.2 (le_sup_left : F₀ ≤ F₀ ⊔ F₁)] at h4

end Generic

theorem u4x_shape_barImage {M L : Subgroup G} (hL : L ∈ calC M) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    IsL2 ↥(barImage M L) n ∨ IsSz ↥(barImage M L) n := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  rcases hS with h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h)

theorem u4x_bar_decomp {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n) {b : ↥M}
    (hbL : (b : G) ∈ normalizer (L : Set G)) (hbK : (b : G) ∈ normalizer (K : Set G))
    (hbq : b ^ q = 1) :
    ∃ x₀ ∈ barImage M L, ∃ x₁ ∈ barImage M K, x₀ ^ q = 1 ∧ x₁ ^ q = 1 ∧
      (∀ f ∈ barImage M L, uc22p21cPi M b * f * (uc22p21cPi M b)⁻¹ = x₀ * f * x₀⁻¹) ∧
      (∀ f ∈ barImage M K, uc22p21cPi M b * f * (uc22p21cPi M b)⁻¹ = x₁ * f * x₁⁻¹) ∧
      uc22p21cPi M b * (x₀ * x₁)⁻¹ ∈
        centralizer ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M)) := by
  obtain ⟨hcomm, -, h₀, h₁, -, -, -⟩ := u4x_bar_structure hL hK hne hset hS
  have hKS := uc22s21ru4e_shape_conj (K := K) (by rw [hset]; simp) hS
  have hinn : ∀ {P : Subgroup G}, P ∈ calC M → (IsL2 (Bar2 P) n ∨ IsSz (Bar2 P) n) →
      ∀ α : MulAut ↥(barImage M P), α ^ q = 1 → α ∈ (MulAut.conj : _ →* MulAut _).range := by
    intro P hP hPS α hα
    rcases u4x_shape_barImage hP hPS with h | h
    · exact uc22p2214_inner_of_prime_L2 h hq hqn hα
    · exact uc22p2214_inner_of_prime_Sz h hq hqn hα
  have hbq' : uc22p21cPi M b ^ q = 1 := by rw [← map_pow, hbq, map_one]
  obtain ⟨x₀, hx₀, hx₀q, hc₀⟩ := u4x_inner_part h₀ (hinn hL hS)
    (uc22ine229_mk_mem_normalizer hbL) hbq'
  obtain ⟨x₁, hx₁, hx₁q, hc₁⟩ := u4x_inner_part h₁ (hinn hK hKS)
    (uc22ine229_mk_mem_normalizer hbK) hbq'
  exact ⟨x₀, hx₀, x₁, hx₁, hx₀q, hx₁q, hc₀, hc₁,
    u4x_mul_inv_mem_centralizer hcomm hx₀ hx₁ hc₀ hc₁⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

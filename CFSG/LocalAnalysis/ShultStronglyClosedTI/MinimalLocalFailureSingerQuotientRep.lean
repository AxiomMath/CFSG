module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSingerQuotientBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerScalar
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain.SingerQuotient

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G] [Finite G]

theorem exists_singer_rep {H Q B X J M : Subgroup G}
    (hQH : Q ≤ H) (hQn : (Q.subgroupOf H).Normal) (hBH : B ≤ H) (hXB : X ≤ B) (hJB : J ≤ B)
    (hM : M = H ⊓ Subgroup.centralizer (Q : Set G)) (hMcore : M.subgroupOf H = CFSG.pCore 2 H)
    {e : ℕ} (he : 1 ≤ e) (hqe : Nat.card Q = 2 ^ e)
    (hBidx : B.relIndex H = Nat.card Q ^ 3) (hJcard : Nat.card J = 2)
    (hMcard : Nat.card M = 2 * Nat.card Q ^ 2)
    {k₀ : Type} [Field k₀] [Finite k₀] [Algebra (ZMod 2) k₀] (hk₀ : Nat.card k₀ = Nat.card Q)
    (φ : Q ≃* Multiplicative k₀) (ι : B →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀)
    (hιker : ι.ker = J.subgroupOf B)
    (hιact : ∀ (b : B) (x y : Q), (y : G) = (b : G) * x * (b : G)⁻¹ →
      (φ y).toAdd = ((ι b).left : k₀) * (ι b).right (φ x).toAdd)
    (hιX : (X.subgroupOf B).map ι = (SemidirectProduct.inl : k₀ˣ →* _).range) :
    ∃ d : ℕ, d ∣ e ∧ ∃ ρ : H →* (k₀ ≃ₗ[ZMod 2] k₀),
      ρ.ker = M.subgroupOf H ∧
      (∀ (h : H) (x y : Q), (y : G) = h * x * (h : G)⁻¹ → (φ y).toAdd = ρ h (φ x).toAdd) ∧
      (X.subgroupOf H).map ρ = Singer.scalars (ZMod 2) k₀ ∧
      Singer.scalars (ZMod 2) k₀ ≤ ρ.range ∧
      Nat.card ρ.range = Nat.card Q * (Nat.card Q - 1) * d ∧
      CFSG.pCore 2 ρ.range = ⊥ ∧ e ≠ 2 := by
  have hHN : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQn
  let σ : H →* MulAut Q := conjHom hHN
  let ρ : H →* (k₀ ≃ₗ[ZMod 2] k₀) := linearRep 2 φ σ
  have hMH : M ≤ H := hM ▸ inf_le_left
  have hρker : ρ.ker = M.subgroupOf H := by
    rw [ker_linearRep, ker_conjHom, hM, Subgroup.inf_subgroupOf_left]
  have hρact : ∀ (h : H) (x y : Q), (y : G) = h * x * (h : G)⁻¹ →
      (φ y).toAdd = ρ h (φ x).toAdd := by
    intro h x y hy
    rw [linearRep_apply_toAdd]
    congr 2
    exact Subtype.ext hy
  have hρX : ∀ b : B, ∀ c : k₀ˣ, ι b = SemidirectProduct.inl c →
      ρ ⟨b, hBH b.2⟩ = Singer.scalarHom (ZMod 2) k₀ c := by
    intro b c hc
    refine LinearEquiv.ext fun v => ?_
    rw [linearRep_apply, Singer.scalarHom_apply]
    have hv := hιact b (φ.symm (Multiplicative.ofAdd v))
      (σ ⟨b, hBH b.2⟩ (φ.symm (Multiplicative.ofAdd v))) rfl
    rw [hc, SemidirectProduct.left_inl, SemidirectProduct.right_inl, MulEquiv.apply_symm_apply,
      toAdd_ofAdd] at hv
    exact hv
  have hmap : (X.subgroupOf H).map ρ = Singer.scalars (ZMod 2) k₀ := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hxH⟩, hxX, rfl⟩
      have hmem : ι ⟨x, hXB hxX⟩ ∈ (SemidirectProduct.inl : k₀ˣ →* _).range := by
        rw [← hιX]
        exact ⟨⟨x, hXB hxX⟩, hxX, rfl⟩
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, (hρX ⟨x, hXB hxX⟩ c hc.symm).symm⟩
    · rintro _ ⟨c, rfl⟩
      have hmem : SemidirectProduct.inl c ∈ (X.subgroupOf B).map ι := by
        rw [hιX]
        exact ⟨c, rfl⟩
      obtain ⟨b, hbX, hb⟩ := hmem
      exact ⟨⟨b, hBH b.2⟩, hbX, hρX b c hb⟩
  have hH : Nat.card H = Nat.card Q ^ 3 * Nat.card B := by
    rw [← hBidx, ← Subgroup.relIndex_mul_card B H, inf_eq_left.mpr hBH]
  have hB : Nat.card B = 2 * Nat.card ι.range := by
    rw [← Subgroup.card_ker_mul_card_range ι, hιker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJB).toEquiv, hJcard]
  have hS : (SemidirectProduct.inl : k₀ˣ →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀).range ≤
      ι.range := by
    rw [← hιX]
    exact Subgroup.map_le_range ι _
  set d := Nat.card (ι.range.map SemidirectProduct.rightHom)
  have hι : Nat.card ι.range = (Nat.card Q - 1) * d := by
    rw [card_eq_mul_card_map_rightHom ι.range hS, Nat.card_units, hk₀]
  have hde : d ∣ e := by
    obtain ⟨-, -, -, -, hAut, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two he (hk₀.trans hqe)
    have hdvd := Subgroup.card_subgroup_dvd_card (ι.range.map SemidirectProduct.rightHom)
    rwa [show Nat.card (RingAut k₀) = e from hAut] at hdvd
  have hρcard : Nat.card ρ.range = Nat.card Q * (Nat.card Q - 1) * d := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hρker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv, hMcard, hH, hB, hι]
      at h1
    have hq : 0 < Nat.card Q := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 * Nat.card Q ^ 2 by positivity) ?_
    rw [h1]
    ring
  have hne2 : e ≠ 2 := by
    rintro rfl
    obtain ⟨hfin, hle⟩ := card_linearEquiv_le (k := ZMod 2) (F := k₀)
    have h1 := Subgroup.card_le_card_group ρ.range
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hde (by norm_num)
    rw [hk₀, hqe] at hle
    rw [hρcard, hqe] at h1
    have h2 := h1.trans hle
    norm_num [Nat.factorial] at h2
    omega
  exact ⟨d, hde, ρ, hρker, hρact, hmap, hmap ▸ Subgroup.map_le_range ρ _, hρcard,
    pCore_range_eq_bot ρ (hρker.trans hMcore), hne2⟩

end CFSG.ShultStronglyClosedTI.FinalChain.SingerQuotient

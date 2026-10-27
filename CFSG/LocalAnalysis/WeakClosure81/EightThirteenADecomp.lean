module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenCommutator
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenOrderEight

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Sit813.eq_of_decomp {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K)
    {a b k₁ k₂ t₁ t₂ : G} (ha : a ∈ A) (hb : b ∈ A) (hk₁ : k₁ ∈ K ⊓ normalizer (V : Set G))
    (hk₂ : k₂ ∈ K ⊓ normalizer (V : Set G)) (ht₁ : t₁ ∈ rGrp H T K) (ht₂ : t₂ ∈ rGrp H T K)
    (h₁ : a = k₁ * t₁) (h₂ : b = k₂ * t₂) (hN : k₁⁻¹ * k₂ ∈ oTwoMod (cGrp H T) K) : a = b := by
  classical
  by_contra hne
  have D := h.fiveData
  set K₁ : Subgroup G := K ⊓ normalizer (V : Set G) with hK₁def
  have S : Five.FiveSetup K K₁ (oTwoMod (cGrp H T) K) := D.setup
  haveI : Fintype (Five.Cosets K K₁) := Fintype.ofFinite _
  have hcard : Fintype.card (Five.Cosets K K₁) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.card_cosets
  have haK := D.a_normK ha
  have hbK := D.a_normK hb
  have haK₁ := Five.mem_normalizer_inf_normalizer haK (D.a_normV ha)
  have hbK₁ := Five.mem_normalizer_inf_normalizer hbK (D.a_normV hb)
  have habA : a * b ∈ A := A.mul_mem ha hb
  have hab1 : a * b ≠ 1 := fun h1 => hne ((mul_left_cancel (h1.trans (D.a_sq a ha).symm)).symm)
  have hpa : Five.conjPerm K K₁ a haK haK₁ = MulAction.toPerm (⟨k₁, S.le hk₁⟩ : ↥K) :=
    Five.conjPerm_eq_toPerm S hk₁ h₁ (D.r_comm t₁ ht₁) haK haK₁
  have hpb : Five.conjPerm K K₁ b hbK hbK₁ = MulAction.toPerm (⟨k₂, S.le hk₂⟩ : ↥K) :=
    Five.conjPerm_eq_toPerm S hk₂ h₂ (D.r_comm t₂ ht₂) hbK hbK₁
  have hpab : (MulAction.toPerm (⟨k₁, S.le hk₁⟩ : ↥K) : Equiv.Perm (Five.Cosets K K₁)) =
      MulAction.toPerm (⟨k₂, S.le hk₂⟩ : ↥K) := by
    have h1 := (S.toPerm_eq_one_iff (⟨k₁, S.le hk₁⟩⁻¹ * ⟨k₂, S.le hk₂⟩)).mpr hN
    have h2 : (MulAction.toPermHom ↥K (Five.Cosets K K₁))
        (⟨k₁, S.le hk₁⟩⁻¹ * ⟨k₂, S.le hk₂⟩) = 1 := h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hsq : Five.conjPerm K K₁ a haK haK₁ * Five.conjPerm K K₁ a haK haK₁ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk _ : Five.Cosets K K₁) = QuotientGroup.mk g
      congr 1
      ext
      change a * (a * (g : G) * a⁻¹) * a⁻¹ = g
      calc a * (a * (g : G) * a⁻¹) * a⁻¹ = (a * a) * (g : G) * (a * a)⁻¹ := by group
        _ = g := by rw [D.a_sq a ha]; group
  have habK := D.a_normK habA
  have habK₁ := Five.mem_normalizer_inf_normalizer habK (D.a_normV habA)
  have hone : Five.conjPerm K K₁ (a * b) habK habK₁ = 1 := by
    rw [Five.conjPerm_mul a b haK haK₁ hbK hbK₁ habK habK₁, hpb, ← hpab, ← hpa]
    exact hsq
  haveI : Nontrivial (Five.Cosets K K₁) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨ω, hω⟩ := exists_ne (QuotientGroup.mk 1 : Five.Cosets K K₁)
  refine hω (D.unique_fixed habA hab1 ω ?_)
  have := congrArg (fun σ : Equiv.Perm (Five.Cosets K K₁) => σ ω) hone
  simpa using this

theorem Sit813.exists_fixed_of_central_decomp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hNV : ∀ n ∈ oTwoMod (cGrp H T) K, ∀ w ∈ V, n * w = w * n)
    (hcen : ∀ a ∈ A, ∀ k ∈ K ⊓ normalizer (V : Set G), ∀ t ∈ rGrp H T K, a = k * t →
      ∀ w ∈ V, k * w = w * k) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ y ∈ K ⊓ normalizer (V : Set G), y * v * y⁻¹ = v := by
  set N : Subgroup G := oTwoMod (cGrp H T) K with hNdef
  set K₁ : Subgroup G := K ⊓ normalizer (V : Set G) with hK₁def
  set P : Subgroup G := K₁ ⊓ centralizer (V : Set G) with hPdef
  have hNK₁ : N ≤ K₁ := h.oTwoMod_le_inf
  have hK₁K : K₁ ≤ K := inf_le_left
  have hPK₁ : P ≤ K₁ := inf_le_left
  have hNP : N ≤ P := fun n hn => Subgroup.mem_inf.mpr ⟨hNK₁ hn,
    Subgroup.mem_centralizer_iff.mpr fun w hw => (hNV n hn w hw).symm⟩
  have hidx5 : K₁.relIndex K = 5 := h.concl813.d_index
  have hN60 : N.relIndex K = 60 := h.kn4
  have hN12 : N.relIndex K₁ = 12 := by
    have h1 := Subgroup.relIndex_mul_relIndex (H := N) (K := K₁) (L := K) hNK₁ hK₁K
    rw [hidx5, hN60] at h1
    omega
  have hNPK : N.relIndex P * P.relIndex K₁ = N.relIndex K₁ :=
    Subgroup.relIndex_mul_relIndex (H := N) (K := P) (L := K₁) hNP hPK₁
  have hex : ∀ a : ↥A, ∃ k : ↥P, ∃ t ∈ rGrp H T K, (a : G) = k * t := by
    intro a
    obtain ⟨k, hk, t, ht, hat⟩ := h.exists_decomp a.2
    exact ⟨⟨k, Subgroup.mem_inf.mpr ⟨hk, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (hcen a a.2 k hk t ht hat w hw).symm⟩⟩, t, ht, hat⟩
  choose kf tf htf hatf using hex
  have hinj : Function.Injective
      (fun a : ↥A => (QuotientGroup.mk (kf a) : ↥P ⧸ N.subgroupOf P)) := by
    intro a b hab
    have h1 := QuotientGroup.eq.mp hab
    rw [Subgroup.mem_subgroupOf] at h1
    exact Subtype.ext (h.eq_of_decomp a.2 b.2 (Subgroup.mem_inf.mp (kf a).2).1
      (Subgroup.mem_inf.mp (kf b).2).1 (htf a) (htf b) (hatf a) (hatf b) h1)
  have hA4 : 4 ≤ N.relIndex P := by
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [h.card_A_eq_four] at h1
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact h1
  have hP3 : P.relIndex K₁ ≤ 3 := by
    by_contra hlt
    push Not at hlt
    rw [hN12] at hNPK
    nlinarith
  refine exists_fixed_of_relIndex_le_three (X := K₁) (P := P) h.card_V_eq_eight inf_le_right hP3 ?_
  intro p hp w hw
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hp).2 w hw).symm

end CFSG.LocalAnalysis.WeakClosure81

end

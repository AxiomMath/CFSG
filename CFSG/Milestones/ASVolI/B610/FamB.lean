module

public import CFSG.Milestones.ASVolI.B610.FamA

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideB610_rk_of_card_eq_mul {A B C : Type*} [Group A] [Group B] [Group C] [Finite B]
    [Finite C] (h : Nat.card A = Nat.card B * Nat.card C) : rk A = rk B + rk C := by
  unfold rk
  rw [h, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']

theorem burnsideB610_rk_le_of_card_le {A B C : Type*} [Group A] [Group B] [Group C] [Finite A]
    [Finite B] [Finite C] (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) (hC : IsPGroup 2 C)
    (h : Nat.card A ≤ Nat.card B * Nat.card C) : rk A ≤ rk B + rk C := by
  rw [card_eq_two_pow_of_isPGroup hA, card_eq_two_pow_of_isPGroup hB,
    card_eq_two_pow_of_isPGroup hC, ← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem burnsideB610_rk_add_le_of_card_le {A B C : Type*} [Group A] [Group B] [Group C] [Finite A]
    [Finite B] [Finite C] (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) (hC : IsPGroup 2 C)
    (h : Nat.card B * Nat.card C ≤ Nat.card A) : rk B + rk C ≤ rk A := by
  rw [card_eq_two_pow_of_isPGroup hA, card_eq_two_pow_of_isPGroup hB,
    card_eq_two_pow_of_isPGroup hC, ← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem burnsideB610_rk_inf_inf [Finite G] {A B₁ B₂ : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    rk ↥(A ⊓ B₁) + rk ↥(A ⊓ B₂) ≤ rk ↥A + rk ↥(A ⊓ B₁ ⊓ B₂) := by
  have h := B2F.rk_sup_add_rk_inf_of_commute (A := A ⊓ B₁) (B := A ⊓ B₂)
    (fun a ha b hb => hA a ha.1 b hb.1)
  have h2 : (A ⊓ B₁) ⊓ (A ⊓ B₂) = A ⊓ B₁ ⊓ B₂ := by
    rw [inf_inf_inf_comm, inf_idem, inf_assoc]
  have h3 : rk ↥((A ⊓ B₁) ⊔ (A ⊓ B₂)) ≤ rk ↥A := rk_mono (sup_le inf_le_left inf_le_left)
  rw [h2] at h
  omega

theorem burnsideB610_rk_le_sum [Finite G] {A : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {ι : Type} [DecidableEq ι] (B : ι → Subgroup G) :
    ∀ 𝒮 : Finset ι, rk ↥A ≤ rk ↥(A ⊓ ⨅ i ∈ 𝒮, B i) + ∑ i ∈ 𝒮, (rk ↥A - rk ↥(A ⊓ B i)) := by
  intro 𝒮
  induction 𝒮 using Finset.induction_on with
  | empty =>
    have he : (⨅ i ∈ (∅ : Finset ι), B i) = ⊤ :=
      le_antisymm le_top (le_iInf₂ fun i hi => (Finset.notMem_empty i hi).elim)
    rw [he, inf_top_eq, Finset.sum_empty, add_zero]
  | insert j 𝒮' hj ih =>
    rw [Finset.iInf_insert, Finset.sum_insert hj]
    have h1 := burnsideB610_rk_inf_inf (A := A) (B₁ := ⨅ i ∈ 𝒮', B i) (B₂ := B j) hA
    have h2 : A ⊓ (B j ⊓ ⨅ i ∈ 𝒮', B i) = A ⊓ (⨅ i ∈ 𝒮', B i) ⊓ B j := by
      rw [inf_comm (B j), inf_assoc]
    have h3 : rk ↥(A ⊓ B j) ≤ rk ↥A := rk_mono inf_le_left
    rw [h2]
    omega

theorem burnsideB610_img_le_natNorm {L V : Subgroup G} {F : Type} [Field F] (D : NatData L V F)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (Y : Subgroup G) :
    D.img Y ≤ H.natNorm (Assembly.LowTwoRank.StatedSL 2 F) := by
  rintro _ ⟨x, -, rfl⟩
  have hnorm : ∀ (y : ↥(nLV L V)), ∀ l : ↥L,
      D.act y * H.natAut (Assembly.LowTwoRank.StatedSL 2 F) (D.α l) * (D.act y)⁻¹ ∈
        H.natImage (Assembly.LowTwoRank.StatedSL 2 F) := by
    intro y l
    have hyl : (y : G) * l * (y : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp y.2.1 l).mp l.2
    refine ⟨D.α ⟨_, hyl⟩, ?_⟩
    rw [← D.act_of_mem hLV ⟨_, hyl⟩, ← D.act_of_mem hLV l, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  refine B6.mem_normalizer_of_forall_mem (fun e he => ?_) fun e he => ?_
  · obtain ⟨γ, rfl⟩ := he
    obtain ⟨l, rfl⟩ := D.surj γ
    exact hnorm x l
  · obtain ⟨γ, rfl⟩ := he
    obtain ⟨l, rfl⟩ := D.surj γ
    have := hnorm x⁻¹ l
    rwa [map_inv, inv_inv] at this

theorem burnsideB610_img_isElemAbelian2 {L V : Subgroup G} {F : Type} [Field F]
    (D : NatData L V F) {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAbelian2 (D.img A) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact B2F.isElemAbelian_comm hA (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hA.2 _ (Subgroup.mem_subgroupOf.mp hx)
    rw [this, map_one]

theorem burnsideB610_card_img_mul [Finite G] {L V : Subgroup G} {F : Type} [Field F]
    (D : NatData L V F)
    (hker : ∀ a : ↥(nLV L V), D.act a = 1 →
      (a : G) ∈ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G))
    {A : Subgroup G} (hA : A ≤ nLV L V) :
    Nat.card (D.img A) * Nat.card ↥(A ⊓ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G)) =
      Nat.card A := by
  set f : ↥(A.subgroupOf (nLV L V)) →* MulAut (H.StdMod (Fin 2) F) :=
    D.act.comp (A.subgroupOf (nLV L V)).subtype with hf
  have e1 := Subgroup.card_ker_mul_card_range f
  have hr : f.range = D.img A := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hc : Nat.card ↥(A.subgroupOf (nLV L V)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  set ι : ↥(A.subgroupOf (nLV L V)) →* G := (nLV L V).subtype.comp (A.subgroupOf (nLV L V)).subtype
    with hι
  have hιinj : Function.Injective ι := (nLV L V).subtype_injective.comp Subtype.val_injective
  have hk : f.ker.map ι = A ⊓ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.mem_subgroupOf.mp x.2, hker _ hx⟩
    · rintro ⟨hgA, hgC⟩
      refine ⟨⟨⟨g, hA hgA⟩, Subgroup.mem_subgroupOf.mpr hgA⟩, ?_, rfl⟩
      exact burnsideB610_act_eq_one_of_cent D ⟨g, hA hgA⟩ hgC
  have e2 : Nat.card f.ker =
      Nat.card ↥(A ⊓ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G)) := by
    rw [← hk, Subgroup.card_map_of_injective hιinj]
  rw [← hr, ← e2, ← hc, mul_comm]
  exact e1

theorem burnsideB610_rk_img [Finite G] {L V : Subgroup G} {F : Type} [Field F] [Finite F]
    (D : NatData L V F)
    (hker : ∀ a : ↥(nLV L V), D.act a = 1 →
      (a : G) ∈ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G))
    {A : Subgroup G} (hA : A ≤ nLV L V) :
    rk ↥(D.img A) + rk ↥(A ⊓ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G)) = rk ↥A :=
  (burnsideB610_rk_of_card_eq_mul (burnsideB610_card_img_mul D hker hA).symm).symm

theorem burnsideB610_rk_img_le [Finite G] {L V : Subgroup G} {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (D : NatData L V F)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    rk ↥(D.img A) ≤ rkIdx (fixV (D.img A)) := by
  have hE := burnsideB610_img_isElemAbelian2 D hA
  have h := nl2w_card_mul_card_fixV_le hn hF (burnsideB610_img_le_natNorm D hLV A) hE
  have hW2 : IsPGroup 2 (H.StdMod (Fin 2) F) := by
    refine IsPGroup.of_card (n := 2 * n) ?_
    rw [H.card_stdMod, Fintype.card_fin, hF, ← pow_mul, mul_comm]
  have h2 := burnsideB610_rk_add_le_of_card_le hW2 hE.isPGroup (hW2.to_subgroup _) h
  have h3 := rk_add_rkIdx (fixV (D.img A))
  omega

@[expose] def burnsideB610_pre {L V : Subgroup G} {F : Type} [Field F] (D : NatData L V F)
    (E : Subgroup (H.StdMod (Fin 2) F)) : Subgroup G :=
  (E.comap D.β).map (⁅V, L⁆ : Subgroup G).subtype

theorem burnsideB610_rk_pre [Finite G] {L V : Subgroup G} {F : Type} [Field F] [Finite F]
    (D : NatData L V F) (E : Subgroup (H.StdMod (Fin 2) F)) :
    rk ↥(burnsideB610_pre D E) + rkIdx E = rk ↥(⁅V, L⁆ : Subgroup G) := by
  have h1 : rk ↥(burnsideB610_pre D E) = rk ↥(E.comap D.β) := by
    unfold rk burnsideB610_pre
    rw [Subgroup.card_map_of_injective (⁅V, L⁆ : Subgroup G).subtype_injective]
  have h2 := rk_add_rkIdx (E.comap D.β)
  have h3 : rkIdx (E.comap D.β) = rkIdx E := by
    unfold rkIdx
    rw [Subgroup.index_comap_of_surjective E D.βsurj]
  rw [h1, ← h3]
  exact h2

end CFSG.Quasithin.B610T

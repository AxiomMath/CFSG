module

public import CFSG.Quasithin.H13.NQRigidInputs
public import CFSG.Quasithin.H13.NQBlockCcomponentQuotient
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)

theorem isFrattiniLatticeIrreducible_of {H : Type*} [Group H] {X A : Subgroup H}
    (hirr : IsFrattiniIrreducible X A) : IsFrattiniLatticeIrreducible X A (CFSG.pCore 2 X) := by
  intro Y hΦY hYX hAY
  set ι : X →* (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) :=
    (QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 X)) with hι
  have hker : ι.ker.map X.subtype = frattiniPreimage X (CFSG.pCore 2 X) := by
    rw [frattiniPreimage]
    congr 1
    ext x
    simp only [hι, MonoidHom.mem_ker, MonoidHom.comp_apply, mem_comap, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  set YW := (Y.subgroupOf X).map ι with hYW
  have hinv : ∀ h : normalizer (X : Set H), (h : H) ∈ A → ∀ y ∈ YW,
      normalizerFrattiniConj X h y ∈ YW := by
    rintro h hhA _ ⟨y, hy, rfl⟩
    refine ⟨X.normalizerMonoidHom h y, ?_, rfl⟩
    have hy' : (y : H) ∈ Y := hy
    show ((X.normalizerMonoidHom h y : X) : H) ∈ Y
    exact (mem_normalizer_iff.mp (hAY hhA) y).mp hy'
  rcases hirr YW hinv with h0 | ht
  · left
    apply le_antisymm _ hΦY
    intro y hy
    have hyX := hYX hy
    have h1 : ι ⟨y, hyX⟩ ∈ YW := ⟨⟨y, hyX⟩, mem_subgroupOf.mpr hy, rfl⟩
    rw [h0, mem_bot] at h1
    rw [← hker]
    exact ⟨⟨y, hyX⟩, h1, rfl⟩
  · right
    apply le_antisymm hYX
    intro x hx
    have h1 : ι ⟨x, hx⟩ ∈ YW := ht ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    have hk : y⁻¹ * ⟨x, hx⟩ ∈ ι.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have h2 : ((y⁻¹ * ⟨x, hx⟩ : X) : H) ∈ Y := hΦY (hker ▸ ⟨_, hk, rfl⟩)
    have h3 : (y : H) ∈ Y := mem_subgroupOf.mp hy
    have h4 : x = (y : H) * ((y⁻¹ * ⟨x, hx⟩ : X) : H) := by
      simp
    rw [h4]
    exact Y.mul_mem h3 h2

theorem pow_mem_pCore_of_exponent {X : Type*} [Group X] {p : ℕ}
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p) (x : X) : x ^ p ∈ CFSG.pCore 2 X := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hexp]
  exact Monoid.pow_exponent_eq_one _

theorem pRank_quotient_of_isPGroup_two {H : Type*} [Group H] [Finite H] (C : Subgroup H)
    [C.Normal] (hC : IsPGroup 2 C) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.pRank r (H ⧸ C) = CFSG.pRank r H := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrC : ¬ r ∣ Nat.card C := by
    obtain ⟨k, hk⟩ := hC.exists_card_eq
    rw [hk]
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq C hrC,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top]

section Conjugates

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem isCComponent_conjugate {K : Subgroup H} (hK : CFSG.IsCComponent K) (g : H) :
    CFSG.IsCComponent (CFSG.conjugate K g) := by
  have h1 := CFSG.Quasithin.cComp_map_mulEquiv (MulAut.conj g⁻¹)
    (CFSG.Quasithin.mem_cComp_top_iff_isCComponent.mpr hK)
  rw [map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at h1
  exact CFSG.Quasithin.mem_cComp_top_iff_isCComponent.mp h1

omit [Finite H] in
theorem conjugate_conjugate (K : Subgroup H) (a b : H) :
    CFSG.conjugate (CFSG.conjugate K a) b = CFSG.conjugate K (a * b) := by
  rw [CFSG.conjugate, CFSG.conjugate, CFSG.conjugate, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

omit [Finite H] in
theorem map_conjugate_hom {E : Type*} [Group E] (f : H →* E) (K : Subgroup H) (g : H) :
    (CFSG.conjugate K g).map f = CFSG.conjugate (K.map f) (f g) := by
  rw [CFSG.conjugate, CFSG.conjugate, map_map, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv, MulAut.conj_inv_apply,
    map_mul]

omit [Finite H] in
theorem conjugate_one (K : Subgroup H) : CFSG.conjugate K 1 = K := by
  ext x
  simp [CFSG.conjugate, Subgroup.mem_map]

omit [Finite H] in
theorem conjugate_injective {K₁ K₂ : Subgroup H} {g : H}
    (h : CFSG.conjugate K₁ g = CFSG.conjugate K₂ g) : K₁ = K₂ := by
  have := congrArg (fun K => CFSG.conjugate K g⁻¹) h
  simp only [conjugate_conjugate, mul_inv_cancel, conjugate_one] at this
  exact this

omit [Finite H] in
theorem conjugate_eq_self_iff {K : Subgroup H} {g : H} :
    CFSG.conjugate K g = K ↔ g ∈ normalizer (K : Set H) := by
  rw [CFSG.conjugate, ← inv_mem_iff (x := g), mem_normalizer_iff_map_conj_eq]
  exact Iff.rfl

theorem eq_of_map_eq_of_isCComponent {N : Subgroup H} [N.Normal] (hN : Group.IsSolvable N)
    {K₁ K₂ : Subgroup H} (hK₁ : CFSG.IsCComponent K₁) (hK₂ : CFSG.IsCComponent K₂)
    (h : K₁.map (QuotientGroup.mk' N) = K₂.map (QuotientGroup.mk' N)) : K₁ = K₂ :=
  (NQBlock.Ccomponent_solvable_quotient_bijection N hN).1.injOn hK₁ hK₂ h

theorem conjugate_dichotomy {N : Subgroup H} [N.Normal] (hN : Group.IsSolvable N)
    {K : Subgroup H} (hK : CFSG.IsCComponent K)
    (horb : (Set.range (CFSG.conjugate (K.map (QuotientGroup.mk' N)))).ncard ≤ 2) {h : H}
    (hh : CFSG.conjugate K h ≠ K) (g : H) :
    CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K h := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hg1, hg2⟩ := hne
  set π := QuotientGroup.mk' N with hπ
  have hinj : ∀ a b : H, CFSG.conjugate K a ≠ CFSG.conjugate K b →
      CFSG.conjugate (K.map π) (π a) ≠ CFSG.conjugate (K.map π) (π b) := by
    intro a b hab heq
    apply hab
    apply eq_of_map_eq_of_isCComponent hN (isCComponent_conjugate hK a)
      (isCComponent_conjugate hK b)
    rw [map_conjugate_hom, map_conjugate_hom]
    exact heq
  have h1 : CFSG.conjugate (K.map π) (π 1) ≠ CFSG.conjugate (K.map π) (π h) :=
    hinj 1 h (by rw [conjugate_one]; exact hh.symm)
  have h2 : CFSG.conjugate (K.map π) (π 1) ≠ CFSG.conjugate (K.map π) (π g) :=
    hinj 1 g (by rw [conjugate_one]; exact hg1.symm)
  have h3 : CFSG.conjugate (K.map π) (π h) ≠ CFSG.conjugate (K.map π) (π g) :=
    hinj h g (Ne.symm hg2)
  have hsub : ({CFSG.conjugate (K.map π) (π 1), CFSG.conjugate (K.map π) (π h),
      CFSG.conjugate (K.map π) (π g)} : Set (Subgroup (H ⧸ N))) ⊆
      Set.range (CFSG.conjugate (K.map π)) := by
    rintro _ (rfl | rfl | rfl)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have h3card := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_eq_three.mpr ⟨_, _, _, h1, h2, h3, rfl⟩] at h3card
  omega

theorem normalizer_ge_of_commute_images {N : Subgroup H} [N.Normal] (hN : Group.IsSolvable N)
    {K₁ K₂ : Subgroup H} (hK₁ : CFSG.IsCComponent K₁)
    (hJ : ⁅K₁.map (QuotientGroup.mk' N), K₂.map (QuotientGroup.mk' N)⁆ = ⊥) :
    K₂ ≤ normalizer (K₁ : Set H) := by
  set π := QuotientGroup.mk' N with hπ
  have hcent : ∀ a ∈ K₁, ∀ b ∈ K₂, π b * π a = π a * π b := by
    intro a ha b hb
    have h1 := (commutator_eq_bot_iff_le_centralizer.mp hJ) (mem_map_of_mem π ha)
    exact mem_centralizer_iff.mp h1 _ (mem_map_of_mem π hb)
  intro k hk
  rw [mem_normalizer_iff_map_conj_eq]
  have hc : CFSG.IsCComponent (K₁.map (MulAut.conj k).toMonoidHom) := by
    have h1 := isCComponent_conjugate hK₁ k⁻¹
    rwa [CFSG.conjugate, inv_inv] at h1
  refine eq_of_map_eq_of_isCComponent hN hc hK₁ ?_
  ext y
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨a, ha, ?_⟩
    change π a = π (k * a * k⁻¹)
    rw [map_mul, map_mul, map_inv, hcent a ha k hk, mul_inv_cancel_right]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨k * a * k⁻¹, ⟨a, ha, rfl⟩, ?_⟩
    change π (k * a * k⁻¹) = π a
    rw [map_mul, map_mul, map_inv, hcent a ha k hk, mul_inv_cancel_right]

end Conjugates

end CFSG.Quasithin.H13.NQRigid

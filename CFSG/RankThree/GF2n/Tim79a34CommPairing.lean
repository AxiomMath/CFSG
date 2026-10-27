module

public import CFSG.RankThree.GF2n.Tim79a34SpFacts

public section

namespace CFSG.RankThree.GF2n.Tim79a

open scoped commutatorElement

theorem commutator_mul_right_pairing {G : Type*} [Group G] (b r r' : G) :
    ⁅b, r * r'⁆ = ⁅b, r⁆ * (r * ⁅b, r'⁆ * r⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutator_mul_left_pairing {G : Type*} [Group G] (b b' r : G) :
    ⁅b * b', r⁆ = b * ⁅b', r⁆ * b⁻¹ * ⁅b, r⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_self_of_mul_eq {G : Type*} [Group G] {a r : G} (h : a * r = r * a) :
    r * a * r⁻¹ = a := by
  rw [← h, mul_inv_cancel_right]

theorem card_le_of_commutator_pairing {G : Type*} [Group G] [Finite G]
    (A B Px K₀ : Subgroup G) (m : ℕ)
    (hAB : A ≤ B) (hK₀ : K₀ ≤ Px)
    (hcomm : ∀ b ∈ B, ∀ r ∈ Px, ⁅b, r⁆ ∈ A)
    (hAcent : ∀ a ∈ A, ∀ x ∈ B ⊔ Px, a * x = x * a)
    (hBK : ∀ b ∈ B, ∀ k ∈ K₀, b * k = k * b)
    (hker : ∀ b ∈ B, (∀ r ∈ Px, b * r = r * b) → b ∈ A)
    (hKn : ∀ r ∈ Px, ∀ k ∈ K₀, r * k * r⁻¹ ∈ K₀)
    (hab : ∀ r ∈ Px, ∀ r' ∈ Px, ⁅r, r'⁆ ∈ K₀) (hsq : ∀ r ∈ Px, r * r ∈ K₀)
    (hidx : K₀.relIndex Px = 2 ^ m) :
    Nat.card B ≤ Nat.card A * Nat.card A ^ m := by
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    hAcent a ha a' (Subgroup.mem_sup_left (hAB ha'))
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun x y => Subtype.ext (hAcomm x.1 x.2 y.1 y.2) }
  haveI hN : (K₀.subgroupOf Px).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hKn (g : G) g.2 (n : G) hn⟩
  have hQcomm : ∀ x y : ↥Px ⧸ K₀.subgroupOf Px, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h := hab (((b : G))⁻¹) (Px.inv_mem b.2) (((a : G))⁻¹) (Px.inv_mem a.2)
    convert h using 1
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  letI : CommGroup (↥Px ⧸ K₀.subgroupOf Px) :=
    { (inferInstance : Group (↥Px ⧸ K₀.subgroupOf Px)) with mul_comm := hQcomm }
  have hQexp : ∀ x : ↥Px ⧸ K₀.subgroupOf Px, x * x = 1 := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq (a : G) a.2
  have hQcard : Nat.card (↥Px ⧸ K₀.subgroupOf Px) = 2 ^ m := by
    rw [← hidx]
    rfl
  have hmulapp : ∀ (f g : (↥Px ⧸ K₀.subgroupOf Px) →* ↥A) (x : ↥Px ⧸ K₀.subgroupOf Px),
      (f * g) x = f x * g x := fun _ _ _ => rfl
  have hmulR : ∀ b ∈ B, ∀ r ∈ Px, ∀ r' ∈ Px, ⁅b, r * r'⁆ = ⁅b, r⁆ * ⁅b, r'⁆ := by
    intro b hb r hr r' hr'
    rw [commutator_mul_right_pairing,
      conj_eq_self_of_mul_eq (hAcent _ (hcomm b hb r' hr') r (Subgroup.mem_sup_right hr))]
  have hmulB : ∀ b ∈ B, ∀ b' ∈ B, ∀ r ∈ Px, ⁅b * b', r⁆ = ⁅b, r⁆ * ⁅b', r⁆ := by
    intro b hb b' hb' r hr
    have ha : ⁅b', r⁆ ∈ A := hcomm b' hb' r hr
    have hc : ⁅b, r⁆ ∈ A := hcomm b hb r hr
    rw [commutator_mul_left_pairing,
      conj_eq_self_of_mul_eq (hAcent _ ha b (Subgroup.mem_sup_left hb))]
    exact hAcomm _ ha _ hc
  have hΦex : ∀ b : ↥B, ∃ Φ : (↥Px ⧸ K₀.subgroupOf Px) →* ↥A,
      ∀ r : ↥Px, ((Φ (r : ↥Px ⧸ K₀.subgroupOf Px) : ↥A) : G) = ⁅(b : G), (r : G)⁆ := by
    intro b
    obtain ⟨χ, hχ⟩ : ∃ χ : ↥Px →* ↥A, ∀ r : ↥Px, ((χ r : ↥A) : G) = ⁅(b : G), (r : G)⁆ :=
      ⟨MonoidHom.mk' (fun r => ⟨⁅(b : G), (r : G)⁆, hcomm (b : G) b.2 (r : G) r.2⟩)
        (fun r r' => Subtype.ext (hmulR (b : G) b.2 (r : G) r.2 (r' : G) r'.2)), fun r => rfl⟩
    have hχk : K₀.subgroupOf Px ≤ χ.ker := by
      intro n hn
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hχ]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (hBK (b : G) b.2 (n : G) (Subgroup.mem_subgroupOf.mp hn))
    refine ⟨QuotientGroup.lift (K₀.subgroupOf Px) χ hχk, fun r => ?_⟩
    rw [QuotientGroup.lift_mk]
    exact hχ r
  choose Φ hΦ using hΦex
  have hΦmul : ∀ b b' : ↥B, Φ (b * b') = Φ b * Φ b' := by
    intro b b'
    refine MonoidHom.ext fun e => ?_
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective e
    apply Subtype.ext
    rw [hmulapp, Subgroup.coe_mul, hΦ, hΦ, hΦ, Subgroup.coe_mul]
    exact hmulB (b : G) b.2 (b' : G) b'.2 (r : G) r.2
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥B →* ((↥Px ⧸ K₀.subgroupOf Px) →* ↥A),
      ∀ (b : ↥B) (r : ↥Px), ((θ b) (r : ↥Px ⧸ K₀.subgroupOf Px) : G) = ⁅(b : G), (r : G)⁆ :=
    ⟨MonoidHom.mk' Φ (fun b b' => hΦmul b b'), fun b r => hΦ b r⟩
  have hkerB : ∀ b : ↥B, b ∈ θ.ker → (b : G) ∈ A := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    refine hker (b : G) b.2 fun r hr => ?_
    have h1 := hθ b ⟨r, hr⟩
    simp only [hb, MonoidHom.one_apply, Subgroup.coe_one] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1.symm
  have hθker_card : Nat.card θ.ker ≤ Nat.card A := by
    refine Nat.card_le_card_of_injective (fun x => (⟨(x.1 : G), hkerB x.1 x.2⟩ : ↥A)) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥A => (z : G)) hxy
  haveI : Finite ((↥Px ⧸ K₀.subgroupOf Px) →* ↥A) :=
    Finite.of_injective
      (fun f : (↥Px ⧸ K₀.subgroupOf Px) →* ↥A => (f : (↥Px ⧸ K₀.subgroupOf Px) → ↥A))
      DFunLike.coe_injective
  have hθrange_card : Nat.card θ.range ≤ Nat.card ((↥Px ⧸ K₀.subgroupOf Px) →* ↥A) :=
    Nat.card_le_card_of_injective (fun x => (x : (↥Px ⧸ K₀.subgroupOf Px) →* ↥A))
      Subtype.val_injective
  have hpow : Nat.card ((↥Px ⧸ K₀.subgroupOf Px) →* ↥A) ≤ Nat.card A ^ m :=
    natCard_monoidHom_le_pow hQexp hQcard
  calc Nat.card B = Nat.card θ.ker * Nat.card θ.range := by
        rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    _ ≤ Nat.card A * Nat.card ((↥Px ⧸ K₀.subgroupOf Px) →* ↥A) :=
        Nat.mul_le_mul hθker_card hθrange_card
    _ ≤ Nat.card A * Nat.card A ^ m := Nat.mul_le_mul le_rfl hpow

end CFSG.RankThree.GF2n.Tim79a

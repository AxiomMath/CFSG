module

public import Mathlib
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneAxioms

public section

namespace CFSG.Quasithin.A94.He42Plane

open CFSG.ComponentClassification.WittDesign

variable {L : Type} [Group L] [Finite L]

@[expose] def Inc (L₁ L₂ : Subgroup L) (p : L ⧸ L₁) (ℓ : L ⧸ L₂) : Prop :=
  ∃ g : L, (g : L ⧸ L₁) = p ∧ (g : L ⧸ L₂) = ℓ

open Classical in
noncomputable instance (L₁ : Subgroup L) : Fintype (L ⧸ L₁) := Fintype.ofFinite _

open Classical in
@[expose] noncomputable def pts (L₁ L₂ : Subgroup L) (ℓ : L ⧸ L₂) : Finset (L ⧸ L₁) :=
  Finset.univ.filter (fun p => Inc L₁ L₂ p ℓ)

open Classical in
@[expose] noncomputable def lineSet (L₁ L₂ : Subgroup L) : Finset (Finset (L ⧸ L₁)) :=
  Finset.univ.image (pts L₁ L₂)

theorem he42pl_mem_pts_iff (L₁ L₂ : Subgroup L) (p : L ⧸ L₁) (ℓ : L ⧸ L₂) :
    p ∈ pts L₁ L₂ ℓ ↔ Inc L₁ L₂ p ℓ := by
  simp [pts]

theorem he42pl_mem_lineSet {L₁ L₂ : Subgroup L} {M : Finset (L ⧸ L₁)} :
    M ∈ lineSet L₁ L₂ ↔ ∃ ℓ : L ⧸ L₂, pts L₁ L₂ ℓ = M := by
  simp [lineSet]

theorem he42pl_inc_iff_pt (L₁ L₂ : Subgroup L) (x y : L) :
    Inc L₁ L₂ (x : L ⧸ L₁) (y : L ⧸ L₂) ↔ ∃ a ∈ L₂, ((y * a : L) : L ⧸ L₁) = (x : L ⧸ L₁) := by
  constructor
  · rintro ⟨g, hg1, hg2⟩
    rw [QuotientGroup.eq] at hg2
    refine ⟨y⁻¹ * g, ?_, ?_⟩
    · simpa only [mul_inv_rev, inv_inv] using L₂.inv_mem hg2
    · rw [mul_inv_cancel_left]
      exact hg1
  · rintro ⟨a, ha, hax⟩
    refine ⟨y * a, hax, ?_⟩
    rw [QuotientGroup.eq]
    have e : (y * a)⁻¹ * y = a⁻¹ := by group
    rw [e]
    exact L₂.inv_mem ha

theorem he42pl_inc_iff_line (L₁ L₂ : Subgroup L) (x y : L) :
    Inc L₁ L₂ (x : L ⧸ L₁) (y : L ⧸ L₂) ↔ ∃ l ∈ L₁, ((x * l : L) : L ⧸ L₂) = (y : L ⧸ L₂) := by
  constructor
  · rintro ⟨g, hg1, hg2⟩
    rw [QuotientGroup.eq] at hg1
    refine ⟨x⁻¹ * g, ?_, ?_⟩
    · simpa only [mul_inv_rev, inv_inv] using L₁.inv_mem hg1
    · rw [mul_inv_cancel_left]
      exact hg2
  · rintro ⟨l, hl, hxl⟩
    refine ⟨x * l, ?_, hxl⟩
    rw [QuotientGroup.eq]
    have e : (x * l)⁻¹ * x = l⁻¹ := by group
    rw [e]
    exact L₁.inv_mem hl

theorem he42pl_inc_iff_exists (L₁ L₂ : Subgroup L) (x y : L) :
    Inc L₁ L₂ (x : L ⧸ L₁) (y : L ⧸ L₂) ↔ ∃ l₁ ∈ L₁, ∃ l₂ ∈ L₂, x * l₁ = y * l₂ := by
  constructor
  · intro h
    obtain ⟨a, ha, hax⟩ := (he42pl_inc_iff_pt L₁ L₂ x y).1 h
    rw [QuotientGroup.eq] at hax
    refine ⟨x⁻¹ * (y * a), ?_, a, ha, ?_⟩
    · simpa only [mul_inv_rev, inv_inv] using L₁.inv_mem hax
    · rw [mul_inv_cancel_left]
  · rintro ⟨l₁, hl₁, l₂, hl₂, h⟩
    refine (he42pl_inc_iff_line L₁ L₂ x y).2 ⟨l₁, hl₁, ?_⟩
    rw [h, QuotientGroup.eq]
    have e : (y * l₂)⁻¹ * y = l₂⁻¹ := by group
    rw [e]
    exact L₂.inv_mem hl₂

theorem he42pl_card_range_coset (A B : Subgroup L) (x : L) :
    Nat.card (Set.range fun a : A => ((x * (a : L) : L) : L ⧸ B)) = (A ⊓ B).relIndex A := by
  have hwd : ∀ a b : A, QuotientGroup.leftRel ((A ⊓ B).subgroupOf A) a b →
      ((x * (a : L) : L) : L ⧸ B) = ((x * (b : L) : L) : L ⧸ B) := by
    intro a b hab
    have h := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hab))
    rw [QuotientGroup.eq]
    have e : (x * (a : L))⁻¹ * (x * (b : L)) = (a : L)⁻¹ * (b : L) := by group
    rw [e]
    exact h.2
  obtain ⟨F, hF⟩ : ∃ F : A ⧸ (A ⊓ B).subgroupOf A → L ⧸ B,
      ∀ a : A, F (QuotientGroup.mk a) = ((x * (a : L) : L) : L ⧸ B) :=
    ⟨Quotient.lift (fun a : A => ((x * (a : L) : L) : L ⧸ B)) hwd, fun a => rfl⟩
  have hinj : Function.Injective F := by
    intro q₁ q₂ hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q₂
    rw [hF, hF, QuotientGroup.eq] at hq
    have e : (x * (a : L))⁻¹ * (x * (b : L)) = (a : L)⁻¹ * (b : L) := by group
    rw [e] at hq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.2 ⟨A.mul_mem (A.inv_mem a.2) b.2, hq⟩
  have hrange : Set.range F = Set.range (fun a : A => ((x * (a : L) : L) : L ⧸ B)) := by
    ext q
    constructor
    · rintro ⟨q', rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q'
      exact ⟨a, (hF a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨QuotientGroup.mk a, hF a⟩
  rw [← hrange, Nat.card_range_of_injective hinj]
  rfl

open Classical in
theorem he42pl_card_pts {L₁ L₂ : Subgroup L} (h5 : (L₁ ⊓ L₂).relIndex L₂ = 5) (y : L) :
    (pts L₁ L₂ (y : L ⧸ L₂)).card = 5 := by
  have hset : ((pts L₁ L₂ (y : L ⧸ L₂) : Finset (L ⧸ L₁)) : Set (L ⧸ L₁)) =
      Set.range fun a : L₂ => ((y * (a : L) : L) : L ⧸ L₁) := by
    ext p
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    rw [Finset.mem_coe, he42pl_mem_pts_iff, he42pl_inc_iff_pt, Set.mem_range]
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨⟨a, ha⟩, h⟩
    · rintro ⟨⟨a, ha⟩, h⟩
      exact ⟨a, ha, h⟩
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq, hset, he42pl_card_range_coset L₂ L₁ y,
    inf_comm]
  exact h5

open Classical in
theorem he42pl_card_lines_thru {L₁ L₂ : Subgroup L} (h5 : (L₁ ⊓ L₂).relIndex L₁ = 5) (x : L) :
    (Finset.univ.filter fun ℓ : L ⧸ L₂ => Inc L₁ L₂ (x : L ⧸ L₁) ℓ).card = 5 := by
  have hset : ((Finset.univ.filter fun ℓ : L ⧸ L₂ => Inc L₁ L₂ (x : L ⧸ L₁) ℓ :
      Finset (L ⧸ L₂)) : Set (L ⧸ L₂)) =
      Set.range fun l : L₁ => ((x * (l : L) : L) : L ⧸ L₂) := by
    ext ℓ
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ℓ
    rw [Finset.mem_coe, Finset.mem_filter, Set.mem_range]
    refine ⟨fun h => ?_, fun ⟨l, hl⟩ =>
      ⟨Finset.mem_univ _, (he42pl_inc_iff_line L₁ L₂ x y).2 ⟨l.1, l.2, hl⟩⟩⟩
    obtain ⟨l, hl, h'⟩ := (he42pl_inc_iff_line L₁ L₂ x y).1 h.2
    exact ⟨⟨l, hl⟩, h'⟩
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq, hset, he42pl_card_range_coset L₁ L₂ x]
  exact h5

theorem he42pl_exists_line {L₁ L₂ : Subgroup L}
    (hcov : ∀ g : L, ∃ h ∈ L₁, ∃ m ∈ L₂, ∃ h' ∈ L₁, g = h * m * h') (p q : L ⧸ L₁) :
    ∃ ℓ : L ⧸ L₂, Inc L₁ L₂ p ℓ ∧ Inc L₁ L₂ q ℓ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨h, hh, m, hm, h', hh', hz⟩ := hcov (x⁻¹ * z)
  refine ⟨((x * h : L) : L ⧸ L₂), (he42pl_inc_iff_line L₁ L₂ x (x * h)).2 ⟨h, hh, rfl⟩, ?_⟩
  rw [he42pl_inc_iff_pt]
  refine ⟨m, hm, ?_⟩
  rw [QuotientGroup.eq]
  have hz' : z = x * (h * m * h') := by rw [← hz, mul_inv_cancel_left]
  have e : (x * h * m)⁻¹ * z = h' := by rw [hz']; group
  rw [e]
  exact hh'

theorem he42pl_eq_line {L₁ L₂ : Subgroup L}
    (huniq : ∀ h ∈ L₁, ∀ g ∈ L₂, g ∉ L₁ → ∀ l ∈ L₁, ∀ m ∈ L₂, g * l = h * m → h ∈ L₂)
    {p q : L ⧸ L₁} (hpq : p ≠ q) {ℓ ℓ' : L ⧸ L₂} (hp : Inc L₁ L₂ p ℓ) (hq : Inc L₁ L₂ q ℓ)
    (hp' : Inc L₁ L₂ p ℓ') (hq' : Inc L₁ L₂ q ℓ') : ℓ = ℓ' := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ℓ
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective ℓ'
  obtain ⟨l, hl, hxl⟩ := (he42pl_inc_iff_line L₁ L₂ x y).1 hp
  obtain ⟨l', hl', hxl'⟩ := (he42pl_inc_iff_line L₁ L₂ x y').1 hp'
  rw [← hxl] at hq
  rw [← hxl'] at hq'
  rw [← hxl, ← hxl']
  obtain ⟨a, ha, hza⟩ := (he42pl_inc_iff_pt L₁ L₂ z (x * l)).1 hq
  obtain ⟨a', ha', hza'⟩ := (he42pl_inc_iff_pt L₁ L₂ z (x * l')).1 hq'
  have ha1 : a ∉ L₁ := by
    intro haL
    apply hpq
    have h1 : ((x * l * a : L) : L ⧸ L₁) = ((x * l : L) : L ⧸ L₁) := by
      rw [QuotientGroup.eq]
      have e : (x * l * a)⁻¹ * (x * l) = a⁻¹ := by group
      rw [e]
      exact L₁.inv_mem haL
    have h2 : ((x * l : L) : L ⧸ L₁) = (x : L ⧸ L₁) := by
      rw [QuotientGroup.eq]
      have e : (x * l)⁻¹ * x = l⁻¹ := by group
      rw [e]
      exact L₁.inv_mem hl
    exact h2.symm.trans (h1.symm.trans hza)
  have hc₁ : (x * l * a)⁻¹ * z ∈ L₁ := QuotientGroup.eq.1 hza
  have hc₂ : (x * l' * a')⁻¹ * z ∈ L₁ := QuotientGroup.eq.1 hza'
  obtain ⟨c₁, hc₁', hz₁⟩ : ∃ c ∈ L₁, z = x * l * a * c :=
    ⟨_, hc₁, (mul_inv_cancel_left _ _).symm⟩
  obtain ⟨c₂, hc₂', hz₂⟩ : ∃ c ∈ L₁, z = x * l' * a' * c :=
    ⟨_, hc₂, (mul_inv_cancel_left _ _).symm⟩
  have hkey : a * (c₁ * c₂⁻¹) = l⁻¹ * l' * a' := by
    have h := hz₁.symm.trans hz₂
    calc a * (c₁ * c₂⁻¹) = l⁻¹ * (x⁻¹ * (x * l * a * c₁)) * c₂⁻¹ := by group
      _ = l⁻¹ * (x⁻¹ * (x * l' * a' * c₂)) * c₂⁻¹ := by rw [h]
      _ = l⁻¹ * l' * a' := by group
  have hu := huniq (l⁻¹ * l') (L₁.mul_mem (L₁.inv_mem hl) hl') a ha ha1 (c₁ * c₂⁻¹)
    (L₁.mul_mem hc₁' (L₁.inv_mem hc₂')) a' ha' hkey
  rw [QuotientGroup.eq]
  have e : (x * l)⁻¹ * (x * l') = l⁻¹ * l' := by group
  rw [e]
  exact hu

open Classical in
theorem he42pl_card_of_incidence {P Q : Type} [Fintype P] [Fintype Q] (Inc' : P → Q → Prop)
    (p₀ : P) (h1 : ∀ p q : P, p ≠ q → ∃ ℓ, Inc' p ℓ ∧ Inc' q ℓ)
    (h2 : ∀ p q : P, ∀ ℓ ℓ' : Q, p ≠ q → Inc' p ℓ → Inc' q ℓ → Inc' p ℓ' → Inc' q ℓ' → ℓ = ℓ')
    (h3 : ∀ ℓ : Q, (Finset.univ.filter fun p => Inc' p ℓ).card = 5)
    (h4 : (Finset.univ.filter fun ℓ => Inc' p₀ ℓ).card = 5) :
    Fintype.card P = 21 := by
  have hcover : Finset.univ.erase p₀ =
      (Finset.univ.filter fun ℓ => Inc' p₀ ℓ).biUnion
        fun ℓ => (Finset.univ.filter fun p => Inc' p ℓ).erase p₀ := by
    ext q
    constructor
    · intro hq
      rw [Finset.mem_erase] at hq
      obtain ⟨ℓ, hpℓ, hqℓ⟩ := h1 p₀ q (Ne.symm hq.1)
      exact Finset.mem_biUnion.2 ⟨ℓ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpℓ⟩,
        Finset.mem_erase.2 ⟨hq.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hqℓ⟩⟩⟩
    · intro hq
      obtain ⟨ℓ, -, hq'⟩ := Finset.mem_biUnion.1 hq
      exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hq').1, Finset.mem_univ _⟩
  have hdisj : (((Finset.univ.filter fun ℓ => Inc' p₀ ℓ) : Finset Q) : Set Q).PairwiseDisjoint
      fun ℓ => (Finset.univ.filter fun p => Inc' p ℓ).erase p₀ := by
    intro ℓ hℓ ℓ' hℓ' hne
    rw [Finset.mem_coe, Finset.mem_filter] at hℓ hℓ'
    refine Finset.disjoint_left.2 fun q hq hq' => hne ?_
    obtain ⟨hqp, hq⟩ := Finset.mem_erase.1 hq
    obtain ⟨-, hq'⟩ := Finset.mem_erase.1 hq'
    exact h2 p₀ q ℓ ℓ' (Ne.symm hqp) hℓ.2 (Finset.mem_filter.1 hq).2 hℓ'.2
      (Finset.mem_filter.1 hq').2
  have hterm : ∀ ℓ ∈ Finset.univ.filter (fun ℓ => Inc' p₀ ℓ),
      ((Finset.univ.filter fun p => Inc' p ℓ).erase p₀).card = 4 := by
    intro ℓ hℓ
    have hp : p₀ ∈ Finset.univ.filter (fun p => Inc' p ℓ) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hℓ).2⟩
    have e1 := Finset.card_erase_of_mem hp
    have e2 := h3 ℓ
    omega
  have hsum : (Finset.univ.erase p₀).card = 20 := by
    rw [hcover, Finset.card_biUnion hdisj, Finset.sum_congr rfl hterm, Finset.sum_const, h4,
      smul_eq_mul] <;> norm_num
  have hpos : 0 < (Finset.univ : Finset P).card := Finset.card_pos.2 ⟨p₀, Finset.mem_univ _⟩
  have herase := Finset.card_erase_of_mem (Finset.mem_univ p₀)
  rw [← Finset.card_univ]
  omega

open Classical in
theorem isSteinerPlane_lineSet {L₁ L₂ : Subgroup L} (h5₁ : (L₁ ⊓ L₂).relIndex L₁ = 5)
    (h5₂ : (L₁ ⊓ L₂).relIndex L₂ = 5)
    (hcov : ∀ g : L, ∃ h ∈ L₁, ∃ m ∈ L₂, ∃ h' ∈ L₁, g = h * m * h')
    (huniq : ∀ h ∈ L₁, ∀ g ∈ L₂, g ∉ L₁ → ∀ l ∈ L₁, ∀ m ∈ L₂, g * l = h * m → h ∈ L₂) :
    IsSteinerPlane (lineSet L₁ L₂) := by
  have h1 : ∀ p q : L ⧸ L₁, p ≠ q → ∃ ℓ : L ⧸ L₂, Inc L₁ L₂ p ℓ ∧ Inc L₁ L₂ q ℓ :=
    fun p q _ => he42pl_exists_line hcov p q
  have h2 : ∀ p q : L ⧸ L₁, ∀ ℓ ℓ' : L ⧸ L₂, p ≠ q → Inc L₁ L₂ p ℓ → Inc L₁ L₂ q ℓ →
      Inc L₁ L₂ p ℓ' → Inc L₁ L₂ q ℓ' → ℓ = ℓ' :=
    fun _ _ _ _ hpq hp hq hp' hq' => he42pl_eq_line huniq hpq hp hq hp' hq'
  have h3 : ∀ ℓ : L ⧸ L₂, (Finset.univ.filter fun p => Inc L₁ L₂ p ℓ).card = 5 := by
    intro ℓ
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ℓ
    exact he42pl_card_pts h5₂ y
  have hcard : Fintype.card (L ⧸ L₁) = 21 :=
    he42pl_card_of_incidence (fun p ℓ => Inc L₁ L₂ p ℓ) ((1 : L) : L ⧸ L₁) h1 h2 h3
      (he42pl_card_lines_thru h5₁ 1)
  unfold IsSteinerPlane
  refine ⟨hcard, ?_, ?_⟩
  · intro M hM
    obtain ⟨ℓ, rfl⟩ := he42pl_mem_lineSet.1 hM
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ℓ
    exact he42pl_card_pts h5₂ y
  · intro T hT
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 hT
    obtain ⟨ℓ₀, hp₀, hq₀⟩ := h1 p q hpq
    refine ⟨pts L₁ L₂ ℓ₀, ⟨he42pl_mem_lineSet.2 ⟨ℓ₀, rfl⟩, ?_⟩, ?_⟩
    · exact Finset.insert_subset_iff.2
        ⟨(he42pl_mem_pts_iff L₁ L₂ p ℓ₀).2 hp₀,
          Finset.singleton_subset_iff.2 ((he42pl_mem_pts_iff L₁ L₂ q ℓ₀).2 hq₀)⟩
    · rintro M ⟨hM, hsub⟩
      obtain ⟨ℓ, rfl⟩ := he42pl_mem_lineSet.1 hM
      have hp1 : Inc L₁ L₂ p ℓ :=
        (he42pl_mem_pts_iff L₁ L₂ p ℓ).1 (hsub (Finset.mem_insert_self _ _))
      have hq1 : Inc L₁ L₂ q ℓ :=
        (he42pl_mem_pts_iff L₁ L₂ q ℓ).1
          (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      rw [h2 p q ℓ ℓ₀ hpq hp1 hq1 hp₀ hq₀]

end CFSG.Quasithin.A94.He42Plane

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Pair

variable {Q : Type*} [Group Q]

theorem exists_mul_of_mem_sup {A₁ A₂ : Subgroup Q} (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    {x : Q} (hx : x ∈ A₁ ⊔ A₂) : ∃ a ∈ A₁, ∃ b ∈ A₂, x = a * b := by
  let S : Subgroup Q :=
    { carrier := {x | ∃ a ∈ A₁, ∃ b ∈ A₂, x = a * b}
      one_mem' := ⟨1, A₁.one_mem, 1, A₂.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A₁.mul_mem ha ha', b * b', A₂.mul_mem hb hb', ?_⟩
        have h := hc a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A₁.inv_mem ha, b⁻¹, A₂.inv_mem hb, ?_⟩
        have h := hc a⁻¹ (A₁.inv_mem ha) b⁻¹ (A₂.inv_mem hb)
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := h.symm }
  have hA₁ : A₁ ≤ S := fun a ha => ⟨a, ha, 1, A₂.one_mem, by simp⟩
  have hA₂ : A₂ ≤ S := fun b hb => ⟨1, A₁.one_mem, b, hb, by simp⟩
  exact sup_le hA₁ hA₂ hx

theorem eq_of_isSubnormal_of_simple {A X : Subgroup Q} [IsSimpleGroup ↥A] (hX : IsSubnormal X A)
    (hne : X ≠ ⊥) : X = A := by
  by_contra hXA
  have hlt : X < A := lt_of_le_of_ne (A3.subnormal_le hX) hXA
  obtain ⟨P, hPA, hPn, hXP⟩ := A3.subnormal_exists_normal_of_lt hX hlt
  rcases hPn.eq_bot_or_eq_top with h | h
  · apply hne
    rw [Subgroup.subgroupOf_eq_bot] at h
    apply le_bot_iff.mp
    intro x hx
    have hxP : x ∈ P := hXP hx
    have hxA : x ∈ A := A3.subnormal_le hX hx
    have : x ∈ P ⊓ A := ⟨hxP, hxA⟩
    rw [h.eq_bot] at this
    exact this
  · rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd hPA (not_lt_of_ge h)

theorem exists_noncomm_of_simple {A : Subgroup Q} [IsSimpleGroup ↥A]
    (hna : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) {a : Q} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∃ x ∈ A, a * x ≠ x * a := by
  by_contra hcon
  push Not at hcon
  have hz : (⟨a, ha⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcon g g.2).symm
  rcases (inferInstance : (Subgroup.center ↥A).Normal).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact ha1 (congrArg Subtype.val hz)
  · obtain ⟨x, hx, y, hy, hxy⟩ := hna
    apply hxy
    have : (⟨x, hx⟩ : ↥A) ∈ Subgroup.center ↥A := by rw [h]; exact Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp this ⟨y, hy⟩).symm

theorem eq_bot_of_commute_of_simple {A₁ A₂ : Subgroup Q} [IsSimpleGroup ↥A₁]
    (hna : ∃ x ∈ A₁, ∃ y ∈ A₁, x * y ≠ y * x) (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) :
    A₁ ⊓ A₂ = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  by_contra h1
  obtain ⟨x, hx, hax⟩ :=
    exists_noncomm_of_simple hna ha.1 (fun h => h1 (by rw [h]; exact Subgroup.one_mem _))
  exact hax (hc x hx a ha.2).symm

theorem normal_subgroupOf_inf_of_le {A B P : Subgroup Q} (hA : A ≤ B)
    (hP : (P.subgroupOf B).Normal) : ((P ⊓ A).subgroupOf A).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 : (⟨(n : Q), hA n.2⟩ : ↥B) ∈ P.subgroupOf B := Subgroup.mem_subgroupOf.mpr hn.1
  have h2 := hP.conj_mem _ h1 ⟨(g : Q), hA g.2⟩
  exact ⟨Subgroup.mem_subgroupOf.mp h2, A.mul_mem (A.mul_mem g.2 n.2) (A.inv_mem g.2)⟩

theorem le_of_mem_normal_of_ne_one {A₁ A₂ P : Subgroup Q} [IsSimpleGroup ↥A₁]
    (hna₁ : ∃ x ∈ A₁, ∃ y ∈ A₁, x * y ≠ y * x) (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hP : (P.subgroupOf (A₁ ⊔ A₂)).Normal) {a b : Q} (ha : a ∈ A₁) (hb : b ∈ A₂)
    (hab : a * b ∈ P) (ha1 : a ≠ 1) : A₁ ≤ P := by
  obtain ⟨x, hx, hax⟩ := exists_noncomm_of_simple hna₁ ha ha1
  have hCn : ((P ⊓ A₁).subgroupOf A₁).Normal :=
    normal_subgroupOf_inf_of_le (le_sup_left : A₁ ≤ A₁ ⊔ A₂) hP
  have hxb : x * b = b * x := hc x hx b hb
  have hbx : b * x * b⁻¹ = x := by
    rw [← hxb]
    simp
  have hconj : (a * b) * x * (a * b)⁻¹ = a * x * a⁻¹ := by
    calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [hbx]
  have hcc : a * x * a⁻¹ * x⁻¹ = (a * b) * (x * (a * b)⁻¹ * x⁻¹) := by
    calc a * x * a⁻¹ * x⁻¹ = ((a * b) * x * (a * b)⁻¹) * x⁻¹ := by rw [hconj]
      _ = (a * b) * (x * (a * b)⁻¹ * x⁻¹) := by group
  have hab' : a * b ∈ A₁ ⊔ A₂ := Subgroup.mul_mem_sup ha hb
  have hconjP : x * (a * b)⁻¹ * x⁻¹ ∈ P := by
    have h1 : (⟨(a * b)⁻¹, A₁⊔A₂ |>.inv_mem hab'⟩ : ↥(A₁ ⊔ A₂)) ∈ P.subgroupOf (A₁ ⊔ A₂) :=
      Subgroup.mem_subgroupOf.mpr (P.inv_mem hab)
    have h2 := hP.conj_mem _ h1 ⟨x, Subgroup.mem_sup_left hx⟩
    simpa using Subgroup.mem_subgroupOf.mp h2
  have hcP : a * x * a⁻¹ * x⁻¹ ∈ P := by
    rw [hcc]
    exact P.mul_mem hab hconjP
  have hcA : a * x * a⁻¹ * x⁻¹ ∈ A₁ :=
    A₁.mul_mem (A₁.mul_mem (A₁.mul_mem ha hx) (A₁.inv_mem ha)) (A₁.inv_mem hx)
  have hc1 : a * x * a⁻¹ * x⁻¹ ≠ 1 := by
    intro h
    apply hax
    calc a * x = (a * x * a⁻¹ * x⁻¹) * (x * a) := by group
      _ = x * a := by rw [h, one_mul]
  have hmem : (⟨a * x * a⁻¹ * x⁻¹, hcA⟩ : ↥A₁) ∈ (P ⊓ A₁).subgroupOf A₁ :=
    Subgroup.mem_subgroupOf.mpr ⟨hcP, hcA⟩
  rcases hCn.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.mem_bot] at hmem
    exact absurd (congrArg Subtype.val hmem) hc1
  · rw [Subgroup.subgroupOf_eq_top] at h
    exact h.trans inf_le_left

theorem le_of_normal_pair {A₁ A₂ P : Subgroup Q} [IsSimpleGroup ↥A₁] [IsSimpleGroup ↥A₂]
    (hna₁ : ∃ x ∈ A₁, ∃ y ∈ A₁, x * y ≠ y * x) (hna₂ : ∃ x ∈ A₂, ∃ y ∈ A₂, x * y ≠ y * x)
    (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hP : (P.subgroupOf (A₁ ⊔ A₂)).Normal)
    (hPle : P ≤ A₁ ⊔ A₂) (hne : P ≠ ⊥) : A₁ ≤ P ∨ A₂ ≤ P := by
  obtain ⟨p, hpP, hp1⟩ : ∃ p ∈ P, p ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall P).mpr hcon)
  obtain ⟨a, ha, b, hb, hpab⟩ := exists_mul_of_mem_sup hc (hPle hpP)
  have hpP' : a * b ∈ P := by rw [← hpab]; exact hpP
  by_cases ha1 : a = 1
  · right
    have hb1 : b ≠ 1 := by
      intro hb1
      apply hp1
      rw [hpab, ha1, hb1]
      simp
    have hP' : (P.subgroupOf (A₂ ⊔ A₁)).Normal := by rwa [sup_comm]
    exact le_of_mem_normal_of_ne_one hna₂ (fun b hb a ha => (hc a ha b hb).symm) hP' hb ha
      (by simpa [ha1] using hpP') hb1
  · left
    exact le_of_mem_normal_of_ne_one hna₁ hc hP ha hb hpP' ha1

theorem eq_of_normal_of_le_of_lt {A₁ A₂ P : Subgroup Q} [IsSimpleGroup ↥A₂]
    (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hP : (P.subgroupOf (A₁ ⊔ A₂)).Normal)
    (h1 : A₁ ≤ P) (hlt : P < A₁ ⊔ A₂) : P = A₁ := by
  have hPle : P ≤ A₁ ⊔ A₂ := hlt.le
  have hn2 : ((P ⊓ A₂).subgroupOf A₂).Normal :=
    normal_subgroupOf_inf_of_le (le_sup_right : A₂ ≤ A₁ ⊔ A₂) hP
  refine le_antisymm (fun p hp => ?_) h1
  obtain ⟨a, ha, b, hb, hpab⟩ := exists_mul_of_mem_sup hc (hPle hp)
  have hbP : b ∈ P := by
    have : a⁻¹ * p ∈ P := P.mul_mem (P.inv_mem (h1 ha)) hp
    rw [hpab] at this
    simpa using this
  rcases hn2.eq_bot_or_eq_top with h | h
  · have hmem : (⟨b, hb⟩ : ↥A₂) ∈ (P ⊓ A₂).subgroupOf A₂ := Subgroup.mem_subgroupOf.mpr ⟨hbP, hb⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hb1 : b = 1 := congrArg Subtype.val hmem
    rw [hpab, hb1, mul_one]
    exact ha
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h
    have : A₁ ⊔ A₂ ≤ P := sup_le h1 (h.trans inf_le_left)
    exact absurd hlt (not_lt_of_ge this)

theorem classify_subnormal {A₁ A₂ X : Subgroup Q} [IsSimpleGroup ↥A₁] [IsSimpleGroup ↥A₂]
    (hna₁ : ∃ x ∈ A₁, ∃ y ∈ A₁, x * y ≠ y * x) (hna₂ : ∃ x ∈ A₂, ∃ y ∈ A₂, x * y ≠ y * x)
    (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hX : IsSubnormal X (A₁ ⊔ A₂)) (hne : X ≠ ⊥) :
    X = A₁ ∨ X = A₂ ∨ X = A₁ ⊔ A₂ := by
  by_cases hXtop : X = A₁ ⊔ A₂
  · exact Or.inr (Or.inr hXtop)
  have hlt : X < A₁ ⊔ A₂ := lt_of_le_of_ne (A3.subnormal_le hX) hXtop
  obtain ⟨P, hPlt, hPn, hXP⟩ := A3.subnormal_exists_normal_of_lt hX hlt
  have hPne : P ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hXP))
  have hP1 : P = A₁ ∨ P = A₂ := by
    rcases le_of_normal_pair hna₁ hna₂ hc hPn hPlt.le hPne with h1 | h2
    · exact Or.inl (eq_of_normal_of_le_of_lt hc hPn h1 hPlt)
    · refine Or.inr (eq_of_normal_of_le_of_lt (A₁ := A₂) (A₂ := A₁)
        (fun b hb a ha => (hc a ha b hb).symm) (by rwa [sup_comm]) h2 (by rwa [sup_comm]))
  rcases hP1 with rfl | rfl
  · left
    exact eq_of_isSubnormal_of_simple (A3.subnormal_of_le_of_le hX hXP le_sup_left) hne
  · right; left
    exact eq_of_isSubnormal_of_simple (A3.subnormal_of_le_of_le hX hXP le_sup_right) hne

theorem conj_mem_right_of_mem_sup {A₁ A₂ : Subgroup Q} (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    {g : Q} (hg : g ∈ A₁ ⊔ A₂) {x : Q} (hx : x ∈ A₂) : g * x * g⁻¹ ∈ A₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hg
  have hxb : b * x * b⁻¹ ∈ A₂ := A₂.mul_mem (A₂.mul_mem hb hx) (A₂.inv_mem hb)
  have h := hc a ha (b * x * b⁻¹) hxb
  have h2 : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
  rw [h2, h]
  simpa using hxb

theorem conj_mem_left_of_mem_sup {A₁ A₂ : Subgroup Q} (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    {g : Q} (hg : g ∈ A₁ ⊔ A₂) {x : Q} (hx : x ∈ A₁) : g * x * g⁻¹ ∈ A₁ :=
  conj_mem_right_of_mem_sup (A₁ := A₂) (A₂ := A₁) (fun b hb a ha => (hc a ha b hb).symm)
    (by rwa [sup_comm]) hx

theorem normal_subgroupOf_sup_left {A₁ A₂ : Subgroup Q} (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) :
    (A₁.subgroupOf (A₁ ⊔ A₂)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr fun g hg => ?_
  refine B6.mem_normalizer_of_forall_mem (fun x hx => conj_mem_left_of_mem_sup hc hg hx)
    (fun x hx => ?_)
  simpa using conj_mem_left_of_mem_sup hc ((A₁ ⊔ A₂).inv_mem hg) hx

theorem map_conj_eq_of_swap {A₁ A₂ : Subgroup Q} [IsSimpleGroup ↥A₁] [IsSimpleGroup ↥A₂]
    (hna₁ : ∃ x ∈ A₁, ∃ y ∈ A₁, x * y ≠ y * x) (hna₂ : ∃ x ∈ A₂, ∃ y ∈ A₂, x * y ≠ y * x)
    (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hnorm : (A₁ ⊔ A₂).Normal) {τ : Q}
    (hA₂ : A₂ = A₁.map (MulAut.conj τ).toMonoidHom) :
    A₂.map (MulAut.conj τ).toMonoidHom = A₁ := by
  have hint : A₁ ⊓ A₂ = ⊥ := eq_bot_of_commute_of_simple hna₁ hc
  have hA₁ne : A₁ ≠ ⊥ := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hna₁
    intro h
    rw [h, Subgroup.mem_bot] at hx hy
    exact hxy (by rw [hx, hy])
  have hA₂ne : A₂ ≠ ⊥ := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hna₂
    intro h
    rw [h, Subgroup.mem_bot] at hx hy
    exact hxy (by rw [hx, hy])
  have hnormτ : (A₁ ⊔ A₂).map (MulAut.conj τ).toMonoidHom = A₁ ⊔ A₂ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hnorm.conj_mem x hx τ
    · intro x hx
      refine ⟨τ⁻¹ * x * τ, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      simpa using hnorm.conj_mem x hx τ⁻¹
  set A₃ : Subgroup Q := A₂.map (MulAut.conj τ).toMonoidHom with hA₃
  have hA₃le : A₃ ≤ A₁ ⊔ A₂ := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hnorm.conj_mem x (Subgroup.mem_sup_right hx) τ
  have hA₃n : (A₃.subgroupOf (A₁ ⊔ A₂)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := hn
    have hg' : τ⁻¹ * (g : Q) * τ ∈ A₁ ⊔ A₂ := by
      simpa using hnorm.conj_mem (g : Q) g.2 τ⁻¹
    refine ⟨τ⁻¹ * (g : Q) * τ * x * (τ⁻¹ * (g : Q) * τ)⁻¹, ?_, ?_⟩
    · exact conj_mem_right_of_mem_sup hc hg' hx
    · have e : (MulAut.conj τ).toMonoidHom (τ⁻¹ * (g : Q) * τ * x * (τ⁻¹ * (g : Q) * τ)⁻¹) =
          (g : Q) * ((MulAut.conj τ).toMonoidHom x) * (g : Q)⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e, hxn]
      simp
  have hA₃ne : A₃ ≠ ⊥ := by
    intro h
    apply hA₂ne
    have := congrArg (Subgroup.map (MulAut.conj τ⁻¹).toMonoidHom) h
    rw [hA₃, Subgroup.map_map] at this
    have h2 : (MulAut.conj τ⁻¹).toMonoidHom.comp (MulAut.conj τ).toMonoidHom = MonoidHom.id Q := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [h2, Subgroup.map_id, Subgroup.map_bot] at this
    exact this
  rcases classify_subnormal hna₁ hna₂ hc (A3.subnormal_of_normal hA₃le hA₃n) hA₃ne with h | h | h
  · exact h
  · exfalso
    apply hA₁ne
    have h1 : A₁.map (MulAut.conj τ).toMonoidHom = A₂.map (MulAut.conj τ).toMonoidHom := by
      rw [← hA₂, ← hA₃, h]
    have h12 : A₁ = A₂ := Subgroup.map_injective (MulAut.conj τ).injective h1
    calc A₁ = A₁ ⊓ A₁ := (inf_idem A₁).symm
      _ = A₁ ⊓ A₂ := by rw [← h12]
      _ = ⊥ := hint
  · exfalso
    apply hA₁ne
    have h1 : A₂ = A₁ ⊔ A₂ :=
      Subgroup.map_injective (MulAut.conj τ).injective (h.trans hnormτ.symm)
    have hle : A₁ ≤ A₂ := h1 ▸ le_sup_left
    rw [← inf_eq_left.mpr hle]
    exact hint

@[expose] noncomputable def sylowOfIsSylowTwoOf [Finite Q] {S A : Subgroup Q}
    (h : IsSylowTwoOf S A) : Sylow 2 ↥A :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm).toSylow h.2.2

theorem coe_sylowOfIsSylowTwoOf [Finite Q] {S A : Subgroup Q} (h : IsSylowTwoOf S A) :
    ((sylowOfIsSylowTwoOf h : Sylow 2 ↥A) : Subgroup ↥A) = S.subgroupOf A := rfl

theorem mem_of_mul_mem_of_isSylowTwoOf [Finite Q] {A₁ A₂ P : Subgroup Q}
    (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hint : A₁ ⊓ A₂ = ⊥) (hP2 : IsPGroup 2 P)
    (hS : IsSylowTwoOf (P ⊓ A₁) A₁) {a b : Q} (ha : a ∈ A₁) (hb : b ∈ A₂) (hab : a * b ∈ P) :
    a ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ x ∈ A₁, a * x * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by
    intro x hxA
    have hxb : x * b = b * x := hc x hxA b hb
    have h2 : (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    rw [h2, ← hxb]
    simp
  have hnormS : a ∈ Subgroup.normalizer ((P ⊓ A₁ : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxP, hxA⟩
      refine ⟨?_, A₁.mul_mem (A₁.mul_mem ha hxA) (A₁.inv_mem ha)⟩
      rw [hconj x hxA]
      exact P.mul_mem (P.mul_mem hab hxP) (P.inv_mem hab)
    · rintro ⟨hxP, hxA⟩
      have hxA' : x ∈ A₁ := by
        have := A₁.mul_mem (A₁.mul_mem (A₁.inv_mem ha) hxA) ha
        simpa [mul_assoc] using this
      refine ⟨?_, hxA'⟩
      have hx : x = (a * b)⁻¹ * (a * x * a⁻¹) * (a * b) := by
        rw [hconj x hxA']
        group
      rw [hx]
      exact P.mul_mem (P.mul_mem (P.inv_mem hab) hxP) hab
  obtain ⟨k, hk⟩ := hP2 ⟨a * b, hab⟩
  have hk' : (a * b) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hcomm : Commute a b := hc a ha b hb
  have h2 : a ^ (2 ^ k) * b ^ (2 ^ k) = 1 := by rw [← hcomm.mul_pow]; exact hk'
  have h3 : a ^ (2 ^ k) = 1 := by
    have hmem : a ^ (2 ^ k) ∈ A₁ ⊓ A₂ := by
      refine ⟨A₁.pow_mem ha _, ?_⟩
      have : a ^ (2 ^ k) = (b ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [this]
      exact A₂.inv_mem (A₂.pow_mem hb _)
    rw [hint] at hmem
    exact hmem
  set SA : Sylow 2 ↥A₁ := sylowOfIsSylowTwoOf hS with hSA
  have hW2 : IsPGroup 2 (Subgroup.zpowers (⟨a, ha⟩ : ↥A₁)) := by
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext h3)
  have hWN : Subgroup.zpowers (⟨a, ha⟩ : ↥A₁) ≤
      Subgroup.normalizer ((SA : Subgroup ↥A₁) : Set ↥A₁) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := (Subgroup.mem_normalizer_iff.mp hnormS) (x : Q)
    rw [hSA, coe_sylowOfIsSylowTwoOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using this
  have hinf : Subgroup.zpowers (⟨a, ha⟩ : ↥A₁) ⊓
      Subgroup.normalizer ((SA : Subgroup ↥A₁) : Set ↥A₁) =
      Subgroup.zpowers (⟨a, ha⟩ : ↥A₁) ⊓ (SA : Subgroup ↥A₁) := hW2.inf_normalizer_sylow SA
  have hmemW : (⟨a, ha⟩ : ↥A₁) ∈ Subgroup.zpowers (⟨a, ha⟩ : ↥A₁) ⊓
      Subgroup.normalizer ((SA : Subgroup ↥A₁) : Set ↥A₁) :=
    ⟨Subgroup.mem_zpowers _, hWN (Subgroup.mem_zpowers _)⟩
  rw [hinf] at hmemW
  have h5 : (⟨a, ha⟩ : ↥A₁) ∈ (SA : Subgroup ↥A₁) := hmemW.2
  rw [hSA, coe_sylowOfIsSylowTwoOf, Subgroup.mem_subgroupOf] at h5
  exact h5.1

theorem pair_overgroup [Finite Q] {A₁ A₂ P Y : Subgroup Q} {τ : Q} [IsSimpleGroup ↥A₁]
    [IsSimpleGroup ↥A₂] (hna₁ : ∃ x ∈ A₁, ∃ y ∈ A₁, x * y ≠ y * x)
    (hna₂ : ∃ x ∈ A₂, ∃ y ∈ A₂, x * y ≠ y * x) (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hnorm : (A₁ ⊔ A₂).Normal) (hA₂ : A₂ = A₁.map (MulAut.conj τ).toMonoidHom)
    (hP2 : IsPGroup 2 P) (hS₁ : IsSylowTwoOf (P ⊓ A₁) A₁) (hS₁ne : P ⊓ A₁ ≠ ⊥) (hτP : τ ∈ P)
    (hPY : P ≤ Y)
    (hB : ∀ S R : Subgroup Q, IsSylowTwoOf S A₁ → S ≤ R → R ≤ A₁ →
      R ≤ Subgroup.normalizer (S : Set Q) ∨ A₁ ≤ R) :
    A₁ ⊔ A₂ ≤ Y ∨ ∀ z ∈ Y ⊓ (A₁ ⊔ A₂), ∀ s ∈ P ⊓ (A₁ ⊔ A₂), z * s * z⁻¹ ∈ P := by
  have hint : A₁ ⊓ A₂ = ⊥ := eq_bot_of_commute_of_simple hna₁ hc
  have hswap := map_conj_eq_of_swap hna₁ hna₂ hc hnorm hA₂
  have hτY : τ ∈ Y := hPY hτP
  have hτA₂ : ∀ x ∈ A₂, τ⁻¹ * x * τ ∈ A₁ := fun x hx => by
    rw [hA₂] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [MulAut.conj_apply, mul_assoc] using hy
  have hτA₁' : ∀ x ∈ A₁, τ⁻¹ * x * τ ∈ A₂ := fun x hx => by
    rw [← hswap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [MulAut.conj_apply, mul_assoc] using hy
  set Z : Subgroup Q := Y ⊓ (A₁ ⊔ A₂) with hZ
  have hZτ : ∀ z ∈ Z, τ * z * τ⁻¹ ∈ Z := fun z hz =>
    ⟨Y.mul_mem (Y.mul_mem hτY hz.1) (Y.inv_mem hτY), hnorm.conj_mem z hz.2 τ⟩
  have hZτ' : ∀ z ∈ Z, τ⁻¹ * z * τ ∈ Z := fun z hz =>
    ⟨Y.mul_mem (Y.mul_mem (Y.inv_mem hτY) hz.1) hτY, by simpa using hnorm.conj_mem z hz.2 τ⁻¹⟩
  let Z₁ : Subgroup Q :=
    { carrier := {a | a ∈ A₁ ∧ ∃ b ∈ A₂, a * b ∈ Z}
      one_mem' := ⟨A₁.one_mem, 1, A₂.one_mem, by rw [mul_one]; exact Z.one_mem⟩
      mul_mem' := by
        rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
        refine ⟨A₁.mul_mem ha ha', b * b', A₂.mul_mem hb hb', ?_⟩
        have e : a * a' * (b * b') = (a * b) * (a' * b') := by
          calc a * a' * (b * b') = a * (a' * b) * b' := by group
            _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
            _ = a * b * (a' * b') := by group
        rw [e]
        exact Z.mul_mem hab hab'
      inv_mem' := by
        rintro a ⟨ha, b, hb, hab⟩
        refine ⟨A₁.inv_mem ha, b⁻¹, A₂.inv_mem hb, ?_⟩
        have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
          have h := hc a⁻¹ (A₁.inv_mem ha) b⁻¹ (A₂.inv_mem hb)
          rw [h]; group
        rw [e]
        exact Z.inv_mem hab }
  have hS₁Z₁ : P ⊓ A₁ ≤ Z₁ := fun s hs =>
    ⟨hs.2, 1, A₂.one_mem, by rw [mul_one]; exact ⟨hPY hs.1, Subgroup.mem_sup_left hs.2⟩⟩
  have hZ₁A₁ : Z₁ ≤ A₁ := fun a ha => ha.1
  rcases hB (P ⊓ A₁) Z₁ hS₁ hS₁Z₁ hZ₁A₁ with hN | hfull
  · right
    intro z hz s hs
    obtain ⟨a, ha, b, hb, hzab⟩ := exists_mul_of_mem_sup hc hz.2
    obtain ⟨a', ha', b', hb', hsab⟩ := exists_mul_of_mem_sup hc hs.2
    have hzZ : a * b ∈ Z := by rw [← hzab]; exact hz
    have haN : a ∈ Subgroup.normalizer ((P ⊓ A₁ : Subgroup Q) : Set Q) := hN ⟨ha, b, hb, hzZ⟩
    have ha₀ : τ⁻¹ * b * τ ∈ A₁ := hτA₂ b hb
    have hb₀ : τ⁻¹ * a * τ ∈ A₂ := hτA₁' a ha
    have hz₀ : (τ⁻¹ * b * τ) * (τ⁻¹ * a * τ) ∈ Z := by
      have h1 := hZτ' _ hzZ
      have e : τ⁻¹ * (a * b) * τ = (τ⁻¹ * b * τ) * (τ⁻¹ * a * τ) := by
        have h2 := hc (τ⁻¹ * b * τ) ha₀ (τ⁻¹ * a * τ) hb₀
        rw [h2]; group
      rw [e] at h1
      exact h1
    have ha₀N : τ⁻¹ * b * τ ∈ Subgroup.normalizer ((P ⊓ A₁ : Subgroup Q) : Set Q) :=
      hN ⟨ha₀, τ⁻¹ * a * τ, hb₀, hz₀⟩
    have hsP : a' * b' ∈ P := by rw [← hsab]; exact hs.1
    have ha'P : a' ∈ P := mem_of_mul_mem_of_isSylowTwoOf hc hint hP2 hS₁ ha' hb' hsP
    have ha'' : τ⁻¹ * b' * τ ∈ A₁ := hτA₂ b' hb'
    have hb'' : τ⁻¹ * a' * τ ∈ A₂ := hτA₁' a' ha'
    have hsP' : (τ⁻¹ * b' * τ) * (τ⁻¹ * a' * τ) ∈ P := by
      have e : (τ⁻¹ * b' * τ) * (τ⁻¹ * a' * τ) = τ⁻¹ * (a' * b') * τ := by
        have h2 := hc (τ⁻¹ * b' * τ) ha'' (τ⁻¹ * a' * τ) hb''
        rw [h2]; group
      rw [e]
      exact P.mul_mem (P.mul_mem (P.inv_mem hτP) hsP) hτP
    have ha''P : τ⁻¹ * b' * τ ∈ P := mem_of_mul_mem_of_isSylowTwoOf hc hint hP2 hS₁ ha'' hb'' hsP'
    have hb'P : b' ∈ P := by
      have := P.mul_mem (P.mul_mem hτP ha''P) (P.inv_mem hτP)
      simpa [mul_assoc] using this
    have h1 : a * a' * a⁻¹ ∈ P ⊓ A₁ :=
      (Subgroup.mem_normalizer_iff.mp haN a').mp ⟨ha'P, ha'⟩
    have h2 : (τ⁻¹ * b * τ) * (τ⁻¹ * b' * τ) * (τ⁻¹ * b * τ)⁻¹ ∈ P ⊓ A₁ :=
      (Subgroup.mem_normalizer_iff.mp ha₀N (τ⁻¹ * b' * τ)).mp ⟨ha''P, ha''⟩
    have h3 : b * b' * b⁻¹ ∈ P := by
      have := P.mul_mem (P.mul_mem hτP h2.1) (P.inv_mem hτP)
      have e : τ * ((τ⁻¹ * b * τ) * (τ⁻¹ * b' * τ) * (τ⁻¹ * b * τ)⁻¹) * τ⁻¹ = b * b' * b⁻¹ := by
        group
      rw [e] at this
      exact this
    have hconj : z * s * z⁻¹ = (a * a' * a⁻¹) * (b * b' * b⁻¹) := by
      rw [hzab, hsab]
      have hba' : b * a' = a' * b := (hc a' ha' b hb).symm
      have hbb'a : a * (b * b' * b⁻¹) = (b * b' * b⁻¹) * a :=
        hc a ha _ (A₂.mul_mem (A₂.mul_mem hb hb') (A₂.inv_mem hb))
      calc a * b * (a' * b') * (a * b)⁻¹ = a * (b * a') * b' * b⁻¹ * a⁻¹ := by group
        _ = a * (a' * b) * b' * b⁻¹ * a⁻¹ := by rw [hba']
        _ = a * a' * (b * b' * b⁻¹) * a⁻¹ := by group
        _ = a * a' * ((b * b' * b⁻¹) * a⁻¹) := by group
        _ = a * a' * (a⁻¹ * (b * b' * b⁻¹)) := by
          have h := hc a⁻¹ (A₁.inv_mem ha) _ (A₂.mul_mem (A₂.mul_mem hb hb') (A₂.inv_mem hb))
          rw [h]
        _ = (a * a' * a⁻¹) * (b * b' * b⁻¹) := by group
    rw [hconj]
    exact P.mul_mem h1.1 h3
  · left
    have hCn : ((Z ⊓ A₁).subgroupOf A₁).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨b, hb, hgb⟩ := (hfull g.2).2
      have hnb : (n : Q) * b = b * n := hc n n.2 b hb
      have e : (g : Q) * (n : Q) * (g : Q)⁻¹ = ((g : Q) * b) * (n : Q) * ((g : Q) * b)⁻¹ := by
        have h2 : ((g : Q) * b) * (n : Q) * ((g : Q) * b)⁻¹ =
            (g : Q) * (b * (n : Q) * b⁻¹) * (g : Q)⁻¹ := by group
        rw [h2, ← hnb, mul_inv_cancel_right]
      have hgn : ((g * n * g⁻¹ : ↥A₁) : Q) = (g : Q) * (n : Q) * (g : Q)⁻¹ := rfl
      refine ⟨?_, A₁.mul_mem (A₁.mul_mem g.2 n.2) (A₁.inv_mem g.2)⟩
      rw [hgn, e]
      exact Z.mul_mem (Z.mul_mem hgb hn.1) (Z.inv_mem hgb)
    have hCne : Z ⊓ A₁ ≠ ⊥ := by
      intro h
      apply hS₁ne
      rw [eq_bot_iff, ← h]
      exact fun s hs => ⟨⟨hPY hs.1, Subgroup.mem_sup_left hs.2⟩, hs.2⟩
    have hA₁Z : A₁ ≤ Z := by
      rcases hCn.eq_bot_or_eq_top with h | h
      · exfalso
        apply hCne
        rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_assoc, inf_idem] at h
        exact h
      · rw [Subgroup.subgroupOf_eq_top] at h
        exact h.trans inf_le_left
    have hA₂Z : A₂ ≤ Z := fun x hx => by
      have := hZτ _ (hA₁Z (hτA₂ x hx))
      simpa [mul_assoc] using this
    exact (sup_le hA₁Z hA₂Z).trans inf_le_left

end Pair

end CFSG.Quasithin.GoldS146R

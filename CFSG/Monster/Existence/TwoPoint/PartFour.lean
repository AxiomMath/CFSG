module

public import CFSG.Monster.Existence.TwoPoint.GraphAssembly

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G]

theorem inv_eq_self_of_isConj {a x : G} (ha : orderOf a = 2) (hx : IsConj a x) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_left (mul_self_of_isConj ha hx)

theorem isConj_mul_comm_of_isConj {a x y : G} (ha : orderOf a = 2) (hx : IsConj a x)
    (hy : IsConj a y) (h : IsConj a (x * y)) : IsConj a (y * x) := by
  have e : y * x = (x * y)⁻¹ := by
    rw [mul_inv_rev, inv_eq_self_of_isConj ha hx, inv_eq_self_of_isConj ha hy]
  have hxy : (x * y)⁻¹ = x * y := inv_eq_self_of_isConj ha h
  rw [e, hxy]
  exact h

variable [Finite G] {d₀ : B} {a z₀ : G}

theorem three_iv_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {α β : G}
    (hα : IsConj a α) (hβ : IsConj a β) (h4 : orderOf (α * β) = 4)
    (hsq : IsConj a ((α * β) ^ 2)) :
    α ≠ β ∧ ¬ IsConj a (α * β) ∧ ∃! γ, IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (γ * β) := by
  have ha : orderOf a = 2 := hG.1.1
  have hα2 : α * α = 1 := mul_self_of_isConj ha hα
  have hβ2 : β * β = 1 := mul_self_of_isConj ha hβ
  have hne : α ≠ β := by
    rintro rfl
    rw [hα2, orderOf_one] at h4
    exact absurd h4 (by norm_num)
  have hnc : ¬ IsConj a (α * β) := fun h => by
    rw [← orderOf_eq_of_isConj h, ha] at h4
    exact absurd h4 (by norm_num)
  set b := (α * β) ^ 2 with hb
  have hβi : β⁻¹ = β := inv_eq_self_of_isConj ha hβ
  have hαi : α⁻¹ = α := inv_eq_self_of_isConj ha hα
  have hαb : α * b = β * α * β⁻¹ := by
    rw [hb, pow_two, hβi]
    calc α * (α * β * (α * β)) = (α * α) * β * α * β := by group
      _ = β * α * β := by rw [hα2, one_mul]
  have hbβ : b * β = α * β * α⁻¹ := by
    rw [hb, pow_two, hαi]
    calc α * β * (α * β) * β = α * β * α * (β * β) := by group
      _ = α * β * α := by rw [hβ2, mul_one]
  have hbA : b ∈ twoANbr a α := ⟨hsq, by rw [hαb]; exact hα.trans (isConj_iff.2 ⟨β, rfl⟩)⟩
  have hβO : β ∈ tableVISet a α b := by
    refine ⟨⟨hβ, ?_⟩, hne.symm, ?_⟩
    · rw [hbβ]; exact hβ.trans (isConj_iff.2 ⟨α, rfl⟩)
    · intro e
      have h1 : β * 1 = β * (α * β⁻¹) := by rw [mul_one, ← mul_assoc]; exact e.trans hαb
      exact hne (mul_inv_eq_one.1 (mul_left_cancel h1).symm)
  have hcap := s342_one I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hα hbA hβO
    (Or.inl rfl)
  refine ⟨hne, hnc, b, ⟨hbA.1, hbA.2, ?_⟩, ?_⟩
  · rw [hbβ]; exact hβ.trans (isConj_iff.2 ⟨α, rfl⟩)
  · rintro γ ⟨hγ, hαγ, hγβ⟩
    have hmem : γ ∈ twoANbr a α ∩ twoANbr a β :=
      ⟨⟨hγ, hαγ⟩, ⟨hγ, isConj_mul_comm_of_isConj ha hγ hβ hγβ⟩⟩
    rw [hcap] at hmem
    exact hmem

omit [Finite G] in
theorem eq_insert_of_isTriangle {s : Set G} {α β : G} (hs : IsTriangle a s) (hα : α ∈ s)
    (hβ : β ∈ s) (hne : α ≠ β) : ∃ γ ∈ s, γ ≠ α ∧ γ ≠ β ∧ s = {α, β, γ} := by
  obtain ⟨hc, -, -⟩ := hs
  have hfin : s.Finite := Set.finite_of_ncard_pos (by rw [hc]; norm_num)
  have h2 : ({α, β} : Set G).ncard = 2 := Set.ncard_pair hne
  have hsub : ({α, β} : Set G) ⊆ s := Set.insert_subset hα (Set.singleton_subset_iff.2 hβ)
  have hlt : ({α, β} : Set G).ncard < s.ncard := by rw [h2, hc]; norm_num
  obtain ⟨γ, hγs, hγ⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hγ
  refine ⟨γ, hγs, hγ.1, hγ.2, ?_⟩
  have hsub3 : ({α, β, γ} : Set G) ⊆ s :=
    Set.insert_subset hα (Set.insert_subset hβ (Set.singleton_subset_iff.2 hγs))
  have h3 : ({α, β, γ} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hγ.2)]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, fun h => hγ.1 h.symm⟩
  exact (Set.eq_of_subset_of_ncard_le hsub3 (by rw [hc, h3]) hfin).symm

omit [Finite G] in
theorem commute_of_isConj_mul {α β : G} (ha : orderOf a = 2) (hα : IsConj a α) (hβ : IsConj a β)
    (h : IsConj a (α * β)) : α * β = β * α := by
  have e := inv_eq_self_of_isConj ha h
  rw [mul_inv_rev, inv_eq_self_of_isConj ha hα, inv_eq_self_of_isConj ha hβ] at e
  exact e.symm

omit [Finite G] in
theorem isTriangle_insert {α β γ : G} (ha : orderOf a = 2) (hα : IsConj a α) (hβ : IsConj a β)
    (hγ : IsConj a γ) (hne : α ≠ β) (hγα : γ ≠ α) (hγβ : γ ≠ β) (hαβ : IsConj a (α * β))
    (hαγ : IsConj a (α * γ)) (hβγ : IsConj a (β * γ)) : IsTriangle a {α, β, γ} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hγβ)]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, fun h => hγα h.symm⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro x (rfl | rfl | rfl) <;> assumption
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) hxy <;>
      first
        | exact absurd rfl hxy
        | assumption
        | exact isConj_mul_comm_of_isConj ha (by assumption) (by assumption) (by assumption)

omit [Finite G] in
theorem ncard_short_triangles (hG : GMSF1Type d₀ a z₀) {α β : G} (hα : IsConj a α)
    (hβ : IsConj a β) (hαβ : IsConj a (α * β)) :
    {s | IsShortTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard = 1 := by
  have ha : orderOf a = 2 := hG.1.1
  have hα2 : α * α = 1 := mul_self_of_isConj ha hα
  have hβ2 : β * β = 1 := mul_self_of_isConj ha hβ
  have hc := commute_of_isConj_mul ha hα hβ hαβ
  have hne1 : ∀ {y : G}, IsConj a y → y ≠ 1 := fun {y} hy h => by
    rw [h] at hy
    have := orderOf_eq_of_isConj hy
    rw [ha, orderOf_one] at this
    exact absurd this (by norm_num)
  have hne : α ≠ β := fun h => hne1 hαβ (by rw [h, hβ2])
  have hγα : α * β ≠ α := fun h => hne1 hβ (mul_left_cancel (h.trans (mul_one α).symm))
  have hγβ : α * β ≠ β := fun h => hne1 hα (mul_right_cancel (h.trans (one_mul β).symm))
  have p1 : β * α = α * β := hc.symm
  have p2 : α * (α * β) = β := by rw [← mul_assoc, hα2, one_mul]
  have p3 : α * β * α = β := by rw [hc, mul_assoc, hα2, mul_one]
  have p4 : β * (α * β) = α := by rw [← mul_assoc, p1, mul_assoc, hβ2, mul_one]
  have p5 : α * β * β = α := by rw [mul_assoc, hβ2, mul_one]
  have hT : IsTriangle a {α, β, α * β} := isTriangle_insert ha hα hβ hαβ hne hγα hγβ hαβ
    (by rw [p2]; exact hβ) (by rw [p4]; exact hα)
  rw [Set.ncard_eq_one]
  refine ⟨{α, β, α * β}, Set.eq_singleton_iff_unique_mem.2 ⟨⟨⟨hT, ?_⟩, by simp, by simp⟩, ?_⟩⟩
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy ⊢ <;>
      first
        | exact absurd rfl hxy
        | simp only [p1, p2, p3, p4, p5, true_or, or_true]
  · rintro s ⟨⟨hsT, hsc⟩, hαs, hβs⟩
    obtain ⟨γ, hγs, hγα', hγβ', rfl⟩ := eq_insert_of_isTriangle hsT hαs hβs hne
    have hab := hsc α (by simp) β (by simp) hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
    rcases hab with h | h | h
    · exact absurd h hγα
    · exact absurd h hγβ
    · rw [h]

theorem ncard_long_triangles
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {α β : G}
    (hα : IsConj a α) (hβ : IsConj a β) (hαβ : IsConj a (α * β)) :
    {s | IsLongTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard = 3968055 := by
  have ha : orderOf a = 2 := hG.1.1
  have hα2 : α * α = 1 := mul_self_of_isConj ha hα
  have hβ2 : β * β = 1 := mul_self_of_isConj ha hβ
  have hne1 : ∀ {y : G}, IsConj a y → y ≠ 1 := fun {y} hy h => by
    rw [h] at hy
    have := orderOf_eq_of_isConj hy
    rw [ha, orderOf_one] at this
    exact absurd this (by norm_num)
  have hne : α ≠ β := fun h => hne1 hαβ (by rw [h, hβ2])
  have hb : β ∈ twoANbr a α := ⟨hβ, hαβ⟩
  have hset : {s | IsLongTriangle a s ∧ α ∈ s ∧ β ∈ s} =
      (fun γ => ({α, β, γ} : Set G)) '' tableVIOrbit a z₀ α β .two_A := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨hsT, hsS⟩, hαs, hβs⟩
      obtain ⟨γ, hγs, hγα, hγβ, rfl⟩ := eq_insert_of_isTriangle hsT hαs hβs hne
      refine ⟨γ, ⟨⟨⟨hsT.2.1 γ hγs, hsT.2.2 β (by simp) γ hγs (Ne.symm hγβ)⟩, hγα, ?_⟩,
        hsT.2.2 α (by simp) γ hγs (Ne.symm hγα)⟩, rfl⟩
      intro hγ
      apply hsS
      refine ⟨hsT, ?_⟩
      have p1 : β * α = α * β := (commute_of_isConj_mul ha hα hβ hαβ).symm
      intro x hx y hy hxy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
      have p2 : α * (α * β) = β := by rw [← mul_assoc, hα2, one_mul]
      have p3 : α * β * α = β := by rw [← p1, mul_assoc, hα2, mul_one]
      have p4 : β * (α * β) = α := by rw [← mul_assoc, p1, mul_assoc, hβ2, mul_one]
      have p5 : α * β * β = α := by rw [mul_assoc, hβ2, mul_one]
      rw [hγ] at hx hy ⊢
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy ⊢ <;>
        first
          | exact absurd rfl hxy
          | simp only [p1, p2, p3, p4, p5, true_or, or_true]
    · rintro ⟨γ, ⟨⟨⟨hγ, hβγ⟩, hγα, hγαβ⟩, hαγ⟩, rfl⟩
      have hγβ : γ ≠ β := fun h => hne1 hβγ (by rw [h, hβ2])
      have hT := isTriangle_insert ha hα hβ hγ hne hγα hγβ hαβ hαγ hβγ
      refine ⟨⟨hT, fun hS => hγαβ ?_⟩, by simp, by simp⟩
      have hab := hS.2 α (by simp) β (by simp) hne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
      rcases hab with h | h | h
      · exact absurd (mul_left_cancel (h.trans (mul_one α).symm)) (hne1 hβ)
      · exact absurd (mul_right_cancel (h.trans (one_mul β).symm)) (hne1 hα)
      · exact h.symm
  have hinj : Set.InjOn (fun γ => ({α, β, γ} : Set G)) (tableVIOrbit a z₀ α β .two_A) := by
    rintro γ ⟨⟨⟨-, hβγ⟩, hγα, -⟩, -⟩ γ' ⟨⟨⟨-, hβγ'⟩, hγα', -⟩, -⟩ e
    have hγβ : γ ≠ β := fun h => hne1 hβγ (by rw [h, hβ2])
    have e' : ({α, β, γ} : Set G) = {α, β, γ'} := e
    have hmem : γ ∈ ({α, β, γ'} : Set G) := by
      rw [← e']; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd h hγα
    · exact absurd h hγβ
    · exact h
  rw [hset, hinj.ncard_image, s341_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hα hb
    .two_A]
  rfl

omit [Finite G] in
theorem conjSet_insert (g x : G) (s : Set G) :
    conjSet g (insert x s) = insert (g * x * g⁻¹) (conjSet g s) := by
  simp [conjSet, Set.image_insert_eq]

omit [Finite G] in
theorem conjSet_singleton (g x : G) : conjSet g {x} = {g * x * g⁻¹} := by
  simp [conjSet]

omit [Finite G] in
theorem conjSet_conjSet (g h : G) (s : Set G) : conjSet g (conjSet h s) = conjSet (g * h) s := by
  ext y
  simp only [conjSet, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by group⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h * x * h⁻¹, ⟨x, hx, rfl⟩, by group⟩

omit [Finite G] in
theorem mem_conjSet_iff {g y : G} {s : Set G} : y ∈ conjSet g s ↔ g⁻¹ * y * g ∈ s := by
  simp only [conjSet, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    convert hx using 1
    group
  · intro h
    exact ⟨g⁻¹ * y * g, h, by group⟩

omit [Finite G] in
theorem IsTriangle.conjSet {s : Set G} (h : IsTriangle a s) (g : G) :
    IsTriangle a (conjSet g s) := by
  obtain ⟨hc, hA, hP⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [CFSG.Monster.Existence.conjSet, Set.ncard_image_of_injective _ (by
      intro x y e; simpa using e), hc]
  · intro x hx
    rw [mem_conjSet_iff] at hx
    have := hA _ hx
    exact this.trans (isConj_iff.2 ⟨g, by group⟩)
  · intro x hx y hy hxy
    rw [mem_conjSet_iff] at hx hy
    have := hP _ hx _ hy (fun e => hxy (by
      have := congrArg (fun t => g * t * g⁻¹) e
      simpa [mul_assoc] using this))
    refine this.trans (isConj_iff.2 ⟨g, ?_⟩)
    group

omit [Finite G] in
theorem IsShortTriangle.conjSet {s : Set G} (h : IsShortTriangle a s) (g : G) :
    IsShortTriangle a (conjSet g s) := by
  refine ⟨h.1.conjSet g, fun x hx y hy hxy => ?_⟩
  rw [mem_conjSet_iff] at hx hy ⊢
  have := h.2 _ hx _ hy (fun e => hxy (by
    have := congrArg (fun t => g * t * g⁻¹) e
    simpa [mul_assoc] using this))
  convert this using 1
  group

omit [Finite G] in
theorem isShortTriangle_mul (ha : orderOf a = 2) {α β : G} (hα : IsConj a α) (hβ : IsConj a β)
    (hαβ : IsConj a (α * β)) : IsShortTriangle a {α, β, α * β} := by
  have hα2 : α * α = 1 := mul_self_of_isConj ha hα
  have hβ2 : β * β = 1 := mul_self_of_isConj ha hβ
  have hne1 : ∀ {y : G}, IsConj a y → y ≠ 1 := fun {y} hy h => by
    rw [h] at hy
    have := orderOf_eq_of_isConj hy
    rw [ha, orderOf_one] at this
    exact absurd this (by norm_num)
  have hne : α ≠ β := fun h => hne1 hαβ (by rw [h, hβ2])
  have hγα : α * β ≠ α := fun h => hne1 hβ (mul_left_cancel (h.trans (mul_one α).symm))
  have hγβ : α * β ≠ β := fun h => hne1 hα (mul_right_cancel (h.trans (one_mul β).symm))
  have p1 : β * α = α * β := (commute_of_isConj_mul ha hα hβ hαβ).symm
  have p2 : α * (α * β) = β := by rw [← mul_assoc, hα2, one_mul]
  have p3 : α * β * α = β := by rw [← p1, mul_assoc, hα2, mul_one]
  have p4 : β * (α * β) = α := by rw [← mul_assoc, p1, mul_assoc, hβ2, mul_one]
  have p5 : α * β * β = α := by rw [mul_assoc, hβ2, mul_one]
  refine ⟨isTriangle_insert ha hα hβ hαβ hne hγα hγβ hαβ (by rw [p2]; exact hβ)
    (by rw [p4]; exact hα), ?_⟩
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy ⊢ <;>
    first
      | exact absurd rfl hxy
      | simp only [p1, p2, p3, p4, p5, true_or, or_true]

omit [Finite G] in
theorem isLongTriangle_of_mem_orbit (ha : orderOf a = 2) {α β γ : G} (hα : IsConj a α)
    (hβ : IsConj a β) (hαβ : IsConj a (α * β)) (hγ : γ ∈ tableVIOrbit a z₀ α β .two_A) :
    IsLongTriangle a {α, β, γ} := by
  obtain ⟨⟨⟨hγA, hβγ⟩, hγα, hγαβ⟩, hαγ⟩ := hγ
  have hβ2 : β * β = 1 := mul_self_of_isConj ha hβ
  have hne1 : ∀ {y : G}, IsConj a y → y ≠ 1 := fun {y} hy h => by
    rw [h] at hy
    have := orderOf_eq_of_isConj hy
    rw [ha, orderOf_one] at this
    exact absurd this (by norm_num)
  have hne : α ≠ β := fun h => hne1 hαβ (by rw [h, hβ2])
  have hγβ : γ ≠ β := fun h => hne1 hβγ (by rw [h, hβ2])
  refine ⟨isTriangle_insert ha hα hβ hγA hne hγα hγβ hαβ hαγ hβγ, fun hS => hγαβ ?_⟩
  have hab := hS.2 α (by simp) β (by simp) hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
  rcases hab with h | h | h
  · exact absurd (mul_left_cancel (h.trans (mul_one α).symm)) (hne1 hβ)
  · exact absurd (mul_right_cancel (h.trans (one_mul β).symm)) (hne1 hα)
  · exact h.symm

theorem two_triangle_orbits
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∃ s₁ s₂ : Set G, IsTriangle a s₁ ∧ IsTriangle a s₂ ∧ (∀ g : G, conjSet g s₁ ≠ s₂) ∧
      ∀ s, IsTriangle a s → ∃ g : G, conjSet g s = s₁ ∨ conjSet g s = s₂ := by
  have ha : orderOf a = 2 := hG.1.1
  obtain ⟨y, hy⟩ := table7_nonempty I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG
    (IsConj.refl a) .two_A
  have hyA : IsConj a y := hy.1
  have hay : IsConj a (a * y) := hy.2
  have hlong := ncard_long_triangles I hG (IsConj.refl a) hyA hay
  have hne : (tableVIOrbit a z₀ a y .two_A).Nonempty := by
    rw [← Set.ncard_pos (Set.finite_of_ncard_pos (by
      rw [s341_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG (IsConj.refl a) hy
        .two_A]; norm_num [tableVISize]))]
    rw [s341_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG (IsConj.refl a) hy .two_A]
    norm_num [tableVISize]
  obtain ⟨γ, hγ⟩ := hne
  have hS := isShortTriangle_mul ha (IsConj.refl a) hyA hay
  have hL := isLongTriangle_of_mem_orbit ha (IsConj.refl a) hyA hay hγ
  refine ⟨{a, y, a * y}, {a, y, γ}, hS.1, hL.1, fun g e => hL.2 (e ▸ hS.conjSet g), ?_⟩
  intro s hs
  have hfin : s.Finite := Set.finite_of_ncard_pos (by rw [hs.1]; norm_num)
  obtain ⟨α, hα⟩ : s.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hs.1]; norm_num)
  obtain ⟨β, hβs, hβα⟩ : ∃ β ∈ s, β ≠ α := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    have : s ⊆ {α} := fun x hx => hc x hx
    have := Set.ncard_le_ncard this (Set.finite_singleton α)
    rw [hs.1, Set.ncard_singleton] at this
    exact absurd this (by norm_num)
  have hαA := hs.2.1 α hα
  have hβA := hs.2.1 β hβs
  have hαβ := hs.2.2 α hα β hβs (Ne.symm hβα)
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 hαA
  have hβ' : g₁⁻¹ * β * g₁ ∈ twoANbr a a := by
    refine ⟨hβA.trans (isConj_iff.2 ⟨g₁⁻¹, by group⟩), ?_⟩
    have e : a * (g₁⁻¹ * β * g₁) = g₁⁻¹ * (α * β) * g₁ := by rw [← hg₁]; group
    rw [e]
    exact hαβ.trans (isConj_iff.2 ⟨g₁⁻¹, by group⟩)
  obtain ⟨g₂, hg₂, hg₂β⟩ := table7_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby
    I.threeSwap I.leechPair hG (IsConj.refl a) (K := .two_A) hβ' hy
  have hg₂a : g₂ * a * g₂⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hg₂, mul_inv_cancel_right]
  set g := g₂ * g₁⁻¹ with hg
  have hgα : g * α * g⁻¹ = a := by rw [hg, ← hg₁]; calc
    g₂ * g₁⁻¹ * (g₁ * a * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ = g₂ * a * g₂⁻¹ := by group
    _ = a := hg₂a
  have hgβ : g * β * g⁻¹ = y := by
    rw [← hg₂β, hg]; group
  have hs' := hs.conjSet g
  have ha' : a ∈ conjSet g s := ⟨α, hα, hgα⟩
  have hy' : y ∈ conjSet g s := ⟨β, hβs, hgβ⟩
  have hya : a ≠ y := fun h => by
    rw [← h] at hay
    have := orderOf_eq_of_isConj hay
    rw [ha, orderOf_eq_one_iff.2 (mul_self_of_isConj ha (IsConj.refl a))] at this
    exact absurd this (by norm_num)
  obtain ⟨γ', hγ's, hγ'a, hγ'y, he⟩ := eq_insert_of_isTriangle hs' ha' hy' hya
  by_cases hshort : IsShortTriangle a (conjSet g s)
  · refine ⟨g, Or.inl ?_⟩
    rw [he]
    have hab := hshort.2 a ha' y hy' hya
    rw [he] at hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
    rcases hab with h | h | h
    · exact absurd (mul_left_cancel (h.trans (mul_one a).symm)) (fun e => by
        rw [e] at hyA
        have := orderOf_eq_of_isConj hyA
        rw [ha, orderOf_one] at this
        exact absurd this (by norm_num))
    · exact absurd (mul_right_cancel (h.trans (one_mul y).symm)) (fun e => by
        have := ha
        rw [e, orderOf_one] at this
        exact absurd this (by norm_num))
    · rw [h]
  ·
    have hγ'O : γ' ∈ tableVIOrbit a z₀ a y .two_A := by
      have hγ'A := hs'.2.1 γ' hγ's
      refine ⟨⟨⟨hγ'A, hs'.2.2 y hy' γ' hγ's (Ne.symm hγ'y)⟩, hγ'a, ?_⟩,
        hs'.2.2 a ha' γ' hγ's (Ne.symm hγ'a)⟩
      intro e
      apply hshort
      rw [he, e]
      exact isShortTriangle_mul ha (IsConj.refl a) hyA hay
    obtain ⟨g₃, hg₃, hg₃γ⟩ := s341_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby
      I.threeSwap I.leechPair hG (IsConj.refl a) hy hγ'O hγ
    obtain ⟨hg₃a, hg₃y⟩ := Subgroup.mem_inf.1 hg₃
    refine ⟨g₃ * g, Or.inr ?_⟩
    rw [← conjSet_conjSet, he, conjSet_insert, conjSet_insert, conjSet_singleton,
      Subgroup.mem_centralizer_singleton_iff.1 hg₃a, mul_inv_cancel_right,
      Subgroup.mem_centralizer_singleton_iff.1 hg₃y, mul_inv_cancel_right, hg₃γ]

theorem isTwoAGraphData_of_tables
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (hsep : OddTypesSeparated a z₀) (b : Fin 9 → G)
    (hb : ∀ j, nineClass a z₀ j (b j))
    (hshape : ∀ i, TwoPointShape (cent2 a (b (classIndex i))) i)
    (hiii : ∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (a * b (classIndex 3)) →
      (∃ γ, IsConj a γ ∧ IsConj (α * γ) (a * b (classIndex 3)) ∧ IsConj a (β * γ)) ∧
      (∀ γ γ', IsConj a γ → IsConj (α * γ) (a * b (classIndex 3)) → IsConj a (β * γ) →
        IsConj a γ' → IsConj (α * γ') (a * b (classIndex 3)) → IsConj a (β * γ') →
        ∃ g ∈ cent2 α β, g * γ * g⁻¹ = γ') ∧
      ∀ γ, IsConj a γ → IsConj (α * γ) (a * b (classIndex 3)) → IsConj a (β * γ) →
        CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent γ) .PSp 4 2 1)
    (hv : ∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (a * b (classIndex 3)) →
      (∃ D : Set ↥(cent2 α β), CFSG.Blueprint.Fischer.Pair ↥(cent2 α β) D ∧
        {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)} =
          Subtype.val '' D ∧
        ∀ γ ∈ D, Nat.card ↥(Subgroup.centralizer ({γ} : Set ↥(cent2 α β))) =
          2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ∧
      Set.ncard {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)} = 31671)
    (h4c : ∀ s, IsLongTriangle a s →
      CFSG.Blueprint.LieModel (pointStab s ⧸ CFSG.pCore 2 (pointStab s)) .PSU 6 2 1 ∧
      HasLayeredTwoShape (pointStab s) 3 20 fun X _ => CFSG.Blueprint.LieModel X .PSU 6 2 1)
    (h4d : ∀ α β : G, IsConj a α → IsConj a β → IsConj a (α * β) →
      ∃ γ δ : G, IsLongTriangle a {α, β, γ} ∧ IsConj a δ ∧
        IsConj (α * δ) (a * b (classIndex 3)) ∧ IsConj (β * δ) (a * b (classIndex 3)) ∧
        (cent2 α β ⊓ cent γ) ⊔ (cent2 α β ⊓ cent δ) = cent2 α β ∧
        CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent δ) .PSp 4 2 1) :
    IsTwoAGraphData a z₀ := by
  refine isTwoAGraphData_of I hG hex hsep b hb hshape hiii ?_ hv (two_triangle_orbits I hG)
    (fun α β hα hβ hαβ => ⟨ncard_short_triangles hG hα hβ hαβ,
      ncard_long_triangles I hG hα hβ hαβ⟩) h4c h4d
  intro α β hα hβ h
  have h4B := (nineClass_even 3).1 (hb (classIndex 6))
  exact three_iv_of I hG hα hβ ((orderOf_eq_of_isConj h).trans h4B.2.1)
    (h4B.2.2.trans (isConj_pow_of_isConj h 2).symm)

end CFSG.Monster.Existence

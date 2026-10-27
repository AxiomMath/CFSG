module

public import CFSG.Quasithin.Recognition.CertTwoLocalIndexTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Ext

variable {M : Type*} [Group M]

@[expose] def extSub (H : Subgroup M) (q : M) (hq : q ∈ Subgroup.normalizer (H : Set M))
    (hq2 : q * q ∈ H) : Subgroup M where
  carrier := {x | x ∈ H ∨ x * q⁻¹ ∈ H}
  mul_mem' := by
    have hN : ∀ h, h ∈ H ↔ q * h * q⁻¹ ∈ H := Subgroup.mem_normalizer_iff.1 hq
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (H.mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact H.mul_mem ha hb)
    · refine Or.inr ?_
      have h1 : (a * b) * q⁻¹ = (a * q⁻¹) * (q * b * q⁻¹) := by group
      rw [h1]
      exact H.mul_mem ha ((hN b).1 hb)
    · refine Or.inl ?_
      have h1 : a * b = (a * q⁻¹) * (q * (b * q⁻¹) * q⁻¹) * (q * q) := by group
      rw [h1]
      exact H.mul_mem (H.mul_mem ha ((hN _).1 hb)) hq2
  one_mem' := Or.inl H.one_mem
  inv_mem' := by
    have hN' : ∀ h : M, h ∈ H ↔ q⁻¹ * h * q ∈ H := Subgroup.mem_normalizer_iff''.1 hq
    rintro a (ha | ha)
    · exact Or.inl (H.inv_mem ha)
    · refine Or.inr ?_
      have h1 : a⁻¹ * q⁻¹ = (q⁻¹ * (a * q⁻¹)⁻¹ * q) * (q * q)⁻¹ := by group
      rw [h1]
      exact H.mul_mem ((hN' _).1 (H.inv_mem ha)) (H.inv_mem hq2)

variable {H : Subgroup M} {q : M} {hq : q ∈ Subgroup.normalizer (H : Set M)} {hq2 : q * q ∈ H}

theorem mem_extSub {x : M} : x ∈ extSub H q hq hq2 ↔ x ∈ H ∨ x * q⁻¹ ∈ H := Iff.rfl

theorem le_extSub : H ≤ extSub H q hq hq2 := fun _ hx => Or.inl hx

theorem q_mem_extSub : q ∈ extSub H q hq hq2 := Or.inr (by simp)

theorem mul_inv_mem_of_not_mem {D : Subgroup M} (hD : D.index = 2) {x y : M} (hx : x ∉ D)
    (hy : y ∉ D) : x * y⁻¹ ∈ D := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hD
  have h1 : x * a ∈ D := by
    rcases ha x with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hx
  have h2 : y * a ∈ D := by
    rcases ha y with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hy
  have := D.mul_mem h1 (D.inv_mem h2)
  simpa [mul_assoc] using this

theorem isPGroup_extSub (hH : IsPGroup 2 H) : IsPGroup 2 (extSub H q hq hq2) := by
  intro g
  obtain ⟨x, hx⟩ := g
  rcases hx with hx | hx
  · obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  · have hx2 : x * x ∈ H := by
      have h1 : x * x = (x * q⁻¹) * (q * (x * q⁻¹) * q⁻¹) * (q * q) := by group
      rw [h1]
      exact H.mul_mem (H.mul_mem hx ((Subgroup.mem_normalizer_iff.1 hq _).1 hx)) hq2
    obtain ⟨k, hk⟩ := hH ⟨x * x, hx2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h2 ⊢
    rw [pow_succ', pow_mul, sq]
    exact h2

theorem relIndex_extSub (hqH : q ∉ H) : H.relIndex (extSub H q hq hq2) = 2 := by
  rw [Subgroup.relIndex]
  refine Subgroup.index_eq_two_iff.2 ⟨⟨q, q_mem_extSub⟩, fun b => ?_⟩
  obtain ⟨x, hx⟩ := b
  change Xor (x * q ∈ H) (x ∈ H)
  rcases hx with hx | hx
  · refine Or.inr ⟨hx, fun h => hqH ?_⟩
    have := H.mul_mem (H.inv_mem hx) h
    simpa using this
  · by_cases hxH : x ∈ H
    · refine Or.inr ⟨hxH, fun h => hqH ?_⟩
      have := H.mul_mem (H.inv_mem hxH) h
      simpa using this
    · refine Or.inl ⟨?_, hxH⟩
      have h1 : x * q = (x * q⁻¹) * (q * q) := by group
      rw [h1]
      exact H.mul_mem hx hq2

end Ext

section Lattice

variable {M : Type*} [Group M]

structure IndexTwoLatticeData (M : Type*) [Group M] where
  D : Subgroup M
  S : Subgroup M
  P₁ : Subgroup M
  P₂ : Subgroup M
  q : M
  D_normal : D.Normal
  D_index : D.index = 2
  q_not_mem : q ∉ D
  S_le_P₁ : S ≤ P₁
  S_le_P₂ : S ≤ P₂
  P₁_le_D : P₁ ≤ D
  P₂_le_D : P₂ ≤ D
  lattice : ∀ X : Subgroup M, S ≤ X → X ≤ D → X = S ∨ X = P₁ ∨ X = P₂ ∨ X = D
  S_ne_P₁ : S ≠ P₁
  S_ne_P₂ : S ≠ P₂
  P₁_not_le_P₂ : ¬ P₁ ≤ P₂
  P₂_not_le_P₁ : ¬ P₂ ≤ P₁
  sylowS_p : IsPGroup 2 S
  sylowS_idx : ¬ 2 ∣ (S.subgroupOf D).index
  normS : ∀ x ∈ D, x ∈ Subgroup.normalizer (S : Set M) → x ∈ S
  noNormal : ∀ Q : Subgroup M, Q.Normal → Q ≤ D → IsPGroup 2 Q → Q = ⊥
  centD : ∀ x : M, (∀ d ∈ D, x * d = d * x) → x = 1
  q_norm_S : q ∈ Subgroup.normalizer (S : Set M)
  q_norm_P₁ : q ∈ Subgroup.normalizer (P₁ : Set M)
  q_norm_P₂ : q ∈ Subgroup.normalizer (P₂ : Set M)
  loc₁ : ∃ Q : Subgroup M, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ P₁ ≤ Subgroup.normalizer (Q : Set M) ∧
    q ∈ Subgroup.normalizer (Q : Set M)
  loc₂ : ∃ Q : Subgroup M, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ P₂ ≤ Subgroup.normalizer (Q : Set M) ∧
    q ∈ Subgroup.normalizer (Q : Set M)

namespace IndexTwoLatticeData

variable (d : IndexTwoLatticeData M)

theorem q_inv_not_mem : d.q⁻¹ ∉ d.D := fun h => d.q_not_mem (by simpa using d.D.inv_mem h)

theorem q_mul_self_mem_D : d.q * d.q ∈ d.D := by
  have := mul_inv_mem_of_not_mem d.D_index d.q_not_mem d.q_inv_not_mem
  simpa using this

theorem q_mul_self_mem_S : d.q * d.q ∈ d.S :=
  d.normS _ d.q_mul_self_mem_D (Subgroup.mul_mem _ d.q_norm_S d.q_norm_S)

theorem q_mul_self_mem_P₁ : d.q * d.q ∈ d.P₁ := d.S_le_P₁ d.q_mul_self_mem_S

theorem q_mul_self_mem_P₂ : d.q * d.q ∈ d.P₂ := d.S_le_P₂ d.q_mul_self_mem_S

theorem mem_D_or (x : M) : x ∈ d.D ∨ x * d.q⁻¹ ∈ d.D := by
  by_cases hx : x ∈ d.D
  · exact Or.inl hx
  · exact Or.inr (mul_inv_mem_of_not_mem d.D_index hx d.q_not_mem)

@[expose] def Sx : Subgroup M := extSub d.S d.q d.q_norm_S d.q_mul_self_mem_S

@[expose] def P₁x : Subgroup M := extSub d.P₁ d.q d.q_norm_P₁ d.q_mul_self_mem_P₁

@[expose] def P₂x : Subgroup M := extSub d.P₂ d.q d.q_norm_P₂ d.q_mul_self_mem_P₂

theorem mem_of_mem_ext_of_mem_D {H : Subgroup M} (hHD : H ≤ d.D)
    {hq : d.q ∈ Subgroup.normalizer (H : Set M)} {hq2 : d.q * d.q ∈ H} {x : M}
    (hx : x ∈ extSub H d.q hq hq2) (hxD : x ∈ d.D) : x ∈ H := by
  rcases hx with hx | hx
  · exact hx
  · exfalso
    apply d.q_inv_not_mem
    have := d.D.mul_mem (d.D.inv_mem hxD) (hHD hx)
    simpa using this

theorem eq_ext_of_inf {H : Subgroup M} {X : Subgroup M}
    {hq : d.q ∈ Subgroup.normalizer (H : Set M)} {hq2 : d.q * d.q ∈ H}
    (hqX : d.q ∈ X) (hY : X ⊓ d.D = H) : X = extSub H d.q hq hq2 := by
  ext x
  constructor
  · intro hx
    by_cases hxD : x ∈ d.D
    · exact Or.inl (hY ▸ ⟨hx, hxD⟩)
    · refine Or.inr (hY ▸ ⟨X.mul_mem hx (X.inv_mem hqX), mul_inv_mem_of_not_mem d.D_index hxD
        d.q_not_mem⟩)
  · rintro (hx | hx)
    · exact (hY ▸ hx : x ∈ X ⊓ d.D).1
    · have h1 : x * d.q⁻¹ ∈ X := (hY ▸ hx : x * d.q⁻¹ ∈ X ⊓ d.D).1
      have := X.mul_mem h1 hqX
      simpa using this

theorem S_le_D : d.S ≤ d.D := d.S_le_P₁.trans d.P₁_le_D

theorem q_mem_Sx : d.q ∈ d.Sx := q_mem_extSub

theorem S_le_Sx : d.S ≤ d.Sx := le_extSub

theorem sylowx_p : IsPGroup 2 d.Sx := isPGroup_extSub d.sylowS_p

theorem relIndex_S_Sx : d.S.relIndex d.Sx = 2 := by
  rw [Subgroup.relIndex]
  refine Subgroup.index_eq_two_iff.2 ⟨⟨d.q, d.q_mem_Sx⟩, fun b => ?_⟩
  obtain ⟨x, hx⟩ := b
  change Xor (x * d.q ∈ d.S) (x ∈ d.S)
  rcases hx with hx | hx
  · refine Or.inr ⟨hx, fun h => d.q_not_mem (d.S_le_D ?_)⟩
    have := d.S.mul_mem (d.S.inv_mem hx) h
    simpa using this
  · by_cases hxS : x ∈ d.S
    · refine Or.inr ⟨hxS, fun h => d.q_not_mem (d.S_le_D ?_)⟩
      have := d.S.mul_mem (d.S.inv_mem hxS) h
      simpa using this
    · refine Or.inl ⟨?_, hxS⟩
      have h1 : x * d.q = (x * d.q⁻¹) * (d.q * d.q) := by group
      rw [h1]
      exact d.S.mul_mem hx d.q_mul_self_mem_S

theorem sylowx_idx : ¬ 2 ∣ d.Sx.index := by
  have h1 := Subgroup.relIndex_mul_index d.S_le_Sx
  have h2 := Subgroup.relIndex_mul_index d.S_le_D
  rw [d.relIndex_S_Sx] at h1
  rw [d.D_index] at h2
  have h3 : d.Sx.index = d.S.relIndex d.D := by omega
  rw [h3]
  exact d.sylowS_idx

theorem lattice_x (X : Subgroup M) (hX : d.Sx ≤ X) :
    X = d.Sx ∨ X = d.P₁x ∨ X = d.P₂x ∨ X = ⊤ := by
  have hqX : d.q ∈ X := hX d.q_mem_Sx
  have hSY : d.S ≤ X ⊓ d.D := le_inf (le_trans d.S_le_Sx hX) d.S_le_D
  rcases d.lattice (X ⊓ d.D) hSY inf_le_right with h | h | h | h
  · exact Or.inl (d.eq_ext_of_inf hqX h)
  · exact Or.inr (Or.inl (d.eq_ext_of_inf hqX h))
  · exact Or.inr (Or.inr (Or.inl (d.eq_ext_of_inf hqX h)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [eq_top_iff]
    intro x _
    rcases d.mem_D_or x with hx | hx
    · have : x ∈ X ⊓ d.D := by rw [h]; exact hx
      exact this.1
    · have h1 : x * d.q⁻¹ ∈ X := by
        have : x * d.q⁻¹ ∈ X ⊓ d.D := by rw [h]; exact hx
        exact this.1
      have := X.mul_mem h1 hqX
      simpa using this

include d in
theorem noNormal_M (Q : Subgroup M) (hQ : Q.Normal) (hp : IsPGroup 2 Q) : Q = ⊥ := by
  have h1 : Q ⊓ d.D = ⊥ := by
    have := hQ
    have := d.D_normal
    exact d.noNormal (Q ⊓ d.D) inferInstance inf_le_right (hp.to_inf_left)
  rw [eq_bot_iff]
  intro x hx
  by_contra hne
  have hx1 : x ≠ 1 := fun h => hne (by rw [h]; exact Subgroup.one_mem _)
  have hxD : x ∉ d.D := fun hD => hx1 (by
    have : x ∈ Q ⊓ d.D := ⟨hx, hD⟩
    rw [h1] at this
    exact Subgroup.mem_bot.1 this)
  apply hx1
  refine d.centD x fun dd hdd => ?_
  have hy : dd * x * dd⁻¹ ∈ Q := hQ.conj_mem x hx dd
  have hyD : dd * x * dd⁻¹ ∉ d.D := fun h => hxD (by
    have := d.D_normal.conj_mem _ h dd⁻¹
    simpa [mul_assoc] using this)
  have h2 : dd * x * dd⁻¹ * x⁻¹ ∈ d.D := mul_inv_mem_of_not_mem d.D_index hyD hxD
  have h3 : dd * x * dd⁻¹ * x⁻¹ ∈ Q ⊓ d.D := ⟨Q.mul_mem hy (Q.inv_mem hx), h2⟩
  rw [h1] at h3
  have h4 := Subgroup.mem_bot.1 h3
  have h5 : dd * x * dd⁻¹ = x := by
    have := mul_inv_eq_one.1 h4
    exact this
  calc x * dd = (dd * x * dd⁻¹) * dd := by rw [h5]
    _ = dd * x := by group

theorem normSx : Subgroup.normalizer (d.Sx : Set M) ≤ d.Sx := by
  intro x hx
  have hxD' : x ∈ Subgroup.normalizer (d.D : Set M) := by
    rw [Subgroup.normalizer_eq_top_iff.2 d.D_normal]
    exact Subgroup.mem_top x
  have hxD : ∀ y, y ∈ d.D ↔ x * y * x⁻¹ ∈ d.D := Subgroup.mem_normalizer_iff.1 hxD'
  have hS : ∀ s, s ∈ d.S ↔ x * s * x⁻¹ ∈ d.S := by
    intro s
    constructor
    · intro hs
      have h1 : x * s * x⁻¹ ∈ d.Sx := (Subgroup.mem_normalizer_iff.1 hx s).1 (d.S_le_Sx hs)
      exact d.mem_of_mem_ext_of_mem_D d.S_le_D h1 ((hxD s).1 (d.S_le_D hs))
    · intro hs
      have h1 : x⁻¹ * (x * s * x⁻¹) * x ∈ d.Sx :=
        (Subgroup.mem_normalizer_iff''.1 hx (x * s * x⁻¹)).1 (d.S_le_Sx hs)
      have h2 : s ∈ d.D := (hxD s).2 (d.S_le_D hs)
      have h3 : s ∈ d.Sx := by simpa [mul_assoc] using h1
      exact d.mem_of_mem_ext_of_mem_D d.S_le_D h3 h2
  by_cases hxDm : x ∈ d.D
  · exact d.S_le_Sx (d.normS x hxDm (Subgroup.mem_normalizer_iff.2 hS))
  · refine Or.inr (d.normS _ (mul_inv_mem_of_not_mem d.D_index hxDm d.q_not_mem) ?_)
    have hxn : x ∈ Subgroup.normalizer (d.S : Set M) := Subgroup.mem_normalizer_iff.2 hS
    exact Subgroup.mul_mem _ hxn (Subgroup.inv_mem _ d.q_norm_S)

@[expose] def toLattice (d : IndexTwoLatticeData M) : TwoLocalLattice M where
  S := d.Sx
  P₁ := d.P₁x
  P₂ := d.P₂x
  sylow := ⟨d.sylowx_p, d.sylowx_idx⟩
  lattice := d.lattice_x
  S_le_P₁ := fun x hx => by
    rcases hx with hx | hx
    · exact Or.inl (d.S_le_P₁ hx)
    · exact Or.inr (d.S_le_P₁ hx)
  S_le_P₂ := fun x hx => by
    rcases hx with hx | hx
    · exact Or.inl (d.S_le_P₂ hx)
    · exact Or.inr (d.S_le_P₂ hx)
  S_ne_P₁ := fun h => d.S_ne_P₁ (by
    ext x
    constructor
    · exact fun hx => d.S_le_P₁ hx
    · intro hx
      have h1 : x ∈ d.Sx := h ▸ (le_extSub hx : x ∈ d.P₁x)
      exact d.mem_of_mem_ext_of_mem_D d.S_le_D h1 (d.P₁_le_D hx))
  S_ne_P₂ := fun h => d.S_ne_P₂ (by
    ext x
    constructor
    · exact fun hx => d.S_le_P₂ hx
    · intro hx
      have h1 : x ∈ d.Sx := h ▸ (le_extSub hx : x ∈ d.P₂x)
      exact d.mem_of_mem_ext_of_mem_D d.S_le_D h1 (d.P₂_le_D hx))
  P₁_not_le_P₂ := fun h => d.P₁_not_le_P₂ fun x hx =>
    d.mem_of_mem_ext_of_mem_D d.P₂_le_D (h (le_extSub hx)) (d.P₁_le_D hx)
  P₂_not_le_P₁ := fun h => d.P₂_not_le_P₁ fun x hx =>
    d.mem_of_mem_ext_of_mem_D d.P₁_le_D (h (le_extSub hx)) (d.P₂_le_D hx)
  O₂ := d.noNormal_M
  loc₁ := by
    obtain ⟨Q, hQ, hp, hP, hqQ⟩ := d.loc₁
    refine ⟨Q, hQ, hp, fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact hP hx
    · have h1 : x = (x * d.q⁻¹) * d.q := by group
      rw [h1]
      exact Subgroup.mul_mem _ (hP hx) hqQ
  loc₂ := by
    obtain ⟨Q, hQ, hp, hP, hqQ⟩ := d.loc₂
    refine ⟨Q, hQ, hp, fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact hP hx
    · have h1 : x = (x * d.q⁻¹) * d.q := by group
      rw [h1]
      exact Subgroup.mul_mem _ (hP hx) hqQ
  normS := d.normSx

theorem toLattice_inf_D_S : d.Sx ⊓ d.D = d.S := by
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    exact d.mem_of_mem_ext_of_mem_D d.S_le_D hx hxD
  · intro hx
    exact ⟨d.S_le_Sx hx, d.S_le_D hx⟩

end IndexTwoLatticeData

end Lattice

end CFSG.Quasithin

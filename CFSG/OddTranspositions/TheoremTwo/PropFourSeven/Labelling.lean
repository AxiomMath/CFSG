module

public import CFSG.OddTranspositions.SixTenPetersen
public import CFSG.GroupTheory.SymmetricFiveTranspositions

public section

namespace CFSG.OddTranspositions.PropFourSeven

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.GroupTheory Equiv

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure S5Labelling (D θ : Set G) (ψ : G → Perm (Fin 5)) : Prop where
  mem : ∀ x ∈ DalphaStar D θ, ψ x ∈ transpositions
  surj : ∀ σ ∈ transpositions, ∃ x ∈ DalphaStar D θ, ψ x = σ
  comm : ∀ x ∈ DalphaStar D θ, ∀ y ∈ DalphaStar D θ,
    (Commute x y ↔ x = y ∨ (ψ x ≠ ψ y ∧ Commute (ψ x) (ψ y)))
  equiv : ∀ x ∈ DalphaStar D θ, ∀ y ∈ DalphaStar D θ,
    ψ (x * y * x⁻¹) = ψ x * ψ y * (ψ x)⁻¹
  block : ∀ β ∈ Dalpha D θ, ∀ x ∈ β, ∀ y ∈ β, ψ x = ψ y

@[expose] def Phi (D θ : Set G) (x : G) : Set G :=
  {y | y ∈ DalphaStar D θ ∧
    ∀ t ∈ DalphaStar D θ, t ≠ x → t ≠ y → (Commute t x ↔ Commute t y)}

noncomputable abbrev labelOf {α : Set G}
    (ε : (Halpha D α ⧸ CFSG.solvableRadical (Halpha D α)) ≃* Perm (Fin 5)) : G → Perm (Fin 5) :=
  piG (Halpha D α) ((ε : Halpha D α ⧸ CFSG.solvableRadical (Halpha D α) →* Perm (Fin 5)).comp
    (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D α))))

omit [Finite G] in
theorem conj_conj_inv (g x : G) : g⁻¹ * (g * x * g⁻¹) * g = x := by group

omit [Finite G] in
theorem conj_inv_conj (g x : G) : g * (g⁻¹ * x * g) * g⁻¹ = x := by group

theorem mem_DalphaStar_conj_iff (hN : IsNormalSet D) (g : G) {θ : Set G} {x : G} :
    x ∈ DalphaStar D ((fun y => g * y * g⁻¹) '' θ) ↔ g⁻¹ * x * g ∈ DalphaStar D θ := by
  constructor
  · intro hx
    have h := DalphaStar.conj hN hx g⁻¹
    rwa [image_conj_inv_image_conj, inv_inv] at h
  · intro hx
    have h := DalphaStar.conj hN hx g
    rwa [conj_inv_conj] at h

theorem mem_Dalpha_conj_iff (hN : IsNormalSet D) (g : G) {θ β : Set G} :
    β ∈ Dalpha D ((fun y => g * y * g⁻¹) '' θ) ↔
      (fun y => g⁻¹ * y * g⁻¹⁻¹) '' β ∈ Dalpha D θ := by
  constructor
  · intro hβ
    have h := Dalpha.conj hN hβ g⁻¹
    rwa [image_conj_inv_image_conj] at h
  · intro hβ
    have h := Dalpha.conj hN hβ g
    rwa [image_conj_image_conj_inv] at h

omit [Finite G] in
theorem commute_conj_iff (g x y : G) : Commute (g * x * g⁻¹) (g * y * g⁻¹) ↔ Commute x y := by
  constructor
  · intro h
    have := h.map (MulAut.conj g⁻¹).toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc] using this
  · intro h
    have := h.map (MulAut.conj g).toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem S5Labelling.conj (hN : IsNormalSet D) {θ : Set G} {ψ : G → Perm (Fin 5)}
    (h : S5Labelling D θ ψ) (g : G) :
    S5Labelling D ((fun x => g * x * g⁻¹) '' θ) (fun x => ψ (g⁻¹ * x * g)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact h.mem _ ((mem_DalphaStar_conj_iff hN g).mp hx)
  · intro σ hσ
    obtain ⟨x, hx, rfl⟩ := h.surj σ hσ
    refine ⟨g * x * g⁻¹, (mem_DalphaStar_conj_iff hN g).mpr (by rwa [conj_conj_inv]), ?_⟩
    simp only [conj_conj_inv]
  · intro x hx y hy
    have hx' := (mem_DalphaStar_conj_iff hN g).mp hx
    have hy' := (mem_DalphaStar_conj_iff hN g).mp hy
    have key := h.comm _ hx' _ hy'
    rw [← commute_conj_iff g⁻¹ x y, inv_inv, key]
    constructor
    · rintro (he | he)
      · left
        have := congrArg (fun t => g * t * g⁻¹) he
        simpa only [conj_inv_conj] using this
      · exact Or.inr he
    · rintro (rfl | he)
      · exact Or.inl rfl
      · exact Or.inr he
  · intro x hx y hy
    have hx' := (mem_DalphaStar_conj_iff hN g).mp hx
    have hy' := (mem_DalphaStar_conj_iff hN g).mp hy
    have := h.equiv _ hx' _ hy'
    rw [← this]
    congr 1
    group
  · intro β hβ x hx y hy
    have hβ' := (mem_Dalpha_conj_iff hN g).mp hβ
    exact h.block _ hβ' _ ⟨x, hx, by simp⟩ _ ⟨y, hy, by simp⟩

theorem mem_Phi_conj_iff (hN : IsNormalSet D) (g : G) {θ : Set G} {x y : G} :
    y ∈ Phi D ((fun z => g * z * g⁻¹) '' θ) (g * x * g⁻¹) ↔
      g⁻¹ * y * g ∈ Phi D θ x := by
  constructor
  · rintro ⟨hy, hall⟩
    refine ⟨(mem_DalphaStar_conj_iff hN g).mp hy, fun t ht htx hty => ?_⟩
    have ht' : g * t * g⁻¹ ∈ DalphaStar D ((fun z => g * z * g⁻¹) '' θ) :=
      (mem_DalphaStar_conj_iff hN g).mpr (by rwa [conj_conj_inv])
    have key := hall _ ht'
      (fun he => htx (by simpa [conj_conj_inv] using congrArg (fun s => g⁻¹ * s * g) he))
      (fun he => hty (by rw [← he, conj_conj_inv]))
    rw [← commute_conj_iff g t x, key, ← commute_conj_iff g t (g⁻¹ * y * g), conj_inv_conj]
  · rintro ⟨hy, hall⟩
    refine ⟨(mem_DalphaStar_conj_iff hN g).mpr hy, fun t ht htx hty => ?_⟩
    have ht' := (mem_DalphaStar_conj_iff hN g).mp ht
    have key := hall _ ht'
      (fun he => htx (by rw [← conj_inv_conj g t, he]))
      (fun he => hty (by rw [← conj_inv_conj g t, he, conj_inv_conj]))
    have e1 : Commute t (g * x * g⁻¹) ↔ Commute (g⁻¹ * t * g) x := by
      rw [← commute_conj_iff g (g⁻¹ * t * g) x, conj_inv_conj]
    have e2 : Commute t y ↔ Commute (g⁻¹ * t * g) (g⁻¹ * y * g) := by
      rw [← commute_conj_iff g (g⁻¹ * t * g) (g⁻¹ * y * g), conj_inv_conj, conj_inv_conj]
    rw [e1, e2]
    exact key

theorem exists_separating_swap_fin5 : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    swap a b ≠ swap c d → ∃ e f : Fin 5, e ≠ f ∧ swap e f ≠ swap a b ∧ swap e f ≠ swap c d ∧
      swap e f * swap a b = swap a b * swap e f ∧
      swap e f * swap c d ≠ swap c d * swap e f := by decide

theorem exists_separating_transposition {σ₁ σ₂ : Perm (Fin 5)} (h₁ : σ₁ ∈ transpositions)
    (h₂ : σ₂ ∈ transpositions) (hne : σ₁ ≠ σ₂) :
    ∃ σ ∈ transpositions, σ ≠ σ₁ ∧ σ ≠ σ₂ ∧ Commute σ σ₁ ∧ ¬ Commute σ σ₂ := by
  obtain ⟨a, b, hab, rfl⟩ := h₁
  obtain ⟨c, d, hcd, rfl⟩ := h₂
  obtain ⟨e, f, hef, h1, h2, h3, h4⟩ := exists_separating_swap_fin5 a b c d hab hcd hne
  exact ⟨swap e f, ⟨e, f, hef, rfl⟩, h1, h2, h3, h4⟩

section Labelling

variable {θ : Set G} {ψ : G → Perm (Fin 5)}

omit [Finite G] in
theorem S5Labelling.eq_of_commute_of_mem_block (h : S5Labelling D θ ψ) {β : Set G}
    (hβ : β ∈ Dalpha D θ) {x y : G} (hx : x ∈ β) (hy : y ∈ β) (hxy : Commute x y) :
    x = y := by
  rcases (h.comm x (subset_DalphaStar hβ hx) y (subset_DalphaStar hβ hy)).mp hxy with he | ⟨hne, -⟩
  · exact he
  · exact absurd (h.block β hβ x hx y hy) hne

omit [Finite G] in
theorem S5Labelling.commute_of_label (h : S5Labelling D θ ψ) {x y : G}
    (hx : x ∈ DalphaStar D θ) (hy : y ∈ DalphaStar D θ) (hne : ψ x ≠ ψ y)
    (hc : Commute (ψ x) (ψ y)) : Commute x y :=
  (h.comm x hx y hy).mpr (Or.inr ⟨hne, hc⟩)

omit [Finite G] in
theorem S5Labelling.label_of_commute (h : S5Labelling D θ ψ) {x y : G}
    (hx : x ∈ DalphaStar D θ) (hy : y ∈ DalphaStar D θ) (hne : x ≠ y) (hc : Commute x y) :
    ψ x ≠ ψ y ∧ Commute (ψ x) (ψ y) :=
  ((h.comm x hx y hy).mp hc).resolve_left hne

omit [Finite G] in
theorem S5Labelling.not_commute_of_label_eq (h : S5Labelling D θ ψ) {x y : G}
    (hx : x ∈ DalphaStar D θ) (hy : y ∈ DalphaStar D θ) (hne : x ≠ y) (he : ψ x = ψ y) :
    ¬ Commute x y := fun hc => (h.label_of_commute hx hy hne hc).1 he

omit [Finite G] in
theorem S5Labelling.mem_Phi_iff (h : S5Labelling D θ ψ) {x y : G}
    (hx : x ∈ DalphaStar D θ) : y ∈ Phi D θ x ↔ y ∈ DalphaStar D θ ∧ ψ y = ψ x := by
  constructor
  · rintro ⟨hy, hall⟩
    refine ⟨hy, ?_⟩
    by_contra hne
    obtain ⟨σ, hσ, hσy, hσx, hcx, hncy⟩ :=
      exists_separating_transposition (h.mem x hx) (h.mem y hy) (Ne.symm hne)
    obtain ⟨t, ht, rfl⟩ := h.surj σ hσ
    have htx : t ≠ x := fun e => hσy (by rw [e])
    have hty : t ≠ y := fun e => hσx (by rw [e])
    have hct : Commute t x := h.commute_of_label ht hx hσy hcx
    exact hncy (h.label_of_commute ht hy hty ((hall t ht htx hty).mp hct)).2
  · rintro ⟨hy, he⟩
    refine ⟨hy, fun t ht htx hty => ?_⟩
    rw [h.comm t ht x hx, h.comm t ht y hy, he]
    simp only [htx, hty, false_or]

omit [Finite G] in
theorem S5Labelling.Phi_eq_of_mem (h : S5Labelling D θ ψ) {x y : G}
    (hx : x ∈ DalphaStar D θ) (hy : y ∈ Phi D θ x) : Phi D θ y = Phi D θ x := by
  have hy' := (h.mem_Phi_iff hx).mp hy
  ext z
  rw [h.mem_Phi_iff hy'.1, h.mem_Phi_iff hx, hy'.2]

omit [Finite G] in
theorem S5Labelling.mem_Phi_self (h : S5Labelling D θ ψ) {x : G} (hx : x ∈ DalphaStar D θ) :
    x ∈ Phi D θ x :=
  (h.mem_Phi_iff hx).mpr ⟨hx, rfl⟩

end Labelling

omit [Finite G] in
theorem conj_mem_DalphaStar (hN : IsNormalSet D) {θ : Set G} {x y : G}
    (hx : x ∈ DalphaStar D θ) (hy : y ∈ DalphaStar D θ) : x * y * x⁻¹ ∈ DalphaStar D θ := by
  have hxN : x ∈ Subgroup.normalizer (DalphaStar D θ) :=
    Halpha_le_normalizer hN (Subgroup.subset_closure hx)
  exact (Subgroup.mem_set_normalizer_iff.mp hxN y).mp hy

end CFSG.OddTranspositions.PropFourSeven


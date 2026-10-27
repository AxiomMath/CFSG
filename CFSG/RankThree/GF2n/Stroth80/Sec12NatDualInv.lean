module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualCoord
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Open.StatedAPI Matrix CFSG.ClassicalGroups.SpecialLinear

namespace NatDualCoord

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F} (C : NatDualCoord ρ ρ')

@[expose] def W₁ : AddSubgroup E :=
  AddSubgroup.comap C.Ψ.toAddMonoidHom ((⊤ : AddSubgroup (Fin n → F)).prod ⊥)

@[expose] def W₂ : AddSubgroup E :=
  AddSubgroup.comap C.Ψ.toAddMonoidHom ((⊥ : AddSubgroup (Fin n → F)).prod ⊤)

theorem mem_W₁ {e : E} : e ∈ C.W₁ ↔ (C.Ψ e).2 = 0 := by
  simp [W₁, AddSubgroup.mem_prod]

theorem mem_W₂ {e : E} : e ∈ C.W₂ ↔ (C.Ψ e).1 = 0 := by
  simp [W₂, AddSubgroup.mem_prod]

theorem inl_mem_W₁ (x : Fin n → F) : C.inl x ∈ C.W₁ := by
  rw [mem_W₁, Ψ_inl]

theorem inr_mem_W₂ (y : Fin n → F) : C.inr y ∈ C.W₂ := by
  rw [mem_W₂, Ψ_inr]

theorem eq_inl_of_mem_W₁ {e : E} (h : e ∈ C.W₁) : e = C.inl (C.Ψ e).1 := by
  have := C.eq_inl_add_inr e
  rw [mem_W₁] at h
  rw [h, map_zero, add_zero] at this
  exact this

theorem eq_inr_of_mem_W₂ {e : E} (h : e ∈ C.W₂) : e = C.inr (C.Ψ e).2 := by
  have := C.eq_inl_add_inr e
  rw [mem_W₂] at h
  rw [h, map_zero, zero_add] at this
  exact this

theorem inl_injective : Function.Injective C.inl := by
  intro x x' h
  have := congrArg C.Ψ h
  rw [Ψ_inl, Ψ_inl] at this
  exact (Prod.mk.inj this).1

theorem inr_injective : Function.Injective C.inr := by
  intro y y' h
  have := congrArg C.Ψ h
  rw [Ψ_inr, Ψ_inr] at this
  exact (Prod.mk.inj this).2

theorem invariant_classification (hn : 3 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (S : AddSubgroup E) (hS : ∀ (g : Γ) (e : E), e ∈ S → ρ g e ∈ S) :
    S = ⊥ ∨ S = C.W₁ ∨ S = C.W₂ ∨ S = ⊤ := by
  set W : AddSubgroup ((Fin n → F) × (Fin n → F)) := S.map C.Ψ.toAddMonoidHom with hW
  have hWinv : ∀ g ∈ StatedSL n F, ∀ p ∈ W,
      (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ p.1,
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *ᵥ p.2) ∈ W := by
    intro g hg p hp
    obtain ⟨s, hs⟩ : g ∈ ρ'.range := hrange ▸ hg
    obtain ⟨e, heS, rfl⟩ := AddSubgroup.mem_map.mp hp
    refine AddSubgroup.mem_map.mpr ⟨ρ s e, hS s e heS, ?_⟩
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    rw [C.act, hs]
    rfl
  have hcl := natDual_invariant_addSubgroup hn W hWinv
  have hSW : S = W.comap C.Ψ.toAddMonoidHom := by
    rw [hW]
    exact (AddSubgroup.comap_map_eq_self_of_injective
      (f := C.Ψ.toAddMonoidHom) C.Ψ.injective S).symm
  rw [hSW]
  rcases hcl with h | h | h | h
  · left
    rw [h]
    ext e
    simp [AddSubgroup.mem_comap]
  · right; left
    rw [h]
    rfl
  · right; right; left
    rw [h]
    rfl
  · right; right; right
    rw [h]
    ext e
    simp [AddSubgroup.mem_comap]

theorem ρ_mem_W₁ (g : Γ) {e : E} (h : e ∈ C.W₁) : ρ g e ∈ C.W₁ := by
  rw [C.eq_inl_of_mem_W₁ h, ρ_inl]
  exact C.inl_mem_W₁ _

theorem ρ_mem_W₂ (g : Γ) {e : E} (h : e ∈ C.W₂) : ρ g e ∈ C.W₂ := by
  rw [C.eq_inr_of_mem_W₂ h, ρ_inr]
  exact C.inr_mem_W₂ _

theorem exists_ne_zero (hn : 1 ≤ n) : ∃ x : Fin n → F, x ≠ 0 :=
  ⟨Pi.single ⟨0, by omega⟩ 1, Pi.single_ne_zero_iff.mpr one_ne_zero⟩

@[expose] def Preserves (T : E ≃ₗ[K] E) : Prop :=
  (∀ x, T (C.inl x) ∈ C.W₁) ∧ (∀ y, T (C.inr y) ∈ C.W₂)

@[expose] def Swaps (T : E ≃ₗ[K] E) : Prop :=
  (∀ x, T (C.inl x) ∈ C.W₂) ∧ (∀ y, T (C.inr y) ∈ C.W₁)

theorem map_invariant (T : E ≃ₗ[K] E) (hT : ∀ g : Γ, ∃ g' : Γ, ∀ e, ρ g (T e) = T (ρ g' e))
    (W : AddSubgroup E) (hW : ∀ (g : Γ) (e : E), e ∈ W → ρ g e ∈ W) (g : Γ) (e : E)
    (he : e ∈ W.map T.toAddEquiv.toAddMonoidHom) : ρ g e ∈ W.map T.toAddEquiv.toAddMonoidHom := by
  obtain ⟨e₀, he₀, rfl⟩ := AddSubgroup.mem_map.mp he
  obtain ⟨g', hg'⟩ := hT g
  refine AddSubgroup.mem_map.mpr ⟨ρ g' e₀, hW g' e₀ he₀, ?_⟩
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, LinearEquiv.coe_toAddEquiv]
  exact (hg' e₀).symm

theorem inr_mem_W₁_iff {y : Fin n → F} : C.inr y ∈ C.W₁ ↔ y = 0 := by
  rw [mem_W₁, Ψ_inr]

theorem inl_mem_W₂_iff {x : Fin n → F} : C.inl x ∈ C.W₂ ↔ x = 0 := by
  rw [mem_W₂, Ψ_inl]

theorem preserves_or_swaps (hn : 3 ≤ n) (hrange : ρ'.range = StatedSL n F) (T : E ≃ₗ[K] E)
    (hT : ∀ g : Γ, ∃ g' : Γ, ∀ e, ρ g (T e) = T (ρ g' e)) :
    C.Preserves T ∨ C.Swaps T := by
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero (F := F) (by omega : 1 ≤ n)
  have hinl0 : C.inl x₀ ≠ 0 := fun h => hx₀ (C.inl_injective (by rw [h, map_zero]))
  have hinr0 : C.inr x₀ ≠ 0 := fun h => hx₀ (C.inr_injective (by rw [h, map_zero]))
  have hTinj := T.injective
  have hnot : ∀ (W : AddSubgroup E) (e : E), e ∉ W →
      T e ∉ W.map T.toAddEquiv.toAddMonoidHom := by
    intro W e he hmem
    obtain ⟨e₀, he₀, h⟩ := AddSubgroup.mem_map.mp hmem
    apply he
    have : e₀ = e := hTinj h
    rwa [← this]
  have hi₁ := C.invariant_classification hn hrange (C.W₁.map T.toAddEquiv.toAddMonoidHom)
    (map_invariant T hT C.W₁ (fun g e he => C.ρ_mem_W₁ g he))
  have hi₂ := C.invariant_classification hn hrange (C.W₂.map T.toAddEquiv.toAddMonoidHom)
    (map_invariant T hT C.W₂ (fun g e he => C.ρ_mem_W₂ g he))
  have hmem₁ : ∀ x, T (C.inl x) ∈ C.W₁.map T.toAddEquiv.toAddMonoidHom := fun x =>
    AddSubgroup.mem_map.mpr ⟨C.inl x, C.inl_mem_W₁ x, rfl⟩
  have hmem₂ : ∀ y, T (C.inr y) ∈ C.W₂.map T.toAddEquiv.toAddMonoidHom := fun y =>
    AddSubgroup.mem_map.mpr ⟨C.inr y, C.inr_mem_W₂ y, rfl⟩
  have hinr_notW₁ : C.inr x₀ ∉ C.W₁ := fun h => hx₀ (C.inr_mem_W₁_iff.mp h)
  have hinl_notW₂ : C.inl x₀ ∉ C.W₂ := fun h => hx₀ (C.inl_mem_W₂_iff.mp h)
  have hT0 : ∀ e : E, T e = 0 → e = 0 := fun e h => hTinj (by rw [h, map_zero])
  have hS₁ : C.W₁.map T.toAddEquiv.toAddMonoidHom = C.W₁ ∨
      C.W₁.map T.toAddEquiv.toAddMonoidHom = C.W₂ := by
    rcases hi₁ with h | h | h | h
    · exfalso
      have := hmem₁ x₀
      rw [h, AddSubgroup.mem_bot] at this
      exact hinl0 (hT0 _ this)
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      exact hnot C.W₁ _ hinr_notW₁ (by rw [h]; trivial)
  have hS₂ : C.W₂.map T.toAddEquiv.toAddMonoidHom = C.W₁ ∨
      C.W₂.map T.toAddEquiv.toAddMonoidHom = C.W₂ := by
    rcases hi₂ with h | h | h | h
    · exfalso
      have := hmem₂ x₀
      rw [h, AddSubgroup.mem_bot] at this
      exact hinr0 (hT0 _ this)
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      exact hnot C.W₂ _ hinl_notW₂ (by rw [h]; trivial)
  rcases hS₁ with h₁ | h₁ <;> rcases hS₂ with h₂ | h₂
  · exfalso
    have h3 := hmem₂ x₀
    rw [h₂] at h3
    exact hnot C.W₁ _ hinr_notW₁ (by rw [h₁]; exact h3)
  · left
    refine ⟨fun x => ?_, fun y => ?_⟩
    · have := hmem₁ x
      rwa [h₁] at this
    · have := hmem₂ y
      rwa [h₂] at this
  · right
    refine ⟨fun x => ?_, fun y => ?_⟩
    · have := hmem₁ x
      rwa [h₁] at this
    · have := hmem₂ y
      rwa [h₂] at this
  · exfalso
    have h3 := hmem₁ x₀
    rw [h₁] at h3
    exact hnot C.W₂ _ hinl_notW₂ (by rw [h₂]; exact h3)

end NatDualCoord

namespace NatDualCoord

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F} (C : NatDualCoord ρ ρ')
  (Q : QuadDatum K E)

theorem eq_self_of_isometry (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (U : E →+ E) (hU : ∀ e, Q.Qf (U e) = Q.Qf e) (hl : ∀ x, U (C.inl x) = C.inl x)
    (hr : ∀ y, U (C.inr y) ∈ C.W₂) (e : E) : U e = e := by
  have hinr : ∀ y, U (C.inr y) = C.inr y := by
    intro y
    set d : E := U (C.inr y) - C.inr y with hd
    have hdW : d ∈ C.W₂ := C.W₂.sub_mem (hr y) (C.inr_mem_W₂ y)
    have hBl : ∀ x, Q.B (C.inl x) d = 0 := by
      intro x
      have h := Q.B_eq_of_isometry U hU (C.inl x) (C.inr y)
      rw [hl x] at h
      rw [hd, map_sub, h, sub_self]
    have hBr : ∀ z, Q.B (C.inr z) d = 0 := by
      intro z
      rw [C.eq_inr_of_mem_W₂ hdW, C.B_inr_inr Q hn hrange hQρ hK]
    have hall : ∀ e' : E, Q.B e' d = 0 := by
      intro e'
      rw [C.eq_inl_add_inr e', map_add, LinearMap.add_apply, hBl, hBr, add_zero]
    have hd0 : d = 0 := Q.nondeg _ fun f => by rw [Q.B_comm, hall f, neg_zero]
    exact sub_eq_zero.mp hd0
  conv_lhs => rw [C.eq_inl_add_inr e]
  rw [map_add, hl, hinr, ← C.eq_inl_add_inr e]

theorem exists_eq_of_preserves [Finite F] [CharP F 2] (hn : 3 ≤ n)
    (hrange : ρ'.range = StatedSL n F) (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e)
    (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1) (T : E ≃ₗ[K] E) (hT2 : ∀ e, T (T e) = e)
    (hTQ : ∀ e, Q.Qf (T e) = Q.Qf e) (hP : C.Preserves T) : ∃ g : Γ, ρ g = T := by
  have hTl : ∀ x, T (C.inl x) = C.inl (C.Ψ (T (C.inl x))).1 := fun x =>
    C.eq_inl_of_mem_W₁ (hP.1 x)
  let A₀ : (Fin n → F) →ₗ[F] (Fin n → F) :=
    { toFun := fun x => (C.Ψ (T (C.inl x))).1
      map_add' := fun x x' => by simp [map_add]
      map_smul' := fun a x => by
        have h1 : C.inl (a • x) = (C.θ₁.symm a) • C.inl x := by
          rw [C.smul_inl, RingEquiv.apply_symm_apply]
        have h2 := C.smul (C.θ₁.symm a) (T (C.inl x))
        simp only [RingHom.id_apply]
        rw [h1, map_smul, h2, RingEquiv.apply_symm_apply] }
  have hA₀ : ∀ x, T (C.inl x) = C.inl (A₀ x) := hTl
  have hAA : ∀ x, A₀ (A₀ x) = x := by
    intro x
    apply C.inl_injective
    rw [← hA₀, ← hA₀, hT2]
  set Amat : Matrix (Fin n) (Fin n) F := LinearMap.toMatrix' A₀ with hAmat
  have hAmatv : ∀ x, Amat *ᵥ x = A₀ x := fun x => by
    rw [← Matrix.toLin'_apply, hAmat, Matrix.toLin'_toMatrix']
  have hAmat2 : Amat * Amat = 1 := by
    have h : A₀ ∘ₗ A₀ = LinearMap.id := LinearMap.ext hAA
    have := congrArg LinearMap.toMatrix' h
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  let A : GL (Fin n) F := ⟨Amat, Amat, hAmat2, hAmat2⟩
  have hAA1 : A * A = 1 := Units.ext hAmat2
  have hdet : (A : Matrix (Fin n) (Fin n) F).det = 1 :=
    det_eq_one_of_pow_two_pow_eq_one A (k := 1) (by rw [pow_one, pow_two, hAA1])
  obtain ⟨g, hg⟩ := exists_eq_of_mem_statedSL hrange (mem_statedSL_of_det hdet)
  have hinvA : A⁻¹ = A := inv_eq_of_mul_eq_one_right hAA1
  let U : E →+ E :=
    (ρ g⁻¹).toAddEquiv.toAddMonoidHom.comp T.toAddEquiv.toAddMonoidHom
  have hUapp : ∀ e, U e = ρ g⁻¹ (T e) := fun e => rfl
  have hU : ∀ e, Q.Qf (U e) = Q.Qf e := fun e => by rw [hUapp, hQρ, hTQ]
  have hl : ∀ x, U (C.inl x) = C.inl x := by
    intro x
    rw [hUapp, hA₀, C.ρ_inl, map_inv, hg, hinvA]
    congr 1
    show Amat *ᵥ (A₀ x) = x
    rw [hAmatv, hAA]
  have hr : ∀ y, U (C.inr y) ∈ C.W₂ := fun y => by
    rw [hUapp]
    exact C.ρ_mem_W₂ _ (hP.2 y)
  have hall := C.eq_self_of_isometry Q (by omega) hrange hQρ hK U hU hl hr
  refine ⟨g, LinearEquiv.ext fun e => ?_⟩
  have h := hall e
  rw [hUapp] at h
  calc ρ g e = ρ g (ρ g⁻¹ (T e)) := by rw [h]
    _ = T e := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl

end NatDualCoord

end CFSG.RankThree.GF2n.Stroth80

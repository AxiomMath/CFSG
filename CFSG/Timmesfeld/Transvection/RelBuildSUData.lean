module

public import CFSG.Timmesfeld.Transvection.RelBuildBasic
public import CFSG.Timmesfeld.Transvection.RelBuildField

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

structure PreSURelations (r : ℕ) {F : Type*} [Field F] (σ : F ≃+* F) (G : Type*) [Group G]
    extends PreRelations r σ G where
  inj : ∀ a b, idx a ≠ idx b → Function.Injective (ξ a b)
  injL : ∀ a s t, σ s = s → σ t = t → ξL a s = ξL a t → s = t
  short : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∀ s t, ∃ u,
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) u ∧
      σ u * u = σ s * s * (σ t * t)
  shortSMul : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∀ c s t u, σ c = c →
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) u →
      ⁅ξ (.inl j) (.inr i) (c * s), ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) (c * u) ∧
        ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) (c * t)⁆ = ξ (.inl k) (.inr i) (c * u)

namespace RelBuild

theorem comm_mul_left {G : Type*} [Group G] (a b c : G) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_right {G : Type*} [Group G] (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem tetra {G : Type*} [Group G] {x u y : G} (hxy : x * y = y * x)
    (h₁ : ⁅u, y⁆ * ⁅x, u⁆ = ⁅x, u⁆ * ⁅u, y⁆)
    (h₂ : ⁅u, y⁆ * ⁅⁅x, u⁆, y⁆ = ⁅⁅x, u⁆, y⁆ * ⁅u, y⁆) : ⁅x, ⁅u, y⁆⁆ = ⁅⁅x, u⁆, y⁆ := by
  have hy : x * y * x⁻¹ = y := by rw [hxy]; group
  have hz : x * u * x⁻¹ = ⁅x, u⁆ * u := by simp only [commutatorElement_def]; group
  calc ⁅x, ⁅u, y⁆⁆ = (x * u * x⁻¹) * (x * y * x⁻¹) * (x * u * x⁻¹)⁻¹ * (x * y * x⁻¹)⁻¹ *
        ⁅u, y⁆⁻¹ := by simp only [commutatorElement_def]; group
    _ = (⁅x, u⁆ * u) * y * (⁅x, u⁆ * u)⁻¹ * y⁻¹ * ⁅u, y⁆⁻¹ := by rw [hy, hz]
    _ = ⁅x, u⁆ * ⁅u, y⁆ * ⁅x, u⁆⁻¹ * ⁅⁅x, u⁆, y⁆ * ⁅u, y⁆⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅u, y⁆ * ⁅⁅x, u⁆, y⁆ * ⁅u, y⁆⁻¹ := by rw [← h₁]; group
    _ = ⁅⁅x, u⁆, y⁆ := by rw [h₂]; group

end RelBuild

namespace PreRelations

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} {G : Type*} [Group G]
  (P : PreRelations r σ G)

theorem inv_eq [CharP F 2] {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (c : F) :
    (P.ξ a b c)⁻¹ = P.ξ a b c := by
  have h := P.add a b hab c c
  rw [CharTwo.add_self_eq_zero, P.map_zero hab] at h
  exact inv_eq_of_mul_eq_one_left h.symm

@[expose] def ShortRel (i j k : Fin r) (M : F → F → F) : Prop :=
  ∀ a b d : Fin r ⊕ Fin r, idx a = i → idx b = j → idx d = k → ∀ s t,
    ⁅P.ξ a b s, P.ξ (Sum.swap b) d t⁆ = P.ξ a d (M s t)

theorem shortRel_of_pattern {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {M : F → F → F} {a₀ b₀ d₀ : Fin r ⊕ Fin r} (ha : idx a₀ = i) (hb : idx b₀ = j)
    (hd : idx d₀ = k) (h : ∀ s t, ⁅P.ξ a₀ b₀ s, P.ξ (Sum.swap b₀) d₀ t⁆ = P.ξ a₀ d₀ (M s t)) :
    P.ShortRel i j k M := by
  intro a b d ha' hb' hd' s t
  have key := RelBuild.of_flip (fun Q : Fin 3 → Fin r ⊕ Fin r => idx (Q 0) ≠ idx (Q 1) →
      idx (Q 1) ≠ idx (Q 2) → idx (Q 0) ≠ idx (Q 2) →
      ∀ s t, ⁅P.ξ (Q 0) (Q 1) s, P.ξ (Sum.swap (Q 1)) (Q 2) t⁆ = P.ξ (Q 0) (Q 2) (M s t))
    (fun k Q hQ h1 h2 h3 s t => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at h1 h2 h3 ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ h1 h2 h3 s t)
      simp only [RelBuild.conj_commutatorElement] at h
      rwa [P.weyl k _ _ h1, P.weyl k _ _ (by rwa [idx_swap]), P.weyl k _ _ h3,
        RelBuild.flip_swap] at h)
    (P := ![a₀, b₀, d₀]) (P' := ![a, b, d])
    (fun x => by fin_cases x <;> simp [ha, hb, hd, ha', hb', hd'])
    (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ _ _ s t => by simpa using h s t)
  simpa using key (by simpa [ha', hb'] using hij) (by simpa [hb', hd'] using hjk)
    (by simpa [ha', hd'] using hik) s t

variable {P} in
theorem ShortRel.unique (hinj : ∀ a b, idx a ≠ idx b → Function.Injective (P.ξ a b))
    {i k : Fin r} (j : Fin r) (hik : i ≠ k) {M M' : F → F → F} (h : P.ShortRel i j k M)
    (h' : P.ShortRel i j k M') (s t : F) : M s t = M' s t :=
  hinj _ _ (by simpa using hik) ((h (.inl i) (.inl j) (.inl k) rfl rfl rfl s t).symm.trans
    (h' (.inl i) (.inl j) (.inl k) rfl rfl rfl s t))

variable {P} in
theorem ShortRel.rev [CharP F 2] {i j k : Fin r} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) {M : F → F → F} (h : P.ShortRel i j k M) :
    P.ShortRel k j i (fun t s => σ (M (σ s) (σ t))) := by
  intro a b d ha hb hd t s
  have hab : idx a ≠ idx b := by rw [ha, hb]; exact hjk.symm
  have hdb : idx d ≠ idx (Sum.swap b) := by rw [idx_swap, hb, hd]; exact hij
  have had : idx a ≠ idx d := by rw [ha, hd]; exact hik.symm
  have key := h d (Sum.swap b) a hd (by rw [idx_swap, hb]) ha (σ s) (σ t)
  rw [Sum.swap_swap, ← P.swap d (Sum.swap b) hdb s, ← P.swap b a (Ne.symm hab) t] at key
  rw [← commutatorElement_inv, key, P.inv_eq (Ne.symm had), P.swap a d had]

end PreRelations

namespace RelBuild

structure SUData (r : ℕ) {F : Type*} [Field F] (σ : F ≃+* F) (G : Type*) [Group G]
    extends PreRelations r σ G where
  inj : ∀ a b, idx a ≠ idx b → Function.Injective (ξ a b)
  injL : ∀ a s t, σ s = s → σ t = t → ξL a s = ξL a t → s = t
  μ : Fin r → Fin r → Fin r → F → F → F
  hμ : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∀ s t,
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) (μ i j k s t)
  hμN : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∀ s t,
    σ (μ i j k s t) * μ i j k s t = σ s * s * (σ t * t)
  hμK : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∀ c s t, σ c = c →
    μ i j k (c * s) t = c * μ i j k s t ∧ μ i j k s (c * t) = c * μ i j k s t

end RelBuild

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} {G : Type*} [Group G]

@[expose] noncomputable def PreSURelations.toData (P : PreSURelations r σ G) :
    RelBuild.SUData r σ G where
  toPreRelations := P.toPreRelations
  inj := P.inj
  injL := P.injL
  μ i j k s t := if h : i ≠ j ∧ j ≠ k ∧ i ≠ k then
    (P.short i j k h.1 h.2.1 h.2.2 s t).choose else 0
  hμ i j k hij hjk hik s t := by
    rw [dite_eq_left (⟨hij, hjk, hik⟩ : i ≠ j ∧ j ≠ k ∧ i ≠ k)]
    exact (P.short i j k hij hjk hik s t).choose_spec.1
  hμN i j k hij hjk hik s t := by
    rw [dite_eq_left (⟨hij, hjk, hik⟩ : i ≠ j ∧ j ≠ k ∧ i ≠ k)]
    exact (P.short i j k hij hjk hik s t).choose_spec.2
  hμK i j k hij hjk hik c s t hc := by
    simp only [dite_eq_left (⟨hij, hjk, hik⟩ : i ≠ j ∧ j ≠ k ∧ i ≠ k)]
    have hu := (P.short i j k hij hjk hik s t).choose_spec.1
    obtain ⟨h₁, h₂⟩ := P.shortSMul i j k hij hjk hik c s t _ hc hu
    have hik' : idx (Sum.inl k : Fin r ⊕ Fin r) ≠ idx (Sum.inr i) := by simpa using hik.symm
    exact ⟨P.inj _ _ hik' ((P.short i j k hij hjk hik (c * s) t).choose_spec.1.symm.trans h₁),
      P.inj _ _ hik' ((P.short i j k hij hjk hik s (c * t)).choose_spec.1.symm.trans h₂)⟩

@[simp] theorem PreSURelations.toData_ξ (P : PreSURelations r σ G) : P.toData.ξ = P.ξ := rfl

@[simp] theorem PreSURelations.toData_ξL (P : PreSURelations r σ G) : P.toData.ξL = P.ξL := rfl

namespace RelBuild.SUData

variable (D : SUData r σ G)

theorem shortRel_μ [CharP F 2] {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    D.ShortRel k j i (fun t s => D.μ i j k s t) := by
  refine D.shortRel_of_pattern hjk.symm hij.symm hik.symm (a₀ := .inl k) (b₀ := .inr j)
    (d₀ := .inr i) rfl rfl rfl fun t s => ?_
  rw [Sum.swap_inr, ← commutatorElement_inv, D.hμ i j k hij hjk hik s t,
    D.inv_eq (by simpa using hik.symm)]

theorem μ_rev [CharP F 2] {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t : F) :
    D.μ k j i t s = σ (D.μ i j k (σ s) (σ t)) :=
  PreRelations.ShortRel.unique D.inj j hik (D.shortRel_μ hjk.symm hij.symm hik.symm)
    ((D.shortRel_μ hij hjk hik).rev hjk.symm hij.symm hik.symm) s t

theorem μ_add_left {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s s' t : F) :
    D.μ i j k (s + s') t = D.μ i j k s t + D.μ i j k s' t := by
  have hki : idx (Sum.inl k : Fin r ⊕ Fin r) ≠ idx (Sum.inr i) := by simpa using hik.symm
  have hji : idx (Sum.inl j : Fin r ⊕ Fin r) ≠ idx (Sum.inr i) := by simpa using hij.symm
  have hc : D.ξ (.inl j) (.inr i) s * D.ξ (.inl k) (.inr i) (D.μ i j k s' t) =
      D.ξ (.inl k) (.inr i) (D.μ i j k s' t) * D.ξ (.inl j) (.inr i) s :=
    commutatorElement_eq_one_iff_mul_comm.1 (D.commSS' hji hki (by simp)
      (by simpa using hik.symm) (by simpa using hij) (by simp) s _)
  apply D.inj _ _ hki
  have e1 := D.hμ i j k hij hjk hik (s + s') t
  rw [D.add _ _ hji, RelBuild.comm_mul_left, D.hμ i j k hij hjk hik s' t,
    D.hμ i j k hij hjk hik s t] at e1
  rw [← e1, add_comm (D.μ i j k s t), D.add _ _ hki, hc]
  group

theorem μ_add_right {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t t' : F) :
    D.μ i j k s (t + t') = D.μ i j k s t + D.μ i j k s t' := by
  have hki : idx (Sum.inl k : Fin r ⊕ Fin r) ≠ idx (Sum.inr i) := by simpa using hik.symm
  have hkj : idx (Sum.inl k : Fin r ⊕ Fin r) ≠ idx (Sum.inr j) := by simpa using hjk.symm
  have hc : D.ξ (.inl k) (.inr j) t * D.ξ (.inl k) (.inr i) (D.μ i j k s t') =
      D.ξ (.inl k) (.inr i) (D.μ i j k s t') * D.ξ (.inl k) (.inr j) t :=
    commutatorElement_eq_one_iff_mul_comm.1 (D.commSS' hkj hki (by simp)
      (by simpa using hjk.symm) (by simpa using hik) (by simp) t _)
  apply D.inj _ _ hki
  have e1 := D.hμ i j k hij hjk hik s (t + t')
  rw [D.add _ _ hkj, RelBuild.comm_mul_right, D.hμ i j k hij hjk hik s t,
    D.hμ i j k hij hjk hik s t'] at e1
  rw [← e1, D.add _ _ hki, hc]
  group

theorem μ_tetra {i j k l : Fin r} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) (a b c : F) :
    D.μ i j l a (D.μ j k l b c) = D.μ i k l (D.μ i j k a b) c := by
  apply D.inj (.inl l) (.inr i) (by simpa using hil.symm)
  rw [← D.hμ i j l hij hjl hil, ← D.hμ j k l hjk hkl hjl, ← D.hμ i k l hik hkl hil,
    ← D.hμ i j k hij hjk hik]
  refine RelBuild.tetra ?_ ?_ ?_
  · exact commutatorElement_eq_one_iff_mul_comm.1 (D.commSS' (by simpa using hij.symm)
      (by simpa using hkl.symm) (by simp) (by simpa using hil.symm) (by simpa using hjk.symm)
      (by simp) a c)
  · rw [D.hμ j k l hjk hkl hjl, D.hμ i j k hij hjk hik]
    exact commutatorElement_eq_one_iff_mul_comm.1 (D.commSS' (by simpa using hjl.symm)
      (by simpa using hik.symm) (by simp) (by simpa using hjk.symm) (by simpa using hil)
      (by simp) _ _)
  · rw [D.hμ j k l hjk hkl hjl, D.hμ i j k hij hjk hik, D.hμ i k l hik hkl hil]
    exact commutatorElement_eq_one_iff_mul_comm.1 (D.commSS' (by simpa using hjl.symm)
      (by simpa using hil.symm) (by simp) (by simpa using hjl.symm) (by simpa using hil)
      (by simp) _ _)

theorem eq_zero_of_ξ_eq_ξL [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hne : ∃ θ, σ θ ≠ θ)
    {j k : Fin r} (hjk : j ≠ k) {e f : F} (hf : σ f = f)
    (h : D.ξ (.inl j) (.inl k) e = D.ξL (.inl k) f) : e = 0 := by
  have hkj : idx (Sum.inl k : Fin r ⊕ Fin r) ≠ idx (Sum.inl j) := by simpa using hjk.symm
  have hg : D.ξ (.inl k) (.inl j) (σ e) = D.ξL (.inl k) f := by
    rw [D.swap _ _ (Ne.symm hkj), hσ, h]
  have key : ∀ q, D.ξL (.inl k) (σ e * σ q + e * q) = D.ξL (.inl k) 0 := by
    intro q
    have ht := D.trace' hσ hkj (σ e) q
    rw [hσ, Sum.swap_inl, hg, D.commLS_self (by simpa using hjk.symm) hf q] at ht
    rw [← ht, D.mapL_zero]
  refine RelBuild.eq_zero_of_trace_mul hne fun q => ?_
  have h0 := D.injL _ _ _ (by simp only [map_add, map_mul, hσ]; ring) (_root_.map_zero σ)
    (key q)
  rw [map_mul]
  linear_combination h0

end RelBuild.SUData

namespace RelBuild

structure Recoord (r : ℕ) {F : Type*} [Field F] (σ : F ≃+* F) where
  θ : Fin r → Fin r → F ≃+ F
  swap : ∀ i j c, θ j i c = σ (θ i j (σ c))
  smul : ∀ i j c s, σ c = c → θ i j (c * s) = c * θ i j s
  norm : ∀ i j s, σ (θ i j s) * θ i j s = σ s * s

namespace Recoord

variable (T : Recoord r σ)

theorem symm_smul (i j : Fin r) {c : F} (hc : σ c = c) (x : F) :
    (T.θ i j).symm (c * x) = c * (T.θ i j).symm x := by
  apply (T.θ i j).injective
  rw [AddEquiv.apply_symm_apply, T.smul i j c _ hc, AddEquiv.apply_symm_apply]

theorem symm_norm (i j : Fin r) (x : F) :
    σ ((T.θ i j).symm x) * (T.θ i j).symm x = σ x * x := by
  rw [← T.norm i j, AddEquiv.apply_symm_apply]

theorem trace (i j : Fin r) (s t : F) :
    T.θ i j s * σ (T.θ i j t) + σ (T.θ i j s) * T.θ i j t = s * σ t + σ s * t := by
  have h := T.norm i j (s + t)
  simp only [map_add] at h
  linear_combination h - T.norm i j s - T.norm i j t

end Recoord

namespace SUData

variable (D : SUData r σ G)

@[expose] noncomputable def recoord (hσ : ∀ c, σ (σ c) = c) (T : Recoord r σ) :
    SUData r σ G where
  ξ a b c := D.ξ a b (T.θ (idx b) (idx a) c)
  ξL := D.ξL
  w := D.w
  swap a b hab c := by
    rw [D.swap a b hab, T.swap (idx a) (idx b) (σ c), hσ]
  add a b hab s t := by rw [map_add, D.add a b hab]
  addL := D.addL
  weyl k a b hab c := by rw [D.weyl k a b hab, idx_flip, idx_flip]
  weylL := D.weylL
  shortLong i j hij s t ht := by
    simp only [idx_inl, idx_inr]
    rw [D.shortLong i j hij _ t ht, T.norm, mul_comm s t, T.smul i j t s ht, mul_comm t]
  trace i j hij s t := by
    simp only [idx_inl, idx_inr]
    rw [D.trace i j hij, T.trace]
  commLL := D.commLL
  commLS i j hij s t hs := D.commLS i j hij s _ hs
  commLS₃ i j k h₁ h₂ h₃ s t hs := D.commLS₃ i j k h₁ h₂ h₃ s _ hs
  commSS₃ i j k h₁ h₂ h₃ s t := D.commSS₃ i j k h₁ h₂ h₃ _ _
  commSS₄ i j k l h₁ h₂ h₃ h₄ h₅ h₆ s t := D.commSS₄ i j k l h₁ h₂ h₃ h₄ h₅ h₆ _ _
  inj a b hab := (D.inj a b hab).comp (T.θ (idx b) (idx a)).injective
  injL := D.injL
  μ i j k s t := (T.θ i k).symm (D.μ i j k (T.θ i j s) (T.θ j k t))
  hμ i j k hij hjk hik s t := by
    simp only [idx_inl, idx_inr]
    rw [D.hμ i j k hij hjk hik, AddEquiv.apply_symm_apply]
  hμN i j k hij hjk hik s t := by
    rw [T.symm_norm, D.hμN i j k hij hjk hik, T.norm, T.norm]
  hμK i j k hij hjk hik c s t hc := by
    rw [T.smul i j c s hc, T.smul j k c t hc, (D.hμK i j k hij hjk hik c _ _ hc).1,
      (D.hμK i j k hij hjk hik c _ _ hc).2, T.symm_smul i k hc]
    exact ⟨rfl, rfl⟩

@[simp] theorem recoord_ξ (hσ : ∀ c, σ (σ c) = c) (T : Recoord r σ) (a b : Fin r ⊕ Fin r)
    (c : F) : (D.recoord hσ T).ξ a b c = D.ξ a b (T.θ (idx b) (idx a) c) := rfl

@[simp] theorem recoord_ξL (hσ : ∀ c, σ (σ c) = c) (T : Recoord r σ) :
    (D.recoord hσ T).ξL = D.ξL := rfl

theorem recoord_μ (hσ : ∀ c, σ (σ c) = c) (T : Recoord r σ) (i j k : Fin r) (s t : F) :
    (D.recoord hσ T).μ i j k s t = (T.θ i k).symm (D.μ i j k (T.θ i j s) (T.θ j k t)) := rfl

@[expose] def Reparam (D' D : SUData r σ G) : Prop :=
  D'.ξL = D.ξL ∧ ∀ a b, idx a ≠ idx b → ∃ θ : F ≃+ F, ∀ c, D'.ξ a b c = D.ξ a b (θ c)

theorem reparam_refl : D.Reparam D :=
  ⟨rfl, fun _ _ _ => ⟨AddEquiv.refl F, fun _ => rfl⟩⟩

theorem Reparam.trans {D₁ D₂ D₃ : SUData r σ G} (h₁ : D₁.Reparam D₂) (h₂ : D₂.Reparam D₃) :
    D₁.Reparam D₃ := by
  refine ⟨h₁.1.trans h₂.1, fun a b hab => ?_⟩
  obtain ⟨θ₁, hθ₁⟩ := h₁.2 a b hab
  obtain ⟨θ₂, hθ₂⟩ := h₂.2 a b hab
  exact ⟨θ₁.trans θ₂, fun c => by rw [hθ₁, hθ₂]; rfl⟩

theorem recoord_reparam (hσ : ∀ c, σ (σ c) = c) (T : Recoord r σ) :
    (D.recoord hσ T).Reparam D :=
  ⟨rfl, fun a b _ => ⟨T.θ (idx b) (idx a), fun _ => rfl⟩⟩

end SUData

end RelBuild

end CFSG.Timmesfeld.Transvection

module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tw
public import CFSG.Quasithin.Vol2.Ch10SecK2Tu

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA
open scoped IsMulCommutative commutatorElement

variable {Γ : Type} [Group Γ]

theorem sup_mem_normalizer {A B : Subgroup Γ} {g : Γ}
    (hA : g ∈ Subgroup.normalizer (A : Set Γ)) (hB : g ∈ Subgroup.normalizer (B : Set Γ)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_of_conj_mem [Finite Γ] {X : Subgroup Γ} {g : Γ}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

theorem not_le_centralizer_of_validX {J L R W X : Subgroup Γ} {q : ℕ} (hLJ : L ≤ J)
    (hX : ValidX J L R W q X) (hne : X ≠ ⊥) : ¬ J ≤ Subgroup.centralizer (W : Set Γ) := by
  intro h
  apply hne
  rw [← hX.comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (h (hLJ hl)) x (hX.le hx)).symm

section Graph

variable [Finite Γ] {J L V₁ W₁ W₂ U : Subgroup Γ} [IsMulCommutative ↥W₁]
  {hJU : J ≤ Subgroup.normalizer (U : Set Γ)} {p₁ : ↥U →* ↥W₁} {p₂ : ↥U →* ↥W₂}

omit [Finite Γ] [IsMulCommutative ↥W₁] in
theorem conj_decomp (hJ₁ : J ≤ Subgroup.normalizer (W₁ : Set Γ))
    (hdec : ∀ u : ↥U, ((p₁ u : ↥W₁) : Γ) * (p₂ u : ↥W₂) = u) (ι : ↥W₁ ≃* ↥W₂)
    (hι : ∀ (g : Γ) (hg : g ∈ J) (w : ↥W₁),
      ((ι ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJ₁ hg) w).mp w.2⟩ : ↥W₂) : Γ) =
        g * ι w * g⁻¹) {x : Γ} (hx : x ∈ J) (u : ↥U) :
    x * (u : Γ) * x⁻¹ = ((conjAct W₁ ⟨x, hJ₁ hx⟩ (p₁ u) : ↥W₁) : Γ) *
      (ι (conjAct W₁ ⟨x, hJ₁ hx⟩ (ι.symm (p₂ u))) : ↥W₂) := by
  have e : conjAct W₁ ⟨x, hJ₁ hx⟩ (ι.symm (p₂ u)) = ⟨x * (ι.symm (p₂ u) : Γ) * x⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hJ₁ hx) _).mp (ι.symm (p₂ u)).2⟩ :=
    Subtype.ext (Setup.coe_conjAct_apply _ _)
  rw [e, hι x hx, MulEquiv.apply_symm_apply, Setup.coe_conjAct_apply]
  conv_lhs => rw [← hdec u]
  group

omit [Finite Γ] in
theorem graph_case_bot {ι : ↥W₁ ≃* ↥W₂} {ℓ : Subgroup ↥W₁} {t : MulAut ↥W₁} {g : Γ}
    (hJ₁ : J ≤ Subgroup.normalizer (W₁ : Set Γ))
    (hgU : ∀ {x : Γ} (_ : x ∈ J) (u : ↥U), x * (u : Γ) * x⁻¹ ∈ U)
    (hp₁' : ∀ {x : Γ} (hx : x ∈ J) (u : ↥U),
      conjAct W₁ ⟨x, hJ₁ hx⟩ (p₁ u) = p₁ ⟨x * u * x⁻¹, hgU hx u⟩)
    (hp₂' : ∀ {x : Γ} (hx : x ∈ J) (u : ↥U),
      conjAct W₁ ⟨x, hJ₁ hx⟩ (ι.symm (p₂ u)) = ι.symm (p₂ ⟨x * u * x⁻¹, hgU hx u⟩))
    (hconj : ∀ u : ↥U, g * (u : Γ) * g⁻¹ =
      ((t (p₁ u) : ↥W₁) : Γ) * (ι (t (ι.symm (p₂ u))) : ↥W₂))
    (hK0 : (V₁.subgroupOf W₂).comap ι.toMonoidHom = ⊥)
    (hA : ∀ u : ↥U, (u : Γ) ∈ V₁ → p₁ u ∈ ℓ)
    (hA' : ∀ a ∈ ℓ, ∃ u : ↥U, (u : Γ) ∈ V₁ ∧ p₁ u = a)
    (hB : ∀ u : ↥U, (u : Γ) ∈ V₁ → ι.symm (p₂ u) ∈ ℓ)
    (hsℓ : ∀ s ∈ autOn L W₁, ∀ w ∈ ℓ, s w ∈ ℓ)
    (he : ∀ φ ψ : ↥W₁ → ↥W₁, (∀ u ∈ ℓ, φ u ∈ ℓ) → (∀ u ∈ ℓ, ψ u ∈ ℓ) →
      (∀ u ∈ ℓ, ∀ v ∈ ℓ, φ (u * v) = φ u * φ v) → (∀ u ∈ ℓ, ∀ v ∈ ℓ, ψ (u * v) = ψ u * ψ v) →
      (∀ s ∈ autOn L W₁, ∀ u ∈ ℓ, φ (s u) = s (φ u)) →
      (∀ s ∈ autOn L W₁, ∀ u ∈ ℓ, ψ (s u) = s (ψ u)) → ∀ y ∈ ℓ, φ (ψ y) = ψ (φ y))
    (htℓ : ∀ w ∈ ℓ, t w ∈ ℓ) (htL : ∀ s ∈ autOn L W₁, ∀ w ∈ ℓ, (t * s * t⁻¹ * s⁻¹) w = w)
    (hLJ : L ≤ J) (hLV₁ : L ≤ Subgroup.normalizer (V₁ : Set Γ)) (hV₁U : V₁ ≤ U)
    (hdec : ∀ u : ↥U, ((p₁ u : ↥W₁) : Γ) * (p₂ u : ↥W₂) = u) :
    ∀ v ∈ V₁, g * v * g⁻¹ ∈ V₁ := by
  classical
  have hinj : ∀ u u' : ↥U, (u : Γ) ∈ V₁ → (u' : Γ) ∈ V₁ → p₁ u = p₁ u' → u = u' := by
    intro u u' hu hu' h
    have hm : ((u * u'⁻¹ : ↥U) : Γ) ∈ V₁ := V₁.mul_mem hu (V₁.inv_mem hu')
    have h1 : p₁ (u * u'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 : ((p₂ (u * u'⁻¹) : ↥W₂) : Γ) = (u * u'⁻¹ : ↥U) := by
      rw [← hdec (u * u'⁻¹), h1, Subgroup.coe_one, one_mul]
    have h3 : ι.symm (p₂ (u * u'⁻¹)) ∈ (V₁.subgroupOf W₂).comap ι.toMonoidHom := by
      show ((ι (ι.symm (p₂ (u * u'⁻¹))) : ↥W₂) : Γ) ∈ V₁
      rw [MulEquiv.apply_symm_apply, h2]
      exact hm
    rw [hK0, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h3
    have h4 : ((u * u'⁻¹ : ↥U) : Γ) = 1 := by rw [← h2, h3, Subgroup.coe_one]
    exact mul_inv_eq_one.mp (Subtype.ext h4)
  let θ : ↥W₁ → ↥W₁ := fun a =>
    ι.symm (p₂ (Classical.epsilon fun u : ↥U => (u : Γ) ∈ V₁ ∧ p₁ u = a))
  have hθ : ∀ u : ↥U, (u : Γ) ∈ V₁ → θ (p₁ u) = ι.symm (p₂ u) := by
    intro u hu
    have hs := Classical.epsilon_spec (p := fun u' : ↥U => (u' : Γ) ∈ V₁ ∧ p₁ u' = p₁ u)
      ⟨u, hu, rfl⟩
    show ι.symm (p₂ (Classical.epsilon fun u' : ↥U => (u' : Γ) ∈ V₁ ∧ p₁ u' = p₁ u)) = _
    rw [hinj _ _ hs.1 hu hs.2]
  have hcomm := he t θ htℓ
    (fun a ha => by
      obtain ⟨u, hu, rfl⟩ := hA' a ha
      rw [hθ u hu]
      exact hB u hu)
    (fun a _ b _ => map_mul t a b)
    (fun a ha b hb => by
      obtain ⟨u, hu, rfl⟩ := hA' a ha
      obtain ⟨u', hu', rfl⟩ := hA' b hb
      rw [← map_mul, hθ _ (V₁.mul_mem hu hu'), hθ u hu, hθ u' hu', map_mul, map_mul])
    (fun s hs a ha => by
      have h := htL s hs (s (t a)) (hsℓ s hs _ (htℓ a ha))
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self,
        MulAut.inv_apply_self] at h
      exact h)
    (fun s hs a ha => by
      obtain ⟨l', hl'L, rfl⟩ := Setup.mem_autOn_iff.mp hs
      obtain ⟨u, hu, rfl⟩ := hA' a ha
      have hl' : l' = ⟨(l' : Γ), hJ₁ (hLJ hl'L)⟩ := Subtype.ext rfl
      rw [hl', hp₁' (hLJ hl'L) u, hθ u hu, hp₂' (hLJ hl'L) u, hθ _ ((Subgroup.mem_normalizer_iff.mp
        (hLV₁ hl'L) u).mp hu)])
  intro v hv
  obtain ⟨u', hu', hu'e⟩ := hA' _ (htℓ _ (hA ⟨v, hV₁U hv⟩ hv))
  have h1 : ι.symm (p₂ u') = θ (t (p₁ ⟨v, hV₁U hv⟩)) := by rw [← hu'e, hθ u' hu']
  have h2 : θ (t (p₁ ⟨v, hV₁U hv⟩)) = t (θ (p₁ ⟨v, hV₁U hv⟩)) :=
    (hcomm _ (hA ⟨v, hV₁U hv⟩ hv)).symm
  rw [show v = ((⟨v, hV₁U hv⟩ : ↥U) : Γ) from rfl, hconj, ← hθ _ hv, ← h2, ← h1,
    MulEquiv.apply_symm_apply, ← hu'e, hdec u']
  exact hu'

omit [Finite Γ] in
theorem conj_mem_of_graph (h12 : W₁ ⊓ W₂ = ⊥) (hJ₁ : J ≤ Subgroup.normalizer (W₁ : Set Γ))
    (hLJ : L ≤ J) (hLV₁ : L ≤ Subgroup.normalizer (V₁ : Set Γ)) (hV₁U : V₁ ≤ U) (hW₂U : W₂ ≤ U)
    (hdec : ∀ u : ↥U, ((p₁ u : ↥W₁) : Γ) * (p₂ u : ↥W₂) = u)
    (hp₁ : IsEquivJ hJU p₁) (hp₂ : IsEquivJ hJU p₂) (ι : ↥W₁ ≃* ↥W₂)
    (hι : ∀ (g : Γ) (hg : g ∈ J) (w : ↥W₁),
      ((ι ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJ₁ hg) w).mp w.2⟩ : ↥W₂) : Γ) =
        g * ι w * g⁻¹)
    {ℓ : Subgroup ↥W₁} (hA : ∀ u : ↥U, (u : Γ) ∈ V₁ → p₁ u ∈ ℓ)
    (hA' : ∀ a ∈ ℓ, ∃ u : ↥U, (u : Γ) ∈ V₁ ∧ p₁ u = a)
    (hB : ∀ u : ↥U, (u : Γ) ∈ V₁ → ι.symm (p₂ u) ∈ ℓ)
    (hsℓ : ∀ s ∈ autOn L W₁, ∀ w ∈ ℓ, s w ∈ ℓ)
    (hirr : ∀ X : Subgroup ↥W₁, X ≤ ℓ → (∀ s ∈ autOn L W₁, ∀ x ∈ X, s x ∈ X) → X = ⊥ ∨ X = ℓ)
    (he : ∀ φ ψ : ↥W₁ → ↥W₁, (∀ u ∈ ℓ, φ u ∈ ℓ) → (∀ u ∈ ℓ, ψ u ∈ ℓ) →
      (∀ u ∈ ℓ, ∀ v ∈ ℓ, φ (u * v) = φ u * φ v) → (∀ u ∈ ℓ, ∀ v ∈ ℓ, ψ (u * v) = ψ u * ψ v) →
      (∀ s ∈ autOn L W₁, ∀ u ∈ ℓ, φ (s u) = s (φ u)) →
      (∀ s ∈ autOn L W₁, ∀ u ∈ ℓ, ψ (s u) = s (ψ u)) → ∀ y ∈ ℓ, φ (ψ y) = ψ (φ y))
    {g : Γ} (hgJ : g ∈ J) (htℓ : ∀ w ∈ ℓ, conjAct W₁ ⟨g, hJ₁ hgJ⟩ w ∈ ℓ)
    (htL : ∀ s ∈ autOn L W₁, ∀ w ∈ ℓ,
      (conjAct W₁ ⟨g, hJ₁ hgJ⟩ * s * (conjAct W₁ ⟨g, hJ₁ hgJ⟩)⁻¹ * s⁻¹) w = w) :
    ∀ v ∈ V₁, g * v * g⁻¹ ∈ V₁ := by
  set t := conjAct W₁ ⟨g, hJ₁ hgJ⟩ with ht
  have hgU : ∀ {x : Γ} (hx : x ∈ J) (u : ↥U), x * (u : Γ) * x⁻¹ ∈ U := fun hx u =>
    (Subgroup.mem_normalizer_iff.mp (hJU hx) u).mp u.2
  have hp₁' : ∀ {x : Γ} (hx : x ∈ J) (u : ↥U),
      conjAct W₁ ⟨x, hJ₁ hx⟩ (p₁ u) = p₁ ⟨x * u * x⁻¹, hgU hx u⟩ := fun hx u =>
    Subtype.ext (by rw [Setup.coe_conjAct_apply, hp₁ _ hx u])
  have hp₂' : ∀ {x : Γ} (hx : x ∈ J) (u : ↥U),
      conjAct W₁ ⟨x, hJ₁ hx⟩ (ι.symm (p₂ u)) = ι.symm (p₂ ⟨x * u * x⁻¹, hgU hx u⟩) := by
    intro x hx u
    apply ι.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    have e : conjAct W₁ ⟨x, hJ₁ hx⟩ (ι.symm (p₂ u)) = ⟨x * (ι.symm (p₂ u) : Γ) * x⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hJ₁ hx) _).mp (ι.symm (p₂ u)).2⟩ :=
      Subtype.ext (Setup.coe_conjAct_apply _ _)
    rw [e, hι x hx, MulEquiv.apply_symm_apply, hp₂ _ hx u]
  have hconj : ∀ u : ↥U, g * (u : Γ) * g⁻¹ =
      ((t (p₁ u) : ↥W₁) : Γ) * (ι (t (ι.symm (p₂ u))) : ↥W₂) := fun u => by
    rw [hp₁' hgJ u, hp₂' hgJ u, MulEquiv.apply_symm_apply, hdec]
  set K : Subgroup ↥W₁ := (V₁.subgroupOf W₂).comap ι.toMonoidHom with hK
  have hp₂W : ∀ u : ↥U, (u : Γ) ∈ W₂ → ((p₂ u : ↥W₂) : Γ) = u := fun u hu =>
    (eq_of_mul_eq h12 (p₁ u).2 W₁.one_mem (p₂ u).2 hu ((hdec u).trans (one_mul _).symm)).2
  have hKℓ : K ≤ ℓ := by
    intro w hw
    have h3 : p₂ ⟨(ι w : Γ), hW₂U (ι w).2⟩ = ι w := Subtype.ext (hp₂W _ (ι w).2)
    have := hB ⟨(ι w : Γ), hW₂U (ι w).2⟩ hw
    rwa [h3, MulEquiv.symm_apply_apply] at this
  have hKinv : ∀ s ∈ autOn L W₁, ∀ x ∈ K, s x ∈ K := by
    intro s hs x hx
    obtain ⟨l', hl'L, rfl⟩ := Setup.mem_autOn_iff.mp hs
    show ((ι (conjAct W₁ l' x) : ↥W₂) : Γ) ∈ V₁
    have e : conjAct W₁ l' x = ⟨(l' : Γ) * x * (l' : Γ)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hJ₁ (hLJ hl'L)) x).mp x.2⟩ :=
      Subtype.ext (Setup.coe_conjAct_apply _ x)
    rw [e, hι _ (hLJ hl'L) x]
    exact (Subgroup.mem_normalizer_iff.mp (hLV₁ hl'L) _).mp hx
  rcases hirr K hKℓ hKinv with hK0 | hKℓ'
  · exact graph_case_bot hJ₁ hgU hp₁' hp₂' hconj hK0 hA hA' hB hsℓ he htℓ htL hLJ hLV₁ hV₁U hdec
  ·
    have hℓV : ∀ a ∈ ℓ, ((a : ↥W₁) : Γ) ∈ V₁ := by
      intro a ha
      obtain ⟨u, hu, rfl⟩ := hA' a ha
      have hc : ι.symm (p₂ u) ∈ K := hKℓ' ▸ hB u hu
      have hc' : ((p₂ u : ↥W₂) : Γ) ∈ V₁ := by
        have : ((ι (ι.symm (p₂ u)) : ↥W₂) : Γ) ∈ V₁ := hc
        rwa [MulEquiv.apply_symm_apply] at this
      have := V₁.mul_mem hu (V₁.inv_mem hc')
      rwa [← hdec u, mul_inv_cancel_right] at this
    intro v hv
    rw [show v = ((⟨v, hV₁U hv⟩ : ↥U) : Γ) from rfl, hconj]
    refine V₁.mul_mem (hℓV _ (htℓ _ (hA _ hv))) ?_
    have : t (ι.symm (p₂ ⟨v, hV₁U hv⟩)) ∈ K := hKℓ' ▸ htℓ _ (hB _ hv)
    exact this

end Graph

section Two

variable [Finite Γ]

theorem torus_two_copies {R J L V₁ V W₁ W₂ : Subgroup Γ} {n m : ℕ} (hV : IsElemAbelian 2 V)
    [IsMulCommutative ↥V] (hC : K2Ctx R J L V₁ V n) (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V)
    (h12 : W₁ ⊓ W₂ = ⊥) (hJ₁ : J ≤ Subgroup.normalizer (W₁ : Set Γ))
    (hJ₂ : J ≤ Subgroup.normalizer (W₂ : Set Γ)) (hV₁U : V₁ ≤ W₁ ⊔ W₂)
    [IsMulCommutative ↥W₁] [IsMulCommutative ↥W₂] (hD₁ : TorusData (autOn J W₁) ⊥ (2 ^ m))
    (hD₂ : TorusData (autOn J W₂) ⊥ (2 ^ m)) (ι : ↥W₁ ≃* ↥W₂)
    (hι : ∀ (g : Γ) (hg : g ∈ J) (w : ↥W₁),
      ((ι ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJ₁ hg) w).mp w.2⟩ : ↥W₂) : Γ) =
        g * ι w * g⁻¹) :
    ∃ y ∈ J ⊓ Subgroup.normalizer (V₁ : Set Γ), y ∉ Subgroup.centralizer (V₁ : Set Γ) ∧
      (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ)) ∧
      y ^ (2 ^ n - 1) ∈ Subgroup.centralizer (V₁ : Set Γ) := by
  by_cases hV₁₁ : V₁ ≤ W₁
  · exact torus_of_natural hV hC h₁ hJ₁ hV₁₁ hD₁
  by_cases hV₁₂ : V₁ ≤ W₂
  · exact torus_of_natural hV hC h₂ hJ₂ hV₁₂ hD₂
  have hUV : W₁ ⊔ W₂ ≤ V := sup_le h₁ h₂
  have : IsMulCommutative ↥(W₁ ⊔ W₂) := Ch11.SecC.B51.isMulCommutative_of_le hUV
  have hJU : J ≤ Subgroup.normalizer ((W₁ ⊔ W₂ : Subgroup Γ) : Set Γ) := fun g hg =>
    sup_mem_normalizer (hJ₁ hg) (hJ₂ hg)
  have h21 : W₂ ⊓ W₁ = ⊥ := by rw [inf_comm]; exact h12
  have hU₂ : W₁ ⊔ W₂ ≤ W₂ ⊔ W₁ := (sup_comm W₁ W₂).le
  set p₁ := proj h₁ h₂ le_rfl h12 with hp₁def
  set p₂ := proj h₂ h₁ hU₂ h21 with hp₂def
  have hdec : ∀ u : ↥(W₁ ⊔ W₂), ((p₁ u : ↥W₁) : Γ) * (p₂ u : ↥W₂) = u := by
    intro u
    obtain ⟨b, hb, hu⟩ := projFun_spec h₁ h₂ le_rfl u
    have hcomm : b * ((projFun h₁ h₂ le_rfl u : ↥W₁) : Γ) =
        (projFun h₁ h₂ le_rfl u : ↥W₁) * b :=
      mul_comm_of_mem (V := V) inferInstance (h₂ hb) (h₁ (projFun h₁ h₂ le_rfl u).2)
    have hp : ((p₂ u : ↥W₂) : Γ) = b := proj_eq (h₁ := h₂) (h₂ := h₁) (hU := hU₂) h21 hb
      (projFun h₁ h₂ le_rfl u).2 (hcomm.trans hu)
    rw [hp]
    exact hu
  have hp₁ : IsEquivJ hJU p₁ := fun g hg u => proj_conj h12 (hJU hg) (hJ₁ hg) (hJ₂ hg) u
  have hp₂ : IsEquivJ hJU p₂ := fun g hg u => proj_conj h21 (hJU hg) (hJ₂ hg) (hJ₁ hg) u
  have hι' : ∀ (g : Γ) (hg : g ∈ J) (w : ↥W₂),
      ((ι.symm ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJ₂ hg) w).mp w.2⟩ : ↥W₁) : Γ) =
        g * ι.symm w * g⁻¹ := by
    intro g hg w
    have h := hι g hg (ι.symm w)
    rw [MulEquiv.apply_symm_apply] at h
    have h' : ι ⟨g * (ι.symm w : Γ) * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hJ₁ hg) _).mp (ι.symm w).2⟩ =
        ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJ₂ hg) w).mp w.2⟩ := Subtype.ext h
    rw [← h', MulEquiv.symm_apply_apply]
  have hp₂' : IsEquivJ hJU (ι.symm.toMonoidHom.comp p₂) := by
    intro g hg u
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have e : p₂ ⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJU hg) u).mp u.2⟩ =
        ⟨g * p₂ u * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJ₂ hg) _).mp (p₂ u).2⟩ :=
      Subtype.ext (hp₂ g hg u)
    rw [e, hι' g hg]
  set p₂' := ι.symm.toMonoidHom.comp p₂ with hp₂'def
  have hVU : ValidX J L R (W₁ ⊔ W₂) (2 ^ n) V₁ := hC.hV₁ _ hV₁U
  have hA₁ := validX_map hp₁ hC.hLJ hVU
  have hB₁ := validX_map hp₂' hC.hLJ hVU
  set A₁ := ((V₁.subgroupOf (W₁ ⊔ W₂)).map p₁).map W₁.subtype with hA₁def
  set B₁ := ((V₁.subgroupOf (W₁ ⊔ W₂)).map p₂').map W₁.subtype with hB₁def
  have hA₁ne : A₁ ≠ ⊥ := by
    intro h
    apply hV₁₂
    intro v hv
    have h1 : ((p₁ ⟨v, hV₁U hv⟩ : ↥W₁) : Γ) ∈ A₁ := ⟨_, ⟨⟨v, hV₁U hv⟩, hv, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 := hdec ⟨v, hV₁U hv⟩
    rw [h1, one_mul] at h2
    rw [show v = ((⟨v, hV₁U hv⟩ : ↥(W₁ ⊔ W₂)) : Γ) from rfl, ← h2]
    exact (p₂ _).2
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    apply hV₁₁
    intro v hv
    have h1 : ((p₂' ⟨v, hV₁U hv⟩ : ↥W₁) : Γ) ∈ B₁ := ⟨_, ⟨⟨v, hV₁U hv⟩, hv, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h3 : p₂ ⟨v, hV₁U hv⟩ = 1 := by
      have h4 : ι.symm (p₂ ⟨v, hV₁U hv⟩) = 1 := Subtype.ext h1
      rwa [MulEquiv.map_eq_one_iff] at h4
    have h2 := hdec ⟨v, hV₁U hv⟩
    rw [h3, Subgroup.coe_one, mul_one] at h2
    rw [show v = ((⟨v, hV₁U hv⟩ : ↥(W₁ ⊔ W₂)) : Γ) from rfl, ← h2]
    exact (p₁ _).2
  obtain ⟨P, hP, hLP⟩ := hC.hP
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hC.hlevi
  have hW2₁ : ∀ w : ↥W₁, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w (h₁ w.2))
  obtain ⟨U₂, hLF, hLT, hL, heq⟩ := core_line hW2₁ hJ₁
    (hC.hOJ.trans (Subgroup.centralizer_le h₁)) (not_le_centralizer_of_validX hC.hLJ hA₁ hA₁ne)
    hC.hLJ hC.hRL hC.hq hC.hZY hP hLP hC.hLne hC.hT hC.hn hF e hD₁ hA₁ hA₁ne
  have hA₁ℓ := heq A₁ hA₁ hA₁ne
  have hB₁ℓ := heq B₁ hB₁ hB₁ne
  obtain ⟨t, htJ, ht1, ⟨w₀, hw₀, htw₀⟩, ht3, ht4⟩ := torus_of_line hD₁.hZ hLF hLT
  rw [hL] at ht1 hw₀ ht3
  obtain ⟨-, hirr, -⟩ := hLT
  obtain ⟨-, -, -, hd, he⟩ := hLF
  rw [hL] at hirr hd he
  have hU₂ : U₂ = commS (autOn L W₁) U₂ := hd.trans (sup_bot_eq _)
  set ℓ := commS (autOn L W₁) U₂ with hℓ
  have hirr' : ∀ X : Subgroup ↥W₁, X ≤ ℓ → (∀ s ∈ autOn L W₁, ∀ x ∈ X, s x ∈ X) →
      X = ⊥ ∨ X = ℓ := fun X hX hinv => by
    rw [← hU₂]
    exact hirr X bot_le (hX.trans hU₂.ge) hinv
  have he' : ∀ φ ψ : ↥W₁ → ↥W₁, (∀ u ∈ ℓ, φ u ∈ ℓ) → (∀ u ∈ ℓ, ψ u ∈ ℓ) →
      (∀ u ∈ ℓ, ∀ v ∈ ℓ, φ (u * v) = φ u * φ v) → (∀ u ∈ ℓ, ∀ v ∈ ℓ, ψ (u * v) = ψ u * ψ v) →
      (∀ s ∈ autOn L W₁, ∀ u ∈ ℓ, φ (s u) = s (φ u)) →
      (∀ s ∈ autOn L W₁, ∀ u ∈ ℓ, ψ (s u) = s (ψ u)) → ∀ y ∈ ℓ, φ (ψ y) = ψ (φ y) := by
    intro φ ψ h1 h2 h3 h4 h5 h6
    exact he φ ψ (by rwa [hU₂]) (by rwa [hU₂]) (by rwa [hU₂]) (by rwa [hU₂]) (by rwa [hU₂])
      (by rwa [hU₂])
  have hsℓ : ∀ s ∈ autOn L W₁, ∀ w ∈ ℓ, s w ∈ ℓ := by
    intro s hs w hw
    rw [← hL] at hs
    have h1 : w ∈ U₂ := by rw [hU₂]; exact hw
    have := (mem_stabW.mp (perfectCore_le _ hs).2 w).mp h1
    rw [← hU₂]
    exact this
  have hA : ∀ u : ↥(W₁ ⊔ W₂), (u : Γ) ∈ V₁ → p₁ u ∈ ℓ := fun u hu => by
    rw [← hA₁ℓ]
    exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have hA' : ∀ a ∈ ℓ, ∃ u : ↥(W₁ ⊔ W₂), (u : Γ) ∈ V₁ ∧ p₁ u = a := fun a ha => by
    rw [← hA₁ℓ, Subgroup.mem_subgroupOf] at ha
    obtain ⟨_, ⟨u, hu, rfl⟩, hua⟩ := ha
    exact ⟨u, hu, Subtype.ext hua⟩
  have hB : ∀ u : ↥(W₁ ⊔ W₂), (u : Γ) ∈ V₁ → ι.symm (p₂ u) ∈ ℓ := fun u hu => by
    rw [← hB₁ℓ]
    exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  obtain ⟨⟨y, hyN⟩, hyJ, rfl⟩ := Setup.mem_autOn_iff.mp htJ
  have hconjV := conj_mem_of_graph (hJU := hJU) h12 hJ₁ hC.hLJ hVU.nL hV₁U le_sup_right hdec hp₁
    hp₂ ι hι hA hA' hB hsℓ hirr' he' (g := y) hyJ ht1 ht3
  refine ⟨y, ⟨hyJ, mem_normalizer_of_conj_mem hconjV⟩, fun hc => ?_, fun l hl => ?_, ?_⟩
  ·
    obtain ⟨u₀, hu₀, rfl⟩ := hA' w₀ hw₀
    apply htw₀
    have h1 : y * (u₀ : Γ) * y⁻¹ = u₀ := by
      rw [(Subgroup.mem_centralizer_iff.mp hc (u₀ : Γ) hu₀).symm, mul_inv_cancel_right]
    have h2 : (⟨y * (u₀ : Γ) * y⁻¹, (Subgroup.mem_normalizer_iff.mp (hJU hyJ) u₀).mp u₀.2⟩ :
        ↥(W₁ ⊔ W₂)) = u₀ := Subtype.ext h1
    apply Subtype.ext
    rw [Setup.coe_conjAct_apply]
    have h3 := hp₁ y hyJ u₀
    rw [h2] at h3
    exact h3.symm
  ·
    have hlJ := hC.hLJ hl
    have hcJ : y * l * y⁻¹ * l⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem (J.mul_mem hyJ hlJ) (J.inv_mem hyJ)) (J.inv_mem hlJ)
    have e : (⟨y * l * y⁻¹ * l⁻¹, hJ₁ hcJ⟩ : ↥(Subgroup.normalizer (W₁ : Set Γ))) =
        ⟨y, hJ₁ hyJ⟩ * ⟨l, hJ₁ hlJ⟩ * (⟨y, hJ₁ hyJ⟩)⁻¹ * (⟨l, hJ₁ hlJ⟩)⁻¹ := rfl
    have hsL : conjAct W₁ ⟨l, hJ₁ hlJ⟩ ∈ autOn L W₁ :=
      InternalSec.conjAct_mem_autOn (hC.hLJ.trans hJ₁) hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := conj_decomp hJ₁ hdec ι hι hcJ ⟨v, hV₁U hv⟩
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ht3 _ hsL _ (hA _ hv),
      ht3 _ hsL _ (hB _ hv), MulEquiv.apply_symm_apply, hdec] at h1
    calc v * (y * l * y⁻¹ * l⁻¹)
        = (y * l * y⁻¹ * l⁻¹) * v * (y * l * y⁻¹ * l⁻¹)⁻¹ * (y * l * y⁻¹ * l⁻¹) := by
          rw [h1]
      _ = (y * l * y⁻¹ * l⁻¹) * v := by group
  ·
    have hkJ : y ^ (2 ^ n - 1) ∈ J := J.pow_mem hyJ _
    have e : (⟨y ^ (2 ^ n - 1), hJ₁ hkJ⟩ : ↥(Subgroup.normalizer (W₁ : Set Γ))) =
        (⟨y, hJ₁ hyJ⟩ : ↥(Subgroup.normalizer (W₁ : Set Γ))) ^ (2 ^ n - 1) :=
      Subtype.ext (SubmonoidClass.coe_pow
        (⟨y, hJ₁ hyJ⟩ : ↥(Subgroup.normalizer (W₁ : Set Γ))) (2 ^ n - 1)).symm
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := conj_decomp hJ₁ hdec ι hι hkJ ⟨v, hV₁U hv⟩
    rw [e, map_pow, ht4, MulAut.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply,
      hdec] at h1
    calc v * y ^ (2 ^ n - 1) = y ^ (2 ^ n - 1) * v * (y ^ (2 ^ n - 1))⁻¹ * y ^ (2 ^ n - 1) := by
          rw [h1]
      _ = y ^ (2 ^ n - 1) * v := by group

end Two

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

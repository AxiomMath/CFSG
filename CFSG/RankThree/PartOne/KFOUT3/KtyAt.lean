module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartOne.KFOUT3

section At

variable {Q : Type} [Group Q]

@[expose] def BigAt (p : ℕ) (u : Q) (R : ℕ → Prop) : Prop :=
  ∃ S' : Subgroup Q, Group.IsPerfect S' ∧ IsSimpleGroup S' ∧ (∃ σ ∈ S', orderOf σ = p) ∧
    (∀ σ ∈ S', u * σ = σ * u) ∧
    (∀ x : Q, u * x = x * u → ∀ σ ∈ S', x * σ * x⁻¹ ∈ S') ∧ R (Nat.card S')

@[expose] def SmallAt (u : Q) (R : ℕ → Prop) : Prop :=
  ∀ T : Subgroup Q, Group.IsPerfect T → (∀ τ ∈ T, u * τ = τ * u) → ∀ n, R n → ¬ n ∣ Nat.card T

theorem BigAt.conj {p : ℕ} {u : Q} {R : ℕ → Prop} (h : BigAt p u R) (m : Q) :
    BigAt p (m * u * m⁻¹) R := by
  obtain ⟨S', hperf, hsimple, ⟨σ, hσ, hσp⟩, hc, hn, hM⟩ := h
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  let e : ↥S' ≃* ↥(S'.map (MulAut.conj m).toMonoidHom) := S'.equivMapOfInjective _ hinj
  refine ⟨S'.map (MulAut.conj m).toMonoidHom, ?_, ?_, ⟨m * σ * m⁻¹, ⟨σ, hσ, rfl⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  · exact e.symm.isSimpleGroup
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hσp
  · rintro _ ⟨σ', hσ', rfl⟩
    have := hc σ' hσ'
    show m * u * m⁻¹ * (m * σ' * m⁻¹) = m * σ' * m⁻¹ * (m * u * m⁻¹)
    calc m * u * m⁻¹ * (m * σ' * m⁻¹) = m * (u * σ') * m⁻¹ := by group
      _ = m * (σ' * u) * m⁻¹ := by rw [this]
      _ = m * σ' * m⁻¹ * (m * u * m⁻¹) := by group
  · intro x hx
    rintro _ ⟨σ', hσ', rfl⟩
    have hx' : u * (m⁻¹ * x * m) = (m⁻¹ * x * m) * u := by
      have h1 : m * u * m⁻¹ * x = x * (m * u * m⁻¹) := hx
      calc u * (m⁻¹ * x * m) = m⁻¹ * (m * u * m⁻¹ * x) * m := by group
        _ = m⁻¹ * (x * (m * u * m⁻¹)) * m := by rw [h1]
        _ = (m⁻¹ * x * m) * u := by group
    refine ⟨(m⁻¹ * x * m) * σ' * (m⁻¹ * x * m)⁻¹, hn _ hx' σ' hσ', ?_⟩
    show m * ((m⁻¹ * x * m) * σ' * (m⁻¹ * x * m)⁻¹) * m⁻¹ = x * (m * σ' * m⁻¹) * x⁻¹
    group
  · rw [Subgroup.card_map_of_injective hinj]
    exact hM

theorem SmallAt.conj {u : Q} {R : ℕ → Prop} (h : SmallAt u R) (m : Q) :
    SmallAt (m * u * m⁻¹) R := by
  intro T hT hTc n hn
  have hinj : Function.Injective (MulAut.conj m⁻¹).toMonoidHom := (MulAut.conj m⁻¹).injective
  have := hT
  have hperf : Group.IsPerfect ↥(T.map (MulAut.conj m⁻¹).toMonoidHom) := Group.IsPerfect.map _
  have hcard : Nat.card ↥(T.map (MulAut.conj m⁻¹).toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective hinj
  rw [← hcard]
  refine h _ hperf ?_ n hn
  rintro _ ⟨τ, hτ, rfl⟩
  have h1 := hTc τ hτ
  show u * (m⁻¹ * τ * m⁻¹⁻¹) = (m⁻¹ * τ * m⁻¹⁻¹) * u
  calc u * (m⁻¹ * τ * m⁻¹⁻¹) = m⁻¹ * (m * u * m⁻¹ * τ) * m := by group
    _ = m⁻¹ * (τ * (m * u * m⁻¹)) * m := by rw [h1]
    _ = (m⁻¹ * τ * m⁻¹⁻¹) * u := by group

theorem smallAt_of_card_le [Finite Q] {u : Q} {N M : ℕ}
    (hN : Nat.card (Subgroup.centralizer ({u} : Set Q)) ≤ N) (hNM : N < M) :
    SmallAt u (fun n => M ≤ n) := by
  intro T _ hTc n hn hdvd
  have hle : T ≤ Subgroup.centralizer ({u} : Set Q) := fun τ hτ =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hTc τ hτ
  have h1 : Nat.card T ≤ N := (Subgroup.card_le_of_le hle).trans hN
  have h2 : n ≤ Nat.card T := Nat.le_of_dvd Nat.card_pos hdvd
  have h3 : M ≤ n := hn
  omega

end At

end CFSG.RankThree.PartOne.KFOUT3

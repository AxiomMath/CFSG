module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

@[expose] def ggDFix (k : ℕ) (v : Fin k → ℤ) : Subgroup (ggWeylD k) where
  carrier := {w | ∀ u, ggDDot v (toStdD k (weylAction (isFiniteType_cartanD k) w u)) =
    ggDDot v (toStdD k u)}
  mul_mem' {a b} ha hb := by
    intro u
    rw [weylAction_mul_apply, ha, hb]
  one_mem' := by
    intro u
    rw [map_one, Module.End.one_apply]
  inv_mem' {a} ha := by
    intro u
    have h := ha (weylAction (isFiniteType_cartanD k) a⁻¹ u)
    rwa [weylAction_apply_inv_apply, eq_comm] at h

theorem mem_ggDFix_iff {k : ℕ} {v : Fin k → ℤ} {w : ggWeylD k} :
    w ∈ ggDFix k v ↔ ∀ u, ggDDot v (toStdD k (weylAction (isFiniteType_cartanD k) w u)) =
      ggDDot v (toStdD k u) :=
  Iff.rfl

theorem GGDReflRoot.mem_ggDFix {k : ℕ} (hk : 2 ≤ k) {t : ggWeylD k} {γ v : Fin k → ℤ}
    (h : GGDReflRoot k t γ) (h0 : ggDDot v γ = 0) : t ∈ ggDFix k v :=
  mem_ggDFix_iff.2 fun u => by rw [h.action hk, ggDDot_ggDReflect, h0, mul_zero, sub_zero]

theorem GGDReflRoot.dot_eq_zero_of_mem_ggDFix {k : ℕ} (hk : 2 ≤ k) {t : ggWeylD k}
    {γ v : Fin k → ℤ} (h : GGDReflRoot k t γ) (ht : t ∈ ggDFix k v) : ggDDot v γ = 0 := by
  obtain ⟨w, i, -, hγ⟩ := id h
  have h1 := mem_ggDFix_iff.1 ht (weylAction (isFiniteType_cartanD k) w (Pi.single i 1))
  rw [h.action hk, hγ, ggDDot_ggDReflect, ggDDot_self_of_mem (h.mem (by omega))] at h1
  linarith

theorem ggDReflect_comm_of_dot_eq_zero {k : ℕ} {γ γ' : Fin k → ℤ} (h0 : ggDDot γ γ' = 0)
    (x : Fin k → ℤ) : ggDReflect γ (ggDReflect γ' x) = ggDReflect γ' (ggDReflect γ x) := by
  have e1 : ggDDot (ggDReflect γ' x) γ = ggDDot x γ := by
    rw [ggDDot_comm, ggDDot_ggDReflect, h0, mul_zero, sub_zero, ggDDot_comm]
  have e2 : ggDDot (ggDReflect γ x) γ' = ggDDot x γ' := by
    rw [ggDDot_comm, ggDDot_ggDReflect, ggDDot_comm γ' γ, h0, mul_zero, sub_zero, ggDDot_comm]
  funext c
  simp only [ggDReflect_apply, e1, e2]
  ring

theorem GGDReflRoot.commute_of_dot_eq_zero {k : ℕ} (hk : 2 ≤ k) {t t' : ggWeylD k}
    {γ γ' : Fin k → ℤ} (h : GGDReflRoot k t γ) (h' : GGDReflRoot k t' γ')
    (h0 : ggDDot γ γ' = 0) : t * t' = t' * t := by
  apply weylAction_injective (isFiniteType_cartanD k)
  refine LinearMap.ext fun x => toStdD_injective k ?_
  simp only [weylAction_mul_apply, h.action hk, h'.action hk]
  exact ggDReflect_comm_of_dot_eq_zero h0 _

theorem eq_zero_of_top_le_ggDFix {k : ℕ} (hk : 2 ≤ k) {v : Fin k → ℤ} (h : ⊤ ≤ ggDFix k v) :
    v = 0 := by
  funext c
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  obtain ⟨d, hd⟩ := exists_ne c
  have key : ∀ s : ℤ, (s = 1 ∨ s = -1) → v c + s * v d = 0 := fun s hs => by
    obtain ⟨t, ht⟩ : ∃ t, GGDReflRoot k t (Pi.single c 1 + Pi.single d s) :=
      exists_ggDReflRoot ⟨c, d, 1, s, hd.symm, Or.inl rfl, hs, rfl⟩
    have h1 := ht.dot_eq_zero_of_mem_ggDFix hk (h (Subgroup.mem_top t))
    rwa [ggDDot_comm, ggDDot_single_add_single, one_mul] at h1
  have h1 := key 1 (Or.inl rfl)
  have h2 := key (-1) (Or.inr rfl)
  rw [Pi.zero_apply]
  linarith

theorem exists_ggDReflRoot_of_conj {ι : Type} {M : CoxeterMatrix ι} {k : ℕ} {σ : Fin k ≃ ι}
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (w : M.Group) (i : ι) : ∃ γ, GGDReflRoot k (φ (w * M.simple i * w⁻¹)) γ :=
  ⟨_, φ w, σ.symm i, by rw [map_mul, map_mul, map_inv, ← hφ, Equiv.apply_symm_apply], rfl⟩

theorem ggDIrred_of_connected {k : ℕ} {Φ : Set (Fin k → ℤ)} {ν : Type*} {adj : ν → ν → Prop}
    (η : ν → Fin k → ℤ) (hη : ∀ a, η a ∈ Φ) (hconn : ∀ a b, Relation.ReflTransGen adj a b)
    (hadj : ∀ a b, adj a b → ggDDot (η a) (η b) ≠ 0)
    (hcov : ∀ γ ∈ Φ, ∃ a, ggDDot (η a) γ ≠ 0) : GGDIrred Φ := by
  have hchain : ∀ a b, Relation.ReflTransGen (fun u v => u ∈ Φ ∧ v ∈ Φ ∧ ggDDot u v ≠ 0)
      (η a) (η b) := fun a b => by
    have h := hconn a b
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail ⟨hη _, hη _, hadj _ _ hbc⟩
  intro γ hγ δ hδ
  obtain ⟨a, ha⟩ := hcov γ hγ
  obtain ⟨b, hb⟩ := hcov δ hδ
  refine Relation.ReflTransGen.head ⟨hγ, hη a, ?_⟩ ((hchain a b).tail ⟨hη b, hδ, hb⟩)
  rwa [ggDDot_comm]

end CFSG.StandardType

end

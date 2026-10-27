module

public import CFSG.Quasithin.SteinbergCFOneFactorFixedKernel
public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.Quasithin

open SteinbergCF

namespace SteinbergBQ.OneFactor

variable {k S E : Type*} [Field k] [Group S] [AddCommGroup E] [Module k E]
  {ρ : Representation k S E}

theorem eq_zero_of_fixed {U U' : Subrepresentation ρ} (hirr : (factorRep U U').IsIrreducible)
    (hnt : ∃ s w, factorRep U U' s w ≠ w) {w : U'.toSubmodule ⧸ factorSub U U'}
    (hw : ∀ s, factorRep U U' s w = w) : w = 0 := by
  let F : Subrepresentation (factorRep U U') :=
    { toSubmodule := Representation.invariants (factorRep U U')
      apply_mem_toSubmodule := fun g v hv => by
        rw [Representation.mem_invariants] at hv ⊢
        intro s
        rw [hv g, hv s] }
  have := hirr
  rcases IsSimpleOrder.eq_bot_or_eq_top F with h | h
  · have h1 : w ∈ F.toSubmodule := (Representation.mem_invariants _ w).2 hw
    rw [h] at h1
    exact (Submodule.mem_bot k).1 h1
  · exfalso
    obtain ⟨s, w', hw'⟩ := hnt
    have h1 : w' ∈ F.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    exact hw' ((Representation.mem_invariants _ w').1 h1 s)

theorem fixed_of_trivial_factors (hS : Group.IsPerfect S) {r : ℕ}
    (Us : Fin (r + 1) → Subrepresentation ρ) (h0 : Us 0 = ⊥)
    (htriv : ∀ i : Fin r, ∀ s : S, ∀ x ∈ (Us i.succ).toSubmodule,
      ρ s x - x ∈ (Us i.castSucc).toSubmodule) :
    ∀ i : Fin (r + 1), ∀ s : S, ∀ x ∈ (Us i).toSubmodule, ρ s x = x := by
  have hL : Group.IsPerfect (⊤ : Subgroup S) := Group.IsPerfect.top_iff.2 hS
  have key : ∀ i : Fin (r + 1), ∀ s : S, ∀ x ∈ (Us i).toSubmodule,
      ρ s x - x ∈ (⊥ : Submodule k E) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro s x hx
      rw [h0] at hx
      change x ∈ (⊥ : Submodule k E) at hx
      rw [(Submodule.mem_bot k).1 hx, map_zero, sub_zero]
      exact Submodule.zero_mem _
    | succ i ih =>
      intro s x hx
      exact sub_mem_of_isPerfect ρ hL (U := (Us i.castSucc).toSubmodule)
        (fun l _ u hu => ih l u hu) (fun l _ => htriv i l x hx) s (Subgroup.mem_top s)
  intro i s x hx
  have h1 := key i s x hx
  rwa [Submodule.mem_bot, sub_eq_zero] at h1

end SteinbergBQ.OneFactor

open SteinbergBQ.OneFactor

variable {k S E : Type*} [Field k] [Group S] [AddCommGroup E] [Module k E]

theorem perfect_one_factor_module_central_quotient [Finite S] [FiniteDimensional k E]
    [Nontrivial E] (ρ : Representation k S E) (hS : Group.IsPerfect S)
    (hE : Submodule.span k {w | ∃ (s : S) (v : E), w = ρ s v - v} = ⊤)
    {r : ℕ} (Us : Fin (r + 1) → Subrepresentation ρ) (h0 : Us 0 = ⊥)
    (hr : Us (Fin.last r) = ⊤)
    (hcomp : ∀ i : Fin r, Us i.castSucc ≤ Us i.succ ∧
      (factorRep (Us i.castSucc) (Us i.succ)).IsIrreducible)
    (hone : ∀ i j : Fin r, (∃ s w, factorRep (Us i.castSucc) (Us i.succ) s w ≠ w) →
      (∃ s w, factorRep (Us j.castSucc) (Us j.succ) s w ≠ w) → i = j) :
    ∃ j : Fin r, (∀ i : Fin r, (∃ s w, factorRep (Us i.castSucc) (Us i.succ) s w ≠ w) ↔ i = j) ∧
      ∃ π : E →ₗ[k] (Us j.succ).toSubmodule ⧸ factorSub (Us j.castSucc) (Us j.succ),
        (∀ s v, π (ρ s v) = factorRep (Us j.castSucc) (Us j.succ) s (π v)) ∧
        Function.Surjective π ∧ LinearMap.ker π = Representation.invariants ρ ∧
        (∀ s : S, ∀ v ∈ LinearMap.ker π, ρ s v = v) ∧
        (factorRep (Us j.castSucc) (Us j.succ)).IsIrreducible ∧
        ∃ s w, factorRep (Us j.castSucc) (Us j.succ) s w ≠ w := by
  obtain ⟨j, hj⟩ : ∃ j : Fin r, ∃ s w, factorRep (Us j.castSucc) (Us j.succ) s w ≠ w := by
    by_contra hcon
    push Not at hcon
    have htriv : ∀ i : Fin r, ∀ s : S, ∀ x ∈ (Us i.succ).toSubmodule,
        ρ s x - x ∈ (Us i.castSucc).toSubmodule :=
      fun i s => (factorRep_eq_self_iff _ _ s).1 (hcon i s)
    have hfix := fixed_of_trivial_factors hS Us h0 htriv (Fin.last r)
    have hbot : Submodule.span k {w | ∃ (s : S) (v : E), w = ρ s v - v} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨s, v, rfl⟩
      rw [hfix s v (by rw [hr]; exact Submodule.mem_top), sub_self]
    rw [hE] at hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact hx (by simpa using (Submodule.eq_bot_iff _).1 hbot x Submodule.mem_top)
  have hW : ∀ i : Fin r, (∃ s w, factorRep (Us i.castSucc) (Us i.succ) s w ≠ w) ↔ i = j :=
    fun i => ⟨fun hi => hone i j hi hj, fun h => h ▸ hj⟩
  have hirr := (hcomp j).2
  have hinv : Representation.invariants (ρ.comp (⊤ : Subgroup S).subtype) =
      Representation.invariants ρ := by
    ext v
    simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, Subtype.forall, Subgroup.mem_top, forall_const]
  obtain ⟨-, -, ⟨π, hπ, hπs, hπk⟩, -⟩ :=
    perfect_normal_one_factor_commutator_module_fixed_kernel ρ (L := ⊤)
      (Group.IsPerfect.top_iff.2 hS)
      (by
        rw [← hE]
        congr 1
        ext w
        simp only [Subgroup.mem_top, true_and, Set.mem_ofPred_eq])
      Us h0 hr j
      (fun i => ⟨fun ⟨l, _, w, hw⟩ => (hW i).1 ⟨l, w, hw⟩,
        fun h => let ⟨s, w, hw⟩ := (hW i).2 h; ⟨s, Subgroup.mem_top s, w, hw⟩⟩)
      (fun w hw => eq_zero_of_fixed hirr hj fun s => hw s (Subgroup.mem_top s))
  rw [hinv] at hπk
  refine ⟨j, hW, π, fun s v => hπ.isIntertwining s v, hπs, hπk, fun s v hv => ?_, hirr, hj⟩
  rw [hπk] at hv
  exact (Representation.mem_invariants ρ v).1 hv s

end CFSG.Quasithin

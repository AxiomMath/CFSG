module

public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Sporadic.Co2Rank3.Orbital
public import Certificates.Data.CFSGNative.Co2Rank3.Orbits

public section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Rank3.Native MulAction

variable {n : ℕ}

structure OrbitFacts (n : ℕ) (gens : Array (Array ℕ)) (lab dep par via : Array ℕ) : Prop where
  inv : ∀ k < gens.size, ∀ x < n, (gens[k]!)[x]! < n ∧ lab[(gens[k]!)[x]!]! = lab[x]!
  lab_lt : ∀ x < n, lab[x]! < n
  tree : ∀ x < n, (dep[x]! = 1 ∧ lab[x]! = x) ∨
    (dep[x]! ≠ 1 ∧ par[x]! < n ∧ dep[par[x]!]! + 1 = dep[x]! ∧ via[x]! < gens.size ∧
      (gens[via[x]!]!)[par[x]!]! = x)

theorem orbitFacts_of_orbitsOK {gens : Array (Array ℕ)} {lab dep par via : Array ℕ}
    (h : orbitsOK n gens lab dep par via = true) : OrbitFacts n gens lab dep par via := by
  simp only [orbitsOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun k hk x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have := allLt_spec (allLt_spec h1 hk) hx
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
  · have := allLt_spec h2 hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := (allLt_spec h2 hx)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have h3 := this.2
    by_cases hd : dep[x]! = 1
    · simp only [hd, beq_self_eq_true, ite_true, beq_iff_eq] at h3
      exact Or.inl ⟨hd, h3⟩
    · have hd' : (dep[x]! == 1) = false := by simpa using hd
      simp only [hd', Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h3
      obtain ⟨⟨⟨h4, h5⟩, h6⟩, h7⟩ := h3
      exact Or.inr ⟨hd, h4, h5, h6, h7⟩

section Facts

variable {gens : Array (Array ℕ)} {lab dep par via : Array ℕ} {Gs : ℕ → Equiv.Perm (Fin n)}
  (hF : OrbitFacts n gens lab dep par via) (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k))
include hF hrep

theorem lab_smul_of_mem {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ Subgroup.closure {g | ∃ k < gens.size, Gs k = g}) (x : Fin n) :
    lab[((σ x : Fin n) : ℕ)]! = lab[(x : ℕ)]! := by
  induction hσ using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    obtain ⟨k, hk, rfl⟩ := hg
    rw [← hrep k hk x]
    exact (hF.inv k hk x x.2).2
  | one => rfl
  | mul g h _ _ hg hh =>
    rw [Equiv.Perm.mul_apply, hg, hh]
  | inv g _ hg =>
    have := hg (g⁻¹ x)
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
    exact this.symm

@[expose] def labPt (hF : OrbitFacts n gens lab dep par via) (x : Fin n) : Fin n :=
  ⟨lab[(x : ℕ)]!, hF.lab_lt x x.2⟩

theorem exists_mem_smul_lab (x : Fin n) :
    ∃ σ ∈ Subgroup.closure {g | ∃ k < gens.size, Gs k = g}, σ (labPt hF x) = x := by
  suffices h : ∀ d, ∀ x : Fin n, dep[(x : ℕ)]! = d →
      ∃ σ ∈ Subgroup.closure {g | ∃ k < gens.size, Gs k = g}, σ (labPt hF x) = x from
    h _ x rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hx
    rcases hF.tree x x.2 with ⟨-, hl⟩ | ⟨hd, hp, hdp, hv, himg⟩
    · exact ⟨1, Subgroup.one_mem _, Fin.ext (by simp [labPt, hl])⟩
    · set p : Fin n := ⟨par[(x : ℕ)]!, hp⟩
      have hlt : dep[(p : ℕ)]! < d := by
        change dep[par[(x : ℕ)]!]! < d
        omega
      obtain ⟨τ, hτ, hτp⟩ := ih (dep[(p : ℕ)]!) hlt p rfl
      have hgen : Gs via[(x : ℕ)]! ∈ Subgroup.closure {g | ∃ k < gens.size, Gs k = g} :=
        Subgroup.subset_closure ⟨_, hv, rfl⟩
      have hstep : Gs via[(x : ℕ)]! p = x := by
        apply Fin.ext
        rw [← hrep _ hv p]
        exact himg
      have hlab : labPt hF p = labPt hF x := by
        apply Fin.ext
        change lab[par[(x : ℕ)]!]! = lab[(x : ℕ)]!
        have := (hF.inv _ hv _ hp).2
        rw [himg] at this
        exact this.symm
      refine ⟨Gs via[(x : ℕ)]! * τ, Subgroup.mul_mem _ hgen hτ, ?_⟩
      rw [Equiv.Perm.mul_apply, ← hlab, hτp, hstep]

theorem mem_orbit_iff_lab {x y : Fin n} :
    y ∈ orbit (Subgroup.closure {g | ∃ k < gens.size, Gs k = g}) x ↔
      lab[(y : ℕ)]! = lab[(x : ℕ)]! := by
  rw [mem_orbit_subgroup_iff]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact lab_smul_of_mem hF hrep hσ x
  · intro h
    obtain ⟨σ, hσ, hσx⟩ := exists_mem_smul_lab hF hrep x
    obtain ⟨τ, hτ, hτy⟩ := exists_mem_smul_lab hF hrep y
    have e : labPt hF y = labPt hF x := Fin.ext h
    refine ⟨τ * σ⁻¹, Subgroup.mul_mem _ hτ (Subgroup.inv_mem _ hσ), ?_⟩
    have hy : (τ * σ⁻¹) x = y := by
      rw [Equiv.Perm.mul_apply, ← hσx, ← Equiv.Perm.mul_apply σ⁻¹ σ, inv_mul_cancel,
        Equiv.Perm.one_apply, ← e, hτy]
    exact hy

theorem ncard_orbit_eq (x : Fin n) :
    (orbit (Subgroup.closure {g | ∃ k < gens.size, Gs k = g}) x).ncard =
      (Finset.univ.filter fun y : Fin n => lab[(y : ℕ)]! = lab[(x : ℕ)]!).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  exact mem_orbit_iff_lab hF hrep

end Facts

theorem labelsOK_spec {lab : Array ℕ} {roots : List (ℕ × ℕ)} (h : labelsOK n lab roots = true) :
    (∀ x < n, ∃ r ∈ roots, r.1 = lab[x]!) ∧ ∀ r ∈ roots, lab[r.1]! = r.1 := by
  simp only [labelsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  refine ⟨fun x hx => ?_, h.2⟩
  have := allLt_spec h.1 hx
  simpa only [List.any_eq_true, beq_iff_eq] using this

theorem listLabelOK_spec {l : List ℕ} {lab : Array ℕ} {good : List ℕ}
    (h : listLabelOK n l lab good = true) {x : ℕ} (hx : x < n) :
    x ∈ l ↔ lab[x]! ∈ good := by
  have := allLt_spec h hx
  simp only [beq_iff_eq] at this
  rw [← List.contains_iff_mem, ← List.contains_iff_mem, this]

end CFSG.Sporadic.Co2Rank3

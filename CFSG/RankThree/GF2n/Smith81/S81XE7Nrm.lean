module

public import CFSG.RankThree.GF2n.Smith81.S81XE7Grp

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
open scoped commutatorElement


variable {K : Type} [Field K]

private theorem nrm_pr_add (a : Fin e7Data.d) (δ γ : Fin (Tag.rank .E7) → ℤ) :
    pr a (δ + γ) = pr a δ + pr a γ := by
  unfold pr
  rw [dotProduct_add]

private theorem nrm_xE_mem_UA {a : Fin e7Data.d} {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Phi a)
    (c : K) : e7Data_valid.xm K γ c ∈ UA K a := by
  unfold UA
  exact Subgroup.subset_closure ⟨γ, hγ, c, rfl⟩

theorem conj_UA_of_gen {a a' : Fin e7Data.d} {g : Gp K}
    (h : ∀ γ ∈ Phi a, ∀ c : K, g * xE γ c * g⁻¹ ∈ UA K a') : ∀ x ∈ UA K a, g * x * g⁻¹ ∈ UA K a' := by
  have key : UA K a ≤ (UA K a').comap (MulAut.conj g).toMonoidHom := by
    unfold UA
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, rfl⟩
    exact h γ hγ c
  intro x hx
  exact key hx

theorem conj_UA_xE {a : Fin e7Data.d} {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ)
    (hpr : pr a δ ≠ -1) (c : K) : ∀ x ∈ UA K a, e7Data_valid.xm K δ c * x * (e7Data_valid.xm K δ c)⁻¹ ∈ UA K a := by
  refine conj_UA_of_gen (a := a) (a' := a) (g := e7Data_valid.xm K δ c) ?_
  intro γ hγ d
  obtain ⟨hγr, hγ1⟩ := mem_Phi.1 hγ
  have hpδ : pr a δ = 0 ∨ pr a δ = 1 := by
    rcases pr_mem hδ a with h | h | h
    · exact absurd h hpr
    · exact Or.inl h
    · exact Or.inr h
  have hsum : pr a (δ + γ) = pr a δ + 1 := by
    rw [nrm_pr_add, hγ1]
  have hne : δ + γ ≠ 0 := by
    intro h
    have h0 : pr a (δ + γ) = 0 := by simp [h, pr]
    rcases hpδ with h1 | h1 <;> omega
  obtain ⟨hroot, hnroot⟩ := e7Data_valid.commutator_xm K hδ hγr hne
  have hconj : e7Data_valid.xm K δ c * e7Data_valid.xm K γ d * (e7Data_valid.xm K δ c)⁻¹ =
      ⁅e7Data_valid.xm K δ c, e7Data_valid.xm K γ d⁆ * e7Data_valid.xm K γ d := by
    rw [commutatorElement_def]
    group
  by_cases hr : IsRoot .E7 (δ + γ)
  · obtain ⟨σ, -, hσ⟩ := hroot hr
    have hmem : pr a (δ + γ) = 1 := by
      rcases pr_mem hr a with h | h | h <;> rcases hpδ with h1 | h1 <;> omega
    have hD : δ + γ ∈ Phi a := mem_Phi.2 ⟨hr, hmem⟩
    rw [hconj, hσ c d]
    exact mul_mem (nrm_xE_mem_UA hD _) (nrm_xE_mem_UA hγ d)
  · rw [hconj, hnroot hr c d, one_mul]
    exact nrm_xE_mem_UA hγ d

theorem conj_UA_tor (a : Fin e7Data.d) {t : Gp K} (ht : t ∈ Tor K) :
    ∀ x ∈ UA K a, t * x * t⁻¹ ∈ UA K a := by
  refine Subgroup.iSup_induction (fun i => e7Data_valid.torus K i)
    (C := fun s => ∀ x ∈ UA K a, s * x * s⁻¹ ∈ UA K a) ht ?_ ?_ ?_
  · intro i y hy
    obtain ⟨s, rfl⟩ := (e7Data_valid.mem_torus K).1 hy
    refine conj_UA_of_gen (a := a) (a' := a) (g := e7Data_valid.hm K i s) ?_
    intro γ hγ c
    rw [e7Data_valid.hm_conj_xm K (mem_Phi.1 hγ).1 i s c]
    exact nrm_xE_mem_UA hγ _
  · intro x hx
    simpa using hx
  · intro x y hx hy z hz
    have e : x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hy z hz)

theorem conj_UA_uni {a : Fin e7Data.d} (hdom : ∀ γ, IsRoot .E7 γ → 0 < ht γ → pr a γ ≠ -1)
    {u : Gp K} (hu : u ∈ Uni K) : ∀ x ∈ UA K a, u * x * u⁻¹ ∈ UA K a := by
  have hu' : u ∈ ⨆ γ ∈ {γ | γ ∈ (e7Datum K).roots ∧ 0 < ht γ}, (e7Datum K).rootGroup γ := hu
  refine Subgroup.iSup_induction _ (C := fun v => ∀ x ∈ UA K a, v * x * v⁻¹ ∈ UA K a) hu' ?_ ?_ ?_
  · intro γ y hy
    by_cases hγ : γ ∈ {γ | γ ∈ (e7Datum K).roots ∧ 0 < ht γ}
    · rw [iSup_pos hγ] at hy
      obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hy
      obtain ⟨hγr, hγp⟩ : γ ∈ (e7Datum K).roots ∧ 0 < ht γ := hγ
      have hr : IsRoot .E7 γ := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 hγr
      exact conj_UA_xE hr (hdom γ hr hγp) c
    · rw [iSup_neg hγ, Subgroup.mem_bot] at hy
      subst hy
      intro x hx
      simpa using hx
  · intro x hx
    simpa using hx
  · intro x y hx hy z hz
    have e : x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hy z hz)

theorem conj_UA_bor {a : Fin e7Data.d} (hdom : ∀ γ, IsRoot .E7 γ → 0 < ht γ → pr a γ ≠ -1)
    {b : Gp K} (hb : b ∈ Bor K) : ∀ x ∈ UA K a, b * x * b⁻¹ ∈ UA K a := by
  obtain ⟨u, hu, t, ht', rfl⟩ := bor_eq_mul hb
  intro x hx
  have e : u * t * x * (u * t)⁻¹ = u * (t * x * t⁻¹) * u⁻¹ := by group
  rw [e]
  exact conj_UA_uni hdom hu _ (conj_UA_tor a ht' x hx)

theorem conj_UA_bor7 {b : Gp K} (hb : b ∈ Bor K) :
    ∀ x ∈ UA K (⟨0, by decide⟩ : Fin e7Data.d), b * x * b⁻¹ ∈ UA K (⟨0, by decide⟩ : Fin e7Data.d) := by
  exact conj_UA_bor (a := (⟨0, by decide⟩ : Fin e7Data.d))
    (fun γ hγ hpos => pr_zero_ne_neg_one_of_pos hγ hpos) hb

end CFSG.RankThree.GF2n.Smith81.E7X

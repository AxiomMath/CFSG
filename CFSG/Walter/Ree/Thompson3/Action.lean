module

public import CFSG.Walter.Ree.Thompson3.Presentation

public section

namespace CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3]

abbrev ppv (σ : k ≃+* k) (v : k × k × k) : ThompsonN k σ := pp σ v.1 v.2.1 v.2.2

@[expose] def coords {σ : k ≃+* k} (n : ThompsonN k σ) : k × k × k := (n.α, n.β, n.γ)

theorem ppv_mem_P (σ : k ≃+* k) (v : k × k × k) : ppv σ v ∈ ThompsonN.P σ := rfl

theorem ppv_zero (σ : k ≃+* k) : ppv σ (0, 0, 0) = 1 := rfl

omit [CharP k 3] in
theorem coords_ppv (σ : k ≃+* k) (v : k × k × k) : coords (ppv σ v) = v := rfl

theorem ppv_coords {σ : k ≃+* k} {p : ThompsonN k σ} (hp : p ∈ ThompsonN.P σ) :
    ppv σ (coords p) = p := (ThompsonN.eq_of_mem_P hp).symm

theorem torus_mul_ppv_coords {σ : k ≃+* k} (m : ThompsonN k σ) :
    ThompsonN.torus σ m.κ * ppv σ (coords m) = m := by
  ext <;> simp [ThompsonN.mul_def, thompsonMul, coords, pp]

namespace RType

variable [Finite k] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem exists_pres'
    {g : G} (hg : g ∉ R.N) :
    ∃ v : k × k × k, ∃ ν : ThompsonN k σ, g = R.ι ν * R.K * R.ι (ppv σ v) := by
  obtain ⟨ν, v, h⟩ := R.exists_pres hg
  exact ⟨v, ν, h⟩

@[expose] noncomputable def pt
    (g : G) : Option (k × k × k) := by
  classical
  exact if hg : g ∈ R.N then none else some (Classical.choose (R.exists_pres' hg))

theorem pt_of_mem
    {g : G} (hg : g ∈ R.N) : R.pt g = none := by
  classical
  simp [pt, hg]

theorem pt_eq_none_iff
    (g : G) : R.pt g = none ↔ g ∈ R.N := by
  classical
  refine ⟨fun h => ?_, R.pt_of_mem⟩
  by_contra hg
  simp [pt, hg] at h

omit [Finite k] in
theorem pres_not_mem (ν : ThompsonN k σ) (v : k × k × k) :
    R.ι ν * R.K * R.ι (ppv σ v) ∉ R.N :=
  R.presMap_not_mem (ν, ⟨ppv σ v, ppv_mem_P σ v⟩)

theorem pt_pres
    (ν : ThompsonN k σ) (v : k × k × k) :
    R.pt (R.ι ν * R.K * R.ι (ppv σ v)) = some v := by
  classical
  have hg := R.pres_not_mem ν v
  simp only [pt, hg, dite_false, Option.some.injEq]
  have h := Classical.choose_spec (R.exists_pres' hg)
  obtain ⟨ν', hν'⟩ := h
  exact (R.pres_unique hν'.symm).2

theorem pt_eq_some_iff
    (g : G) (v : k × k × k) :
    R.pt g = some v ↔ ∃ ν : ThompsonN k σ, g = R.ι ν * R.K * R.ι (ppv σ v) := by
  constructor
  · intro h
    have hg : g ∉ R.N := fun hg => by rw [R.pt_of_mem hg] at h; simp at h
    obtain ⟨w, ν, hν⟩ := R.exists_pres' hg
    rw [hν, R.pt_pres, Option.some.injEq] at h
    exact ⟨ν, h ▸ hν⟩
  · rintro ⟨ν, rfl⟩; exact R.pt_pres ν v

theorem pt_mul_left
    {n g : G} (hn : n ∈ R.N) : R.pt (n * g) = R.pt g := by
  by_cases hg : g ∈ R.N
  · rw [R.pt_of_mem hg, R.pt_of_mem (R.N.mul_mem hn hg)]
  · obtain ⟨v, ν, rfl⟩ := R.exists_pres' hg
    obtain ⟨n', rfl⟩ := R.exists_ι hn
    rw [R.pt_pres, show R.ι n' * (R.ι ν * R.K * R.ι (ppv σ v)) =
      R.ι (n' * ν) * R.K * R.ι (ppv σ v) by rw [map_mul]; group, R.pt_pres]

@[expose] noncomputable def rep : Option (k × k × k) → G
  | none => 1
  | some v => R.K * R.ι (ppv σ v)

omit [Finite k] in
theorem rep_eq_pres (v : k × k × k) : R.rep (some v) = R.ι 1 * R.K * R.ι (ppv σ v) := by
  simp [rep]

theorem pt_rep
    (ω : Option (k × k × k)) : R.pt (R.rep ω) = ω := by
  cases ω with
  | none => exact R.pt_of_mem R.N.one_mem
  | some v => rw [R.rep_eq_pres, R.pt_pres]

theorem exists_eq_mul_rep
    (g : G) : ∃ n ∈ R.N, g = n * R.rep (R.pt g) := by
  by_cases hg : g ∈ R.N
  · exact ⟨g, hg, by rw [R.pt_of_mem hg]; simp [rep]⟩
  · obtain ⟨v, ν, rfl⟩ := R.exists_pres' hg
    refine ⟨R.ι ν, R.ι_mem ν, ?_⟩
    rw [R.pt_pres]; simp only [rep]; group

@[expose] noncomputable def act
    (ω : Option (k × k × k)) (g : G) : Option (k × k × k) :=
  R.pt (R.rep ω * g)

theorem act_one
    (ω : Option (k × k × k)) : R.act ω 1 = ω := by
  rw [act, mul_one, R.pt_rep]

theorem act_mul
    (ω : Option (k × k × k)) (g h : G) :
    R.act ω (g * h) = R.act (R.act ω g) h := by
  obtain ⟨n, hn, he⟩ := R.exists_eq_mul_rep (R.rep ω * g)
  calc R.act ω (g * h) = R.pt (R.rep ω * g * h) := by rw [act, mul_assoc]
    _ = R.pt (n * (R.rep (R.pt (R.rep ω * g)) * h)) := by rw [← mul_assoc, ← he]
    _ = R.act (R.act ω g) h := by rw [R.pt_mul_left hn]; rfl

theorem act_none
    (g : G) : R.act none g = R.pt g := by simp [act, rep]

theorem act_none_eq_none_iff
    (g : G) : R.act none g = none ↔ g ∈ R.N := by
  rw [act_none, pt_eq_none_iff]

theorem act_act_inv
    (ω : Option (k × k × k)) (g : G) : R.act (R.act ω g) g⁻¹ = ω := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_inv_act
    (ω : Option (k × k × k)) (g : G) : R.act (R.act ω g⁻¹) g = ω := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_injective
    (g : G) : Function.Injective (fun ω => R.act ω g) := by
  intro ω ω' h
  have := congrArg (fun x => R.act x g⁻¹) h
  simpa only [act_act_inv] using this

theorem act_eq_iff
    (ω ω' : Option (k × k × k)) (g : G) :
    R.act ω g = ω' ↔ ω = R.act ω' g⁻¹ := by
  constructor
  · rintro rfl; rw [act_act_inv]
  · rintro rfl; rw [act_inv_act]

@[expose] noncomputable def perm
    (g : G) : Equiv.Perm (Option (k × k × k)) where
  toFun ω := R.act ω g⁻¹
  invFun ω := R.act ω g
  left_inv ω := by simp only; rw [← act_mul, inv_mul_cancel, act_one]
  right_inv ω := by simp only; rw [← act_mul, mul_inv_cancel, act_one]

@[expose] noncomputable def ρ :
    G →* Equiv.Perm (Option (k × k × k)) where
  toFun := R.perm
  map_one' := by ext ω; simp [perm, act_one]
  map_mul' g h := by
    ext ω
    simp only [perm, Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply, mul_inv_rev,
      act_mul]

theorem ρ_apply
    (g : G) (ω : Option (k × k × k)) : R.ρ g ω = R.act ω g⁻¹ := rfl

theorem act_ι
    (v : k × k × k) (n : ThompsonN k σ) :
    R.act (some v) (R.ι n) = some (coords (ppv σ v * n)) := by
  set m := ppv σ v * n
  have h : R.rep (some v) * R.ι n =
      R.ι (ThompsonN.torus σ m.κ⁻¹) * R.K * R.ι (ppv σ (coords m)) := by
    have hm : R.ι m = R.ι (ThompsonN.torus σ m.κ) * R.ι (ppv σ (coords m)) := by
      rw [← map_mul, torus_mul_ppv_coords]
    calc R.rep (some v) * R.ι n = R.K * R.ι m := by rw [rep, mul_assoc, ← map_mul]
      _ = R.K * R.ι (ThompsonN.torus σ m.κ) * R.ι (ppv σ (coords m)) := by rw [hm, mul_assoc]
      _ = _ := by rw [R.K_mul_torus]
  rw [act, h, R.pt_pres]

theorem act_none_ι
    (n : ThompsonN k σ) : R.act none (R.ι n) = none := by
  rw [act_none_eq_none_iff]; exact R.ι_mem n

theorem act_none_of_mem
    {g : G} (hg : g ∈ R.N) : R.act none g = none :=
  (R.act_none_eq_none_iff g).mpr hg

theorem act_none_K :
    R.act none R.K = some (0, 0, 0) := by
  rw [act_none, pt_eq_some_iff]
  exact ⟨1, by rw [ppv_zero, map_one, one_mul, mul_one]⟩

theorem act_zero_K :
    R.act (some (0, 0, 0)) R.K = none := by
  rw [act, rep, ppv_zero, map_one, mul_one, R.K_mul_K, R.pt_of_mem R.N.one_mem]

theorem act_K_of_eq
    {v w : k × k × k} {ν : ThompsonN k σ}
    (h : R.K * R.ι (ppv σ v) * R.K = R.ι ν * R.K * R.ι (ppv σ w)) :
    R.act (some v) R.K = some w := by
  rw [act, rep, h, R.pt_pres]

theorem act_K_K
    (ω : Option (k × k × k)) : R.act (R.act ω R.K) R.K = ω := by
  rw [← act_mul, R.K_mul_K, act_one]

theorem fix_none_zero_iff (g : G) :
    (R.act none g = none ∧ R.act (some (0, 0, 0)) g = some (0, 0, 0)) ↔
      ∃ t : kˣ, g = R.ι (ThompsonN.torus σ t) := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨n, rfl⟩ := R.exists_ι ((R.act_none_eq_none_iff g).mp h1)
    rw [act_ι, Option.some.injEq, ppv_zero, one_mul] at h2
    refine ⟨n.κ, ?_⟩
    congr 1
    have := torus_mul_ppv_coords n
    rw [h2, ppv_zero, mul_one] at this
    exact this.symm
  · rintro ⟨t, rfl⟩
    refine ⟨R.act_none_ι _, ?_⟩
    rw [act_ι, ppv_zero, one_mul]
    rfl

theorem eq_one_of_act
    {g : G} (h : ∀ ω, R.act ω g = ω) : g = 1 := by
  obtain ⟨t, rfl⟩ := (R.fix_none_zero_iff g).mp ⟨h none, h _⟩
  have h1 := h (some (1, 0, 0))
  rw [act_ι, Option.some.injEq] at h1
  have h2 : (t : k) = 1 := by
    have := congrArg Prod.fst h1
    simpa [coords, ThompsonN.mul_def, thompsonMul, pp] using this
  have : t = 1 := Units.ext h2
  rw [this, map_one, map_one]

theorem ρ_injective :
    Function.Injective R.ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g⁻¹ = 1 := R.eq_one_of_act fun ω => by
    have := congrArg (fun f : Equiv.Perm (Option (k × k × k)) => f ω) hg
    simpa [ρ_apply] using this
  exact inv_eq_one.mp this

theorem act_rep_inv
    (ω : Option (k × k × k)) : R.act ω (R.rep ω)⁻¹ = none := by
  rw [act, mul_inv_cancel, R.pt_of_mem R.N.one_mem]

theorem act_none_rep
    (ω : Option (k × k × k)) : R.act none (R.rep ω) = ω := by
  rw [act_none, pt_rep]

theorem act_ppv_inv
    (v : k × k × k) : R.act (some v) (R.ι (ppv σ v)⁻¹) = some (0, 0, 0) := by
  rw [act_ι, mul_inv_cancel]; rfl

theorem exists_two
    {ω₁ ω₂ : Option (k × k × k)} (h : ω₁ ≠ ω₂) :
    ∃ g : G, R.act ω₁ g = none ∧ R.act ω₂ g = some (0, 0, 0) := by
  set g₁ := (R.rep ω₁)⁻¹
  have h1 : R.act ω₁ g₁ = none := R.act_rep_inv ω₁
  obtain ⟨v, hv⟩ : ∃ v, R.act ω₂ g₁ = some v := by
    rcases h2 : R.act ω₂ g₁ with _ | v
    · exact absurd ((R.act_injective g₁) (h1.trans h2.symm)) h
    · exact ⟨v, rfl⟩
  refine ⟨g₁ * R.ι (ppv σ v)⁻¹, ?_, ?_⟩
  · rw [act_mul, h1, act_none_ι]
  · rw [act_mul, hv, act_ppv_inv]

end RType

end CFSG.Walter.Ree.T2

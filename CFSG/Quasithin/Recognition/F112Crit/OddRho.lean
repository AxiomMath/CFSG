module

public import CFSG.Quasithin.Background.F7Geometry

public section

namespace CFSG.Quasithin.F112Crit

open CosetGeom (graph stab ballStab nbrs vtype)

variable {G : Type} [Group G] {G₀ G₁ G₂ : Subgroup G}

@[expose] noncomputable def rhoNbrs (x : G) (δ : CosetGeom G₀ G₁ G₂) : ZMod 2 := by
  classical exact if x ∈ ballStab 1 δ then 0 else 1

theorem rhoNbrs_eq_zero_iff {x : G} {δ : CosetGeom G₀ G₁ G₂} :
    rhoNbrs x δ = 0 ↔ x ∈ ballStab 1 δ := by
  by_cases h : x ∈ ballStab 1 δ
  · simp only [rhoNbrs, if_pos h]
    exact ⟨fun _ => h, fun _ => trivial⟩
  · simp only [rhoNbrs, if_neg h]
    exact ⟨fun h0 => absurd h0 (by decide), fun hb => absurd hb h⟩

theorem rhoNbrs_eq_one_iff {x : G} {δ : CosetGeom G₀ G₁ G₂} :
    rhoNbrs x δ = 1 ↔ x ∉ ballStab 1 δ := by
  by_cases h : x ∈ ballStab 1 δ
  · simp only [rhoNbrs, if_pos h]
    exact ⟨fun h0 => absurd h0 (by decide), fun hb => absurd h hb⟩
  · simp only [rhoNbrs, if_neg h]
    exact ⟨fun _ => h, fun _ => trivial⟩

private theorem smul_mem_nbrs_of_mem_stab {δ : CosetGeom G₀ G₁ G₂} {g : ↥G₀}
    (hg : (g : G) ∈ stab δ) {u : CosetGeom G₀ G₁ G₂} (hu : u ∈ nbrs δ) :
    g • u ∈ nbrs δ := by
  have h := (CosetGeom.smul_adj g).mpr hu
  rwa [CosetGeom.smul_eq_of_mem_stab hg] at h

private theorem smul_ne_of_smul_eq_self {g : ↥G₀} {a b : CosetGeom G₀ G₁ G₂}
    (hb : g • b = b) (hab : a ≠ b) : g • a ≠ b := by
  intro h
  exact hab (smul_left_cancel g (by rw [h, hb]))

private theorem smul_cases_of_mem_stab {δ μ ε ε' : CosetGeom G₀ G₁ G₂}
    (hS : nbrs δ = {μ, ε, ε'}) (hμε : μ ≠ ε) (hμε' : μ ≠ ε') (hee' : ε ≠ ε')
    {g : ↥G₀} (hg : (g : G) ∈ stab δ ⊓ stab μ) :
    (g • ε = ε ∨ g • ε = ε') ∧ (g • ε' = ε' ∨ g • ε' = ε) ∧
      (g • ε = ε ↔ g • ε' = ε') := by
  have hgδ : (g : G) ∈ stab δ := hg.1
  have hgμ : g • μ = μ := CosetGeom.smul_eq_of_mem_stab hg.2
  have hεmem : ε ∈ nbrs δ := by rw [hS]; simp
  have hε'mem : ε' ∈ nbrs δ := by rw [hS]; simp
  have hεn : g • ε ∈ nbrs δ := smul_mem_nbrs_of_mem_stab hgδ hεmem
  have hε'n : g • ε' ∈ nbrs δ := smul_mem_nbrs_of_mem_stab hgδ hε'mem
  rw [hS] at hεn hε'n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hεn hε'n
  have hεne : g • ε ≠ μ := smul_ne_of_smul_eq_self hgμ hμε.symm
  have hε'ne : g • ε' ≠ μ := smul_ne_of_smul_eq_self hgμ hμε'.symm
  have hεcases : g • ε = ε ∨ g • ε = ε' := by
    rcases hεn with h | h | h
    · exact absurd h hεne
    · exact Or.inl h
    · exact Or.inr h
  have hε'cases : g • ε' = ε' ∨ g • ε' = ε := by
    rcases hε'n with h | h | h
    · exact absurd h hε'ne
    · exact Or.inr h
    · exact Or.inl h
  refine ⟨hεcases, hε'cases, ?_⟩
  constructor
  · intro h
    rcases hε'cases with h' | h'
    · exact h'
    · exact absurd (smul_left_cancel g (by rw [h', h])).symm hee'
  · intro h
    rcases hεcases with h' | h'
    · exact h'
    · exact absurd (smul_left_cancel g (by rw [h', h])) hee'

private theorem mem_ballStab_one_iff_smul (hG : G₀ = G₁ ⊔ G₂) {δ μ ε ε' : CosetGeom G₀ G₁ G₂}
    (hS : nbrs δ = {μ, ε, ε'}) (hμε : μ ≠ ε) (hμε' : μ ≠ ε') (hee' : ε ≠ ε')
    {g : ↥G₀} (hg : (g : G) ∈ stab δ ⊓ stab μ) :
    (g : G) ∈ ballStab 1 δ ↔ g • ε = ε := by
  obtain ⟨-, hε'cases, hiff⟩ := smul_cases_of_mem_stab hS hμε hμε' hee' hg
  have hεmem : ε ∈ nbrs δ := by rw [hS]; simp
  constructor
  · intro hb
    exact CosetGeom.smul_eq_of_mem_stab
      (CosetGeom.mem_ballStab.mp hb ε (CosetGeom.dist_eq_one_iff_adj.mpr hεmem).le)
  · intro hε
    refine CosetGeom.mem_ballStab.mpr fun w hw => ?_
    rcases (CosetGeom.dist_le_one_iff hG).mp hw with rfl | hadj
    · exact hg.1
    · have hwmem : w ∈ nbrs δ := hadj
      rw [hS] at hwmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
      rcases hwmem with hw | hw | hw
      · subst w; exact hg.2
      · subst w; exact CosetGeom.mem_stab_of_smul_eq hε
      · subst w; exact CosetGeom.mem_stab_of_smul_eq (hiff.mp hε)

private theorem rhoNbrs_eq_ite (hG : G₀ = G₁ ⊔ G₂) {δ μ ε ε' : CosetGeom G₀ G₁ G₂}
    (hS : nbrs δ = {μ, ε, ε'}) (hμε : μ ≠ ε) (hμε' : μ ≠ ε') (hee' : ε ≠ ε')
    {g : ↥G₀} (hg : (g : G) ∈ stab δ ⊓ stab μ) [Decidable (g • ε = ε)] :
    rhoNbrs (g : G) δ = if g • ε = ε then 0 else 1 := by
  have h := mem_ballStab_one_iff_smul hG hS hμε hμε' hee' hg
  by_cases hc : g • ε = ε
  · rw [rhoNbrs_eq_zero_iff.mpr (h.mpr hc), if_pos hc]
  · rw [rhoNbrs_eq_one_iff.mpr (fun hb => hc (h.mp hb)), if_neg hc]

theorem rhoNbrs_mul (hG : G₀ = G₁ ⊔ G₂) {δ μ : CosetGeom G₀ G₁ G₂} (h3 : (nbrs δ).ncard = 3)
    (hμ : μ ∈ nbrs δ) {x y : G} (hx : x ∈ stab δ ⊓ stab μ) (hy : y ∈ stab δ ⊓ stab μ) :
    rhoNbrs (x * y) δ = rhoNbrs x δ + rhoNbrs y δ := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := Set.ncard_eq_three.mp h3
  have hμabc : μ ∈ ({a, b, c} : Set (CosetGeom G₀ G₁ G₂)) := hS ▸ hμ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμabc
  have hex : ∃ ε ε' : CosetGeom G₀ G₁ G₂, μ ≠ ε ∧ μ ≠ ε' ∧ ε ≠ ε' ∧
      nbrs δ = {μ, ε, ε'} := by
    rcases hμabc with rfl | rfl | rfl
    · exact ⟨b, c, hab, hac, hbc, hS⟩
    · exact ⟨a, c, hab.symm, hbc, hac, by rw [hS, Set.insert_comm a μ]⟩
    · exact ⟨a, b, hac.symm, hbc.symm, hab, by
        rw [hS]
        ext w
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto⟩
  obtain ⟨ε, ε', hμε, hμε', hee', hS⟩ := hex
  let xG : ↥G₀ := ⟨x, CosetGeom.stab_le δ hx.1⟩
  let yG : ↥G₀ := ⟨y, CosetGeom.stab_le δ hy.1⟩
  have hxy : x * y ∈ stab δ ⊓ stab μ := mul_mem hx hy
  let xyG : ↥G₀ := ⟨x * y, CosetGeom.stab_le δ hxy.1⟩
  change rhoNbrs (xyG : G) δ = rhoNbrs (xG : G) δ + rhoNbrs (yG : G) δ
  obtain ⟨hxcases, hx'cases, hxiff⟩ :=
    smul_cases_of_mem_stab hS hμε hμε' hee' (g := xG) hx
  obtain ⟨hycases, -, -⟩ := smul_cases_of_mem_stab hS hμε hμε' hee' (g := yG) hy
  have hxite := rhoNbrs_eq_ite hG hS hμε hμε' hee' (g := xG) hx
  have hyite := rhoNbrs_eq_ite hG hS hμε hμε' hee' (g := yG) hy
  have hxyite := rhoNbrs_eq_ite hG hS hμε hμε' hee' (g := xyG) hxy
  have hxy_smul : xyG • ε = xG • (yG • ε) := by
    rw [show xyG = xG * yG from Subtype.ext rfl, mul_smul]
  rw [hxyite, hxite, hyite, hxy_smul]
  have hne : ε' ≠ ε := hee'.symm
  rcases hycases with hyε | hyε
  · rw [hyε]
    by_cases hxε : xG • ε = ε
    · simp [hxε]
    · simp [hxε]
  · rw [hyε]
    by_cases hxε : xG • ε = ε
    · have hx' : xG • ε' = ε' := hxiff.mp hxε
      simp [hxε, hx', hne]
    · have hx' : xG • ε' = ε := by
        rcases hx'cases with h | h
        · exact absurd (hxiff.mpr h) hxε
        · exact h
      simp [hxε, hx', hne]
      decide

theorem rhoNbrs_conj (g : ↥G₀) (x : G) (δ : CosetGeom G₀ G₁ G₂) :
    rhoNbrs ((g : G) * x * (g : G)⁻¹) (g • δ) = rhoNbrs x δ := by
  by_cases h : x ∈ ballStab 1 δ
  · have h' : (g : G) * x * (g : G)⁻¹ ∈ ballStab 1 (g • δ) := by
      rw [CosetGeom.ballStab_smul, mem_conjSub]
      simpa [mul_assoc] using h
    rw [rhoNbrs_eq_zero_iff.mpr h', rhoNbrs_eq_zero_iff.mpr h]
  · have h' : (g : G) * x * (g : G)⁻¹ ∉ ballStab 1 (g • δ) := by
      rw [CosetGeom.ballStab_smul, mem_conjSub]
      simpa [mul_assoc] using h
    rw [rhoNbrs_eq_one_iff.mpr h', rhoNbrs_eq_one_iff.mpr h]

end CFSG.Quasithin.F112Crit

end

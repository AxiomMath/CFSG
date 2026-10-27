module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOffNatA

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

set_option linter.unusedSectionVars false

theorem alt5_three_comm : ∀ t u : Alt5, t ^ 3 = 1 → u * u = 1 → u ≠ 1 → t * u = u * t →
    t = 1 := by
  decide +kernel

theorem alt5_eq_of_normalized {V U : Subgroup Alt5} (hV : Nat.card V = 4) (hU : U ≤ V)
    (hne : U ≠ ⊥) {t : Alt5} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) (ht : ∀ u ∈ U, t * u * t⁻¹ ∈ U) :
    U = V := by
  obtain ⟨⟨u, huU⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : u * u = 1 := alt5_klein_sq hV (hU huU)
  have htu := ht u huU
  have hdvd : Nat.card U ∣ 4 := hV ▸ Subgroup.card_dvd_of_le hU
  have hU1 : Nat.card U ≠ 1 := by
    intro h
    exact hne ((Subgroup.card_eq_one).mp h)
  have hU2 : Nat.card U ≠ 2 := by
    intro h
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : U)).mp h
    have h1 := hy ⟨u, huU⟩ hu1
    have h2 : (⟨t * u * t⁻¹, htu⟩ : U) ≠ 1 := by
      intro h'
      have : t * u * t⁻¹ = 1 := congrArg Subtype.val h'
      apply hu1'
      calc u = t⁻¹ * (t * u * t⁻¹) * t := by group
        _ = 1 := by rw [this]; group
    have h3 := hy _ h2
    have h4 : t * u * t⁻¹ = u := by
      have := h3.trans h1.symm
      exact congrArg Subtype.val this
    apply ht1
    refine alt5_three_comm t u ht3 hu2 hu1' ?_
    calc t * u = (t * u * t⁻¹) * t := by group
      _ = u * t := by rw [h4]
  have h4 : Nat.card U = 4 := by
    have hle : Nat.card U ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card U := Nat.card_pos
    interval_cases h : Nat.card U <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hU (by rw [hV, h4])

section Cover

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}
variable (F : Frame L1 L2 S D X)
include F

theorem klein_cover {u α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hu : vtype u = true)
    (hα' : α' ∈ nbrs u) {K : Subgroup G} (hKQ : K ≤ Qv α') {ρ : G} (hρ : ρ ∈ stab u)
    (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∉ Qv u) (hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K)
    (hKnt : ∃ k ∈ K, k ∉ Qv u) :
    ∀ x ∈ Qv α', ∃ k ∈ K, k⁻¹ * x ∈ Qv u := by
  have hA := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hu
  have hQs : Qv α' ≤ stab u := hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hα')
  have hV := card_map_Qv_nbr F hu hα' hφs hφk
  set V := ((Qv α').subgroupOf (stab u)).map φ with hVdef
  set U := (K.subgroupOf (stab u)).map φ with hUdef
  have hUV : U ≤ V := by
    refine Subgroup.map_mono ?_
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hKQ (Subgroup.mem_subgroupOf.mp hy))
  have hker : ∀ y : ↥(stab u), φ y = 1 ↔ (y : G) ∈ Qv u := by
    intro y
    rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have hne : U ≠ ⊥ := by
    obtain ⟨k, hk, hkQ⟩ := hKnt
    intro hb
    have hmem : φ ⟨k, hQs (hKQ hk)⟩ ∈ U :=
      ⟨⟨k, hQs (hKQ hk)⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact hkQ ((hker _).mp hmem)
  set t : Alt5 := φ ⟨ρ, hρ⟩ with htdef
  have ht3 : t ^ 3 = 1 := by
    rw [htdef, ← map_pow]
    have : (⟨ρ, hρ⟩ : ↥(stab u)) ^ 3 = 1 := Subtype.ext (by simpa using hρ3)
    rw [this, map_one]
  have ht1 : t ≠ 1 := fun h => hρQ ((hker _).mp h)
  have hUt : ∀ y ∈ U, t * y * t⁻¹ ∈ U := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨ρ, hρ⟩ * k * ⟨ρ, hρ⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hk' : (k : G) ∈ K := hk
    show ((⟨ρ, hρ⟩ * k * ⟨ρ, hρ⟩⁻¹ : ↥(stab u)) : G) ∈ K
    have := hρK _ hk'
    simpa using this
  have hUeq : U = V := alt5_eq_of_normalized hV hUV hne ht3 ht1 hUt
  intro x hx
  have hmem : φ ⟨x, hQs hx⟩ ∈ U := by
    rw [hUeq]
    exact ⟨⟨x, hQs hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨k, hk, hkx⟩ := hmem
  refine ⟨(k : G), Subgroup.mem_subgroupOf.mp hk, ?_⟩
  have : φ (k⁻¹ * ⟨x, hQs hx⟩) = 1 := by rw [map_mul, map_inv, hkx]; group
  exact (hker _).mp this

end Cover

end CFSG.Quasithin.Kleidman.F204

module

public import CFSG.Quasithin.H13.GoldschmidtI51GQSub
public import CFSG.Quasithin.H13.GoldschmidtI51Local

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6 Equiv

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

@[expose] def Nr (Gs : Fin 3 → Subgroup G) (u : G) : Prop :=
  ∃ a ∈ Gs 0 ⊓ Gs 1, ∃ b ∈ Gs 0 ⊓ Gs 2, ∃ c ∈ Gs 0 ⊓ Gs 1, u = a * b * c

structure Mod0 (Gs : Fin 3 → Subgroup G) (b o : Bool) where
  ψ : ↥(Gs 0) →* Perm (Fin 6)
  range : ψ.range = sgR b
  ker : ψ.ker = CFSG.Open.pCore 2 ↥(Gs 0)
  hA : ((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)).map ψ = sgA b o
  hB : ((Gs 0 ⊓ Gs 2).subgroupOf (Gs 0)).map ψ = sgB b o

theorem model0_bo (hD : IsDSystem .C3 Gs) : ∃ b o : Bool, Nonempty (Mod0 Gs b o) := by
  obtain ⟨R, A, B, ψ, hR, hrange, hker, hA, hB, hT, hAB⟩ := model0 hD
  rcases hR with rfl | rfl
  · rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨false, true, ⟨ψ, by simpa [sgR] using hrange, hker, by simpa [sgA, sgR] using hA,
        by simpa [sgB, sgR] using hB⟩⟩
    · exact ⟨false, false, ⟨ψ, by simpa [sgR] using hrange, hker, by simpa [sgA, sgR] using hA,
        by simpa [sgB, sgR] using hB⟩⟩
  · rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨true, true, ⟨ψ, by simpa [sgR] using hrange, hker, by simpa [sgA, sgR] using hA,
        by simpa [sgB, sgR] using hB⟩⟩
    · exact ⟨true, false, ⟨ψ, by simpa [sgR] using hrange, hker, by simpa [sgA, sgR] using hA,
        by simpa [sgB, sgR] using hB⟩⟩

namespace Mod0

variable {b o : Bool} (M : Mod0 Gs b o)

omit [Finite G] in
theorem mem_R (u : ↥(Gs 0)) : M.ψ u ∈ sgR b := by
  rw [← M.range]; exact ⟨u, rfl⟩

omit [Finite G] in
theorem exists_pre {σ : Perm (Fin 6)} (hσ : σ ∈ sgR b) : ∃ u : ↥(Gs 0), M.ψ u = σ := by
  rw [← M.range] at hσ; exact hσ

omit [Finite G] in
theorem ker_mem {u : ↥(Gs 0)} : M.ψ u = 1 ↔ (u : G) ∈ QQ Gs 0 :=
  (MonoidHom.mem_ker (f := M.ψ)).symm.trans (mem_ker_iff_mem_pCoreOf' M.ψ M.ker u)

variable (hD : IsDSystem .C3 Gs)

include hD in
theorem memP {u : ↥(Gs 0)} : (u : G) ∈ Gs 0 ⊓ Gs 1 ↔ M.ψ u ∈ sgA b o := by
  constructor
  · intro h
    rw [← M.hA]
    exact ⟨u, Subgroup.mem_subgroupOf.2 h, rfl⟩
  · intro h
    rw [← M.hA] at h
    obtain ⟨p, hp, hpu⟩ := h
    have hq : M.ψ (p⁻¹ * u) = 1 := by rw [map_mul, map_inv, hpu]; group
    have hqQ := M.ker_mem.1 hq
    have e : (u : G) = (p : G) * ((p⁻¹ * u : ↥(Gs 0)) : G) := by simp
    rw [e]
    exact (Gs 0 ⊓ Gs 1).mul_mem (Subgroup.mem_subgroupOf.1 hp) (Q0_le_P01 hD hqQ)

include hD in
theorem memP' {u : ↥(Gs 0)} : (u : G) ∈ Gs 0 ⊓ Gs 2 ↔ M.ψ u ∈ sgB b o := by
  constructor
  · intro h
    rw [← M.hB]
    exact ⟨u, Subgroup.mem_subgroupOf.2 h, rfl⟩
  · intro h
    rw [← M.hB] at h
    obtain ⟨p, hp, hpu⟩ := h
    have hq : M.ψ (p⁻¹ * u) = 1 := by rw [map_mul, map_inv, hpu]; group
    have hqQ := M.ker_mem.1 hq
    have e : (u : G) = (p : G) * ((p⁻¹ * u : ↥(Gs 0)) : G) := by simp
    rw [e]
    exact (Gs 0 ⊓ Gs 2).mul_mem (Subgroup.mem_subgroupOf.1 hp) (Q0_le_P02 hD hqQ)

end Mod0

namespace Mod0

variable {b o : Bool} (M : Mod0 Gs b o)

noncomputable def f (g : G) : Perm (Fin 6) := by
  classical exact if h : g ∈ Gs 0 then M.ψ ⟨g, h⟩ else 1

omit [Finite G] in
theorem f_of_mem {g : G} (h : g ∈ Gs 0) : M.f g = M.ψ ⟨g, h⟩ := by
  simp [f, h]

omit [Finite G] in
theorem f_mul {g h : G} (hg : g ∈ Gs 0) (hh : h ∈ Gs 0) : M.f (g * h) = M.f g * M.f h := by
  rw [M.f_of_mem hg, M.f_of_mem hh, M.f_of_mem ((Gs 0).mul_mem hg hh)]
  exact map_mul M.ψ ⟨g, hg⟩ ⟨h, hh⟩

omit [Finite G] in
theorem f_inv {g : G} (hg : g ∈ Gs 0) : M.f g⁻¹ = (M.f g)⁻¹ := by
  rw [M.f_of_mem hg, M.f_of_mem ((Gs 0).inv_mem hg)]
  exact map_inv M.ψ ⟨g, hg⟩

omit [Finite G] in
theorem f_mem_R {g : G} (hg : g ∈ Gs 0) : M.f g ∈ sgR b := by
  rw [M.f_of_mem hg]; exact M.mem_R _

omit [Finite G] in
theorem exists_f {σ : Perm (Fin 6)} (hσ : σ ∈ sgR b) : ∃ g ∈ Gs 0, M.f g = σ := by
  obtain ⟨u, hu⟩ := M.exists_pre hσ
  exact ⟨u, u.2, by rw [M.f_of_mem u.2]; exact hu⟩

omit [Finite G] in
theorem f_ker {g : G} (hg : g ∈ Gs 0) : M.f g = 1 ↔ g ∈ QQ Gs 0 := by
  rw [M.f_of_mem hg]; exact M.ker_mem (u := ⟨g, hg⟩)

variable (hD : IsDSystem .C3 Gs)

include hD in
theorem f_P {g : G} (hg : g ∈ Gs 0) : g ∈ Gs 0 ⊓ Gs 1 ↔ M.f g ∈ sgA b o := by
  rw [M.f_of_mem hg]; exact M.memP hD (u := ⟨g, hg⟩)

include hD in
theorem f_P' {g : G} (hg : g ∈ Gs 0) : g ∈ Gs 0 ⊓ Gs 2 ↔ M.f g ∈ sgB b o := by
  rw [M.f_of_mem hg]; exact M.memP' hD (u := ⟨g, hg⟩)

include hD in
theorem exists_P {σ : Perm (Fin 6)} (hσ : σ ∈ sgA b o) : ∃ p ∈ Gs 0 ⊓ Gs 1, M.f p = σ := by
  obtain ⟨g, hg, hgσ⟩ := M.exists_f (sgA_le_sgR b o hσ)
  exact ⟨g, (M.f_P hD hg).2 (hgσ ▸ hσ), hgσ⟩

include hD in
theorem exists_P' {σ : Perm (Fin 6)} (hσ : σ ∈ sgB b o) : ∃ p ∈ Gs 0 ⊓ Gs 2, M.f p = σ := by
  obtain ⟨g, hg, hgσ⟩ := M.exists_f (sgB_le_sgR b o hσ)
  exact ⟨g, (M.f_P' hD hg).2 (hgσ ▸ hσ), hgσ⟩

omit [Finite G] in
theorem eq_mul_ker {g h : G} (hg : g ∈ Gs 0) (hh : h ∈ Gs 0) (e : M.f g = M.f h) :
    ∃ q ∈ QQ Gs 0, g = h * q := by
  refine ⟨h⁻¹ * g, ?_, by group⟩
  rw [← M.f_ker ((Gs 0).mul_mem ((Gs 0).inv_mem hh) hg), M.f_mul ((Gs 0).inv_mem hh) hg,
    M.f_inv hh, e]
  group

include hD in
theorem nr_iff {u : G} (hu : u ∈ Gs 0) :
    Nr Gs u ↔ ∃ a ∈ sgA b o, ∃ β ∈ sgB b o, ∃ c ∈ sgA b o, M.f u = a * β * c := by
  constructor
  · rintro ⟨p, hp, q, hq, r, hr, rfl⟩
    refine ⟨M.f p, (M.f_P hD hp.1).1 hp, M.f q, (M.f_P' hD hq.1).1 hq, M.f r,
      (M.f_P hD hr.1).1 hr, ?_⟩
    rw [M.f_mul ((Gs 0).mul_mem hp.1 hq.1) hr.1, M.f_mul hp.1 hq.1]
  · rintro ⟨a, ha, β, hβ, c, hc, h⟩
    obtain ⟨p, hp, hpa⟩ := M.exists_P hD ha
    obtain ⟨q, hq, hqβ⟩ := M.exists_P' hD hβ
    obtain ⟨r, hr, hrc⟩ := M.exists_P hD hc
    have hpqr : p * q * r ∈ Gs 0 := (Gs 0).mul_mem ((Gs 0).mul_mem hp.1 hq.1) hr.1
    have e : M.f u = M.f (p * q * r) := by
      rw [M.f_mul ((Gs 0).mul_mem hp.1 hq.1) hr.1, M.f_mul hp.1 hq.1, hpa, hqβ, hrc, h]
    obtain ⟨s, hs, hus⟩ := M.eq_mul_ker hu hpqr e
    exact ⟨p, hp, q, hq, r * s, (Gs 0 ⊓ Gs 1).mul_mem hr (Q0_le_P01 hD hs), by rw [hus]; group⟩

end Mod0

structure GQLoc (Gs : Fin 3 → Subgroup G) : Prop where
  idx01 : (Gs 0 ⊓ Gs 1).relIndex (Gs 0) = 15
  idx02 : (Gs 0 ⊓ Gs 2).relIndex (Gs 0) = 15
  core : ∀ u ∈ Gs 0, (∀ g ∈ Gs 0, g⁻¹ * u * g ∈ Gs 0 ⊓ Gs 1) → u ∈ QQ Gs 0
  gq3 : ∀ g ∈ Gs 0, ∃ c ∈ Gs 0 ⊓ Gs 2, Nr Gs (c⁻¹ * g)
  farT : ∀ f ∈ Gs 0, ¬ Nr Gs f → ∀ f' ∈ Gs 0, ¬ Nr Gs f' →
    ∃ p ∈ Gs 0 ⊓ Gs 1, ∃ p' ∈ Gs 0 ⊓ Gs 1, f' = p * f * p'
  farE : ∃ f ∈ Gs 0, ¬ Nr Gs f ∧
    ((Gs 0 ⊓ Gs 1) ⊓ cj f (Gs 0 ⊓ Gs 1)).relIndex (Gs 0 ⊓ Gs 1) = 8
  nearD : ∃ n ∈ Gs 0 ⊓ Gs 2, n ∉ Gs 0 ⊓ Gs 1 ∧
    (∀ u ∈ Gs 0, Nr Gs u → u ∈ Gs 0 ⊓ Gs 1 ∨
      ∃ p ∈ Gs 0 ⊓ Gs 1, ∃ p' ∈ Gs 0 ⊓ Gs 1, u = p * n * p') ∧
    ((Gs 0 ⊓ Gs 1) ⊓ cj n (Gs 0 ⊓ Gs 1)).relIndex (Gs 0 ⊓ Gs 1) = 6

namespace Mod0

variable {b o : Bool} (M : Mod0 Gs b o) (hD : IsDSystem .C3 Gs)

include hD in
theorem subgroupOf01 : (Gs 0 ⊓ Gs 1).subgroupOf (Gs 0) = (sgA b o).comap M.ψ := by
  ext u; rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]; exact M.memP hD

include hD in
theorem subgroupOf02 : (Gs 0 ⊓ Gs 2).subgroupOf (Gs 0) = (sgB b o).comap M.ψ := by
  ext u; rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]; exact M.memP' hD

include M hD in
theorem idx01 : (Gs 0 ⊓ Gs 1).relIndex (Gs 0) = 15 := by
  show ((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)).index = 15
  rw [M.subgroupOf01 hD, Subgroup.index_comap, M.range, relIndex_sgA]

include M hD in
theorem idx02 : (Gs 0 ⊓ Gs 2).relIndex (Gs 0) = 15 := by
  show ((Gs 0 ⊓ Gs 2).subgroupOf (Gs 0)).index = 15
  rw [M.subgroupOf02 hD, Subgroup.index_comap, M.range, relIndex_sgB]

include M hD in
theorem core_loc : ∀ u ∈ Gs 0, (∀ g ∈ Gs 0, g⁻¹ * u * g ∈ Gs 0 ⊓ Gs 1) → u ∈ QQ Gs 0 := by
  intro u hu h
  rw [← M.f_ker hu]
  refine gq_core b o (M.f_mem_R hu) (fun ρ hρ => ?_)
  obtain ⟨g, hg, rfl⟩ := M.exists_f hρ
  have hgug : g⁻¹ * u * g ∈ Gs 0 := (Gs 0).mul_mem ((Gs 0).mul_mem ((Gs 0).inv_mem hg) hu) hg
  have := (M.f_P hD hgug).1 (h g hg)
  rwa [M.f_mul ((Gs 0).mul_mem ((Gs 0).inv_mem hg) hu) hg, M.f_mul ((Gs 0).inv_mem hg) hu,
    M.f_inv hg] at this

include M hD in
theorem gq3_loc : ∀ g ∈ Gs 0, ∃ c ∈ Gs 0 ⊓ Gs 2, Nr Gs (c⁻¹ * g) := by
  intro g hg
  rcases gq_cover b o (M.f_mem_R hg) with h | ⟨a, ha, a', ha', h⟩ | ⟨a, ha, a', ha', h⟩
  · refine ⟨1, (Gs 0 ⊓ Gs 2).one_mem, ?_⟩
    rw [inv_one, one_mul]
    exact (M.nr_iff hD hg).2 ⟨M.f g, h, 1, (sgB b o).one_mem, 1, (sgA b o).one_mem, by group⟩
  · refine ⟨1, (Gs 0 ⊓ Gs 2).one_mem, ?_⟩
    rw [inv_one, one_mul]
    exact (M.nr_iff hD hg).2 ⟨a, ha, nn o, nn_mem_B b o, a', ha', h⟩
  · obtain ⟨c₀, hc₀, h3⟩ := gq_gq3 b o ha
    obtain ⟨c, hc, hcf⟩ := M.exists_P' hD hc₀
    refine ⟨c, hc, ?_⟩
    have hcg : c⁻¹ * g ∈ Gs 0 := (Gs 0).mul_mem ((Gs 0).inv_mem hc.1) hg
    rw [M.nr_iff hD hcg, M.f_mul ((Gs 0).inv_mem hc.1) hg, M.f_inv hc.1, hcf, h]
    rcases h3 with h3 | ⟨a₁, ha₁, a₂, ha₂, h3⟩
    · exact ⟨c₀⁻¹ * a * ff o * a', (sgA b o).mul_mem h3 ha', 1, (sgB b o).one_mem, 1,
        (sgA b o).one_mem, by group⟩
    · exact ⟨a₁, ha₁, nn o, nn_mem_B b o, a₂ * a', (sgA b o).mul_mem ha₂ ha', by
        calc c₀⁻¹ * (a * ff o * a') = (c₀⁻¹ * a * ff o) * a' := by group
          _ = a₁ * nn o * (a₂ * a') := by rw [h3]; group⟩

include M hD in
theorem farT_loc : ∀ f ∈ Gs 0, ¬ Nr Gs f → ∀ f' ∈ Gs 0, ¬ Nr Gs f' →
    ∃ p ∈ Gs 0 ⊓ Gs 1, ∃ p' ∈ Gs 0 ⊓ Gs 1, f' = p * f * p' := by
  intro f hf hnf f' hf' hnf'
  obtain ⟨a, ha, a', ha', h⟩ :=
    gq_far_cover b o (M.f_mem_R hf) (fun h => hnf ((M.nr_iff hD hf).2 h))
  obtain ⟨c, hc, c', hc', h'⟩ :=
    gq_far_cover b o (M.f_mem_R hf') (fun h => hnf' ((M.nr_iff hD hf').2 h))
  obtain ⟨p, hp, hpf⟩ := M.exists_P hD ((sgA b o).mul_mem hc ((sgA b o).inv_mem ha))
  obtain ⟨p', hp', hp'f⟩ := M.exists_P hD ((sgA b o).mul_mem ((sgA b o).inv_mem ha') hc')
  have hmem : p * f * p' ∈ Gs 0 := (Gs 0).mul_mem ((Gs 0).mul_mem hp.1 hf) hp'.1
  have e : M.f f' = M.f (p * f * p') := by
    rw [M.f_mul ((Gs 0).mul_mem hp.1 hf) hp'.1, M.f_mul hp.1 hf, hpf, hp'f, h, h']
    group
  obtain ⟨q, hq, hfq⟩ := M.eq_mul_ker hf' hmem e
  exact ⟨p, hp, p' * q, (Gs 0 ⊓ Gs 1).mul_mem hp' (Q0_le_P01 hD hq), by rw [hfq]; group⟩

end Mod0

namespace Mod0

variable {b o : Bool} (M : Mod0 Gs b o) (hD : IsDSystem .C3 Gs)

include hD in
theorem subgroupOf_conj01 {x : G} (hx : x ∈ Gs 0) {σ : Perm (Fin 6)} (hσ : M.f x = σ) :
    ((Gs 0 ⊓ Gs 1) ⊓ cj x (Gs 0 ⊓ Gs 1)).subgroupOf (Gs 0) =
      (sgA b o ⊓ cj σ (sgA b o)).comap M.ψ := by
  ext u
  have hu := u.2
  have hconj : x⁻¹ * (u : G) * x ∈ Gs 0 :=
    (Gs 0).mul_mem ((Gs 0).mul_mem ((Gs 0).inv_mem hx) hu) hx
  have e : M.f (x⁻¹ * (u : G) * x) = σ⁻¹ * M.ψ u * σ := by
    rw [M.f_mul ((Gs 0).mul_mem ((Gs 0).inv_mem hx) hu) hx, M.f_mul ((Gs 0).inv_mem hx) hu,
      M.f_inv hx, hσ, M.f_of_mem hu]
  have h1 : (u : G) ∈ Gs 0 ⊓ Gs 1 ↔ M.ψ u ∈ sgA b o := M.memP hD
  have h2 : x⁻¹ * (u : G) * x ∈ Gs 0 ⊓ Gs 1 ↔ σ⁻¹ * M.ψ u * σ ∈ sgA b o := by
    rw [M.f_P hD hconj, e]
  show ((u : G) ∈ (Gs 0 ⊓ Gs 1) ⊓ cj x (Gs 0 ⊓ Gs 1)) ↔
    M.ψ u ∈ sgA b o ⊓ cj σ (sgA b o)
  rw [Subgroup.mem_inf, h1, Subgroup.mem_inf, mem_cj, mem_cj, h2]

include hD in
theorem relIndex_conj01 {x : G} (hx : x ∈ Gs 0) {σ : Perm (Fin 6)} (hσ : M.f x = σ) :
    ((Gs 0 ⊓ Gs 1) ⊓ cj x (Gs 0 ⊓ Gs 1)).relIndex (Gs 0 ⊓ Gs 1) =
      (sgA b o ⊓ cj σ (sgA b o)).relIndex (sgA b o) := by
  rw [← Subgroup.relIndex_subgroupOf (inf_le_left : Gs 0 ⊓ Gs 1 ≤ Gs 0),
    M.subgroupOf_conj01 hD hx hσ, M.subgroupOf01 hD, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq, M.range, inf_eq_right.2 (sgA_le_sgR b o)]

include M hD in
theorem farE_loc : ∃ f ∈ Gs 0, ¬ Nr Gs f ∧
    ((Gs 0 ⊓ Gs 1) ⊓ cj f (Gs 0 ⊓ Gs 1)).relIndex (Gs 0 ⊓ Gs 1) = 8 := by
  obtain ⟨f, hf, hff⟩ := M.exists_f (ff_mem_R b o)
  refine ⟨f, hf, fun h => ff_far b o (hff ▸ (M.nr_iff hD hf).1 h), ?_⟩
  rw [M.relIndex_conj01 hD hf hff, relIndex_far]

include M hD in
theorem nearD_loc : ∃ n ∈ Gs 0 ⊓ Gs 2, n ∉ Gs 0 ⊓ Gs 1 ∧
    (∀ u ∈ Gs 0, Nr Gs u → u ∈ Gs 0 ⊓ Gs 1 ∨
      ∃ p ∈ Gs 0 ⊓ Gs 1, ∃ p' ∈ Gs 0 ⊓ Gs 1, u = p * n * p') ∧
    ((Gs 0 ⊓ Gs 1) ⊓ cj n (Gs 0 ⊓ Gs 1)).relIndex (Gs 0 ⊓ Gs 1) = 6 := by
  obtain ⟨n, hn, hnf⟩ := M.exists_P' hD (nn_mem_B b o)
  refine ⟨n, hn, fun h => nn_not_mem_A b o (hnf ▸ (M.f_P hD hn.1).1 h), ?_, ?_⟩
  · intro u hu hNr
    rw [M.nr_iff hD hu, gq_near_iff] at hNr
    rcases hNr with h | ⟨a, ha, a', ha', h⟩
    · exact Or.inl ((M.f_P hD hu).2 h)
    · refine Or.inr ?_
      obtain ⟨p, hp, hpa⟩ := M.exists_P hD ha
      obtain ⟨p', hp', hp'a⟩ := M.exists_P hD ha'
      have hmem : p * n * p' ∈ Gs 0 := (Gs 0).mul_mem ((Gs 0).mul_mem hp.1 hn.1) hp'.1
      have e : M.f u = M.f (p * n * p') := by
        rw [M.f_mul ((Gs 0).mul_mem hp.1 hn.1) hp'.1, M.f_mul hp.1 hn.1, hpa, hnf, hp'a, h]
      obtain ⟨q, hq, huq⟩ := M.eq_mul_ker hu hmem e
      exact ⟨p, hp, p' * q, (Gs 0 ⊓ Gs 1).mul_mem hp' (Q0_le_P01 hD hq), by rw [huq]; group⟩
  · rw [M.relIndex_conj01 hD hn.1 hnf, relIndex_near]

end Mod0

theorem gqLoc (hD : IsDSystem .C3 Gs) : GQLoc Gs := by
  obtain ⟨b, o, ⟨M⟩⟩ := model0_bo hD
  exact ⟨M.idx01 hD, M.idx02 hD, M.core_loc hD, M.gq3_loc hD, M.farT_loc hD, M.farE_loc hD,
    M.nearD_loc hD⟩

end CFSG.Quasithin.H13.I51

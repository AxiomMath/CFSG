module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Lp

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_forall {U : Subgroup G} {y : G} (h : ∀ u ∈ U, y * u * y⁻¹ ∈ U)
    (h' : ∀ u ∈ U, y⁻¹ * u * y⁻¹⁻¹ ∈ U) : y ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => h u hu, fun hu => ?_⟩
  have := h' _ hu
  rwa [inv_inv, show y⁻¹ * (y * u * y⁻¹) * y = u by group] at this

omit [Finite G] in
@[expose] def normClos (β : Geo H M) (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | ∃ g ∈ stab β, ∃ x ∈ X, y = g * x * g⁻¹}

omit [Finite G] in
theorem normClos_le_stab {β : Geo H M} {X : Subgroup G} (hX : X ≤ stab β) :
    normClos β X ≤ stab β := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, x, hx, rfl⟩
  exact (stab β).mul_mem ((stab β).mul_mem hg (hX hx)) ((stab β).inv_mem hg)

omit [Finite G] in
theorem le_normClos {β : Geo H M} {X : Subgroup G} : X ≤ normClos β X := fun x hx =>
  Subgroup.subset_closure ⟨1, (stab β).one_mem, x, hx, by simp⟩

omit [Finite G] in
theorem stab_le_normalizer_normClos {β : Geo H M} {X : Subgroup G} :
    stab β ≤ Subgroup.normalizer (normClos β X : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ h ∈ stab β, ∀ y ∈ normClos β X, h * y * h⁻¹ ∈ normClos β X := by
    intro h hh y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨g, hg, x, hx, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨h * g, (stab β).mul_mem hh hg, x, hx, ?_⟩
      group
    | one => simp
    | mul a b _ _ ha hb =>
      have : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      rw [this]
      exact (normClos β X).mul_mem ha hb
    | inv a _ ha =>
      have : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
      rw [this]
      exact (normClos β X).inv_mem ha
  intro y
  refine ⟨fun hy => key h hh y hy, fun hy => ?_⟩
  have := key h⁻¹ ((stab β).inv_mem hh) _ hy
  rwa [inv_inv, show h⁻¹ * (h * y * h⁻¹) * h = y by group] at this

omit [Finite G] in
theorem normClos_le_normalizer {β : Geo H M} {X U : Subgroup G}
    (hc : ∀ x ∈ X, ∀ w ∈ Wb β, x * w * x⁻¹ * w⁻¹ ∈ Vn β) (hVU : Vn β ≤ U) (hUW : U ≤ Wb β) :
    normClos β X ≤ Subgroup.normalizer (U : Set G) := by
  have gen : ∀ g ∈ stab β, ∀ x ∈ X, ∀ u ∈ U, (g * x * g⁻¹) * u * (g * x * g⁻¹)⁻¹ ∈ U := by
    intro g hg x hx u hu
    have hu' : g⁻¹ * u * g ∈ Wb β := by
      have := (Subgroup.mem_normalizer_iff.mp (Std.Wb_normal β ((stab β).inv_mem hg)) u).mp
        (hUW hu)
      simpa using this
    have h1 := hc x hx _ hu'
    have h2 := Ch.conj_mem_Vn hg h1
    have e : g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ =
        (g * (x * (g⁻¹ * u * g) * x⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹) * u := by group
    rw [e]
    exact U.mul_mem (hVU h2) hu
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, x, hx, rfl⟩
  refine mem_normalizer_of_forall (gen g hg x hx) (fun u hu => ?_)
  have := gen g hg x⁻¹ (X.inv_mem hx) u hu
  have e : (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ := by group
  rw [e]
  simpa [e] using this

theorem end_contra (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) {X : Subgroup G}
    (hXs : X ≤ stab β) (hXQ : ¬ X ≤ Qv β)
    (hc : ∀ x ∈ X, ∀ w ∈ Wb β, x * w * x⁻¹ * w⁻¹ ∈ Vn β) : False := by
  obtain ⟨α, hα⟩ := exists_adj β
  have hα' : α ∈ nbrs β := hα
  have hαβ : β ∈ nbrs α := Std.mem_nbrs_symm.mp hα'
  set U := Wl α with hU
  have hVU : Vn β ≤ U := Std.Vn_le_Wl hαβ
  have hUW : U ≤ Wb β := by
    refine Std.Wl_le fun ρ hρ => ?_
    by_cases h : ρ = β
    · subst h
      exact Std.Vn_le_Wb_self hS hβ
    · exact Std.Vn_le_Wb (Std.dist_eq_two_iff.mpr ⟨α, hα', hρ, h⟩)
  have hUQ : U ≤ Qv β := hUW.trans (Std.Wb_le_Qv hS β)
  have hUs : U ≤ stab α ⊓ stab β :=
    le_inf (hUQ.trans (Std.Qv_le_stab hS hα')) (hUQ.trans (Ch.Qv_le_stab' β))
  have hne : U ≠ ⊥ := fun h => by
    apply F53.Zv_ne_bot hS.glob.amalg β
    rw [eq_bot_iff, ← h]
    exact (S34.Zv_le_Vn hS.glob hβ).trans hVU
  have hCn := normClos_le_normalizer hc hVU hUW
  have hbot : U = ⊥ := by
    refine F53.eq_bot_of_normalizer_transitive_vertex hS.glob.amalg
      (show (graph (H ⊔ M) H M).Adj α β from hαβ) hUs ?_ ?_
    · intro ε hε ε' hε'
      obtain ⟨x, hx, hxε⟩ := stab_transitive_on_nbrs hε hε'
      exact ⟨x, Std.Wl_normal α hx, smul_eq_of_mem_stab hx, hxε⟩
    · intro ε hε ε' hε'
      obtain ⟨c, hcC, hcε⟩ := F53.exists_smul_eq_of_normal_not_le hS.glob.amalg hε hε'
        (normClos_le_stab hXs) stab_le_normalizer_normClos (fun h => hXQ (le_normClos.trans h))
      exact ⟨c, hCn hcC, smul_eq_of_mem_stab (normClos_le_stab hXs hcC), hcε⟩
  exact hne hbot

end S35.Lp

end F53.Stellmacher

end CFSG.Quasithin

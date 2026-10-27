module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChLat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Notation
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Ctx (H M S : Subgroup G) : Prop where
  sit : Sit H M S
  caseI : CaseI H M
  orthZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ)
  hR : ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
    δ ≠ β → δ' ≠ β → δ' ≠ δ →
      Vn β ⊓ Vn δ = Vn β ⊓ Vn δ' ∧ Vn β ⊓ Vn δ = Vn δ ⊓ Vn δ' ∧
        stab l ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G)

namespace Ctx

variable (hC : Ctx H M S)
include hC

theorem nonempty_chart {δ : Geo H M} (hδ : vtype δ = false) : Nonempty (Chart δ) :=
  S35.Ch.nonempty_chart (S34.Zv_le_Vn hC.sit.glob hδ) (hC.orthZ δ hδ)

theorem exists_chart_normalized {δ : Geo H M} (hδ : vtype δ = false) {P : Subgroup G}
    (hP : IsSylowTwoOf P (stab δ)) : ∃ c : Chart δ, (P.subgroupOf (stab δ)).map c.θ = S5Syl :=
  S35.Ch.exists_chart_normalized (S34.Zv_le_Vn hC.sit.glob hδ) (hC.orthZ δ hδ) hP

end Ctx

omit [Finite G] in
theorem stab_inf_smul {δ l : Geo H M} {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab δ) :
    stab δ ⊓ stab (g • l) = conjSub (g : G) (stab δ ⊓ stab l) := by
  have h1 : conjSub (g : G) (stab δ) = stab δ := by
    ext x
    rw [mem_conjSub]
    constructor
    · intro h
      have := (stab δ).mul_mem ((stab δ).mul_mem hg h) ((stab δ).inv_mem hg)
      simpa [mul_assoc] using this
    · intro h
      exact (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).inv_mem hg) h) hg
  rw [stab_smul, conjSub_inf, h1]

theorem norm_S5SylF : ∀ g : Perm (Fin 5), (∀ x ∈ S5SylF, g * x * g⁻¹ ∈ S5SylF) → g ∈ S5SylF := by
  decide +kernel

theorem mem_of_cj_eq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {σ : Perm (Fin 5)}
    (h : cj σ D = D) : σ ∈ D := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have h4 : ∀ x ∈ S5SylF, (g⁻¹ * σ * g) * x * (g⁻¹ * σ * g)⁻¹ ∈ S5SylF := by
    intro x hx
    have hx' : x ∈ S5Syl := (mem_S5Syl_iff x).mpr hx
    have h1 : g * x * g⁻¹ ∈ cj g S5Syl := mem_cj_conj.mpr hx'
    have h2 : σ * (g * x * g⁻¹) * σ⁻¹ ∈ cj σ (cj g S5Syl) := mem_cj_conj.mpr h1
    rw [h, mem_cj] at h2
    have h3 : g⁻¹ * (σ * (g * x * g⁻¹) * σ⁻¹) * g = (g⁻¹ * σ * g) * x * (g⁻¹ * σ * g)⁻¹ := by
      group
    rw [h3] at h2
    exact (mem_S5Syl_iff _).mp h2
  have h5 : g⁻¹ * σ * g ∈ S5Syl := (mem_S5Syl_iff _).mpr (norm_S5SylF _ h4)
  have h6 : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
  rw [h6]
  exact mem_cj_conj.mpr h5

theorem Qv_le_inf' {δ l : Geo H M} (hS : Sit H M S) (hl : l ∈ nbrs δ) :
    Qv δ ≤ stab δ ⊓ stab l := le_inf (Qv_le_stab' δ) (Qv_le_stab hS hl)

namespace Chart

variable {δ : Geo H M} (c : Chart δ)

@[expose] def Dl (l : Geo H M) : Subgroup (Perm (Fin 5)) := c.bar (stab δ ⊓ stab l)

omit [Finite G] in
theorem bar_conjSub {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab δ) {X : Subgroup G} (_hX : X ≤ stab δ) :
    c.bar (conjSub (g : G) X) = cj (c.θ ⟨g, hg⟩) (c.bar X) := by
  ext σ
  rw [mem_cj]
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp h
    have ha' : (g : G)⁻¹ * (a : G) * (g : G) ∈ X := mem_conjSub.mp ha
    have hb : (g : G)⁻¹ * (a : G) * (g : G) ∈ stab δ :=
      (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).inv_mem hg) a.2) hg
    have e : (⟨(g : G)⁻¹ * (a : G) * (g : G), hb⟩ : ↥(stab δ)) =
        (⟨g, hg⟩ : ↥(stab δ))⁻¹ * a * ⟨g, hg⟩ := rfl
    have := c.mem_bar_of_mem ha' hb
    rw [e, map_mul, map_mul, map_inv] at this
    exact this
  · intro h
    obtain ⟨b, hb, hbs⟩ := (c.mem_bar_iff).mp h
    have hbG : (b : G) ∈ stab δ := b.2
    have hc : (g : G) * (b : G) * (g : G)⁻¹ ∈ stab δ :=
      (stab δ).mul_mem ((stab δ).mul_mem hg hbG) ((stab δ).inv_mem hg)
    refine (c.mem_bar_iff).mpr ⟨⟨_, hc⟩, ?_, ?_⟩
    · rw [mem_conjSub]
      simpa [mul_assoc] using hb
    · have : (⟨(g : G) * (b : G) * (g : G)⁻¹, hc⟩ : ↥(stab δ)) = ⟨g, hg⟩ * b * ⟨g, hg⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hbs]
      group

omit [Finite G] in
theorem Dl_smul {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab δ) (l : Geo H M) :
    c.Dl (g • l) = cj (c.θ ⟨g, hg⟩) (c.Dl l) := by
  unfold Dl
  rw [stab_inf_smul hg, c.bar_conjSub hg inf_le_left]

theorem card_Dl (hS : Sit H M S) {l : Geo H M} (hl : l ∈ nbrs δ) : Nat.card (c.Dl l) = 8 :=
  card_image_sylow c.surj (sylow_stab_inf_left hS.glob.amalg hl)

theorem preθ_Dl (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    c.preθ (c.Dl l) = stab δ ⊓ stab l :=
  c.preθ_bar hS hδ inf_le_left (Qv_le_inf' hS hl)

theorem Dl_injOn (hS : Sit H M S) (hδ : vtype δ = false) {l l' : Geo H M} (hl : l ∈ nbrs δ)
    (hl' : l' ∈ nbrs δ) (h : c.Dl l = c.Dl l') : l = l' := by
  obtain ⟨g, hg, hgl⟩ := stab_transitive_on_nbrs hl hl'
  have h1 : c.Dl l' = cj (c.θ ⟨g, hg⟩) (c.Dl l) := by rw [← hgl]; exact c.Dl_smul hg l
  have h2 : cj (c.θ ⟨g, hg⟩) (c.Dl l) = c.Dl l := by rw [← h1, h]
  have h3 := mem_of_cj_eq (c.card_Dl hS hl) h2
  have h4 : (g : G) ∈ c.preθ (c.Dl l) := (c.mem_preθ_iff ⟨g, hg⟩).mpr h3
  rw [c.preθ_Dl hS hδ hl] at h4
  rw [← hgl]
  exact (smul_eq_of_mem_stab h4.2).symm

theorem Dl_surjOn (hS : Sit H M S) (_hδ : vtype δ = false) {D : Subgroup (Perm (Fin 5))}
    (hD : Nat.card D = 8) : ∃ l ∈ nbrs δ, c.Dl l = D := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hμ' : μ ∈ nbrs δ := hμ
  obtain ⟨g1, hg1⟩ := exists_cj hD
  obtain ⟨g0, hg0⟩ := exists_cj (c.card_Dl hS hμ')
  obtain ⟨x, hx⟩ := c.surj (g1 * g0⁻¹)
  have hxG : (x : G) ∈ H ⊔ M := stab_le δ x.2
  refine ⟨(⟨x, hxG⟩ : ↥(H ⊔ M)) • μ, ?_, ?_⟩
  · have hxδ : ((⟨x, hxG⟩ : ↥(H ⊔ M)) : G) ∈ stab δ := x.2
    exact S35.Std.smul_mem_nbrs_of_stab hxδ hμ'
  · rw [c.Dl_smul x.2, hx, hg0, hg1]
    ext τ
    simp only [mem_cj]
    constructor <;> intro h <;> simpa [mul_assoc] using h

end Chart

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin

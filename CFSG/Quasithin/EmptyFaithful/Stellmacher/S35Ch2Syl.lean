module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch2

open S35.Std S35.Fin S35.Ch
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Chart2

variable {δ : Geo H M} (c : Chart2 δ)

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

end Chart2

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin

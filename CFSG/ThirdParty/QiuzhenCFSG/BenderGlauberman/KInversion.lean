module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: `K₁`/`K₂` inversion infrastructure

After the `Hyp11` fidelity repair (`tasks/bg-hyp11-kdata.md`), `K₁` and
`K₂` are supplied by `Hyp11KData` carrying the paper's "largest
`2'`-subgroup of `H` inverted by `tᵢ`" contract:

* containment in `H`,
* odd cardinality,
* pointwise inversion,
* maximality.

This module turns that contract into the small public lemmas used by
`BenderGlauberman.Section3.Lemma36` and the theorem-C infrastructure:
pointwise inversion, the intersections `K = K₁ ⊓ K₂`, containment in `H`,
and oddness of `K` transferred from `K₁`/`K₂`.
-/

noncomputable section

namespace CFSG.BenderGlauberman

universe u

variable {G : Type u} [Group G] [Fintype G]

/-! ## Pointwise inversion from the `Hyp11` contract -/

/-- `t₁` inverts every element of `K₁`, from the K-data contract. -/
public theorem K1_inverted_apply (c : Hyp11 G) [Hyp11KData c]
    (h : IsInvertedBy c.t1 c.K1)
    {x : G} (hx : x ∈ c.K1) :
    c.t1 * x * c.t1⁻¹ = x⁻¹ :=
  h x hx

/-- `t₂` inverts every element of `K₂`, from the K-data contract. -/
public theorem K2_inverted_apply (c : Hyp11 G) [Hyp11KData c]
    (h : IsInvertedBy c.t2 c.K2)
    {x : G} (hx : x ∈ c.K2) :
    c.t2 * x * c.t2⁻¹ = x⁻¹ :=
  h x hx

/-! ## The intersection `K = K₁ ⊓ K₂` -/

/-- `K ≤ K₁`. -/
public theorem K_le_K1 (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.K1 := by
  change c.K1 ⊓ c.K2 ≤ c.K1
  exact inf_le_left

/-- `K ≤ K₂`. -/
public theorem K_le_K2 (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.K2 := by
  change c.K1 ⊓ c.K2 ≤ c.K2
  exact inf_le_right

/-- `K ≤ H`. -/
public theorem K_le_H (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.H := by
  exact le_trans (K_le_K1 c) c.K1_le_H

/-- `K ≤ H` (same statement, under the name used by downstream consumers). -/
public theorem K_in_H (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.H :=
  K_le_H c

/-! ## Oddness of `K` -/

/-- If `K₁` is odd, then `K = K₁ ⊓ K₂` is odd, since `K ≤ K₁`. -/
public theorem K_coprime_of_K1_odd (c : Hyp11 G) [Hyp11KData c]
    (h : Nat.Coprime 2 (Nat.card c.K1)) :
    Nat.Coprime 2 (Nat.card ↥(c.K)) := by
  have hdiv : Nat.card ↥(c.K) ∣ Nat.card ↥(c.K1) :=
    Subgroup.card_dvd_of_le (K_le_K1 c)
  exact h.coprime_dvd_right hdiv

/-- If `K₂` is odd, then `K = K₁ ⊓ K₂` is odd, since `K ≤ K₂`. -/
public theorem K_coprime_of_K2_odd (c : Hyp11 G) [Hyp11KData c]
    (h : Nat.Coprime 2 (Nat.card c.K2)) :
    Nat.Coprime 2 (Nat.card ↥(c.K)) := by
  have hdiv : Nat.card ↥(c.K) ∣ Nat.card ↥(c.K2) :=
    Subgroup.card_dvd_of_le (K_le_K2 c)
  exact h.coprime_dvd_right hdiv

end CFSG.BenderGlauberman

module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanT2
public import CFSG.Quasithin.Vol2.Ch11SecSFactsCartan

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autOn_lOf [Finite G] {L V U : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hU : U ≤ V) : autOn (LOf L U) V = gammaW (autOn L V) (U.subgroupOf V) := by
  rw [autOn_perfectCore (inf_le_left.trans hL), autOn_inf_normalizer hU]

omit [Finite G] in
theorem inv_mul_mem_centralizer {V : Subgroup G} {a x : G}
    {ha : a ∈ Subgroup.normalizer (V : Set G)} {hx : x ∈ Subgroup.normalizer (V : Set G)}
    (h : conjV V a ha = conjV V x hx) : a⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h
  simp only [conjV_apply_coe] at this
  calc v * (a⁻¹ * x) = a⁻¹ * (a * v * a⁻¹) * x := by group
    _ = a⁻¹ * (x * v * x⁻¹) * x := by rw [this]
    _ = a⁻¹ * x * v := by group

omit [Finite G] in
theorem odd_orderOf_of_mem {X : Subgroup G} (hX : Odd (Nat.card ↥X)) {x : G} (hx : x ∈ X) :
    Odd (orderOf x) := by
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : ↥X)
  rw [Subgroup.orderOf_mk] at h
  exact hX.of_dvd_nat h

omit [Finite G] in
theorem le_normalizer_lOf_of_centralizer {L V U : Subgroup G} (hU : U ≤ V) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (LOf L U : Set G) := by
  refine le_trans ?_ (normalizer_le_normalizer_perfectCore _)
  intro c hc
  refine Subgroup.le_normalizer ⟨hc.1, ?_⟩
  show c ∈ Subgroup.normalizer (U : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 u (hU hu)
    have h1 : c * u * c⁻¹ = u := by rw [← hcomm]; group
    rw [h1]
    exact hu
  · intro hu
    have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ (hU hu)
    have h2 : c * u = c * (c * u * c⁻¹) := by rw [← hcomm]; group
    rw [mul_left_cancel h2]
    exact hu

theorem autOn_inf_lOf {L V U X : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hU : U ≤ V) (hXL : X ≤ L) (hX : Odd (Nat.card ↥X))
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))) :
    autOn (X ⊓ LOf L U) V = autOn X V ⊓ gammaW (autOn L V) (U.subgroupOf V) := by
  rw [← autOn_lOf hL hU]
  refine le_antisymm (le_inf (autOn_mono inf_le_left) (autOn_mono inf_le_right)) ?_
  rintro g ⟨hgX, hgU⟩
  obtain ⟨x, hxX, hxV, rfl⟩ := mem_autOn_iff.mp hgX
  obtain ⟨a, haU, haV, hag⟩ := mem_autOn_iff.mp hgU
  have haL : a ∈ L := (perfectCore_le _).trans inf_le_left haU
  have hc : a⁻¹ * x ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨L.mul_mem (L.inv_mem haL) (hXL hxX), inv_mul_mem_centralizer hag.symm⟩
  have hxs : x ∈ LOf L U ⊔ (L ⊓ Subgroup.centralizer (V : Set G)) := by
    have := Subgroup.mul_mem_sup haU hc
    rwa [mul_inv_cancel_left] at this
  have hxU := mem_of_mem_sup_of_odd hC (le_normalizer_lOf_of_centralizer hU) hxs
    (odd_orderOf_of_mem hX hxX)
  exact conjV_mem_autOn (Subgroup.mem_inf.mpr ⟨hxX, hxU⟩) hxV

end CFSG.Quasithin.Vol2.Ch11.SecS

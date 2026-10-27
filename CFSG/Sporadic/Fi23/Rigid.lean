module

public import CFSG.Sporadic.Fi23.Graph
public import CFSG.Fischer.Uniq.RigidTransfer
public import CFSG.Sporadic.Fi22.TauGroup

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Fi22Side

open CFSG.Sporadic.Fi22

theorem conjPerm_mem_lhOrbit
    (g : Fi22.J) {i : Fin 2} {T : Set Fi22.D} (hT : T ∈ lhOrbit i) :
    ⇑(Pair.conjPerm Fi22.pair_D g) '' T ∈ lhOrbit i := by
  obtain ⟨h, rfl⟩ := hT
  refine ⟨g * h, ?_⟩
  rw [Set.image_image]
  apply Set.image_congr
  intro x _
  show (Pair.conjPerm Fi22.pair_D g) ((Pair.conjPerm Fi22.pair_D h) x) =
    (Pair.conjPerm Fi22.pair_D (g * h)) x
  rw [map_mul, Equiv.Perm.mul_apply]

theorem mem_range_innerTau_of_preserves_lhOrbit
    (hFF : Fi22Facts) (σ : tauGroup Fi22.pair_D)
    (hσ : ∀ T ∈ lhOrbit 0, ⇑(σ : Equiv.Perm Fi22.D) '' T ∈ lhOrbit 0) :
    σ ∈ (innerTau Fi22.pair_D).range := by
  have hu1 : ⇑lhU '' lhRoot 0 ∈ lhOrbit 1 := by
    have h := hFF.image_lhU_lhOrbit 0
    have h01 : (0 + 1 : Fin 2) = 1 := rfl
    rw [h01] at h
    rw [← h]
    exact ⟨_, lhRoot_mem_lhOrbit 0, rfl⟩
  exact mem_range_innerTau_of_preserves Fi22.pair_D index_innerTau_range (Set.toFinite _)
    (hFF.lhOrbit_disjoint 0 1 (by decide)) (fun g _ hT => conjPerm_mem_lhOrbit g hT)
    (u := ⟨lhU, fun x y => hFF.lhU_tv x y⟩) (lhRoot_mem_lhOrbit 0) hu1 σ hσ

end Fi22Side

section Stab

variable (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
include hPF hHF hFF

theorem card_stabT_le :
    Nat.card (stabT pair_J d_mem_D23) ≤ 129123503308800 := by
  obtain ⟨L, hL⟩ := exists_localPoints_lhOrbit_zero hPF hHF hFF pair_J (localPoints_D23 hPF)
    d_mem_D23
  have h := coverHyp_lhOrbit_zero hPF hFF pair_J (localPoints_D23 hPF) d_mem_D23 L hL
  have hXi := connected_of_D2 Fi22.xi23Root hFF.xi23_D2
  have hmu : ∀ c ∈ D23, c * d ≠ d * c → (muSet D23 d c).Nonempty := fun c hc hcd =>
    Pair.muSet_nonempty pair_J (connected_D23 hPF) d_mem_D23 hc hcd
  have := Pair.card_stabT_le_of_rigid Fi22.pair_D pair_J d_mem_D23 Fi22.center_eq_bot L h hXi hmu
    (mem_range_innerTau_of_preserves_lhOrbit hFF)
  rw [Fi22.card_J] at this
  omega

theorem tauGroup_D23_eq_range
    (σ : tauGroup pair_J) : σ ∈ (innerTau pair_J).range :=
  Pair.mem_range_innerTau_of_card_stabT pair_J center_J d_mem_D23
    (by rw [card_centralizer_d]; exact card_stabT_le hPF hHF hFF) σ

theorem fi23_complete :
    ∀ φ : MulAut J, ∃ g : J, φ = MulAut.conj g :=
  @complete_of_tauGroup (↥J) inferInstance D23 pair_J pair_eq_D23
    (tauGroup_D23_eq_range hPF hHF hFF)

end Stab

end CFSG.Sporadic.Fi23

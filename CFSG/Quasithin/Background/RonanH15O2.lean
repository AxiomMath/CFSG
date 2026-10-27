module

public import CFSG.Quasithin.Background.HMathieuStatements
import CFSG.Quasithin.Background.HMathieuO2Data

public section

namespace CFSG.Quasithin.RonanH15

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu

private theorem closure_comm_eq_top_of_O2Data {V : Type*} [CommGroup V]
    {L M : Subgroup (MulAut V)} {v : V} {N : ℕ} (hLM : L ≤ M) (h : O2Data L v N) :
    Subgroup.closure {w | ∃ y ∈ M ⊓ centSub (Subgroup.zpowers v), ∃ u : V, w = y u * u⁻¹} = ⊤ := by
  have h1 : perfectCore (stabV L v) ≤ M ⊓ centSub (Subgroup.zpowers v) := by
    intro φ hφ
    obtain ⟨hφL, hφv⟩ := mem_stabV.1 (perfectCore_le (stabV L v) hφ)
    refine ⟨hLM hφL, ?_⟩
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    show φ (v ^ k) = v ^ k
    rw [map_zpow, hφv]
  refine eq_top_iff.2 fun w _ => ?_
  have hw : w ∈ CFSG.Quasithin.H.Mathieu.commV (perfectCore (stabV L v)) := by
    rw [h.2.2.1]
    exact Subgroup.mem_top w
  refine Subgroup.closure_mono ?_ hw
  rintro w ⟨x, hx, u, rfl⟩
  exact ⟨x, h1 hx, u, rfl⟩

theorem closure_comm_eq_top_24
    {V : Type*} [CommGroup V]
    {L M : Subgroup (MulAut V)} (hLM : L ≤ M) (hMC : MathieuCocode24 L ⊤ ⊥) {v : V}
    (hv : IsCocodeO2 L v) :
    Subgroup.closure {w | ∃ y ∈ M ⊓ centSub (Subgroup.zpowers v), ∃ u : V, w = y u * u⁻¹} = ⊤ :=
  closure_comm_eq_top_of_O2Data hLM (o2Data_of_cocode24 hMC hv)

theorem closure_comm_eq_top_23
    {V : Type*} [CommGroup V]
    {L M : Subgroup (MulAut V)} (hLM : L ≤ M) (hMC : MathieuCocode23 L ⊤ ⊥) {v : V}
    (hv : IsCocodeO2 L v) :
    Subgroup.closure {w | ∃ y ∈ M ⊓ centSub (Subgroup.zpowers v), ∃ u : V, w = y u * u⁻¹} = ⊤ :=
  closure_comm_eq_top_of_O2Data hLM (o2Data_of_cocode23 hMC hv)

theorem closure_comm_eq_top_22
    {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)} (hLM : L ≤ M)
    (hMC : MathieuCocode22 L ⊤ ⊥) {v : V} (hv : IsCocodeO2 L v) :
    Subgroup.closure {w | ∃ y ∈ M ⊓ centSub (Subgroup.zpowers v), ∃ u : V, w = y u * u⁻¹} = ⊤ :=
  closure_comm_eq_top_of_O2Data hLM (o2Data_of_cocode22 hMC hv)

end CFSG.Quasithin.RonanH15

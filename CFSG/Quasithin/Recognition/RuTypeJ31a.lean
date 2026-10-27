module

public import CFSG.Quasithin.Recognition.RuTypeJ29f

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

omit [Finite G] in
theorem mul_self_of_isConj_z {u : G} (hu : IsConj M.z u) : u * u = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hu
  have hz : M.z * M.z = 1 := by rw [← pow_two]; exact M.z_sq
  calc g * M.z * g⁻¹ * (g * M.z * g⁻¹) = g * (M.z * M.z) * g⁻¹ := by group
    _ = 1 := by rw [hz]; group

theorem lemma_J32
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {u v : G} (hu : IsConj M.z u)
    (hv : IsConj M.z v) (huv : u * v = v * u) (h1 : u * v ≠ 1) : IsConj M.z (u * v) := by
  have hu2 := M.mul_self_of_isConj_z hu
  have hv2 := M.mul_self_of_isConj_z hv
  have h2 : (u * v) ^ 2 = 1 := by
    calc (u * v) ^ 2 = u * (v * u) * v := by rw [pow_two]; group
      _ = u * (u * v) * v := by rw [huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, one_mul]
  rcases (M.lemma_J27_4 hs hs1).2 _ h2 h1 with h | h
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    have hs' : s = (g⁻¹ * u * g) * (g⁻¹ * v * g) := by
      calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = g⁻¹ * (u * v) * g := by rw [hg]
        _ = (g⁻¹ * u * g) * (g⁻¹ * v * g) := by group
    have hu' : IsConj M.z (g⁻¹ * u * g) := hu.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    have hv' : IsConj M.z (g⁻¹ * v * g) := hv.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    have hcomm : (g⁻¹ * u * g) * (g⁻¹ * v * g) = (g⁻¹ * v * g) * (g⁻¹ * u * g) := by
      calc (g⁻¹ * u * g) * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g := by group
        _ = g⁻¹ * (v * u) * g := by rw [huv]
        _ = (g⁻¹ * v * g) * (g⁻¹ * u * g) := by group
    have hu2' := M.mul_self_of_isConj_z hu'
    have hv2' := M.mul_self_of_isConj_z hv'
    have huC : g⁻¹ * u * g ∈ Cen s := by
      rw [mem_Cen, hs']
      calc g⁻¹ * u * g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) =
          ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * (g⁻¹ * v * g) := by group
        _ = (g⁻¹ * v * g) * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) := by rw [hu2', one_mul, mul_one]
        _ = (g⁻¹ * u * g) * (g⁻¹ * v * g) * (g⁻¹ * u * g) := by
          rw [← mul_assoc, ← hcomm]
    have hvC : g⁻¹ * v * g ∈ Cen s := by
      rw [mem_Cen, hs']
      calc g⁻¹ * v * g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) =
          g⁻¹ * v * g * ((g⁻¹ * v * g) * (g⁻¹ * u * g)) := by rw [hcomm]
        _ = ((g⁻¹ * v * g) * (g⁻¹ * v * g)) * (g⁻¹ * u * g) := by group
        _ = (g⁻¹ * u * g) * ((g⁻¹ * v * g) * (g⁻¹ * v * g)) := by rw [hv2', one_mul, mul_one]
        _ = (g⁻¹ * u * g) * (g⁻¹ * v * g) * (g⁻¹ * v * g) := by group
    have huL := ((M.isConj_z_iff hs hs1 huC).mp hu').1
    have hvL := ((M.isConj_z_iff hs hs1 hvC).mp hv').1
    have hsL : (g⁻¹ * u * g) * (g⁻¹ * v * g) ∈ Ls s := mul_mem huL hvL
    rw [← hs'] at hsL
    exact hs1 (M.S0_inf_Ls hs hs1 hs hsL)

theorem mem_S1_iff_comm_z
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {x : G} (hx : x ∈ Ls s) :
    x * M.z = M.z * x ↔ x ∈ M.S1 := by
  refine ⟨fun h => M.mem_S1_of_comm_V hs hs1 M.z_mem_V M.z_ne_one hx h, fun h => ?_⟩
  exact M.V_comm_S M.z_mem_V (M.S1_le_S h)

theorem lemma_J33
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    Nat.card {u : G // IsConj M.z u ∧ u * s = s * u} = 455 ∧
      Nat.card {u : G // u ∈ Ls s ∧ u ^ 2 = 1 ∧ u ≠ 1} = 455 := by
  let _ : MulAction (Ls s) G := MulAction.compHom G ((MulAut.conj).comp (Ls s).subtype)
  have hsmul : ∀ (l : Ls s) (x : G), l • x = (l : G) * x * (l : G)⁻¹ := fun _ _ => rfl
  have hzL : M.z ∈ Ls s := M.S1_le_Ls hs hs1 (M.V_le_S1 M.z_mem_V)
  have horb : MulAction.orbit (Ls s) M.z = {u : G | IsConj M.z u ∧ u * s = s * u} := by
    ext u
    simp only [MulAction.mem_orbit_iff, hsmul]
    show _ ↔ IsConj M.z u ∧ u * s = s * u
    constructor
    · rintro ⟨l, rfl⟩
      refine ⟨isConj_iff.mpr ⟨l, rfl⟩, ?_⟩
      have hC : (l : G) * M.z * (l : G)⁻¹ ∈ Cen s :=
        Ls_le_Cen s (mul_mem (mul_mem l.2 hzL) (inv_mem l.2))
      exact mem_Cen.mp hC
    · rintro ⟨hzu, hus⟩
      obtain ⟨l, hl, rfl⟩ := M.exists_Ls_conj_z hs hs1 hzu hus
      exact ⟨⟨l, hl⟩, rfl⟩
  have hstab : MulAction.stabilizer (Ls s) M.z = M.S1.subgroupOf (Ls s) := by
    ext l
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      ← M.mem_S1_iff_comm_z hs hs1 l.2]
    constructor
    · intro h
      calc (l : G) * M.z = ((l : G) * M.z * (l : G)⁻¹) * l := by group
        _ = M.z * l := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have hS1L : M.S1 ≤ Ls s := M.S1_le_Ls hs hs1
  have hcard : Nat.card (MulAction.orbit (Ls s) M.z) = 455 := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (Ls s) M.z), hstab]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.S1.subgroupOf (Ls s))
    rw [M.card_Ls hs hs1, card_subgroupOf_of_le hS1L, M.card_S1] at h
    omega
  have h1 : Nat.card {u : G // IsConj M.z u ∧ u * s = s * u} = 455 := by
    rw [← hcard, horb]
    rfl
  refine ⟨h1, ?_⟩
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  constructor
  · rintro ⟨huL, hu2, hu1⟩
    have huC : u ∈ Cen s := Ls_le_Cen s huL
    exact ⟨(M.isConj_z_iff hs hs1 huC).mpr ⟨huL, hu2, hu1⟩, mem_Cen.mp huC⟩
  · rintro ⟨hzu, hus⟩
    exact (M.isConj_z_iff hs hs1 (mem_Cen.mpr hus)).mp hzu

end RuDataM

end CFSG.Quasithin.RuType

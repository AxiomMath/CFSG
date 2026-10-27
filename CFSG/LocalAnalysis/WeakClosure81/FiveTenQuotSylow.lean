module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenSylow
public import CFSG.LocalAnalysis.WeakClosure81.FiveKer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_normalizer_weakClosure_sup {H M T : Subgroup G} {Ω : Set (Subgroup G)}
    (h : FiveTenHyp H M T Ω) {x : G} (hxH : x ∈ H)
    (hx : x ∈ normalizer ((E1.weakClosure T Ω ⊔ kerMOf M H : Subgroup G) : Set G)) : x ∈ M := by
  have hJM : kerMOf M H ≤ M := kerMOf_le_left M H
  have hJH : kerMOf M H ≤ H := kerMOf_le_group M H
  have hTM : T ≤ M := h.le_M
  have hTH : T ≤ H := h.sylow.le
  have hTJM : T ⊔ kerMOf M H ≤ M := sup_le hTM hJM
  have hTJH : T ⊔ kerMOf M H ≤ H := sup_le hTH hJH
  have hWT : E1.weakClosure T Ω ≤ T := E1.weakClosure_le
  have hTsyl : IsSylowIn 2 T (T ⊔ kerMOf M H) :=
    E1.isSylowIn_two_iff.2 (B6.isSylowTwoOf_mono (E1.isSylowIn_two_iff.1 h.sylow)
      le_sup_left hTJH)
  have hxW : A1b.conjSub x (E1.weakClosure T Ω) ≤ T ⊔ kerMOf M H := by
    intro y hy
    rw [A1b.mem_conjSub_iff] at hy
    have h1 : x * (x⁻¹ * y * x) * x⁻¹ ∈ (E1.weakClosure T Ω ⊔ kerMOf M H : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.1 hx _).1 (Subgroup.mem_sup_left hy)
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [e] at h1
    exact sup_le_sup_right hWT _ h1
  have hW2 : IsPGroup 2 (A1b.conjSub x (E1.weakClosure T Ω)) :=
    (h.sylow.isPGroup.to_le hWT).map _
  obtain ⟨m, hm, hmW⟩ := exists_conjSub_le_of_isSylowIn hTsyl le_sup_left hW2 hxW hxW
  have hmJ : m ∈ T ⊔ kerMOf M H := (Subgroup.mem_inf.1 hm).1
  have hmH : m ∈ H := hTJH hmJ
  have hmM : m ∈ M := hTJM hmJ
  have hmx : m * x ∈ normalizer (E1.weakClosure T Ω : Set G) := by
    refine mem_normalizer_weakClosure_of_isInvColl h.invColl (H.mul_mem hmH hxH) ?_
    intro w hw
    have h1 : (m * x) * w * (m * x)⁻¹ ∈ A1b.conjSub (m * x) (E1.weakClosure T Ω) :=
      A1b.mem_conjSub_of_mem hw
    rw [A1b.conjSub_mul] at h1
    exact hmW h1
  have hmxM : m * x ∈ M := h.normalizer_le ⟨H.mul_mem hmH hxH, hmx⟩
  have : x = m⁻¹ * (m * x) := by group
  rw [this]
  exact M.mul_mem (M.inv_mem hmM) hmxM

end CFSG.LocalAnalysis.WeakClosure81

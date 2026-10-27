module

public import CFSG.LocalAnalysis.WeakClosure81.EightFourteen
public import CFSG.LocalAnalysis.WeakClosure81.EightNVBasic
public import CFSG.LocalAnalysis.WeakClosure81.EightNVOmega
public import CFSG.LocalAnalysis.WeakClosure81.EightNineAS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem le_normalizer_inf_of_le {T H C : Subgroup G} (hTH : T ≤ H)
    (hHC : H ≤ normalizer (C : Set G)) : T ≤ normalizer ((T ⊓ C : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hT : y ∈ T ↔ t * y * t⁻¹ ∈ T :=
    ⟨fun hy => T.mul_mem (T.mul_mem ht hy) (T.inv_mem ht), fun hy => by
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hy) ht
      simpa [mul_assoc] using this⟩
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hT, (Subgroup.mem_normalizer_iff.mp (hHC (hTH ht)) y)]

theorem Sit813.inf_cGrp_le_pCoreOf_AS (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    T ⊓ cGrp H T ≤ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := h.minCex.hyp
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.calH0.1 hyp.sylow
  have hCH : cGrp H T ≤ H := h.concl813.comp.2.1.trans h.concl813.comp.2.2.1
  have hCnorm : ((cGrp H T).subgroupOf H).Normal := h.concl813.comp.1
  have hHC : H ≤ normalizer (cGrp H T : Set G) := h.le_normalizer_cGrp
  have hP : IsSylowIn 2 (T ⊓ cGrp H T) (cGrp H T) := h.isSylowIn_inf_cGrp
  have hTP : T ≤ normalizer ((T ⊓ cGrp H T : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le hTH.le hHC
  have hX : H ≤ normalizer ((T ⊓ cGrp H T : Subgroup G) : Set G) := by
    by_contra hnot
    set X : Subgroup G := H ⊓ normalizer ((T ⊓ cGrp H T : Subgroup G) : Set G) with hXdef
    have hXH : X < H := lt_of_le_of_ne inf_le_left fun heq => hnot (heq.symm.le.trans inf_le_right)
    obtain ⟨Y, hY, hXY⟩ := exists_mem_calNIn_of_lt (le_inf hTH.le hTP) hXH
    rw [h.minCex.calNIn_eq_AS h5_11 h5_13, Set.mem_singleton_iff] at hY
    have hXM : X ≤ normalizer (V : Set G) := hXY.trans (hY.le.trans inf_le_right)
    apply hyp.notLe
    intro x hx
    obtain ⟨k, hk, n, hn, rfl⟩ := frattini_argument hCH hCnorm hP hx
    exact (normalizer (V : Set G)).mul_mem (h.cGrp_le_normalizer hk) (hXM hn)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (inf_le_left.trans hTH.le) hX (hTH.isPGroup.to_le inf_le_left)

theorem w3GapNV1_holds_AS (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) : W3GapNV1 G := by
  intro V H T A L K i h n hn
  obtain ⟨s, hs, c, hc, rfl⟩ := h.exists_mul_eq_of_mem_oTwoMod hn
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.calH0.1 h.minCex.hyp.sylow
  have hCZ := cGrp_le_centralizer_omegaOneCenterOf_pCoreOf hTH h.eGrp_le_omegaOneCenterOf
    (h.inf_cGrp_le_pCoreOf_AS h5_11 h5_13)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨hsT, hsN⟩ := Subgroup.mem_inf.mp hs
  have hsS : s ∈ sGrp H T A K :=
    (le_sup_left : rGrp H T K ≤ sGrp H T A K) (h.mem_rGrp_of_mem_oTwoMod hsN hsT)
  have hsv : s * v = v * s := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 s hsS
  have hvc : v * c = c * v :=
    Subgroup.mem_centralizer_iff.mp (hCZ hc) v (h.v1Grp_le_omegaOneCenterOf_pCoreOf hv)
  calc v * (s * c) = (v * s) * c := by group
    _ = (s * v) * c := by rw [hsv]
    _ = s * (v * c) := by group
    _ = s * (c * v) := by rw [hvc]
    _ = (s * c) * v := by group

theorem w3In814_of_inputs_AS (h122one : W3Lem122One) (h122two : W3Lem122Two)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) : W3In814 G :=
  ⟨h122one, h122two, w3GapNV1_holds_AS h5_11 h5_13⟩

end CFSG.LocalAnalysis.WeakClosure81

end

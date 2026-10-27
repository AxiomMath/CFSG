module

public import CFSG.RankThree.GF2n.Stroth80.KSSec93Grp
import CFSG.RankThree.GF2n.Stroth80.KSSec93Mod
import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
import CFSG.RankThree.GF2n.Stroth80.Sec711Step3
public import CFSG.RankThree.GF2n.Stroth80.Sec91

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace KS93

variable {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {s z : G}

namespace Hyp

variable (H : Hyp hc n t r Z0 s z)
include H

theorem shift : Hyp hc n t r Z0 s (r⁻¹ * z) := by
  have hrR : r ∈ Rt M (LB M Q B) t := H.hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have e : ∀ y : G, ⁅(r⁻¹ * z) * s * (r⁻¹ * z)⁻¹, y⁆ =
      r⁻¹ * ⁅z * s * z⁻¹, r * y * r⁻¹⁆ * r⁻¹⁻¹ := fun y => by
    simp only [commutatorElement_def]
    group
  refine ⟨H.hs, H.hr, H.hZ0, H.hsc, ⟨H.s_mem, M.mul_mem (M.inv_mem hrM) H.z_mem, ?_, ?_⟩, H.h1,
    ?_, H.h3, H.hC⟩
  · intro y hy
    rw [e]
    exact n12l3_normalizes_Q hc (M.inv_mem hrM) (H.hT1.comm _ (H.conj_mem_Z0 hrR hy))
  · intro h
    apply H.hT1.not_mem
    have h' := H.conj_mem_Z0 hrR h
    rwa [show r * ((r⁻¹ * z) * s * (r⁻¹ * z)⁻¹) * r⁻¹ = z * s * z⁻¹ by group] at h'
  · intro v hv
    have hrv : r * v * r⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt H.t_mem hrR) v).mp hv
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hrM)) _).mp (H.h2 _ hrv)

theorem conj_le_inter (h34 : Stroth34Statement) :
    conjSubgroup z (Vt M (LB M Q B) B Z t) ≤
      QB (conjSubgroup r B) ⊓ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
  obtain ⟨hQD, hW⟩ := H.le_QB_and_conj_le_Wt h34
  have hQD' := (H.shift.le_QB_and_conj_le_Wt h34).1
  have hWdef : Wt Q (Vt M (LB M Q B) B Z t) =
      Q ⊓ Subgroup.centralizer (Vt M (LB M Q B) B Z t : Set G) := rfl
  refine le_inf (le_inf ?_ ?_) ?_
  · have h := conjSubgroup_mono (g := z) hQD'
    rwa [← QB_conj, ← conjSubgroup_mul, show z * (r⁻¹ * z)⁻¹ = r by group] at h
  · have h := conjSubgroup_mono (g := z) hQD
    rwa [← QB_conj, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one] at h
  · intro y hy
    rw [mem_conjSubgroup] at hy
    rw [hWdef]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := n12l3_normalizes_Q hc H.z_mem (hc.Vt_le_Q t hy)
      rwa [show z * (z⁻¹ * y * z) * z⁻¹ = y by group] at h
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : z⁻¹ * v * z ∈ conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t) := by
        rw [mem_conjSubgroup, inv_inv, show z * (z⁻¹ * v * z) * z⁻¹ = v by group]
        exact hv
      have hvW := hW hv'
      rw [hWdef] at hvW
      have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hvW).2 _ hy
      calc v * y = z * ((z⁻¹ * v * z) * (z⁻¹ * y * z)) * z⁻¹ := by group
        _ = z * ((z⁻¹ * y * z) * (z⁻¹ * v * z)) * z⁻¹ := by rw [h]
        _ = y * v := by group

theorem inconsistent (h34 : Stroth34Statement) : False := by
  have hle := Subgroup.card_le_of_le (H.conj_le_inter h34)
  rw [card_conjSubgroup, H.hs.card_V] at hle
  have hI := step91Inter_of h34 G M Q Z B hc n t H.hs r H.hr _ _ rfl rfl
  have hq : 4 ≤ Nat.card Z := hc.hyp.q4
  have h53 : Nat.card Z ^ 3 < Nat.card Z ^ 5 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  exact (not_le.mpr h53) (hle.trans hI)

end Hyp

end KS93

theorem step93Four_of (h34 : Stroth34Statement) (hCentre : Step95CentreStatement) :
    Step93FourStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 hsc s z hT1 h1 h2 h3
  exact (KS93.Hyp.inconsistent
    ⟨hs, hr, hZ0, hsc, hT1, h1, h2, h3, hCentre G M Q Z B hc n t hs Z0 hZ0⟩ h34).elim

theorem step93End_of_claims (h34 : Stroth34Statement) (hCentre : Step95CentreStatement)
    (hOne : Step93OneStatement) (hVan : Step93VanishStatement) (hTI : Step93TIStatement) :
    Step93EndStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 hsc s z hT1 _
  exact KS93.Hyp.inconsistent ⟨hs, hr, hZ0, hsc, hT1, hOne G M Q Z B hc n t hs r hr Z0 hZ0 hsc,
    hVan G M Q Z B hc n t hs r hr Z0 hZ0 hsc s z hT1, hTI G M Q Z B hc n t hs r hr Z0 hZ0 hsc,
    hCentre G M Q Z B hc n t hs Z0 hZ0⟩ h34

end CFSG.RankThree.GF2n.Stroth80

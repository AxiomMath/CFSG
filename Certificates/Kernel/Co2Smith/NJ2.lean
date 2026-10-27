module

public import Certificates.Kernel.Co2Smith.NJ1
public import Certificates.Kernel.Co2Smith.NJFix
public import Certificates.Kernel.Co2Smith.NJ2K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith CFSG.KC.Enum
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch.Co2M
open CFSG.Sporadic.Co2Cert CFSG.KS.Co2M

theorem jt_eq {m : Nat} (hm : m < 1024) (v : Nat) : colActT glNJJT[m]! v = jtK m v := by
  unfold glNJJT
  rw [getElem!_pos _ m (by simp [hm]), Array.getElem_ofFn]
  simp only
  rw [colActT, jc_eq, tr_sound (Nat.beq_refl _), CFSG.KC.F2W.vecMulN_unpackR]
  rfl

theorem permR_eq (R : Array Nat) : glNJPermR R = glPermArr R := rfl

theorem nj2_ok : glNJ2OK = true := by
  have hA := njPtA_k
  have hB := njPtB_k
  have hC := njPtC_k
  have hO := njO77_k
  unfold njPtAK at hA
  unfold njPtBK at hB
  unfold njPtCK at hC
  unfold njO77K at hO
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hA hB hC hO
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hBs, hB⟩ := hB
  obtain ⟨⟨⟨hCl, hC1⟩, hCs⟩, hC2⟩ := hC
  obtain ⟨⟨⟨⟨hO1, hO2⟩, hOs1⟩, hOs2⟩, hO3⟩ := hO
  have hvp : co2PackedVecs[1]! = vpK := V_get (by decide)
  unfold glNJ2OK glNJPtOK glNJO77OK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨fun k hk => ?_, fun m hm => ?_⟩, hBs⟩, fun x hx => ?_⟩, hCl⟩, fun x hx => ?_⟩,
    hCs⟩, ?_⟩, ?_⟩
  · rw [njG_eq hk, glMaps_unpack _ (by decide) (by decide)]
    exact hA1 k hk
  · rcases hA2 m hm with h | h
    · exact Or.inl h
    · right
      rw [hvp, jt_eq hm]
      exact h
  · obtain ⟨hJ, hr⟩ := hB x hx
    refine ⟨hJ, ?_⟩
    rw [hvp, jt_eq hJ, V_get hx, jt_eq hJ]
    exact hr
  · obtain ⟨hx2, he⟩ := hC1 x hx
    have hJ := (hB x hx2).1
    refine ⟨hx2, ?_⟩
    rw [hvp, jt_eq hJ, V_get hx2]
    exact he
  · have hm : (glNJBasis.toArray.map fun x => co2PackedVecs[x]!) =
        glNJBasis.toArray.map fun x => VG (PV 0) x := by
      apply Array.map_congr_left
      intro x hx
      exact V_get (hC1 x (by simpa using hx)).1
    rw [hm]
    exact hC2
  · refine ⟨⟨⟨⟨hO1, fun k hk => ?_⟩, hOs1⟩, hOs2⟩, fun m hm => ?_⟩
    · have hb := CFSG.KS.allN_spec njBind_k k hk
      have hR : glNJGt k = unpackR 22 (mulV (jcK glNJTw[k]!) (njGK k)) := by
        rw [glNJGt, jc_eq, njG_eq hk, mulRows_unpack]
      have hp := permOK_of hb
      simp only [permR_eq, hR]
      rw [permArr_eq hb] at hp ⊢
      refine ⟨hp, fun x hx => ?_⟩
      rw [unpack12 (hO1 x hx)]
      exact hO2 k hk x hx
    · rcases hO3 m hm with h | h
      · exact Or.inl h
      · right
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
        have hx : glNJO77Wx[m]! < 2300 := hO1 _ (List.elem_iff.1 h1)
        rw [jt_eq hm, V_get hx, V_get h2]
        exact h4

end CertificateChecks.KernelCo2Smith

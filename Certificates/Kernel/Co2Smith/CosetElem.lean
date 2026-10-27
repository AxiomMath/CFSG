module

public import Certificates.Kernel.Co2Smith.Root
public import Certificates.Kernel.Co2Smith.CosetElemK
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co2Smith.GlCosetInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem cosetElem_ok : glCosetElemOK = true := by
  have hK := cosetElem_k
  obtain ⟨-, -, -, -, -, -, e34, e0⟩ := frame_eqs
  obtain ⟨-, -, -, -, e43, -, -, -⟩ := frame_eqs
  have eB : glB3 = unpackR 22 b3K := by rw [glB3, e34, e43, mulRows_unpack]; rfl
  have eV : glV = unpackR 22 vK := by rw [glV, el_eqs.2.2.2, e0, mulRows_unpack, mulRows_unpack]; rfl
  have eV1 : glV1 = unpackR 22 v1K := by
    rw [glV1, eB, eV, mulRows_unpack, mulRows_unpack, mulRows_unpack]; rfl
  have e14 : glRows[14]! = unpackR 22 (LP 14) := glRows_get (by decide)
  unfold cosetElemK at hK
  unfold glCosetElemOK
  simp only [Bool.and_eq_true, List.all_eq_true] at hK ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hK
  have hm := fun A x y (hx : x < 2300) (hy : y < 2300) => glMaps_unpack A hx hy
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, h11⟩, fun w hw => ?_⟩, ?_⟩
  · rw [glZ_eq, hm _ _ _ (by decide) (by decide)]; exact h1
  · rw [e14, hm _ _ _ (by decide) (by decide)]; exact h2
  · rw [e14, hm _ _ _ (by decide) (by decide)]; exact h3
  · rw [e0, hm _ _ _ (by decide) (by decide)]; exact h4
  · rw [eB, hm _ _ _ (by decide) (by decide)]; exact h5
  · rw [eB, hm _ _ _ (by decide) (by decide)]; exact h6
  · rw [eB, hm _ _ _ (by decide) (by decide)]; exact h7
  · rw [el_eqs.2.2.2, hm _ _ _ (by decide) (by decide)]; exact h8
  · rw [e0, hm _ _ _ (by decide) (by decide)]; exact h9
  · rw [eV1, glZ_eq, mulRows_unpack, hm _ _ _ (by decide) (by decide)]; exact h10
  · obtain ⟨⟨hl, ha⟩, hb⟩ := h12 w hw
    have hl' : ∀ k ∈ w, k < 22 := fun k hk => of_decide_eq_true (hl k hk)
    rw [glR_eq hl', hm _ _ _ (by decide) (by decide), hm _ _ _ (by decide) (by decide)]
    exact ⟨ha, hb⟩
  · have hl : ∀ k ∈ glM2Words[0]!, k < 22 := by decide
    rw [glR_eq hl, hm _ _ _ (by decide) (by decide)]; exact h13

end CertificateChecks.KernelCo2Smith

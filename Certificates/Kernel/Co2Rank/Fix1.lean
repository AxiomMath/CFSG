module

public import CFSG.Sporadic.Co2Cert.Data
public import CFSG.Sporadic.Co2InvData

public section

namespace CertificateChecks.KernelCo2Rank

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Inv CFSG.Sporadic.SmallF2.Native

theorem fix1 : (List.range 2300).countP (fun i =>
    vecMulN 22 (transposeRows 22 co2InvReps[1]!) co2PackedVecs[i]! == co2PackedVecs[i]!) = 140 := by
  have key : ∀ (a : Array ℕ) (p : ℕ → Bool),
      (List.range a.size).countP (fun i => p a[i]!) = a.toList.countP p := by
    intro a p
    have e : (List.range a.size).map (fun i => a[i]!) = a.toList := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      exact getElem!_pos a i (by simpa using h1)
    rw [← e, List.countP_map]
    rfl
  have hs : co2PackedVecs.size = 2300 := by decide +kernel
  have h := key co2PackedVecs fun v => vecMulN 22 (transposeRows 22 co2InvReps[1]!) v == v
  rw [hs] at h
  rw [h]
  decide +kernel

end CertificateChecks.KernelCo2Rank

end

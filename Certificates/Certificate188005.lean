module

public import Certificates.Data.HuppertU38F.Data
import CFSG.Certificates.Kernel.U38NSound
import CFSG.Certificates.Kernel.HeisWordsSound
import Certificates.Kernel.Heis.C188005

public section

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.HeisWords HuppertU38F

namespace Certificates

open CertificateChecks

open HuppertU38F CFSG.LieType.SeitzGeneration.HeisSmall in
theorem certificate188005 : u38Check outerLetters8 words2_8 u38Table = true := by
  have hw : words2_8 = decodeL KernelHeis.W8.chars := by
    rw [KernelHeis.W8.eq, decodeWords_ofList]
  have hS : wordsS = decodeL KernelHeis.WS.chars := by
    rw [KernelHeis.WS.eq, decodeWords_ofList]
  have hC : wordsCw = decodeL KernelHeis.WC.chars := by
    rw [KernelHeis.WC.eq, decodeWords_ofList]
  have hm : ∀ L : List (List ℕ), L.map mat8 = (L.map matN).map (FK.toL fk8 GF8.ofNat') :=
    fun L => by
      rw [List.map_map]
      rfl
  have hl : outerLetters8 =
      words1_8.map (evalW (rawGens8.map fun l => FK.toL fk8 GF8.ofNat' (matN l))) := rfl
  have hL : outerLetters8 = KernelHeis.letters188005.map (FK.toL fk8 GF8.ofNat') := by
    rw [outerLetters8, gens8, hm, FK.evalsN_toL fk8_sound]
    rfl
  have ht : u38Table = KernelHeis.rows188005.map fun r =>
      (⟨FK.toL fk8 GF8.ofNat' (matN r.1), r.2.1.map (FK.toL fk8 GF8.ofNat'), r.2.2⟩ : U38Entry) := by
    rw [u38Table, KernelHeis.rows188005, hS, hC, hm, hm, hL]
    rfl
  have ho : FK.dec fk8 GF8.ofNat' 8 = w0 := by
    ext <;> rfl
  rw [hw, hl, ht]
  exact FK.u38N_sound fk8_sound ho rawGens8 words1_8 _ KernelHeis.rows188005 KernelHeis.u38_k

end Certificates

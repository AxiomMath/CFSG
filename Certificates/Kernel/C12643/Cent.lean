module

public import Certificates.Kernel.C12643.CentB0
public import Certificates.Kernel.C12643.CentB1
public import Certificates.Kernel.C12643.CentB2
public import Certificates.Kernel.C12643.CentB3
public import Certificates.Kernel.C12643.CentB4
public import Certificates.Kernel.C12643.CentB5
public import Certificates.Kernel.C12643.CentB6
public import Certificates.Kernel.C12643.CentB7
public import Certificates.Kernel.Misc.Perm.J2Cent
public import CFSG.Certificates.Kernel.J2CentSound
public import CFSG.Certificates.Kernel.J2Enum.Group
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC12643

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.J2Enum CFSG.KC.J2Cent CFSG.KC.Child3
open CertificateChecks.KernelJ2Cover CFSG.ComponentClassification.J2Cover
open CertificateChecks.KernelMisc.J2Cent (sumF_congr kL0 k20 chainPA)

theorem allC5 : ∀ a < 315, fC5 a = true := by
  intro a ha
  have c0 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c12643B0.all
  have c1 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c12643B1.all
  have c2 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c12643B2.all
  have c3 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c12643B3.all
  simp only [fC50, fC51, fC52, fC53, Nat.add_eq] at c0 c1 c2 c3
  rcases Nat.lt_or_ge a 80 with h0 | h0
  · exact c0 a h0
  rcases Nat.lt_or_ge a 160 with h1 | h1
  · have := c1 (a - 80) (by omega)
    rwa [Nat.add_sub_cancel' h0] at this
  rcases Nat.lt_or_ge a 240 with h2 | h2
  · have := c2 (a - 160) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  · have := c3 (a - 240) (by omega)
    rwa [Nat.add_sub_cancel' h2] at this

theorem allC7 : ∀ a < 315, fC7 a = true := by
  intro a ha
  have c0 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c12643B4.all
  have c1 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c12643B5.all
  have c2 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c12643B6.all
  have c3 := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c12643B7.all
  simp only [fC70, fC71, fC72, fC73, Nat.add_eq] at c0 c1 c2 c3
  rcases Nat.lt_or_ge a 80 with h0 | h0
  · exact c0 a h0
  rcases Nat.lt_or_ge a 160 with h1 | h1
  · have := c1 (a - 80) (by omega)
    rwa [Nat.add_sub_cancel' h0] at this
  rcases Nat.lt_or_ge a 240 with h2 | h2
  · have := c2 (a - 160) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  · have := c3 (a - 240) (by omega)
    rwa [Nat.add_sub_cancel' h2] at this

theorem sumC5 : sumF (rcnt (PA.LR 0)) (blkCent 315 9 PA.LR PA.TR PA.BP X5A X5C) =
    sumF 315 (fun a => lget CT5 (blkKey 315 9 PA.LR PA.TR PA.BP a)) := by
  rw [kL0]
  exact sumF_congr 315 fun a ha => Nat.eq_of_beq_eq_true (allC5 a ha)

theorem sumC7 : sumF (rcnt (PA.LR 0)) (blkCent 315 9 PA.LR PA.TR PA.BP X7 E1) =
    sumF 315 (fun a => lget CT7 (blkKey 315 9 PA.LR PA.TR PA.BP a)) := by
  rw [kL0]
  exact sumF_congr 315 fun a ha => Nat.eq_of_beq_eq_true (allC7 a ha)

theorem k5a : Nat.beq (fld20 (sumF 315 (fun a => lget CT5 (blkKey 315 9 PA.LR PA.TR PA.BP a))) 0)
    300 = true := by quickRfl

theorem k5c : Nat.beq (fld20 (sumF 315 (fun a => lget CT5 (blkKey 315 9 PA.LR PA.TR PA.BP a))) 1)
    50 = true := by quickRfl

theorem k7 : Nat.beq (fld20 (sumF 315 (fun a => lget CT7 (blkKey 315 9 PA.LR PA.TR PA.BP a))) 0)
    7 = true := by quickRfl

theorem ke1 : Nat.beq (fld20 (sumF 315 (fun a => lget CT7 (blkKey 315 9 PA.LR PA.TR PA.BP a))) 1)
    240 = true := by quickRfl

theorem memX5A : ∃ ξ ∈ Raw.Orb.Gen 315 autStrong 2, Raw.Orb.PRep 315 9 X5A ξ :=
  ((GrpPf.group3 binds PA.head PA.hl (by norm_num) PA.hs).2.2.1 X5A (by quickRfl)).1 (by quickRfl)

theorem memX5C : ∃ ξ ∈ Raw.Orb.Gen 315 autStrong 2, Raw.Orb.PRep 315 9 X5C ξ :=
  ((GrpPf.group3 binds PA.head PA.hl (by norm_num) PA.hs).2.2.1 X5C (by quickRfl)).1 (by quickRfl)

theorem memX7 : ∃ ξ ∈ Raw.Orb.Gen 315 autStrong 2, Raw.Orb.PRep 315 9 X7 ξ :=
  ((GrpPf.group3 binds PA.head PA.hl (by norm_num) PA.hs).2.2.1 X7 (by quickRfl)).1 (by quickRfl)

theorem memE1 : ∃ ξ ∈ Raw.Orb.Gen 315 autStrong 2, Raw.Orb.PRep 315 9 E1 ξ :=
  ((GrpPf.group3 binds PA.head PA.hl (by norm_num) PA.hs).2.2.1 E1 (by quickRfl)).1 (by quickRfl)

theorem card_cent_x5a {ξ : Equiv.Perm (Fin 315)} (hξ : ξ ∈ Raw.Orb.Gen 315 autStrong 2)
    (hX : Raw.Orb.PRep 315 9 X5A ξ) :
    Nat.card {g : Equiv.Perm (Fin 315) // g ∈ Raw.Orb.Gen 315 autStrong 2 ∧ g * ξ = ξ * g} =
      300 := by
  obtain ⟨ν, hν, hV⟩ := memX5C
  rw [(cntComm_sound chainPA k20 hξ hX hν hV).1, sumC5, Nat.eq_of_beq_eq_true k5a]

theorem card_cent_x5c {ν : Equiv.Perm (Fin 315)} (hν : ν ∈ Raw.Orb.Gen 315 autStrong 2)
    (hV : Raw.Orb.PRep 315 9 X5C ν) :
    Nat.card {g : Equiv.Perm (Fin 315) // g ∈ Raw.Orb.Gen 315 autStrong 2 ∧ g * ν = ν * g} =
      50 := by
  obtain ⟨ξ, hξ, hX⟩ := memX5A
  rw [(cntComm_sound chainPA k20 hξ hX hν hV).2, sumC5, Nat.eq_of_beq_eq_true k5c]

theorem card_cent_x7 {ξ : Equiv.Perm (Fin 315)} (hξ : ξ ∈ Raw.Orb.Gen 315 autStrong 2)
    (hX : Raw.Orb.PRep 315 9 X7 ξ) :
    Nat.card {g : Equiv.Perm (Fin 315) // g ∈ Raw.Orb.Gen 315 autStrong 2 ∧ g * ξ = ξ * g} =
      7 := by
  obtain ⟨ν, hν, hV⟩ := memE1
  rw [(cntComm_sound chainPA k20 hξ hX hν hV).1, sumC7, Nat.eq_of_beq_eq_true k7]

theorem card_cent_e1 {ν : Equiv.Perm (Fin 315)} (hν : ν ∈ Raw.Orb.Gen 315 autStrong 2)
    (hV : Raw.Orb.PRep 315 9 E1 ν) :
    Nat.card {g : Equiv.Perm (Fin 315) // g ∈ Raw.Orb.Gen 315 autStrong 2 ∧ g * ν = ν * g} =
      240 := by
  obtain ⟨ξ, hξ, hX⟩ := memX7
  rw [(cntComm_sound chainPA k20 hξ hX hν hV).2, sumC7, Nat.eq_of_beq_eq_true ke1]

end CertificateChecks.KernelC12643

end

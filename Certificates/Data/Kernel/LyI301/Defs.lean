module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.LyI301

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def lyPT : Nat := nat_lit 2826343747

@[expose] noncomputable def lyIX : Nat := nat_lit 7929921077248

@[expose] noncomputable def lyS3T : Nat := nat_lit 20825209903265219088

@[expose] noncomputable def lyS4T : Nat :=
  nat_lit 174994926091799167457378996644500605178666494776450675025642794166427807763120275200030484569131150404661231497744

@[expose] noncomputable def lyVT : Nat :=
  nat_lit 32702020880219496801346892926766202269958630463675584928990082423079310965814110984919652897608150417145469279650738377766216399653563713256357915914338848053667239002000148971945350724499139116888297034445238800

@[expose] noncomputable def lyB0 : Nat := nat_lit 11641631814160

@[expose] noncomputable def lyB0I : Nat := nat_lit 11645406687760

@[expose] noncomputable def lyB1 : Nat := nat_lit 11649934508065

@[expose] noncomputable def lyB1I : Nat := nat_lit 11649935429890

@[expose] noncomputable def lyPt (m : Nat) : Nat := fld(lyPT, Nat.mul (nat_lit 4) m, nat_lit 15)

@[expose] noncomputable def lyS3 (a : Nat) : Nat :=
  fld(lyS3T, Nat.mul (nat_lit 12) a, nat_lit 4095)

@[expose] noncomputable def lyS4 (k : Nat) : Nat :=
  fld(lyS4T, Nat.mul (nat_lit 16) k, nat_lit 65535)

@[expose] noncomputable def lyVk (k : Nat) : Nat :=
  fld(lyVT, Nat.mul (nat_lit 44) k, nat_lit 17592186044415)

@[expose] noncomputable def lyImg (s e α β i : Nat) : Nat :=
  nIf(Nat.blt i (nat_lit 3), fld(s, Nat.mul (nat_lit 4) i, nat_lit 15),
    strictN fld(lyIX, Nat.mul (nat_lit 4) i, nat_lit 15) (fun t =>
      nIf(Nat.blt t (nat_lit 4),
        lyPt (Nat.add (Nat.mul (nat_lit 4) e) fld(α, Nat.mul (nat_lit 4) t, nat_lit 15)),
        lyPt (Nat.sub (Nat.add (nat_lit 4) fld(β, Nat.mul (nat_lit 4) (Nat.sub t (nat_lit 4)), nat_lit 15))
          (Nat.mul (nat_lit 4) e)))))

@[expose] noncomputable def lyMk (s e α β : Nat) : Nat :=
  pmk (nat_lit 11) (nat_lit 4) (lyImg s e α β)

@[expose] noncomputable def lyNotV (x : Nat) : Bool :=
  allN (nat_lit 16) (fun k => bIf(Nat.beq x (lyVk k), false, true))

@[expose] noncomputable def lyMul (p q : Nat) : Nat := pcomp (nat_lit 11) (nat_lit 4) (nat_lit 15) p q

@[expose] noncomputable def lyComm (g gi b bi : Nat) : Bool :=
  strictB (lyMul (lyMul b g) bi) (fun h =>
    strictB (lyMul (lyMul b gi) bi) (fun hi =>
      lyNotV (lyMul (lyMul (lyMul g h) gi) hi)))

@[expose] noncomputable def lyEl (g : Nat) : Bool :=
  bIf(lyNotV (lyMul g g), true, bIf(lyNotV g,
    strictB (pinvS (nat_lit 11) (nat_lit 4) (nat_lit 15) g) (fun gi =>
      bIf(lyComm g gi lyB0 lyB0I, true, lyComm g gi lyB1 lyB1I)), true))

@[expose] noncomputable def lyRow (r : Nat) : Bool :=
  strictB (lyS3 (Nat.shiftRight r (nat_lit 1))) (fun s =>
    strictB (Nat.land r (nat_lit 1)) (fun e =>
      allN (nat_lit 24) (fun ka => strictB (lyS4 ka) (fun α =>
        allN (nat_lit 24) (fun kb => lyEl (lyMk s e α (lyS4 kb)))))))

end CFSG.KC.LyI301

end

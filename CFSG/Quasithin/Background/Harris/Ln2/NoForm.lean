module

public import CFSG.Quasithin.Background.Harris.Ln2.NoFormWedge
public import CFSG.Quasithin.Background.SmithB42LnL4Models
public import CFSG.Quasithin.Background.JonesParshallCurtisModels
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.OneCompActions
public import CFSG.Quasithin.Background.JonesParshallCurtisBound
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Background.SmithB42LnBase
public import CFSG.Quasithin.Background.SmithB51LnSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Ln2

open Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def tvG {n : ℕ} (s : Fin n) : Matrix.SpecialLinearGroup (Fin (n + 1)) (ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection (Fin.succ_ne_zero s).symm 1

theorem coe_tvG {n : ℕ} (s : Fin n) : (tvG s : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) = tv s :=
  rfl

theorem not_selfDual_natRep4 {L : Subgroup (CFSG.Quasithin.G11.GLV V)}
    {θ : ↥L ≃* CFSG.Quasithin.B42Ln.G4} {β : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)}
    (h : ActsAs L θ CFSG.Quasithin.B42Ln.natRep4 β) :
    ¬ CFSG.Quasithin.G11.SelfDual L ⊤ :=
  not_selfDual_of_form h (fun s : Fin 3 => tvG s) fun f hf hinv =>
    no_form_nat (n := 3) (by norm_num) f hf fun s x y => by
      simpa [CFSG.Quasithin.B42Ln.natRep4_apply, coe_tvG] using hinv s x y

theorem not_selfDual_natRep5 {L : Subgroup (CFSG.Quasithin.G11.GLV V)}
    {θ : ↥L ≃* CFSG.Quasithin.JonesParshall.Curtis.G5} {β : V ≃ₗ[ZMod 2] (Fin 5 → ZMod 2)}
    (h : ActsAs L θ CFSG.Quasithin.JonesParshall.Curtis.natRep β) :
    ¬ CFSG.Quasithin.G11.SelfDual L ⊤ :=
  not_selfDual_of_form h (fun s : Fin 4 => tvG s) fun f hf hinv =>
    no_form_nat (n := 4) (by norm_num) f hf fun s x y => by
      simpa [CFSG.Quasithin.JonesParshall.Curtis.natRep_apply, coe_tvG] using hinv s x y

theorem not_selfDual_wedgeRep5 {L : Subgroup (CFSG.Quasithin.G11.GLV V)}
    {θ : ↥L ≃* CFSG.Quasithin.JonesParshall.Curtis.G5} {β : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)}
    (h : ActsAs L θ CFSG.Quasithin.JonesParshall.wedgeRep β) :
    ¬ CFSG.Quasithin.G11.SelfDual L ⊤ :=
  not_selfDual_of_form h (fun s : Fin 4 => tvG s) fun f hf hinv =>
    no_form_wedge f hf fun s x y => by
      simpa [CFSG.Quasithin.JonesParshall.Curtis.wedgeRep_apply', coe_tvG, tw] using hinv s x y

end CFSG.Quasithin.G11.Harris.Ln2

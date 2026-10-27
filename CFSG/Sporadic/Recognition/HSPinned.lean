module

public import CFSG.Sporadic.Recognition.HSPinnedAction
public import CFSG.Sporadic.Recognition.HSPinnedRank3
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Recognition.HSPinned

open CFSG.Blueprint CFSG.Sporadic.HS.Native

noncomputable def hsEquivJ :
    NativeSporadic.HS ≃* JHS := CFSG.Sporadic.SmallF2.seedEquiv hsBaseFacts

noncomputable instance hsAction :
    MulAction NativeSporadic.HS (Fin 100) :=
  MulAction.compHom (Fin 100) (hsEquivJ : NativeSporadic.HS →* JHS)

theorem hs_smul_def
    (g : NativeSporadic.HS) (x : Fin 100) : g • x = hsEquivJ g • x := rfl

@[expose] noncomputable def hsPerm :
    NativeSporadic.HS →* Equiv.Perm (Fin 100) :=
  MulAction.toPermHom NativeSporadic.HS (Fin 100)

theorem hsPerm_apply
    (g : NativeSporadic.HS) (x : Fin 100) : hsPerm g x = g • x := rfl

theorem hs_faithful :
    FaithfulSMul NativeSporadic.HS (Fin 100) :=
  ⟨fun {_ _} hgh => hsEquivJ.injective (FaithfulSMul.eq_of_smul_eq_smul fun x => hgh x)⟩

theorem hsPerm_injective :
    Function.Injective hsPerm := by
  intro g h hgh
  have := hs_faithful
  exact FaithfulSMul.eq_of_smul_eq_smul fun x => by
    have := congrArg (fun p : Equiv.Perm (Fin 100) => p x) hgh
    exact this

theorem card_hsPerm_range :
    Nat.card hsPerm.range = 44352000 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hsPerm_injective).toEquiv]
  exact CFSG.Sporadic.HS.card_HS

@[expose] noncomputable def sigmaHS :
    SimpleGraph (Fin 100) :=
  orbitalGraph NativeSporadic.HS (0 : Fin 100) 4

noncomputable instance :
    DecidableRel sigmaHS.Adj := Classical.decRel _

end CFSG.Sporadic.Recognition.HSPinned

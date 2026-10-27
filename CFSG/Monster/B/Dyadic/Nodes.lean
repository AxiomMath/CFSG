module

public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.Gen.PacketGeneration
public import CFSG.Monster.B.Rep4371.ExactActions
public import CFSG.Monster.B.Dyadic.Beta

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Dyadic

open Module CFSG.Monster.B.Binary.Native
open scoped Matrix

noncomputable local instance instAddCommGroupVst : AddCommGroup Vst :=
  Module.addCommMonoidToAddCommGroup ℚ

theorem packetQ_numerAt (k : Fin 48) (t u : Fin 4371) :
    packetQ k t u = (numerAt k t u : ℚ) / 8 := by
  unfold packetQ packetNum numerAt
  rfl

theorem chi_selGen_apply
    (g : Fin 26) (t : Fin 4371) :
    (chi (selGen g) : Vst →ₗ[ℚ] Vst) (Rbasis t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • Rbasis u := by
  rw [show selGen g = packetElt ⟨Native.selIdx g, selIdx_lt g⟩ from rfl, chi_packetElt_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [packetQ_numerAt, numer_eq_numerAt]

theorem finite_Cbar :
    Finite Cbar := short_centralizer_generated_quotient_simple.1

theorem isSimpleGroup_Cbar :
    IsSimpleGroup Cbar :=
  short_centralizer_generated_quotient_simple.2.2.1

theorem lamS_stable :
    ∀ s : Cbar, ∀ x ∈ Lam Rbasis, chi s x ∈ Lam Rbasis := by
  have := finite_Cbar
  exact lam_stable Rbasis chi selGen closure_selGen chi_selGen_apply

theorem fbarS_fixed
    (s : Cbar) :
    modRep Rbasis chi lamS_stable s (fbar Rbasis) = fbar Rbasis :=
  fbar_fixed Rbasis chi lamS_stable selGen closure_selGen chi_selGen_apply s

@[expose] noncomputable def betaS :
    Cbar →* GL (Fin 4370) (ZMod 2) :=
  beta Rbasis chi lamS_stable fbarS_fixed

theorem betaS_gen
    (g : Fin 26) :
    ((betaS (selGen g) : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      (Qmat g).transpose :=
  beta_gen Rbasis chi lamS_stable selGen chi_selGen_apply fbarS_fixed g

end CFSG.Monster.B.Dyadic

end


module

public import CFSG.Sporadic.Schreier.RuAutInnerBase

public import CFSG.Sporadic.Schreier.RuTCount
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.Sporadic.Schreier.RuCheckBasicInputs
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public import CFSG.Sporadic.Schreier.RuCheckInvInputs
public meta import CFSG.Sporadic.Schreier.RuTreeEltA
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuCheckIsoInputs
public import CFSG.Sporadic.Schreier.RuCheckLInputs
public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.Sporadic.Schreier.RuOrbLFacts
public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public meta import CFSG.Sporadic.Schreier.RuOrbLDefs
public import CFSG.Sporadic.Schreier.RuCheckSylowInputs
public import CFSG.Sporadic.Schreier.RuCheckTreeInputs
public import CFSG.Sporadic.Schreier.RuWitArrays
public import Certificates.Data.CFSGNative.Ru.Data

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_centralizer_a_le :
    Nat.card (ruP ⊓ Subgroup.centralizer {ruA0} : Subgroup _) ≤ 116480 := by
  have h1 : ((fun c => c * ruA1 * c⁻¹) '' ((ruP ⊓ Subgroup.centralizer {ruA0} : Subgroup _) :
      Set (Equiv.Perm (Fin 4060)))).ncard =
      Nat.card (ruP ⊓ Subgroup.centralizer {ruA0} : Subgroup _) := by
    rw [conj_ruA1_injOn.ncard_image]
    exact (Nat.card_coe_set_eq _).symm
  have h2 : (fun c => c * ruA1 * c⁻¹) '' ((ruP ⊓ Subgroup.centralizer {ruA0} : Subgroup _) :
      Set (Equiv.Perm (Fin 4060))) ⊆ ruT := by
    rintro _ ⟨c, hc, rfl⟩
    exact conj_mem_ruT hc ruA1_mem_ruT
  rw [← h1, ← ncard_ruT]
  exact Set.ncard_le_ncard h2 (Set.toFinite _)

theorem ruCentralizer_a :
    ruP ⊓ Subgroup.centralizer {ruA0} = ruL :=
  (Subgroup.eq_of_le_of_card_ge ruL_le_centralizer (card_centralizer_a_le.trans card_ruL.ge)).symm

theorem ruT_eq_orbit :
    ruT = (fun l => l * ruA1 * l⁻¹) '' (ruL : Set (Equiv.Perm (Fin 4060))) := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨l, hl, rfl⟩
    exact conj_mem_ruT (ruL_le_centralizer hl) ruA1_mem_ruT
  · rw [ncard_ruT, (conj_ruA1_injOn.mono fun x hx => ruL_le_centralizer hx).ncard_image,
      ← Nat.card_coe_set_eq]
    exact card_ruL.ge
  · exact Set.toFinite _

theorem mulAut_inner
    (φ : MulAut ruP) : ∃ g : ruP, φ = MulAut.conj g := by
  have ha : ((φ ruA0' : ruP) : Equiv.Perm (Fin 4060)) ∈ ruAP :=
    (mulAut_ruAP_iff φ ruA0').2 (self_mem_conjSet ruP ruA0)
  obtain ⟨g, hg, hga⟩ := ha
  set g' : ruP := ⟨g, hg⟩
  have hga' : g' * ruA0' * g'⁻¹ = φ ruA0' := Subtype.ext hga
  set ψ : MulAut ruP := (MulAut.conj g')⁻¹ * φ with hψdef
  have hψa : ψ ruA0' = ruA0' := by
    rw [hψdef, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, ← hga']
    group
  have hb : ((ψ ruA1' : ruP) : Equiv.Perm (Fin 4060)) ∈ ruT := mulAut_mem_ruT hψa ruA1_mem_ruT
  rw [ruT_eq_orbit] at hb
  obtain ⟨l, hl, hlb⟩ := hb
  set l' : ruP := ⟨l, ruL_le hl⟩
  have hla : MulAut.conj l' ruA0' = ruA0' := by
    rw [MulAut.conj_apply]
    apply Subtype.ext
    have hc : l * ruA0 = ruA0 * l :=
      Subgroup.mem_centralizer_singleton_iff.1 (ruL_le_centralizer hl).2
    show l * ruA0 * l⁻¹ = ruA0
    rw [hc]
    group
  have hlb' : MulAut.conj l' ruA1' = ψ ruA1' := by
    rw [MulAut.conj_apply]
    exact Subtype.ext hlb
  have hψl : ψ = MulAut.conj l' := by
    apply MulEquiv.toMonoidHom_injective
    refine MonoidHom.eq_of_eqOn_dense closure_ruA' ?_
    intro x hx
    rcases hx with rfl | rfl
    · show ψ ruA0' = MulAut.conj l' ruA0'
      rw [hψa, hla]
    · show ψ ruA1' = MulAut.conj l' ruA1'
      rw [hlb']
  refine ⟨g' * l', ?_⟩
  rw [map_mul, ← hψl, hψdef, mul_inv_cancel_left]

theorem conj_bijective :
    Function.Bijective (MulAut.conj : ruP →* MulAut ruP) := by
  refine ⟨?_, fun φ => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center ruP := Subgroup.mem_center_iff.2 fun x => by
      have := congrArg (fun f : MulAut ruP => f x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    rw [center_ruP] at hc
    exact hc
  · obtain ⟨g, hg⟩ := mulAut_inner φ
    exact ⟨g, hg.symm⟩

theorem card_outer_ruP :
    Nat.card (Outer ruP) = 1 := by
  have h : OuterAutomorphisms.inner ruP = ⊤ := by
    rw [OuterAutomorphisms.inner, MonoidHom.range_eq_top]
    exact conj_bijective.2
  show (OuterAutomorphisms.inner ruP).index = 1
  rw [h, Subgroup.index_top]

theorem CTUC_Ru_full_inner_automorphisms_and_second_centralizer :
    Subgroup.center ruP = ⊥ ∧ Function.Bijective (MulAut.conj : ruP →* MulAut ruP) ∧
    Nat.card (Outer ruP) = 1 ∧ ruP ⊓ Subgroup.centralizer {ruA0} = ruL :=
  ⟨center_ruP, conj_bijective, card_outer_ruP, ruCentralizer_a⟩

end CFSG.Sporadic.RuSchreier

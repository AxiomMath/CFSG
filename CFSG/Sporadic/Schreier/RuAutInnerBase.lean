
module

public import CFSG.Sporadic.Schreier.RuTCountBase
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
public import CFSG.Sporadic.Th.F2Spec

@[expose] public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

abbrev ruA0' : ruP := ⟨ruA0, ruA0_mem⟩

abbrev ruA1' : ruP := ⟨ruA1, ruA1_mem⟩

theorem closure_ruA' : Subgroup.closure ({ruA0', ruA1'} : Set ruP) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage
    (k := ({ruA0, ruA1} : Set (Equiv.Perm (Fin 4060))))
  have e : (((↑) : Subgroup.closure ({ruA0, ruA1} : Set (Equiv.Perm (Fin 4060))) →
      Equiv.Perm (Fin 4060)) ⁻¹' {ruA0, ruA1}) = ({ruA0', ruA1'} : Set ruP) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  rw [e] at h
  exact h

theorem center_ruP :
    Subgroup.center ruP = ⊥ := by
  have := isSimpleGroup_ruP
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ruP) with h | h
  · exact h
  · exfalso
    have ha : ruA0' ∈ Subgroup.center ruP := h ▸ Subgroup.mem_top _
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 ha ruA1')
    exact ruSeed_relations.2.2.2.2.2.2.2 this.symm

theorem eq_one_of_comm_gens
    {d : ruP} (ha : d * ruA0' = ruA0' * d) (hb : d * ruA1' = ruA1' * d) :
    d = 1 := by
  have hd : d ∈ Subgroup.centralizer (Subgroup.closure ({ruA0', ruA1'} : Set ruP)) := by
    rw [Subgroup.centralizer_closure]
    intro g hg
    rcases hg with rfl | rfl
    · exact ha.symm
    · exact hb.symm
  rw [closure_ruA', Subgroup.coe_top, Subgroup.centralizer_univ, center_ruP] at hd
  exact hd

theorem ruA1_mem_ruT :
    ruA1 ∈ ruT := by
  obtain ⟨-, -, -, -, h13, h14, h29, -⟩ := ruSeed_relations
  exact ⟨ruA1_mem, ruA1_sq_mem, h13, h14, h29⟩

theorem conj_mem_ruT {c x : Equiv.Perm (Fin 4060)} (hc : c ∈ ruP ⊓ Subgroup.centralizer {ruA0})
    (hx : x ∈ ruT) : c * x * c⁻¹ ∈ ruT := by
  obtain ⟨hxP, hz, h13, h14, h29⟩ := hx
  have hcP := (Subgroup.mem_inf.1 hc).1
  have hca : c * ruA0 = ruA0 * c :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2
  have key : ∀ y : Equiv.Perm (Fin 4060), ruA0 * (c * y * c⁻¹) = c * (ruA0 * y) * c⁻¹ := by
    intro y
    calc ruA0 * (c * y * c⁻¹) = (ruA0 * c) * y * c⁻¹ := by group
      _ = (c * ruA0) * y * c⁻¹ := by rw [hca]
      _ = c * (ruA0 * y) * c⁻¹ := by group
  refine ⟨ruP.mul_mem (ruP.mul_mem hcP hxP) (ruP.inv_mem hcP), ?_, ?_, ?_, ?_⟩
  · rw [conj_pow]
    exact conj_mem_conjSet hz hcP
  · rw [key, conj_pow, h13]
    group
  · rw [conj_pow, key, orderOf_conj', h14]
  · have e : ruA0 * (c * x * c⁻¹) * ruA0 * (c * x * c⁻¹) ^ 2 =
        c * (ruA0 * x * ruA0 * x ^ 2) * c⁻¹ := by
      rw [key, conj_pow]
      calc c * (ruA0 * x) * c⁻¹ * ruA0 * (c * x ^ 2 * c⁻¹)
          = c * (ruA0 * x) * (c⁻¹ * (ruA0 * c)) * x ^ 2 * c⁻¹ := by group
        _ = c * (ruA0 * x) * (c⁻¹ * (c * ruA0)) * x ^ 2 * c⁻¹ := by rw [hca]
        _ = c * (ruA0 * x * ruA0 * x ^ 2) * c⁻¹ := by group
    rw [e, conj_pow, h29]
    group

theorem conj_ruA1_injOn :
    Set.InjOn (fun c => c * ruA1 * c⁻¹) (ruP ⊓ Subgroup.centralizer {ruA0} : Subgroup _) := by
  intro c hc c' hc' h
  simp only at h
  have hcP := (Subgroup.mem_inf.1 hc).1
  have hcP' := (Subgroup.mem_inf.1 hc').1
  have hca : c * ruA0 = ruA0 * c :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2
  have hca' : c' * ruA0 = ruA0 * c' :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc').2
  let d : ruP := ⟨c'⁻¹ * c, ruP.mul_mem (ruP.inv_mem hcP') hcP⟩
  have hd1 : d = 1 := eq_one_of_comm_gens
    (Subtype.ext (by
      show c'⁻¹ * c * ruA0 = ruA0 * (c'⁻¹ * c)
      have : c'⁻¹ * ruA0 = ruA0 * c'⁻¹ := by
        calc c'⁻¹ * ruA0 = c'⁻¹ * (ruA0 * c') * c'⁻¹ := by group
          _ = c'⁻¹ * (c' * ruA0) * c'⁻¹ := by rw [hca']
          _ = ruA0 * c'⁻¹ := by group
      calc c'⁻¹ * c * ruA0 = c'⁻¹ * (c * ruA0) := by group
        _ = c'⁻¹ * (ruA0 * c) := by rw [hca]
        _ = (c'⁻¹ * ruA0) * c := by group
        _ = (ruA0 * c'⁻¹) * c := by rw [this]
        _ = ruA0 * (c'⁻¹ * c) := by group))
    (Subtype.ext (by
      show c'⁻¹ * c * ruA1 = ruA1 * (c'⁻¹ * c)
      calc c'⁻¹ * c * ruA1 = c'⁻¹ * (c * ruA1 * c⁻¹) * c := by group
        _ = c'⁻¹ * (c' * ruA1 * c'⁻¹) * c := by rw [h]
        _ = ruA1 * (c'⁻¹ * c) := by group))
  have := congrArg Subtype.val hd1
  simp only [d, Subgroup.coe_one] at this
  calc c = c' * (c'⁻¹ * c) := by group
    _ = c' := by rw [this, mul_one]

theorem mem_ruT_iff (y : ruP) : (y : Equiv.Perm (Fin 4060)) ∈ ruT ↔
    (((y ^ 2 : ruP) : Equiv.Perm (Fin 4060)) ∈ ruZP ∧ (ruA0' * y) ^ 13 = 1 ∧
      orderOf (ruA0' * y ^ 2) = 14 ∧ (ruA0' * y * ruA0' * y ^ 2) ^ 29 = 1) := by
  simp only [ruT, Set.mem_ofPred_eq, Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_mul,
    Subgroup.coe_one, ← Subgroup.orderOf_coe, y.2, true_and]

theorem mulAut_mem_ruT
    {ψ : MulAut ruP} (hψ : ψ ruA0' = ruA0') {y : ruP}
    (hy : (y : Equiv.Perm (Fin 4060)) ∈ ruT) : ((ψ y : ruP) : Equiv.Perm (Fin 4060)) ∈ ruT := by
  rw [mem_ruT_iff] at hy ⊢
  obtain ⟨h2, h13, h14, h29⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow ψ]
    exact (mulAut_ruZP_iff ψ (y ^ 2)).2 h2
  · rw [← hψ, ← map_mul ψ, ← map_pow ψ, h13, map_one]
  · rw [← hψ, ← map_pow ψ, ← map_mul ψ, MulEquiv.orderOf_eq, h14]
  · rw [← hψ, ← map_pow ψ, ← map_mul ψ, ← map_mul ψ, ← map_mul ψ, ← map_pow ψ, h29, map_one]

end CFSG.Sporadic.RuSchreier

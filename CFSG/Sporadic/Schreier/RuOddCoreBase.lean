
module

public import CFSG.Sporadic.Schreier.RuAutInnerBase
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Sporadic.Schreier.RuCheckBasicInputs
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
public meta import CFSG.Sporadic.Schreier.RuCheckSylow
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
public import CFSG.Sporadic.Schreier.RuCheckTreeInputs
public import CFSG.Sporadic.Schreier.RuWitArrays
public import Certificates.Data.CFSGNative.Ru.Data

@[expose] public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

def NoOddNormal (G : Type*) [Group G] : Prop :=
  ∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥

theorem NoOddNormal.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : NoOddNormal G) : NoOddNormal H := by
  intro R hR hodd
  have hc : (R.comap e.toMonoidHom).Normal := hR.comap _
  have hcard : Nat.card (R.comap e.toMonoidHom) = Nat.card R := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.map_comap_eq_self_of_surjective e.surjective]
  have h0 := h _ hc (hcard ▸ hodd)
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective R, h0,
    Subgroup.map_bot]

theorem NoOddNormal.cores {G : Type*} [Group G] [Finite G] (h : NoOddNormal G) :
    CFSG.piCore {p : Nat.Primes | p.1 ≠ 2} G = ⊥ ∧ CFSG.pPrimeCore 2 G = ⊥ ∧
      CFSG.oddCore G = ⊥ := by
  refine ⟨?_, CFSG.pPrimeCore_eq_bot_iff.2 fun K hK hc => h K hK (Nat.coprime_two_left.1 hc),
    sSup_eq_bot.2 fun N hN => h N hN.1 hN.2⟩
  refine h _ inferInstance ?_
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  exact (CFSG.LocalCores.piCore_isPiSubgroup {p : Nat.Primes | p.1 ≠ 2} ⟨2, Nat.prime_two⟩ h2) rfl

theorem noOddNormal_ruC :
    NoOddNormal ruC := by
  intro R hR hodd
  set Jc : Subgroup ruC := ruJ.subgroupOf ruC
  have hJn : Jc.Normal := ruJ_normal
  have hcardJ : Nat.card Jc = 2 ^ 11 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ruJ_leC).toEquiv, card_ruJ]
    norm_num
  have hRJ : R ⊓ Jc = ⊥ := by
    apply Subgroup.card_eq_one.1
    have h1 : Nat.card (R ⊓ Jc : Subgroup ruC) ∣ Nat.card R :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (R ⊓ Jc : Subgroup ruC) ∣ 2 ^ 11 :=
      hcardJ ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases k with _ | k
    · simpa using hk
    · exfalso
      have : 2 ∣ Nat.card R := by
        rw [hk, pow_succ] at h1
        exact (Dvd.intro_left _ rfl).trans h1
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  rw [eq_bot_iff]
  intro r hr
  have hcomm : ∀ j ∈ Jc, r * j = j * r := by
    intro j hj
    have hc : r * j * r⁻¹ * j⁻¹ ∈ R ⊓ Jc := by
      refine ⟨?_, ?_⟩
      · have := hR.conj_mem r⁻¹ (R.inv_mem hr) j
        have e : r * j * r⁻¹ * j⁻¹ = r * (j * r⁻¹ * j⁻¹) := by group
        rw [e]
        exact R.mul_mem hr this
      · exact Jc.mul_mem (hJn.conj_mem j hj r) (Jc.inv_mem hj)
    rw [hRJ, Subgroup.mem_bot] at hc
    calc r * j = r * j * r⁻¹ * j⁻¹ * j * r := by group
      _ = j * r := by rw [hc]; group
  have hrJ : (r : Equiv.Perm (Fin 4060)) ∈ ruJ := by
    apply ruCentralizer_J
    refine ⟨r.2, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
    have := hcomm ⟨j, ruJ_leC hj⟩ (Subgroup.mem_subgroupOf.2 hj)
    exact (congrArg Subtype.val this).symm
  have : r ∈ R ⊓ Jc := ⟨hr, Subgroup.mem_subgroupOf.2 hrJ⟩
  rw [hRJ] at this
  exact this

def conjCentralizerEquiv {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (x : Equiv.Perm (Fin 4060)) :
    (ruP ⊓ Subgroup.centralizer {x} : Subgroup _) ≃*
      (ruP ⊓ Subgroup.centralizer {g * x * g⁻¹} : Subgroup _) where
  toFun c := ⟨g * c * g⁻¹, Subgroup.mem_inf.2 ⟨ruP.mul_mem (ruP.mul_mem hg
      (Subgroup.mem_inf.1 c.2).1) (ruP.inv_mem hg), Subgroup.mem_centralizer_singleton_iff.2 (by
        have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2
        calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
          _ = g * (x * c) * g⁻¹ := by rw [h]
          _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group)⟩⟩
  invFun c := ⟨g⁻¹ * c * g, Subgroup.mem_inf.2 ⟨ruP.mul_mem (ruP.mul_mem (ruP.inv_mem hg)
      (Subgroup.mem_inf.1 c.2).1) hg, Subgroup.mem_centralizer_singleton_iff.2 (by
        have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2
        calc g⁻¹ * c * g * x = g⁻¹ * (c * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * c) * g := by rw [h]
          _ = x * (g⁻¹ * c * g) := by group)⟩⟩
  left_inv c := Subtype.ext (by simp only; group)
  right_inv c := Subtype.ext (by simp only; group)
  map_mul' c d := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem noOddNormal_centralizer_ruZ :
    NoOddNormal (ruP ⊓ Subgroup.centralizer {ruZ} : Subgroup _) :=
  NoOddNormal.of_mulEquiv (MulEquiv.subgroupCongr ruC_eq_centralizer) noOddNormal_ruC

end CFSG.Sporadic.RuSchreier

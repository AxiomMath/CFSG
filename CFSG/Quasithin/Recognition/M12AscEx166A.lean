module

public import CFSG.Quasithin.Recognition.M12AscKlein
public import CFSG.Quasithin.Recognition.M12AscX1Abs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

open Subgroup

variable {I : Type*} [Group I]

theorem KleinCore.toTop [Finite I] {K V : Subgroup I} {z y : I} (h : KleinCore K V z y) :
    KleinCore (⊤ : Subgroup ↥K) (V.subgroupOf K) ⟨z, h.V_le h.z_mem⟩ ⟨y, h.y_mem⟩ where
  z_sq := Subtype.ext h.z_sq
  z_ne := fun e => h.z_ne (congrArg Subtype.val e)
  z_mem := Subgroup.mem_subgroupOf.2 h.z_mem
  V_le := le_top
  V_card := by
    rw [← h.V_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.V_le).toEquiv
  V_sq := fun v hv => Subtype.ext (h.V_sq v (Subgroup.mem_subgroupOf.1 hv))
  cent := fun k _ hk => Subgroup.mem_subgroupOf.2 (h.cent k k.2 (congrArg Subtype.val hk))
  y_mem := trivial
  y_cube := Subtype.ext h.y_cube
  y_norm := fun v hv => Subgroup.mem_subgroupOf.2 (h.y_norm v (Subgroup.mem_subgroupOf.1 hv))
  y_ne := fun e => h.y_ne (congrArg Subtype.val e)
  syl := by
    intro W _ hW
    have hmapcard : Nat.card (W.map K.subtype) = Nat.card W :=
      (Nat.card_congr (Subgroup.equivMapOfInjective W K.subtype K.subtype_injective)).symm
    have hp : IsPGroup 2 (W.map K.subtype) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hW
      refine (IsPGroup.iff_card).2 ⟨n, ?_⟩
      rw [hmapcard, hn]
    have := h.syl _ (Subgroup.map_subtype_le _) hp
    rwa [hmapcard] at this

theorem isKleinFour_of_card_four {S : Type*} [Group S] (hc : Nat.card S = 4)
    (hsq : ∀ s : S, s * s = 1) : IsKleinFour S := by
  refine ⟨hc, ?_⟩
  have hpow : ∀ s : S, s ^ 2 = 1 := fun s => by rw [pow_two]; exact hsq s
  have hdvd : Monoid.exponent S ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have : Subsingleton S := Monoid.exp_eq_one_iff.mp h1
    have := Nat.card_unique (α := S)
    omega
  · exact h2

namespace KleinCore

variable {X : Type*} [Group X] {V : Subgroup X} {z y : X}

theorem exists_sylow_eq [Finite X] (h : KleinCore (⊤ : Subgroup X) V z y) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = V := by
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [h.V_card]; norm_num)
  obtain ⟨S0, hS0⟩ := hVp.exists_le_sylow
  have hS0card : Nat.card (S0 : Subgroup X) ≤ 4 := h.syl _ le_top S0.isPGroup'
  exact ⟨S0, (Subgroup.eq_of_le_of_card_ge hS0 (by rw [h.V_card]; exact hS0card)).symm⟩

theorem sylow_facts [Finite X] (h : KleinCore (⊤ : Subgroup X) V z y) (S : Sylow 2 X) :
    (∀ s : ↥(S : Subgroup X), s * s = 1) ∧ Nat.card (S : Subgroup X) = 4 := by
  obtain ⟨P, hP⟩ := h.exists_sylow_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P S
  have hcard : Nat.card (S : Subgroup X) = 4 := by
    have h1 := Sylow.card_eq_multiplicity S
    have h2 := Sylow.card_eq_multiplicity P
    rw [h1, ← h2, hP, h.V_card]
  refine ⟨fun s => ?_, hcard⟩
  have hs : (s : X) ∈ ((g • P : Sylow 2 X) : Subgroup X) := by rw [hg]; exact s.2
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP] at hs
  obtain ⟨w, hw, hws⟩ := Subgroup.mem_map.1 hs
  apply Subtype.ext
  have hws' : g * w * g⁻¹ = (s : X) := by simpa [MulAut.conj_apply] using hws
  show (s : X) * (s : X) = 1
  rw [← hws']
  calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    _ = 1 := by rw [h.V_sq w hw]; group

theorem hasDihedralSylowTwo [Finite X] (h : KleinCore (⊤ : Subgroup X) V z y) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo X := by
  intro S
  obtain ⟨hsq, hcard⟩ := h.sylow_facts S
  have : IsKleinFour ↥(S : Subgroup X) := isKleinFour_of_card_four hcard hsq
  refine ⟨1, le_refl 1, ?_⟩
  simpa using (IsKleinFour.nonempty_mulEquiv (G₁ := ↥(S : Subgroup X)) (G₂ := DihedralGroup 2))

theorem pPrimeCore_eq_bot [Finite X] (h : KleinCore (⊤ : Subgroup X) V z y) :
    CFSG.pPrimeCore 2 X = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hNn hcop
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.1 hcop
  have hsq1 : ∀ a ∈ N, a * a = 1 → a = 1 := by
    intro a ha haa
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact haa)
    have hodd : Odd (orderOf a) :=
      Odd.of_dvd_nat hNodd (by simpa using Subgroup.orderOf_dvd_natCard N ha)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h2'
    · exact orderOf_eq_one_iff.1 h1
    · rw [h2'] at hodd
      exact absurd hodd (by decide)
  have hinv : ∀ w ∈ V, w ≠ 1 → ∀ a ∈ N, w * a * w⁻¹ = a⁻¹ := by
    intro w hwV hw1
    have hw2 : w * w = 1 := h.V_sq w hwV
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hg : ∀ p ∈ N, w * p * w⁻¹ ∈ N := fun p hp => hNn.conj_mem p hp w
    let σ : ↥N →* ↥N := conjP N w hg
    have hσσ : ∀ a, σ (σ a) = a := by
      intro a
      apply Subtype.ext
      show w * (w * (a : X) * w⁻¹) * w⁻¹ = a
      rw [hwi]
      calc w * (w * (a : X) * w) * w = (w * w) * (a : X) * (w * w) := by group
        _ = a := by rw [hw2]; group
    have hfix : ∀ a, σ a = a → a = 1 := by
      intro a ha
      have hc : w * (a : X) * w⁻¹ = a := congrArg Subtype.val ha
      have hcomm : (a : X) * w = w * (a : X) := by
        calc (a : X) * w = (w * (a : X) * w⁻¹) * w := by rw [hc]
          _ = w * (a : X) := by group
      have haV : (a : X) ∈ V := h.cent_sharp hwV hw1 (Subgroup.mem_top _) hcomm
      apply Subtype.ext
      exact hsq1 a a.2 (h.V_sq _ haV)
    have hσ := fpf_inverts σ hσσ hfix
    intro a ha
    exact congrArg Subtype.val (hσ ⟨a, ha⟩)
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  obtain ⟨n12, -, -⟩ := h.V_three_ne
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq
  have hz1V : y * z * y⁻¹ ∈ V := h.y_norm z h.z_mem
  have hz11 : y * z * y⁻¹ ≠ 1 := by
    intro e
    apply h.z_ne
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [e]; group
  have hw3V : z * (y * z * y⁻¹) ∈ V := V.mul_mem h.z_mem hz1V
  have hw31 : z * (y * z * y⁻¹) ≠ 1 := by
    intro e
    apply n12
    have := eq_inv_of_mul_eq_one_right e
    rw [hzi] at this
    exact this.symm
  have h1 := hinv z h.z_mem h.z_ne a ha
  have h2 := hinv _ hz1V hz11 a ha
  have h3 := hinv _ hw3V hw31 a ha
  have e3 : (z * (y * z * y⁻¹)) * a * (z * (y * z * y⁻¹))⁻¹ = a := by
    calc (z * (y * z * y⁻¹)) * a * (z * (y * z * y⁻¹))⁻¹
        = z * ((y * z * y⁻¹) * a * (y * z * y⁻¹)⁻¹) * z⁻¹ := by group
      _ = z * a⁻¹ * z⁻¹ := by rw [h2]
      _ = (z * a * z⁻¹)⁻¹ := by group
      _ = a := by rw [h1, inv_inv]
  rw [e3] at h3
  have haa : a * a = 1 := by
    calc a * a = a * a⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel a
  exact hsq1 a ha haa

end KleinCore

end CFSG.Quasithin

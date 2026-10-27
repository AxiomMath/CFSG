module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.RankThree.PartTwo.Sec5.Item37
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4FStar

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open scoped commutatorElement

private theorem t28q_not_three_dvd_card {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  rw [hn]
  intro h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

private theorem t28q_commutator_mem_centralizer {Q : Type*} [Group Q] {K : Subgroup Q} {u x : Q}
    (hu : u ∈ Subgroup.normalizer (K : Set Q)) (hx : x ∈ Subgroup.centralizer (K : Set Q)) :
    ⁅u, x⁆ ∈ Subgroup.centralizer (K : Set Q) := by
  have h1 : u * x * u⁻¹ ∈ Subgroup.centralizer (K : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : u⁻¹ * k * u ∈ K := (Subgroup.mem_normalizer_iff''.mp hu k).mp hk
    have hc := Subgroup.mem_centralizer_iff.mp hx _ hk'
    calc k * (u * x * u⁻¹) = u * ((u⁻¹ * k * u) * x) * u⁻¹ := by group
      _ = u * (x * (u⁻¹ * k * u)) * u⁻¹ := by rw [hc]
      _ = u * x * u⁻¹ * k := by group
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hx)

namespace Res3Q

theorem isElemAbelian_A {Q : Type} [Group Q] [Finite Q] {c d g : Q}
    {A B₀ K V₀ U : Subgroup Q} (h : Res3Q c d g A B₀ K V₀ U) :
    CFSG.Assembly.IsElemAbelian 3 A := by
  have hB : CFSG.Assembly.IsElemAbelian 3 B₀ :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [h.B₀_card]; norm_num),
      h.B₀_pow⟩
  have hc : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c) :=
    CFSG.Open.isElemAbelian_zpowers h.c_pow
  rw [h.A_eq]
  refine CFSG.Open.IsElemAbelian.sup_of_commute hB hc fun a ha b hb => ?_
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr h.c_cent hb) a (h.B₀_le ha)

theorem commutator_pCore_V₀ {Q : Type} [Group Q] [Finite Q] {c d g : Q}
    {A B₀ K V₀ U : Subgroup Q} (h : Res3Q c d g A B₀ K V₀ U) :
    ⁅CFSG.pCore 3 Q, V₀⁆ = ⊥ := by
  have hAV : A ≤ Subgroup.normalizer (V₀ : Set Q) := by
    rw [h.A_eq]
    refine sup_le (fun b hb => Subgroup.centralizer_le_normalizer _ ?_)
      (Subgroup.zpowers_le.mpr h.c_memV₀)
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (h.V₀_le hv) b hb).symm
  have hAP : A ≤ Subgroup.normalizer ((CFSG.pCore 3 Q : Subgroup Q) : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hVP : V₀ ≤ Subgroup.normalizer ((CFSG.pCore 3 Q : Subgroup Q) : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  exact Sec5.rank3II_3_7 Q 3 Nat.prime_three (by norm_num) A V₀ (CFSG.pCore 3 Q)
    h.isElemAbelian_A (t28q_not_three_dvd_card h.V₀_isPGroup) hAV CFSG.pCore_isPGroup hAP hVP
    fun y hy hy3 => h.A_max y (Subgroup.mem_inf.mp hy).2 hy3

theorem U_le_centralizer_K {Q : Type} [Group Q] [Finite Q] {c d g : Q}
    {A B₀ K V₀ U : Subgroup Q} (h : Res3Q c d g A B₀ K V₀ U)
    (hC : Res3QCompFacts c d A B₀ K) : U ≤ Subgroup.centralizer (K : Set Q) := by
  have hKc : CFSG.IsComponent K := ⟨h.K_quasi, h.K_subnormal⟩
  have hcK : Subgroup.zpowers c ≤ Subgroup.centralizer (K : Set Q) :=
    Subgroup.zpowers_le.mpr h.c_cent
  refine h.U_comm_c.symm.le.trans (Subgroup.commutator_le.mpr fun u hu x hx => ?_)
  exact t28q_commutator_mem_centralizer
    (hC.normalizes K hKc u (h.V₀_le (h.U_le hu))) (hcK hx)

theorem exists_isComponent {Q : Type} [Group Q] [Finite Q] {c d g : Q}
    {A B₀ K V₀ U : Subgroup Q} (h : Res3Q c d g A B₀ K V₀ U)
    (hC : Res3QCompFacts c d A B₀ K) :
    ∃ J : Subgroup Q, CFSG.IsComponent J ∧ J ≠ K ∧ ¬ U ≤ Subgroup.centralizer (J : Set Q) := by
  by_contra hno
  push Not at hno
  have hUJ : ∀ J : Subgroup Q, CFSG.IsComponent J → U ≤ Subgroup.centralizer (J : Set Q) := by
    intro J hJ
    by_cases hJK : J = K
    · rw [hJK]
      exact h.U_le_centralizer_K hC
    · exact hno J hJ hJK
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.U_ne
  have huV : (u : Q) ∈ V₀ := h.U_le u.2
  have hu1' : (u : Q) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  have hO3 : CFSG.pPrimeCore 3 Q = ⊥ :=
    CFSG.pPrimeCore_eq_bot_iff.mpr fun N hN hcop =>
      h.oThreePrime N hN ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
  have hO2 : CFSG.pCore 2 Q = ⊥ :=
    h.oThreePrime _ CFSG.pCore_normal (t28q_not_three_dvd_card CFSG.pCore_isPGroup)
  have hcomm : CFSG.pCore 3 Q ≤ Subgroup.centralizer (V₀ : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.commutator_pCore_V₀
  have hF : ∀ x ∈ CFSG.fittingSubgroup Q, (u : Q) * x = x * u := by
    intro x hx
    rw [CFSG.Fitting_eq_pcore Q 3 hO3] at hx
    exact Subgroup.mem_centralizer_iff.mp (hcomm hx) u huV
  obtain ⟨k, hk⟩ := h.V₀_isPGroup ⟨(u : Q), huV⟩
  obtain ⟨x, hx, hne⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.fstar_bridge hO2 hu1'
    ⟨k, by simpa using congrArg Subtype.val hk⟩ hF
  have hlayer : CFSG.layer Q ≤ Subgroup.centralizer ({(u : Q)} : Set Q) := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun J hJ y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hUJ J hJ u.2) y hy)
  exact hne (Subgroup.mem_centralizer_singleton_iff.mp (hlayer hx)).symm

end Res3Q

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3

module

public import CFSG.RankThree.GF2n.Smith81.LinSetup
import CFSG.RankThree.GF2n.Smith81.TiSylow
import CFSG.RankThree.GF2n.Smith81.Sec1Frobenius
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43OutGen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables
public import CFSG.RankThree.GF2n.Smith81.TiRecognition

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
  Matrix
open CFSG.SeitzReduction.F4Pilot (ordSL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

theorem factorization_ordSL_two {f : ℕ} (hf : 1 ≤ f) (n : ℕ) :
    (ordSL n (2 ^ f)).factorization 2 = f * (n * (n - 1) / 2) := by
  have hodd : Odd (∏ j ∈ Finset.Icc 2 n, ((2 ^ f) ^ j - 1)) := by
    refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun j hj => ?_
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have h1 : 2 ∣ (2 ^ f) ^ j := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
    have h2 : 1 ≤ (2 ^ f) ^ j := Nat.one_le_pow _ _ (by positivity)
    rw [Nat.odd_iff]
    omega
  refine factorization_two_eq_of_odd ?_ hodd
  rw [ordSL, pow_mul]

section Frob

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem factorization_relIndex_H0_le (H : StrothHyp M Q Z) {f : ℕ} (hf : Nat.card Z = 2 ^ f) :
    ((H0 M Z).relIndex M).factorization 2 ≤ f.factorization 2 := by
  classical
  obtain ⟨-, K, _, _, e, hact⟩ := semilinAct_Z H
  have hMN : M ≤ Subgroup.normalizer (Z : Set G) := H.Z_normal.2
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := H.q4
      rw [hf] at this
      norm_num at this
    · exact h
  let ε : ↥Z ≃ K := e.toEquiv.trans Multiplicative.toAdd
  have hK : Nat.card K = 2 ^ f := (Nat.card_congr ε).symm.trans hf
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let c : ↥M →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hMN)
  let ρ : ↥M →* Equiv.Perm K := ε.permCongrHom.toMonoidHom.comp ((MulAut.toPerm ↥Z).comp c)
  have hρ : ∀ (m : ↥M) (x : K), ρ m x = ε (c m (ε.symm x)) := fun _ _ => rfl
  have hc : ∀ (m : ↥M) (z : ↥Z), ((c m z : ↥Z) : G) = (m : G) * z * (m : G)⁻¹ :=
    fun _ _ => rfl
  have hform : ∀ m : ↥M, ∃ (a : K) (σ : K ≃+* K), ∀ x, ρ m x = a * σ x := by
    intro m
    obtain ⟨a, σ, h⟩ := hact m m.2
    refine ⟨a, σ, fun x => ?_⟩
    have h1 := h (ε.symm x) (c m (ε.symm x)) (hc m _)
    have h2 : Multiplicative.toAdd (e (ε.symm x)) = x := ε.apply_symm_apply x
    rw [h2] at h1
    exact h1
  have hrange : ρ.range ≤ semilinearPerm K K := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨a, σ, h⟩ := hform m
    refine ⟨fun x y => ?_, σ, fun t x => ?_⟩
    · rw [h, h, h, map_add, mul_add]
    · rw [h, h, smul_eq_mul, smul_eq_mul, map_mul]
      ring
  have hker : ρ.ker = (H0 M Z).subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      refine ⟨m.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have h2 : c m ⟨z, hz⟩ = ⟨z, hz⟩ := by
        apply ε.injective
        have h3 := congrArg (fun T : Equiv.Perm K => T (ε ⟨z, hz⟩)) h1
        simp only [hρ, Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq] at h3
        exact h3
      have h3 := congrArg Subtype.val h2
      rw [hc] at h3
      calc z * m = (m * z * (m : G)⁻¹) * m := by rw [h3]
        _ = m * z := by group
    · rintro ⟨-, hm⟩
      refine Equiv.ext fun x => ?_
      rw [hρ, Equiv.Perm.coe_one, id_eq]
      have h1 : c m (ε.symm x) = ε.symm x := by
        apply Subtype.ext
        rw [hc]
        have h2 := Subgroup.mem_centralizer_iff.mp hm _ (ε.symm x).2
        rw [← h2]
        group
      rw [h1, Equiv.apply_symm_apply]
  have hHM : H0 M Z ≤ M := inf_le_left
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv] at hcard
  have hrel := Subgroup.relIndex_mul_card (H := H0 M Z) (K := M)
  rw [inf_eq_left.mpr hHM] at hrel
  have hidx : (H0 M Z).relIndex M = Nat.card ρ.range := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(H0 M Z))) ?_
    rw [hrel, ← hcard, mul_comm]
  have hdvd : Nat.card ρ.range ∣ Nat.card (semilinearPerm K K) := Subgroup.card_dvd_of_le hrange
  have hle := factorization_card_semilinearPerm_le (K := K) (E := K) hf1 hK (Module.finrank_self K)
  have hle' := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvd 2
  rw [hidx]
  simp only [Nat.sub_self, mul_zero, Nat.zero_div, zero_add] at hle
  exact hle'.trans hle

end Frob

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem descendAut_injective_of_two_le {K : Type} [Field K] [Finite K] (hn : 2 ≤ n)
    (h4 : 4 ≤ Nat.card K) :
    Function.Injective (LocalAnalysis.ComponentInitial.LinearFlag.descendAut n K) := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin n) K) := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      haveI : Fintype K := Fintype.ofFinite K
      have hcard : 4 ≤ (Finset.univ : Finset K).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact h4
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) hcard
      exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩
    · exact CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect h3
  haveI : Group.IsPerfect (SpecialLinearGroup (Fin n) K) := hperf
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro e he
  rw [MonoidHom.mem_ker] at he
  rw [Subgroup.mem_bot]
  refine CFSG.RankThree.PartTwo.KFacts.eq_one_of_forall_mul_inv_mem_center (τ := e) fun s => ?_
  have h := congrArg (fun φ : MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) =>
    φ (LocalAnalysis.ComponentInitial.LinearFlag.proj n K s)) he
  simp only [LocalAnalysis.ComponentInitial.LinearFlag.descendAut_proj, MulAut.one_apply] at h
  rw [LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_proj_iff,
    LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center] at h
  have := (Subgroup.center (SpecialLinearGroup (Fin n) K)).inv_mem h
  simpa using this

theorem card_outer_projectiveSL_dvd {K : Type} [Field K] {f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    Nat.card (Outer (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)) ∣
      2 * f * Nat.gcd n (2 ^ f - 1) := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    let e : LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 K ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
      QuotientGroup.quotientMulEquivOfEq
        (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 K)
    have hout := (LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
      Nat.prime_two K hK).2 (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 K) ⟨e⟩
    exact hout.trans ⟨2, by ring⟩
  · exact
      LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
        Nat.prime_two hf h3 hK

theorem _root_.CFSG.RankThree.GF2n.Smith81.LinSetup.centDvdN_two
    (hS : LinSetup M Q Z B n V₁ V₂) :
    CentDvdN 2 M Q Z (Lgen M (LB M Q B)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcent⟩ := hS
  exact hcent

private theorem ker_descendAut_outAct_le {G : Type} [Group G] {L Q H C : Subgroup G}
    {K : Type} [Field K] {n : ℕ} [(Q.subgroupOf L).Normal]
    (hRL : H ≤ Subgroup.normalizer (L : Set G))
    (hRN : ∀ r ∈ H, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q)
    (hCmem : ∀ h, h ∈ C ↔ h ∈ H ∧ ∀ x ∈ L, ⁅h, x⁆ ∈ Q)
    (E : ↥L ⧸ Q.subgroupOf L ≃* SpecialLinearGroup (Fin n) K)
    (hinj : Function.Injective (LocalAnalysis.ComponentInitial.LinearFlag.descendAut n K)) :
    ((LocalAnalysis.ComponentInitial.LinearFlag.descendAut n K).comp
      ((MulAut.congr E).toMonoidHom.comp
        (LocalAnalysis.EvenBN.U5.Lin43Out.outAct (N := Q) hRL hRN))).ker ≤
      C.subgroupOf H := by
  let act := LocalAnalysis.EvenBN.U5.Lin43Out.outAct (N := Q) hRL hRN
  change ((LocalAnalysis.ComponentInitial.LinearFlag.descendAut n K).comp
    ((MulAut.congr E).toMonoidHom.comp act)).ker ≤ C.subgroupOf H
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : act x = 1 := by
    have h2 : (MulAut.congr E) (act x) = 1 :=
      hinj (hx.trans (map_one _).symm)
    exact (MulAut.congr E).injective (h2.trans (map_one _).symm)
  rw [Subgroup.mem_subgroupOf, hCmem]
  refine ⟨x.2, fun y hy => ?_⟩
  have h3 := congrArg (fun α : MulAut (↥L ⧸ Q.subgroupOf L) =>
      α ((⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : ↥L) : ↥L ⧸ Q.subgroupOf L)) h1
  simp only [act, LocalAnalysis.EvenBN.U5.Lin43Out.outAct_mk, MulAut.one_apply] at h3
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv,
    LocalAnalysis.EvenBN.U5.Lin43Out.conjL_coe] at h3
  have e1 : ⁅(x : G), y⁆ = ((x : G) * y⁻¹ * (x : G)⁻¹)⁻¹ * y⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e1]
  exact h3

private theorem factorization_ker_le_of_dvd {k c f n : ℕ}
    (hk : k ∣ 2 ^ (f * (2 * n + 1)) * (c * (2 ^ f - 1)))
    (hc0 : c ≠ 0) (hm1 : 2 ^ f - 1 ≠ 0) (hodd : ¬ 2 ∣ 2 ^ f - 1) :
    k.factorization 2 ≤ f * (2 * n + 1) + c.factorization 2 := by
  have hpow : 2 ^ (f * (2 * n + 1)) ≠ 0 := by positivity
  have hcq : c * (2 ^ f - 1) ≠ 0 := mul_ne_zero hc0 hm1
  have hb : 2 ^ (f * (2 * n + 1)) * (c * (2 ^ f - 1)) ≠ 0 := mul_ne_zero hpow hcq
  have hk0 : k ≠ 0 := fun h0 => hb (Nat.eq_zero_of_zero_dvd (h0 ▸ hk))
  have h := (Nat.factorization_le_iff_dvd hk0 hb).mpr hk 2
  rw [Nat.factorization_mul hpow hcq, Finsupp.add_apply,
    Nat.factorization_mul hc0 hm1, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd] at h
  omega

private theorem factorization_range_le_of_dvd {k f n : ℕ}
    (hk : k ∣ (2 * f * Nat.gcd n (2 ^ f - 1)) * ordSL n (2 ^ f))
    (hOut0 : 2 * f * Nat.gcd n (2 ^ f - 1) ≠ 0)
    (hS0 : ordSL n (2 ^ f) ≠ 0)
    (hd0 : Nat.gcd n (2 ^ f - 1) ≠ 0)
    (hdodd : ¬ 2 ∣ Nat.gcd n (2 ^ f - 1))
    (hf1 : 1 ≤ f) :
    k.factorization 2 ≤ 1 + f.factorization 2 + f * (n * (n - 1) / 2) := by
  have hb : (2 * f * Nat.gcd n (2 ^ f - 1)) * ordSL n (2 ^ f) ≠ 0 :=
    mul_ne_zero hOut0 hS0
  have hk0 : k ≠ 0 := fun h0 => hb (Nat.eq_zero_of_zero_dvd (h0 ▸ hk))
  have h := (Nat.factorization_le_iff_dvd hk0 hb).mpr hk 2
  rw [Nat.factorization_mul hOut0 hS0, Finsupp.add_apply,
    Nat.factorization_mul (mul_ne_zero (by norm_num) (by omega)) hd0,
    Finsupp.add_apply, Nat.factorization_mul (by norm_num) (by omega),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hdodd, add_zero,
    factorization_ordSL_two hf1] at h
  omega

private theorem two_pow_sub_one_ne_zero_and_odd {f : ℕ} (hf1 : 1 ≤ f) :
    2 ^ f - 1 ≠ 0 ∧ ¬ 2 ∣ 2 ^ f - 1 := by
  have hq2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  refine ⟨?_, ?_⟩
  · have : 2 ≤ 2 ^ f := Nat.le_of_dvd (by positivity) hq2
    omega
  · intro h
    exact (Nat.not_even_iff_odd.mpr
      (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := f) (by omega)))
      (even_iff_two_dvd.mpr h)

private theorem ordSL_two_pow_ne_zero {n f : ℕ} (hf1 : 1 ≤ f) :
    ordSL n (2 ^ f) ≠ 0 := by
  have hq2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  rw [ordSL]
  refine mul_ne_zero (by positivity) (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
  have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  have : 2 ≤ (2 ^ f) ^ j := le_trans (Nat.le_of_dvd (by positivity) hq2)
    (Nat.le_self_pow (by omega) _)
  omega

private theorem exists_action_ker_le {K : Type} [Field K] [Finite K] (hc : Ctx M Q Z B)
    (hKZ : Nat.card K = Nat.card Z) (φ : Lgen M (LB M Q B) →* GL (Fin n) K)
    (hker : φ.ker = Q.subgroupOf (Lgen M (LB M Q B)))
    (hrange : φ.range = StatedSL n K) (hn : 2 ≤ n) {C : Subgroup G}
    (hCmem : ∀ h, h ∈ C ↔ h ∈ H0 M Z ∧ ∀ x ∈ Lgen M (LB M Q B), ⁅h, x⁆ ∈ Q) :
    ∃ Ψ : ↥(H0 M Z) →* MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K),
      Ψ.ker ≤ C.subgroupOf (H0 M Z) := by
  have hNM : H0 M Z ≤ M := inf_le_left
  have hRL : H0 M Z ≤ Subgroup.normalizer (Lgen M (LB M Q B) : Set G) :=
    hNM.trans (Lgen_normalizes M _)
  have hRN : ∀ r ∈ H0 M Z, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := fun r hr x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hNM hr)) x).mp hx
  haveI : (Q.subgroupOf (Lgen M (LB M Q B))).Normal := hker ▸ φ.normal_ker
  let act := LocalAnalysis.EvenBN.U5.Lin43Out.outAct (N := Q) hRL hRN
  let e₀ : SpecialLinearGroup (Fin n) K ≃* ↥(StatedSL n K) :=
    (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (StatedAPI.statedSL_eq_range_toGL n K).symm)
  let E : ↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)) ≃*
      SpecialLinearGroup (Fin n) K :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))).trans
      e₀.symm
  let Ψ : ↥(H0 M Z) →* MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) :=
    (LocalAnalysis.ComponentInitial.LinearFlag.descendAut n K).comp
      ((MulAut.congr E).toMonoidHom.comp act)
  refine ⟨Ψ, ?_⟩
  exact ker_descendAut_outAct_le hRL hRN hCmem E
    (descendAut_injective_of_two_le (n := n) (K := K) hn (by rw [hKZ]; exact hc.hyp.q4))

theorem factorization_card_H0_le_of_centDvdN (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 2 ≤ n) {c : ℕ} (hc0 : c ≠ 0) (hcent : CentDvdN c M Q Z (Lgen M (LB M Q B))) {f : ℕ}
    (hf : Nat.card Z = 2 ^ f) :
    (Nat.card (H0 M Z)).factorization 2 ≤
      f * (2 * n + 1) + f * (n * (n - 1) / 2) + f.factorization 2 + 1 + c.factorization 2 := by
  classical
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hS.width hc.hyp
  obtain ⟨K, _, _, hKZ, φ, hrange, hker, -, -, -, -, -, -, -, -, -, -⟩ := hS
  obtain ⟨C, -, hCH, hCmem, hCdvd⟩ := hcent
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr fun h0 => by
    have := hc.hyp.q4
    rw [hf, h0, pow_zero] at this
    norm_num at this
  have hK : Nat.card K = 2 ^ f := hKZ.trans hf
  obtain ⟨Ψ, hkerΨ⟩ := exists_action_ker_le hc hKZ φ hker hrange hn hCmem
  have hcard := Subgroup.card_ker_mul_card_range Ψ
  haveI : Finite (MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)) :=
    Finite.of_injective
      (fun α : MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) =>
        (α : LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K →
          LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)) DFunLike.coe_injective
  have hkdvd : Nat.card Ψ.ker ∣ Nat.card C := by
    have h := Subgroup.card_dvd_of_le hkerΨ
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv] at h
  have hrdvd : Nat.card Ψ.range ∣
      Nat.card (Outer (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)) *
        Nat.card (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) := by
    refine (Subgroup.card_subgroup_dvd_card Ψ.range).trans ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (inner (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K))]
    exact mul_dvd_mul_left _ (Subgroup.card_range_dvd _)
  have hT : Nat.card (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) ∣
      ordSL n (2 ^ f) := by
    have h := Subgroup.card_quotient_dvd_card
      (LocalAnalysis.ComponentInitial.LinearFlag.scalars n K)
    rw [LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), hK] at h
    exact h
  have hOut : Nat.card (Outer (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)) ∣
      2 * f * Nat.gcd n (2 ^ f - 1) :=
    card_outer_projectiveSL_dvd (n := n) (K := K) (f := f) hn hf1 hK
  obtain ⟨hqm1, hodd⟩ := two_pow_sub_one_ne_zero_and_odd hf1
  have hd0 : Nat.gcd n (2 ^ f - 1) ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have hdodd : ¬ 2 ∣ Nat.gcd n (2 ^ f - 1) := fun h2 => hodd (h2.trans (Nat.gcd_dvd_right _ _))
  have hS0 : ordSL n (2 ^ f) ≠ 0 := ordSL_two_pow_ne_zero hf1
  have hOut0 : 2 * f * Nat.gcd n (2 ^ f - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) hd0
  have hker0 : Nat.card Ψ.ker ≠ 0 := Nat.card_pos.ne'
  have hran0 : Nat.card Ψ.range ≠ 0 := Nat.card_pos.ne'
  have hkerdvd : Nat.card Ψ.ker ∣
      2 ^ (f * (2 * n + 1)) * (c * (2 ^ f - 1)) := by
    have h := hkdvd.trans hCdvd
    rw [hw, hf, ← pow_mul] at h
    exact h
  have hk : (Nat.card Ψ.ker).factorization 2 ≤
      f * (2 * n + 1) + c.factorization 2 :=
    factorization_ker_le_of_dvd hkerdvd hc0 hqm1 hodd
  have hr : (Nat.card Ψ.range).factorization 2 ≤
      1 + f.factorization 2 + f * (n * (n - 1) / 2) :=
    factorization_range_le_of_dvd (hrdvd.trans (mul_dvd_mul hOut hT)) hOut0 hS0 hd0 hdodd hf1
  have hv : (Nat.card Ψ.ker * Nat.card Ψ.range).factorization 2 =
      (Nat.card Ψ.ker).factorization 2 + (Nat.card Ψ.range).factorization 2 := by
    rw [Nat.factorization_mul hker0 hran0, Finsupp.add_apply]
  rw [← hcard, hv]
  omega

theorem factorization_card_le_lin_of_centDvdN (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 2 ≤ n) {c : ℕ} (hc0 : c ≠ 0)
    (hcent : CentDvdN c M Q Z (Lgen M (LB M Q B))) {f : ℕ} (hf : Nat.card Z = 2 ^ f) :
    (Nat.card G).factorization 2 ≤
      f * (2 * n + 1) + f * (n * (n - 1) / 2) + 2 * f.factorization 2 + 1 + c.factorization 2 := by
  rw [← factorization_card_M_eq hc.hyp]
  have h1 := factorization_relIndex_H0_le hc.hyp hf
  have h2 := factorization_card_H0_le_of_centDvdN hc hS hn hc0 hcent hf
  have hHM : H0 M Z ≤ M := inf_le_left
  have hrel := Subgroup.relIndex_mul_card (H := H0 M Z) (K := M)
  rw [inf_eq_left.mpr hHM] at hrel
  have hr0 : (H0 M Z).relIndex M ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hrel
    exact Nat.card_pos.ne' hrel.symm
  rw [← hrel, Nat.factorization_mul hr0 Nat.card_pos.ne', Finsupp.add_apply]
  omega

end CFSG.RankThree.GF2n.Smith81.Insp

module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentTau
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Borel
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Tor
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3L21
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3L26
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Ker
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65
import CFSG.RankThree.PartTwo.Sec15.Sylow155Swap
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1TLeN
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.PGLModel (projSU)
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

private theorem res1U3_centralizer_le_res1C (A L : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤ Res1C A L := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun b hb =>
    Subgroup.mem_centralizer_iff.mp hx b (Subgroup.mem_inf.mp hb).1

private theorem res1U3_conjNormal_eq_one_iff {Q : Type*} [Group Q] {N : Subgroup Q} [N.Normal]
    (x : Q) : (MulAut.conjNormal x : MulAut ↥N) = 1 ↔ ∀ y ∈ N, x * y = y * x := by
  constructor
  · intro h y hy
    have h1 : (MulAut.conjNormal x : MulAut ↥N) ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [h]; rfl
    have h2 := congrArg Subtype.val h1
    simp only [MulAut.conjNormal_apply] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  · intro h
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply, h y y.2, mul_inv_cancel_right]

private theorem res1U3_orderOf_point {A : Subgroup G} {c : G} {L : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) {c' : ↥(Res1C A L)}
    (hc'Y : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈ Yc) (hc' : (c' : G) = c) :
    orderOf (⟨_, hc'Y⟩ : ↥Yc) = 3 := by
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(Res1C A L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hcmem := zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hcmem.2.1
  have hcc : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'] using hcc)
  have hy3 : (⟨_, hc'Y⟩ : ↥Yc) ^ 3 = 1 := by
    apply Subtype.ext
    show QuotientGroup.mk' _ c' ^ 3 = 1
    rw [← map_pow, hc'3, map_one]
  refine orderOf_eq_prime hy3 fun h => ?_
  have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' = 1 := congrArg Subtype.val h
  have hcN : c' ∈ CFSG.pPrimeCore 3 ↥(Res1C A L) := (QuotientGroup.eq_one_iff c').mp h1
  have hc'1 : c' = 1 :=
    Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_three hN hcN (a := 1) (by simpa using hc'3)
  have hc1 : c = 1 := by rw [← hc', hc'1]; rfl
  rw [hc1, orderOf_one] at hc3
  omega

private theorem res1U3_comm_point {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    {c' x : ↥(Res1C A L)} (hc' : (c' : G) = c)
    (hx : (x : G) ∈ Subgroup.centralizer (A : Set G)) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (x : G) * (c' : G) = (c' : G) * (x : G)
  rw [hc']
  exact (Subgroup.mem_centralizer_iff.mp hx c hcA).symm

private theorem res1U3_conj_mem_pPrimeCoreOf {H : Subgroup G} {h x : G} (hh : h ∈ H)
    (hx : x ∈ pPrimeCoreOf 2 H) : h * x * h⁻¹ ∈ pPrimeCoreOf 2 H := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  exact ⟨⟨h, hh⟩ * x₀ * ⟨h, hh⟩⁻¹,
    (inferInstance : (CFSG.pPrimeCore 2 ↥H).Normal).conj_mem x₀ hx₀ ⟨h, hh⟩, rfl⟩

private theorem res1U3_conj_injective {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [← hZ, Subgroup.mem_center_iff]
  intro w
  have h := congrArg (fun α : MulAut Y => α w) (MonoidHom.mem_ker.mp hz)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

private theorem res1U3_five_le {n p : ℕ} (hn : 0 < n) (heven : Even n) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ n + 1) : 5 ≤ p := by
  have h3 : 2 ^ n % 3 = 1 := CFSG.two_pow_mod_three_of_even heven
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
  have hp2 := hp.two_le
  by_contra hlt
  have hlt' : p < 5 := by omega
  interval_cases p
  · omega
  · omega
  · exact absurd hp (by norm_num)

theorem res1ZExclLeN_su3_of_centLeM_gen
    (h142 : Concl142S14)
    {Q : ∀ (X : Type) [Group X], Prop} (hcent : Res1CentLeMN Q Res1OpenSU3Type) :
    Res1ZExclLeN Q Res1OpenSU3Type := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX hLΔ hKX hΩ hMX hMO hE0N z hz2 hzV hzC hzR hAz hKz hCN hJ
  obtain ⟨n, hn, heven, ⟨e⟩⟩ := hP
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := heven
    omega
  set H := delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) with hHdef
  set Ob := pPrimeCoreOf 2 H with hObdef
  have hY' := hY
  obtain ⟨hhyp, -, -, hYc, -⟩ := hY'
  have hYc' := hYc
  obtain ⟨hYcomp, hcY, -⟩ := hYc'
  haveI hYn : Yc.Normal := res1_isComponent_normal hS hhyp hYcomp
  set C := Res1C A L with hCdef
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) with hπdef
  let ρ : ↥C →* MulAut ↥Yc := (MulAut.conjNormal : Res1Q A L →* MulAut ↥Yc).comp π
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).1
  obtain ⟨c', hc'Y, hc'⟩ := hcY
  have hc'val : (c' : G) = c := hc'
  set x : ↥Yc := ⟨π c', hc'Y⟩ with hxdef
  have hx : orderOf x = 3 := res1U3_orderOf_point hS hc'Y hc'val
  have hfixx : ∀ u : ↥C, (u : G) ∈ Subgroup.centralizer (A : Set G) → ρ u x = x := by
    intro u hu
    apply Subtype.ext
    show π u * π c' * (π u)⁻¹ = π c'
    rw [mul_inv_eq_iff_eq_mul]
    exact res1U3_comm_point hcA hc'val hu
  have hOA : Ob ≤ Subgroup.centralizer (A : Set G) := by
    rw [← hEO]
    exact hEA
  have hzA : z ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hAz ha)
  obtain ⟨-, hRH, -, -⟩ := Sylow155B1.delta_host_facts hS h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  have hzH : z ∈ H := hRH hzR
  set J := ⁅Ob, Subgroup.zpowers z⁆ with hJdef
  have hJA : J ≤ Subgroup.centralizer (A : Set G) := by
    rw [hJdef, Subgroup.commutator_le]
    intro o ho g hg
    have hg' : g ∈ Subgroup.centralizer (A : Set G) := (Subgroup.zpowers_le.mpr hzA) hg
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hOA ho) hg') (inv_mem (hOA ho))) (inv_mem hg')
  have hJO : J ≤ Ob := by
    rw [hJdef, Subgroup.commutator_le]
    intro o ho g hg
    have hgH : g ∈ H := (Subgroup.zpowers_le.mpr hzH) hg
    have h1 := res1U3_conj_mem_pPrimeCoreOf hgH (inv_mem ho)
    rw [commutatorElement_def, show o * g * o⁻¹ * g⁻¹ = o * (g * o⁻¹ * g⁻¹) by group]
    exact mul_mem ho h1
  obtain ⟨⟨j₀, hj₀J⟩, hj₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJ
  have hj₀1' : j₀ ≠ 1 := fun h => hj₀1 (Subtype.ext h)
  have ho1 : orderOf j₀ ≠ 1 := fun h => hj₀1' (orderOf_eq_one_iff.mp h)
  set p := (orderOf j₀).minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime ho1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpo : p ∣ orderOf j₀ := Nat.minFac_dvd _
  have ho0 : orderOf j₀ ≠ 0 := (orderOf_pos j₀).ne'
  set j₁ := j₀ ^ (orderOf j₀ / p) with hj₁def
  have hj₁p : orderOf j₁ = p := orderOf_pow_orderOf_div ho0 hpo
  have hj₁J : j₁ ∈ J := J.pow_mem hj₀J _
  have hj₁1 : j₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hj₁p
    exact hp.one_lt.ne hj₁p
  have hj₁C : j₁ ∈ C := res1U3_centralizer_le_res1C A L (hJA hj₁J)
  have hzC' : z ∈ C := res1U3_centralizer_le_res1C A L hzA
  have hOC : Ob ≤ C := hOA.trans (res1U3_centralizer_le_res1C A L)
  set j : ↥C := ⟨j₁, hj₁C⟩ with hjdef
  set z' : ↥C := ⟨z, hzC'⟩ with hz'def
  set O' : Subgroup ↥C := Ob.subgroupOf C with hO'def
  have hjp : orderOf j = p := (Subgroup.orderOf_coe j).symm.trans hj₁p
  have hmapJ : (⁅O', Subgroup.zpowers z'⁆).map C.subtype = J := by
    rw [Subgroup.map_commutator, hO'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hOC,
      MonoidHom.map_zpowers]
    rfl
  have hjJ' : j ∈ ⁅O', Subgroup.zpowers z'⁆ := by
    rw [← Subgroup.mem_map_iff_mem C.subtype_injective, hmapJ]
    exact hj₁J
  have hq3 : 2 ^ n % 3 = 1 := CFSG.two_pow_mod_three_of_even heven
  have hq2 : 2 < 2 ^ n :=
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hZ : Subgroup.center ↥Yc = ⊥ := res1U3_center_eq_bot (by omega) e
  have hI : ∀ σ τ : MulAut ↥Yc, KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) :=
    KFacts.isInnerAut_commutator_of_mulEquiv_unitaryPSU (Sec4.unitaryFieldData_galoisField 2 n hn)
      hq3 hq2 (e.trans (Sec4.projSUEquivUnitaryPSU 2 n (Sec4.unitaryFieldData_galoisField 2 n hn)))
  have hCx : ∀ a b : ↥Yc, a * x = x * a → b * x = x * b → a * b = b * a :=
    fun a b ha hb => res1U3_commute_of_commute hn heven e hx ha hb
  have hzz : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have hz2' : z' ^ 2 = 1 := Subtype.ext hzz
  have hOx : ∀ o ∈ O', ρ o x = x := fun o ho => hfixx o (hOA (Subgroup.mem_subgroupOf.mp ho))
  have hzx : ρ z' x = x := hfixx z' hzA
  obtain ⟨w, hρw, hwx, hzw⟩ :=
    res1U3_exists_conj_of_mem_commutator hZ hI hCx ρ hz2' hOx hzx hjJ'
  have hρj : ρ j ≠ 1 := by
    intro h1
    have hc := (res1U3_conjNormal_eq_one_iff (π j)).mp h1
    have := hcomm j (hJO hj₁J) hc
    exact hj₁1 (congrArg Subtype.val this)
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hρj (by rw [hρw, map_one])
  have hβ2 : ρ z' * ρ z' = 1 := by rw [← map_mul, ← pow_two, hz2', map_one]
  obtain ⟨hpow, S, hSw, ⟨eS⟩⟩ :=
    res1U3_exists_slTwo_le_centralizer hn heven e hx hwx hw1 hβ2 hzx hzw
  have hρjp : orderOf (ρ j) = p := by
    have hd : orderOf (ρ j) ∣ p := (orderOf_map_dvd ρ j).trans (dvd_of_eq hjp)
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hρj
    · exact h
  have hpdvd : p ∣ 2 ^ n + 1 := by
    rw [← hρjp]
    apply orderOf_dvd_of_pow_eq_one
    rw [hρw, ← map_pow, hpow, map_one]
  have hp5 : 5 ≤ p := res1U3_five_le hn heven hp hpdvd
  have hconj := res1U3_conj_injective hZ
  set S' : Subgroup (MulAut ↥Yc) := S.map MulAut.conj with hS'def
  have eS' : ↥S' ≃* projSL 2 (GaloisField 2 n) :=
    (S.equivMapOfInjective MulAut.conj hconj).symm.trans eS
  have hSj : S' ≤ Subgroup.centralizer {ρ j} := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hρw, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hSw hs)]
  have hIρ : (MulAut.conj : ↥Yc →* MulAut ↥Yc).range ≤ ρ.range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥C) (s : Res1Q A L)
    refine ⟨u, ?_⟩
    change MulAut.conjNormal (π u) = MulAut.conj s
    rw [hu]
    exact MulAut.conjNormal_val
  have hSI : S' ≤ (MulAut.conj : ↥Yc →* MulAut ↥Yc).range := Subgroup.map_le_range _ _
  have hSρ : S' ≤ ρ.range := hSI.trans hIρ
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  obtain ⟨B, hBsolv, hBmem⟩ := res1_rho_mem_borel hS hAM (h142 G A c L hS) hY hn heven e
  have hjM : Subgroup.centralizer ({j₁} : Set G) ≤ M :=
    hcent G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple
      ⟨n, hn, heven, ⟨e⟩⟩ hEA hEO hcomm hfield hLX hLΔ hKX hΩ hMX hMO hE0N z hz2 hzV hzC hzR hAz
      hKz hCN j₁ hj₁J hj₁1
  have hcentB : ∀ u ∈ Subgroup.centralizer {j}, ρ u ∈ B := by
    intro u hu
    refine hBmem u (hjM ?_)
    rw [Subgroup.mem_centralizer_singleton_iff] at hu ⊢
    exact congrArg Subtype.val hu
  have hjpg : IsPGroup p (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hjp, pow_one])
  have hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3 :=
    hS.toTheoremFourHyp.localRank_lt p hp (by omega)
  rcases Nat.lt_or_ge n 4 with h4 | h4
  ·
    have hn2' : n = 2 := by
      obtain ⟨k, hk⟩ := heven
      omega
    subst hn2'
    have hp5' : p = 5 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp (by simpa using hpdvd)
    have hker : ∀ k ∈ ρ.ker, ∃ a : ℕ, k ^ 3 ^ a ∈ CFSG.pPrimeCore 3 ↥C := by
      intro k hk
      have hkY : ∀ y ∈ Yc, π k * y = y * π k := (res1U3_conjNormal_eq_one_iff (π k)).mp hk
      obtain ⟨a, m, hm3, hom⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (π k)).ne' 3 (by norm_num)
      have hx1 : π k ^ 3 ^ a = 1 := by
        refine res1_eq_one_of_centralizes hS hhyp hYc hsimple ?_ fun y hy =>
          (Commute.pow_left (hkY y hy : Commute (π k) y) _).eq
        have hdvd : orderOf (π k ^ 3 ^ a) ∣ m := by
          apply orderOf_dvd_of_pow_eq_one
          rw [← pow_mul, ← hom, pow_orderOf_eq_one]
        exact Nat.Coprime.coprime_dvd_left hdvd
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
      refine ⟨a, (QuotientGroup.eq_one_iff _).mp ?_⟩
      change π (k ^ 3 ^ a) = 1
      rw [map_pow]
      exact hx1
    exact false_of_frattini_section_u34 (hp5' ▸ hloc) ρ (hp5' ▸ hjpg) eS'
      ((MonoidHom.ofInjective hconj).symm.trans e) hSj hSI hIρ hBsolv hcentB
      CFSG.pPrimeCore_coprime_card.symm hker
  rcases Nat.lt_or_ge n 6 with h6 | h6
  · have hn4' : n = 4 := by
      obtain ⟨k, hk⟩ := heven
      omega
    subst hn4'
    exact false_of_frattini_section_four (by omega) hloc ρ hjpg hSj hSρ hBsolv hcentB eS'
  · exact false_of_frattini_section hp5 hloc ρ hjpg hSj hSρ hBsolv hcentB h6 eS'

theorem res1ZExclLeN_su3_of_centLeM_five
    (h142 : Concl142S14)
    {Q : ∀ (X : Type) [Group X], Prop} (hcent : Res1CentLeMN Q Res1OpenSU3Type)
    (_h5 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
      (L X K Y M T P' : Subgroup G) (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau Q (fun Y _ => Nonempty (Y ≃* projSU 3 2 2)) A c L X K Y M T P' Yc z →
      res1J A X Y M z ≠ ⊥ → 5 ∣ Nat.card X ∧ ∀ x ∈ X, x ∈ Res1C A L → x ^ 5 = 1 → x = 1) :
    Res1ZExclLeN Q Res1OpenSU3Type :=
  res1ZExclLeN_su3_of_centLeM_gen h142 hcent

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

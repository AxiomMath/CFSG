module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent361
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Tau
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Lem154
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Cent
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Borel
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Tor
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3L21
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1V
import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJSyl
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.PGLModel (projSU)
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

private theorem res1U3T_commutator_le_left {R A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (R : Set G)) : ⁅R, A⁆ ≤ R := by
  rw [Subgroup.commutator_le]
  intro r hr a ha
  rw [show ⁅r, a⁆ = r * (a * r⁻¹ * a⁻¹) by rw [commutatorElement_def]; group]
  exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hA ha) r⁻¹).mp (R.inv_mem hr))

private theorem res1U3T_conj_mem_centralizer {O : Subgroup G} {x k : G}
    (hx : x ∈ Subgroup.normalizer (O : Set G)) (hk : k ∈ Subgroup.centralizer (O : Set G)) :
    x * k * x⁻¹ ∈ Subgroup.centralizer (O : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have ho' : x⁻¹ * o * x ∈ O := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) o).mp ho
    simpa using this
  have h := Subgroup.mem_centralizer_iff.mp hk _ ho'
  calc o * (x * k * x⁻¹) = x * ((x⁻¹ * o * x) * k) * x⁻¹ := by group
    _ = x * (k * (x⁻¹ * o * x)) * x⁻¹ := by rw [h]
    _ = (x * k * x⁻¹) * o := by group

private theorem res1U3T_commutator_le_of_decomp {R A K : Subgroup G}
    (hdec : R ≤ ⁅R, A⁆ ⊔ R ⊓ Subgroup.centralizer (A : Set G))
    (hKR : K ≤ R) (hKn : ∀ x ∈ R, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hRA : ⁅R, A⁆ ≤ K)
    (hCC : ∀ s ∈ R ⊓ Subgroup.centralizer (A : Set G), ∀ t ∈ R ⊓ Subgroup.centralizer (A : Set G),
      ⁅s, t⁆ ∈ K) :
    ⁅R, R⁆ ≤ K := by
  let cen : Set G → Subgroup G := fun T =>
    { carrier := {y | y ∈ R ∧ ∀ t ∈ T, ⁅t, y⁆ ∈ K}
      mul_mem' := fun {y₁ y₂} h₁ h₂ => ⟨R.mul_mem h₁.1 h₂.1, fun t ht => by
        have e : ⁅t, y₁ * y₂⁆ = ⁅t, y₁⁆ * (y₁ * ⁅t, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact K.mul_mem (h₁.2 t ht) (hKn y₁ h₁.1 _ (h₂.2 t ht))⟩
      one_mem' := ⟨R.one_mem, fun t _ => by simp⟩
      inv_mem' := fun {y} h => ⟨R.inv_mem h.1, fun t ht => by
        have e : ⁅t, y⁻¹⁆ = y⁻¹ * ⁅t, y⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hKn y⁻¹ (R.inv_mem h.1) _ (K.inv_mem (h.2 t ht))⟩ }
  have hRAcen : ∀ T : Set G, T ⊆ R → ⁅R, A⁆ ≤ cen T := by
    intro T hT u hu
    refine ⟨hKR (hRA hu), fun t ht => ?_⟩
    rw [commutatorElement_def]
    exact K.mul_mem (hKn t (hT ht) u (hRA hu)) (K.inv_mem (hRA hu))
  have hstageA : ∀ s ∈ R ⊓ Subgroup.centralizer (A : Set G), ∀ y ∈ R, ⁅s, y⁆ ∈ K := by
    intro s hs y hy
    have hle : R ≤ cen {s} := hdec.trans (sup_le (hRAcen {s} (by
        rintro _ rfl; exact hs.1)) (fun u hu => ⟨hu.1, fun t ht => by
          rw [Set.mem_singleton_iff.mp ht]; exact hCC s hs u hu⟩))
    exact (hle hy).2 s rfl
  have hle : R ≤ cen (R : Set G) := hdec.trans (sup_le (hRAcen (R : Set G) le_rfl)
    (fun s hs => ⟨hs.1, fun t ht => by
      have h := K.inv_mem (hstageA s hs t ht)
      rwa [commutatorElement_inv] at h⟩))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (hle hy).2 x hx

private theorem res1U3T_commutator_self_characteristic (R : Subgroup G) :
    ((⁅R, R⁆ : Subgroup G).subgroupOf R).Characteristic := by
  have hc : (⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆).Characteristic := inferInstance
  have hmap : (⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆).map R.subtype = ⁅R, R⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : (⁅R, R⁆ : Subgroup G).subgroupOf R = ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  rw [this]
  exact hc

private theorem res1U3T_conj_injective {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [← hZ, Subgroup.mem_center_iff]
  intro w
  have h := congrArg (fun α : MulAut Y => α w) (MonoidHom.mem_ker.mp hz)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

end Abstract

section U3

variable {P₀ : Type*} [Group P₀] {Y₀ : Type} [Group Y₀]

private theorem res1U3T_q_facts {n : ℕ} (hn : 0 < n) (heven : Even n) :
    2 ^ n % 3 = 1 ∧ 2 < 2 ^ n := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := heven
    omega
  exact ⟨CFSG.two_pow_mod_three_of_even heven,
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)⟩

private theorem res1U3T_isInnerAut_commutator {n : ℕ} (hn : 0 < n) (heven : Even n)
    (e : Y₀ ≃* projSU 3 2 n) (α β : MulAut Y₀) : KFacts.IsInnerAut (α * β * α⁻¹ * β⁻¹) :=
  KFacts.isInnerAut_commutator_of_mulEquiv_unitaryPSU (Sec4.unitaryFieldData_galoisField 2 n hn)
    (res1U3T_q_facts hn heven).1 (res1U3T_q_facts hn heven).2
    (e.trans (Sec4.projSUEquivUnitaryPSU 2 n (Sec4.unitaryFieldData_galoisField 2 n hn))) α β

private theorem res1U3T_comm_conj_of_fixed {n : ℕ} (hn : 0 < n) (heven : Even n)
    (e : Y₀ ≃* projSU 3 2 n) {α β : MulAut Y₀} {x : Y₀} (hα : α x = x) (hβ : β x = x) :
    ∃ y : Y₀, y * x = x * y ∧ α * β * α⁻¹ * β⁻¹ = MulAut.conj y := by
  obtain ⟨y, hy⟩ := res1U3T_isInnerAut_commutator hn heven e α β
  refine ⟨y, ?_, hy.symm⟩
  have hα' : α⁻¹ x = x := by
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
    exact hα.symm
  have hβ' : β⁻¹ x = x := by
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
    exact hβ.symm
  have h1 : (α * β * α⁻¹ * β⁻¹) x = x := by
    simp [MulAut.mul_apply, hα, hβ, hα', hβ']
  rw [← hy, MulAut.conj_apply] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem res1U3_rho_commutator_eq_one {n : ℕ} (hn : 0 < n) (heven : Even n)
    (e : Y₀ ≃* projSU 3 2 n) (ρ : P₀ →* MulAut Y₀) {x : Y₀} (hx : orderOf x = 3) {g₁ g₂ : P₀}
    (h₁ : ρ g₁ x = x) (h₂ : ρ g₂ x = x) {k : ℕ} (hk : ⁅g₁, g₂⁆ ^ (2 ^ k) = 1) :
    ρ ⁅g₁, g₂⁆ = 1 := by
  obtain ⟨y, hyx, hyeq⟩ := res1U3T_comm_conj_of_fixed hn heven e h₁ h₂
  have hyodd : Odd (orderOf y) := res1U3_odd_orderOf_of_commute hn heven e hx hyx
  have hρ : ρ ⁅g₁, g₂⁆ = MulAut.conj y := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hyeq
  have hd1 : orderOf (ρ ⁅g₁, g₂⁆) ∣ orderOf y := by
    rw [hρ]
    exact orderOf_map_dvd (MulAut.conj : Y₀ →* MulAut Y₀) y
  have hd2 : orderOf (ρ ⁅g₁, g₂⁆) ∣ 2 ^ k :=
    (orderOf_map_dvd ρ _).trans (orderOf_dvd_of_pow_eq_one hk)
  have hodd' : Odd (orderOf (ρ ⁅g₁, g₂⁆)) := Odd.of_dvd_nat hyodd hd1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  rw [← orderOf_eq_one_iff]
  rw [hj] at hodd' ⊢
  rcases j with _ | j
  · rfl
  · exfalso
    exact (Nat.not_even_iff_odd.mpr hodd') ((Nat.even_pow' (by omega)).mpr even_two)

end U3

section Tau

variable {G : Type} [Group G] [Finite G] {Q : ∀ (X : Type) [Group X], Prop}
  {P : ∀ (Y : Type) [Group Y], Prop} {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G}
  {Yc : Subgroup (Res1Q A L)} {z : G}

namespace Res1Tau

theorem exists_rho_fixed_point [Yc.Normal] (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    ∃ x : ↥Yc, orderOf x = 3 ∧ ∀ u : ↥(Res1C A L), (u : G) ∈ Subgroup.centralizer (A : Set G) →
      Liebeck155R1L2.res1L2Rho A L Yc u x = x := by
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp τ.std.zpowers_mem_omegaA).1
  obtain ⟨c', hc'Y, hc'⟩ := τ.at_of.2.2.2.1.2.1
  have hc'val : (c' : G) = c := hc'
  have hc'Y' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈ Yc :=
    Subgroup.mem_comap.mp hc'Y
  refine ⟨⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hc'Y'⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact Gagen155R1HJ.res1_orderOf_pi_c'_eq_three τ.std hc'val
  · intro u hu
    apply Subtype.ext
    show QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u)⁻¹ =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c'
    rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (u : G) * (c' : G) = (c' : G) * (u : G)
    rw [hc'val]
    exact (Subgroup.mem_centralizer_iff.mp hu c hcA).symm

theorem isMulCommutative_of_commutator_mem (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (hCC : ∀ r₁ ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G),
      ∀ r₂ ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G),
        ⁅r₁, r₂⁆ ∈ Subgroup.centralizer (res1Ob A X Y M : Set G)) :
    IsMulCommutative ↥(CFSG.Open.pCoreOf 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOA : res1Ob A X Y M ≤ Subgroup.centralizer (A : Set G) := τ.e_eq ▸ τ.e_le
  have hRO : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.normalizer (res1Ob A X Y M : Set G) :=
    τ.r_le_host.trans τ.host_le_normalizer_ob
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  set Ob := res1Ob A X Y M with hObdef
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := fun a ha =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y (τ.ctx.isY.1.1.1.2 ha)
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hA3 : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup τ.sec15.mem_partTwoF.1
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    obtain ⟨a, ha⟩ := hA3.exists_card_eq
    obtain ⟨b, hb⟩ := hR2.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have hsolv : Group.IsSolvable ↥R := by
    have := hR2.isNilpotent
    infer_instance
  have hdec : R ≤ ⁅R, A⁆ ⊔ R ⊓ Subgroup.centralizer (A : Set G) :=
    CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hAR hcop hsolv
  have hRcomm : ∀ s ∈ R, ∀ t ∈ R, ⁅s, t⁆ ∈ R := fun s hs t ht => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hs ht) (R.inv_mem hs)) (R.inv_mem ht)
  have hKn : ∀ x ∈ R, ∀ k ∈ R ⊓ Subgroup.centralizer (Ob : Set G),
      x * k * x⁻¹ ∈ R ⊓ Subgroup.centralizer (Ob : Set G) := fun x hx k hk =>
    ⟨R.mul_mem (R.mul_mem hx hk.1) (R.inv_mem hx), res1U3T_conj_mem_centralizer (hRO hx) hk.2⟩
  have hRA : ⁅R, A⁆ ≤ R ⊓ Subgroup.centralizer (Ob : Set G) :=
    le_inf (res1U3T_commutator_le_left hAR)
      (Liebeck155R1L2.res1L2_commutator_r_a_centralizes_ob hOA hRO)
  have hCC' : ∀ s ∈ R ⊓ Subgroup.centralizer (A : Set G),
      ∀ t ∈ R ⊓ Subgroup.centralizer (A : Set G),
        ⁅s, t⁆ ∈ R ⊓ Subgroup.centralizer (Ob : Set G) := fun s hs t ht =>
    ⟨hRcomm s hs.1 t ht.1, hCC s hs t ht⟩
  have hRR : ⁅R, R⁆ ≤ Subgroup.centralizer (Ob : Set G) :=
    (res1U3T_commutator_le_of_decomp hdec inf_le_left hKn hRA hCC').trans inf_le_right
  have hbot : ⁅R, R⁆ = ⊥ := by
    by_contra hne
    apply τ.ob_not_le
    have hle : ⁅R, R⁆ ≤ R := res1U3T_commutator_le_left Subgroup.le_normalizer
    have hclaim := τ.endN.claim ⁅R, R⁆ hne hle (res1U3T_commutator_self_characteristic R)
    have hQ : Ob ∈ scriptQ A (lB A) :=
      pPrimeCoreOf_two_host_mem_scriptQ τ.std τ.i146 τ.ctx τ.endN τ.r_le
    have hON : Ob ≤ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G) :=
      (Subgroup.le_centralizer_iff.mp hRR).trans (Subgroup.centralizer_le_normalizer _)
    exact (le_delta hQ hON).trans hclaim
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := Subgroup.commutator_mem_commutator a.2 b.2
  rw [hbot, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h

end Res1Tau

theorem res1JCyclic_su3 : Res1JCyclic Q Res1OpenSU3Type := by
  intro G _ _ A c L X K Y M T P' Yc z τ
  obtain ⟨n, hn, heven, ⟨e⟩⟩ := τ.p
  haveI : Yc.Normal := res1_isComponent_normal τ.std τ.at_of.1 τ.at_of.2.2.2.1.1
  set C := Res1C A L with hCdef
  set ρ := Liebeck155R1L2.res1L2Rho A L Yc with hρdef
  obtain ⟨x, hx, hfix⟩ := τ.exists_rho_fixed_point
  have hOA : res1Ob A X Y M ≤ Subgroup.centralizer (A : Set G) := τ.e_eq ▸ τ.e_le
  have hzA : z ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (τ.a_z ha)
  have hOC : res1Ob A X Y M ≤ C := hOA.trans (Liebeck155R1L2.res1L2_centralizer_le_res1C A L)
  have hzC : z ∈ C := Liebeck155R1L2.res1L2_centralizer_le_res1C A L hzA
  set z' : ↥C := ⟨z, hzC⟩ with hz'def
  set O' : Subgroup ↥C := (res1Ob A X Y M).subgroupOf C with hO'def
  set J' : Subgroup ↥C := ⁅O', Subgroup.zpowers z'⁆ with hJ'def
  have hmapJ : J'.map C.subtype = res1J A X Y M z := by
    rw [hJ'def, Subgroup.map_commutator, hO'def, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hOC, MonoidHom.map_zpowers]
    rfl
  have hJOb : res1J A X Y M z ≤ res1Ob A X Y M :=
    Liebeck155R1L2.res1L2_commutator_le τ.std τ.i146 τ.ctx τ.endN τ.r_le τ.z_r
  have hinj : ∀ u ∈ J', ρ u = 1 → u = 1 := by
    intro u hu h1
    have huJ : (u : G) ∈ res1J A X Y M z := by
      rw [← hmapJ]
      exact Subgroup.mem_map_of_mem C.subtype hu
    exact τ.comm u (hJOb huJ) ((Liebeck155R1L2.res1L2_rho_eq_one_iff u).mp h1)
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hZ : Subgroup.center ↥Yc = ⊥ := res1U3_center_eq_bot hn2 e
  have hconj := res1U3T_conj_injective hZ
  have hI : ∀ σ σ' : MulAut ↥Yc, KFacts.IsInnerAut (σ * σ' * σ⁻¹ * σ'⁻¹) :=
    res1U3T_isInnerAut_commutator hn heven e
  have hCx : ∀ a b : ↥Yc, a * x = x * a → b * x = x * b → a * b = b * a :=
    fun a b ha hb => res1U3_commute_of_commute hn heven e hx ha hb
  have hz2' : z' ^ 2 = 1 := Subtype.ext (by
    have h := pow_orderOf_eq_one z
    rwa [τ.z_two] at h)
  have hOx : ∀ o ∈ O', ρ o x = x := fun o ho => hfix o (hOA (Subgroup.mem_subgroupOf.mp ho))
  have hzx : ρ z' x = x := hfix z' hzA
  have hβ2 : ρ z' * ρ z' = 1 := by rw [← map_mul, ← pow_two, hz2', map_one]
  set H : Subgroup ↥Yc := (J'.map ρ).comap MulAut.conj with hHdef
  have hH : ∀ w ∈ H, w * x = x * w ∧ ρ z' w = w⁻¹ := by
    intro w hw
    obtain ⟨j, hj, hjw⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hw)
    obtain ⟨w', hρw', hw'x, hzw'⟩ :=
      res1U3_exists_conj_of_mem_commutator hZ hI hCx ρ hz2' hOx hzx hj
    have hww' : w = w' := hconj (hjw.symm.trans hρw')
    rw [hww']
    exact ⟨hw'x, hzw'⟩
  haveI : IsCyclic ↥H := res1U3_isCyclic_of_inv hn heven e hx hβ2 hzx H hH
  have hJH : ∀ u ∈ J', ρ u ∈ H.map (MulAut.conj : ↥Yc →* MulAut ↥Yc) := by
    intro u hu
    obtain ⟨w, hρw, -, -⟩ := res1U3_exists_conj_of_mem_commutator hZ hI hCx ρ hz2' hOx hzx hu
    refine Subgroup.mem_map.mpr ⟨w, Subgroup.mem_comap.mpr ?_, hρw.symm⟩
    rw [← hρw]
    exact Subgroup.mem_map_of_mem ρ hu
  let ρJ : ↥J' →* ↥(H.map (MulAut.conj : ↥Yc →* MulAut ↥Yc)) :=
    (ρ.comp J'.subtype).codRestrict _ (fun u => hJH u u.2)
  have hρJ : Function.Injective ρJ := by
    refine (injective_iff_map_eq_one ρJ).mpr fun u hu => ?_
    have h2 : ρ (u : ↥C) = 1 := congrArg Subtype.val hu
    exact Subtype.ext (hinj u u.2 h2)
  let ψ : ↥J' →* ↥H :=
    (Subgroup.equivMapOfInjective H (MulAut.conj : ↥Yc →* MulAut ↥Yc)
      hconj).symm.toMonoidHom.comp ρJ
  have hψ : Function.Injective ψ := fun a b h =>
    hρJ ((Subgroup.equivMapOfInjective H (MulAut.conj : ↥Yc →* MulAut ↥Yc)
      hconj).symm.injective h)
  haveI : IsCyclic ↥J' := isCyclic_of_injective ψ hψ
  rw [← hmapJ]
  exact isCyclic_of_surjective (J'.equivMapOfInjective C.subtype C.subtype_injective)
    (MulEquiv.surjective _)

theorem res1Lem154_su3 : Res1Lem154 Q Res1OpenSU3Type := by
  intro G _ _ A c L X K Y M T P' Yc z τ
  obtain ⟨n, hn, heven, ⟨e⟩⟩ := τ.p
  haveI : Yc.Normal := res1_isComponent_normal τ.std τ.at_of.1 τ.at_of.2.2.2.1.1
  obtain ⟨x, hx, hfix⟩ := τ.exists_rho_fixed_point
  have hOA : res1Ob A X Y M ≤ Subgroup.centralizer (A : Set G) := τ.e_eq ▸ τ.e_le
  have hOC : res1Ob A X Y M ≤ Res1C A L :=
    hOA.trans (Liebeck155R1L2.res1L2_centralizer_le_res1C A L)
  have hRO : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.normalizer (res1Ob A X Y M : Set G) :=
    τ.r_le_host.trans τ.host_le_normalizer_ob
  refine τ.isMulCommutative_of_commutator_mem fun r₁ h₁ r₂ h₂ => ?_
  let u₁ : ↥(Res1C A L) := ⟨r₁, Liebeck155R1L2.res1L2_centralizer_le_res1C A L h₁.2⟩
  let u₂ : ↥(Res1C A L) := ⟨r₂, Liebeck155R1L2.res1L2_centralizer_le_res1C A L h₂.2⟩
  have hcomm_mem : ⁅r₁, r₂⁆ ∈ CFSG.Open.pCoreOf 2 Y := by
    rw [commutatorElement_def]
    exact (CFSG.Open.pCoreOf 2 Y).mul_mem ((CFSG.Open.pCoreOf 2 Y).mul_mem
      ((CFSG.Open.pCoreOf 2 Y).mul_mem h₁.1 h₂.1) (inv_mem h₁.1)) (inv_mem h₂.1)
  have hR2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  obtain ⟨k, hk⟩ := hR2 ⟨⁅r₁, r₂⁆, hcomm_mem⟩
  have hk' : ⁅u₁, u₂⁆ ^ (2 ^ k) = 1 := by
    have h1 := congrArg (fun w : ↥(CFSG.Open.pCoreOf 2 Y) => (w : G)) hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact h1
  have hρ := res1U3_rho_commutator_eq_one hn heven e (Liebeck155R1L2.res1L2Rho A L Yc) hx
    (hfix u₁ h₁.2) (hfix u₂ h₂.2) hk'
  exact Liebeck155R1L2.res1L2_ker_rho_centralizes_ob hOC
    (fun u hu h1 => τ.comm u hu ((Liebeck155R1L2.res1L2_rho_eq_one_iff u).mp h1)) hρ
    (hRO hcomm_mem)

end Tau

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

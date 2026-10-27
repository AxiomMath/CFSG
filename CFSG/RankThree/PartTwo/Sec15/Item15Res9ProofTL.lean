module

public import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofGen
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofRead
import CFSG.RankThree.PartTwo.Sec15.Item15Res9ProofTorusPf
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTransOut
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith
import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof15Res9

section Theta

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem inSubgroup_theta_le_of_le_normalizer {N M : Subgroup Γ} (hNM : N ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set Γ)) :
    inSubgroup (aschbacherSolvableCore 3) N ≤ inSubgroup (aschbacherSolvableCore 3) M := by
  set Θ := inSubgroup (aschbacherSolvableCore 3) N with hΘ
  obtain ⟨hsolv, hchar, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥N) Nat.prime_three
  have hΘN : Θ ≤ N := Subgroup.map_subtype_le _
  have hΘM : Θ ≤ M := hΘN.trans hNM
  have hMΘ : M ≤ Subgroup.normalizer (Θ : Set Γ) :=
    hMN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hnorm : (Θ.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΘM).mpr hMΘ
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have hsolvΘ : Group.IsSolvable Θ := by
    rw [hΘ, inSubgroup]
    exact Group.isSolvable_of_surjective ((N.subtype).subgroupMap_surjective _)
  have hsolv' : Group.IsSolvable (Θ.subgroupOf M) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hΘM).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hΘM).symm.surjective
  have h3' : ¬ 3 ∣ Nat.card (Θ.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΘM).toEquiv, hΘ, inSubgroup,
      Subgroup.card_map_of_injective N.subtype_injective]
    exact h3
  calc Θ = (Θ.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hΘM).symm
    _ ≤ (aschbacherSolvableCore 3 ↥M).map M.subtype :=
        Subgroup.map_mono (hmax _ hnorm hsolv' h3')

theorem le_inSubgroup_theta_of_isPGroup {V C : Subgroup Γ} (hV2 : IsPGroup 2 V) (hVC : V ≤ C)
    (hCV : C ≤ Subgroup.normalizer (V : Set Γ)) :
    V ≤ inSubgroup (aschbacherSolvableCore 3) C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (V.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVC).mpr hCV
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  have hp : IsPGroup 2 (V.subgroupOf C) := hV2.comap_subtype
  have : Group.IsNilpotent (V.subgroupOf C) := hp.isNilpotent
  have h3 : ¬ 3 ∣ Nat.card (V.subgroupOf C) := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  calc V = (V.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hVC).symm
    _ ≤ (aschbacherSolvableCore 3 ↥C).map C.subtype :=
        Subgroup.map_mono (hmax _ hnorm inferInstance h3)

end Theta

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_le_inf_card_eq {Q T V L : Subgroup G} (hT : CFSG.Open.fusionIsSylowIn 2 T Q)
    (hV2 : IsPGroup 2 V) (hVQ : V ≤ Q) (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hVL : V ≤ L) : ∃ W : Subgroup G, W ≤ T ⊓ L ∧ Nat.card W = Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTQ, hT2, hTmax⟩ := hT
  obtain ⟨S, hS⟩ := (hT2.comap_of_injective Q.subtype Q.subtype_injective).exists_le_sylow
  have hST : (S : Subgroup Q).map Q.subtype = T :=
    hTmax _ (Subgroup.map_subtype_le _) (S.isPGroup'.map Q.subtype)
      fun x hx => ⟨⟨x, hTQ hx⟩, hS hx, rfl⟩
  obtain ⟨S', hS'⟩ := (hV2.comap_of_injective Q.subtype Q.subtype_injective).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q S' S
  refine ⟨V.map (MulAut.conj (g : G)).toMonoidHom, ?_,
    Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective⟩
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨?_, ?_⟩
  · have hv' : (⟨v, hVQ hv⟩ : Q) ∈ (S' : Subgroup Q) := hS' hv
    have hmem : g * ⟨v, hVQ hv⟩ * g⁻¹ ∈ ((g • S' : Sylow 2 Q) : Subgroup Q) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        ← map_inv, MulAut.conj_apply, inv_inv]
      simpa [mul_assoc] using hv'
    rw [hg] at hmem
    rw [← hST]
    exact ⟨_, hmem, rfl⟩
  · have hgL := hQL g.2
    exact (Subgroup.mem_normalizer_iff.mp hgL v).mp (hVL hv)

end Sylow

section Orders

theorem sq_sub_one_eq (r : ℕ) : r ^ 2 - 1 = (r - 1) * (r + 1) := by
  rcases r with _ | s
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [show (s + 1) ^ 2 = s * (s + 1 + 1) + 1 by ring, Nat.add_sub_cancel]

theorem cube_sub_one_eq (r : ℕ) : r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) := by
  rcases r with _ | s
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [show (s + 1) ^ 3 = s * ((s + 1) ^ 2 + (s + 1) + 1) + 1 by ring, Nat.add_sub_cancel]

theorem cube_add_one_eq {r : ℕ} (hr : 1 ≤ r) : r ^ 3 + 1 = (r + 1) * (r ^ 2 - r + 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [show (s + 1) ^ 2 - (s + 1) = s * (s + 1) by
    rw [show (s + 1) ^ 2 = s * (s + 1) + (s + 1) by ring, Nat.add_sub_cancel]]
  ring

theorem not_four_pow_dvd_card {M : Type} [Group M] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hM : Sec14.IsLThreeEpsAt M r 1) : ¬ 4 ^ padicValNat 2 (r ^ 2 - 1) ∣ Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : r.Prime := Fact.out
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨k, hk⟩ := hodd
  have hm2 : 2 ∣ r - 1 := ⟨k, by omega⟩
  have hp2 : 2 ∣ r + 1 := ⟨k + 1, by omega⟩
  have hr0 : r ≠ 0 := by omega
  have hm0 : r - 1 ≠ 0 := by omega
  have hp0 : r + 1 ≠ 0 := by omega
  have h30 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr0
  set a := padicValNat 2 (r - 1) with ha
  set b := padicValNat 2 (r + 1) with hb
  have ha1 : 1 ≤ a := one_le_padicValNat_of_dvd hm0 hm2
  have hb1 : 1 ≤ b := one_le_padicValNat_of_dvd hp0 hp2
  have e1 : padicValNat 2 ((r - 1) * (r + 1)) = a + b := padicValNat.mul hm0 hp0
  have hv : padicValNat 2 (r ^ 2 - 1) = a + b := by rw [sq_sub_one_eq, e1]
  have hr3odd : padicValNat 2 (r ^ 3) = 0 :=
    padicValNat.eq_zero_of_not_dvd fun h => by
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)
      omega
  have hpow : (4 : ℕ) ^ (a + b) = 2 ^ (2 * (a + b)) := by rw [pow_mul]; norm_num
  intro hdvd
  rw [hv, hpow] at hdvd
  rcases hM with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  ·
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField r 1)
    rw [GaloisField.card r 1 (by norm_num), pow_one] at hc
    have hN : 2 ^ (2 * (a + b)) ∣ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
      rw [Nat.card_congr φ.toEquiv] at hdvd
      exact hdvd.trans (hc ▸ Dvd.intro _ rfl)
    rw [sq_sub_one_eq, cube_sub_one_eq] at hN
    have hq : ¬ 2 ∣ r ^ 2 + r + 1 := by
      have h2 : 2 ∣ r ^ 2 + r := by
        rw [show r ^ 2 + r = r * (r + 1) by ring]
        exact Dvd.dvd.mul_left hp2 r
      intro h
      exact absurd ((Nat.dvd_add_right h2).mp h) (by norm_num)
    have hq0 : r ^ 2 + r + 1 ≠ 0 := Nat.succ_ne_zero _
    have e2 : padicValNat 2 ((r - 1) * (r ^ 2 + r + 1)) = a := by
      rw [padicValNat.mul hm0 hq0, padicValNat.eq_zero_of_not_dvd hq, add_zero]
    have hX0 : (r - 1) * (r + 1) * ((r - 1) * (r ^ 2 + r + 1)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hm0 hp0) (mul_ne_zero hm0 hq0)
    have hval : padicValNat 2 (r ^ 3 * ((r - 1) * (r + 1) * ((r - 1) * (r ^ 2 + r + 1)))) =
        2 * a + b := by
      rw [padicValNat.mul h30 hX0, padicValNat.mul (mul_ne_zero hm0 hp0) (mul_ne_zero hm0 hq0),
        e1, e2, hr3odd]
      ring
    have := (padicValNat_dvd_iff_le (mul_ne_zero h30 hX0)).mp hN
    omega
  ·
    have hc := KFacts.KS14.card_projSU_three_mul_gcd r 1 le_rfl
    rw [pow_one] at hc
    have hN : 2 ^ (2 * (a + b)) ∣ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) := by
      rw [Nat.card_congr φ.toEquiv] at hdvd
      exact hdvd.trans (hc ▸ Dvd.intro _ rfl)
    rw [sq_sub_one_eq, cube_add_one_eq (by omega)] at hN
    have hq : ¬ 2 ∣ r ^ 2 - r + 1 := by
      have h1 : r ^ 2 - r = r * (r - 1) := by
        rw [Nat.mul_sub_one, sq]
      have h2 : 2 ∣ r ^ 2 - r := by
        rw [h1]
        exact Dvd.dvd.mul_left hm2 r
      intro h
      exact absurd ((Nat.dvd_add_right h2).mp h) (by norm_num)
    have hq0 : r ^ 2 - r + 1 ≠ 0 := Nat.succ_ne_zero _
    have e2 : padicValNat 2 ((r + 1) * (r ^ 2 - r + 1)) = b := by
      rw [padicValNat.mul hp0 hq0, padicValNat.eq_zero_of_not_dvd hq, add_zero]
    have hX0 : (r - 1) * (r + 1) * ((r + 1) * (r ^ 2 - r + 1)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hm0 hp0) (mul_ne_zero hp0 hq0)
    have hval : padicValNat 2 (r ^ 3 * ((r - 1) * (r + 1) * ((r + 1) * (r ^ 2 - r + 1)))) =
        a + 2 * b := by
      rw [padicValNat.mul h30 hX0, padicValNat.mul (mul_ne_zero hm0 hp0) (mul_ne_zero hp0 hq0),
        e1, e2, hr3odd]
      ring
    have := (padicValNat_dvd_iff_le (mul_ne_zero h30 hX0)).mp hN
    omega

end Orders

section Torus

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem map_le_theta_centralizer {X K : Subgroup Γ} (hXK : X ≤ K)
    (hKX : K ≤ Subgroup.normalizer (X : Set Γ)) {x : Γ} (hx : x ∈ X) {V : Subgroup ↥X}
    (hV2 : IsPGroup 2 V) (hVC : V ≤ Subgroup.centralizer {(⟨x, hx⟩ : ↥X)})
    (hCV : Subgroup.centralizer {(⟨x, hx⟩ : ↥X)} ≤ Subgroup.normalizer (V : Set ↥X)) :
    V.map X.subtype ≤
      inSubgroup (aschbacherSolvableCore 3) (K ⊓ Subgroup.centralizer ({x} : Set Γ)) := by
  have hV2' : IsPGroup 2 (V.map X.subtype) := hV2.map X.subtype
  have hVC' : V.map X.subtype ≤ X ⊓ Subgroup.centralizer ({x} : Set Γ) := by
    rintro _ ⟨v, hv, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨v.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hVC hv))
  have hNV : X ⊓ Subgroup.centralizer ({x} : Set Γ) ≤
      Subgroup.normalizer ((V.map X.subtype : Subgroup Γ) : Set Γ) := by
    intro g hg
    have hgC : (⟨g, hg.1⟩ : ↥X) ∈ Subgroup.centralizer {(⟨x, hx⟩ : ↥X)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
    have hgN := hCV hgC
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨v, hv, rfl⟩ := hn
    exact ⟨_, (Subgroup.mem_normalizer_iff.mp hgN v).mp hv, rfl⟩
  refine (le_inSubgroup_theta_of_isPGroup hV2' hVC' hNV).trans
    (inSubgroup_theta_le_of_le_normalizer (inf_le_inf_right _ hXK) ?_)
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  exact ⟨(Subgroup.mem_normalizer_iff.mp (hKX hg.1) n).mp hn.1,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.2 hn.2) (Subgroup.inv_mem _ hg.2)⟩

end Torus

section Preimage

theorem exists_preimage {G Γ : Type} [Group G] [Group Γ] {L : Subgroup G} {f : ↥L →* Γ}
    (hf : Function.Injective f) {V : Subgroup Γ} (hV : V ≤ f.range) :
    ∃ V' : Subgroup G, V' ≤ L ∧ Nat.card V' = Nat.card V ∧
      ∀ l : ↥L, (l : G) ∈ V' → f l ∈ V := by
  refine ⟨(V.comap f).map L.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, ← Subgroup.card_map_of_injective hf,
      Subgroup.map_comap_eq, inf_eq_right.mpr hV]
  · rintro l ⟨l', hl', hll'⟩
    have hl : l' = l := Subtype.ext hll'
    rw [← hl]
    exact hl'

end Preimage

section Img

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
  [(ker142 A LB c).Normal]

theorem mem_of_mk_mem_img142 {Q : Subgroup G} (hOQ : pPrimeCoreOf 3 (k142 A LB c) ≤ Q)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G)) (hc3 : c ^ 3 = 1) {g : ↥(kA142 A LB c)}
    (hg2 : IsPGroup 2 (Subgroup.zpowers (g : G)))
    (hg : QuotientGroup.mk' (ker142 A LB c) g ∈ img142 A LB c Q) : (g : G) ∈ Q := by
  obtain ⟨q, hq, hqe⟩ := hg
  have hker : q⁻¹ * g ∈ ker142 A LB c := QuotientGroup.eq.mp hqe
  have hmem : ((q⁻¹ * g : ↥(kA142 A LB c)) : G) ∈
      pPrimeCoreOf 3 (k142 A LB c) ⊔ Subgroup.zpowers c := Subgroup.mem_subgroupOf.mp hker
  have hQc : (g : G) ∈ Q ⊔ Subgroup.zpowers c := by
    have hg_eq : (g : G) = (q : G) * ((q⁻¹ * g : ↥(kA142 A LB c)) : G) := by simp
    rw [hg_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hq))
      ((sup_le (hOQ.trans le_sup_left) le_sup_right) hmem)
  have hQcN : Q ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hcQ)
  exact Proof1513Res3.le_of_le_sup_zpowers hg2 (Subgroup.zpowers_le.mpr (hQcN hQc)) hcQ hc3
    (Subgroup.zpowers_le.mpr hQc) (Subgroup.mem_zpowers _)

end Img

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_torus_le_inf
    (h142 : Sec14.Item142R)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hθL : aschbacherSolvableCore 3 ↥L = ⊥) {p : ℕ} [Fact p.Prime]
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p 2) (hp2 : p ≠ 2)
    (h9 : ¬ (p ^ 2 % 9 = 1 ∨ p ^ 2 % 9 = 8)) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2)) :
    ∃ W : Subgroup G, W ≤ T ⊓ L ∧ 4 ^ padicValNat 2 (p ^ 2 - 1) ≤ Nat.card W := by
  have hKT := ks1518HessTorus
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hcA : c ∈ A := hD.mem_A
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hCcH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c
  have hKH : k142 A (lB A) c ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    delta_le _
  have hAK : A ≤ Subgroup.normalizer (k142 A (lB A) c : Set G) :=
    Sec14.le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hAO : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 (k142 A (lB A) c) : Set G) :=
    hAK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)
  have hO3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (k142 A (lB A) c)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hTQ𝓠 : T ∈ scriptQ A (lB A) := hT.prop.1.1
  have hTinv : T ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) := ⟨hT.prop.1.2, hTQ𝓠.1.2.1, hTQ𝓠.1.2.2⟩
  obtain ⟨Q, hTQ, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))) hTinv
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hcA
  obtain ⟨hQQ, hcase⟩ := h142 G A c L h Q hQ
  have hQH : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hQ.prop.1
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.prop.2.2
  have hQK : Q ≤ k142 A (lB A) c := le_delta hQQ.1 (hQQ.2.trans hCcH)
  have hTstar : T ∈ scriptQPiStar A (lB A) Q (piOf 2) :=
    ⟨⟨⟨hTQ𝓠, hTQ⟩, hT.prop.2⟩, fun S hS hTS =>
      hT.2 ⟨⟨hS.1.1, hS.1.2.trans hQH⟩, hS.2⟩ hTS⟩
  have hTsyl : CFSG.Open.fusionIsSylowIn 2 T Q :=
    Sec16.Proof165.fusionIsSylowIn_of_mem_scriptQPiStar h.toSec14Std.isE27 hQQ.1 hQ3 hTstar
  rcases hcase with ⟨⟨φ⟩, -, -, -⟩ | ⟨hKeq, htypes⟩
  ·
    exfalso
    obtain ⟨hperf, hZ⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hperf hZ φ
    have h4 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 2 :=
      Or.inl ⟨by norm_num, ⟨ψ⟩⟩
    have hpq := Sec19.Step1917EqProof.eq_of_isoLThreePi (by norm_num) (by norm_num) hiso h4
    exact hp2 (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hpq)
  obtain ⟨eL⟩ := Sec14.Item148PtRes2.nonempty_img142_equiv sporadicModels131 h.toSec14Std hKeq
  obtain ⟨a, ha, ha1, hQα⟩ : ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      img142 A (lB A) c Q = thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔
        thetaCA142 A (lB A) c := by
    rcases htypes with ⟨-, hex⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact hex
    · exact absurd (Proof1520.isoLThreePi_of_mulEquiv (φ.symm.trans eL) hiso)
        (KFacts.KS14.not_isoLThreePi_M22 p 2)
    · exact absurd (Proof1520.isoLThreePi_of_mulEquiv (φ.symm.trans eL) hiso)
        (Sec14.Item148PtRes2.not_isoLThreePi_J2 p 2)
  have hLK : L ≤ k142 A (lB A) c := by
    rw [hKeq]
    exact le_sup_left.trans le_sup_left
  have hLKA : L ≤ kA142 A (lB A) c := hLK.trans le_sup_left
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_types148
    (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hKL : k142 A (lB A) c ≤ Subgroup.normalizer (L : Set G) :=
    hKH.trans (Sec17.Sec15R.normalizer_zpowers_le_normalizer_L h h3L)
  have hQL : Q ≤ Subgroup.normalizer (L : Set G) := hQK.trans hKL
  have hKc : k142 A (lB A) c ≤ Subgroup.centralizer ({c} : Set G) :=
    sSup_le fun Q' hQ' => le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq
      ⟨hQ'.2, hQ'.1.1.2.1, hQ'.1.1.2.2⟩
  have hAα : img142 A (lB A) c A ≤ img142 A (lB A) c L := by
    have hcK : Subgroup.zpowers c ≤ kA142 A (lB A) c :=
      (Subgroup.zpowers_le.mpr hcA).trans le_sup_right
    have hALKA : A ⊓ L ≤ kA142 A (lB A) c := inf_le_left.trans le_sup_right
    calc img142 A (lB A) c A = img142 A (lB A) c (Subgroup.zpowers c ⊔ (A ⊓ L)) :=
          congrArg (img142 A (lB A) c) hAeq
      _ = img142 A (lB A) c (Subgroup.zpowers c) ⊔ img142 A (lB A) c (A ⊓ L) :=
          Proof1513Res3.img142_sup hcK hALKA
      _ = img142 A (lB A) c (A ⊓ L) := by
          rw [Proof1513Res3.img142_eq_bot (le_sup_right : Subgroup.zpowers c ≤
            pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c), bot_sup_eq]
      _ ≤ img142 A (lB A) c L := Proof1513Res3.img142_mono inf_le_right
  have hxL : alpha142 A (lB A) c a ha ∈ img142 A (lB A) c L :=
    hAα (Proof1513Res3.mk_mem_img142 ha)
  have hx3 : alpha142 A (lB A) c a ha ^ 3 = 1 := by
    rw [alpha142, ← map_pow]
    have h3 : (⟨a, Subgroup.mem_sup_right ha⟩ : ↥(kA142 A (lB A) c)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hD.isElemAbelian.2 a ha)
    rw [h3, map_one]
  obtain ⟨V, hV2, hVcard, hVC, hCV⟩ := hKT ↥(img142 A (lB A) c L) p hp2
    (Proof1520.isoLThreePi_of_mulEquiv eL hiso) h9 ⟨_, hxL⟩ (Subtype.ext (by simpa using hx3))
    (fun h1 => ha1 (congrArg Subtype.val h1))
  have hKαL : img142 A (lB A) c (k142 A (lB A) c) ≤
      Subgroup.normalizer ((img142 A (lB A) c L : Subgroup _) : Set _) := by
    rintro _ ⟨k, hk, rfl⟩
    exact Proof1513Res3.mk_mem_normalizer_img142 (hKL (Subgroup.mem_subgroupOf.mp hk))
  have hVQα : V.map (img142 A (lB A) c L).subtype ≤ img142 A (lB A) c Q := by
    rw [hQα]
    exact (map_le_theta_centralizer (Proof1513Res3.img142_mono hLK) hKαL hxL hV2 hVC
      hCV).trans le_sup_left
  obtain ⟨f, hf⟩ : ∃ f : ↥L →* ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c,
      f = (QuotientGroup.mk' (ker142 A (lB A) c)).comp (Subgroup.inclusion hLKA) := ⟨_, rfl⟩
  have hfrange : f.range = img142 A (lB A) c L := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hfker : f.ker = (ker142 A (lB A) c).comap (Subgroup.inclusion hLKA) := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : l ∈ f.ker := hl
    rw [hfker] at h1
    have h2 : (l : G) ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c :=
      Subgroup.mem_subgroupOf.mp
        (Subgroup.mem_comap.mp h1 : Subgroup.inclusion hLKA l ∈ ker142 A (lB A) c)
    have hθ' := Sec14.Item148PtRes2.inf_le_theta sporadicModels131 h.toSec14Std hO3
      (hLK.trans (le_normalizer_pPrimeCoreOf 3 _)) ((pPrimeCoreOf_le 3 _).trans hKc)
      (Subgroup.mem_subgroupOf.mpr h2)
    exact Subgroup.mem_bot.mp (hθL.le hθ')
  have hVr : V.map (img142 A (lB A) c L).subtype ≤ f.range := by
    rw [hfrange]
    exact Subgroup.map_subtype_le V
  obtain ⟨V', hV'L, hV'card, hV'f⟩ := exists_preimage hfinj hVr
  have hV'card' : Nat.card V' = Nat.card V := by
    rw [hV'card, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hV'2 : IsPGroup 2 V' := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV2
    exact IsPGroup.of_card (by rw [hV'card', hn])
  have hOQ : pPrimeCoreOf 3 (k142 A (lB A) c) ≤ Q := by
    have hQO : Q ⊔ pPrimeCoreOf 3 (k142 A (lB A) c) ∈
        invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piCompl 3) := by
      refine ⟨sup_le hQH ((pPrimeCoreOf_le 3 _).trans hKH), ?_, le_normalizer_sup hAQ hAO⟩
      rw [isPiSubgroup_piCompl_iff Nat.prime_three]
      exact Sec6.not_dvd_card_sup Nat.prime_three (hQK.trans (le_normalizer_pPrimeCoreOf 3 _))
        hQ3 hO3
    exact le_sup_right.trans (hQ.2 hQO le_sup_left)
  have hV'Q : V' ≤ Q := by
    intro l hl
    have hl2 : IsPGroup 2 (Subgroup.zpowers l) := hV'2.to_le (Subgroup.zpowers_le.mpr hl)
    have hfl := hV'f ⟨l, hV'L hl⟩ hl
    exact mem_of_mk_mem_img142 (g := Subgroup.inclusion hLKA ⟨l, hV'L hl⟩) hOQ (hAQ hcA) hc3
      hl2 (hVQα (by rw [hf] at hfl; exact hfl))
  obtain ⟨W, hW, hWcard⟩ := exists_le_inf_card_eq hTsyl hV'2 hV'Q hQL hV'L
  exact ⟨W, hW, by rw [hWcard, hV'card']; exact hVcard⟩

end Config

end Proof15Res9

open Proof15Res9

theorem step1518TL_of_hessTorus
    (h142 : Sec14.Item142R) (h138 : Item138N)
    : Step1518TL := by
  intro G _ _ A c L h Y hctx hno hs p e _ he hiso hp2 T hT hTY
  obtain ⟨he2, hLY⟩ := step1518Read G A c L h Y hctx hno hs p e he hiso hp2
  subst he2
  obtain ⟨-, -, -, -, -, hprod, -, -, -⟩ := hctx.concl1515
  have h9 : ¬ (p ^ 2 % 9 = 1 ∨ p ^ 2 % 9 = 8) :=
    not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC he hiso hprod
  obtain ⟨-, -, hAeq⟩ := Proof1517.point_facts h hctx
  have hθL := Proof1520.theta_eq_bot_of_isSimpleGroup h.mem_thetaComponentsAt hs
  obtain ⟨W, hW, hWcard⟩ := exists_torus_le_inf h142 h hAeq hθL hiso hp2 h9 hT
  have hWY : W ≤ L ⊓ Y := le_inf (hW.trans inf_le_right) (hW.trans hTY)
  have hW2 : IsPGroup 2 W :=
    (isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop).to_le (hW.trans inf_le_left)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW2
  have h4 : 4 ^ padicValNat 2 (p ^ 2 - 1) ∣ Nat.card W := by
    rw [hn, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    refine Nat.pow_dvd_pow 2 ?_
    have hle : 2 ^ (2 * padicValNat 2 (p ^ 2 - 1)) ≤ 2 ^ n := by
      rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hn]
      exact hWcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  exact not_four_pow_dvd_card hp2 hLY (h4.trans (Subgroup.card_dvd_of_le hWY))

theorem step1518TL_of
    (h142 : Sec14.Item142R) (h138 : Item138N) : Step1518TL :=
  step1518TL_of_hessTorus h142 h138

end CFSG.RankThree.PartTwo.Sec15

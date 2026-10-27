module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofEven
public import CFSG.RankThree.PartTwo.Sec15.Item1513ProofNoTransv
import CFSG.RankThree.PartTwo.Sec15.Item1513Res2ProofOdd
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCentral
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1513

@[expose] noncomputable def Step1513EvenNotM12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (K : Subgroup G), Ctx1513 G A c L a K →
      ∀ w ∈ K ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 →
        Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9 →
        (∀ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ → w ∉ Subgroup.normalizer (T : Set G)) →
          IsEmpty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12)

namespace Proof1513Res2

open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi)
open CFSG.Assembly.RankThreeEven (projImage)

variable {G : Type} [Group G] [Finite G]

theorem map_centralizer_singleton {X : Type*} [Group X] (α : X ≃* X) (z : X) :
    (Subgroup.centralizer ({z} : Set X)).map α.toMonoidHom =
      Subgroup.centralizer ({α z} : Set X) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg α h
    simpa using this
  · intro h
    apply α.injective
    simpa using h

theorem exists_two_subgroup_of_odd {U R : Subgroup G} (hR3 : IsPGroup 3 R)
    (hRU : R ≤ Subgroup.normalizer (U : Set G)) (hne : R ⊓ U ≠ ⊥) {π : Bool} {p f : ℕ}
    {F : Type} [Field F] (hF : PiField π p f F) (hq : ModThree π (p ^ f)) (hp2 : p ≠ 2)
    (ψ : ↥U ⧸ aschbacherSolvableCore 3 ↥U ≃* projImage (slPi π 3 (p ^ f) F)) :
    ∃ V : Subgroup G, V ≠ ⊥ ∧ IsPGroup 2 V ∧ V ≤ U ∧ R ≤ Subgroup.normalizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := aschbacherSolvableCore 3 ↥U with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥U) Nat.prime_three).2.2.1
  set πU := QuotientGroup.mk' θ with hπU
  set α : R → MulAut (↥U ⧸ θ) := fun r =>
    Sec4.thetaQuotMulAut ↥U (U.normalizerMonoidHom ⟨r, hRU r.2⟩) with hαdef
  have hα : ∀ (r : R) (u : ↥U), α r (πU u) =
      πU (U.normalizerMonoidHom ⟨r, hRU r.2⟩ u) := fun r u => by
    rw [hαdef]
    exact Sec4.thetaQuotMulAut_mk _ u
  obtain ⟨z, ⟨hzR, hzU⟩, hz1, hzc⟩ := Proof1513Steps.exists_central_of_normal hR3 hRU hne
  obtain ⟨k, hk⟩ := hR3 ⟨z, hzR⟩
  have hzk : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set zb := πU ⟨z, hzU⟩ with hzb
  have hzb1 : zb ≠ 1 := by
    intro h
    have hzθ : (⟨z, hzU⟩ : ↥U) ∈ θ := (QuotientGroup.eq_one_iff _).mp h
    have h1 := eq_one_of_mem_of_pow_three_pow hθ3 hzθ (k := k) (Subtype.ext (by simpa using hzk))
    exact hz1 (congrArg Subtype.val h1)
  have hzbk : zb ^ 3 ^ k = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzU⟩ : ↥U) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hzk)
    rw [this, map_one]
  have hzbfix : ∀ r : R, α r zb = zb := by
    intro r
    rw [hzb, hα]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    rw [hzc r r.2, mul_inv_cancel_right]
  have h3ord : 3 ∣ Nat.card (Subgroup.zpowers zb) := by
    rw [Nat.card_zpowers]
    have hd : orderOf zb ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hzbk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    rw [hj]
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact absurd hj hzb1
    · exact dvd_pow_self 3 (Nat.succ_ne_zero j)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers zb) 3 h3ord
  set z₁ : ↥U ⧸ θ := (x : ↥U ⧸ θ) with hz₁
  have hz₁o : orderOf z₁ = 3 := by rw [hz₁, Subgroup.orderOf_coe, hx]
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₁o
    omega
  have hz₁3 : z₁ ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z₁
    rwa [hz₁o] at h1
  have hz₁fix : ∀ r : R, α r z₁ = z₁ := by
    intro r
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
    rw [hz₁, ← hi, map_zpow, hzbfix]
  set Vb := CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z₁} : Set (↥U ⧸ θ))) with hVb
  have hVb1 : Vb ≠ ⊥ := pCoreOf_two_centralizer_ne_bot hF hq hp2 ψ hz₁1 hz₁3
  have hVb2 : IsPGroup 2 Vb := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hVbinv : ∀ r : R, Vb.map (α r).toMonoidHom = Vb := by
    intro r
    rw [hVb, ← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv, map_centralizer_singleton,
      hz₁fix]
  set V'' : Subgroup ↥U := Vb.comap πU with hV''
  set V' : Subgroup G := V''.map U.subtype with hV'
  have hV'U : V' ≤ U := Subgroup.map_subtype_le _
  have hmemV' : ∀ u : ↥U, (u : G) ∈ V' ↔ πU u ∈ Vb := fun u =>
    (Subgroup.mem_map_iff_mem U.subtype_injective).trans Iff.rfl
  have hRV' : R ≤ Subgroup.normalizer (V' : Set G) := by
    intro r hr
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨u, hu, rfl⟩ := hy
    have hu' : πU u ∈ Vb := hu
    have h1 : α ⟨r, hr⟩ (πU u) ∈ Vb := by
      rw [← hVbinv ⟨r, hr⟩]
      exact ⟨πU u, hu', rfl⟩
    rw [hα] at h1
    have h2 := (hmemV' _).mpr h1
    rwa [Sec4.normalizerMonoidHom_apply_coe] at h2
  have hV'3 : ¬ 3 ∣ Nat.card V' := by
    intro h3
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := V') 3 h3
    obtain ⟨u, hu, hyu⟩ := y.2
    have hu' : πU u ∈ Vb := hu
    have hu3 : u ^ 3 = 1 := by
      have : (y : G) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hyu] at this
      exact this
    have hπu : πU u = 1 := by
      obtain ⟨j, hj⟩ := hVb2 ⟨πU u, hu'⟩
      have h2 : (πU u) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have h3' : (πU u) ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left j
        (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one h2)
        (orderOf_dvd_of_pow_eq_one h3'))
    have huθ : u ∈ θ := (QuotientGroup.eq_one_iff _).mp hπu
    have hu1 : u = 1 := eq_one_of_mem_of_pow_three_pow hθ3 huθ (k := 1) (by simpa using hu3)
    have hy1 : y = 1 := Subtype.ext (by rw [← hyu, hu1]; rfl)
    rw [hy1, orderOf_one] at hy
    omega
  obtain ⟨S, hS, -, hRS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hR3 hV'3 hRV' bot_le IsPGroup.of_bot
    (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun y => by simp)
  refine ⟨S, ?_, hS.2.1, hS.1.trans hV'U, hRS⟩
  intro hS0
  obtain ⟨⟨vb, hvb⟩, hvb1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVb1
  have hvb1 : vb ≠ 1 := fun h => hvb1' (Subtype.ext h)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective θ vb
  have huV' : (u : G) ∈ V' := (hmemV' u).mpr hvb
  obtain ⟨j, hj⟩ := hVb2 ⟨πU u, hvb⟩
  have hj' : (πU u) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨v, m, hm2, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos u).ne' 2 (by norm_num)
  set u₂ := u ^ m with hu₂
  have hu₂V' : (u₂ : G) ∈ V' := by
    rw [hu₂, Subgroup.coe_pow]
    exact pow_mem huV' m
  have hu₂2 : u₂ ^ 2 ^ v = 1 := by
    rw [hu₂, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hu₂1 : u₂ ≠ 1 := by
    intro h1
    apply hvb1
    have h2 : (πU u) ^ m = 1 := by rw [← map_pow, ← hu₂, h1, map_one]
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left j
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm2)) (orderOf_dvd_of_pow_eq_one hj')
      (orderOf_dvd_of_pow_eq_one h2))
  have hp : IsPGroup 2 (Subgroup.zpowers (u₂ : G)) := by
    have hd : orderOf (u₂ : G) ∣ 2 ^ v := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hu₂2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have h1 := hS.2.2 (Subgroup.zpowers (u₂ : G)) (Subgroup.zpowers_le.mpr hu₂V') hp
    (by rw [hS0]; exact bot_le)
  apply hu₂1
  apply Subtype.ext
  have := Subgroup.mem_zpowers (u₂ : G)
  rw [h1, hS0, Subgroup.mem_bot] at this
  exact this

theorem exists_mem_scriptQ_of_odd {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h142 : Concl142 A (lB A)) {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) {U : Subgroup G}
    (hUb : U ≤ Subgroup.centralizer ({b} : Set G)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hw3 : w ^ 3 = 1)
    (hwU : w ∈ Subgroup.normalizer (U : Set G))
    (hne : (Subgroup.zpowers w ⊔ A) ⊓ U ≠ ⊥) {π : Bool} {p f : ℕ}
    {F : Type} [Field F] (hF : PiField π p f F) (hq : ModThree π (p ^ f)) (hp2 : p ≠ 2)
    (ψ : ↥U ⧸ aschbacherSolvableCore 3 ↥U ≃* projImage (slPi π 3 (p ^ f) F)) :
    ∃ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ ∧ w ∈ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hA3 : IsPGroup 3 A := Proof1513Steps.isPGroup_of_sec13Data hD
  set R := Subgroup.zpowers w ⊔ A with hR
  have hR3 : IsPGroup 3 R := IsPGroup.to_sup_of_normal_right'
    (Proof1513Steps.isPGroup_zpowers_of_pow_three hw3) hA3 (Subgroup.zpowers_le.mpr hwA)
  have hRU : R ≤ Subgroup.normalizer (U : Set G) := sup_le (Subgroup.zpowers_le.mpr hwU) hAU
  obtain ⟨V, hV1, hV2, hVU, hRV⟩ := exists_two_subgroup_of_odd hR3 hRU hne hF hq hp2 ψ
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hRV
  have hV3 : IsPiSubgroup (piCompl 3) V := by
    rw [isPiSubgroup_piCompl_iff Nat.prime_three]
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hVQ := Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 h.toSec14Std.isE27 h142 hb
    hV3 hAV
  rw [inf_eq_left.mpr (hVU.trans hUb)] at hVQ
  exact ⟨V, ⟨⟨hVQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two V).mpr hV2⟩, hV1,
    hRV (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))⟩

end Proof1513Res2

open Proof1513Res2


theorem step1513EvenType_of (h131 : Item131) (h142 : Concl142S14)
    (hM12 : Step1513EvenNotM12) : Step1513EvenType := by
  intro G _ _ A c L a K hctx w hwKW hw3 hwC9 hT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hctx.toSec15R
  have hD := h.toSec13Data
  have h142' : Concl142 A (lB A) := h142 G A c L h.toSec14Std
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hwKW.2
  have hwH := hctx.normalizer_le hwA
  have hT' : ¬ ∃ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ ∧
      w ∈ Subgroup.normalizer (T : Set G) := fun ⟨T, hTQ, hT1, hwT⟩ => hT T hTQ hT1 hwT
  have hw1 : w ≠ 1 := by
    rintro rfl
    have hAC : A ⊓ Subgroup.centralizer ({(1 : G)} : Set G) = A := inf_of_le_left fun x _ =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
    rw [hAC, hD.card_eq] at hwC9
    norm_num at hwC9
  refine ⟨?_, ?_⟩
  ·
    have h3L : 3 ∣ Nat.card L := (show 3 ∣ 9 by norm_num).trans
      (hctx.card_inf ▸ Subgroup.card_dvd_of_le inf_le_right)
    have hwL : w ∈ Subgroup.normalizer (L : Set G) :=
      Sec17.Sec15R.normalizer_zpowers_le_normalizer_L h h3L hwH
    obtain ⟨-, htypes⟩ := cases_of_irreducible h131 h hctx.card_inf hctx.irreducible
    obtain ⟨p, e, hp, he, hiso⟩ : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rcases htypes with h1 | h1 | h1
      · exact h1
      · exact (step1513NoTransv_of h131 G A c L h (Or.inr h1) w ⟨hwH, hwA⟩ hw3 hwC9).elim
      · exact (step1513NoTransv_of h131 G A c L h (Or.inl h1) w ⟨hwH, hwA⟩ hw3 hwC9).elim
    by_cases hp2 : p = 2
    · subst hp2
      exact ⟨e, he, hiso⟩
    · exfalso
      obtain ⟨π, F, _, hF, hqF, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
      have hne : (Subgroup.zpowers w ⊔ A) ⊓ L ≠ ⊥ := by
        intro hbot
        have hle : A ⊓ L ≤ (Subgroup.zpowers w ⊔ A) ⊓ L := inf_le_inf_right L le_sup_right
        rw [hbot, le_bot_iff] at hle
        have := hctx.card_inf
        rw [hle, Subgroup.card_bot] at this
        norm_num at this
      exact hT' (exists_mem_scriptQ_of_odd h h142' hD.zpowers_mem_omegaA hD.le_centralizer
        hD.le_normalizer hwA hw3 hwL hne hF hqF hp2 ψ)
  ·
    have hDa := (Proof1511.sec15R_point h hctx.zpowers_a_mem hctx.mem_lA_a).toSec13Data
    have hwK : w ∈ K := hwKW.1
    rcases hctx.type_a with hPGL | hM
    · obtain ⟨π, p, f, F, _, hF, hqF, -, ⟨ψ⟩⟩ := Sec13.exists_projImage_slPi_equiv hDa hPGL
      by_cases hp2 : p = 2
      · subst hp2
        obtain ⟨_, hiso⟩ := Sec13.ResProof.isoLThreePi_projImage_slPi hF hqF
        refine ⟨f, hF.one_le, ?_⟩
        rcases hiso with ⟨h1, ⟨φ⟩⟩ | ⟨h1, ⟨φ⟩⟩
        · exact Or.inl ⟨h1, ⟨ψ.trans φ⟩⟩
        · exact Or.inr ⟨h1, ⟨ψ.trans φ⟩⟩
      · exfalso
        have hne : (Subgroup.zpowers w ⊔ A) ⊓ K ≠ ⊥ := by
          intro hbot
          have hwmem : w ∈ (Subgroup.zpowers w ⊔ A) ⊓ K :=
            ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers w), hwK⟩
          rw [hbot, Subgroup.mem_bot] at hwmem
          exact hw1 hwmem
        exact hT' (exists_mem_scriptQ_of_odd h h142' hctx.zpowers_a_mem hDa.le_centralizer
          hDa.le_normalizer hwA hw3 (Subgroup.le_normalizer hwK) hne hF hqF hp2 ψ)
    · exact ((hM12 G A c L a K hctx w hwKW hw3 hwC9 hT).false hM.some).elim

end CFSG.RankThree.PartTwo.Sec15

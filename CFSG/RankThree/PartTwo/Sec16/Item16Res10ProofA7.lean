module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofA7
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.RankThree.PartTwo.Sec17.Item176ProofTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofA7
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.K412Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Res10A7

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_of_isPGroup_two {X : Subgroup G} (hX : IsPGroup 2 X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

omit [Finite G] in
theorem eq_one_of_pow_three_of_pow_two {H : Type*} [Group H] {x : H} (h3 : x ^ 3 = 1) {k : ℕ}
    (h2 : x ^ 2 ^ k = 1) : x = 1 := by
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem le_sup_pCoreOf_of_card_le {M Z : Subgroup G} (hMZ : M ≤ Z)
    (hcard : Nat.card (↥Z ⧸ CFSG.pCore 2 ↥Z) ≤ Nat.card (↥M ⧸ aschbacherSolvableCore 3 ↥M)) :
    Z ≤ M ⊔ CFSG.Open.pCoreOf 2 Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 ↥Z with hN
  set O := CFSG.Open.pCoreOf 2 Z with hOdef
  set θ := aschbacherSolvableCore 3 ↥M with hθ
  set f : ↥M →* ↥Z ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hMZ) with hf
  have hk : f.ker = N.comap (Subgroup.inclusion hMZ) := by
    ext x
    simp [hf, QuotientGroup.eq_one_iff]
  have hk2 : IsPGroup 2 f.ker := by
    rw [hk]
    exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hMZ)
  have hkθ : f.ker ≤ θ := by
    obtain ⟨-, -, -, hmax, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
    have : Group.IsSolvable f.ker := by
      have := hk2.isNilpotent
      infer_instance
    exact hmax f.ker f.normal_ker this (not_three_dvd_of_isPGroup_two (hk2.map M.subtype) ∘
      fun h => by rwa [Subgroup.card_map_of_injective M.subtype_injective])
  have h1 : Nat.card ↥M = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h2 : Nat.card ↥M = Nat.card (↥M ⧸ θ) * Nat.card θ :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup θ
  have h3 : Nat.card f.ker ≤ Nat.card θ := Subgroup.card_le_of_le hkθ
  have h4 : Nat.card (↥M ⧸ θ) ≤ Nat.card f.range := by
    have hpos : 0 < Nat.card θ := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card (↥M ⧸ θ) * Nat.card θ = Nat.card f.range * Nat.card f.ker := by
          rw [← h1, ← h2]
      _ ≤ Nat.card f.range * Nat.card θ := Nat.mul_le_mul_left _ h3
  have hrange : f.range = ⊤ := Subgroup.eq_top_of_le_card _ (hcard.trans h4)
  intro y hy
  obtain ⟨l, hl⟩ : QuotientGroup.mk' N ⟨y, hy⟩ ∈ f.range := hrange ▸ Subgroup.mem_top _
  have h5 : (Subgroup.inclusion hMZ l)⁻¹ * ⟨y, hy⟩ ∈ N := QuotientGroup.eq.mp hl
  have h6 : (l : G)⁻¹ * y ∈ O :=
    ⟨(Subgroup.inclusion hMZ l)⁻¹ * ⟨y, hy⟩, by exact h5, rfl⟩
  have hy' : y = (l : G) * ((l : G)⁻¹ * y) := by group
  rw [hy']
  exact mul_mem (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right h6)

omit [Finite G] in
theorem le_centralizer_of_le_normalizer {Q : Subgroup G} {c : G} (hQ2 : IsPGroup 2 Q)
    (hQH : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G)) (hc3 : c ^ 3 = 1) :
    Q ≤ Subgroup.centralizer ({c} : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : q * c * q⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hQH hq) c).mp (Subgroup.mem_zpowers c))
      (inv_mem (Subgroup.mem_zpowers c))
  have h2 : q * c * q⁻¹ * c⁻¹ ∈ Q := by
    have h3 : c * q⁻¹ * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hcQ q⁻¹).mp (Q.inv_mem hq)
    have e : q * c * q⁻¹ * c⁻¹ = q * (c * q⁻¹ * c⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq h3
  have h4 : (q * c * q⁻¹ * c⁻¹) ^ 3 = 1 := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have h5 := Source.eq_one_of_pow_three_eq_one hQ2 h2 h4
  have h6 : q * c * q⁻¹ = c := by
    have e : q * c * q⁻¹ = (q * c * q⁻¹ * c⁻¹) * c := by group
    rw [e, h5, one_mul]
  calc q * c = q * c * q⁻¹ * q := by group
    _ = c * q := by rw [h6]

theorem mem_cQuot_of_centralizes {A L : Subgroup G}
    (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 7))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {q : G} (hqN : q ∈ Subgroup.normalizer (L : Set G))
    (hqA : ∀ e ∈ A ⊓ L, q * e = e * q) {k : ℕ} (hq2 : q ^ 2 ^ k = 1) :
    q ∈ Sec17.cQuot L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := Sec17.Proof17Res6.actSeven L φ with hψ
  set π := Sec17.Proof17Res6.projSeven L φ with hπ
  set m : Subgroup.normalizer (L : Set G) := ⟨q, hqN⟩ with hm
  set K : Subgroup ↥L := (A ⊓ L).subgroupOf L with hK
  have hK9 : Nat.card K = 9 := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hK3 : IsPGroup 3 K := IsPGroup.of_card (n := 2) (by rw [hK9]; norm_num)
  have hE9 : Nat.card (K.map π) = 9 := by
    rw [Sec17.TailProof.card_map_of_isPGroup_three π
      (Sec17.Proof17Res6.projSeven_ker_isPGroup L φ) hK3, hK9]
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eNine hE9
  have hcent : g * ψ m * g⁻¹ ∈
      Subgroup.centralizer (KFacts.KP2.eNine : Set (Equiv.Perm (Fin 7))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hg] at hx
    obtain ⟨y, ⟨e, he, rfl⟩, rfl⟩ := hx
    have heAL : (e : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp he
    have hcomm : ψ m * π e = π e * ψ m := by
      rw [← Sec17.Proof17Res6.actSeven_eq_projSeven L φ e, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hqA e heAL)
    change g * π e * g⁻¹ * (g * ψ m * g⁻¹) = g * ψ m * g⁻¹ * (g * π e * g⁻¹)
    calc g * π e * g⁻¹ * (g * ψ m * g⁻¹) = g * (π e * ψ m) * g⁻¹ := by group
      _ = g * (ψ m * π e) * g⁻¹ := by rw [hcomm]
      _ = g * ψ m * g⁻¹ * (g * π e * g⁻¹) := by group
  rw [KFacts.K412.centralizer_eNine] at hcent
  obtain ⟨i, j, hij⟩ := hcent
  have h3 : (g * ψ m * g⁻¹) ^ 3 = 1 := by rw [hij]; exact KFacts.KP2.eNineF_pow_three i j
  have h2 : (g * ψ m * g⁻¹) ^ 2 ^ k = 1 := by
    have hm2 : m ^ 2 ^ k = 1 := Subtype.ext (by simpa [hm] using hq2)
    rw [← MulAut.conj_apply, ← map_pow, ← map_pow, hm2, map_one, map_one]
  have h1 := eq_one_of_pow_three_of_pow_two h3 h2
  have hψ1 : ψ m = 1 := by
    have e : ψ m = g⁻¹ * (g * ψ m * g⁻¹) * g := by group
    rw [e, h1]
    group
  exact Sec17.Proof17Res6.mem_cQuot_of_actSeven_eq_one L φ hψ1

theorem exists_mem_scriptY0Star_of_le_centralizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h142 : Concl142 A (lB A)) (h155 : Item155 A (lB A))
    (hL4 : L ∈ scriptY4 A (lB A)) {V : Subgroup G} (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hVc : V ≤ Subgroup.centralizer ({c} : Set G)) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ∃ K ∈ scriptY0Star A (lB A), L ≤ K ∧ V ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set Y' := L ⊔ V with hY'def
  have hVL : V ≤ Subgroup.normalizer (L : Set G) :=
    (hVc.trans (centralizer_singleton_le_normalizer_zpowers c)).trans
      (normalizer_zpowers_le_normalizer_L h
        (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA))
  have hVQ : V ∈ scriptQ A (lB A) :=
    Sec17.Proof176.mem_scriptQ_of_le_centralizer h142 h.zpowers_mem_omegaA
      (not_three_dvd_of_isPGroup_two hV2) hAV hVc
  have hY'V : Y' ≤ Subgroup.normalizer (V : Set G) := sup_le hLV Subgroup.le_normalizer
  have hVO : V ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'V hV2
  have hO2 : CFSG.Open.pCoreOf 2 Y' ≠ ⊥ := fun h0 => hV1 (le_bot_iff.mp (h0 ▸ hVO))
  have hY'Δ : Y' = delta A (lB A) Y' :=
    le_antisymm (sup_le (hL4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hVQ le_sup_right))
      (delta_le _)
  have hY'c : Y' ≤ Subgroup.centralizer ({c} : Set G) := sup_le hD.le_centralizer hVc
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hY'c))
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, Sec14.le_normalizer_sup hD.le_normalizer hAV⟩, hO2⟩, hY'Δ⟩
  have hres : oPrimeResidualOf 3 Y' = L :=
    ((oPrimeResidualOf_eq_of_le le_sup_left fun x hx k hk =>
      mem_of_pow_three_of_mem_sup hVL hV2 hx hk).symm.trans hL4.2.1.symm)
  have hX4 : oPrimeResidualOf 3 Y' ∈ scriptY4 A (lB A) := by
    rw [hres]
    exact hL4
  have hY'eq : Y' = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y' := by
    rw [hres]
    exact le_antisymm (sup_le le_sup_left (hVO.trans le_sup_right))
      (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hΩ : omg155 A (oPrimeResidualOf 3 Y') := by
    rw [hres]
    exact Or.inr ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA, by
      rw [inf_idem, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]⟩
  obtain ⟨K, hK, hXK, hY'K⟩ := (h155 Y' hY'3 hX4 hY'eq).1 hΩ
  exact ⟨K, hK, hres ▸ hXK, le_sup_right.trans hY'K⟩

end Res10A7

open Res10A7

theorem step163A7PassX_of_res10
    (h131 : Item131) (h142 : Concl142R) (h155 : Item155R)
    (h162 : Item162R) : Step163A7PassX := by
  intro G _ _ A c L hR h7 hW hT Y hY hY7 a La ha hLa hLaY hac hQ w hw hcw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hR.toSec13Data
  obtain ⟨Q, ⟨⟨hQQ, hQle⟩, hQpi⟩, hQ1⟩ := hQ
  have hQ2 : IsPGroup 2 Q := (isPiSubgroup_piOf_iff Nat.prime_two Q).mp hQpi
  have hQY : Q ≤ Y := hQle.trans inf_le_left
  have hQH : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hQle.trans inf_le_right
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQQ.1.2.2
  have hcA : c ∈ A := hD.mem_A
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hQc : Q ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_le_normalizer hQ2 hQH (hAQ hcA) hc3
  have hHL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    normalizer_zpowers_le_normalizer_L hR
      (three_dvd_card_of_mem_lA hR hR.zpowers_mem_omegaA hR.mem_lA)
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := hQH.trans hHL
  have hLw : La.map (MulAut.conj w).toMonoidHom = L :=
    map_conj_eq_of_zpowers hR ha hLa hw hcw
  set Yw := Y.map (MulAut.conj w).toMonoidHom with hYwdef
  have hLYw : L ≤ Yw := by
    rw [← hLw]
    exact Subgroup.map_mono hLaY
  by_cases hcase : ∃ e ∈ A ⊓ L, ⁅Q, Subgroup.zpowers e⁆ ≠ ⊥
  ·
    obtain ⟨e, he, hne⟩ := hcase
    set T := ⁅Q, Subgroup.zpowers e⁆ with hTdef
    have hAe : A ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hD.commute he.1 hx) n)
    have hTQ : T ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr he.1).trans hAQ)
    have hTL : T ≤ L := by
      rw [hTdef, Subgroup.commutator_le]
      intro q hq x hx
      have hxL : x ∈ L := (Subgroup.zpowers_le.mpr he.2) hx
      rw [commutatorElement_def]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQN hq) x).mp hxL) (L.inv_mem hxL)
    have hAT : A ≤ Subgroup.normalizer (T : Set G) := Sec14.le_normalizer_commutator hAQ hAe
    refine ⟨1, one_mem _, ?_⟩
    rw [Late.map_conj_one]
    refine ⟨T, ⟨⟨mem_scriptQ_of_le hQQ hTQ hAT, le_inf ((hTQ.trans hQY).trans
      Subgroup.le_normalizer) ((hTL.trans hLYw).trans Subgroup.le_normalizer)⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two T).mpr (hQ2.to_le hTQ)⟩, hne⟩
  ·
    push Not at hcase
    exfalso
    have hqA : ∀ q ∈ Q, ∀ e ∈ A ⊓ L, q * e = e * q := by
      intro q hq e he
      have h1 : Q ≤ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcase e he)
      exact ((Subgroup.mem_centralizer_iff.mp (h1 hq)) e (Subgroup.mem_zpowers e)).symm
    obtain ⟨φL⟩ := h7
    obtain ⟨-, -, hcL, h9⟩ := Sec13.Res4Proof.facts131_of_alt7 h131 hD φL
    obtain ⟨φY⟩ := hY7
    have hYw : Yw ∈ scriptY0Star A (lB A) := map_conj_mem_scriptY0Star hw hY
    set eY : ↥Y ≃* ↥Yw := Y.equivMapOfInjective _ (MulAut.conj w).injective with heY
    have eq : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Yw ⧸ CFSG.pCore 2 ↥Yw :=
      QuotientGroup.congr _ _ eY (CFSG.pCore_map_iso 2 eY)
    have h2520L : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
      rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    have h2520Y : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 := by
      rw [Nat.card_congr φY.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    have h2520Yw : Nat.card (↥Yw ⧸ CFSG.pCore 2 ↥Yw) = 2520 := by
      rw [← Nat.card_congr eq.toEquiv, h2520Y]
    have hYwcov : Yw ≤ L ⊔ CFSG.Open.pCoreOf 2 Yw :=
      le_sup_pCoreOf_of_card_le hLYw (by rw [h2520Yw, h2520L])
    have hYweq : Yw = L ⊔ CFSG.Open.pCoreOf 2 Yw :=
      le_antisymm hYwcov (sup_le hLYw (CFSG.LieType.BorelTits.pCoreOf_le 2 Yw))
    have hL4 : L ∈ scriptY4 A (lB A) :=
      mem_scriptY4_of_cover hR (h142 G A c L hR) hYw.prop.1 hLYw hYwcov
    obtain ⟨eL⟩ := Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv hLYw hYweq
    have φL2 : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 7) :=
      eL.symm.trans (eq.symm.trans φY)
    set OL := CFSG.Open.pCoreOf 2 L with hOLdef
    have hQcQ : ∀ q ∈ Q, ∀ y ∈ L, q * y * q⁻¹ * y⁻¹ ∈ OL := by
      intro q hq y hy
      obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
      have hq2 : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hmem := mem_cQuot_of_centralizes φL2 h9 (hQN hq) (hqA q hq) hq2
      rw [← SetLike.mem_coe, Sec17.coe_cQuot] at hmem
      exact hmem.2 y hy
    have hOL2 : IsPGroup 2 OL := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
    have hNOL : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (OL : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
    have hQOL : Q ≤ Subgroup.normalizer (OL : Set G) := hQN.trans hNOL
    set V := Q ⊔ OL with hVdef
    have hV2 : IsPGroup 2 V := IsPGroup.to_sup_of_normal_right' hQ2 hOL2 hQOL
    have hV1 : V ≠ ⊥ := fun h0 => hQ1 (le_bot_iff.mp (h0 ▸ le_sup_left))
    have hVc : V ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le hQc ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hD.le_centralizer)
    have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
      Sec14.le_normalizer_sup hAQ (hD.le_normalizer.trans hNOL)
    have hLV : L ≤ Subgroup.normalizer (V : Set G) := by
      intro l hl
      refine Subgroup.mem_normalizer_fintype fun v hv => ?_
      have hv' : v ∈ ((Q ⊔ OL : Subgroup G) : Set G) := hv
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Q OL hQOL] at hv'
      obtain ⟨q, hq, o, ho, rfl⟩ := hv'
      have h1 : l * o * l⁻¹ ∈ OL :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer.trans hNOL hl) o).mp ho
      have h2 : q⁻¹ * l * q⁻¹⁻¹ * l⁻¹ ∈ OL := hQcQ q⁻¹ (Q.inv_mem hq) l hl
      have e : l * (q * o) * l⁻¹ = q * (q⁻¹ * l * q⁻¹⁻¹ * l⁻¹) * (l * o * l⁻¹) := by group
      rw [e]
      exact V.mul_mem (V.mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right h2))
        (Subgroup.mem_sup_right h1)
    obtain ⟨K, hK, hLK, hVK⟩ := exists_mem_scriptY0Star_of_le_centralizer hR (h142 G A c L hR)
      (h155 G A c L hR) hL4 hV2 hV1 hVc hAV hLV
    obtain ⟨x, hx, hYK⟩ := h162 G A c L hR Y hY K hK ⟨Q, ⟨⟨hQQ, le_inf
      (hQY.trans Subgroup.le_normalizer) (le_sup_left.trans hVK)⟩, hQpi⟩, hQ1⟩
    have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hx
    have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
      hHL (centralizer_singleton_le_normalizer_zpowers c
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA) hxC))
    have hLY : L ≤ Y := by
      rw [hYK, ← Late.map_conj_eq_of_mem_normalizer hxL]
      exact Subgroup.map_mono hLK
    have hYcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y :=
      le_sup_pCoreOf_of_card_le hLY (by rw [h2520Y, h2520L])
    set O := CFSG.Open.pCoreOf 2 Y with hOdef
    have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
    have hcO : c ∈ Subgroup.normalizer (O : Set G) :=
      (hY.prop.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)) hcA
    have hcsc : c ∈ Late.sectionCentralizer A Y O := by
      refine ⟨hcA, fun y hy => ?_⟩
      have hy' : y ∈ ((L ⊔ O : Subgroup G) : Set G) := hYcov hy
      rw [Subgroup.coe_mul_of_left_le_normalizer_right L O (hLY.trans hYO)] at hy'
      obtain ⟨l, hl, o, ho, rfl⟩ := hy'
      have hcl : c * l = l * c :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)).symm
      have h1 : c * o * c⁻¹ * o⁻¹ ∈ O :=
        O.mul_mem ((Subgroup.mem_normalizer_iff.mp hcO o).mp ho) (O.inv_mem ho)
      have h2 : l * (c * o * c⁻¹ * o⁻¹) * l⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hYO (hLY hl)) _).mp h1
      have e : c * (l * o) * c⁻¹ * (l * o)⁻¹ = l * (c * o * c⁻¹ * o⁻¹) * l⁻¹ := by
        calc c * (l * o) * c⁻¹ * (l * o)⁻¹ = (c * l) * o * c⁻¹ * o⁻¹ * l⁻¹ := by group
          _ = (l * c) * o * c⁻¹ * o⁻¹ * l⁻¹ := by rw [hcl]
          _ = l * (c * o * c⁻¹ * o⁻¹) * l⁻¹ := by group
      rw [e]
      exact h2
    rw [Step163Alt.sectionCentralizer_eq_of_config hR ⟨φL⟩ hT hY φY ha hLa hLaY] at hcsc
    exact hac (Res9A7.zpowers_eq_of_mem ha.2.1 hcsc hD.ne_one).symm

theorem step163A7_of_res10
    (h131 : Item131) (h142 : Concl142R) (h153 : Item153MainR)
    (h155 : Item155R) (h162 : Item162R) : Step163A7 :=
  step163A7_of_passX h162 h142 h153 (step163A7PassX_of_res10 h131 h142 h155 h162)

end CFSG.RankThree.PartTwo.Sec16

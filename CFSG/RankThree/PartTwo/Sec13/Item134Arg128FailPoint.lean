module

public import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailTools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarCoords
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A L K : Subgroup G} {c d : G}

theorem base_of_central (h45 : Sec4.Item4_5) (h131 : Item131) (hspor : SporadicModels131)
    (h415 : Sec4.Item4_15) (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hKeq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K)
    (hA6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hcen : ∀ P : Subgroup G, IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) →
      A ⊓ Sec4.thetaQuotCentralizer K ≤ (Subgroup.center P).map P.subtype) :
    Base A c L d K := by
  obtain ⟨-, heq, -, -⟩ := facts134 h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6
  exact ⟨h45, h131, hspor, h415, h, hJ, hdA, hd1, hS, hK, hLK, hA6, fun P hP => heq ▸ hcen P hP⟩

theorem inf_le_residual (H : Base A c L d K) :
    A ⊓ L ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  obtain ⟨hdL, S₀, hdS₀, hS₀d⟩ := H.exists_d_mem_L
  intro x hx
  exact mem_residual_of_pow_three H.h415 H.quot hdL H.ne_one ⟨S₀, hdS₀, hS₀d⟩ hx.2
    (Subgroup.mem_centralizer_singleton_iff.mpr (H.data.commute hx.1 H.mem_A)) (k := 1)
    (by rw [pow_one]; exact H.data.isElemAbelian.2 x hx.1)

theorem inf_thetaQuotCentralizer_eq {a : G} {J : Subgroup G} (hJ : Sec13Data G A a J) :
    A ⊓ Sec4.thetaQuotCentralizer J = Subgroup.zpowers a := by
  have h1 := hJ.sectionCentralizer_eq
  rw [sectionCentralizer_eq_inf hJ.le_normalizer] at h1
  exact SetLike.coe_injective h1

theorem zpowers_d_not_mem_omegaA (h422 : Sec4.Item4_22) (H : Base A c L d K)
    (heq : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    Subgroup.zpowers d ∉ omegaA A := by
  intro hdΩ
  obtain ⟨I, hI⟩ := item13SetupAt_of h422 H.h45 G H.data.toPartTwoStanding H.data.partTwoS_eq A
    H.data.mem_partTwoF H.data.not_mem_partTwoT d hdΩ
  obtain ⟨hIc, hAN, hsc, -⟩ := hI
  have hd3 := H.d_pow
  by_cases hIK : I = K
  · subst hIK
    rw [sectionCentralizer_eq_inf hAN, heq] at hsc
    have h0 : (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = Subgroup.zpowers d :=
      SetLike.coe_injective hsc
    have h1 := congrArg (fun X : Subgroup G => Nat.card X) h0
    rw [Base.card_B H, card_zpowers_of_pow_three hd3 H.ne_one] at h1
    omega
  · have hle : A ⊓ L ≤ Subgroup.zpowers d := by
      intro x hx
      have hxK : x ∈ K := H.residual_le (inf_le_residual H hx)
      have hmem : x ∈ Late.sectionCentralizer A I
          ((aschbacherSolvableCore 3 I).map I.subtype) := by
        refine ⟨hx.1, fun y hy => ?_⟩
        have h1 := Sec10.commutator_mem_theta_of_ne H.mem_K hIc (Ne.symm hIK) hxK hy
        have h2 : x * y * x⁻¹ * y⁻¹ ∈ I :=
          I.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN hx.1) y).mp hy) (I.inv_mem hy)
        have h3 : x * y * x⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) I := by
          rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hIc]
          exact ⟨h2, h1⟩
        exact h3
      rw [hsc] at hmem
      exact hmem
    have := Subgroup.card_le_of_le hle
    rw [H.card_inf, card_zpowers_of_pow_three hd3 H.ne_one] at this
    omega

theorem exists_sec13Data (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h : Sec13Data G A c L)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) : ∃ J : Subgroup G, Sec13Data G A a J := by
  obtain ⟨J, hJ⟩ := item13SetupAt_of h422 h45 G h.toPartTwoStanding h.partTwoS_eq A
    h.mem_partTwoF h.not_mem_partTwoT a ha
  exact ⟨J, { h.toPartTwoStanding with
    partTwoS_eq := h.partTwoS_eq
    mem_partTwoF := h.mem_partTwoF
    not_mem_partTwoT := h.not_mem_partTwoT
    zpowers_mem_omegaA := ha
    mem_lA := hJ }⟩

omit [Finite G] in
theorem conj_mem_thetaQuotCentralizer [Finite G] {J : Subgroup G} {x g : G}
    (hx : x ∈ Sec4.thetaQuotCentralizer J) (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    g * x * g⁻¹ ∈ Sec4.thetaQuotCentralizer J := by
  obtain ⟨hxN, hxl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨mul_mem (mul_mem hg hxN) (inv_mem hg),
    fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ J := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) l).mp hl
    simpa using this
  have h1 := Sec12.conj_mem_inSubgroup_theta hg (hxl _ hl')
  have e : g * ((g⁻¹ * l * g)⁻¹ * (x * (g⁻¹ * l * g) * x⁻¹)) * g⁻¹ =
      l⁻¹ * (g * x * g⁻¹ * l * (g * x * g⁻¹)⁻¹) := by group
  rw [e] at h1
  exact h1

omit [Finite G] in
theorem commute_of_pow_of_conj_mem {a y : G} (ha3 : a ^ 3 = 1) {k : ℕ} (hy : y ^ 3 ^ k = 1)
    (hya : y * a * y⁻¹ ∈ Subgroup.zpowers a) : y * a = a * y := by
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, one_mul]
  rcases conj_eq_or_eq_inv ha3 ha1 hya with h | h
  · calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [h]
  · have h2 : y ^ 2 * a = a * y ^ 2 := by
      have : y ^ 2 * a * (y ^ 2)⁻¹ = a := by
        calc y ^ 2 * a * (y ^ 2)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by rw [pow_two]; group
          _ = y * a⁻¹ * y⁻¹ := by rw [h]
          _ = (y * a * y⁻¹)⁻¹ := by group
          _ = a := by rw [h, inv_inv]
      calc y ^ 2 * a = y ^ 2 * a * (y ^ 2)⁻¹ * y ^ 2 := by group
        _ = a * y ^ 2 := by rw [this]
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have hy' : y = (y ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hy, one_mul]
    rw [hy']
    exact (Commute.pow_left (show Commute (y ^ 2) a from h2) (m + 1)).eq

theorem pow_six_conj (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) {a : G}
    (haA : a ∈ A) (hdA : d ∈ A) (hd1 : d ≠ 1) (had : a ∉ Subgroup.zpowers d) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) (hwa : w * a = a * w) {x : G}
    (hx : x ∈ A) : w ^ 6 * x * (w ^ 6)⁻¹ = x := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hx3 : x ^ 3 = 1 := hA.2 x hx
  set B := Subgroup.zpowers a ⊔ Subgroup.zpowers d with hB
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hdA)
  have hwdd : w * d * w⁻¹ = d ∨ w * d * w⁻¹ = d⁻¹ :=
    conj_eq_or_eq_inv hd3 hd1 ((Subgroup.mem_normalizer_iff.mp hwd d).mp (Subgroup.mem_zpowers d))
  have hconjB : ∀ g : G, g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) → g * a = a * g →
      ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro g hgd hga
    have hle : B ≤ B.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · change g * a * g⁻¹ ∈ B
        rw [hga, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      · change g * d * g⁻¹ ∈ B
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp hgd d).mp (Subgroup.mem_zpowers d))
    exact fun b hb => hle hb
  have hwB : ∀ b ∈ B, w * b * w⁻¹ ∈ B := hconjB w hwd hwa
  have hwa' : w⁻¹ * a = a * w⁻¹ := (Commute.inv_left (show Commute w a from hwa)).eq
  have hwB' : ∀ b ∈ B, w⁻¹ * b * w⁻¹⁻¹ ∈ B := hconjB w⁻¹ (inv_mem hwd) hwa'
  have hu_d : w ^ 2 * d = d * w ^ 2 := by
    have : w ^ 2 * d * (w ^ 2)⁻¹ = d := by
      rcases hwdd with h | h
      · calc w ^ 2 * d * (w ^ 2)⁻¹ = w * (w * d * w⁻¹) * w⁻¹ := by rw [pow_two]; group
          _ = d := by rw [h, h]
      · have h' : w * d⁻¹ * w⁻¹ = d := by
          rw [show w * d⁻¹ * w⁻¹ = (w * d * w⁻¹)⁻¹ by group, h, inv_inv]
        calc w ^ 2 * d * (w ^ 2)⁻¹ = w * (w * d * w⁻¹) * w⁻¹ := by rw [pow_two]; group
          _ = d := by rw [h, h']
    calc w ^ 2 * d = w ^ 2 * d * (w ^ 2)⁻¹ * w ^ 2 := by group
      _ = d * w ^ 2 := by rw [this]
  have hu_a : w ^ 2 * a = a * w ^ 2 := (Commute.pow_left (show Commute w a from hwa) 2).eq
  have huB : ∀ b ∈ B, w ^ 2 * b = b * w ^ 2 := by
    have hle : B ≤ Subgroup.centralizer ({w ^ 2} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · exact hu_a.symm
      · exact hu_d.symm
    exact fun b hb => (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm
  have hβ : ∃ β ∈ B, w ^ 2 * x * (w ^ 2)⁻¹ = x * β := by
    by_cases hxB : x ∈ B
    · exact ⟨1, one_mem B, by rw [huB x hxB, mul_inv_cancel_right, mul_one]⟩
    have hxC : x ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b (hBA hb) x hx
    have hsup : Subgroup.zpowers x ⊔ B = A := by
      have hle : Subgroup.zpowers x ⊔ B ≤ A := sup_le (Subgroup.zpowers_le.mpr hx) hBA
      have hc : ∀ y ∈ Subgroup.zpowers x, ∀ z ∈ B, y * z = z * y := fun y hy z hz =>
        hcomm y ((Subgroup.zpowers_le.mpr hx) hy) z (hBA hz)
      obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc
      have hB9 : Nat.card B = 9 := by
        have hc' : ∀ y ∈ Subgroup.zpowers a, ∀ z ∈ Subgroup.zpowers d, y * z = z * y :=
          fun y hy z hz => hcomm y ((Subgroup.zpowers_le.mpr haA) hy) z
            ((Subgroup.zpowers_le.mpr hdA) hz)
        obtain ⟨hcard', -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc'
        rw [zpowers_inf_eq_bot ha3 had, Subgroup.card_bot, mul_one,
          card_zpowers_of_pow_three ha3 (fun h => had (h ▸ one_mem _)),
          card_zpowers_of_pow_three hd3 hd1] at hcard'
        exact hcard'
      rw [zpowers_inf_eq_bot hx3 hxB, Subgroup.card_bot, mul_one,
        card_zpowers_of_pow_three hx3 (fun h => hxB (h ▸ one_mem _)), hB9] at hcard
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hA27, hcard])
    have hwx : w * x * w⁻¹ ∈ Subgroup.zpowers x ⊔ B := by
      rw [hsup]
      exact (Subgroup.mem_normalizer_iff.mp hwA x).mp hx
    obtain ⟨k, b, hb, hkb⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hxC hwx
    have hk : k % 3 ≠ 0 := by
      intro hk0
      apply hxB
      have hxk : x ^ k = 1 := by
        rw [← Int.mul_ediv_add_emod k 3, hk0, add_zero, zpow_mul,
          show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hx3, one_zpow]
      rw [hxk, one_mul] at hkb
      have : x = w⁻¹ * b * w⁻¹⁻¹ := by rw [← hkb]; group
      rw [this]
      exact hwB' b hb
    have hk2 : x ^ (k * k) = x := by
      have h1 : (k * k) % 3 = 1 := by
        have : k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases this with h | h <;> rw [Int.mul_emod, h] <;> norm_num
      rw [← Int.mul_ediv_add_emod (k * k) 3, h1, zpow_add, zpow_mul,
        show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hx3, one_zpow, one_mul, zpow_one]
    refine ⟨b ^ k * (w * b * w⁻¹), mul_mem (zpow_mem hb k) (hwB b hb), ?_⟩
    have hxb : Commute x b := hcomm x hx b (hBA hb)
    have hwx' : w * x * w⁻¹ = x ^ k * b := hkb
    calc w ^ 2 * x * (w ^ 2)⁻¹ = w * (w * x * w⁻¹) * w⁻¹ := by rw [pow_two]; group
      _ = w * (x ^ k * b) * w⁻¹ := by rw [hwx']
      _ = (w * x * w⁻¹) ^ k * (w * b * w⁻¹) := by rw [conj_zpow]; group
      _ = (x ^ k * b) ^ k * (w * b * w⁻¹) := by rw [hwx']
      _ = x ^ (k * k) * b ^ k * (w * b * w⁻¹) := by
          rw [(Commute.zpow_left hxb k).mul_zpow, ← zpow_mul]
      _ = x * (b ^ k * (w * b * w⁻¹)) := by rw [hk2, mul_assoc]
  obtain ⟨β, hβB, hβx⟩ := hβ
  have hβ3 : β ^ 3 = 1 := hA.2 β (hBA hβB)
  have hpow : ∀ n : ℕ, (w ^ 2) ^ n * x * ((w ^ 2) ^ n)⁻¹ = x * β ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have huβn : w ^ 2 * β ^ n * (w ^ 2)⁻¹ = β ^ n := by
        rw [(Commute.pow_right (show Commute (w ^ 2) β from huB β hβB) n).eq,
          mul_inv_cancel_right]
      calc (w ^ 2) ^ (n + 1) * x * ((w ^ 2) ^ (n + 1))⁻¹ =
          w ^ 2 * ((w ^ 2) ^ n * x * ((w ^ 2) ^ n)⁻¹) * (w ^ 2)⁻¹ := by
            rw [pow_succ']; group
        _ = (w ^ 2 * x * (w ^ 2)⁻¹) * (w ^ 2 * β ^ n * (w ^ 2)⁻¹) := by rw [ih]; group
        _ = x * β ^ (n + 1) := by rw [hβx, huβn, pow_succ', mul_assoc]
  have h6 := hpow 3
  rw [hβ3, mul_one, ← pow_mul] at h6
  exact h6

theorem false_of_autIn_pow_six (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {a : G} (haA : a ∈ A) (hdA : d ∈ A) (hd1 : d ≠ 1) (had : a ∉ Subgroup.zpowers d)
    {J : Subgroup G} (hJa : J ≤ Subgroup.centralizer ({a} : Set G)) {Q : Type} [Group Q]
    (e : Sec4.autIn J A ≃* Q) {q : Q} (hq : q ^ 6 ≠ 1) : False := by
  apply hq
  set σ := e.symm q with hσ
  obtain ⟨j, hjN, hjJ, hjσ⟩ := Sec4.mem_autIn_iff.mp σ.2
  have hσ6 : σ ^ 6 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hjσ, ← map_pow]
    ext x
    have hja : j * a = a * j := Subgroup.mem_centralizer_singleton_iff.mp (hJa hjJ)
    have := pow_six_conj hA hA27 haA hdA hd1 had hjN (hW hjN) hja x.2
    simpa using this
  have := congrArg e hσ6
  rw [map_pow, hσ, MulEquiv.apply_symm_apply, map_one] at this
  exact this

theorem mem_B_of_autIn (H : Base A c L d K)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {a : G} (haA : a ∈ A) {J : Subgroup G} (hJa : J ≤ Subgroup.centralizer ({a} : Set G))
    {σ : MulAut A} (hσ : σ ∈ Sec4.autIn J A) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  by_contra haB
  obtain ⟨j, hjN, hjJ, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  obtain ⟨e, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos j).ne' 3
    (by norm_num)
  have hj3 : (j ^ m) ^ 3 ^ e = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hjmN : j ^ m ∈ Subgroup.normalizer (A : Set G) := pow_mem hjN m
  obtain ⟨hjc, hjd⟩ := commute_of_pow H ⟨hjmN, hW hjmN⟩ hj3
  have hja : j ^ m * a = a * j ^ m :=
    (Commute.pow_left (show Commute j a from
      Subgroup.mem_centralizer_singleton_iff.mp (hJa hjJ)) m).eq
  have hAC : A ≤ Subgroup.centralizer ({j ^ m} : Set G) := by
    rw [← H.sup_zpowers_eq haA haB]
    refine sup_le (sup_le ?_ ?_) ?_ <;>
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact hjc.symm
    · exact hjd.symm
    · exact hja.symm
  apply hσ1
  have horder : orderOf (A.normalizerMonoidHom ⟨j, hjN⟩) = 3 := orderOf_eq_prime hσ3 hσ1
  have hpow1 : (A.normalizerMonoidHom ⟨j, hjN⟩) ^ m = 1 := by
    rw [← map_pow]
    ext x
    have hx := (Subgroup.mem_centralizer_singleton_iff.mp (hAC x.2)).symm
    change j ^ m * x * (j ^ m)⁻¹ = x
    rw [hx, mul_inv_cancel_right]
  exact absurd (horder ▸ orderOf_dvd_of_pow_eq_one hpow1) hm3

theorem false_of_normalizer_le (H : Base A c L d K) {S : Subgroup G}
    (hSD : SylowData A L d K S)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {a : G} (haA : a ∈ A) (haB : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (hWa : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    False := by
  obtain ⟨s₀, hs₀S, a₀, ha₀A, hmove⟩ := H.exists_moved hSD
  have hs₀W := H.S_le_normalizer hSD hs₀S
  obtain ⟨k, hk⟩ := hSD.isSylowOf.isPGroup ⟨s₀, hs₀S⟩
  have hs₀k : s₀ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨hs₀c, hs₀d⟩ := commute_of_pow H ⟨hs₀W, hW hs₀W⟩ hs₀k
  have hs₀a : s₀ * a = a * s₀ := commute_of_pow_of_conj_mem (H.data.isElemAbelian.2 a haA) hs₀k
    ((Subgroup.mem_normalizer_iff.mp (hWa hs₀W) a).mp (Subgroup.mem_zpowers a))
  have hAC : A ≤ Subgroup.centralizer ({s₀} : Set G) := by
    rw [← H.sup_zpowers_eq haA haB]
    refine sup_le (sup_le ?_ ?_) ?_ <;>
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact hs₀c.symm
    · exact hs₀d.symm
    · exact hs₀a.symm
  apply hmove
  rw [(Subgroup.mem_centralizer_singleton_iff.mp (hAC ha₀A)).symm, mul_inv_cancel_right]

theorem false_of_isSLThreePiTwo (H : Base A c L d K) {S T : Subgroup G}
    (hTD : TData A c L d S T)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {a : G} (had : a ∉ Subgroup.zpowers d) {J : Subgroup G} (hJ : Sec13Data G A a J)
    (hSL : Sec4.IsSLThreePiTwo (lBarA a J A)) : False := by
  obtain ⟨E, hEle, hEe, -, hEC, -⟩ := exists_E_of_isSLThreePiTwo hJ hSL
  have hCA := inf_thetaQuotCentralizer_eq hJ
  have hd3 := H.d_pow
  have ha3 : a ^ 3 = 1 := hJ.isElemAbelian.2 a hJ.mem_A
  obtain ⟨x, hxC, hxA⟩ : ∃ x ∈ E ⊓ Sec4.thetaQuotCentralizer J, x ∉ A := by
    by_contra hcon
    push Not at hcon
    apply hEC
    have hle : E ⊓ Sec4.thetaQuotCentralizer J ≤ Subgroup.zpowers a := by
      rw [← hCA]
      exact fun y hy => ⟨hcon y hy, hy.2⟩
    exact Subgroup.isCyclic_of_le hle
  have hxW : x ∈ Subgroup.normalizer (A : Set G) := (hEle hxC.1).2
  have hx3 : x ^ 3 = 1 := hEe.2 x hxC.1
  obtain ⟨e, heA, hxe⟩ : ∃ e ∈ A, x * e * x⁻¹ ≠ e := by
    by_contra hcon
    push Not at hcon
    apply hxA
    have hcomm : ∀ y ∈ Subgroup.zpowers x, ∀ z ∈ A, y * z = z * y := by
      intro y hy z hz
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hxz : x * z = z * x := by
        calc x * z = x * z * x⁻¹ * x := by group
          _ = z * x := by rw [hcon z hz]
      exact (Commute.zpow_left (show Commute x z from hxz) j).eq
    have hsup := isElemAbelian_sup (isElemAbelian_zpowers hx3) hJ.isElemAbelian hcomm
    have heq := hJ.eq_of_le hsup le_sup_right
    exact heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hcomm_d := conj_mem_zpowers_of_pow hTD ⟨hxW, hW hxW⟩ (k := 1) (by rwa [pow_one]) heA
  have hcomm_A : x * e * x⁻¹ * e⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp hxW e).mp heA) (A.inv_mem heA)
  have hcomm_C : x * e * x⁻¹ * e⁻¹ ∈ Sec4.thetaQuotCentralizer J := by
    have h1 := conj_mem_thetaQuotCentralizer (inv_mem hxC.2) (hJ.le_normalizer heA)
    have h2 : x * e * x⁻¹ * e⁻¹ = x * (e * x⁻¹ * e⁻¹) := by group
    rw [h2]
    exact mul_mem hxC.2 h1
  have hcomm_a : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers a := hCA ▸ ⟨hcomm_A, hcomm_C⟩
  have hne : x * e * x⁻¹ * e⁻¹ ≠ 1 := by
    intro h
    apply hxe
    rwa [mul_inv_eq_one] at h
  have hu3 : (x * e * x⁻¹ * e⁻¹) ^ 3 = 1 := hJ.isElemAbelian.2 _ hcomm_A
  have hzd : Subgroup.zpowers (x * e * x⁻¹ * e⁻¹) = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcomm_d) (by
      rw [card_zpowers_of_pow_three hd3 H.ne_one, card_zpowers_of_pow_three hu3 hne])
  have hza : Subgroup.zpowers (x * e * x⁻¹ * e⁻¹) = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcomm_a) (by
      rw [card_zpowers_of_pow_three ha3 hJ.ne_one, card_zpowers_of_pow_three hu3 hne])
  apply had
  rw [← hzd, hza]
  exact Subgroup.mem_zpowers a

end CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail

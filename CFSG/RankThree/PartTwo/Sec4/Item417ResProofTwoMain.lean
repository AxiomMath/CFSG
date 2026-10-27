module

public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofTwo
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec11.Item119Used
import CFSG.RankThree.PartTwo.Sec21.Item211ProofTransport
import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic
public import CFSG.RankThree.PartTwo.Sec4.Item417ResProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

open scoped Matrix

namespace Res417Two

variable {G : Type} [Group G] [Finite G]

theorem exists_slPi_model_two {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X) {n : ℕ}
    (hn : 1 ≤ n) (h : IsSLThreePiAt X (2 ^ n)) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π 2 n K ∧ ModThree π (2 ^ n) ∧
      2 < 2 ^ n ∧ Nonempty (X ≃* slPi π 3 (2 ^ n) K) := by
  obtain ⟨K, _, _, ⟨hK, hq3, ⟨φ⟩⟩ | ⟨hK, hq3, ⟨φ⟩⟩⟩ := h
  · refine ⟨true, K, inferInstance, ⟨Nat.prime_two, hn, hK⟩, hq3, ?_, ⟨φ⟩⟩
    have h4 : 2 ^ 2 ≤ 2 ^ n := by
      rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
      · norm_num at hq3
      · exact Nat.pow_le_pow_right (by norm_num) h2
    omega
  · have hPi : PiField false 2 n K := ⟨Nat.prime_two, hn, hK⟩
    refine ⟨false, K, inferInstance, hPi, hq3, ?_, ⟨φ⟩⟩
    by_contra h2
    have hn1 : n = 1 := by
      rcases (show n = 1 ∨ 2 ≤ n by omega) with h | h
      · exact h
      · have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
        omega
    subst hn1
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K := hPi.unitary
    have hcard : Nat.card X = 216 := by
      rw [Nat.card_congr φ.toEquiv]
      exact CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
    have := Fintype.ofFinite X
    have hsolv : Group.IsSolvable X :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    have : Group.IsPerfect X := hX.1
    have hnt : Nontrivial X := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    exact Group.IsPerfect.not_isSolvable X hsolv

omit [Finite G] in
theorem isTypeCOnSL_of_subgroupOf {L A : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (h : IsTypeCOnSL (A.subgroupOf (Subgroup.normalizer (L : Set G)))
      (L.subgroupOf (Subgroup.normalizer (L : Set G)))) : IsTypeCOnSL A L := by
  set N := Subgroup.normalizer (L : Set G) with hNdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  obtain ⟨hE, π, p, f, K, _, hK, hq, e, D, hD, hD1, hD2⟩ := h
  let φ : L.subgroupOf N ≃* L := Subgroup.subgroupOfEquivOfLe hLN
  have key : ∀ (g : G) (hg : g ∈ N) (hg' : (⟨g, hg⟩ : N) ∈
      Subgroup.normalizer ((L.subgroupOf N : Subgroup N) : Set N)) (z : L),
      φ.symm (L.normalizerMonoidHom ⟨g, hg⟩ z) =
        (L.subgroupOf N).normalizerMonoidHom ⟨⟨g, hg⟩, hg'⟩ (φ.symm z) := by
    intro g hg hg' z
    rfl
  refine ⟨hAL, π, p, f, K, inferInstance, hK, hq, φ.symm.trans e, D, hD, fun x => ?_,
    fun y hy => ?_⟩
  · have hx' : (⟨x, hAL x.2⟩ : N) ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.mpr x.2
    obtain ⟨y, hy, hyx⟩ := hD1 ⟨⟨x, hAL x.2⟩, hx'⟩
    refine ⟨y, hy, fun z => ?_⟩
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, key x (hAL x.2) (hE hx') z]
    exact hyx (φ.symm z)
  · obtain ⟨x', hx'⟩ := hD2 y hy
    have hxA : ((x' : N) : G) ∈ A := Subgroup.mem_subgroupOf.mp x'.2
    refine ⟨⟨(x' : N), hxA⟩, fun z => ?_⟩
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
      key ((x' : N) : G) (hAL hxA) (hE x'.2) z]
    exact hx' (φ.symm z)

theorem isTypeCOn_of_subgroupOf {L A : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (h : IsTypeCOn (A.subgroupOf (Subgroup.normalizer (L : Set G)))
      (L.subgroupOf (Subgroup.normalizer (L : Set G)))) : IsTypeCOn A L := by
  set N := Subgroup.normalizer (L : Set G) with hNdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  let φ : L.subgroupOf N ≃* L := Subgroup.subgroupOfEquivOfLe hLN
  have hnorm : ∀ g : N, g ∈ Subgroup.normalizer ((L.subgroupOf N : Subgroup N) : Set N) :=
    fun g => by
      rw [(Subgroup.normalizer_eq_top_iff).mpr (Subgroup.normal_in_normalizer)]
      exact Subgroup.mem_top g
  refine Sec21.Item211Proof.isTypeCOn_of_intertwine (thetaQuotCongr φ.symm)
    (fun τ hτ => ?_) (fun τ₁ hτ₁ => ?_) h
  · obtain ⟨g, hg, hgA, rfl⟩ := mem_autThetaQuot_iff.mp hτ
    refine ⟨_, mem_autThetaQuot_iff.mpr ⟨⟨g, hg⟩, hnorm _, Subgroup.mem_subgroupOf.mpr hgA, rfl⟩,
      fun z => ?_⟩
    induction z using QuotientGroup.induction_on with
    | H l => rfl
  · obtain ⟨g, hg, hgA, rfl⟩ := mem_autThetaQuot_iff.mp hτ₁
    have hgA' : (g : G) ∈ A := Subgroup.mem_subgroupOf.mp hgA
    refine ⟨_, mem_autThetaQuot_iff.mpr ⟨(g : G), hAL hgA', hgA', rfl⟩, fun z => ?_⟩
    induction z using QuotientGroup.induction_on with
    | H l => rfl

theorem eq_bot_of_noInv {L A T : Subgroup G} {c : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hcA : c ∈ A)
    (hc3 : orderOf c = 3) (hTL : T ≤ L) (hT2 : IsPGroup 2 T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hinv : ∀ a ∈ A, a ∉ Subgroup.zpowers c → ∀ t ∈ L, t * t = 1 → a * t = t * a → t = 1) :
    T = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hzc : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  have hrank : 3 ^ 2 * Nat.card (Subgroup.zpowers c) ≤ Nat.card A := by
    rw [Nat.card_zpowers, hc3, hA27]
    norm_num
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_inf_centralizer_sdiff Nat.prime_three
    ⟨hA.1, hA.2⟩ hzc hrank hAT hcop
  rw [← hgen, eq_bot_iff]
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hbc => ?_
  rw [le_bot_iff]
  by_contra hne
  have h2' : IsPGroup 2 (T ⊓ Subgroup.centralizer {b} : Subgroup G) := hT2.to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2'
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have htT : (t : G) ∈ T := (Subgroup.mem_inf.mp t.2).1
  have htb : (t : G) * b = b * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp t.2).2
  have ht2 : (t : G) * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact congrArg Subtype.val h
  have h1 := hinv b hb hbc t (hTL htT) ht2 htb.symm
  have : t = 1 := Subtype.ext h1
  rw [this, orderOf_one] at ht
  omega

theorem even_of_two_pow_mod_three {n : ℕ} (h : 2 ^ n % 3 = 1) : Even n := by
  rcases Nat.even_or_odd n with hev | ⟨k, rfl⟩
  · exact hev
  · exfalso
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at h
    norm_num at h

end Res417Two

open Res417Two

section Certs


@[expose] def Item417SL3FrameOdd : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) [L.Normal] (n : ℕ) (K : Type) [Field K],
    PiField false 2 n K → ModThree false (2 ^ n) → 2 < 2 ^ n →
    ∀ (e : L ≃* slPi false 3 (2 ^ n) K) (A : Subgroup H) (c : H),
      Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
      orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c →
      (∀ a ∈ A, ∃ y, IsPGLAt e a y) → (∃ b ∈ A, b ∈ L ∧ b ∉ Subgroup.zpowers c) →
      ∀ T : Subgroup H, T ≤ L → IsPGroup 2 T → A ≤ Subgroup.normalizer (T : Set H) → T = ⊥

@[expose] def Item417SL3FrameEven : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) [L.Normal] (n : ℕ) (K : Type) [Field K],
    PiField true 2 n K → ModThree true (2 ^ n) →
    ∀ (e : L ≃* slPi true 3 (2 ^ n) K) (A : Subgroup H) (c : H),
      Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
      orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c →
      (∀ a ∈ A, ∃ y, IsPGLAt e a y) → (∃ b ∈ A, b ∈ L ∧ b ∉ Subgroup.zpowers c) →
      Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))

@[expose] def Item417L3FrameOdd : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) [L.Normal] (n : ℕ) (K : Type) [Field K],
    PiField false 2 n K → ModThree false (2 ^ n) → 2 < 2 ^ n →
    ∀ (e : L ≃* projImage (slPi false 3 (2 ^ n) K)) (A : Subgroup H) (c : H),
      Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
      orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c →
      (∀ a ∈ A, ∃ y, IsPGLAtP e a y) →
      (∃ b : Fin 3 → (Fin 3 → K), LinearIndependent K b ∧ ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
        ∀ i, ∃ d : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i) →
      ∀ T : Subgroup H, T ≤ L → IsPGroup 2 T → A ≤ Subgroup.normalizer (T : Set H) → T = ⊥

@[expose] def Item417L3FrameEven : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) [L.Normal] (n : ℕ) (K : Type) [Field K],
    PiField true 2 n K → ModThree true (2 ^ n) →
    ∀ (e : L ≃* projImage (slPi true 3 (2 ^ n) K)) (A : Subgroup H) (c : H),
      Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
      orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c →
      (∀ a ∈ A, ∃ y, IsPGLAtP e a y) →
      (∃ b : Fin 3 → (Fin 3 → K), LinearIndependent K b ∧ ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
        ∀ i, ∃ d : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i) →
      Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))

theorem item417SL3PiTwo_of_frames (hSO : Item417SL3FrameOdd) (hSE : Item417SL3FrameEven)
    (hLO : Item417L3FrameOdd) (hLE : Item417L3FrameEven) : Item417SL3PiTwo := by
  intro G _ _ hG h2 L hL A E c hq hAL h1 n hn hL'
  have hq' := hq
  obtain ⟨hAmax, hcard, hAc, hc3, hE, hEA, T, hT, hTc⟩ := hq'
  have hA27 : Nat.card A = 27 := by rw [hcard]; norm_num
  have hEA' : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hA27, hE.2])
  have hcA : c ∈ A := by
    have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
    exact this.1
  obtain ⟨hTL, hT2, hTN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hT
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hEA' ▸ hTN
  set N := Subgroup.normalizer (L : Set G) with hNdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  set L' : Subgroup N := L.subgroupOf N with hL'def
  have hL'n : L'.Normal := Subgroup.normal_in_normalizer
  let eL : L' ≃* L := Subgroup.subgroupOfEquivOfLe hLN
  have hLq' : IsQuasisimple L' := LocalCores.isQuasisimple_of_mulEquiv eL.symm hL.1
  have hA' : Maximal (fun B : Subgroup N => CFSG.Assembly.IsElemAbelian 3 B) (A.subgroupOf N) :=
    Sec11.maximal_subgroupOf_of_le (fun B hB hAB => hAmax.eq_of_ge hB hAB) hAmax.prop hAL
  have hcardA' : Nat.card (A.subgroupOf N) = 27 := by
    rw [← hA27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hc3' : orderOf (⟨c, hAL hcA⟩ : N) = 3 := by rw [Subgroup.orderOf_mk]; exact hc3
  have hAc' := Res417.inf_centralizer_subgroupOf hAc (hAL hcA)
  have hLL : L'.map N.subtype = L := by
    rw [hL'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLN]
  have hnofield : ∀ σ : N, σ ∈ A.subgroupOf N → ¬ InducesStdKind L' σ .field := by
    intro σ hσ hσf
    have h1' := Sec13.inducesStdKind_sub N L' hσf
    rw [hLL] at h1'
    exact h1 ⟨σ, Subgroup.mem_subgroupOf.mp hσ, Or.inl h1'⟩
  have hTL' : T.subgroupOf N ≤ L' := fun t ht => Subgroup.mem_subgroupOf.mpr
    (hTL (Subgroup.mem_subgroupOf.mp ht))
  have hT2' : IsPGroup 2 (T.subgroupOf N) :=
    hT2.comap_of_injective N.subtype N.subtype_injective
  have hAT' : A.subgroupOf N ≤ Subgroup.normalizer ((T.subgroupOf N : Subgroup N) : Set N) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hAT (Subgroup.mem_subgroupOf.mp hx)) y
  have hTbot : T.subgroupOf N = ⊥ → False := by
    intro hbot
    apply hTc
    have : T = ⊥ := by
      rw [eq_bot_iff]
      intro t ht
      have h1' : (⟨t, hLN (hTL ht)⟩ : N) ∈ T.subgroupOf N := Subgroup.mem_subgroupOf.mpr ht
      rw [hbot, Subgroup.mem_bot] at h1'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1')
    rw [this]
    exact bot_le
  have hlift : (∀ a ∈ A.subgroupOf N, a ∉ Subgroup.zpowers (⟨c, hAL hcA⟩ : N) →
      ∀ t ∈ L', t * t = 1 → a * t = t * a → t = 1) →
      ∀ a ∈ A, a ∉ Subgroup.zpowers c → ∀ t ∈ L, t * t = 1 → a * t = t * a → t = 1 := by
    intro hN a ha hac t htL ht2 hat
    have hac' : (⟨a, hAL ha⟩ : N) ∉ Subgroup.zpowers (⟨c, hAL hcA⟩ : N) := by
      rintro ⟨k, hk⟩
      apply hac
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have := hN ⟨a, hAL ha⟩ (Subgroup.mem_subgroupOf.mpr ha) hac' ⟨t, hLN htL⟩
      (Subgroup.mem_subgroupOf.mpr htL) (Subtype.ext ht2) (Subtype.ext hat)
    exact congrArg Subtype.val this
  have hnoinv : (∀ a ∈ A, a ∉ Subgroup.zpowers c → ∀ t ∈ L, t * t = 1 → a * t = t * a →
      t = 1) → False := by
    intro hinv
    have hT1 := Res417Two.eq_bot_of_noInv hAmax.prop hA27 hcA hc3 hTL hT2 hAT hinv
    exact hTc (hT1 ▸ bot_le)
  have hautG : Nonempty (autIn L' (A.subgroupOf N) ≃* Equiv.Perm (Fin 3)) →
      Nonempty (autIn L A ≃* Equiv.Perm (Fin 3)) := by
    rintro ⟨φ⟩
    obtain ⟨ψ⟩ := Sec13.nonempty_autIn_subgroupOf_equiv N hLN hAL
    exact ⟨ψ.symm.trans φ⟩
  rcases hL' with hSL | hPSL
  ·
    obtain ⟨π, K, _, hK, hqK, hq2, ⟨e⟩⟩ :=
      exists_slPi_model_two hLq' hn (Res417.isSLThreePiAt_congr eL hSL)
    have hθ := aschbacherSolvableCore_eq_bot_of_slPi hK hqK hLq' e
    have : Group.IsPerfect L' := hLq'.1
    have hpgl : ∀ a ∈ A.subgroupOf N, ∃ y, IsPGLAt e a y := by
      intro a ha
      have ha3 : (⟨a, mem_normalizer_of_normal a⟩ : Subgroup.normalizer (L' : Set N)) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hA'.1.2 a ha)
      rcases slAct_pgl_or_field hK hq2 hθ e _ ha3 with ⟨y, hy, hys⟩ | ⟨hkind, -⟩
      · exact ⟨y, hy, hys⟩
      · exact (hnofield a ha hkind).elim
    rcases Res417Two.typeC_or_noInv_SL hK hqK e hA' (by rw [hcardA']) hc3' hAc' hpgl with
      ⟨b, hbA, hbL, hbc⟩ | hinv
    · obtain ⟨-, h9, hC⟩ :=
        alt411_one_of_pgl hK hqK e hA' (by rw [hcardA']) hc3' hAc' hpgl hbA hbL hbc
      cases π
      · exact (hTbot (hSO N L' n K hK hqK hq2 e (A.subgroupOf N) _ hA' hcardA' hc3' hAc' hpgl
          ⟨b, hbA, hbL, hbc⟩ _ hTL' hT2' hAT')).elim
      · have hev := Res417Two.even_of_two_pow_mod_three hqK
        exact ⟨⟨n, by omega, hev, Or.inr ⟨hSL, isTypeCOnSL_of_subgroupOf hAL hC⟩⟩,
          hautG (hSE N L' n K hK hqK e (A.subgroupOf N) _ hA' hcardA' hc3' hAc' hpgl
            ⟨b, hbA, hbL, hbc⟩)⟩
    · exact (hnoinv (hlift hinv)).elim
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨π, K, _, hK, hqK, hq2, ⟨e⟩⟩ :=
      exists_pslPi_model hn (Res417.isoLThreePi_congr eL hPSL) hLq'
    have hθ := aschbacherSolvableCore_eq_bot_proj hK hqK hLq' e
    have : Group.IsPerfect L' := hLq'.1
    have := isPerfect_projImage_of_equiv e
    have hpgl : ∀ a ∈ A.subgroupOf N, ∃ y, IsPGLAtP e a y := by
      intro a ha
      have ha3 : (⟨a, mem_normalizer_of_normal a⟩ : Subgroup.normalizer (L' : Set N)) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hA'.1.2 a ha)
      rcases pslAct_pgl_or_field hK hq2 hθ e _ ha3 with ⟨y, hy, hys⟩ | ⟨hkind, -⟩
      · exact ⟨y, hy, hys⟩
      · exact (hnofield a ha hkind).elim
    rcases Res417Two.frame_or_noInv_PSL hK hqK hθ e hA' (by rw [hcardA']) hc3' hAc' hpgl with
      ⟨hC, hframe⟩ | hinv
    · cases π
      · exact (hTbot (hLO N L' n K hK hqK hq2 e (A.subgroupOf N) _ hA' hcardA' hc3' hAc' hpgl
          hframe _ hTL' hT2' hAT')).elim
      · have hev := Res417Two.even_of_two_pow_mod_three hqK
        have hiso : Nonempty (L ≃* projSL 3 (GaloisField 2 n)) := by
          rcases hPSL with ⟨-, hφ⟩ | ⟨h3, -⟩
          · exact hφ
          · change 2 ^ n % 3 = 1 at hqK
            omega
        exact ⟨⟨n, by omega, hev, Or.inl ⟨hiso, isTypeCOn_of_subgroupOf hAL hC⟩⟩,
          hautG (hLE N L' n K hK hqK e (A.subgroupOf N) _ hA' hcardA' hc3' hAc' hpgl hframe)⟩
    · exact (hnoinv (hlift hinv)).elim

theorem item4_17SL3Pi_of_frames
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSO : Item417SL3FrameOdd) (hSE : Item417SL3FrameEven) (hLO : Item417L3FrameOdd)
    (hLE : Item417L3FrameEven) : Item4_17SL3Pi :=
  item4_17SL3Pi_of hGA (item417SL3PiTwo_of_frames hSO hSE hLO hLE)

end Certs

end CFSG.RankThree.PartTwo.Sec4

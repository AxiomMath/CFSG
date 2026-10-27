module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma4Four
public import CFSG.Quasithin.Vol2.Ch12Sec8Six
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

namespace L1286

theorem commutator_eq_bot_of_le {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁)) {g : G}
    (hg : V₁ ≤ CFSG.conjugate V g) : ⁅V, CFSG.conjugate V g⁆ = ⊥ := by
  obtain ⟨k, hk, hkg⟩ := lemma12_8_3_three h hV₁ hg
  rw [← hkg]
  have hVU : V ≤ u128 V V₁ := le_conjClosure _ _
  have hVkU : CFSG.conjugate V k ≤ u128 V V₁ := by
    intro x hx
    have hx' : k * x * k⁻¹ ∈ V := SteinbergBS.mem_conjugate_iff.1 hx
    have h1 := mem_conjClosure (Subgroup.inv_mem _ hk) hx'
    have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
    rwa [e] at h1
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  have hab : (⟨a, hVU ha⟩ : ↥(u128 V V₁)) * ⟨b, hVkU hb⟩ = ⟨b, hVkU hb⟩ * ⟨a, hVU ha⟩ :=
    hU.is_comm.comm _ _
  have hab' : a * b = b * a := congrArg Subtype.val hab
  rw [Subgroup.mem_bot, commutatorElement_def, hab']
  group

omit [Finite G] in
theorem exists_two_pow_mem_of_mem_sup {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {c : G} (hc : c ∈ L ⊔ T) :
    ∃ k : ℕ, c ^ 2 ^ k ∈ L := by
  have hc' : c ∈ (L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]
    exact hc
  obtain ⟨l, hl, t, ht, rfl⟩ := hc'
  have key : ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', h⟩ := ih
      refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), mul_mem hl' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hTL (pow_mem ht m)) l).1 hl
      · rw [pow_succ, h]
        group
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨l', hl', h⟩ := key (2 ^ k)
  exact ⟨k, by rw [h, htk, mul_one]; exact hl'⟩

theorem inf_centralizer_eq_pCoreOf_sup (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hred : IsTwoReducedIn (L ⊔ T) V) :
    T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := h.hyp
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hCL : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [inf_centralizer_eq_pCoreOf h1222 h]
    exact LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    intro c
    obtain ⟨k, hk⟩ := exists_two_pow_mem_of_mem_sup hT2 hyp.normalizes c.2.1
    have hkC : (c : G) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨hk, pow_mem c.2.2 _⟩
    obtain ⟨m, hm⟩ := hCL ⟨_, hkC⟩
    have hm' : ((c : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    refine ⟨k + m, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hm']
  have hCN : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hLTV)
  have hCO : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCN hC2
  have hsyl : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hOC : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) :=
    hred.2.2.2 _ (LieType.BorelTits.pCoreOf_le 2 _) (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      fun d hd => by
        obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
        refine ⟨k, ?_⟩
        have := congrArg Subtype.val hk
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
        rw [this]
        exact Subgroup.one_mem _
  exact le_antisymm ((inf_le_inf_right _ le_sup_right).trans hCO) (le_inf hOT hOC)

theorem hypF81_of_abelian (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ H : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁))
    (hH : IsHzOne T L V₁ H) : HypF81 T V L V₁ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := h.hyp
  have hA := lemma12_8_4_one h1222 h hV₁ hH
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hyp.irrPlus.2.2.1 hTV
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hVO : V ≤ pCoreOf 2 (L ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVLT hLTV hVp
  have hO1 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun hb => hyp.irrPlus.2.1 (le_bot_iff.1 (hb ▸ hVO))
  have hLTchar : CharTwo (L ⊔ T) :=
    charTwo_of_inH hyp.qtke.2.1 (hyp.sylow.1.toSylow hyp.sylow.2) ⟨le_sup_right, hO1⟩
  have hreduced : IsTwoReducedIn (L ⊔ T) V :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hred⟩
  have hLn : ((L).subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hyp.normalizes)
  refine
    { sylow := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_top
      elemAbelian := hA.elemAbelian
      normalizes_L := hyp.normalizes
      oTwoRes_eq := by rw [oTwoRes_eq_oTwoUpper]; exact hA.oTwo_eq.symm
      charTwo_L := hLTchar.of_normal le_sup_left hLn
      reduced := hreduced
      cT := inf_centralizer_eq_pCoreOf_sup h1222 h hreduced
      V₁_ne_bot := hA.ne_bot
      V₁_le_V := hA.le_V
      T_normalizes_V₁ := hA.T_le_normV₁
      weak_a := fun g hg => ?_
      V₁_lt_V := hA.irred.1
      irred := fun W h1 h2 h3 => hA.irred.2.2.2 W h1 h2 (by rw [lOne_eq_L₁Of]; exact h3)
      H_normalizes_V₁ := hA.H_le
      L₁T_le_H := by rw [← lOne_eq_L₁Of]; exact hA.lOne_sup_le
      charTwo_H := hA.charTwo
      ker_le := ?_
      o2_trivial := ?_ }
  ·
    have hle := le_of_card_eq_two_of_inf_ne_bot hV₁2 hg
    have e : conjSub g⁻¹ V = CFSG.conjugate V g := by
      ext x
      rw [mem_conjSub, SteinbergBS.mem_conjugate_iff, inv_inv]
    rw [e] at hle ⊢
    exact commutator_eq_bot_of_le h hV₁ hU hle
  ·
    rw [← lemma12_8_4_four h1222 h37 h38 h39 G T L V n h V₁ H hV₁ hH]
    exact coreIn_centralizerMod_le hA.H_le (hA.V_le_T.trans hA.T_le_normV₁)
  ·
    by_contra hne
    obtain ⟨N, hN⟩ := exists_inM_of_pCoreOf_ne_bot hne
    have hUM := lemma_1_2_7_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39 hyp.sylow
      hyp.maximal
    rw [hyp.conjClosure_eq] at hUM
    have hNM := hUM.2 N ⟨hN.1, le_sup_left.trans hN.2⟩
    exact hH.2.2 (hNM ▸ le_sup_right.trans hN.2)

theorem hypF98_of_abelian (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ H : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁))
    (hH : IsHzOne T L V₁ H) : HypF98 T V L V₁ V H :=
  (hypF81_of_abelian h1222 h37 h38 h39 h hV₁ hU hH).toHypF98 (by simpa using hV₁.2.1)

end L1286

end CFSG.Quasithin.H13

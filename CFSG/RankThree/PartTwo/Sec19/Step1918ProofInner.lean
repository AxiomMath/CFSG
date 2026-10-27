module

public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.Coprime.InvolutionFixedRankBound
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.Assembly.RankThreeEven (projSL)

namespace Step1918Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreAct_of_mem {K : Subgroup G} {u : G} (hu : u ∈ K) :
    Step199Proof.pCoreAct K ⟨u, Subgroup.le_normalizer hu⟩ =
      MulAut.conj ((⟨u, hu⟩ : K) : K ⧸ CFSG.pCore 2 K) := by
  ext x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Step199Proof.pCoreAct_mk _ k ⟨u * k * u⁻¹, K.mul_mem (K.mul_mem hu k.2) (K.inv_mem hu)⟩
    rfl, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

omit [Finite G] in
theorem pCoreAct_eq_one_iff {K : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    Step199Proof.pCoreAct K ⟨x, hx⟩ = 1 ↔
      ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have hN : ∀ k ∈ K, CFSG.Open.pCoreOf 2 K ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) := fun _ _ => Subgroup.le_normalizer
  constructor
  · intro h k hk
    have hmem : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hx k).mp hk
    have h1 := congrArg (fun σ : MulAut (K ⧸ CFSG.pCore 2 K) =>
      σ ((⟨k, hk⟩ : K) : K ⧸ CFSG.pCore 2 K)) h
    simp only [MulAut.one_apply] at h1
    rw [Step199Proof.pCoreAct_mk _ ⟨k, hk⟩ ⟨_, hmem⟩ rfl] at h1
    have h2 : (⟨k, hk⟩ : K)⁻¹ * ⟨_, hmem⟩ ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp h1.symm
    rw [Step1911EndProof.mem_pCore_iff] at h2
    have h3 : k * (k⁻¹ * (x * k * x⁻¹)) * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) _).mp
        (by simpa using h2)
    rwa [show k * (k⁻¹ * (x * k * x⁻¹)) * k⁻¹ = x * k * x⁻¹ * k⁻¹ by group] at h3
  · intro h
    ext q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hmem : x * (k : G) * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hx k).mp k.2
    rw [Step199Proof.pCoreAct_mk _ k ⟨_, hmem⟩ rfl, MulAut.one_apply]
    apply QuotientGroup.eq.mpr
    rw [Step1911EndProof.mem_pCore_iff]
    have h1 := h k k.2
    have h2 : (k : G)⁻¹ * (x * k * x⁻¹ * (k : G)⁻¹) * k ∈ CFSG.Open.pCoreOf 2 K := by
      have h3 := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
        (K.inv_mem k.2)) _).mp h1
      rwa [inv_inv] at h3
    have e : (((⟨_, hmem⟩ : K)⁻¹ * k : K) : G) =
        ((k : G)⁻¹ * (x * k * x⁻¹ * (k : G)⁻¹) * k)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact inv_mem h2

theorem card_le_nine_of_L34 {X : Type} [Group X] [Finite X]
    (ψ : X ≃* projSL 3 (GaloisField 2 2)) {W : Subgroup (MulAut X)}
    (hW : CFSG.Assembly.IsElemAbelian 3 W) : Nat.card W ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk := KFacts.L34.card_galoisField_two_two
  have hW3 : IsPGroup 3 W := fun w => ⟨1, Subtype.ext (by simpa using hW.2 w w.2)⟩
  obtain ⟨n, hn⟩ := hW3.exists_card_eq
  have hle := CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian (by norm_num)
    (Sec4.isElementaryAbelian_of_isElemAbelian hW) hn
  rw [KFacts.L34.pRank_three_mulAut_of_mulEquiv hk
    (ψ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 2)))] at hle
  rw [hn]
  calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    _ = 9 := by norm_num

theorem exists_conj_mem_of_sylow {X : Type} [Group X] [Finite X] {U V : Subgroup X}
    (hU3 : IsPGroup 3 U) (hU9 : Nat.card U = 9) (hV3 : IsPGroup 3 V) (hV1 : V ≠ ⊥)
    (hX : (∀ Q : Sylow 3 X, Nat.card Q ≤ 9) ∨
      ((∀ Q : Sylow 3 X, Nat.card Q ≤ 27) ∧ 9 ≤ Nat.card V)) :
    ∃ k : X, ∃ u ∈ U, u ≠ 1 ∧ k * u * k⁻¹ ∈ V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hVQ⟩ := hV3.exists_le_sylow
  obtain ⟨k, hk⟩ := Late.exists_map_conj_le_sylow hU3 Q
  set U' := U.map (MulAut.conj k).toMonoidHom with hU'
  have hU'9 : Nat.card U' = 9 := by
    rw [hU', Subgroup.card_map_of_injective (MulAut.conj k).injective, hU9]
  have hmemU' : ∀ v ∈ U', ∃ u ∈ U, k * u * k⁻¹ = v := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  have hQ3 : IsPGroup 3 (Q : Subgroup X) := Q.isPGroup'
  have hne : U' ⊓ V ≠ ⊥ := by
    rcases hX with hQ9 | ⟨hQ27, hV9⟩
    · have heq : U' = Q := Subgroup.eq_of_le_of_card_ge hk (by rw [hU'9]; exact hQ9 Q)
      rw [heq, inf_eq_right.mpr hVQ]
      exact hV1
    · by_cases hVQ' : V = Q
      · rw [hVQ', inf_eq_left.mpr hk]
        intro h
        rw [h, Subgroup.card_bot] at hU'9
        norm_num at hU'9
      · have hlt : V < Q := lt_of_le_of_ne hVQ hVQ'
        obtain ⟨x, hxQ, hxV, hxN⟩ := Late.exists_mem_normalizer_not_mem_of_lt hQ3 hlt
        have hVx : V < V ⊔ Subgroup.zpowers x :=
          lt_of_le_of_ne le_sup_left fun h => hxV (h ▸ Subgroup.mem_sup_right
            (Subgroup.mem_zpowers x))
        have hVxQ : V ⊔ Subgroup.zpowers x ≤ Q := sup_le hVQ (Subgroup.zpowers_le.mpr hxQ)
        have hcardQ : Nat.card (Q : Subgroup X) ≤ 27 := hQ27 Q
        obtain ⟨n, hn⟩ := hQ3.exists_card_eq
        obtain ⟨m, hm⟩ := (hQ3.to_le hVxQ).exists_card_eq
        obtain ⟨j, hj⟩ := hV3.exists_card_eq
        have hdvdV : Nat.card V ∣ Nat.card (V ⊔ Subgroup.zpowers x : Subgroup X) :=
          Subgroup.card_dvd_of_le le_sup_left
        have hdvdQ : Nat.card (V ⊔ Subgroup.zpowers x : Subgroup X) ∣ Nat.card (Q : Subgroup X) :=
          Subgroup.card_dvd_of_le hVxQ
        have hlt' : Nat.card V < Nat.card (V ⊔ Subgroup.zpowers x : Subgroup X) :=
          Subgroup.card_lt_of_lt hVx
        have hn3 : n ≤ 3 := by
          by_contra h
          have : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hj2 : 2 ≤ j := by
          by_contra h
          have : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rw [hj, hm] at hlt'
        have hjm : j < m := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt'
        rw [hm, hn] at hdvdQ
        have hmn : m ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvdQ
        have hpow : 3 ^ n ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        have heqQ : V ⊔ Subgroup.zpowers x = Q :=
          Subgroup.eq_of_le_of_card_ge hVxQ (by rw [hm, hn]; exact hpow)
        have hQN : (Q : Subgroup X) ≤ Subgroup.normalizer (V : Set X) := by
          rw [← heqQ]
          exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN)
        have h1 := Sec6.card_sup_mul_card_inf (hk.trans hQN)
        have h2 : Nat.card (U' ⊔ V : Subgroup X) ≤ 27 :=
          (Subgroup.card_le_of_le (sup_le hk hVQ)).trans hcardQ
        intro hbot
        rw [hbot, Subgroup.card_bot, mul_one, hU'9] at h1
        nlinarith
  obtain ⟨⟨v, hvU', hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨u, hu, rfl⟩ := hmemU' v hvU'
  refine ⟨k, u, hu, fun h => hv1 ?_, hvV⟩
  apply Subtype.ext
  change k * u * k⁻¹ = 1
  rw [h, mul_one, mul_inv_cancel]

theorem exists_conj_mem_zpowers {C : Subgroup G}
    (hC : ∀ X : Subgroup G, X ≤ C → CFSG.Assembly.IsElemAbelian 3 X → Nat.card X ≤ 3)
    {w c : G} (hwC : w ∈ C) (hcC : c ∈ C) (hw3 : orderOf w = 3) (hc3 : orderOf c = 3) :
    ∃ y ∈ C, y * w * y⁻¹ ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : ∀ {a : G}, orderOf a = 3 → IsPGroup 3 (Subgroup.zpowers a) := fun {a} ha =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨Q, hcQ⟩ := ((hz3 hc3).comap_subtype (K := C)).exists_le_sylow
  obtain ⟨y, hy⟩ := Late.exists_map_conj_le_sylow ((hz3 hw3).comap_subtype (K := C)) Q
  set Q' : Subgroup G := (Q : Subgroup C).map C.subtype with hQ'
  have hQ'3 : IsPGroup 3 Q' := Q.isPGroup'.map C.subtype
  have hQ'C : Q' ≤ C := Subgroup.map_subtype_le _
  have hcyc : IsCyclic Q' := isCyclic_of_forall_elemAbelian_card_le_three hQ'3 fun X hX hXe =>
    hC X (hX.trans hQ'C) hXe
  have hcQ' : c ∈ Q' := ⟨⟨c, hcC⟩, hcQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c)),
    rfl⟩
  have hywQ' : (y : G) * w * (y : G)⁻¹ ∈ Q' := by
    refine ⟨y * ⟨w, hwC⟩ * y⁻¹, hy ⟨⟨w, hwC⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_zpowers w), rfl⟩, ?_⟩
    simp
  set w' : G := (y : G) * w * (y : G)⁻¹ with hw'
  have hw'3 : orderOf w' = 3 := by
    rw [hw', ← hw3]
    exact (MulAut.conj (y : G)).orderOf_eq w
  have heq : (Subgroup.zpowers w').subgroupOf Q' = (Subgroup.zpowers c).subgroupOf Q' := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.zpowers_le.mpr hywQ')).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcQ')).toEquiv,
      Nat.card_zpowers, Nat.card_zpowers, hw'3, hc3]
  refine ⟨y, y.2, ?_⟩
  have h1 : (⟨w', hywQ'⟩ : Q') ∈ (Subgroup.zpowers w').subgroupOf Q' :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers w')
  rw [heq] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem exists_conj_mem_of_mem_sup {E O : Subgroup G} (hE : IsE27 E) (hO2 : IsPGroup 2 O)
    (hEO : E ≤ Subgroup.normalizer (O : Set G)) {d : G} (hd : d ∈ E ⊔ O) (hd3 : d ^ 3 = 1) :
    ∃ t ∈ E ⊔ O, t⁻¹ * d * t ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := E ⊔ O with hP
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨n, hn⟩ := hO2.exists_card_eq
    rw [hn]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hE3 := hE.isPGroup
  have hEP : E ≤ P := le_sup_left
  have hcardP := Sec6.card_sup_mul_card_inf hEO
  rw [CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hO3 hE3, Subgroup.card_bot,
    mul_one] at hcardP
  have hrel := Subgroup.relIndex_mul_card E P
  rw [inf_eq_left.mpr hEP, hcardP] at hrel
  have hrel' : E.relIndex P = Nat.card O := by
    have hpos : 0 < Nat.card E := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hrel, mul_comm])
  have hSyl : IsSylowOf 3 E P := isSylowOf_iff.mpr ⟨hEP, hE3, by rw [hrel']; exact hO3⟩
  obtain ⟨S, hS⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hd3' : IsPGroup 3 ((Subgroup.zpowers d).subgroupOf P) := by
    refine IsPGroup.comap_subtype ?_
    rcases eq_or_ne d 1 with h1 | h1
    · rw [h1, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_bot
    · exact IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime hd3 h1, pow_one])
  obtain ⟨T, hT⟩ := hd3'.exists_le_sylow
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq P S T
  have hdT : (⟨d, hd⟩ : P) ∈ (T : Subgroup P) :=
    hT (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers d))
  rw [← ht, Sylow.coe_subgroup_smul] at hdT
  obtain ⟨s, hs, hse⟩ := hdT
  refine ⟨t, t.2, ?_⟩
  have hsE : ((s : P) : G) ∈ E := by
    have : s ∈ E.subgroupOf P := hS ▸ hs
    exact Subgroup.mem_subgroupOf.mp this
  have hse' : (t : G) * s * (t : G)⁻¹ = d := by
    have := congrArg Subtype.val hse
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [← hse', show (t : G)⁻¹ * ((t : G) * s * (t : G)⁻¹) * t = s by group]
  exact hsE

theorem card_le_three_of_le {A L E M K F : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) (hFL : F ≤ L)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) {X : Subgroup G}
    (hXM : X ≤ M) (hXC : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hX : CFSG.Assembly.IsElemAbelian 3 X) : Nat.card X ≤ 3 := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hLM : L ≤ M := hLK.trans (le_of_mem_oTwoComponentsIn hK)
  have hOQ : CFSG.Open.pCoreOf 2 K ≤ Q := Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK
  have hX3 : IsPGroup 3 X := fun x => ⟨1, Subtype.ext (by simpa using hX.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hX3.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨X₀', hX₀'⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 3 (n := 2)
    (by rw [hn]; exact pow_dvd_pow 3 hn2)
  set X₀ := X₀'.map X.subtype with hX₀
  have hX₀X : X₀ ≤ X := Subgroup.map_subtype_le _
  have hX₀9 : Nat.card X₀ = 9 := by
    rw [hX₀, Subgroup.card_map_of_injective X.subtype_injective, hX₀']
    norm_num
  have h4 := four_le_localRank_of_pair hQ hQ2 hMQ (CFSG.LieType.BorelTits.pCoreOf_le 2 M) hQ2
    hMQ hF hF9 (hFL.trans hLM) (isElemAbelian_of_le hX hX₀X) hX₀9 (hX₀X.trans hXM)
    (fun a ha b hb => by
      have h1 := hXC b (hX₀X hb) a (hLK (hFL ha))
      have h2 := Q.inv_mem (hOQ h1)
      rwa [show (b * a * b⁻¹ * a⁻¹)⁻¹ = a * b * a⁻¹ * b⁻¹ by group] at h2)
    (fun a ha b hb hab => by
      refine Step1916Proof2.eq_one_of_forall_commutator_mem hZ hLM (hFL ha) (k := 1)
        (by rw [pow_one]; exact hF.2 a ha) fun l hl => ?_
      exact commutator_mem_of_inv_mul_mem hab (hMQ (hLM (hFL ha))) (hMQ (hLM hl))
        (hOQ (hXC b (hX₀X hb) l (hLK hl))))
  rw [hst.toTheoremFourHyp.localRank_three] at h4
  omega

theorem exists_conj_mem_E
    {A L E M K F : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (hKn : M ≤ Subgroup.normalizer (K : Set G))
    (hZK : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) (hFL : F ≤ L)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) {z : G} (hzE : z ∈ E)
    (hzL : z ∈ L) (hz3 : orderOf z = 3)
    (htype : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 2)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.M12))
    {A' D' : Subgroup G} (hA' : A' ∈ partTwoE G) (hA'M : A' ≤ M) (hD'A' : D' ≤ A')
    (hD'9 : Nat.card D' = 9) (hD'K : D' ≤ Subgroup.normalizer (K : Set G))
    (hinj : Function.Injective ((Step199Proof.pCoreAct K).comp (Subgroup.inclusion hD'K)))
    (hinn : ((Step199Proof.pCoreAct K).comp (Subgroup.inclusion hD'K)).range ≤
      (MulAut.conj : K ⧸ CFSG.pCore 2 K →* MulAut _).range) :
    ∃ d ∈ D', d ≠ 1 ∧ ∃ x ∈ M, x * d * x⁻¹ ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hS := hctx.partTwoS_eq
  have hE := Step1916Proof2.isE27_E hctx
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hEM : E ≤ M := le_of_mem_scriptM_gamma hE hctx.mem_scriptM
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  have hcE := Step1916Proof2.mem_E hctx
  have hc3 := Step1916Proof2.orderOf_eq hctx
  set X := K ⧸ CFSG.pCore 2 K with hX
  set O := CFSG.Open.pCoreOf 2 K with hOdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hMO : M ≤ Subgroup.normalizer (O : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hconj := Step1914TriProof.conj_injective_of_center_eq_bot' hZK
  set C : Subgroup G := M ⊓ ((Step199Proof.pCoreAct K).ker.map
    (Subgroup.normalizer (K : Set G)).subtype) with hCdef
  have hmemC : ∀ x : G, x ∈ C ↔ x ∈ M ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O := by
    intro x
    constructor
    · rintro ⟨hxM, ⟨y, hy, rfl⟩⟩
      exact ⟨hxM, (pCoreAct_eq_one_iff y.2).mp hy⟩
    · rintro ⟨hxM, h⟩
      exact ⟨hxM, ⟨⟨x, hKn hxM⟩, (pCoreAct_eq_one_iff (hKn hxM)).mpr h, rfl⟩⟩
  have hCno9 : ∀ Y : Subgroup G, Y ≤ C → CFSG.Assembly.IsElemAbelian 3 Y → Nat.card Y ≤ 3 :=
    fun Y hYC hY => card_le_three_of_le hctx hZ hK hLK hFL hF hF9 (hYC.trans inf_le_left)
      (fun x hx k hk => ((hmemC x).mp (hYC hx)).2 k hk) hY
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := hctx.mem_lA.1
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hcC : c ∈ C := by
    refine (hmemC c).mpr ⟨hEM hcE, fun k hk => ?_⟩
    have hk' : k ∈ ((L ⊔ O : Subgroup G) : Set G) := by rw [← hKL]; exact hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L O
      (hLK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))] at hk'
    obtain ⟨l, hl, o, ho, rfl⟩ := hk'
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)).symm
    have h1 : c * o * c⁻¹ * o⁻¹ ∈ O :=
      O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMO (hEM hcE)) o).mp ho) (O.inv_mem ho)
    have h2 : l * (c * o * c⁻¹ * o⁻¹) * l⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
        (hLK hl)) _).mp h1
    have e : c * (l * o) * c⁻¹ * (l * o)⁻¹ = l * (c * o * c⁻¹ * o⁻¹) * l⁻¹ := by
      calc c * (l * o) * c⁻¹ * (l * o)⁻¹ = (c * l) * o * c⁻¹ * o⁻¹ * l⁻¹ := by group
        _ = (l * c) * o * c⁻¹ * o⁻¹ * l⁻¹ := by rw [hcl]
        _ = l * (c * o * c⁻¹ * o⁻¹) * l⁻¹ := by group
    rw [e]
    exact h2
  have hA'K : A' ≤ Subgroup.normalizer (K : Set G) := hA'M.trans hKn
  have hA'e := isE27_of_mem_partTwoE hA'
  set ρA := (Step199Proof.pCoreAct K).comp (Subgroup.inclusion hA'K) with hρA
  set ρD := (Step199Proof.pCoreAct K).comp (Subgroup.inclusion hD'K) with hρD
  have hρDA : ρD.range ≤ ρA.range := by
    rintro _ ⟨d, rfl⟩
    exact ⟨⟨d, hD'A' d.2⟩, rfl⟩
  have hρAab : CFSG.Assembly.IsElemAbelian 3 ρA.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, rfl⟩⟩ := y
      apply Subtype.ext
      change ρA a * ρA b = ρA b * ρA a
      rw [← map_mul, ← map_mul]
      congr 1
      exact hA'e.1.1.is_comm.comm a b
    · rintro _ ⟨a, rfl⟩
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hA'e.1.2 a a.2)
      rw [← map_pow, this, map_one]
  have hρDcard : Nat.card ρD.range = 9 := by
    rw [← hD'9]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hAinn : ρA.range ≤ (MulAut.conj : X →* MulAut X).range := by
    rcases htype with hL34 | hM12
    · obtain ⟨ψ⟩ := hL34
      have hle := card_le_nine_of_L34 ψ hρAab
      have heq : ρD.range = ρA.range :=
        Subgroup.eq_of_le_of_card_ge hρDA (by rw [hρDcard]; exact hle)
      rw [← heq]
      exact hinn
    · obtain ⟨-, -, hinnM, -⟩ := KFacts.ks18M12 _ hM12
      rintro _ ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := hinnM (ρA a) ⟨1, by rw [pow_one]; exact hρAab.2 _ ⟨a, rfl⟩⟩
      exact ⟨x, hx.symm⟩
  set U := ρD.range.comap (MulAut.conj : X →* MulAut X) with hU
  have hU9 : Nat.card U = 9 := by
    rw [← hρDcard, ← Subgroup.map_comap_eq_self hinn, Subgroup.card_map_of_injective hconj]
  have hU3 : IsPGroup 3 U := IsPGroup.of_card (n := 2) (by rw [hU9]; norm_num)
  have hsyl : ∀ (m : ℕ) (r : ℕ), Nat.card X = 3 ^ m * r → ¬ 3 ∣ r →
      ∀ Q : Sylow 3 X, Nat.card Q = 3 ^ m := fun m r h hr Q => by
    rw [Sylow.card_eq_multiplicity, CFSG.RankThree.Asc83Table.factorization_eq_of_eq
      Nat.prime_three h hr]
  obtain ⟨kb, xb, hxbU, hxb1, e, heE, hke⟩ : ∃ kb : X, ∃ xb ∈ U, xb ≠ 1 ∧
      ∃ e : K, (e : G) ∈ E ∧ kb * xb * kb⁻¹ = (e : X) := by
    rcases htype with hL34 | hM12
    ·
      obtain ⟨ψ⟩ := hL34
      have hXcard : Nat.card X = 20160 := by
        rw [Nat.card_congr (ψ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 2))).toEquiv,
          KFacts.L34.card_projectiveSL KFacts.L34.card_galoisField_two_two]
      set zb : X := ((⟨z, hLK hzL⟩ : K) : X) with hzb
      have hzb1 : zb ≠ 1 := Step1910Proof.mk_ne_one_of_orderOf (J := K) (c := ⟨z, hLK hzL⟩) hz3
      have hzb3 : zb ^ 3 = 1 := by
        rw [hzb, ← QuotientGroup.mk_pow]
        have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
        have : (⟨z, hLK hzL⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hz3')
        rw [this, QuotientGroup.mk_one]
      have hV3 : IsPGroup 3 (Subgroup.zpowers zb) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hzb3 hzb1, pow_one])
      have hV1 : Subgroup.zpowers zb ≠ ⊥ := by
        rw [Ne, Subgroup.zpowers_eq_bot]
        exact hzb1
      obtain ⟨kb, xb, hxbU, hxb1, hkx⟩ := exists_conj_mem_of_sylow hU3 hU9 hV3 hV1
        (Or.inl fun Q => by
          rw [hsyl 2 2240 (by rw [hXcard]; norm_num) (by norm_num) Q]; norm_num)
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hkx
      refine ⟨kb, xb, hxbU, hxb1, ⟨z, hLK hzL⟩ ^ i, ?_, ?_⟩
      · rw [Subgroup.coe_zpow]
        exact E.zpow_mem hzE i
      · rw [← hi, hzb, QuotientGroup.mk_zpow]
    ·
      have hXcard : Nat.card X = 95040 := by
        obtain ⟨φ⟩ := hM12
        rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
      obtain ⟨-, -, hinnM, -⟩ := KFacts.ks18M12 _ hM12
      have hEK : E ≤ Subgroup.normalizer (K : Set G) := hEM.trans hKn
      set ρE := (Step199Proof.pCoreAct K).comp (Subgroup.inclusion hEK) with hρE
      have hρEab : ∀ φ ∈ ρE.range, φ ^ 3 = 1 := by
        rintro _ ⟨a, rfl⟩
        have : a ^ 3 = 1 := Subtype.ext (by simpa using hE.1.2 a a.2)
        rw [← map_pow, this, map_one]
      have hEinn : ρE.range ≤ (MulAut.conj : X →* MulAut X).range := by
        rintro _ ⟨a, rfl⟩
        obtain ⟨x, hx⟩ := hinnM (ρE a) ⟨1, by rw [pow_one]; exact hρEab _ ⟨a, rfl⟩⟩
        exact ⟨x, hx.symm⟩
      have hker : Nat.card ρE.ker ≤ 3 := by
        have hle : ρE.ker.map E.subtype ≤ C := by
          rintro _ ⟨a, ha, rfl⟩
          refine (hmemC _).mpr ⟨hEM a.2, ?_⟩
          exact (pCoreAct_eq_one_iff (hEK a.2)).mp ha
        have h := hCno9 _ hle (isElemAbelian_of_le hE.1 (Subgroup.map_subtype_le _))
        rwa [Subgroup.card_map_of_injective E.subtype_injective] at h
      have hcardE : Nat.card ρE.range * Nat.card ρE.ker = 27 := by
        rw [← Subgroup.index_ker, mul_comm, Subgroup.card_mul_index, hE.2]
      have hρE9 : 9 ≤ Nat.card ρE.range := by
        have hpos : 0 < Nat.card ρE.ker := Nat.card_pos
        nlinarith
      set V := ρE.range.comap (MulAut.conj : X →* MulAut X) with hV
      have hVcard : Nat.card V = Nat.card ρE.range := by
        rw [← Subgroup.map_comap_eq_self hEinn, Subgroup.card_map_of_injective hconj]
      have hV3 : IsPGroup 3 V := by
        intro v
        have hv : MulAut.conj (v : X) ∈ ρE.range := v.2
        have h3 : (v : X) ^ 3 = 1 := hconj (by rw [map_pow, hρEab _ hv, map_one])
        exact ⟨1, Subtype.ext (by simpa using h3)⟩
      have hV1 : V ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hVcard
        omega
      obtain ⟨kb, xb, hxbU, hxb1, hkx⟩ := exists_conj_mem_of_sylow hU3 hU9 hV3 hV1
        (Or.inr ⟨fun Q => by rw [hsyl 3 3520 (by rw [hXcard]; norm_num) (by norm_num) Q]; norm_num,
          by rw [hVcard]; exact hρE9⟩)
      obtain ⟨e, heE, hex⟩ := exists_mem_of_conj_mem_range hst hS hEE hEK hZK hkx
      exact ⟨kb, xb, hxbU, hxb1, e, heE, hex.symm⟩
  obtain ⟨d, hd⟩ := hxbU
  have hd1 : (d : G) ≠ 1 := by
    intro h
    have hd' : d = 1 := Subtype.ext h
    rw [hd', map_one] at hd
    exact hxb1 (hconj (hd.symm.trans (map_one _).symm))
  obtain ⟨u, huA, hux⟩ := exists_mem_of_conj_mem_range hst hS hA' hA'K hZK (x := xb)
    (hρDA ⟨d, hd⟩)
  set w : G := (d : G) * (u : G)⁻¹ with hw
  have hwA : w ∈ A' := A'.mul_mem (hD'A' d.2) (A'.inv_mem huA)
  have hwC : w ∈ C := by
    refine (hmemC w).mpr ⟨hA'M hwA, (pCoreAct_eq_one_iff (hA'K hwA)).mp ?_⟩
    have hsplit : (⟨w, hA'K hwA⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨d, hD'K d.2⟩ * (⟨(u : G), Subgroup.le_normalizer u.2⟩)⁻¹ := rfl
    rw [hsplit, map_mul, map_inv, pCoreAct_of_mem u.2]
    have h1 : Step199Proof.pCoreAct K ⟨d, hD'K d.2⟩ = MulAut.conj xb := hd
    rw [h1]
    have h2 : ((⟨(u : G), u.2⟩ : K) : X) = xb := by
      rw [← hux]
    rw [h2, mul_inv_cancel]
  have hdwu : (d : G) = w * u := by rw [hw]; group
  obtain ⟨y, hyC, hyw⟩ : ∃ y ∈ C, y * w * y⁻¹ ∈ E := by
    by_cases hw1 : w = 1
    · exact ⟨1, C.one_mem, by rw [hw1, mul_one, one_mul, inv_one]; exact E.one_mem⟩
    · have hw3 : orderOf w = 3 := orderOf_eq_prime (hA'e.1.2 w hwA) hw1
      obtain ⟨y, hyC, hy⟩ := exists_conj_mem_zpowers hCno9 hwC hcC hw3 hc3
      exact ⟨y, hyC, Subgroup.zpowers_le.mpr hcE hy⟩
  have hyM : y ∈ M := hyC.1
  have hyK := ((hmemC y).mp hyC).2
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
  have hkue : (e : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) ∈ O := by
    have h1 : ((k * u * k⁻¹ : K) : X) = (e : X) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hke, ← hux]
    have h2 : e⁻¹ * (k * u * k⁻¹) ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp h1.symm
    rw [Step1911EndProof.mem_pCore_iff] at h2
    simpa using h2
  have hEO : E ≤ Subgroup.normalizer (O : Set G) := hEM.trans hMO
  have hyO : ∀ o ∈ O, y * o * y⁻¹ ∈ O := fun o ho =>
    (Subgroup.mem_normalizer_iff.mp (hMO hyM) o).mp ho
  have hkw : (k : G) * w * (k : G)⁻¹ * w⁻¹ ∈ O := by
    have h1 := ((hmemC w).mp hwC).2 k k.2
    have h2 := O.inv_mem h1
    rwa [show (w * k * w⁻¹ * (k : G)⁻¹)⁻¹ = (k : G) * w * (k : G)⁻¹ * w⁻¹ by group] at h2
  have hye : y * e * y⁻¹ * (e : G)⁻¹ ∈ O := hyK e e.2
  have hmem : (y * k) * (d : G) * (y * k)⁻¹ ∈ E ⊔ O := by
    have e1 : (y * k) * (d : G) * (y * k)⁻¹ =
        (y * ((k : G) * w * (k : G)⁻¹ * w⁻¹) * y⁻¹) * (y * w * y⁻¹) *
          ((y * e * y⁻¹ * (e : G)⁻¹) * e *
            (y * ((e : G)⁻¹ * ((k : G) * u * (k : G)⁻¹)) * y⁻¹)) := by
      rw [hdwu]
      group
    rw [e1]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (hyO _ hkw))
      (Subgroup.mem_sup_left hyw)) (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_right hye) (Subgroup.mem_sup_left heE))
        (Subgroup.mem_sup_right (hyO _ hkue)))
  have hd3 : ((y * k) * (d : G) * (y * k)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hA'e.1.2 _ (hD'A' d.2), mul_one, mul_inv_cancel]
  obtain ⟨t, ht, hte⟩ := exists_conj_mem_of_mem_sup hE hO2 hEO hmem hd3
  have htM : t ∈ M := sup_le hEM (CFSG.LieType.BorelTits.pCoreOf_le 2 K |>.trans hKM) ht
  refine ⟨d, d.2, hd1, t⁻¹ * (y * k), M.mul_mem (M.inv_mem htM) (M.mul_mem hyM (hKM k.2)), ?_⟩
  rw [show t⁻¹ * (y * k) * (d : G) * (t⁻¹ * (y * k))⁻¹ =
    t⁻¹ * ((y * k) * (d : G) * (y * k)⁻¹) * t by group]
  exact hte

end Step1918Proof

end CFSG.RankThree.PartTwo.Sec19

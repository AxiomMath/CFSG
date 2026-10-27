module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.AGLEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_odd_mem_of_twoResidual {J K : Subgroup G}
    (hJ : ∀ (X : Subgroup J) [X.Normal], IsPGroup 2 (J ⧸ X) → X = ⊤)
    (h : ∀ x ∈ J, Odd (orderOf x) → x ∈ K) : J ≤ K := by
  intro j hj
  have hle : Subgroup.closure {x : J | Odd (orderOf x)} ≤ K.comap J.subtype :=
    (Subgroup.closure_le _).mpr fun x hx => h x x.2 (by rwa [Subgroup.orderOf_coe])
  rw [closure_odd_eq_top_of_twoResidual hJ] at hle
  exact hle (Subgroup.mem_top ⟨j, hj⟩)

omit [Finite G] in
private theorem mul_mem_of_isSubnormal_of_odd {A B J N : Subgroup G}
    (h : CFSG.Open.IsSubnormal A B) (hN : IsPGroup 2 N) {j n : G} (hj : j ∈ J) (hn : n ∈ N)
    (hodd : Odd (orderOf (j * n))) : J ≤ A → j * n ∈ B → j * n ∈ A := by
  induction h with
  | refl => exact fun _ hx => hx
  | @step X M B hXM hXM' _ ih =>
    intro hJX hxB
    have hxM : j * n ∈ M := ih (hJX.trans hXM) hxB
    have hjM : j ∈ M := hXM (hJX hj)
    have hnM : n ∈ M := by simpa using M.mul_mem (M.inv_mem hjM) hxM
    obtain ⟨k, hk⟩ := hN ⟨n, hn⟩
    have hn2 : n ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hj1 : QuotientGroup.mk' (X.subgroupOf M) ⟨j, hjM⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨j, hjM⟩ : M)).mpr (Subgroup.mem_subgroupOf.mpr (hJX hj))
    have hφ : QuotientGroup.mk' (X.subgroupOf M) ⟨j * n, hxM⟩ =
        QuotientGroup.mk' (X.subgroupOf M) ⟨n, hnM⟩ := by
      rw [show (⟨j * n, hxM⟩ : M) = ⟨j, hjM⟩ * ⟨n, hnM⟩ from rfl, map_mul, hj1, one_mul]
    have h1 : orderOf (QuotientGroup.mk' (X.subgroupOf M) ⟨j * n, hxM⟩) = 1 := by
      refine Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))
        ((orderOf_map_dvd _ _).trans (Subgroup.orderOf_mk _ hxM).dvd) ?_
      rw [hφ]
      refine (orderOf_map_dvd _ _).trans ?_
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hn2
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (⟨j * n, hxM⟩ : M)).mp (orderOf_eq_one_iff.mp h1))

theorem le_normalizer_of_isSubnormal_of_twoResidual {J K N : Subgroup G}
    (hJK : CFSG.Open.IsSubnormal J K)
    (hJ : ∀ (X : Subgroup J) [X.Normal], IsPGroup 2 (J ⧸ X) → X = ⊤)
    (hN : IsPGroup 2 N) (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ Subgroup.normalizer (J : Set G) := by
  have hconj : ∀ n ∈ N, ∀ y ∈ J, n * y * n⁻¹ ∈ J := by
    intro n hn
    have hle : J ≤ J.comap (MulAut.conj n).toMonoidHom := by
      refine le_of_forall_odd_mem_of_twoResidual hJ fun y hy hyo => ?_
      have hyK : y ∈ K := hJK.le hy
      have hnK : n ∈ K := hNK hn
      have hn' : y⁻¹ * n * y * n⁻¹ ∈ N := by
        have h := Subgroup.le_normalizer_iff.mp hKN y⁻¹ (K.inv_mem hyK) n hn
        rw [inv_inv] at h
        exact N.mul_mem h (N.inv_mem hn)
      have e : n * y * n⁻¹ = y * (y⁻¹ * n * y * n⁻¹) := by group
      have ho : orderOf (n * y * n⁻¹) = orderOf y := by
        have h := (MulAut.conj n).orderOf_eq y
        rwa [MulAut.conj_apply] at h
      have hxK : n * y * n⁻¹ ∈ K := K.mul_mem (K.mul_mem hnK hyK) (K.inv_mem hnK)
      show n * y * n⁻¹ ∈ J
      rw [e] at ho hxK ⊢
      exact mul_mem_of_isSubnormal_of_odd hJK hN hy hn' (by rw [ho]; exact hyo) le_rfl hxK
    exact fun y hy => hle hy
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj n hn y, fun h => ?_⟩
  have h' := hconj n⁻¹ (N.inv_mem hn) _ h
  rwa [show n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y by group] at h'

theorem generalizedFitting_eq_pCore_of_isSubnormal_of_charTwo {H J : Subgroup G}
    (hH : H ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 H : Set G) ≤ CFSG.Open.pCoreOf 2 H)
    (hJH : CFSG.Open.IsSubnormal J H) : generalizedFitting J = CFSG.pCore 2 J := by
  have hJ : J ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 J : Set G) ≤ CFSG.Open.pCoreOf 2 J :=
    CFSG.QuasithinUnique.CharTwo.of_isSubnormal hH hJH.le
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hJH.le).mp hJH)
  refine (isCharacteristicP_iff_generalizedFitting_eq_pCore J 2).mp fun x hx => ?_
  have hxG : (x : G) ∈ J ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 J : Set G) := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx y' hy')
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hJ hxG)
  rw [← Subtype.ext hzx]
  exact hz

theorem exists_commutator_mem_of_isPGroup {Q U Z : Subgroup G} (hQ : IsPGroup 2 Q)
    (hUQ : U ≤ Q) (hQU : Q ≤ Subgroup.normalizer (U : Set G))
    (hZQ : Z ≤ Subgroup.centralizer (Q : Set G)) (hUZ : ¬ U ≤ Z) :
    ∃ u ∈ U, u ∉ Z ∧ ∀ q ∈ Q, ⁅u, q⁆ ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZn : (Z.subgroupOf Q).Normal := ⟨fun z hz q => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Subgroup.mem_centralizer_iff.mp (hZQ hz) q q.2, mul_inv_cancel_right]
    exact hz⟩
  have hnil : Group.IsNilpotent (Q ⧸ Z.subgroupOf Q) := (hQ.to_quotient _).isNilpotent
  have hUn : (U.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUQ).mpr hQU
  have hUbar : ((U.subgroupOf Q).map (QuotientGroup.mk' (Z.subgroupOf Q))).Normal :=
    hUn.map _ (QuotientGroup.mk'_surjective _)
  have hne : (U.subgroupOf Q).map (QuotientGroup.mk' (Z.subgroupOf Q)) ≠ ⊥ := by
    intro hbot
    apply hUZ
    intro u hu
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Z.subgroupOf Q))
      (Subgroup.mem_subgroupOf.mpr hu : (⟨u, hUQ hu⟩ : Q) ∈ U.subgroupOf Q)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨u, hUQ hu⟩ : Q)).mp h1)
  obtain ⟨⟨c, hcU, hcZ⟩, hc1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hcU
  refine ⟨u, Subgroup.mem_subgroupOf.mp hu, fun huZ => hc1 (Subtype.ext ?_), fun q hq => ?_⟩
  · exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr huZ)
  · have h := Subgroup.mem_center_iff.mp hcZ (QuotientGroup.mk' (Z.subgroupOf Q) ⟨q, hq⟩)
    have h2 : QuotientGroup.mk' (Z.subgroupOf Q) ⁅u, ⟨q, hq⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h.symm
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⁅u, (⟨q, hq⟩ : Q)⁆).mp h2)

theorem blockU_le_center_of_isFooteBlock {H J : Subgroup G} (hJ : IsFooteBlock H J)
    (hU : ∀ x ∈ blockU J, ∀ y ∈ blockU J, x * y = y * x) :
    blockU J ≤ blockQ J ⊓ Subgroup.centralizer (blockQ J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (blockQ J) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J
  have hJQ : J ≤ Subgroup.normalizer (blockQ J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  have hQJ : blockQ J ≤ J := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 J
  have hUQ : blockU J ≤ blockQ J := Subgroup.le_normalizer_iff_commutator_le_left.mp hJQ
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) :=
    Subgroup.normalizer_commutator_ge_right (blockQ J) J
  have hUJ : blockU J ≤ J := blockU_le_self J
  have hZU : blockZ J ≤ blockU J := blockZ_le_blockU J
  have hZJ : blockZ J ≤ Subgroup.centralizer (J : Set G) := inf_le_right
  have hZQ : blockZ J ≤ Subgroup.centralizer (blockQ J : Set G) :=
    hZJ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQJ))
  have hZc : ∀ z ∈ blockZ J, ∀ g ∈ J, g * z * g⁻¹ = z := fun z hz g hg => by
    rw [Subgroup.mem_centralizer_iff.mp (hZJ hz) g hg, mul_inv_cancel_right]
  have hQc : ∀ g ∈ J, ∀ q ∈ blockQ J, g⁻¹ * q * g ∈ blockQ J := fun g hg q hq => by
    simpa using Subgroup.le_normalizer_iff.mp hJQ g⁻¹ (J.inv_mem hg) q hq
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G,
      ∀ g, g ∈ W ↔ g ∈ blockU J ∧ ∀ q ∈ blockQ J, ⁅g, q⁆ ∈ blockZ J :=
    ⟨{ carrier := {g | g ∈ blockU J ∧ ∀ q ∈ blockQ J, ⁅g, q⁆ ∈ blockZ J}
       mul_mem' := fun {a b} ha hb => ⟨(blockU J).mul_mem ha.1 hb.1, fun q hq => by
         rw [show ⁅a * b, q⁆ = a * ⁅b, q⁆ * a⁻¹ * ⁅a, q⁆ by
           simp only [commutatorElement_def]; group, hZc _ (hb.2 q hq) a (hUJ ha.1)]
         exact (blockZ J).mul_mem (hb.2 q hq) (ha.2 q hq)⟩
       one_mem' := ⟨(blockU J).one_mem, fun q _ => by
         rw [commutatorElement_one_left]
         exact (blockZ J).one_mem⟩
       inv_mem' := fun {a} ha => ⟨(blockU J).inv_mem ha.1, fun q hq => by
         have h := hZc _ ((blockZ J).inv_mem (ha.2 q hq)) a⁻¹ (J.inv_mem (hUJ ha.1))
         rw [inv_inv] at h
         rw [show ⁅a⁻¹, q⁆ = a⁻¹ * ⁅a, q⁆⁻¹ * a by
           simp only [commutatorElement_def]; group, h]
         exact (blockZ J).inv_mem (ha.2 q hq)⟩ },
     fun _ => Iff.rfl⟩
  have hZW : blockZ J ≤ W := fun z hz => (hW z).mpr ⟨hZU hz, fun q hq => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (hZQ hz) q hq).symm]
    exact (blockZ J).one_mem⟩
  have hWU : W ≤ blockU J := fun w hw => ((hW w).mp hw).1
  have hJW : J ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg w hw
    obtain ⟨hwU, hwQ⟩ := (hW w).mp hw
    refine (hW _).mpr ⟨Subgroup.le_normalizer_iff.mp hJU g hg w hwU, fun q hq => ?_⟩
    rw [show ⁅g * w * g⁻¹, q⁆ = g * ⁅w, g⁻¹ * q * g⁆ * g⁻¹ by
      simp only [commutatorElement_def]; group, hZc _ (hwQ _ (hQc g hg q hq)) g hg]
    exact hwQ _ (hQc g hg q hq)
  have hUQZ : ∀ u ∈ blockU J, ∀ q ∈ blockQ J, ⁅u, q⁆ ∈ blockZ J := by
    rcases hJ.chief.2 W hZW hWU hJW with hWZ | hWU'
    · exfalso
      obtain ⟨u, hu, huZ, huQ⟩ := exists_commutator_mem_of_isPGroup hQp hUQ (hQJ.trans hJU) hZQ
        hJ.chief.1.not_ge
      apply huZ
      rw [← hWZ]
      exact (hW u).mpr ⟨hu, huQ⟩
    · intro u hu
      exact ((hW u).mp (by rw [hWU']; exact hu)).2
  have hUQle : ⁅blockU J, blockQ J⁆ ≤ blockZ J := Subgroup.commutator_le.mpr hUQZ
  have hUU : ⁅blockU J, blockU J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hU y hy x hx
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQp
  have hodd : ∀ x ∈ J, Odd (orderOf x) →
      ⁅blockQ J, Subgroup.zpowers x⁆ ≤ blockU J ⊓ Subgroup.centralizer (blockQ J : Set G) ∧
      ⁅⁅blockQ J, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⁅blockQ J, Subgroup.zpowers x⁆ := by
    intro x hx hxo
    have hXJ : Subgroup.zpowers x ≤ J := Subgroup.zpowers_le.mpr hx
    have hQXU : ⁅blockQ J, Subgroup.zpowers x⁆ ≤ blockU J := Subgroup.commutator_mono le_rfl hXJ
    have h3 : ⁅⁅blockU J, Subgroup.zpowers x⁆, blockQ J⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · refine le_bot_iff.mp ((Subgroup.commutator_mono ?_ le_rfl).trans hUU.le)
        rw [Subgroup.commutator_comm]
        exact hQXU
      · refine le_bot_iff.mp ((Subgroup.commutator_mono ?_ le_rfl).trans
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            (hZJ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXJ)))).le)
        rw [Subgroup.commutator_comm]
        exact hUQle
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card (blockQ J)) := by
      rw [Nat.card_zpowers, hm]
      exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hxo)
    have hc := commutator_commutator_eq_of_coprime (hXJ.trans hJQ) hcop
    refine ⟨le_inf hQXU ?_, hc⟩
    rw [← hc]
    exact (Subgroup.commutator_mono hQXU le_rfl).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
  have hCZ : blockZ J ≤ blockU J ⊓ Subgroup.centralizer (blockQ J : Set G) := le_inf hZU hZQ
  have hJC : J ≤ Subgroup.normalizer
      ((blockU J ⊓ Subgroup.centralizer (blockQ J : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg c hc
    refine ⟨Subgroup.le_normalizer_iff.mp hJU g hg c hc.1,
      Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp hc.2 _ (hQc g hg q hq)
    calc q * (g * c * g⁻¹) = g * ((g⁻¹ * q * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * q * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * q := by group
  rcases hJ.chief.2 _ hCZ inf_le_left hJC with hC | hC
  · exfalso
    have hJQc : J ≤ Subgroup.centralizer (blockQ J : Set G) := by
      refine le_of_forall_odd_mem_of_twoResidual hJ.residual fun x hx hxo => ?_
      obtain ⟨h1, h2⟩ := hodd x hx hxo
      have hbot : ⁅blockQ J, Subgroup.zpowers x⁆ = ⊥ := by
        rw [← h2]
        refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (h1.trans ?_)
        rw [hC]
        exact hZJ.trans (Subgroup.centralizer_le
          (SetLike.coe_subset_coe.mpr (Subgroup.zpowers_le.mpr hx)))
      have hQx := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (Subgroup.mem_centralizer_iff.mp (hQx hq) x (Subgroup.mem_zpowers x)).symm
    have hUbot : blockU J = ⊥ := by
      show ⁅blockQ J, J⁆ = ⊥
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJQc
    have hlt := hJ.chief.1
    rw [hUbot] at hlt
    exact not_lt_bot hlt
  · exact le_inf hUQ (hC.symm.le.trans inf_le_right)

theorem isShort_of_isFooteBlock {H J : Subgroup G} (hJ : IsFooteBlock H J)
    (hH : H ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 H : Set G) ≤ CFSG.Open.pCoreOf 2 H)
    (hU : ∀ x ∈ blockU J, ∀ y ∈ blockU J, x * y = y * x) : IsShort J where
  eq_twoResidual := hJ.residual
  generalizedFitting_eq := generalizedFitting_eq_pCore_of_isSubnormal_of_charTwo hH hJ.subnormal
  blockU_le_center := blockU_le_center_of_isFooteBlock hJ hU
  quasisimple_or_prime := Or.inl ⟨⟨hJ.quasisimple.1⟩, hJ.quasisimple.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
      hJ.quasisimple⟩
  blockZ_lt_blockU := hJ.chief.1
  irreducible := hJ.chief.2

theorem le_centralizer_of_isFooteBlock {H J V : Subgroup G} (hJ : IsFooteBlock H J)
    (hU : ¬ ∀ x ∈ blockU J, ∀ y ∈ blockU J, x * y = y * x)
    (hV : CFSG.Open.IsElemAbelian 2 V) (hVH : V ≤ H)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) : V ≤ Subgroup.centralizer (J : Set G) := by
  have hVp : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by simpa using hV.2 v v.2)⟩
  have hJV : J ≤ Subgroup.normalizer (V : Set G) := hJ.le.trans hHV
  have hVJ : V ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_isSubnormal_of_twoResidual hJ.subnormal hJ.residual hVp hVH hHV
  have hJQ : J ≤ Subgroup.normalizer (blockQ J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) :=
    Subgroup.normalizer_commutator_ge_right (blockQ J) J
  have hUJ : blockU J ≤ J := blockU_le_self J
  have hWV : ⁅V, J⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hJV
  have hWJ : ⁅V, J⁆ ≤ J := Subgroup.le_normalizer_iff_commutator_le_right.mp hVJ
  have hJW : J ≤ Subgroup.normalizer ((⁅V, J⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right V J
  have hWQ : ⁅V, J⁆ ≤ blockQ J :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer hWJ hJW (hVp.to_le hWV)
  have hA0 : ⁅⁅V, J⁆, J⁆ = ⁅V, J⁆ := commutator_commutator_eq_of_twoResidual hJ.residual hVp hJV
  have hWU : ⁅V, J⁆ ≤ blockU J := by
    rw [← hA0]
    exact Subgroup.commutator_mono hWQ le_rfl
  have hWc : ∀ g ∈ J, ∀ w ∈ ⁅V, J⁆, g * w * g⁻¹ ∈ ⁅V, J⁆ := Subgroup.le_normalizer_iff.mp hJW
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, ∀ g, g ∈ Y ↔ g ∈ blockU J ∧ ∀ j ∈ J, ⁅g, j⁆ ∈ ⁅V, J⁆ :=
    ⟨{ carrier := {g | g ∈ blockU J ∧ ∀ j ∈ J, ⁅g, j⁆ ∈ ⁅V, J⁆}
       mul_mem' := fun {a b} ha hb => ⟨(blockU J).mul_mem ha.1 hb.1, fun j hj => by
         rw [show ⁅a * b, j⁆ = a * ⁅b, j⁆ * a⁻¹ * ⁅a, j⁆ by
           simp only [commutatorElement_def]; group]
         exact Subgroup.mul_mem _ (hWc a (hUJ ha.1) _ (hb.2 j hj)) (ha.2 j hj)⟩
       one_mem' := ⟨(blockU J).one_mem, fun j _ => by
         rw [commutatorElement_one_left]
         exact Subgroup.one_mem _⟩
       inv_mem' := fun {a} ha => ⟨(blockU J).inv_mem ha.1, fun j hj => by
         rw [show ⁅a⁻¹, j⁆ = a⁻¹ * ⁅a, j⁆⁻¹ * a⁻¹⁻¹ by
           simp only [commutatorElement_def]; group]
         exact hWc _ (J.inv_mem (hUJ ha.1)) _ (Subgroup.inv_mem _ (ha.2 j hj))⟩ },
     fun _ => Iff.rfl⟩
  have hZY : blockZ J ≤ Y := fun z hz => (hY z).mpr ⟨hz.1, fun j hj => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 j hj).symm]
    exact Subgroup.one_mem _⟩
  have hYU : Y ≤ blockU J := fun y hy => ((hY y).mp hy).1
  have hJY : J ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg u hu
    obtain ⟨huU, huJ⟩ := (hY u).mp hu
    refine (hY _).mpr ⟨Subgroup.le_normalizer_iff.mp hJU g hg u huU, fun j hj => ?_⟩
    have hj' : g⁻¹ * j * g ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hg) hj) hg
    rw [show ⁅g * u * g⁻¹, j⁆ = g * ⁅u, g⁻¹ * j * g⁆ * g⁻¹ by
      simp only [commutatorElement_def]; group]
    exact hWc g hg _ (huJ _ hj')
  rcases hJ.chief.2 Y hZY hYU hJY with hYZ | hYU'
  ·
    have hWZ : ⁅V, J⁆ ≤ blockZ J := by
      rw [← hYZ]
      intro w hw
      exact (hY w).mpr ⟨hWU hw, fun j hj => Subgroup.le_normalizer_iff_commutator_le_left.mp hJW
        (Subgroup.commutator_mem_commutator hw hj)⟩
    have hbot : ⁅V, J⁆ = ⊥ := by
      rw [← hA0]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hWZ.trans inf_le_right)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  ·
    exfalso
    apply hU
    have hQp : IsPGroup 2 (blockQ J) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J
    have hUJU : ⁅blockU J, J⁆ = blockU J :=
      commutator_commutator_eq_of_twoResidual hJ.residual hQp hJQ
    have hUW : blockU J ≤ ⁅V, J⁆ := by
      rw [← hUJU, Subgroup.commutator_le]
      intro u hu j hj
      exact ((hY u).mp (by rw [hYU']; exact hu)).2 j hj
    intro x hx y hy
    have hVc := Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
    exact Subgroup.mem_centralizer_iff.mp (hVc (hWV (hUW hy))) x (hWV (hUW hx))

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNY
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNLie
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNQuasi
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS1
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H13.L828N
open scoped IsMulCommutative commutatorElement

@[expose] def E4_828 : Prop :=
  ∀ (Q X : Type) [Group Q] [Finite Q] [Group X], CFSG.IsQuasisimple Q →
    3 ∣ Nat.card (Subgroup.center Q) → Nonempty (Q ⧸ Subgroup.center Q ≃* X) → E22Simple X →
    ∀ S : Sylow 3 X, ¬ IsCyclic (S : Subgroup X)

private theorem isQuasisimple_of_open_828N {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hne
  push Not at hne
  have hperf : commutator (Q ⧸ Subgroup.center Q) = ⊤ := by
    rw [commutator_def]
    have h1 : (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆).map (QuotientGroup.mk' (Subgroup.center Q)) =
        ⁅(⊤ : Subgroup (Q ⧸ Subgroup.center Q)), (⊤ : Subgroup (Q ⧸ Subgroup.center Q))⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [← h1, ← commutator_def, h.1]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hbot : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hne a b)
  have := hperf.symm.trans hbot
  obtain ⟨a, b, hab⟩ := h.2.exists_pair_ne
  have ha : a ∈ (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) := Subgroup.mem_top a
  have hb : b ∈ (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) := Subgroup.mem_top b
  rw [this, Subgroup.mem_bot] at ha hb
  exact hab (ha.trans hb.symm)

section N5

variable {G : Type} [Group G] [Finite G]

theorem s828N_Y (hE22 : E2.E22StatementC) (hE4 : E4_828)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hyp : Hyp7_0_2 G T L I) (c : S828Ctx T L I H h k)
    (hmin : MinParabolic H T (H ⊓ fsuM T L)) (hSQ : SQTKGroup ↥H) (hns : ¬ Group.IsSolvable ↥H)
    (hHIT : H = ch82I (fsuV T I) h ⊔ T)
    {K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))
    (hNK : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hcc : ⁅K, Subgroup.centralizer (ch82U (fsuV T I) h : Set G)⁆ ≤ pCoreOf 2 K)
    (hnc : ∀ S : Sylow 3 ↥K, ¬ IsCyclic (S : Subgroup ↥K))
    (h9 : ¬ 9 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (ch82U (fsuV T I) h : Set G))) :
    ∃ Y : Subgroup G, Y ∈ cComp H ∧ H = Y ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) ∧
      Y ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) ∧
      SzCasesE22 H T (H ⊓ fsuM T L) Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Y, hYc, hHY, hYq, hcases, -⟩ := e22_inst_cocode_829 hE22 hmin hSQ hns
  have hYH : Y ≤ H := le_of_mem_cComp hYc
  have hYperf : ⁅Y, Y⁆ = Y := hYc.2.1
  obtain ⟨-, -, -, -, -, -, -, hTU, -, -, hUZ, -, hIU⟩ := c.hC5
  set U := ch82U (fsuV T I) h with hUdef
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hOC : oTwoUpper H ≤ Subgroup.centralizer (U : Set G) :=
    oTwoUpper_le_centralizer_U_829 hT2 hHIT hIU hTU
  have hYC : Y ≤ Subgroup.centralizer (U : Set G) :=
    (s828N_perfect_le_oTwoUpper hYH hYperf).trans hOC
  have hU2 : IsPGroup 2 ↥U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hV.2 _ x.2.1)⟩
  have hU1 : U ≠ ⊥ := by
    have h1 : ch82ZI (fsuV T I) h ≠ ⊥ := c.hC.2.2.2.1
    rwa [← c.hUZ] at h1
  have hH2 : pCoreOf 2 (Subgroup.normalizer (U : Set G)) ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff, ← hbot]
    exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hU2
  have hrank : CFSG.Open.pRank 3 (Subgroup.normalizer (U : Set G)) ≤ 2 :=
    CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke hH2 Nat.prime_three (by norm_num)
  have hcyc : ∀ S : Sylow 3 ↥Y, IsCyclic (S : Subgroup ↥Y) :=
    s828N_sylow3_cyclic hrank hKN hNK hcc hnc hYC h9
  obtain ⟨π, hπ⟩ : ∃ π : ↥Y →* ↥(E2.star (H ⊓ fsuM T L) H Y), Function.Surjective π := by
    refine ⟨((QuotientGroup.mk' ((kerIn (H ⊓ fsuM T L) H).subgroupOf H)).subgroupMap
      (Y.subgroupOf H)).comp (Subgroup.subgroupOfEquivOfLe hYH).symm.toMonoidHom, ?_⟩
    exact (MonoidHom.subgroupMap_surjective _ _).comp
      (Subgroup.subgroupOfEquivOfLe hYH).symm.surjective
  have h3Y : ¬ 3 ∣ Nat.card ↥Y := by
    intro h3
    obtain ⟨e, he3⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have he3' : (e : G) ^ 3 = 1 := by
      have := pow_orderOf_eq_one e
      rw [he3] at this
      have h2 := congrArg Subtype.val this
      simpa using h2
    have heK : (e : G) ∈ K := s828N_three_mem hrank hKN hNK hcc hnc hYC (e : G) e.2 he3'
    have hHU : H ≤ Subgroup.normalizer (U : Set G) := by
      rw [hHIT]
      exact sup_le (hIU.trans (Subgroup.centralizer_le_normalizer _)) hTU
    have hZs : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer (U : Set G)) :=
      s828N_solvable_of_comm_le inf_le_left
        ((Subgroup.commutator_mono le_rfl inf_le_right).trans hcc)
    haveI hZ'n : ((K ⊓ Subgroup.centralizer (U : Set G)).subgroupOf Y).Normal := by
      constructor
      intro z hz y
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      have hyU : (y : G) ∈ Subgroup.normalizer (U : Set G) := hHU (hYH y.2)
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hNK hyU) (z : G)).mp hz.1
        simpa using this
      · have hNC : Subgroup.normalizer (U : Set G) ≤
            Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
          B6.le_normalizer_centralizer le_rfl
        have := (Subgroup.mem_normalizer_iff.mp (hNC hyU) (z : G)).mp hz.2
        simpa using this
    haveI hZ's : Group.IsSolvable ↥((K ⊓ Subgroup.centralizer (U : Set G)).subgroupOf Y) := by
      let fZ : ↥((K ⊓ Subgroup.centralizer (U : Set G)).subgroupOf Y) →*
          ↥(K ⊓ Subgroup.centralizer (U : Set G)) :=
        ⟨⟨fun z => ⟨((z : ↥Y) : G), Subgroup.mem_subgroupOf.mp z.2⟩, rfl⟩, fun a b => rfl⟩
      refine Group.isSolvable_of_isSolvable_injective (f := fZ) ?_
      intro a b hab
      have h2 := congrArg (fun z : ↥(K ⊓ Subgroup.centralizer (U : Set G)) => (z : G)) hab
      exact Subtype.ext (Subtype.ext h2)
    have heZ' : e ∈ (K ⊓ Subgroup.centralizer (U : Set G)).subgroupOf Y :=
      Subgroup.mem_subgroupOf.mpr ⟨heK, hYC e.2⟩
    have hYq' : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := isQuasisimple_of_open_828N hYq
    have h3c := three_dvd_center_of_solvable_normal hYq' _ heZ' he3
    obtain ⟨hsimp, hnonab⟩ := e22Simple_simple (e22Simple_of_cases hcases)
    obtain ⟨eQ⟩ := quasisimple_quot_equiv π hπ hsimp hnonab hYq'
    have hnc3 := hE4 (↥Y ⧸ CFSG.pCore 2 ↥Y) _ hYq' h3c ⟨eQ⟩ (e22Simple_of_cases hcases)
    exact hnc3 (default : Sylow 3 ↥(E2.star (H ⊓ fsuM T L) H Y))
      (sylow_cyclic_quotient π hπ hcyc _)
  have h3star : ¬ 3 ∣ Nat.card ↥(E2.star (H ⊓ fsuM T L) H Y) := fun h3 =>
    h3Y (h3.trans (Subgroup.card_dvd_of_surjective hπ))
  exact ⟨Y, hYc, hHY, hYq, hYC, e22Cases_Sz hcases h3star⟩

end N5

end CFSG.Quasithin.H13

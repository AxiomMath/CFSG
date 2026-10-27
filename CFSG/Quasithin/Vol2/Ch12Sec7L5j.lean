module

public import CFSG.Quasithin.H13.NQBlockLayerProduct
public import CFSG.Fischer.Classification.Recognition.SpUBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec7L5a

public section

namespace CFSG.Quasithin.H13.S127.L5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem pCore_eq_center {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : IsPGroup 2 ↥(Subgroup.center Q)) : CFSG.pCore 2 Q = Subgroup.center Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, hZ⟩)
  have hn : (CFSG.pCore 2 Q).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hn with htop | hle
  · exfalso
    have h2 : IsPGroup 2 Q := by
      have h := CFSG.pCore_isPGroup (p := 2) (G := Q)
      rw [htop] at h
      exact h.of_equiv Subgroup.topEquiv
    have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    have : Group.IsNilpotent Q := h2.isNilpotent
    have : Group.IsPerfect Q := hQ.1
    exact Group.IsPerfect.not_isSolvable Q inferInstance
  · exact hle

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isComponentOf {H K : Subgroup G} (hH : CFSG.Open.pRank 3 H ≤ 2)
    (hK : IsComponentOf K H) (hZ : IsPGroup 2 ↥(Subgroup.center ↥K))
    (h3 : 2 ≤ CFSG.pRank 3 (↥K ⧸ Subgroup.center ↥K)) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  have eK : ↥K ≃* ↥K' := (Subgroup.subgroupOfEquivOfLe hK.1).symm
  have hKq : CFSG.IsQuasisimple ↥K :=
    CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple hK.2.2
  have hK'q : CFSG.IsQuasisimple ↥K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq
  have hK'c : CFSG.IsComponent K' :=
    ⟨hK'q, CFSG.Fischer.Classification.Recognition.SpU.isSubnormal_subgroupOf hK.2.1⟩
  have hcK : (Subgroup.center ↥K).map eK.toMonoidHom = Subgroup.center ↥K' :=
    Subgroup.map_center_eq eK
  have hZ' : IsPGroup 2 ↥(Subgroup.center ↥K') := by
    rw [← hcK]
    exact hZ.map _
  have hpc : CFSG.pCore 2 ↥K' = Subgroup.center ↥K' := pCore_eq_center hK'q hZ'
  let e1 : (↥K' ⧸ CFSG.pCore 2 ↥K') ≃* (↥K' ⧸ Subgroup.center ↥K') :=
    QuotientGroup.quotientMulEquivOfEq hpc
  let e2 : (↥K ⧸ Subgroup.center ↥K) ≃* (↥K' ⧸ Subgroup.center ↥K') :=
    QuotientGroup.congr _ _ eK hcK
  have hr1 : 2 ≤ CFSG.pRank 3 (↥K' ⧸ CFSG.pCore 2 ↥K') := by
    rw [NQBlock.pRank_mulEquiv e1 3, ← NQBlock.pRank_mulEquiv e2 3]
    exact h3
  have hcop : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥K') := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥K'))
    rw [ha]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hr2 : 2 ≤ CFSG.pRank 3 ↥K' := by
    rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three
      (CFSG.pCore 2 ↥K') hcop]
    exact hr1
  have hsimple : IsSimpleGroup (↥K' ⧸ CFSG.pCore 2 ↥K') := by
    have := hK'q.2.1
    exact e1.isSimpleGroup
  have hnab : ∃ a b : ↥K' ⧸ CFSG.pCore 2 ↥K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK'q.2.2
    refine ⟨e1.symm a, e1.symm b, fun h => hab ?_⟩
    have := congrArg e1 h
    simpa using this
  intro g hg
  set c : MulAut ↥H := MulAut.conj (⟨g, hg⟩ : ↥H) with hc
  set K'' : Subgroup ↥H := K'.map c.toMonoidHom with hK''
  have hK''c : CFSG.IsComponent K'' := CFSG.LocalCores.isComponent_map_mulEquiv c hK'c
  rcases CFSG.LocalCores.distinct_components_commute hK'c hK''c with heq | hcomm
  ·
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have h1 : c ⟨k, hK.1 hk⟩ ∈ K'' := ⟨⟨k, hK.1 hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [← heq] at h1
    simpa [hc] using Subgroup.mem_subgroupOf.mp h1
  ·
    exfalso
    have hc1 : K' ≤ Subgroup.centralizer (K'' : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hc2 : K'' ≤ Subgroup.centralizer (K' : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact hcomm)
    have hN1 : K' ≤ Subgroup.normalizer (K'' : Set ↥H) := fun a ha =>
      Subgroup.mem_normalizer_fintype fun x hx => by
        rw [← Subgroup.mem_centralizer_iff.mp (hc1 ha) x hx, mul_inv_cancel_right]
        exact hx
    have hN2 : K'' ≤ Subgroup.normalizer (K' : Set ↥H) := fun a ha =>
      Subgroup.mem_normalizer_fintype fun x hx => by
        rw [← Subgroup.mem_centralizer_iff.mp (hc2 ha) x hx, mul_inv_cancel_right]
        exact hx
    have hsum := NQBlock.commuting_product_pRank hN1 hN2 (by rw [hcomm]; exact bot_le) hsimple
      hnab Nat.prime_three (by norm_num)
    have hr3 : 2 ≤ CFSG.pRank 3 ↥K'' := by
      rw [hK'', NQBlock.pRank_map_mulEquiv c K' 3]
      exact hr2
    have hle : CFSG.pRank 3 ↥(K' ⊔ K'') ≤ 2 := by
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
      refine (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans ?_
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
        CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
      exact hH
    omega

namespace D127

variable {T L V : Subgroup G} {t : G} (d : D127 G T L V t)
include d

theorem pRank_le_two (ht2 : t ^ 2 = 1) :
    CFSG.Open.pRank 3 (Subgroup.centralizer ({t} : Set G)) ≤ 2 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three (by norm_num)
    _ (CFSG.QuasithinUnique.Lin2.isTwoLocal_centralizer_of_sq_eq_one ht2 d.ne_one)).trans
    d.hyp.hyp.qtke.2.2

theorem conjClosure_eq {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({t} : Set G)))
    (hN : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : Lt L t ≤ K) :
    conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G)) = K := by
  set Kt := conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G)) with hKt
  have hle : Kt ≤ K := conjClosure_le fun h hh z hz =>
    (Subgroup.mem_normalizer_iff.mp (hN hh) z).mp (hLK hz)
  refine le_antisymm hle ?_
  have hKq : CFSG.IsQuasisimple ↥K :=
    CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple hK.2.2
  have hnorm : (Kt.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro x k hx hk
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ (hK.1 hk)) x).mp hx
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hnorm with htop | hcen
  · intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ Kt.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  ·
    exfalso
    have hLc : Lt L t ≤ Subgroup.centralizer (V : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hlz : (⟨l, hLK hl⟩ : ↥K) ∈ Subgroup.center ↥K :=
        hcen (Subgroup.mem_subgroupOf.mpr (le_conjClosure _ _ hl))
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hlz ⟨v, hLK (d.v_le_lt hv)⟩)
    have hb : ⁅V, Lt L t⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLc
    have h1 : Nat.card ↥V = 1 := by
      rw [d.comm_eq, hb]
      simp
    rw [d.card_V] at h1
    norm_num at h1

end D127

end CFSG.Quasithin.H13.S127.L5

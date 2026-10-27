module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem515
public import CFSG.Quasithin.Vol2.Ch1Ten
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_14_one : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      quasithinIsMaximalLocal T (oTwoUpper H) ∧ ¬ quasithinIsFaithfulLocal T (oTwoUpper H)

@[expose] def Stmt5_1_14_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → Concl5_1_14_four T L V B D n

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quasithinOmegaOneCenter_le_inf (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

omit [Finite G] in
theorem quasithinOmegaOneCenter_le_self (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T :=
  (quasithinOmegaOneCenter_le_inf T).trans inf_le_left

omit [Finite G] in
theorem mem_centralizer_singleton_of {x z : G} (h : z * x = x * z) :
    x ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun w hw => by
    rw [Set.mem_singleton_iff.mp hw]
    exact h

omit [Finite G] in
theorem comm_of_mem_centralizer_singleton {x z : G}
    (h : x ∈ Subgroup.centralizer ({z} : Set G)) : z * x = x * z :=
  Subgroup.mem_centralizer_iff.mp h z (Set.mem_singleton z)

theorem centralizer_le_of_isUniqueM {H Mp P : Subgroup G} (hU : IsUniqueM H Mp) (hP : IsPGroup 2 P)
    {z : G} (hzP : z ∈ P) (hz : z ≠ 1) (hH : H ≤ Subgroup.centralizer ({z} : Set G)) :
    Subgroup.centralizer ({z} : Set G) ≤ Mp := by
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) := hP.to_le (Subgroup.zpowers_le.mpr hzP)
  have hZ1 : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    apply hz
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hCN : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro c hc
    have hzc : Commute z c := comm_of_mem_centralizer_singleton hc
    have hc' : c ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left hzc k).eq
    exact Subgroup.centralizer_le_normalizer _ hc'
  have hloc : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :=
    ⟨Subgroup.zpowers z, hZ1, hZ2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq : M' = Mp := hU.2 M' ⟨hM', hH.trans (hCN.trans hle)⟩
  exact hM'eq ▸ hCN.trans hle

end General

theorem stmt5_1_14_first_of (h331 : Stmt3_3_1) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1 : Stmt5_1_14_one) : Stmt5_1_14_first := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨hmax, hnf⟩ := h1 G T M L V H B D n hyp hN hV hK
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
  have hHeq : H = oTwoUpper H ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hTH
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hH.1.1.trans (le_normalizer_oTwoUpper H)
  have hcc : conjClosure (oTwoUpper H) T = oTwoUpper H := by
    apply le_antisymm _ (le_conjClosure _ T)
    exact conjClosure_le fun t ht z hz =>
      (Subgroup.mem_normalizer_iff.mp (hTK ht) z).mp hz
  have hU : IsUniqueM H (Subgroup.normalizer (oTwoUpper H : Set G)) := by
    have := lemma_1_2_7_three h.qtke h.simple h.nonabelian h37 h38 h39 h.sylow hmax
    rwa [hcc, ← hHeq] at this
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.sylow
  have hInH : InH (oTwoUpper H ⊔ T) H := ⟨hHeq.symm.le, hH.1.2⟩
  have htfae := lemma_1_2_10_of_maximal h.qtke h.simple h.nonabelian h36 h37 h39 h.sylow hmax hInH
  have hno : ¬ ∃ W, IsTwoReducedIn H W ∧ ⁅W, oTwoUpper H⁆ ≠ ⊥ := fun hW =>
    hnf ((htfae.out 1 2).mpr hW)
  have hcharH : CharTwo H := charTwo_of_inH' h.qtke h.sylow hH.1
  have hVZ : IsTwoReducedIn H (conjClosure (quasithinOmegaOneCenter T) H) := by
    have := isTwoReducedIn_conjClosure H S (hS ▸ hH.1.1) hcharH (Z := quasithinOmegaOneCenter T)
      (by rw [hS])
    exact this
  have hKZ : ⁅conjClosure (quasithinOmegaOneCenter T) H, oTwoUpper H⁆ = ⊥ := by
    by_contra hne
    exact hno ⟨_, hVZ, hne⟩
  have hZT : quasithinOmegaOneCenter T ≤ T := quasithinOmegaOneCenter_le_self T
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) := by
    rw [hHeq]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hKC : oTwoUpper H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKZ
      rw [Subgroup.le_centralizer_iff] at this
      exact this.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ H)))
    have hTC : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwc := quasithinOmegaOneCenter_le_inf T hw
      exact (Subgroup.mem_centralizer_iff.mp hwc.2 t ht).symm
    have hx' : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      sup_le hKC hTC hx
    exact (Subgroup.mem_centralizer_iff.mp hx' z hz).symm
  have hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZC
  have hcent : ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    intro z hz hz1
    refine centralizer_le_of_isUniqueM hU h.sylow.1 (hZT hz) hz1 ?_
    intro x hx
    exact mem_centralizer_singleton_of (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm
  refine ⟨⟨hmax, hU, hnf⟩, ⟨hZH, hcent⟩, ?_⟩
  rw [eq_bot_iff]
  intro z hz
  by_contra hz1
  rw [Subgroup.mem_bot] at hz1
  obtain ⟨hzZ, hzL⟩ := hz
  have hLTz : L ⊔ T ≤ Subgroup.centralizer ({z} : Set G) := by
    apply sup_le
    · intro l hl
      exact mem_centralizer_singleton_of (Subgroup.mem_centralizer_iff.mp hzL l hl).symm
    · intro t ht
      have hzc := quasithinOmegaOneCenter_le_inf T hzZ
      exact mem_centralizer_singleton_of (Subgroup.mem_centralizer_iff.mp hzc.2 t ht).symm
  have hLTK : L ⊔ T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hLTz.trans (hcent z hzZ hz1)
  have hMeq : Subgroup.normalizer (oTwoUpper H : Set G) = M :=
    (h.isUniqueM h331).2 _ ⟨hU.1.1, hLTK⟩
  exact hH.2.1 (hMeq ▸ hU.1.2)

theorem stmt5_1_14_of (hfirst : Stmt5_1_14_first) (h4 : Stmt5_1_14_four) (h5116 : Stmt5_1_16) :
    Stmt5_1_14 := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  obtain ⟨h1, h2, h3⟩ := hfirst G T M L V H B D n hyp hN hV hK
  have hc4 := h4 G T M L V H B D n hyp hN hV hK
  obtain ⟨h3', hsolv⟩ := h5116 G T M L V H B D n hyp hN hV hK
  have hDK : D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [hc4.2.2]
    exact (hN.1.1.trans inf_le_right).trans (le_normalizer_oTwoUpper H)
  refine ⟨h1, h2, h3, hc4, ?_, h3'⟩
  by_contra hns
  exact (hsolv hns).2.2 hDK

end CFSG.Quasithin.H13

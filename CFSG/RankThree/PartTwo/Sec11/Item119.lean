module

public import CFSG.RankThree.PartTwo.Sec11.Item112
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartOne.EmbeddingFixedResidual

section Subgroups

variable {G : Type*} [Group G]

theorem isElemAbelian_map_subtype {p : ℕ} {H : Subgroup G} {E : Subgroup H}
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.map H.subtype) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem partTwoE_eq_partTwoF_subgroup (hEF : partTwoE G = partTwoF G) (H : Subgroup G) :
    partTwoE H = partTwoF H := by
  have hmapE : ∀ E : Subgroup H, E ∈ partTwoE H → E.map H.subtype ∈ partTwoE G := by
    rintro E ⟨hab, hcard, U, hU, hU2, hEU⟩
    refine ⟨isElemAbelian_map_subtype hab,
      by rw [Subgroup.card_map_of_injective H.subtype_injective, hcard], U.map H.subtype,
      fun h => hU ((Subgroup.map_eq_bot_iff_of_injective U H.subtype_injective).mp h),
      hU2.map _, ?_⟩
    exact (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)
  ext E
  constructor
  · intro hE
    have hG := hmapE E hE
    rw [hEF] at hG
    obtain ⟨-, hmax, -⟩ := hG
    refine ⟨hE.1, fun B hB hEB => ?_, E, hE, le_rfl⟩
    exact Subgroup.map_injective H.subtype_injective
      (hmax (B.map H.subtype) (isElemAbelian_map_subtype hB) (Subgroup.map_mono hEB))
  · rintro ⟨hab, -, E₀, hE₀, hE₀E⟩
    have hG := hmapE E₀ hE₀
    rw [hEF] at hG
    obtain ⟨-, hmax, -⟩ := hG
    have h1 := hmax (E.map H.subtype) (isElemAbelian_map_subtype hab) (Subgroup.map_mono hE₀E)
    rw [Subgroup.map_injective H.subtype_injective h1]
    exact hE₀

end Subgroups

theorem isoLThreeMinusPi_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X' ≃* X) {p n : ℕ}
    [Fact p.Prime] (h : Sec8.IsoLThreeMinusPi X p n) : Sec8.IsoLThreeMinusPi X' p n := by
  rcases h with ⟨h1, ⟨f⟩⟩ | ⟨h1, ⟨f⟩⟩
  · exact Or.inl ⟨h1, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨h1, ⟨e.trans f⟩⟩

@[expose] def IsType424 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (X ≃* projSL 2 (GaloisField 2 n))) ∨
    (∃ (p n : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ n ∧
      Nonempty (X ≃* projSL 2 (GaloisField p n))) ∨
    ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 n

theorem isType424_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X' ≃* X)
    (h : IsType424 X) : IsType424 X' := by
  rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨p, n, hp, h3, hn, ⟨f⟩⟩ | ⟨n, hn, h⟩
  · exact Or.inl ⟨n, hn, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨p, n, hp, h3, hn, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, isoLThreeMinusPi_of_mulEquiv e h⟩)

@[expose] def KType119 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      A = Subgroup.closure {c, a, d} →
        IsType424 (sec11K L a ⧸ aschbacherSolvableCore 3 (sec11K L a))

section Core

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_theta_map_subtype_sub {H : Subgroup G} (K : Subgroup H) :
    inSubgroup (aschbacherSolvableCore 3) (K.map H.subtype) =
      (inSubgroup (aschbacherSolvableCore 3) K).map H.subtype := by
  set e := K.equivMapOfInjective H.subtype H.subtype_injective
  have h := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  rw [inSubgroup, inSubgroup, ← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem Sec11Std.not_mem_facts {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d}) :
    c ∉ Subgroup.zpowers a ∧ a ∉ Subgroup.closure ({c, d} : Set G) ∧ d ≠ 1 := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have hdA : d ∈ A := by
    have hd : d ∈ A ⊓ L := by
      rw [hdL]
      exact Subgroup.mem_zpowers d
    exact hd.1
  constructor
  · intro hca
    have hle : A ≤ Subgroup.closure ({a, d} : Set G) := by
      rw [hA, Subgroup.closure_le]
      have ha : a ∈ Subgroup.closure ({a, d} : Set G) := Subgroup.subset_closure (by simp)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact Subgroup.zpowers_le.mpr ha hca
      · exact ha
      · exact Subgroup.subset_closure (by simp)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm a haA d hdA) (hexp a haA) (hexp d hdA)
    rw [h.card_eq] at h1
    omega
  refine ⟨fun hacd => ?_, fun hd1 => ?_⟩
  · have hle : A ≤ Subgroup.closure ({c, d} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact hacd
      · exact Subgroup.subset_closure (by simp)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA d hdA) (hexp c hcA) (hexp d hdA)
    rw [h.card_eq] at h1
    omega
  · rw [hd1] at hA
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.one_mem _
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a haA) (hexp c hcA) (hexp a haA)
    rw [h.card_eq] at h1
    omega

theorem mem_thetaComponentsIn_sec11K (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d})
    (hcC : c ∈ Subgroup.centralizer ({a} : Set G)) :
    (sec11K L a).subgroupOf (Subgroup.centralizer ({a} : Set G)) ∈
      thetaComponentsIn (Y.subgroupOf (Subgroup.centralizer ({a} : Set G)) ⊓
        Subgroup.centralizer
          ({(⟨c, hcC⟩ : Subgroup.centralizer ({a} : Set G))} : Set _)) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set c' : C := ⟨c, hcC⟩ with hc'
  set K := sec11K L a with hK
  have hacd := (h.not_mem_facts hdL hA).2.1
  obtain ⟨haN, ha3, hZ, hQ, -⟩ := basic_facts_of_conj h45 h hdL hA h.a_mem hacd
  obtain ⟨hYC, -⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt_Y
  obtain ⟨hLc, hL'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt
  have hKC : K ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
  have hKY : K ≤ Y := h.sec11K_le
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := (sec11K_le L a).trans hLc
  set Z := Y.subgroupOf C ⊓ Subgroup.centralizer ({c'} : Set C) with hZdef
  have hKZ : K.subgroupOf C ≤ Z := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr (hKY hk), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKc hk)
  set T := (K.subgroupOf C).subgroupOf Z with hT
  set e : T ≃* K := (Subgroup.subgroupOfEquivOfLe hKZ).trans (Subgroup.subgroupOfEquivOfLe hKC)
    with he
  refine mem_thetaComponentsIn_iff.mpr ⟨hKZ, ?_, ?_, ?_⟩
  · have hKp : Group.IsPerfect K := Sec6.isPerfect_inSubgroup_perfectResidual _
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · set ι : Z →* Subgroup.centralizer ({c} : Set G) :=
      (C.subtype.comp Z.subtype).codRestrict _ (fun z => by
        have hz := Subgroup.mem_centralizer_singleton_iff.mp z.2.2
        exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hz)) with hι
    set MD := (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).comap ι with hMD
    have hMDsn : MD.IsSubnormal := hL'.2.1.comap ι
    have hTMD : T ≤ MD := by
      intro t ht
      rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ht
      rw [hMD, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact sec11K_le L a ht
    have hTn : (T.subgroupOf MD).Normal := by
      constructor
      intro t ht m
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ht ⊢
      have hmL : (((m : Z) : C) : G) ∈ L := m.2
      have hmM : (((m : Z) : C) : G) ∈ L ⊓ Subgroup.centralizer ({a} : Set G) :=
        ⟨hmL, ((m : Z) : C).2⟩
      have := GroupTheory.conj_mem_inSubgroup_perfectResidual hmM ht
      simpa [hK, sec11K] using this
    exact Subgroup.IsSubnormal.trans hTMD hTn.isSubnormal hMDsn
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three e)).symm (isQuasisimple_sec11K_quotient haN ha3 hQ hZ)

end Core

end CFSG.RankThree.PartTwo.Sec11

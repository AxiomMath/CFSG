module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourWeak
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaPrimePullback
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K63ThreeHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.OUpperTwoSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {L : Subgroup G}

private abbrev DeltaShape (e : ℕ) : Type :=
  alternatingGroup (Fin 5) × alternatingGroup (Fin 5) × Multiplicative (ZMod (5 ^ e))

private theorem center_deltaShape (e : ℕ) :
    Subgroup.center (DeltaShape e) = (⊥ : Subgroup (alternatingGroup (Fin 5))).prod
      ((⊥ : Subgroup (alternatingGroup (Fin 5))).prod
        (⊤ : Subgroup (Multiplicative (ZMod (5 ^ e))))) := by
  rw [Subgroup.center_prod, Subgroup.center_prod,
    alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5)),
    Subgroup.center_eq_top]

private noncomputable def centerDeltaShapeEquiv (e : ℕ) :
    ↥(Subgroup.center (DeltaShape e)) ≃* Multiplicative (ZMod (5 ^ e)) where
  toFun x := x.1.2.2
  invFun c := ⟨(1, 1, c), by
    rw [Subgroup.mem_center_iff]
    intro y
    ext <;> simp [mul_comm]⟩
  left_inv x := by
    apply Subtype.ext
    have hx : (x : DeltaShape e) ∈ (⊥ : Subgroup (alternatingGroup (Fin 5))).prod
        ((⊥ : Subgroup (alternatingGroup (Fin 5))).prod
          (⊤ : Subgroup (Multiplicative (ZMod (5 ^ e))))) := by
      rw [← center_deltaShape]
      exact x.2
    simp only [Subgroup.mem_prod, Subgroup.mem_bot] at hx
    ext <;> simp [hx.1, hx.2.1]
  right_inv c := rfl
  map_mul' x y := rfl

@[expose] noncomputable def deltaCyclicQ (D : Data G) : Subgroup (Bar2 D.M) :=
  CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))

private theorem deltaQ_normal (D : Data G) : (deltaCyclicQ D).Normal :=
  CFSG.LocalAnalysis.RankThreeUC.S15.K63ThreeProof.pElementSubgroup_top_normal 5

private noncomputable def centerDeltaQEquiv {D : Data G} {e : ℕ}
    (φ : ↥(deltaCyclicQ D) ≃* DeltaShape e) :
    ↥(Subgroup.center ↥(deltaCyclicQ D)) ≃* Multiplicative (ZMod (5 ^ e)) :=
  (Subgroup.equivMapOfInjective (Subgroup.center ↥(deltaCyclicQ D)) φ.toMonoidHom
    φ.injective).trans
    ((MulEquiv.subgroupCongr (Subgroup.map_center_eq φ)).trans (centerDeltaShapeEquiv e))

private theorem pRank_center_deltaQ {D : Data G} {e : ℕ} (he : 1 ≤ e)
    (φ : ↥(deltaCyclicQ D) ≃* DeltaShape e) :
    CFSG.Open.pRank 5 (Subgroup.center ↥(deltaCyclicQ D)) = 1 := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
      (centerDeltaQEquiv φ)]
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_multiplicative_zmod he

private theorem isPGroup_center_deltaQ {D : Data G} {e : ℕ}
    (φ : ↥(deltaCyclicQ D) ≃* DeltaShape e) :
    IsPGroup 5 (Subgroup.center ↥(deltaCyclicQ D)) :=
  IsPGroup.of_equiv
    (IsPGroup.of_pow (ZModModule.isPGroup_multiplicative (n := 5 ^ e) (G := ZMod (5 ^ e))))
    (centerDeltaQEquiv φ).symm

noncomputable def deltaOmega (D : Data G) : Subgroup ↥(deltaCyclicQ D) :=
  CFSG.RankThree.PartOne.omegaOne 5 (Subgroup.center ↥(deltaCyclicQ D))

noncomputable def deltaCyclicR (D : Data G) : Subgroup (Bar2 D.M) :=
  (deltaOmega D).map (deltaCyclicQ D).subtype

private theorem deltaOmega_characteristic (D : Data G) : (deltaOmega D).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr ?_
  intro ψ x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hmap : ∀ z ∈ Subgroup.center ↥(deltaCyclicQ D), z ^ 5 = 1 →
      ψ z ∈ Subgroup.center ↥(deltaCyclicQ D) ∧ (ψ z) ^ 5 = 1 := by
    intro z hz hz5
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff] at hz ⊢
      intro w
      obtain ⟨w', rfl⟩ := ψ.surjective w
      rw [← map_mul, ← map_mul, hz w']
    · rw [← map_pow, hz5, map_one]
  have hsub : ψ.toMonoidHom '' {z : ↥(deltaCyclicQ D) | z ∈ Subgroup.center ↥(deltaCyclicQ D) ∧
      z ^ 5 = 1} ⊆ {z : ↥(deltaCyclicQ D) | z ∈ Subgroup.center ↥(deltaCyclicQ D) ∧ z ^ 5 = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hmap z hz.1 hz.2
  have hmem : ψ.toMonoidHom y ∈ (Subgroup.closure {z : ↥(deltaCyclicQ D) |
      z ∈ Subgroup.center ↥(deltaCyclicQ D) ∧ z ^ 5 = 1}).map ψ.toMonoidHom :=
    Subgroup.mem_map_of_mem _ hy
  rw [MonoidHom.map_closure] at hmem
  exact Subgroup.closure_mono hsub hmem

theorem deltaR_card {D : Data G} {V₀ V L : Subgroup G} (c : A5Data18 D V₀ V L) :
    Nat.card ↥(deltaCyclicR D) = 5 := by
  obtain ⟨e, he, ⟨φ⟩⟩ := c.shape
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcomm : ∀ x ∈ Subgroup.center ↥(deltaCyclicQ D),
      ∀ y ∈ Subgroup.center ↥(deltaCyclicQ D), x * y = y * x :=
    fun x hx y _ => (Subgroup.mem_center_iff.mp hx y).symm
  have homega : deltaOmega D =
      CFSG.Walter.omegaOneOfComm 5 (Subgroup.center ↥(deltaCyclicQ D)) hcomm := by
    unfold deltaOmega
    apply le_antisymm
    · rw [CFSG.RankThree.PartOne.omegaOne]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      exact hx
    · intro x hx
      rw [CFSG.RankThree.PartOne.omegaOne]
      exact Subgroup.subset_closure (CFSG.Walter.mem_omegaOneOfComm.mp hx)
  have hcard : Nat.card ↥(deltaOmega D) = 5 := by
    rw [homega, CFSG.Walter.card_omegaOneOfComm Nat.prime_five _ hcomm
      (isPGroup_center_deltaQ φ), pRank_center_deltaQ he φ]
    norm_num
  rw [deltaCyclicR, Subgroup.card_map_of_injective (deltaCyclicQ D).subtype_injective, hcard]

theorem deltaOmega_le_center (D : Data G) :
    deltaOmega D ≤ Subgroup.center ↥(deltaCyclicQ D) := by
  rw [deltaOmega, CFSG.RankThree.PartOne.omegaOne]
  exact (Subgroup.closure_le _).mpr fun x hx => hx.1

theorem deltaCyclicR_le_centralizer (D : Data G) :
    deltaCyclicR D ≤ Subgroup.centralizer (deltaCyclicQ D : Set (Bar2 D.M)) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [deltaCyclicR] at hz
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
  have hcent : c ∈ Subgroup.center ↥(deltaCyclicQ D) := deltaOmega_le_center D hc
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcent ⟨y, hy⟩)

private theorem deltaR_normal (D : Data G) : (deltaCyclicR D).Normal := by
  have : (deltaCyclicQ D).Normal := deltaQ_normal D
  have : (deltaOmega D).Characteristic := deltaOmega_characteristic D
  exact ConjAct.normal_of_characteristic_of_normal

noncomputable def deltaB (D : Data G) : Subgroup G :=
  ((deltaCyclicR D).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))).map D.M.subtype

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {L : Subgroup G}

private theorem oUpperTwo_subgroupOf_normal {M X : Subgroup G} (hXM : X ≤ M)
    (hXN : (X.subgroupOf M).Normal) :
    ((CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.oUpperTwo X).subgroupOf M).Normal := by
  rw [S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure,
    Subgroup.normal_subgroupOf_iff_le_normalizer
      ((CFSG.GroupTheory.oddOrderClosure_le X).trans hXM)]
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXN).trans
    (CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure X)

private theorem oUpperTwo_sup_normal_of_normal {M X T : Subgroup G}
    (hXM : X ≤ M) (hXN : (X.subgroupOf M).Normal) (hTM : T ≤ M) (hT2 : IsPGroup 2 T) :
    ((CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.oUpperTwo (X ⊔ T)).subgroupOf M).Normal := by
  have hXH : X ≤ X ⊔ T := le_sup_left
  have hXN' : (X.subgroupOf (X ⊔ T)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXH]
    exact (sup_le hXM hTM).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXN)
  rw [S17.oUpperTwo_sup_eq_of_normal hXN' hT2]
  exact oUpperTwo_subgroupOf_normal hXM hXN

theorem deltaB_le_M (D : Data G) : deltaB D ≤ D.M :=
  Subgroup.map_subtype_le _

theorem deltaB_subgroupOf (D : Data G) :
    (deltaB D).subgroupOf D.M =
      (deltaCyclicR D).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
  unfold deltaB
  apply Subgroup.map_injective (f := D.M.subtype) D.M.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)]

private theorem deltaB_normal (D : Data G) : ((deltaB D).subgroupOf D.M).Normal := by
  rw [deltaB_subgroupOf]
  exact (deltaR_normal D).comap _

private theorem pCoreOf_le_deltaB (D : Data G) :
    CFSG.Open.pCoreOf 2 D.M ≤ deltaB D := by
  rw [CFSG.Open.pCoreOf]
  refine Subgroup.map_mono ?_
  intro x hx
  rw [Subgroup.mem_comap]
  have hx1 : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [hx1]
  exact (deltaCyclicR D).one_mem

private theorem pCoreOf_deltaB (D : Data G) :
    CFSG.Open.pCoreOf 2 (deltaB D) = CFSG.Open.pCoreOf 2 D.M := by
  apply le_antisymm
  · have hPle : CFSG.Open.pCoreOf 2 (deltaB D) ≤ deltaB D :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _
    have hBM : D.M ≤ Subgroup.normalizer (deltaB D : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (deltaB_le_M D)).mp (deltaB_normal D)
    have hPnorm : ((CFSG.Open.pCoreOf 2 (deltaB D)).subgroupOf D.M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hPle.trans (deltaB_le_M D))]
      exact hBM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (deltaB D))
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2
      (CFSG.Open.pCoreOf 2 (deltaB D)) D.M (hPle.trans (deltaB_le_M D)) hPnorm
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  · have hPM : CFSG.Open.pCoreOf 2 D.M ≤ deltaB D := pCoreOf_le_deltaB D
    have hMnorm : D.M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 D.M : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 D.M
    have hPMnorm : ((CFSG.Open.pCoreOf 2 D.M).subgroupOf (deltaB D)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPM]
      exact (deltaB_le_M D).trans hMnorm
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2
      (CFSG.Open.pCoreOf 2 D.M) (deltaB D) hPM hPMnorm
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)

private theorem deltaB_card {D : Data G} {V₀ V L : Subgroup G} (c : A5Data18 D V₀ V L) :
    Nat.card ↥(deltaB D) = 5 * Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
  unfold deltaB
  rw [Subgroup.card_map_of_injective D.M.subtype_injective,
    CFSG.ABGLocalTools.card_comap_mk' (CFSG.pCore 2 ↥D.M) (deltaCyclicR D),
    deltaR_card c, Nat.mul_comm]

private theorem deltaB_inf_pCoreOf_sup (D : Data G) :
    deltaB D ⊓ CFSG.Open.pCoreOf 2 (deltaB D ⊔ D.T) = CFSG.Open.pCoreOf 2 D.M := by
  apply le_antisymm
  · have hPle : CFSG.Open.pCoreOf 2 (deltaB D ⊔ D.T) ≤ deltaB D ⊔ D.T :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _
    have hPB : deltaB D ≤ Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 (deltaB D ⊔ D.T) : Set G) :=
      (le_sup_left : deltaB D ≤ deltaB D ⊔ D.T).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
    have hN : deltaB D ≤ Subgroup.normalizer
        (deltaB D ⊓ CFSG.Open.pCoreOf 2 (deltaB D ⊔ D.T) : Set G) := by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨(Subgroup.le_normalizer : deltaB D ≤ _) hx, hPB hx⟩
    have hnormal : ((deltaB D ⊓ CFSG.Open.pCoreOf 2 (deltaB D ⊔ D.T)).subgroupOf
        (deltaB D)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hN
    have hle := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2
      (deltaB D ⊓ CFSG.Open.pCoreOf 2 (deltaB D ⊔ D.T)) (deltaB D) inf_le_left hnormal
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    rwa [pCoreOf_deltaB D] at hle
  · refine le_inf (pCoreOf_le_deltaB D) ?_
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2
      (CFSG.Open.pCoreOf 2 D.M) (deltaB D ⊔ D.T) ?_ ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    · exact (pCoreOf_le_deltaB D).trans le_sup_left
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer
        ((pCoreOf_le_deltaB D).trans le_sup_left)]
      exact (sup_le (deltaB_le_M D) D.sylowM.le).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 D.M)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {L : Subgroup G}

private theorem deltaBR_card {D : Data G} {V₀ V L : Subgroup G} (c : A5Data18 D V₀ V L) :
    Nat.card ↥(UC22.barImage (deltaB D ⊔ D.T) (deltaB D)) = 5 := by
  let H : Subgroup G := deltaB D ⊔ D.T
  have hBM : Nat.card ↥(deltaB D) = 5 * Nat.card ↥(CFSG.pCore 2 ↥D.M) := deltaB_card c
  have hmain := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ((deltaB D).subgroupOf H)
  rw [QuotientGroup.ker_mk'] at hmain
  have hcardK : Nat.card ↥((deltaB D).subgroupOf H) = Nat.card ↥(deltaB D) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : deltaB D ≤ H)).toEquiv
  have hcardMap : ((deltaB D).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) = UC22.barImage H (deltaB D) := rfl
  have hinf : (deltaB D).subgroupOf H ⊓ CFSG.pCore 2 ↥H =
      ((deltaB D ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf H) := by
    apply Subgroup.map_injective (f := H.subtype) H.subtype_injective
    rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective]
    rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_left : deltaB D ≤ H)]
    rw [show (CFSG.pCore 2 ↥H).map H.subtype = CFSG.Open.pCoreOf 2 H from rfl]
    rw [Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left.trans (le_sup_left : deltaB D ≤ H))]
  have hcardKer : Nat.card ↥((deltaB D).subgroupOf H ⊓ CFSG.pCore 2 ↥H) =
      Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
    rw [hinf]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans (le_sup_left : deltaB D ≤ H))).toEquiv,
      deltaB_inf_pCoreOf_sup D,
      show CFSG.Open.pCoreOf 2 D.M = (CFSG.pCore 2 ↥D.M).map D.M.subtype from rfl,
      Subgroup.card_map_of_injective D.M.subtype_injective]
  have h1 : Nat.card ↥(deltaB D) =
      Nat.card ↥(UC22.barImage H (deltaB D)) * Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
    calc Nat.card ↥(deltaB D) = Nat.card ↥((deltaB D).subgroupOf H) := hcardK.symm
      _ = Nat.card ↥(((deltaB D).subgroupOf H).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) *
          Nat.card ↥((deltaB D).subgroupOf H ⊓ CFSG.pCore 2 ↥H) := hmain
      _ = Nat.card ↥(UC22.barImage H (deltaB D)) * Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
          rw [hcardMap, hcardKer]
  have h2 : 5 * Nat.card ↥(CFSG.pCore 2 ↥D.M) =
      Nat.card ↥(UC22.barImage H (deltaB D)) * Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
    rw [← hBM, h1]
  have hpos : 0 < Nat.card ↥(CFSG.pCore 2 ↥D.M) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

private theorem deltaBR_hirr {D : Data G} {V₀ V L : Subgroup G} (c : A5Data18 D V₀ V L) :
    ∀ N : Subgroup (Bar2 (deltaB D ⊔ D.T)), N.Normal →
      N ≤ UC22.barImage (deltaB D ⊔ D.T) (deltaB D) →
      N ≤ (frattini ↥(UC22.barImage (deltaB D ⊔ D.T) (deltaB D))).map
        (UC22.barImage (deltaB D ⊔ D.T) (deltaB D)).subtype ∨
        N = UC22.barImage (deltaB D ⊔ D.T) (deltaB D) := by
  intro N _ hN
  let R : Subgroup (Bar2 (deltaB D ⊔ D.T)) := UC22.barImage (deltaB D ⊔ D.T) (deltaB D)
  have hRcard : Nat.card ↥R = 5 := deltaBR_card c
  have : Fact (Nat.card ↥R).Prime := ⟨by rw [hRcard]; exact Nat.prime_five⟩
  rcases (N.subgroupOf R).eq_bot_or_eq_top_of_prime_card with h | h
  · left
    have hNbot : N = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hN, h, Subgroup.map_bot]
    rw [hNbot]
    exact bot_le
  · right
    rw [← Subgroup.map_subgroupOf_eq_of_le hN, h, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {L : Subgroup G}

private theorem deltaB_sup_inFSq_one {D : Data G} {V₀ V L : Subgroup G}
    (c : A5Data18 D V₀ V L) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (deltaB D ⊔ D.T) := by
  let H : Subgroup G := deltaB D ⊔ D.T
  let R : Subgroup (Bar2 H) := UC22.barImage H (deltaB D)
  have hT2 : IsPGroup 2 D.T :=
    (WeakClosure81.isSylowOf_two_iff_isSylowIn.mp D.sylowM).2.1
  have hBH : ((deltaB D).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : deltaB D ≤ H)]
    exact (sup_le (deltaB_le_M D) D.sylowM.le).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (deltaB_le_M D)).mp (deltaB_normal D))
  have : R.Normal := by
    change (UC22.barImage H (deltaB D)).Normal
    rw [UC22.barImage]
    exact hBH.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      (QuotientGroup.mk'_surjective _)
  have hTsub2 : IsPGroup 2 (D.T.subgroupOf H) :=
    IsPGroup.comap_of_injective hT2 H.subtype H.subtype_injective
  have hS0 : IsPGroup 2 (UC22.barImage H D.T) := hTsub2.map _
  have hRS : R ⊔ UC22.barImage H D.T = ⊤ := by
    change (UC22.barImage H (deltaB D) ⊔ UC22.barImage H D.T) = ⊤
    rw [UC22.barImage, UC22.barImage,
      ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup
        (le_sup_left : deltaB D ≤ H) (le_sup_right : D.T ≤ H),
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _)]
  have hQR : IsPGroup 2 (Bar2 H ⧸ R) :=
    uc22s21rb_isPGroup_quotient hS0 hRS
  have hRq : IsPGroup 5 R := by
    refine IsPGroup.of_card (n := 1) ?_
    change Nat.card ↥(UC22.barImage H (deltaB D)) = 5 ^ 1
    rw [deltaBR_card c, pow_one]
  refine uc22s21rb_inF_one_frattini (q := 5) Nat.prime_five (by norm_num) hRq hQR ?_
    (deltaBR_hirr c)
  exact CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥H) (p := 2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G}

@[expose] def DeltaCalMOf (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Δ : Set (Subgroup G)) : Prop :=
  ∀ K : Subgroup G, D.T ≤ K → K ≤ ⨆ H ∈ Δ, H →
    barSub V₀ V hV K = ⨆ H ∈ Δ, barSub V₀ V hV H → calMOf K = {D.M}

@[expose] def DeltaCalMOfCase (D : Data G) (V₀ V L : Subgroup G) : Prop :=
  ∀ (K : Subgroup G) (hK : A5Pair18 D V₀ V L K),
    (UC22.conjClosure D.M L = L ⊔ K →
      DeltaCalMOf D V₀ V hK.data.hyp.hyp125.isElemAbelian
        {UC22.conjClosure D.M L ⊔ D.T, deltaB D ⊔ D.T}) ∧
    DeltaCalMOf D V₀ V hK.data.hyp.hyp125.isElemAbelian
      {L ⊔ D.T, K ⊔ D.T, deltaB D ⊔ D.T}

theorem gap_18_4_Delta_of
    (c : A5Data18 D V₀ V L) (h61 : UC6.R6_1 D)
    (h43c : W3Lem45_2Chief)
    (hgen : CFSG.SignalizerFunctorTheorem.McBride.orbitClosure
        (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) L)
        (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T) ⊔
      imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T = ⊤)
    (hcf : ∀ T' : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T)),
      CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF (S17.nOf L) ⊤ T')
    (hKc : K_L2SzAutRank) (h1768 : S17.R17_68At D V₀ V)
    (hcal : DeltaCalMOfCase D V₀ V L) :
    Gap_18_4_Delta D V₀ V L c := by
  classical
  intro hV₀
  have hT2 : IsPGroup 2 D.T :=
    (WeakClosure81.isSylowOf_two_iff_isSylowIn.mp D.sylowM).2.1
  have hTM : D.T ≤ D.M := D.sylowM.le
  obtain ⟨K, hK, hKne, hAltK, hK5, hKX, hcalC, hcomm, hdich⟩ := c.exists_second
  have h3sig : 3 ∉ D.sig := c.three_not_mem_sig h1768
  have hpair : A5Pair18 D V₀ V L K :=
    { data := c
      mem_calC := hK
      ne_L := hKne
      alt_K := hAltK
      mem_calLp := hK5
      conjClosure_mem := hKX
      calC_eq := hcalC
      commutator_le := hcomm
      dichotomy := hdich
      three_not_mem_sig := h3sig }
  have hcalK := hcal K hpair
  have hpRank : CFSG.Open.pRank 5 (L ⊔ K) = 2 :=
    pRank_five_sup_eq_two_of_calC c.hyp.hL.1 hK hKne c.alt hAltK hcomm
  obtain ⟨A, hA, hAel, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) (L ⊔ K)
  have hAp : IsPGroup 5 A := CFSG.Open.IsElemAbelian.isPGroup hAel
  have hAc : ¬ IsCyclic A := by
    intro hcyc
    have : IsCyclic ↥A := hcyc
    have : Fintype ↥A := Fintype.ofFinite _
    have hle := IsCyclic.card_pow_eq_one_le (α := ↥A) (n := 5) (by norm_num)
    have hall : Finset.univ.filter (fun x : ↥A => x ^ 5 = 1) = Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Subtype.ext (hAel.2 x x.2)
    rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
    rw [hAcard, hpRank] at hle
    norm_num at hle
  have hL2two : IsL2 (Bar2 L) 2 := by
    obtain ⟨e⟩ := c.alt
    exact CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e
  have hNof : S17.nOf L = 2 := S17.nOf_eq_of_isL2 hL2two
  have hL2 : IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L) := by
    rw [hNof]
    exact Or.inl hL2two
  have hXinFSq : CFSG.LocalAnalysis.WeakClosure81.InFSq (S17.nOf L)
      (UC22.conjClosure D.M L ⊔ D.T) :=
    A5Data18.inFSq_conjClosure_sup c h43c hL2 hgen hcf
  have hBinFSq : CFSG.LocalAnalysis.WeakClosure81.InFSq 2 (deltaB D ⊔ D.T) :=
    TwelveTwentyTwo.inFSq_mono (by norm_num : 1 ≤ 2) (deltaB_sup_inFSq_one c)
  rcases hdich with ⟨hXeq, hx⟩ | ⟨hXeq, hLnorm, hKnorm⟩
  ·
    let X : Subgroup G := UC22.conjClosure D.M L
    let Δ : Set (Subgroup G) := {X ⊔ D.T, deltaB D ⊔ D.T}
    have hXle : X ≤ D.M := c.hyp.X_le_M
    have hXnorm : (X.subgroupOf D.M).Normal := c.conjClosure_normal
    have hΔM : (⨆ H ∈ Δ, H) ≤ D.M := by
      refine iSup₂_le fun H hH => ?_
      simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl
      · exact sup_le hXle hTM
      · exact sup_le (deltaB_le_M D) hTM
    have hMmem : D.M ∈ calMOf (⨆ H ∈ Δ, H) := ⟨D.maxLocal, hΔM⟩
    have hAle : A ≤ ⨆ H ∈ Δ, H :=
      hA.trans ((show L ⊔ K ≤ X ⊔ D.T from by
          rw [← hXeq]; exact le_sup_left)
        |>.trans (le_iSup₂_of_le (X ⊔ D.T) (by simp [Δ]) le_rfl))
    have hΔunique : UniqueMax D.M (⨆ H ∈ Δ, H) :=
      uniqueMax_iSup_of_noncyclic_of_le D h61 c.hyp hΔM hMmem hAle hAp hAc
    refine ⟨0, Δ, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨c.hyp.hyp125, hV₀, c.conjClosure_normal, ?_, ?_, ?_,
        A5Data18.xCond1218_conjClosure_of_data c hV₀ 0⟩
      · intro H hH
        simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
        rcases hH with rfl | rfl
        · exact sup_le hXle hTM
        · exact sup_le (deltaB_le_M D) hTM
      · intro H hH
        simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
        rcases hH with rfl | rfl
        · exact le_sup_right
        · exact le_sup_right
      · exact hΔunique
    · simp [Δ, X]
    · intro H hH
      simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl
      · exact oUpperTwo_sup_normal_of_normal hXle hXnorm hTM hT2
      · exact oUpperTwo_sup_normal_of_normal (deltaB_le_M D) (deltaB_normal D) hTM hT2
    · intro K' hTK' hK'le hbar
      exact (hcalK.1 hXeq) K' hTK' hK'le hbar
    · refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndexMax_le_iff.mpr ?_
      intro H hH
      simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl
      · have h := hXinFSq
        rw [hNof] at h
        exact h
      · exact hBinFSq
  ·
    let Δ : Set (Subgroup G) := {L ⊔ D.T, K ⊔ D.T, deltaB D ⊔ D.T}
    have hLle : L ≤ D.M := s13_le_of_mem_calC c.hyp.hL.1
    have hKle : K ≤ D.M := s13_le_of_mem_calC hK
    have hΔM : (⨆ H ∈ Δ, H) ≤ D.M := by
      refine iSup₂_le fun H hH => ?_
      simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl | rfl
      · exact sup_le hLle hTM
      · exact sup_le hKle hTM
      · exact sup_le (deltaB_le_M D) hTM
    have hMmem : D.M ∈ calMOf (⨆ H ∈ Δ, H) := ⟨D.maxLocal, hΔM⟩
    have hAle : A ≤ ⨆ H ∈ Δ, H := by
      refine hA.trans ?_
      have hLsup : L ⊔ D.T ≤ ⨆ H ∈ Δ, H :=
        le_iSup₂_of_le (L ⊔ D.T) (by simp [Δ]) le_rfl
      have hKsup : K ⊔ D.T ≤ ⨆ H ∈ Δ, H :=
        le_iSup₂_of_le (K ⊔ D.T) (by simp [Δ]) le_rfl
      refine sup_le ?_ ?_
      · exact le_sup_left.trans hLsup
      · exact le_sup_left.trans hKsup
    have hΔunique : UniqueMax D.M (⨆ H ∈ Δ, H) :=
      uniqueMax_iSup_of_noncyclic_of_le D h61 c.hyp hΔM hMmem hAle hAp hAc
    have hLinFSq : CFSG.LocalAnalysis.WeakClosure81.InFSq 2 (L ⊔ D.T) :=
      inFSq_sup_T_of_normal c.hyp.hL.1 hLnorm c.alt hKc
    have hKinFSq : CFSG.LocalAnalysis.WeakClosure81.InFSq 2 (K ⊔ D.T) :=
      inFSq_sup_T_of_normal hK hKnorm hAltK hKc
    refine ⟨0, Δ, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨c.hyp.hyp125, hV₀, c.conjClosure_normal, ?_, ?_, ?_,
        A5Data18.xCond1218_conjClosure_of_data c hV₀ 0⟩
      · intro H hH
        simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
        rcases hH with rfl | rfl | rfl
        · exact sup_le hLle hTM
        · exact sup_le hKle hTM
        · exact sup_le (deltaB_le_M D) hTM
      · intro H hH
        simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
        rcases hH with rfl | rfl | rfl <;> exact le_sup_right
      · exact hΔunique
    · rw [hXeq]
      simp [Δ]
    · intro H hH
      simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl | rfl
      · exact oUpperTwo_sup_normal_of_normal hLle hLnorm hTM hT2
      · exact oUpperTwo_sup_normal_of_normal hKle hKnorm hTM hT2
      · exact oUpperTwo_sup_normal_of_normal (deltaB_le_M D) (deltaB_normal D) hTM hT2
    · intro K' hTK' hK'le hbar
      exact hcalK.2 K' hTK' hK'le hbar
    · refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndexMax_le_iff.mpr ?_
      intro H hH
      simp only [Δ, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl | rfl
      · exact hLinFSq
      · exact hKinFSq
      · exact hBinFSq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

module

public import CFSG.RankThree.PartTwo.Sec21.Item211
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofMono
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Item63
import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint
open scoped commutatorElement

@[expose] def IsBar211 (X : Type) [Group X] : Prop :=
  Sec4.IsTripleCover X NativeSporadic.M22 ∨ Nonempty (X ≃* NativeSporadic.M22) ∨
    Nonempty (X ≃* NativeSporadic.M23) ∨ Nonempty (X ≃* NativeSporadic.HS) ∨
    Nonempty (X ≃* NativeSporadic.M24) ∨ Nonempty (X ≃* NativeSporadic.He) ∨
    Nonempty (X ≃* NativeSporadic.J2) ∨ Nonempty (X ≃* NativeSporadic.Ru) ∨
    Nonempty (X ≃* NativeSporadic.J4) ∨
    (∃ n : ℕ, 0 < n ∧ Even n ∧ (Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (X ≃* SL3 n) ∨ ChevalleyExceptionalModel X .G2 2 n ∨
      ChevalleyExceptionalModel X .trialityD4 2 n ∨
      Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSU 4 2 n))) ∨
    Nonempty (X ≃* projSU 5 2 2) ∨ (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (X ≃* projSU 4 2 n)) ∨
    Nonempty (X ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover X NativeSporadic.J3 ∨
    StatedClassicalModel X .PSL 4 2 1 ∨ StatedClassicalModel X .PSL 5 2 1 ∨
    StatedClassicalModel X .PSp 3 2 1

@[expose] def KS213Order : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsBar211 X → 5616 < Nat.card (X ⧸ Subgroup.center X)

@[expose] def KS213Nine : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsBar211 X →
    ∃ E : Subgroup (X ⧸ Subgroup.center X), Monoid.exponent E ∣ 3 ∧ Nat.card E = 9

@[expose] def KS213TwoRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsBar211 X →
    ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsPGroup 2 (Subgroup.center J) →
      Nonempty (J ⧸ Subgroup.center J ≃* X ⧸ Subgroup.center X) →
      3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup J)

@[expose] def Item213Center : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → CFSG.pCore 2 L = ⊥ →
      3 ∣ Nat.card (Subgroup.center (lBar L)) → CFSG.IsQuasisimple L

namespace Item21EarlyProof

section General

variable {X : Type*} [Group X]

abbrev centerPre (T : Subgroup X) [T.Normal] : Subgroup X :=
  (Subgroup.center (X ⧸ T)).comap (QuotientGroup.mk' T)

instance centerPre_normal (T : Subgroup X) [T.Normal] : (centerPre T).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem le_centerPre (T : Subgroup X) [T.Normal] : T ≤ centerPre T := by
  intro t ht
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff t).mpr ht]
  exact Subgroup.one_mem _

@[expose] noncomputable def centerPreEquiv (T : Subgroup X) [T.Normal] :
    X ⧸ centerPre T ≃* (X ⧸ T) ⧸ Subgroup.center (X ⧸ T) :=
  (QuotientGroup.quotientQuotientEquivQuotient T (centerPre T) (le_centerPre T)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective T) _))

theorem isSolvable_centerPre (T : Subgroup X) [T.Normal] (hT : Group.IsSolvable T) :
    Group.IsSolvable (centerPre T) := by
  let g : centerPre T →* Subgroup.center (X ⧸ T) :=
    ((QuotientGroup.mk' T).comp (centerPre T).subtype).codRestrict _ fun x => x.2
  have hcomm : Group.IsSolvable (Subgroup.center (X ⧸ T)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (le_centerPre T)) g ?_
  intro x hx
  have hx' : QuotientGroup.mk' T (x : X) = 1 := congrArg Subtype.val hx
  exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp hx'⟩, rfl⟩

theorem not_dvd_card_centerPre [Finite X] (T : Subgroup X) [T.Normal] {p : ℕ} (hp : p.Prime)
    (hT : ¬ p ∣ Nat.card T) (hZ : ¬ p ∣ Nat.card (Subgroup.center (X ⧸ T))) :
    ¬ p ∣ Nat.card (centerPre T) := by
  let g : centerPre T →* Subgroup.center (X ⧸ T) :=
    ((QuotientGroup.mk' T).comp (centerPre T).subtype).codRestrict _ fun x => x.2
  have hker : Nat.card g.ker = Nat.card T := by
    have hk : g.ker = T.subgroupOf (centerPre T) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
      · intro hx
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_centerPre T)).toEquiv
  have hmul := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker, hker] at hmul
  have hR : Nat.card g.range ∣ Nat.card (Subgroup.center (X ⧸ T)) :=
    Subgroup.card_subgroup_dvd_card _
  rw [← hmul]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact hT h1
  · exact hZ (h1.trans hR)

theorem le_center_of_commutator_le [Group.IsPerfect X] {N : Subgroup X}
    (hN : ⁅N, (⊤ : Subgroup X)⁆ ≤ Subgroup.center X) : N ≤ Subgroup.center X := by
  have hZ : ∀ M : Subgroup X, M ≤ Subgroup.center X → ⁅M, (⊤ : Subgroup X)⁆ = ⊥ := by
    intro M hM
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ]
    exact hM
  have h1 : ⁅⁅(⊤ : Subgroup X), N⁆, (⊤ : Subgroup X)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm ⊤ N]
    exact hZ _ hN
  have h := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := ⊤) (H₂ := ⊤) (H₃ := N) h1
    (hZ _ hN)
  have hp : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  rw [hp, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.coe_top, Subgroup.centralizer_univ] at h
  exact h

theorem isQuasisimple_of_le_center [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup (X ⧸ K)] (hnc : ∃ a b : X ⧸ K, a * b ≠ b * a)
    (hK : K ≤ Subgroup.center X) : IsQuasisimple X := by
  have hZK : Subgroup.center X = K := by
    refine le_antisymm ?_ hK
    have hM : ((Subgroup.center X).map (QuotientGroup.mk' K)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective K)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Subgroup.center X).map (QuotientGroup.mk' K)) with h | h
    · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hb : b ∈ (Subgroup.center X).map (QuotientGroup.mk' K) := h ▸ Subgroup.mem_top b
      obtain ⟨z, hz, rfl⟩ := hb
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K a
      apply hab
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz a]
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (QuotientGroup.quotientMulEquivOfEq hZK).isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hnc
    let e := QuotientGroup.quotientMulEquivOfEq hZK
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this

end General

variable {G : Type} [Group G]

theorem isBar211_of_case211 [Finite G] {A L : Subgroup G} {c : G} (h : Case211 A c L) :
    IsBar211 (lBar L) := by
  rcases h with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h | h, -⟩ | ⟨h | h, -⟩ | ⟨h, -⟩ | ⟨h | h, -⟩ |
      ⟨⟨n, hn, he, ⟨h, -⟩ | ⟨h, -⟩⟩, -⟩ | ⟨⟨n, hn, he, h | h⟩, -⟩ |
      ⟨⟨n, hn, he, h | h⟩ | h, -⟩ | ⟨⟨n, hn, hno, h⟩, -⟩ | ⟨h | h, -⟩ | ⟨h | h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, hn, he, Or.inl h⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, hn, he, Or.inr (Or.inl h)⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, hn, he, Or.inr (Or.inr (Or.inl h))⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, hn, he, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, hn, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, hn, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨n, hn, hno, h⟩)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))

theorem commutatorElement_mem {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) {l : G} (hl : l ∈ L) : ⁅l, a⁆ ∈ L := by
  rw [commutatorElement_def]
  have h : a * l⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ha _).mp (L.inv_mem hl)
  have e : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
  rw [e]
  exact L.mul_mem hl h

theorem pCore_two_le_center [Finite G] (h45 : Sec4.Item4_5) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) : CFSG.pCore 2 L ≤ Subgroup.center L := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hLq : IsQuasisimple (lBar L) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨hTs, -, -, -, -, -, hpT⟩ := solvable_prime_complement_core_characterization
    (H := L) Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  set Q := CFSG.pCore 2 L with hQ
  set QG := Q.map L.subtype with hQG
  have hQT : Q ≤ T := hpT 2 Nat.prime_two (by norm_num)
  have hQ2 : IsPGroup 2 QG := CFSG.pCore_isPGroup.map _
  have hAQ : A ≤ Subgroup.normalizer (QG : Set G) :=
    hAL.trans (SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic L Q)
  have hQθ : QG ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) :=
    (Subgroup.map_mono hQT).trans (theta_le_theta_centralizer hLc)
  have hcomm : ⁅QG, A⁆ = ⊥ :=
    Sec6.commutator_eq_bot_of_mem_partTwoS hpair.mem_S hcA hc1 le_rfl hQθ hQ2 hAQ
  have hLQ : L ≤ Subgroup.normalizer (QG : Set G) := Sec6.le_normalizer_map_subtype Q
  have h3 : ⁅⁅L, A⁆, QG⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm A QG, hcomm, Subgroup.commutator_bot_left]
    · exact eq_bot_iff.mpr ((Subgroup.commutator_mono
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hLQ) le_rfl).trans hcomm.le)
  have hLAQ : ⁅L, A⁆ ≤ Subgroup.centralizer (QG : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  set C := Subgroup.centralizer (Q : Set L) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hLAC : ∀ (l : L) (a : G) (ha : a ∈ A),
      (⟨⁅(l : G), a⁆, commutatorElement_mem (hAL ha) l.2⟩ : L) ∈ C := by
    intro l a ha
    rw [hC, Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hx : ⁅(l : G), a⁆ ∈ ⁅L, A⁆ := Subgroup.commutator_mem_commutator l.2 ha
    have := Subgroup.mem_centralizer_iff.mp (hLAQ hx) (q : G) ⟨q, hq, rfl⟩
    simpa using this
  set K₀ := centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPre T hTs
  have : IsSimpleGroup (lBar L ⧸ Subgroup.center (lBar L)) := hLq.2.1
  have : IsSimpleGroup (L ⧸ K₀) := (centerPreEquiv T).isSimpleGroup
  have : Group.IsPerfect (lBar L) := hLq.1
  have hCK : ¬ C ≤ K₀ := by
    intro hCK
    have hσ : ∀ (a : G) (ha : a ∈ A), ∀ l : L,
        (((L.normalizerMonoidHom ⟨a, hAL ha⟩ l : L) : lBar L)) = (l : lBar L) := by
      intro a ha
      set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, hAL ha⟩) with hσ
      have hid :=
        CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
        σ.toMonoidHom (by
          intro z
          obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
          change ((l : lBar L))⁻¹ * σ (l : lBar L) ∈ Subgroup.center (lBar L)
          rw [hσ, Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
          have hmem : l⁻¹ * L.normalizerMonoidHom ⟨a, hAL ha⟩ l ∈ C := by
            have h := hLAC l⁻¹ a ha
            convert h using 1
            apply Subtype.ext
            simp [commutatorElement_def, mul_assoc]
          exact hCK hmem)
      intro l
      have := congrArg (fun φ : lBar L →* lBar L => φ (l : lBar L)) hid
      simpa [hσ, Sec4.thetaQuotMulAut_mk] using this
    obtain ⟨E', -, hE'A, hLE'⟩ := mem_lZeroUnion_iff.mp hpairs.2.2.1.2.1
    obtain ⟨-, U', hU', hnot⟩ := hLE'
    apply hnot
    rw [Subgroup.commutator_le]
    intro u hu e he
    have hul : u ∈ L := hU'.1 hu
    have h := hσ e (hE'A he) ⟨u, hul⟩⁻¹
    rw [eq_comm, QuotientGroup.eq] at h
    refine ⟨_, h, ?_⟩
    simp [commutatorElement_def, mul_assoc]
  have hCtop : C = ⊤ := Sec4.Census.eq_top_of_not_le hK₀s hCK
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro l
  have hl : l ∈ C := hCtop ▸ Subgroup.mem_top l
  exact (Subgroup.mem_centralizer_iff.mp hl q hq).symm

theorem isQuasisimple_of_quotient_pCore_two {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (h1 : IsQuasisimple (X ⧸ CFSG.pCore 2 X)) (hO2 : CFSG.pCore 2 X ≤ Subgroup.center X) :
    IsQuasisimple X := by
  obtain ⟨hTs, -, -, -, -, -, hpT⟩ := solvable_prime_complement_core_characterization
    (H := X) Nat.prime_three
  set T := aschbacherSolvableCore 3 X with hT
  set O := CFSG.pCore 2 X with hO
  have : IsSimpleGroup ((X ⧸ T) ⧸ Subgroup.center (X ⧸ T)) := hq.2.1
  have : IsSimpleGroup (X ⧸ centerPre T) := (centerPreEquiv T).isSimpleGroup
  have hnc : ∃ a b : X ⧸ centerPre T, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    refine ⟨(centerPreEquiv T).symm a, (centerPreEquiv T).symm b, fun h => hab ?_⟩
    simpa using congrArg (centerPreEquiv T) h
  have hN : (T.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hTZ : T.map (QuotientGroup.mk' O) ≤ Subgroup.center (X ⧸ O) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups h1 hN with h | h
    · exfalso
      have hs : Group.IsSolvable (T.map (QuotientGroup.mk' O)) :=
        Group.isSolvable_of_surjective ((QuotientGroup.mk' O).subgroupMap_surjective T)
      rw [h] at hs
      have hsol : Group.IsSolvable (X ⧸ O) :=
        Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := X ⧸ O)).toMonoidHom)
          (Subgroup.topEquiv (G := X ⧸ O)).surjective
      have : Nontrivial (X ⧸ O) := CFSG.LocalCores.isQuasisimple_nontrivial h1
      have : Group.IsPerfect (X ⧸ O) := h1.1
      exact Group.IsPerfect.not_isSolvable (X ⧸ O) hsol
    · exact h
  have hTO : ⁅T, (⊤ : Subgroup X)⁆ ≤ Subgroup.center X := by
    refine le_trans ?_ hO2
    rw [Subgroup.commutator_le]
    rintro t ht x -
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hTZ ⟨t, ht, rfl⟩) _).symm
  have hTc : T ≤ Subgroup.center X := le_center_of_commutator_le hTO
  have hK₀ : ⁅centerPre T, (⊤ : Subgroup X)⁆ ≤ Subgroup.center X := by
    refine le_trans ?_ hTc
    rw [Subgroup.commutator_le]
    rintro z hz x -
    rw [← QuotientGroup.ker_mk' T, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hz _).symm
  exact isQuasisimple_of_le_center hnc (le_center_of_commutator_le hK₀)

theorem exists_nine_quotient {X : Type*} [Group X] (T : Subgroup X) [T.Normal]
    {E' : Subgroup ((X ⧸ T) ⧸ Subgroup.center (X ⧸ T))} (hE3 : Monoid.exponent E' ∣ 3)
    (hE9 : Nat.card E' = 9) :
    ∃ E : Subgroup (X ⧸ centerPre T), Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  let f := (centerPreEquiv T).symm.toMonoidHom
  have hf : Function.Injective f := (centerPreEquiv T).symm.injective
  let e : E' ≃* E'.map f := E'.equivMapOfInjective f hf
  refine ⟨E'.map f, ?_, ?_⟩
  · rwa [← Monoid.exponent_eq_of_mulEquiv e]
  · rwa [← Nat.card_congr e.toEquiv]

end Item21EarlyProof

open Item21EarlyProof

theorem item213_of (h211 : Item211) (h44 : Sec4.Item4_4)
    (h45 : Sec4.Item4_5) (hOrd : KS213Order) (hNine : KS213Nine) (hTwo : KS213TwoRank)
    (hCen : Item213Center) : Item213 := by
  intro G _ _ A E U c L hpair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hc1 : c ≠ 1 := hpairs.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hLq : IsQuasisimple (lBar L) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hX : IsBar211 (lBar L) := isBar211_of_case211 (h211 G A E U c L hpair)
  obtain ⟨hTs, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  set K₀ := centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPre T hTs
  have : IsSimpleGroup (lBar L ⧸ Subgroup.center (lBar L)) := hLq.2.1
  have : IsSimpleGroup (L ⧸ K₀) := (centerPreEquiv T).isSimpleGroup
  have hnc : ∃ a b : L ⧸ K₀, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hLq
    refine ⟨(centerPreEquiv T).symm a, (centerPreEquiv T).symm b, fun h => hab ?_⟩
    simpa using congrArg (centerPreEquiv T) h
  have hZK : Subgroup.center (L ⧸ K₀) = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  have hbig : 5616 < Nat.card (L ⧸ K₀) := by
    rw [Nat.card_congr (centerPreEquiv T).toEquiv]
    exact hOrd _ hX
  have hL4 : SectionFourHyp L := by
    have hLtop : L ≠ ⊤ := fun hLt =>
      Sec6.centralizer_ne_top_of_ne_one hpair.standing.toTheoremFourHyp hc1
        (top_le_iff.mp (hLt ▸ Sec6.le_centralizer_of_mem_thetaComponentsAt hLc))
    exact hpair.standing.toTheoremFourHyp.sectionFourHyp hLtop
  have hcardA : ∀ n : ℕ, 5 ≤ n → n ≤ 6 →
      1 < Nat.card (alternatingGroup (Fin n)) ∧ Nat.card (alternatingGroup (Fin n)) < 5616 := by
    intro n hn5 hn6
    rw [KFacts.KS14.card_alternatingGroup_fin (by omega)]
    interval_cases n <;> decide
  rcases h44 L hL4 hLp K₀ hK₀s inferInstance with
    h1 | he2 | ⟨p, hp, hp3, he3⟩ | (he4 | h4b) | ⟨hO2, h5⟩
  ·
    exact isQuasisimple_of_quotient_pCore_two hLq h1 (pCore_two_le_center h45 hpair)
  ·
    exfalso
    obtain ⟨e2⟩ := he2
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
      rw [Sec4.Census.card_SL2]
      norm_num
    exact Sec13.false_of_surjective_of_card_lt hK₀s (e2.toMonoidHom.comp (QuotientGroup.mk' _))
      (e2.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)
  ·
    exfalso
    obtain ⟨e3⟩ := he3
    obtain ⟨E', hE'3, hE'9⟩ := hNine _ hX
    obtain ⟨E, hE3, hE9⟩ := exists_nine_quotient T hE'3 hE'9
    exact Sec13.false_of_oTwoP_equiv_SL2 hp hp3 e3 hE3 hE9
  ·
    exfalso
    obtain ⟨e4⟩ := he4
    have hc : Nat.card (projSL 3 (GaloisField 3 1)) = 5616 := by
      rw [← Nat.card_congr Sec4.Census.sl3EquivProjSL.toEquiv, Sec4.Census.card_SL3_three]
    exact Sec13.false_of_surjective_of_card_lt hK₀s (e4.toMonoidHom.comp (QuotientGroup.mk' _))
      (e4.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)
  ·
    obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
    exact (Sec13.false_of_isExtOf_of_card_lt hK₀s h4b h1 (by omega)).elim
  ·
    by_cases h3Z : 3 ∣ Nat.card (Subgroup.center (lBar L))
    · exact hCen G A E U c L hpair hO2 h3Z
    have hK₀3 : ¬ 3 ∣ Nat.card K₀ := not_dvd_card_centerPre T Nat.prime_three hT3 h3Z
    exfalso
    rcases h5 hK₀3 with ⟨hm, hO | hext⟩ | ⟨-, hext | hext | hext⟩
    ·
      have hOK := Sec13.oddCore_le_of_isQuasisimple hK₀s hO
      have hZ := Sec13.center_quotient_oddCore_eq_map hK₀s hZK hO hOK
      let e : (L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L) ≃* L ⧸ K₀ :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans
          (QuotientGroup.quotientQuotientEquivQuotient _ _ hOK)
      have hZ2 : IsPGroup 2 (Subgroup.center (L ⧸ CFSG.oddCore L)) :=
        Sec4.Census.isPGroup_two_center_of_oddCore_eq_bot
          (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot L)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hrank : CFSG.Open.pRank 2 (⊤ : Subgroup (L ⧸ CFSG.oddCore L)) =
          CFSG.Open.pRank 2 (⊤ : Subgroup L) :=
        CFSG.SectionRank.pRank_quotient_eq (CFSG.oddCore L) (fun h2 =>
          (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore L))
            (even_iff_two_dvd.mpr h2))
      have := hTwo (lBar L) hX (L ⧸ CFSG.oddCore L) hO hZ2 ⟨e.trans (centerPreEquiv T)⟩
      omega
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact Sec13.false_of_isExtOf_of_card_lt hK₀s hext h1 (by omega)
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact Sec13.false_of_isExtOf_of_card_lt hK₀s hext h1 (by omega)
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact Sec13.false_of_isExtOf_of_card_lt hK₀s hext h1 (by omega)
    · obtain ⟨h1, h2⟩ := hcardA 6 (by norm_num) le_rfl
      exact Sec13.false_of_isExtOf_of_card_lt hK₀s hext h1 (by omega)

end CFSG.RankThree.PartTwo.Sec21

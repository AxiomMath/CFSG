module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Sec
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 (NoSimpleSec)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem noSimpleSec_sup_of_le_normalizer {p : ℕ} {N X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hN : NoSimpleSec p ↥N)
    (hX : NoSimpleSec p ↥X) : NoSimpleSec p ↥(N ⊔ X) := by
  let W : Subgroup G := N ⊔ X
  have hNW : N ≤ W := le_sup_left
  have hXW : X ≤ W := le_sup_right
  haveI : (N.subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hXN)
  refine NoSimpleSec.of_extension (N.subgroupOf W)
    (NoSimpleSec.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNW) hN) ?_
  let f : ↥X →* ↥W ⧸ N.subgroupOf W := (QuotientGroup.mk' _).comp (Subgroup.inclusion hXW)
  refine NoSimpleSec.of_surjective f (fun z => ?_) hX
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf W) z
  have hw : (w : G) ∈ (N : Set G) * (X : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N X hXN]
    exact w.2
  obtain ⟨n, hn, x, hx, hnx⟩ := Set.mem_mul.mp hw
  let nW : ↥W := ⟨n, hNW hn⟩
  let xW : ↥W := ⟨x, hXW hx⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  have hwn : w = nW * xW := Subtype.ext hnx.symm
  have hnq : (QuotientGroup.mk' (N.subgroupOf W)) nW = 1 := by
    simpa using (QuotientGroup.eq_one_iff (N := N.subgroupOf W) (x := nW)).mpr
      (show nW ∈ N.subgroupOf W from hn)
  calc f ⟨x, hx⟩ = (QuotientGroup.mk' (N.subgroupOf W)) xW := rfl
    _ = (QuotientGroup.mk' (N.subgroupOf W)) (nW * xW) := by rw [map_mul, hnq, one_mul]
    _ = (QuotientGroup.mk' (N.subgroupOf W)) w := by rw [hwn]

theorem noSimpleSec_sup_pPrimeCoreOf {p : ℕ} (hp : 3 ∣ p) {C X : Subgroup G}
    (hXC : X ≤ C) (hX : NoSimpleSec p ↥X) :
    NoSimpleSec p ↥(pPrimeCoreOf 3 C ⊔ X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine noSimpleSec_sup_of_le_normalizer (hXC.trans (Sec14.le_normalizer_pPrimeCoreOf 3 C))
    (NoSimpleSec.of_not_dvd fun h => ?_) hX
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (Sec14.coprime_card_pPrimeCoreOf (G := G) 3 C) (hp.trans h)

theorem noSimpleSec_sup {p : ℕ} (hp : 3 ∣ p) {A : Subgroup G} {a : G} (ha : a ∈ A)
    {X : Subgroup G} (hXa : X ≤ Subgroup.centralizer ({a} : Set G))
    (hnorm : Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hX : NoSimpleSec p ↥X) :
    NoSimpleSec p ↥(pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Oa : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))
  let OA : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  have hOA : OA ≤ Subgroup.normalizer ((Oa ⊔ X : Subgroup G) : Set G) :=
    (Sec14.pPrimeCoreOf_le 3 _).trans
      ((le_inf (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
        (Subgroup.centralizer_le_normalizer (A : Set G))).trans hnorm)
  have h := noSimpleSec_sup_of_le_normalizer hOA (noSimpleSec_sup_pPrimeCoreOf hp hXa hX)
    (NoSimpleSec.of_not_dvd fun h => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Sec14.coprime_card_pPrimeCoreOf (G := G) 3 _) (hp.trans h))
  rwa [show Oa ⊔ X ⊔ OA = Oa ⊔ OA ⊔ X by ac_rfl] at h

theorem noSimpleSec_of_eq_sup_theta {p : ℕ} {X Y : Subgroup G}
    (hXY : X = Y ⊔ inSubgroup (aschbacherSolvableCore 3) X) (hY : NoSimpleSec p ↥Y) :
    NoSimpleSec p ↥X := by
  let θ : Subgroup ↥X := aschbacherSolvableCore 3 ↥X
  haveI : θ.Normal := aschbacherSolvableCore_normal 3 ↥X
  haveI : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have hYX : Y ≤ X := by rw [hXY]; exact le_sup_left
  have h := noSimpleSec_sup_of_le_normalizer
    (hYX.trans (CFSG.ABGLocalTools.le_normalizer_map_subtype X θ))
    (NoSimpleSec.of_mulEquiv (θ.equivMapOfInjective _ X.subtype_injective).symm
      (NoSimpleSec.of_isSolvable p)) hY
  rw [hXY, sup_comm]
  exact h

theorem noSimpleSec21_of_a6 {X : Subgroup G}
    (h : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    NoSimpleSec 21 ↥X := by
  let θ : Subgroup ↥X := aschbacherSolvableCore 3 ↥X
  haveI : θ.Normal := aschbacherSolvableCore_normal 3 ↥X
  haveI hθsol : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  refine NoSimpleSec.of_extension θ (NoSimpleSec.of_isSolvable 21) ?_
  have hQ : ¬ 7 ∣ Nat.card (↥X ⧸ θ) := by
    rcases h with h6 | hprod
    · have hcard : Nat.card (↥X ⧸ θ) = 1080 := by
        obtain ⟨hc, ⟨e⟩⟩ := h6
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
              (Subgroup.center (↥X ⧸ θ)),
            Nat.card_congr e.toEquiv, hc,
            CFSG.RankThree.PartTwo.KFacts.K412.card_alternating_six_seven.1]
      rw [hcard]
      norm_num
    · obtain ⟨U, V, -, -, hUVtop, hUVcomm, -, hU6, hV6⟩ := hprod
      have hU1080 : Nat.card ↥U = 1080 := by
        obtain ⟨hc, ⟨e⟩⟩ := hU6
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥U),
            Nat.card_congr e.toEquiv, hc,
            CFSG.RankThree.PartTwo.KFacts.K412.card_alternating_six_seven.1]
      have hV1080 : Nat.card ↥V = 1080 := by
        obtain ⟨hc, ⟨e⟩⟩ := hV6
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥V),
            Nat.card_congr e.toEquiv, hc,
            CFSG.RankThree.PartTwo.KFacts.K412.card_alternating_six_seven.1]
      have hcomm : ∀ u : ↥U, ∀ v : ↥V, Commute (U.subtype u) (V.subtype v) := by
        have hUVle : U ≤ Subgroup.centralizer (V : Set (↥X ⧸ θ)) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUVcomm
        intro u v
        exact (Subgroup.mem_centralizer_iff.mp (hUVle u.2) v v.2).symm
      let f : ↥U × ↥V →* (↥X ⧸ θ) := U.subtype.noncommCoprod V.subtype hcomm
      have hrange : f.range = ⊤ := by
        change (U.subtype.noncommCoprod V.subtype hcomm).range = ⊤
        rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype,
          hUVtop]
      have hsurj : Function.Surjective f := by
        rw [← MonoidHom.range_eq_top]
        exact hrange
      have hdvd : Nat.card (↥X ⧸ θ) ∣ Nat.card (↥U × ↥V) :=
        Subgroup.card_dvd_of_surjective (f := f) hsurj
      have hdvd' : Nat.card (↥X ⧸ θ) ∣ 1080 * 1080 := by
        simpa [Nat.card_prod, hU1080, hV1080] using hdvd
      intro h21
      exact (by norm_num : ¬ 7 ∣ 1080 * 1080) (h21.trans hdvd')
  refine NoSimpleSec.of_not_dvd ?_
  intro h21
  exact hQ ((by norm_num : 7 ∣ 21).trans h21)

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

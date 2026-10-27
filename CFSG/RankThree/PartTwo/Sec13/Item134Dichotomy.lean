module

public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Orders

theorem card_eq_of_isTripleCover_six {X : Type*} [Group X]
    (h : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) : Nat.card X = 1080 :=
  KFacts.KS14.card_eq_of_isExtOf_alternating_six h.isExtOf

theorem not_isSLThreePiAt_two_pow {X : Type} [Group X] (hX : Nat.card X = 1080) {n : ℕ}
    (hn : 1 ≤ n) : ¬ Sec4.IsSLThreePiAt X (2 ^ n) := by
  rintro ⟨F, _, _, ⟨hF, h3, ⟨e⟩⟩ | ⟨hF, h3, ⟨e⟩⟩⟩
  · have hc := Nat.card_congr e.toEquiv
    rw [hX, CFSG.SectionRank.OddCover.card_statedSL_three, hF] at hc
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n
        norm_num at h3
      · exact h
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have h1 : 64 ≤ (2 ^ n) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 15 ≤ (2 ^ n) ^ 2 - 1 := by
      have := Nat.pow_le_pow_left hq 2
      omega
    have h4 : 63 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
    omega
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * n)
      (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
    have hc := Nat.card_congr e.toEquiv
    rw [hX, CFSG.SectionRank.OddCover.card_statedSU_three (p := 2) (f := n) hF] at hc
    rcases Nat.lt_or_ge n 2 with h | hn2
    · interval_cases n
      norm_num at hc
    · have hq : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have h1 : 64 ≤ (2 ^ n) ^ 3 := by
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
      have h2 : 15 ≤ (2 ^ n) ^ 2 - 1 := by
        have := Nat.pow_le_pow_left hq 2
        omega
      have h4 : 65 ≤ (2 ^ n) ^ 3 + 1 := by omega
      have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
      omega

end Orders


section Sup

variable {G : Type*} [Group G] [Finite G]

theorem nonempty_quotTheta_equiv_of_eq_sup {T X : Subgroup G} (hTX : T ≤ X)
    (hX : X = T ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    Nonempty (↥T ⧸ aschbacherSolvableCore 3 ↥T ≃* ↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
  set θ₀ := aschbacherSolvableCore 3 ↥X with hθ₀
  obtain ⟨hθs, -, hθp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  have htop : T.subgroupOf X ⊔ θ₀ = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTX, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hX.symm
  have hmap : (T.subgroupOf X).map (QuotientGroup.mk' θ₀) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' θ₀)) htop
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective θ₀),
      (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' θ₀).ge, sup_bot_eq] at h
    exact h
  let f : ↥T →* ↥X ⧸ θ₀ := (QuotientGroup.mk' θ₀).comp (Subgroup.inclusion hTX)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨t, ht, htq⟩ := (hmap ▸ Subgroup.mem_top q : q ∈ (T.subgroupOf X).map _)
    exact ⟨⟨(t : G), ht⟩, by rw [← htq]; rfl⟩
  obtain ⟨hks, hk3⟩ := ker_facts_of_injective f (Subgroup.inclusion hTX)
    (Subgroup.inclusion_injective hTX) θ₀
    (fun y hy => by
      have h2 : QuotientGroup.mk' θ₀ (Subgroup.inclusion hTX y) = 1 := hy
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2) hθs hθp
  have hQ : aschbacherSolvableCore 3 (↥X ⧸ θ₀) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers Nat.prime_three θ₀ hθs hθp).2.2.1
  exact nonempty_quotTheta_equiv_of_surjective f hf hks hk3 hQ

end Sup

theorem dichotomy134 (h426 : Sec4.Item4_26ThetaA6) (h415 : Sec4.Item4_15)
    {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K) :
    (K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
          inSubgroup (aschbacherSolvableCore 3) K ∧
        Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∨
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) CFSG.Blueprint.NativeSporadic.ON := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  obtain ⟨S, ⟨Q, hQ⟩, hZS⟩ := hS
  have hdZ : d ∈ (Subgroup.center S).map S.subtype := hZS ▸ Subgroup.mem_zpowers d
  obtain ⟨s, hs, hsd⟩ := hdZ
  have hdS : d ∈ S := hsd ▸ s.2
  have hdQ : d ∈ (Q : Subgroup ↥L).map L.subtype := hQ ▸ hdS
  obtain ⟨q₀, hq₀, hq₀d⟩ := hdQ
  have hdL : d ∈ L := hq₀d ▸ q₀.2
  have hc : ∃ S' : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S' : Subgroup ↥L) ∧
      (S' : Subgroup ↥L) ≤ Subgroup.centralizer ({(⟨d, hdL⟩ : ↥L)} : Set ↥L) := by
    refine ⟨Q, ?_, fun q hq => ?_⟩
    · have : q₀ = ⟨d, hdL⟩ := Subtype.ext hq₀d
      exact this ▸ hq₀
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hqS : (q : G) ∈ S := hQ ▸ Subgroup.mem_map_of_mem L.subtype hq
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hs ⟨q, hqS⟩)
      have hsd' : (s : G) = d := hsd
      simp only [Subgroup.coe_mul] at h1
      rw [hsd'] at h1
      exact h1
  obtain ⟨hqs, htc, hdJ, hcen⟩ := residual_facts h415 hJ hdL hd1 hc
  replace hdJ : d ∈ J := hdJ
  replace hcen : ∀ x ∈ J, x ∈ Subgroup.centralizer (J : Set G) → ∀ k : ℕ, x ^ 3 ^ k = 1 →
      x ∈ Subgroup.zpowers d := hcen
  replace htc : Sec4.IsTripleCover (↥J ⧸ aschbacherSolvableCore 3 ↥J)
      (alternatingGroup (Fin 6)) := htc
  have hcd : c * d = d * c := h.commute h.mem_A hdA
  set D := Subgroup.centralizer ({d} : Set G) with hD
  obtain ⟨T, hT, hTJ⟩ := Sec14.exists_mem_thetaComponentsAt_of_residual hcd
    h.mem_thetaComponentsAt hqs
  replace hTJ : T.map D.subtype = J := hTJ
  set c' : ↥D := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr hcd⟩ with hc'
  obtain ⟨hKD, hK₀⟩ := PartOne.mem_thetaComponentsAt_iff.mp hK
  set K₀ := K.subgroupOf D with hK₀def
  obtain ⟨hTc, hT'⟩ := PartOne.mem_thetaComponentsAt_iff.mp hT
  have hK₀map : K₀.map D.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKD
  have hTK₀ : T ≤ K₀ := by
    rw [← Subgroup.map_le_map_iff_of_injective D.subtype_injective, hTJ, hK₀map]
    exact hLK
  have hle : T ≤ K₀ ⊓ Subgroup.centralizer ({c'} : Set ↥D) := le_inf hTK₀ hTc
  have hTin : T ∈ thetaComponentsIn (K₀ ⊓ Subgroup.centralizer ({c'} : Set ↥D)) :=
    ⟨T.subgroupOf _, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hle
      inf_le_right hT', Subgroup.map_subgroupOf_eq_of_le hle⟩
  let eTJ : ↥T ≃* ↥J :=
    (T.equivMapOfInjective D.subtype D.subtype_injective).trans (MulEquiv.subgroupCongr hTJ)
  have hTA6 : Sec4.IsTripleCover (↥T ⧸ aschbacherSolvableCore 3 ↥T) (alternatingGroup (Fin 6)) :=
    isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eTJ).symm htc
  set dD : ↥D := ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hdD
  have hdDc : dD ∈ Subgroup.center ↥D := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  set Y := T ⊓ Subgroup.centralizer (T : Set ↥D) with hY
  have hZ : inSubgroup (CFSG.pCore 3) Y ≤ Subgroup.center ↥D := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥Y)) ⟨w, hw⟩
    have hk1 : w ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hwk : ((w : ↥D) : G) ^ 3 ^ k = 1 := by
      have := congrArg (fun u : ↥Y => ((u : ↥D) : G)) hk1
      simpa using this
    have hwJ : ((w : ↥D) : G) ∈ J := hTJ ▸ Subgroup.mem_map_of_mem D.subtype w.2.1
    have hwC : ((w : ↥D) : G) ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      rw [← hTJ] at hj
      obtain ⟨t, ht, rfl⟩ := hj
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp w.2.2 t ht)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hcen _ hwJ hwC k hwk)
    have hw' : (w : ↥D) = dD ^ m := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    change (w : ↥D) ∈ Subgroup.center ↥D
    rw [hw']
    exact Subgroup.zpow_mem _ hdDc m
  have hZne : inSubgroup (CFSG.pCore 3) Y ≠ ⊥ := by
    have hdT : dD ∈ T := by
      rw [← hTJ] at hdJ
      obtain ⟨t, ht, htd⟩ := hdJ
      have : t = dD := Subtype.ext htd
      exact this ▸ ht
    have hdTC : dD ∈ Subgroup.centralizer (T : Set ↥D) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t _
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp t.2)
    set w : ↥Y := ⟨dD, hdT, hdTC⟩ with hw
    have hwcomm : ∀ y : ↥Y, y * w = w * y := fun y =>
      Subtype.ext (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (y : ↥D).2))
    have hwn : (Subgroup.zpowers w).Normal := ⟨fun n hn g => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [((Commute.zpow_right (hwcomm g) m)).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers w m⟩
    have hd3 : d ^ 3 = 1 := h.isElemAbelian.2 d hdA
    have hw3 : w ^ 3 = 1 := Subtype.ext (Subtype.ext (by simpa using hd3))
    have hw1 : w ≠ 1 := fun h1 => hd1 (congrArg (fun u : ↥Y => ((u : ↥D) : G)) h1)
    have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    have hwp : IsPGroup 3 (Subgroup.zpowers w) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwo, pow_one])
    have hwP : w ∈ CFSG.pCore 3 ↥Y :=
      (le_sSup ⟨hwn, hwp⟩ : Subgroup.zpowers w ≤ CFSG.pCore 3 ↥Y) (Subgroup.mem_zpowers w)
    intro hbot
    have hmem : (w : ↥D) ∈ inSubgroup (CFSG.pCore 3) Y := ⟨w, hwP, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hd1 (congrArg Subtype.val hmem)
  have hDtop : D ≠ ⊤ := by
    intro hDt
    have hdZ' : d ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ D := hDt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases h.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hdZ'
      exact hd1 hdZ'
    · obtain ⟨a, b, hab⟩ := h.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a)
  have hS4 : SectionFourHyp ↥D := h.toTheoremFourHyp.sectionFourHyp hDtop
  have hc'3 : orderOf c' = 3 := (Subgroup.orderOf_mk c _).trans h.orderOf_eq
  let eK : ↥K₀ ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKD
  rcases h426 ↥D hS4 K₀ hK₀ c' hc'3 T hTin hTA6 hZne hZ with h1 | ⟨n, hn, -, hn2⟩ |
    ⟨hON, -⟩
  · left
    have hθmap : (inSubgroup (aschbacherSolvableCore 3) K₀).map D.subtype =
        inSubgroup (aschbacherSolvableCore 3) K := by
      rw [inSubgroup, inSubgroup, Subgroup.map_map,
        ← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eK, Subgroup.map_map]
      rfl
    refine ⟨?_, ?_⟩
    · calc K = K₀.map D.subtype := hK₀map.symm
        _ = (T ⊔ inSubgroup (aschbacherSolvableCore 3) K₀).map D.subtype :=
          congrArg (Subgroup.map D.subtype) h1
        _ = J ⊔ inSubgroup (aschbacherSolvableCore 3) K := by
          rw [Subgroup.map_sup, hTJ, hθmap]
    · obtain ⟨e⟩ := nonempty_quotTheta_equiv_of_eq_sup hTK₀ h1
      exact isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eK)
        (isTripleCover_of_mulEquiv e hTA6)
  · exact absurd hn2 (not_isSLThreePiAt_two_pow (card_eq_of_isTripleCover_six hTA6) hn)
  · exact Or.inr (isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eK) hON)

end CFSG.RankThree.PartTwo.Sec13

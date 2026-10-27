module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaE
import CFSG.GroupTheory.Fitting.QuasisimpleNormalFstarTwo
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_center_map_subtype_le_centralizer {A : Type*} [Group A] (K : Subgroup A) :
    (Subgroup.center ↥K).map K.subtype ≤ Subgroup.centralizer (K : Set A) := by
  rintro z ⟨z', hz', rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨k, hk⟩)

private theorem w1369_isPGroup_zpowers_of_sq_eq_one {A : Type*} [Group A] {d : A}
    (hd : d ^ 2 = 1) : IsPGroup 2 ↥(Subgroup.zpowers d) := by
  have hdvd : orderOf d ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem Std139.alpha_context (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    {d : MulAut W} (hd : d ∈ D) (hd1 : d ≠ 1) : Is135Context (K ⊔ Subgroup.zpowers d) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdG : d ∈ G := S.DG hd
  have hKG : K ≤ G := hK.comp.1
  have hY1G : K ⊔ Subgroup.zpowers d ≤ G :=
    sup_le hKG (Subgroup.zpowers_le.mpr hdG)
  have hKG' : CFSG.IsKGroup ↥G :=
    KCore.KGroupNonab.kGroupAllSimple Assembly.inCatalog_isoInvariant
      Assembly.abelian_simple S.isK
  have hIsK : CFSG.IsKGroup ↥(K ⊔ Subgroup.zpowers d) :=
    hKG'.of_injective (Subgroup.inclusion hY1G) (Subgroup.inclusion_injective hY1G)
  have hd2 : d ^ 2 = 1 := S.elem.2 d hd
  have hdmem : d ∈ Subgroup.normalizer (K : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hK.normal d hdG)
  have hKnorm : K ⊔ Subgroup.zpowers d ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hdmem)
  have hKsubNormal : (K.subgroupOf (K ⊔ Subgroup.zpowers d)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
  have hqK : CFSG.IsQuasisimple ↥K :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥K)).mpr hK.comp.2.2
  have hP2z : IsPGroup 2 ↥(Subgroup.zpowers d) :=
    w1369_isPGroup_zpowers_of_sq_eq_one hd2
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer (K : Set (MulAut W)) ⊓
      (K ⊔ Subgroup.zpowers d))) := by
    have hle : Subgroup.centralizer (K : Set (MulAut W)) ⊓ (K ⊔ Subgroup.zpowers d) ≤ X := by
      rw [← Std139.alpha_centralizer hw2 S hn hK hirr]
      exact inf_le_left
    have hdvd : Nat.card ↥(Subgroup.centralizer (K : Set (MulAut W)) ⊓
        (K ⊔ Subgroup.zpowers d)) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [S.Xcard] at h
    exact Odd.of_dvd_nat (by decide : Odd 3) hdvd
  have hGF : CFSG.generalizedFitting ↥(K ⊔ Subgroup.zpowers d) =
      K.subgroupOf (K ⊔ Subgroup.zpowers d) :=
    CFSG.GroupTheory.generalizedFitting_sup_eq_of_isPGroup_two hqK le_sup_left le_sup_right
      hKsubNormal hP2z hCodd
  have hQleK : pCoreOf 2 (K ⊔ Subgroup.zpowers d) ≤ K := by
    change (CFSG.pCore 2 ↥(K ⊔ Subgroup.zpowers d)).map (K ⊔ Subgroup.zpowers d).subtype ≤ K
    calc (CFSG.pCore 2 ↥(K ⊔ Subgroup.zpowers d)).map (K ⊔ Subgroup.zpowers d).subtype
        ≤ (CFSG.fittingSubgroup ↥(K ⊔ Subgroup.zpowers d)).map
            (K ⊔ Subgroup.zpowers d).subtype :=
          Subgroup.map_mono (CFSG.pCore_le_fitting ↥(K ⊔ Subgroup.zpowers d) 2)
      _ ≤ (CFSG.generalizedFitting ↥(K ⊔ Subgroup.zpowers d)).map
            (K ⊔ Subgroup.zpowers d).subtype :=
          Subgroup.map_mono (by
            rw [CFSG.generalizedFitting.eq_sup]
            exact le_sup_left)
      _ = K := by rw [hGF, Subgroup.map_subgroupOf_eq_of_le le_sup_left]
  have hQ2 : IsPGroup 2 (pCoreOf 2 (K ⊔ Subgroup.zpowers d)) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 (K ⊔ Subgroup.zpowers d)
  have hQnormK : ((pCoreOf 2 (K ⊔ Subgroup.zpowers d)).subgroupOf K).Normal := by
    have hQnormY : K ⊔ Subgroup.zpowers d ≤
        Subgroup.normalizer (pCoreOf 2 (K ⊔ Subgroup.zpowers d) : Set (MulAut W)) :=
      CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2
        (K ⊔ Subgroup.zpowers d)
    exact Subgroup.normal_subgroupOf_of_le_normalizer (le_trans le_sup_left hQnormY)
  have hQne : (pCoreOf 2 (K ⊔ Subgroup.zpowers d)).subgroupOf K ≠ ⊤ := by
    intro htop
    have hKleQ : K ≤ pCoreOf 2 (K ⊔ Subgroup.zpowers d) := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥K) ∈
          (pCoreOf 2 (K ⊔ Subgroup.zpowers d)).subgroupOf K := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'
    have hK2 : IsPGroup 2 K := hQ2.to_le hKleQ
    haveI hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hqK
    haveI hperf : Group.IsPerfect ↥K := hqK.1
    exact Group.IsPerfect.not_isNilpotent ↥K hK2.isNilpotent
  have hQcenter : (pCoreOf 2 (K ⊔ Subgroup.zpowers d)).subgroupOf K ≤
      Subgroup.center ↥K :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hqK hQnormK).resolve_left hQne
  have hQleX : pCoreOf 2 (K ⊔ Subgroup.zpowers d) ≤ X := by
    have h1 : pCoreOf 2 (K ⊔ Subgroup.zpowers d) ≤
        (Subgroup.center ↥K).map K.subtype := by
      intro x hx
      have hx' : (⟨x, hQleK hx⟩ : ↥K) ∈
          (pCoreOf 2 (K ⊔ Subgroup.zpowers d)).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hQleK hx⟩, hQcenter hx', rfl⟩
    have h2 : (Subgroup.center ↥K).map K.subtype ≤
        Subgroup.centralizer (K : Set (MulAut W)) :=
      w1369_center_map_subtype_le_centralizer K
    have h3 : Subgroup.centralizer (K : Set (MulAut W)) = X :=
      Std139.alpha_centralizer hw2 S hn hK hirr
    exact h1.trans (h2.trans h3.le)
  have hQbot : pCoreOf 2 (K ⊔ Subgroup.zpowers d) = ⊥ := by
    have hdvd : Nat.card ↥(pCoreOf 2 (K ⊔ Subgroup.zpowers d)) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hQleX
      rwa [S.Xcard] at h
    have hodd : Odd (Nat.card ↥(pCoreOf 2 (K ⊔ Subgroup.zpowers d))) :=
      Odd.of_dvd_nat (by decide : Odd 3) hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact h
      · exfalso
        have h2dvd : 2 ∣ Nat.card ↥(pCoreOf 2 (K ⊔ Subgroup.zpowers d)) := by
          rw [hk]
          exact dvd_pow_self 2 h.ne'
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
    have hcard1 : Nat.card ↥(pCoreOf 2 (K ⊔ Subgroup.zpowers d)) = 1 := by
      rw [hk, hk0, pow_zero]
    exact Subgroup.card_eq_one.mp hcard1
  have hFstar : Fstar (K ⊔ Subgroup.zpowers d) = K := by
    rw [Fstar, CFSG.Adapters.genFittingFStar_eq_foundations, hGF,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left]
  refine ⟨hIsK, ?_, le_sup_left, hFstar, hqK, hirr⟩
  intro P hPY hPn hP2
  have hPle : P ≤ pCoreOf 2 (K ⊔ Subgroup.zpowers d) :=
    CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hPY hPn hP2
  rw [hQbot] at hPle
  exact le_bot_iff.mp hPle

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

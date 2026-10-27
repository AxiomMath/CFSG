module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPerfectCyclicNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearSylowIntoComplement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearSemidirectPSL2Complement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DefiningPSubgroupCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddSubgroupNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SFourNormalizerNoncyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddPSubgroupIndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjNormalizerCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjComplement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourInjectiveMap
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A normal complement from Dickson's PSL₂ subgroup classification

For a coprime odd-prime Sylow subgroup of a subgroup of `PSL₂(K)`, a
cyclic normalizer has a normal complement of order dividing `|K|`, except
possibly when the subgroup contains a Klein four group.  The latter outcome
is exactly the exceptional branch excluded by the ambient Section 4
centralizer argument.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups
open scoped Pointwise

universe u

/-- The normal-complement output needed by the equation-(11) bad-fibre
classification. -/
@[expose] public def SecondCaseLinearNormalComplementData
    {K : Type u} [Field K] [Finite K]
    {p : ℕ} (H : Subgroup (PSL2MatrixGroup K)) (P : Sylow p H)
    (q : ℕ) : Prop :=
  ∃ Q : Subgroup H, Q.Normal ∧
    Q.IsComplement' (Subgroup.normalizer (P : Set H)) ∧ Nat.card Q ∣ q

/-- Dickson's classification produces the required normal complement unless
the subgroup contains a Klein four group. -/
public theorem secondCase_linear_psl2_normalComplement_or_kleinFour
    {K : Type u} [Field K] [Finite K]
    {r f p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hKcard : Nat.card K = r ^ f) (hrodd : Odd r)
    (hKseven : 7 ≤ Nat.card K) (hpodd : Odd p)
    (hpcop : Nat.Coprime p (Nat.card K)) (hpne : p ≠ r)
    (H : Subgroup (PSL2MatrixGroup K)) (P : Sylow p H)
    (hPcard : Nat.card (P : Subgroup H) = p)
    (hNcyc : IsCyclic (Subgroup.normalizer (P : Set H))) :
    SecondCaseLinearNormalComplementData H P (Nat.card K) ∨
      ∃ V : Subgroup H, IsKleinFour V := by
  classical
  have hSylowCyc : ∀ S : Sylow p H, IsCyclic S := by
    intro S
    obtain ⟨S', hSS'⟩ :=
      (S.isPGroup').map H.subtype |>.exists_le_sylow
    have hScyc : IsCyclic S' := by
      exact psl2_sylow_isCyclic_of_coprime_field_card K hKcard hKseven
        p (by
          intro hp2
          subst p
          exact hpodd.not_two_dvd_nat (by simp)) hpcop S'
    have hmapcyc : IsCyclic ((S : Subgroup H).map H.subtype) := by
      let : IsCyclic S' := hScyc
      exact Subgroup.isCyclic_of_le hSS'
    let eS : (S : Subgroup H) ≃* ((S : Subgroup H).map H.subtype) :=
      Subgroup.equivMapOfInjective (S : Subgroup H) H.subtype H.subtype_injective
    exact (MulEquiv.isCyclic eS).mpr hmapcyc
  have hPp : IsPGroup p (P : Subgroup H) := P.isPGroup'
  have hPne : (P : Subgroup H) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    have hpone : 1 < p := (Fact.out : Nat.Prime p).one_lt
    simpa [hPcard] using hpone
  let N : Subgroup H := Subgroup.normalizer (P : Set H)
  have hbotComp : (⊥ : Subgroup H).IsComplement' (⊤ : Subgroup H) := by
    apply Subgroup.isComplement'_of_card_mul_and_disjoint
    · simp
    · exact disjoint_bot_left
  have hNC_of_top : N = ⊤ →
      SecondCaseLinearNormalComplementData H P (Nat.card K) := by
    intro hNtop
    refine ⟨⊥, Subgroup.normal_bot, ?_, by simp⟩
    simpa [N, hNtop] using hbotComp
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hKcard H with hElem | hCyc | hDih | hA4 | hS4 | hA5 |
      hSemi | hPSL | hPGL
  · exfalso
    let : IsElementaryAbelian r H := hElem
    obtain ⟨a, ha⟩ := (IsElementaryAbelian.isPGroup r H).exists_card_eq
    have hPdivP : p ∣ Nat.card (P : Subgroup H) := by
      rw [hPcard]
    have hPdivH : Nat.card (P : Subgroup H) ∣ Nat.card H := by
      simpa using (Subgroup.card_dvd_of_le
        (H := (P : Subgroup H)) (K := (⊤ : Subgroup H)) le_top)
    have hPdiv : p ∣ Nat.card H := hPdivP.trans hPdivH
    have hpr : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow
      (by simpa [ha] using hPdiv)
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime r)).mp hpr with h1 | heq
    · exact (Fact.out : Nat.Prime p).ne_one h1
    · exact hpne heq
  · rcases hCyc with ⟨z, hzdiv, hzcard, hHcyc⟩
    have hNtop : N = ⊤ := by
      apply Subgroup.normalizer_eq_top_iff.mpr
      refine ⟨?_⟩
      intro x hx g
      have hcomm : g * x = x * g := by
        let : IsMulCommutative H := hHcyc.isMulCommutative
        exact (isMulCommutative_iff.mp inferInstance) _ _
      rw [show g * x * g⁻¹ = x by
        calc
          g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
          _ = x := by simp]
      exact hx
    exact Or.inl (hNC_of_top hNtop)
  · rcases hDih with ⟨z, hzdiv, hzcard, he⟩
    have hPnormal : (P : Subgroup H).Normal := by
      have hP' : IsPGroup p ((P : Subgroup H).map he.some.toMonoidHom) :=
        hPp.map he.some.toMonoidHom
      have hN' : ((P : Subgroup H).map he.some.toMonoidHom).Normal :=
        dihedral_odd_subgroup_normal hpodd _ hP'
      refine ⟨?_⟩
      intro n hn g
      have hm : he.some (g * n * g⁻¹) ∈
          (P : Subgroup H).map he.some.toMonoidHom := by
        simpa using hN'.conj_mem (he.some n)
          (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩) (he.some g)
      rcases Subgroup.mem_map.mp hm with ⟨p0, hp0, heq⟩
      have heq' : g * n * g⁻¹ = p0 := by
        apply he.some.injective
        simpa using heq.symm
      rw [heq']
      exact hp0
    exact Or.inl (hNC_of_top (Subgroup.normalizer_eq_top_iff.mpr hPnormal))
  · rcases hA4 with ⟨_, he⟩
    let V : Subgroup H :=
      (alternatingGroup.kleinFour (Fin 4)).map he.some.symm.toMonoidHom
    refine Or.inr ⟨V, ?_⟩
    exact isKleinFour_map_mulEquiv_cross
      (alternatingGroup.kleinFour (Fin 4))
      (alternatingGroup.kleinFour_isKleinFour (by simp)) he.some.symm
  · rcases hS4 with ⟨_, he⟩
    exact (sfour_normalizer_not_cyclic_of_prime_card hpodd P hPcard he).elim hNcyc
  · rcases hA5 with ⟨_, he⟩
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)⟩
    let hperf : Group.IsPerfect H :=
      Group.IsPerfect.ofSurjective (f := he.some.symm.toMonoidHom)
        he.some.symm.surjective
    exact (normalizer_not_cyclic_of_perfect_of_prime_card hperf
      (P : Subgroup H) hPcard hSylowCyc hNcyc).elim
  · rcases hSemi with ⟨m, t, ht1, ht2, N₀, C₀,
      hNnormal, hNelem, hNcard, hCcyc, hCcard, hdisj, hjoin⟩
    let : IsElementaryAbelian r N₀ := hNelem
    have hNcard_dvd : Nat.card N₀ ∣ Nat.card K := by
      have hNamb : IsPGroup r (N₀.map H.subtype) :=
        (IsElementaryAbelian.isPGroup r N₀).map H.subtype
      have hdiv := psl2_defining_pgroup_card_dvd_field K hKcard
        (N₀.map H.subtype) hNamb
      rw [Subgroup.card_map_of_injective H.subtype_injective] at hdiv
      exact hdiv
    obtain ⟨g, hPgC⟩ :=
      secondCase_linear_sylow_into_semidirect_complement
        N₀ C₀ hNnormal hNcard hdisj hjoin hpne P
    let P' : Subgroup H :=
      (P : Subgroup H).map (MulAut.conj g).toMonoidHom
    have hP'leC : P' ≤ C₀ := by simpa [P'] using hPgC
    have hP'card : Nat.card P' = p := by
      change Nat.card ((P : Subgroup H).map
        (MulAut.conj g).toMonoidHom) = p
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hPcard
    have hP'ne : P' ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot]
      have hpone : 1 < p := (Fact.out : Nat.Prime p).one_lt
      simpa [hP'card] using hpone
    have hNcyc' : IsCyclic (Subgroup.normalizer (P' : Set H)) := by
      exact isCyclic_normalizer_conjugate (P : Subgroup H) g hNcyc
    have hbase := secondCase_linear_semidirect_psl2_normal_complement
      (F := K) (r := r) (p := p) hKcard hpne H N₀ C₀ P'
      hNnormal hNelem hNcard_dvd hCcyc hdisj hjoin hP'leC
      hP'card hP'ne hNcyc'
    rcases hbase with ⟨hbaseN, hbaseEq, hbaseInf, hbaseSup, hbaseCard⟩
    have hcomp' : N₀.IsComplement'
        (Subgroup.normalizer (P' : Set H)) := by
      let : N₀.Normal := hbaseN
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · exact (disjoint_iff.mpr hbaseInf)
      · rw [← Subgroup.normal_mul N₀
          (Subgroup.normalizer (P' : Set H)), hbaseSup]
        rfl
    have hPback : P'.map (MulAut.conj g⁻¹).toMonoidHom =
        (P : Subgroup H) := by
      dsimp [P']
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hback := normalComplement_conj P' N₀ g⁻¹ hbaseN hcomp'
    refine Or.inl ⟨N₀.map (MulAut.conj g⁻¹).toMonoidHom,
      hback.1, ?_, ?_⟩
    · have hback' := hback.2
      change (N₀.map (MulAut.conj g⁻¹).toMonoidHom).IsComplement'
        (Subgroup.normalizer
          (P'.map (MulAut.conj g⁻¹).toMonoidHom : Set H)) at hback'
      rw [hPback] at hback'
      exact hback'
    · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hNcard_dvd
  · rcases hPSL with ⟨m, hm0, hmf, he⟩
    let L := GaloisField r m
    have hLcard : Nat.card L = r ^ m := GaloisField.card r m hm0
    have hrge : 3 ≤ r := by
      have hr2 := (Fact.out : Nat.Prime r).two_le
      have hrne2 : r ≠ 2 := by
        intro hr
        subst r
        exact hrodd.not_two_dvd_nat (by simp)
      omega
    have hmone : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hLge : 3 ≤ Nat.card L := by
      rw [hLcard]
      calc
        3 ≤ r := hrge
        _ = r ^ 1 := by simp
        _ ≤ r ^ m := Nat.pow_le_pow_right
          (Fact.out : Nat.Prime r).pos hmone
    by_cases hLgt : 3 < Nat.card L
    · let : Group.IsPerfect (PSL2 L) :=
        psl2_isPerfect_of_card_gt_three L hLgt
      have hperf : Group.IsPerfect H :=
        Group.IsPerfect.ofSurjective (f := he.some.symm.toMonoidHom)
          he.some.symm.surjective
      exact (normalizer_not_cyclic_of_perfect_of_prime_card hperf
        (P : Subgroup H) hPcard hSylowCyc hNcyc).elim
    · have hL3 : Nat.card L = 3 := by omega
      let : Fintype L := Fintype.ofFinite L
      have hL3' : Fintype.card L = 3 := by
        simpa [Nat.card_eq_fintype_card] using hL3
      let eL : ZMod 3 ≃+* L :=
        ZMod.ringEquivOfPrime L Nat.prime_three hL3'
      let eA4 : PSL2 L ≃* alternatingGroup (Fin 4) :=
        (psl2RingEquiv eL).symm.trans psl2_three_equiv_alternatingGroup
      let eHA4 : H ≃* alternatingGroup (Fin 4) := he.some.trans eA4
      let V : Subgroup H :=
        (alternatingGroup.kleinFour (Fin 4)).map eHA4.symm.toMonoidHom
      exact Or.inr ⟨V, isKleinFour_map_mulEquiv_cross
        (alternatingGroup.kleinFour (Fin 4))
        (alternatingGroup.kleinFour_isKleinFour (by simp)) eHA4.symm⟩
  · rcases hPGL with ⟨m, hm0, hmf, he⟩
    let L := GaloisField r m
    let : Field L := inferInstance
    let : Finite L := inferInstance
    let : Finite (PGL2 L) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk
        Matrix.ProjGenLinGroup.mk_surjective
    have hLcard : Nat.card L = r ^ m := GaloisField.card r m hm0
    have hLodd : IsOddPrimePower (Nat.card L) :=
      ⟨r, m, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr hm0, hLcard⟩
    have hLoddcard : Odd (Nat.card L) := by
      rw [hLcard]
      exact hrodd.pow
    have hLge : 3 ≤ Nat.card L := by
      have hrge : 3 ≤ r := by
        have hr2 := (Fact.out : Nat.Prime r).two_le
        have hrne2 : r ≠ 2 := by
          intro hr
          subst r
          exact hrodd.not_two_dvd_nat (by simp)
        omega
      have hmone : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      rw [hLcard]
      calc
        3 ≤ r := hrge
        _ = r ^ 1 := by simp
        _ ≤ r ^ m := Nat.pow_le_pow_right
          (Fact.out : Nat.Prime r).pos hmone
    by_cases hLgt : 3 < Nat.card L
    · let : Group.IsPerfect (PSL2 L) :=
        psl2_isPerfect_of_card_gt_three L hLgt
      let ePGL : H ≃* PGL2 L := he.some
      let J : Subgroup H :=
        (commutator (PGL2 L)).comap ePGL.toMonoidHom
      have hJnormal : J.Normal := by
        dsimp [J]
        exact Subgroup.Normal.comap (inferInstance :
          (commutator (PGL2 L)).Normal) ePGL.toMonoidHom
      have hJmap : J.map ePGL.toMonoidHom = commutator (PGL2 L) := by
        dsimp [J]
        rw [Subgroup.map_comap_eq]
        rw [ePGL.range_eq_top]
        simp
      let eComm : commutator (PGL2 L) ≃* PSL2 L :=
        (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
          L hLodd hLgt (MulEquiv.refl (PGL2 L))).some
      let eJ : J ≃* PSL2 L := by
        let eJmap : J ≃* J.map ePGL.toMonoidHom :=
          Subgroup.equivMapOfInjective J ePGL.toMonoidHom ePGL.injective
        exact eJmap.trans ((MulEquiv.subgroupCongr hJmap).trans eComm)
      have hJcard : Nat.card J =
          Nat.card L * (Nat.card L ^ 2 - 1) / 2 := by
        calc
          Nat.card J = Nat.card (PSL2 L) := Nat.card_congr eJ.toEquiv
          _ = Nat.card L * (Nat.card L ^ 2 - 1) / 2 :=
            psl2_card_formula L hLodd
      have hHcard : Nat.card H = Nat.card L * (Nat.card L ^ 2 - 1) := by
        calc
          Nat.card H = Nat.card (PGL2 L) := Nat.card_congr ePGL.toEquiv
          _ = Nat.card L * (Nat.card L ^ 2 - 1) := pgl2_card_formula L
      have hJindex : J.index = 2 := by
        have hAeven : 2 ∣ Nat.card L * (Nat.card L ^ 2 - 1) := by
          rcases hLoddcard with ⟨a, ha⟩
          refine ⟨Nat.card L * (2 * a * (a + 1)), ?_⟩
          rw [ha]
          have hsq : (2 * a + 1) ^ 2 = 4 * a * (a + 1) + 1 := by ring
          rw [hsq]
          have hsub : 4 * a * (a + 1) + 1 - 1 = 4 * a * (a + 1) := by omega
          rw [hsub]
          ring
        apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := J))
        calc
          Nat.card J * J.index = Nat.card H := J.card_mul_index
          _ = Nat.card J * 2 := by
            rw [hJcard, hHcard]
            rw [Nat.div_mul_cancel hAeven]
      have hPleJ : (P : Subgroup H) ≤ J := by
        exact odd_pgroup_le_normal_index_two hpodd J (P : Subgroup H)
          hJnormal hJindex P.isPGroup'
      have hNcycJ : IsCyclic
          (Subgroup.normalizer (P.subgroupOf J : Set J)) :=
        isCyclic_normalizer_subgroupOf J (P : Subgroup H) hPleJ hNcyc
      have hSylowCycJ : ∀ S : Sylow p J, IsCyclic S := by
        intro S
        let f : J →* PSL2MatrixGroup K := H.subtype.comp J.subtype
        obtain ⟨S', hSS'⟩ := (S.isPGroup').map f |>.exists_le_sylow
        have hScyc : IsCyclic S' := by
          exact psl2_sylow_isCyclic_of_coprime_field_card K hKcard hKseven
            p (by
              intro hp2
              subst p
              exact hpodd.not_two_dvd_nat (by simp)) hpcop S'
        have hmapcyc : IsCyclic ((S : Subgroup J).map f) := by
          let : IsCyclic S' := hScyc
          exact Subgroup.isCyclic_of_le hSS'
        let eS : (S : Subgroup J) ≃* ((S : Subgroup J).map f) :=
          Subgroup.equivMapOfInjective (S : Subgroup J) f
            (by intro a b hab; exact J.subtype_injective (H.subtype_injective hab))
        exact (MulEquiv.isCyclic eS).mpr hmapcyc
      have hperfJ : Group.IsPerfect J :=
        Group.IsPerfect.ofSurjective (f := eJ.symm.toMonoidHom)
          eJ.symm.surjective
      exact (normalizer_not_cyclic_of_perfect_of_prime_card hperfJ
        (P.subgroupOf J) (by
          calc
            Nat.card (P.subgroupOf J) =
                Nat.card ((P.subgroupOf J).map J.subtype) :=
              (Subgroup.card_map_of_injective J.subtype_injective).symm
            _ = Nat.card (P : Subgroup H) := by
              rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPleJ]
            _ = p := hPcard)
        hSylowCycJ hNcycJ).elim
    · have hL3 : Nat.card L = 3 := by omega
      let : Fintype L := Fintype.ofFinite L
      have hL3' : Fintype.card L = 3 := by
        simpa [Nat.card_eq_fintype_card] using hL3
      let eL : ZMod 3 ≃+* L :=
        ZMod.ringEquivOfPrime L Nat.prime_three hL3'
      let eS4 : PGL2 L ≃* Equiv.Perm (Fin 4) :=
        (pgl2RingEquiv eL).symm.trans pgl2_three_equiv_perm
      let eH : H ≃* Equiv.Perm (Fin 4) := he.some.trans eS4
      let K4 : Subgroup (alternatingGroup (Fin 4)) :=
        alternatingGroup.kleinFour (Fin 4)
      have hK4 : IsKleinFour K4 :=
        alternatingGroup.kleinFour_isKleinFour (by simp)
      let V4 : Subgroup (Equiv.Perm (Fin 4)) :=
        K4.map (alternatingGroup (Fin 4)).subtype
      have hV4 : IsKleinFour V4 :=
        isKleinFour_map_injective K4 hK4
          (alternatingGroup (Fin 4)).subtype
          (alternatingGroup (Fin 4)).subtype_injective
      let V : Subgroup H := V4.map eH.symm.toMonoidHom
      exact Or.inr ⟨V, isKleinFour_map_mulEquiv_cross V4 hV4 eH.symm⟩

end CFSG.GorensteinWalter

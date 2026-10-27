module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypesTools
import CFSG.RankThree.PartTwo.Sec17.G1724J2
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof155P

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank

private theorem center_nativeJ2_eq_bot :
    Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := by
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  have hxg : CFSG.RankThree.PartTwo.Sec17.G1724.xE *
      CFSG.RankThree.PartTwo.Sec17.G1724.gE ≠
      CFSG.RankThree.PartTwo.Sec17.G1724.gE *
        CFSG.RankThree.PartTwo.Sec17.G1724.xE := by
    intro h
    have h1 : CFSG.RankThree.PartTwo.Sec17.G1724.gE *
        CFSG.RankThree.PartTwo.Sec17.G1724.xE *
        CFSG.RankThree.PartTwo.Sec17.G1724.gE⁻¹ =
        CFSG.RankThree.PartTwo.Sec17.G1724.xE := by
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [CFSG.RankThree.PartTwo.Sec17.G1724.gE_conj_x] at h1
    have h3 : CFSG.RankThree.PartTwo.Sec17.G1724.xE ^ 3 = 1 := by
      calc
        CFSG.RankThree.PartTwo.Sec17.G1724.xE ^ 3 =
            CFSG.RankThree.PartTwo.Sec17.G1724.xE ^ 3 * 1 := (mul_one _).symm
        _ = CFSG.RankThree.PartTwo.Sec17.G1724.xE ^ 3 *
            (CFSG.RankThree.PartTwo.Sec17.G1724.xE *
              CFSG.RankThree.PartTwo.Sec17.G1724.xE⁻¹) := by rw [mul_inv_cancel]
        _ = (CFSG.RankThree.PartTwo.Sec17.G1724.xE ^ 3 *
            CFSG.RankThree.PartTwo.Sec17.G1724.xE) *
              CFSG.RankThree.PartTwo.Sec17.G1724.xE⁻¹ := by rw [mul_assoc]
        _ = CFSG.RankThree.PartTwo.Sec17.G1724.xE ^ 4 *
            CFSG.RankThree.PartTwo.Sec17.G1724.xE⁻¹ := by rw [← pow_succ]
        _ = CFSG.RankThree.PartTwo.Sec17.G1724.xE *
            CFSG.RankThree.PartTwo.Sec17.G1724.xE⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel _
    have hd3 : orderOf CFSG.RankThree.PartTwo.Sec17.G1724.xE ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr h3
    have hd5 : orderOf CFSG.RankThree.PartTwo.Sec17.G1724.xE ∣ 5 :=
      orderOf_dvd_iff_pow_eq_one.mpr
        (CFSG.RankThree.PartTwo.Sec17.G1724.xE_pow_five)
    have hd1 : orderOf CFSG.RankThree.PartTwo.Sec17.G1724.xE ∣ 1 := by
      have := Nat.dvd_gcd hd3 hd5
      rwa [show Nat.gcd 3 5 = 1 by norm_num] at this
    exact CFSG.RankThree.PartTwo.Sec17.G1724.xE_ne_one
      (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1))
  have hnc : ∃ a b : CFSG.Blueprint.NativeSporadic.J2, a * b ≠ b * a := by
    refine ⟨CFSG.ComponentClassification.J2Cover.nativeEquivP.symm
      CFSG.RankThree.PartTwo.Sec17.G1724.xE,
      CFSG.ComponentClassification.J2Cover.nativeEquivP.symm
        CFSG.RankThree.PartTwo.Sec17.G1724.gE, ?_⟩
    intro h
    apply hxg
    have := congrArg CFSG.ComponentClassification.J2Cover.nativeEquivP h
    simpa using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center CFSG.Blueprint.NativeSporadic.J2) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have ha : a ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.J2 := by
      rw [h]
      exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

private theorem card_alternatingGroup_five :
    Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem j2prod_facts
    {T : Type} [Group T] [Finite T]
    (e : T ≃* alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2)
    {V E : Subgroup T} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V)
    (hE : E.IsSubnormal) (hEp : Group.IsPerfect ↥E) (hE1 : E ≠ ⊥) (hVE : ⁅V, E⁆ = ⊥) :
    (2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥V) ∧ 5 ∣ Nat.card E) ∨
      (5 ∣ Nat.card V ∧ 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥E)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hJ2s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  haveI : Group.IsPerfect ↥E := hEp
  have hVne : V ≠ ⊥ := by
    intro h
    haveI : Nontrivial ↥V := CFSG.LocalCores.isQuasisimple_nontrivial hVq
    rw [h] at this
    obtain ⟨a, b, hab⟩ := this
    exact hab (Subsingleton.elim a b)
  have hV'ne : V.map e.toMonoidHom ≠ ⊥ := fun h =>
    hVne ((Subgroup.map_eq_bot_iff_of_injective V e.injective).mp h)
  have hE'ne : E.map e.toMonoidHom ≠ ⊥ := fun h =>
    hE1 ((Subgroup.map_eq_bot_iff_of_injective E e.injective).mp h)
  have hVsub' : (V.map e.toMonoidHom).IsSubnormal := hV.map e.surjective
  have hEsub' : (E.map e.toMonoidHom).IsSubnormal := hE.map e.surjective
  have hVq' : CFSG.IsQuasisimple ↥(V.map e.toMonoidHom) := by
    refine CFSG.LocalCores.isQuasisimple_map hVq e.toMonoidHom ?_
    rw [MonoidHom.ker_eq_bot e.toMonoidHom e.injective, le_bot_iff]
    exact hVne
  have hVp' : Group.IsPerfect ↥(V.map e.toMonoidHom) := hVq'.1
  have hEp' : Group.IsPerfect ↥(E.map e.toMonoidHom) :=
    Group.IsPerfect.map e.toMonoidHom
  have hVE' : ⁅V.map e.toMonoidHom, E.map e.toMonoidHom⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, hVE, Subgroup.map_bot]
  have hZ1 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hZ2 : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ :=
    center_nativeJ2_eq_bot
  rcases Proof153Twin2.pair_prod hZ1 hZ2 hVsub' hEsub' hVp' hEp' hV'ne hE'ne hVE' with
    ⟨⟨eVA5⟩, ⟨eEJ2⟩⟩ | ⟨⟨eVJ2⟩, ⟨eEA5⟩⟩
  · right
    have hcardV : Nat.card ↥V = 60 := by
      rw [← Subgroup.card_map_of_injective (K := V) (f := e.toMonoidHom) e.injective,
        Nat.card_congr eVA5.toEquiv, card_alternatingGroup_five]
    refine ⟨?_, ?_⟩
    · rw [hcardV]; norm_num
    · have h1 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥E) =
          CFSG.Open.pRank 5 (⊤ : Subgroup ↥(E.map e.toMonoidHom)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
          (Subgroup.equivMapOfInjective E e.toMonoidHom e.injective)
      have h2 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥(E.map e.toMonoidHom)) =
          CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.J2) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) eEJ2
      rw [h1, h2]
      exact CFSG.RankThree.PartTwo.Sec17.G1724.two_le_pRank_five_J2
  · left
    have hcardE : Nat.card ↥E = 60 := by
      rw [← Subgroup.card_map_of_injective (K := E) (f := e.toMonoidHom) e.injective,
        Nat.card_congr eEA5.toEquiv, card_alternatingGroup_five]
    refine ⟨?_, ?_⟩
    · have h1 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥V) =
          CFSG.Open.pRank 5 (⊤ : Subgroup ↥(V.map e.toMonoidHom)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
          (Subgroup.equivMapOfInjective V e.toMonoidHom e.injective)
      have h2 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥(V.map e.toMonoidHom)) =
          CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.J2) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) eVJ2
      rw [h1, h2]
      exact CFSG.RankThree.PartTwo.Sec17.G1724.two_le_pRank_five_J2
    · rw [hcardE]; norm_num

theorem aschbacherSolvableCore_le_pCore_two {W : Type} [Group W] [Finite W]
    (hq : CFSG.IsQuasisimple (W ⧸ CFSG.pCore 2 W))
    (hp : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 2 ∣ Nat.card (W ⧸ aschbacherSolvableCore 3 W)) :
    aschbacherSolvableCore 3 W ≤ CFSG.pCore 2 W := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 2 W with hO
  set θ := aschbacherSolvableCore 3 W with hθ
  obtain ⟨hθsol, hθchar, hθ3, hmax, -, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := W) Nat.prime_three
  have hO2 : IsPGroup 2 ↥O := CFSG.pCore_isPGroup
  have hOsol : Group.IsSolvable ↥O := @IsNilpotent.to_isSolvable _ _ hO2.isNilpotent
  have hO3 : ¬ 3 ∣ Nat.card ↥O := by
    intro h3
    obtain ⟨n, hn⟩ := hO2.exists_card_eq
    rw [hn] at h3
    exact (by norm_num : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3)
  have hOleθ : O ≤ θ := hmax O CFSG.pCore_normal hOsol hO3
  set K := W ⧸ O with hK
  set Z : Subgroup K := θ.map (QuotientGroup.mk' O) with hZ
  have hqK : CFSG.IsQuasisimple K := hq
  have hKperf : Group.IsPerfect K := hqK.1
  haveI : Group.IsPerfect K := hKperf
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hqK
  have hθn : θ.Normal := Subgroup.normal_of_characteristic θ
  have hZn : Z.Normal := hθn.map (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  haveI : Z.Normal := hZn
  have hZcard : Nat.card ↥Z ∣ Nat.card ↥θ :=
    Subgroup.card_map_dvd θ (QuotientGroup.mk' O)
  have hZcenter : Z ≤ Subgroup.center K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqK hZn with hZtop | hZc
    · exfalso
      let φ : ↥θ →* ↥Z := ((QuotientGroup.mk' O).comp θ.subtype).codRestrict Z
        (fun x => Subgroup.mem_map_of_mem _ x.2)
      have hφsurj : Function.Surjective φ := by
        intro z
        obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp z.2
        refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
        exact hxz
      have hZsol : Group.IsSolvable ↥Z := Group.isSolvable_of_surjective hφsurj
      have hKsol : Group.IsSolvable K := by
        have htop : Group.IsSolvable ↥(⊤ : Subgroup K) := by
          rw [← hZtop]
          exact hZsol
        let e : ↥(⊤ : Subgroup K) ≃* K := Subgroup.topEquiv
        exact Group.isSolvable_of_surjective (G := ↥(⊤ : Subgroup K)) (G' := K)
          (f := e) e.surjective
      exact Group.IsPerfect.not_isSolvable K hKsol
    · exact hZc
  have hZ2 : IsPGroup 2 ↥Z :=
    CFSG.RankThree.PartTwo.Sec14.HJRes148.isPGroup_two_of_central hZcenter (by
      intro p hpprime hp2 hpZ
      have hpθ : p ∣ Nat.card ↥θ := hpZ.trans hZcard
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact hθ3 hpθ
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with hlt | hge
        · have hp2le : 2 ≤ p := hpprime.two_le
          interval_cases p
          · exact (hp2 rfl).elim
          · exact (hp3 rfl).elim
          · norm_num at hpprime
        · exact hge
      have hdvd := hp p hpprime hp5
      intro h
      apply hdvd
      have hiso : (K ⧸ Z) ≃* (W ⧸ θ) :=
        QuotientGroup.quotientQuotientEquivQuotient O θ hOleθ
      rwa [Nat.card_congr hiso.toEquiv] at h)
  have hθ2 : IsPGroup 2 ↥θ := by
    intro x
    have hxZ : (QuotientGroup.mk' O) (x : W) ∈ Z :=
      Subgroup.mem_map_of_mem _ x.2
    obtain ⟨k, hk⟩ := hZ2 ⟨(QuotientGroup.mk' O) (x : W), hxZ⟩
    have hxpowO : (x : W) ^ 2 ^ k ∈ O := by
      have h := congrArg Subtype.val hk
      have h' : (QuotientGroup.mk' O) ((x : W) ^ 2 ^ k) = 1 := by
        simpa [map_pow] using h
      exact (QuotientGroup.eq_one_iff _).mp h'
    obtain ⟨l, hl⟩ := (CFSG.pCore_isPGroup (p := 2) (G := W))
      ⟨(x : W) ^ 2 ^ k, hxpowO⟩
    refine ⟨k + l, Subtype.ext ?_⟩
    have hExp : (x : W) ^ 2 ^ (k + l) = 1 := by
      rw [pow_add, pow_mul]
      exact congrArg Subtype.val hl
    simpa using hExp
  have hθle : θ ≤ CFSG.pCore 2 W := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le θ (le_iSup_of_le hθn (le_iSup_of_le hθ2 le_rfl))
  simpa [hO] using hθle

end CFSG.RankThree.PartTwo.Sec15.Proof155P

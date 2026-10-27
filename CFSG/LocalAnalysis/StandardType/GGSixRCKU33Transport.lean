module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


section Transport

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup map_fixSubgroup_le
  normal_map_fixSubgroup)

theorem not_le_of_le_center {K : Type*} [Group K] {J N : Subgroup K}
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hN : N ≤ Subgroup.center K) : ¬ J ≤ N := by
  intro hle
  obtain ⟨hperf, hs⟩ := hJ
  have hab : ∀ a b : ↥J, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hN (hle a.2)) b).symm
  have hbot : commutator ↥J = ⊥ := by
    rw [eq_bot_iff, commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hab a b
  have htop : (⊤ : Subgroup ↥J) = ⊥ := hperf ▸ hbot
  haveI := hs
  obtain ⟨q, hq⟩ := exists_ne (1 : ↥J ⧸ Subgroup.center ↥J)
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) q
  have : j = 1 := by
    have hj : j ∈ (⊤ : Subgroup ↥J) := Subgroup.mem_top j
    rw [htop] at hj
    exact hj
  exact hq (by rw [this, map_one])

theorem nonempty_centerQuot_map {K Q : Type*} [Group K] [Group Q] (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) {J : Subgroup K} (hJ : Group.IsPerfect ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) := by
  let f : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hf : Function.Surjective f := π.subgroupMap_surjective J
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro g
    have hj' : (j : K) ∈ π.ker :=
      MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hj))
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hj') g)
  have hc := CFSG.LocalCores.comap_center_eq_of_perfect hJ f hf hfker
  have hc' : Subgroup.center ↥J =
      ((QuotientGroup.mk' (Subgroup.center ↥(J.map π))).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hc.symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc').trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem u33_isComponentOf_map_fixSubgroup {K Q : Type*} [Group K] [Group Q] (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
    (hαβ : ∀ k, π (α k) = β (π k)) (hπ : Function.Surjective π) {J : Subgroup K}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup α)) :
    CFSG.Open.IsComponentOf (J.map π) (fixSubgroup β) := by
  have hle := map_fixSubgroup_le π hker α β hαβ
  have hn := normal_map_fixSubgroup π hker α β hαβ hπ
  refine ⟨(Subgroup.map_mono hJ.1).trans hle, ?_, ?_⟩
  · exact (hJ.2.1.map π).trans (CFSG.Open.IsSubnormal.step hle hn (CFSG.Open.IsSubnormal.refl _))
  · obtain ⟨hperf, hs⟩ := hJ.2.2
    haveI : Group.IsPerfect ↥J := ⟨hperf⟩
    obtain ⟨e⟩ := nonempty_centerQuot_map π hker (J := J) ‹_›
    refine ⟨?_, ?_⟩
    · have hP : Group.IsPerfect ↥(J.map π) :=
        Group.IsPerfect.ofSurjective (f := π.subgroupMap J) (π.subgroupMap_surjective J)
      exact hP.commutator_eq_top
    · haveI := hs
      exact e.symm.isSimpleGroup

end Transport


section Component

open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem exists_sLevel_of_component {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ]
    {L K A : Subgroup Γ} {y : Γ} (hLq : CFSG.Open.IsQuasisimple ↥L) (hAel : IsElemAbelian p A)
    (hInn : S10.InnDiagOn p A L) (hyA : y ∈ A) (hyC : ¬ CentMod p L y)
    (hK : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ))) :
    ∃ (labL : GLALabel) (β : MulAut (PSimple p L)) (J : Subgroup (PSimple p L)),
      HasLabel (PQuot p L) (· = labL) ∧
      Subgroup.center (PSimple p L) = ⊥ ∧
      InnDiagKind (PSimple p L) labL β ∧
      β ^ p = 1 ∧ β ≠ 1 ∧ CFSG.Open.IsComponentOf J (fixSubgroup β) ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* ↥J ⧸ Subgroup.center ↥J) := by
  have hyN : y ∈ Subgroup.normalizer (L : Set Γ) := hInn.1 hyA
  have hyp : y ^ p = 1 := hAel.2 y hyA
  have hInnZ : S10.InnDiagOn p (Subgroup.zpowers y) L := by
    refine ⟨fun z hz => hInn.1 (Subgroup.zpowers_le.mpr hyA hz), ?_⟩
    exact CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ hP a ha => hP a (Subgroup.zpowers_le.mpr hyA ha)) hInn.2
  have hlabAll : HasLabel (PQuot p L) (fun _ => True) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ _ => trivial) hInn.2
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := hasLabel_isQuasisimple hlabAll
  obtain ⟨labL, hlab, hin⟩ := innDiagKind_chevAut hyN hq hInnZ
  have hcen : Subgroup.center (PSimple p L) = ⊥ := center_centerQuot_eq_bot hq
  have hβp : chevAut p L ⟨y, hyN⟩ ^ p = 1 := chevAut_pow_eq_one p L hyN hyp
  have hβ1 : chevAut p L ⟨y, hyN⟩ ≠ 1 := by
    intro h1
    exact hyC ((chevAut_eq_one_iff_of_quasisimple hq hyN).1 h1)
  have hne : (chevQuotHom p L).ker ≠ ⊤ := by
    intro htop
    haveI : IsSimpleGroup (PSimple p L) := hq.2
    obtain ⟨s, hs⟩ := exists_ne (1 : PSimple p L)
    obtain ⟨l, rfl⟩ := chevQuotHom_surjective p L s
    exact hs (MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top l))
  have hLq' : CFSG.IsQuasisimple ↥L :=
    ⟨⟨hLq.1⟩, hLq.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLq⟩
  have hker : (chevQuotHom p L).ker ≤ Subgroup.center ↥L :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hLq'
      (chevQuotHom p L).normal_ker).resolve_left hne
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨y, hyN⟩ with hα
  have hαβ : ∀ k, chevQuotHom p L (α k) = chevAut p L ⟨y, hyN⟩ (chevQuotHom p L k) :=
    fun k => (chevAut_chevQuotHom p L ⟨y, hyN⟩ k).symm
  have hKL : K ≤ L := hK.1.trans inf_le_left
  have hK' : CFSG.Open.IsComponentOf (K.subgroupOf L) (fixSubgroup α) := by
    rw [hα, fixSubgroup_normalizerMonoidHom hyN]
    exact ⟨fun x hx => hK.1 hx, hK.2.1.comap L.subtype,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL) hK.2.2⟩
  have hJ := u33_isComponentOf_map_fixSubgroup (chevQuotHom p L) hker α (chevAut p L ⟨y, hyN⟩) hαβ
    (chevQuotHom_surjective p L) hK'
  haveI : Group.IsPerfect ↥(K.subgroupOf L) := ⟨hK'.2.2.1⟩
  obtain ⟨e₂⟩ := nonempty_centerQuot_map (chevQuotHom p L) hker (J := K.subgroupOf L) ‹_›
  let g : ↥(K.subgroupOf L) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
  have e₁ : ↥K ⧸ Subgroup.center ↥K ≃* ↥(K.subgroupOf L) ⧸ Subgroup.center ↥(K.subgroupOf L) :=
    QuotientGroup.congr _ _ g.symm (Subgroup.map_center_eq g.symm)
  exact ⟨labL, chevAut p L ⟨y, hyN⟩, (K.subgroupOf L).map (chevQuotHom p L), hlab, hcen, hin,
    hβp, hβ1, hJ, ⟨e₁.trans e₂⟩⟩

private abbrev u33RankSmall : TauCeti.CFSGIndex → Prop :=
  fun i => rsG2Char2 i ∨ rsU3 i ∨ rsAlt 5 i ∨ rsAlt 6 i ∨ rsAlt 8 i ∨ rsL27 i ∨ rsTits i

private lemma g2Char2_or_u3_le_u33RankSmall {i : TauCeti.CFSGIndex}
    (h : rsG2Char2 i ∨ rsU3 i) : u33RankSmall i := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

private lemma tits_le_u33RankSmall {i : TauCeti.CFSGIndex} (h : rsTits i) : u33RankSmall i :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

private lemma ambiguousChev_lie_A_ge {k : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A k q).Valid) (hk : 2 ≤ k) :
    ambiguousChev 2 (.lie ⟨TauCeti.LieTypeIndex.A k q, hv⟩) = False := by
  simp only [ambiguousChev]
  split <;> simp_all

private lemma ambiguousChev_lie_twistedA_ge {k : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA k q).Valid) (hk : 3 ≤ k) :
    ambiguousChev 2 (.lie ⟨TauCeti.LieTypeIndex.twistedA k q, hv⟩) = False := by
  simp only [ambiguousChev]
  split <;> simp_all

private lemma ambiguous_le_u33RankSmall {i : TauCeti.CFSGIndex}
    (h : ambiguousChev 2 i) : u33RankSmall i := by
  cases i with
  | cyclic p hp => simp_all [ambiguousChev]
  | sporadic s => simp_all [ambiguousChev]
  | alternating n hn =>
      simp_all [ambiguousChev, u33RankSmall, rsG2Char2, rsG2Odd, rsU3, rsAlt, rsL27, rsTits, onLie]
  | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | A r q =>
          rcases r with _ | _ | _ | r
          · simp_all [ambiguousChev, u33RankSmall, rsG2Char2, rsG2Odd, rsU3, rsAlt, rsL27,
              rsTits, onLie, TauCeti.PrimePower.card_def]
          · simp_all [ambiguousChev, u33RankSmall, rsG2Char2, rsG2Odd, rsU3, rsAlt, rsL27,
              rsTits, onLie, TauCeti.PrimePower.card_def]
          · simp_all [ambiguousChev, u33RankSmall, rsG2Char2, rsG2Odd, rsU3, rsAlt, rsL27,
              rsTits, onLie, TauCeti.PrimePower.card_def]
          · rw [ambiguousChev_lie_A_ge hv (by omega)] at h
            exact absurd h (by simp)
      | twistedA r q =>
          rcases r with _ | _ | _ | r
          · simp_all [ambiguousChev, u33RankSmall, rsG2Char2, rsG2Odd, rsU3, rsAlt, rsL27,
              rsTits, onLie, TauCeti.PrimePower.card_def]
          · simp_all [ambiguousChev, u33RankSmall, rsG2Char2, rsG2Odd, rsU3, rsAlt, rsL27,
              rsTits, onLie, TauCeti.PrimePower.card_def]
          · simp_all [ambiguousChev, u33RankSmall, rsG2Char2, rsG2Odd, rsU3, rsAlt, rsL27,
              rsTits, onLie, TauCeti.PrimePower.card_def]
          · rw [ambiguousChev_lie_twistedA_ge hv (by omega)] at h
            exact absurd h (by simp)
      | _ =>
          simp_all [ambiguousChev, u33RankSmall, rsG2Char2, rsG2Odd, rsU3, rsAlt, rsL27,
            rsTits, onLie, TauCeti.PrimePower.card_def]

private theorem catalogIs_tits_of_char2 {S : Type} [Group S]
    (h : catalogIs S (onLie fun d => d.characteristic = 2))
    (ht : ¬ catalogIs S isLie2NoTits) : catalogIs S rsTits := by
  obtain ⟨i, hi, e⟩ := h
  cases i with
  | lie d =>
      by_cases htits : d.1 = TauCeti.LieTypeIndex.tits
      · exact ⟨.lie d, htits, e⟩
      · exact absurd ⟨.lie d, ⟨hi, htits⟩, e⟩ ht
  | _ => exact absurd hi (by simp [onLie])

private theorem catalogIs_g2Char2_or_u3_of_hasLabel_G2
    {X : Type} [Group X] {lab : GLALabel}
    (h : HasLabel X (· = lab)) (ht : lab.tag = .G2) :
    catalogIs (X ⧸ Subgroup.center X) (fun i => rsG2Char2 i ∨ rsU3 i) := by
  obtain ⟨t, r, n⟩ := lab
  simp only at ht
  subst ht
  have hlam := lambda2_of_hasLabel h
  obtain ⟨-, rfl, hn2⟩ := hlam
  have hM := markedModel_of_hasLabel h
  have hLM : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .G2 0 2 n := hM
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 2 n :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  obtain ⟨hadm, hm⟩ := hce
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eK⟩⟩ := hm
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn2
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, hn0⟩
  have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · simpa [TauCeti.LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K (by rw [hKcard, hq])
  exact ⟨.lie ⟨.G2 q, hv⟩, by left; rfl, ⟨eK.trans b⟩⟩

theorem i141DynkinAt_card_comp
    {G : Type} [Group G] [Finite G] {p : ℕ} {L K A : Subgroup G} {y : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hchev : IsChevSimple 2 (PSimple p L))
    (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hAel : IsElemAbelian p A) (hInn : S10.InnDiagOn p A L)
    (hrank : p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p L) ≤ Nat.card A) (hyA : y ∈ A)
    (hyC : ¬ CentMod p L y)
    (hK : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set G))) :
    Nat.card (↥K ⧸ Subgroup.center ↥K) ≠ 6048 := by
  intro hcard
  have hQ : catalogIs (PSimple p L) u33RankSmall := by
    rcases hchev with h | h
    · by_cases ht : catalogIs (PSimple p L) isLie2NoTits
      · obtain ⟨labL, β, J, hlab, hcen, hin, hβp, hβ1, hJ, hKiso⟩ :=
          exists_sLevel_of_component hLq hAel hInn hyA hyC hK
        have hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 6048 := by
          rw [← Nat.card_congr hKiso.some.toEquiv]
          exact hcard
        exact S10.catalogIs_imp (fun i hi => g2Char2_or_u3_le_u33RankSmall hi)
          (catalogIs_g2Char2_or_u3_of_hasLabel_G2 hlab
            (tag_eq_G2_of_compTypeLie2 compTypeLie2_holds hp hp2 hcen hin hβp hβ1 hJ hJc))
      · exact S10.catalogIs_imp (fun i hi => tits_le_u33RankSmall hi)
          (catalogIs_tits_of_char2 h ht)
    · exact S10.catalogIs_imp (fun i hi => ambiguous_le_u33RankSmall hi) h
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h | h | h | h | h | h
  · exact i141RankG2Char2_holds p hp hp2 G L A ⟨i, h, e⟩ hAel hInn hrank
  · exact i141RankU3_holds p hp hp2 G L A ⟨i, h, e⟩ hAel hInn hrank
  · exact i141RankA5_holds p hp hp2 G L A ⟨i, h, e⟩ hAel hInn hrank
  · exact i141RankA6_holds p hp hp2 G L A ⟨i, h, e⟩ hAel hInn hrank
  · exact i141RankA8_holds p hp hp2 G L A ⟨i, h, e⟩ hAel hInn hrank
  · exact i141RankL27_holds p hp hp2 G L A ⟨i, h, e⟩ hAel hInn hrank
  · exact i141RankTits_holds p hp hp2 G L A ⟨i, h, e⟩ hAel hInn hrank


end Component

end CFSG.LocalAnalysis.GLTheoremA.I141F

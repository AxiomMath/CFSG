module

public import CFSG.RankThree.PartTwo.Sec17.Item1729
public import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec13.Naturality

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Assembly

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem case7_of_mem (h131 : Item131) (hspor : SporadicModels131) (h : Sec13Data G A c L)
    (hcL : c ∈ L) :
    (Sec4.IsSLThreePiTwo (lBarA c L A) ∨
        (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
          (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
            Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
            Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L)
              CFSG.Blueprint.NativeSporadic.M22))) ∧
      (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) →
          Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
      ∀ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) →
        CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
        ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) →
        ¬ IsCyclic (E ⊓ L : Subgroup G) →
          E ∈ partTwoF G ∧ (E ∉ partTwoT G →
            Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
            (∃ K ∈ thetaComponentsAt 3 c, A ≤ L ⊔ K ∧
              Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
            ∃ e ∈ E ⊓ L, e ∉ Subgroup.zpowers c ∧
              omegaA E = orbitIn A (Subgroup.zpowers e) ∧
              ∃ I : Subgroup G, lA E e = {I} ∧
                Nonempty (I ⧸ CFSG.pCore 2 I ≃* CFSG.Blueprint.NativeSporadic.J2)) := by
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
  rcases h131 G A c L h with ⟨hL3, -⟩ | ⟨hPGL, -, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | h7
  · exfalso
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hS, hZ⟩ := isPerfect_center_projSL p e he hq
      exact (facts_of_prod h hS hZ φ).1 hcL
    · by_cases hq2 : 2 < p ^ e
      · obtain ⟨hS, hZ⟩ := isPerfect_center_projSU p e he hq hq2
        exact (facts_of_prod h hS hZ φ).1 hcL
      · have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable h isSolvable_projSU_two φ
  · exfalso
    obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
    by_cases hq2 : 2 < p ^ f
    · exact not_mem_of_center_inf_commutator h φ
        (by rw [center_projImage_glPi hK hq hq2, bot_inf_eq]) hcL
    · have h2 : p ^ f = 2 := by
        have hf : f ≠ 0 := by have := hK.one_le; omega
        have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
        omega
      cases π
      · exact false_of_isSolvable h (isSolvable_projImage_glPi_two hK h2) φ
      · change p ^ f % 3 = 1 at hq
        omega
  · exact absurd hcL (facts_of_prod h isPerfect_center_alt7.1 isPerfect_center_alt7.2 φ).1
  · exact absurd hcL (facts_of_prod h hM22p hM22z φ).1
  · exact absurd hcL (facts_of_prod h hM12p hM12z φ).1
  · exact absurd hcL (facts_of_prod h hJ2p hJ2z φ).1
  · exact h7

theorem theta_eq_pCore_two {I : Type*} [Group I] [Finite I] {S : Type*} [Group S]
    (hS : IsSimpleGroup S) (hSp : Group.IsPerfect S) (φ : I ⧸ CFSG.pCore 2 I ≃* S) :
    aschbacherSolvableCore 3 I = CFSG.pCore 2 I := by
  have : (CFSG.pCore 2 I).Normal := CFSG.pCore_normal
  have hθ := solvable_prime_complement_core_characterization (H := I) Nat.prime_three
  apply le_antisymm
  · set f := QuotientGroup.mk' (CFSG.pCore 2 I) with hf
    set N := (aschbacherSolvableCore 3 I).map f with hN
    have : (aschbacherSolvableCore 3 I).Normal := by
      have := hθ.2.1
      infer_instance
    have hNn : N.Normal := Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
    have hθs := hθ.1
    have hNs : Group.IsSolvable N :=
      Group.isSolvable_of_surjective (f.subgroupMap_surjective (aschbacherSolvableCore 3 I))
    have hφN : (N.map φ.toMonoidHom).Normal := Subgroup.Normal.map hNn _ φ.surjective
    rcases hS.eq_bot_or_eq_top_of_normal (N.map φ.toMonoidHom) with hb | ht
    · have hN' : N = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hb
      intro x hx
      have h1 : f x ∈ N := Subgroup.mem_map_of_mem f hx
      rw [hN', Subgroup.mem_bot, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      have h1 : Group.IsSolvable (N.map φ.toMonoidHom) :=
        Group.isSolvable_of_surjective (φ.toMonoidHom.subgroupMap_surjective N)
      rw [ht] at h1
      have : Group.IsSolvable S :=
        Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S) : (⊤ : Subgroup S) →* S))
          Subgroup.topEquiv.surjective
      have : Nontrivial S := hS.toNontrivial
      exact Group.IsPerfect.not_isSolvable S inferInstance
  · exact hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num)

theorem chosen136_of_forall_not_mem (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (hD : Sec13Data G A c L)
    (hgood : ∀ c' : G, Subgroup.zpowers c' ∈ omegaA A → ∀ L' ∈ lA A c', c' ∉ L') :
    Chosen136 A := by
  refine ⟨hD.mem_partTwoF, fun c' hc' L' hL' => ?_⟩
  have hD' : Sec13Data G A c' L' :=
    { hD.toPartTwoStanding with
      partTwoS_eq := hD.partTwoS_eq, mem_partTwoF := hD.mem_partTwoF,
      not_mem_partTwoT := hD.not_mem_partTwoT, zpowers_mem_omegaA := hc', mem_lA := hL' }
  exact ⟨(facts_of_not_mem h131 hspor hSLC hD' (hgood c' hc' L' hL')).1,
    moreover_of_not_mem h131 hspor hSLC hD' (hgood c' hc' L' hL')⟩

theorem rank3II_13_6_of_inputs (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) :
    Sec17.Item136 := by
  intro G _ _ A c L hD hST
  by_cases hgood : ∀ c' : G, Subgroup.zpowers c' ∈ omegaA A → ∀ L' ∈ lA A c', c' ∉ L'
  · exact ⟨A, chosen136_of_forall_not_mem h131 hspor hSLC hD hgood⟩
  push Not at hgood
  obtain ⟨c', hc', L', hL', hcL'⟩ := hgood
  have hT : HypT A := hST.resolve_left fun hS => hS.2.2 c' hc' L' hL' hcL'
  have hD' : Sec13Data G A c' L' :=
    { hD.toPartTwoStanding with
      partTwoS_eq := hD.partTwoS_eq, mem_partTwoF := hD.mem_partTwoF,
      not_mem_partTwoT := hD.not_mem_partTwoT, zpowers_mem_omegaA := hc', mem_lA := hL' }
  obtain ⟨h7, -, hEcl⟩ := case7_of_mem h131 hspor hD' hcL'
  obtain ⟨U, hzU, hU9, hU3, hUΛ, hUΛz, hAbU⟩ : ∃ U : Subgroup (lBarA c' L' A),
      mkC (L := L') hD'.mem_A ∈ U ∧ 9 ≤ Nat.card U ∧ (∀ x ∈ U, x ^ 3 = 1) ∧
      (∀ u ∈ U, ∀ l ∈ (Sec12.lBar c' L').subgroupOf (lBarA c' L' A), u * l = l * u) ∧
      (∀ u ∈ U, u ∈ (Sec12.lBar c' L').subgroupOf (lBarA c' L' A) →
        u ∈ Subgroup.zpowers (mkC (L := L') hD'.mem_A)) ∧
      (∀ a ∈ (aBarHom hD').range, ∀ u ∈ U,
        a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers (mkC (L := L') hD'.mem_A)) := by
    rcases h7 with hSL | ⟨hH, hlist⟩
    · exact exists_U_of_isSLThreePiTwo hD' hcL' hSL
    · have hZ3 : Nat.card (Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L')) = 3 := by
        rcases hlist with h | h | h
        · exact card_center_of_isSLThreePi h
        · exact h.1
        · exact h.1
      exact exists_U_of_isHeisCentral hD' hcL' hH hZ3
  obtain ⟨E, hEle, hEab, hE27, hEθ, hEL, hAE⟩ :=
    exists_E_of_U hD' hcL' hzU hU9 hU3 hUΛ hUΛz hAbU
  obtain ⟨hEF, hEcl'⟩ := hEcl E hEle hEab hE27 hEθ hEL
  have hEC : E ≤ Subgroup.centralizer ({c'} : Set G) :=
    hEle.trans (inf_le_left.trans (sup_le hD'.le_centralizer hD'.A_le_centralizer))
  have hET : E ∉ partTwoT G := fun hET => by
    have h1 := hT.2.2 c' hc'
    rw [Set.eq_empty_iff_forall_notMem] at h1
    exact h1 E ⟨hET, hEC⟩
  obtain ⟨-, -, e, -, -, hΩ, I, hI, ⟨φI⟩⟩ := hEcl' hET
  refine ⟨E, hEF, fun e' he' L'' hL'' => ?_⟩
  have he'Ω := he'
  rw [hΩ] at he'
  obtain ⟨a, ha, hae⟩ := he'
  have hz : Subgroup.zpowers e' = Subgroup.zpowers (a * e * a⁻¹) := by
    rw [hae, MonoidHom.map_zpowers]
    rfl
  have hL''a := hL''
  rw [lA_congr hz] at hL''a
  have haN : a ∈ Subgroup.normalizer (E : Set G) := hAE ha
  have hL''eq : L'' = I.map (MulAut.conj a).toMonoidHom := by
    have h1 : L''.map (MulAut.conj a⁻¹).toMonoidHom ∈ lA E (a⁻¹ * (a * e * a⁻¹) * a⁻¹⁻¹) :=
      (map_conj_mem_lA_iff (Subgroup.inv_mem _ haN)).mpr hL''a
    have h2 : a⁻¹ * (a * e * a⁻¹) * a⁻¹⁻¹ = e := by group
    rw [h2, hI, Set.mem_singleton_iff] at h1
    rw [← h1, Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  subst hL''eq
  have hD'' : Sec13Data G E e' (I.map (MulAut.conj a).toMonoidHom) :=
    { hD.toPartTwoStanding with
      partTwoS_eq := hD.partTwoS_eq, mem_partTwoF := hEF, not_mem_partTwoT := hET,
      zpowers_mem_omegaA := he'Ω, mem_lA := hL'' }
  have hθI := theta_eq_pCore_two hJ2 hspor.2.2.1 φI
  have hZI : Subgroup.center (I ⧸ aschbacherSolvableCore 3 I) = ⊥ :=
    center_eq_bot_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hθI).trans φI) hspor.2.2.2
  set eI := I.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective
  have hZ : Subgroup.center (I.map (MulAut.conj a).toMonoidHom ⧸
      aschbacherSolvableCore 3 (I.map (MulAut.conj a).toMonoidHom)) = ⊥ :=
    center_eq_bot_of_mulEquiv (QuotientGroup.congr _ _ eI
      (aschbacherSolvableCore_map_mulEquiv Nat.prime_three eI)).symm hZI
  have he'L := not_mem_of_center_eq_bot hD'' hZ
  exact ⟨(facts_of_not_mem h131 hspor hSLC hD'' he'L).1,
    moreover_of_not_mem h131 hspor hSLC hD'' he'L⟩

end Assembly

end CFSG.RankThree.PartTwo.Sec13

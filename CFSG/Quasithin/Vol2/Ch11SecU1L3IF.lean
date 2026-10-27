module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IE
public import CFSG.Quasithin.EmptyFaithful.E22PL2PglB
public import CFSG.Goldschmidt.Steps.Sec87d
public import CFSG.Quasithin.EmptyFaithful.E22PL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_normal
  pslRange_index_eq_two)

theorem mem_normalizer_of_subgroupOf {G : Type*} [Group G] {J V : Subgroup G} (hVJ : V ≤ J)
    {n : ↥J} (hn : n ∈ Subgroup.normalizer ((V.subgroupOf J : Subgroup ↥J) : Set ↥J)) :
    (n : G) ∈ Subgroup.normalizer (V : Set G) := by
  have hn' := Subgroup.mem_normalizer_iff.mp hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Subgroup.mem_subgroupOf.mp ((hn' ⟨x, hVJ hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx))
  · intro hx
    have hxJ : x ∈ J := by
      have h2 : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) ∈ J :=
        J.mul_mem (J.mul_mem (J.inv_mem n.2) (hVJ hx)) n.2
      simpa [mul_assoc] using h2
    have h3 : (⟨x, hxJ⟩ : ↥J) ∈ V.subgroupOf J := by
      rw [hn' ⟨x, hxJ⟩]
      exact Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp h3

theorem isSolvable_normalizer_of_kleinFour {G : Type} [Group G] {V : Subgroup G}
    (hV : IsKleinFour ↥V) (hcent : Subgroup.centralizer (V : Set G) = V) :
    Group.IsSolvable ↥(Subgroup.normalizer (V : Set G)) := by
  set N := Subgroup.normalizer (V : Set G) with hN
  have : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV.card_four]; norm_num)
  let f : ↥(V.subgroupOf N) →* ↥N := (V.subgroupOf N).subtype
  let g : ↥N →* Equiv.Perm ↥V := (MulAut.toPerm ↥V).comp V.normalizerMonoidHom
  have hker : g.ker ≤ f.range := by
    intro n hn
    have hc : (n : G) ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun σ : Equiv.Perm ↥V => ((σ ⟨y, hy⟩ : ↥V) : G))
        (MonoidHom.mem_ker.mp hn)
      have h2 : ((V.normalizerMonoidHom n ⟨y, hy⟩ : ↥V) : G) = y := h1
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      calc y * n = ((n : G) * y * (n : G)⁻¹) * n := by rw [h2]
        _ = n * y := by group
    rw [hcent] at hc
    exact ⟨⟨n, Subgroup.mem_subgroupOf.mpr hc⟩, rfl⟩
  have hab : Group.IsSolvable ↥(V.subgroupOf N) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (kleinFour_comm hV (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2)))
  have hperm : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable (by rw [hV.card_four])
  exact Group.isSolvable_of_ker_le_range f g hker

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem pgl2_centralizer_inner_involution_isCoatom_pm_three
    (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hp11 : 11 ≤ p) {z : PGL2 K}
    (hz : orderOf z = 2) (hzJ : z ∈ commutator (PGL2 K)) :
    IsCoatom (Subgroup.centralizer ({z} : Set (PGL2 K))) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  have hodd : IsOddPrimePower (Nat.card K) :=
    CFSG.Walter.isOddPrimePower_of_card hK1 hpodd one_pos
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three K hodd (by omega)
  obtain ⟨w, rfl⟩ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range := hcomm ▸ hzJ
  have hφ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K)
  have hw : orderOf w = 2 := by rw [← orderOf_injective _ hφ w]; exact hz
  have hN : (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.Normal := by
    rw [← hcomm]
    infer_instance
  exact E22L2.e22pd_isCoatom_centralizer_of_index_two _ hφ hN
    (pgl2_psl2Range_index_eq_two K hodd) hw
    (fun x hx => CFSG.Walter.psl2_isConj_of_orderOf_eq_two K hK1 hpodd one_pos hx hw)
    (CFSG.Walter.psl2_centralizer_involution_isCoatom K hK1 hpodd one_pos (by omega)
      (by rw [pow_one]; exact hp8) hw)
    (CFSG.Walter.psl2_center_centralizer_involution K hK1 hpodd one_pos (by omega) hw)

theorem inEFor_pgl2_pm_three
    (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (hp11 : 11 ≤ p) {T : Subgroup (PGL2 K)} (hT : IsSylowIn 2 T ⊤) : InEFor 1 ⊤ T := by
  have := E22L2.e22pl2pgl_finite K
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  have hodd : IsOddPrimePower (Nat.card K) :=
    CFSG.Walter.isOddPrimePower_of_card hK1 hpodd one_pos
  have hcard : 3 < Nat.card K := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := pslRange K with hJ
  have hJn : J.Normal := pslRange_normal hodd hcard
  have hcomm : commutator (PGL2 K) = J :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hodd hcard
  set A := T ⊓ J with hA
  have hAJ : A ≤ J := inf_le_right
  have hAT : A ≤ T := inf_le_left
  have hAsyl : QuasithinUnique.IsSylowTwoOf A J :=
    B6.isSylowTwoOf_inf_normal hT le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hJn])
  have hpgJ : IsPGroup 2 ↥(A.subgroupOf J) :=
    hAsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hAJ).symm
  let S : Sylow 2 ↥J := hpgJ.toSylow hAsyl.2.2
  let eJ : ↥J ≃* PSL2 K := (MonoidHom.ofInjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K))).symm
  let S' : Sylow 2 (PSL2 K) := S.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hS' : IsKleinFour ↥(S' : Subgroup (PSL2 K)) :=
    CFSG.Walter.psl2_sylow_two_isKleinFour K hK1 hpodd one_pos (by rw [pow_one]; exact hp8) S'
  have hSK : IsKleinFour ↥(A.subgroupOf J) := by
    have := hS'
    let e1 : ↥(A.subgroupOf J) ≃* ↥(S' : Subgroup (PSL2 K)) :=
      (A.subgroupOf J).equivMapOfInjective eJ.toMonoidHom eJ.injective
    exact E22L2.e22pl2pgl_isKleinFour_of_mulEquiv e1
  have hAK : IsKleinFour ↥A := by
    have := hSK
    exact E22L2.e22pl2pgl_isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAJ).symm
  have hTN : T ≤ Subgroup.normalizer (A : Set (PGL2 K)) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxJ⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), hJn.conj_mem x hxJ t⟩
    · rintro ⟨hxT, hxJ⟩
      refine ⟨?_, ?_⟩
      · have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
        simpa [mul_assoc] using this
      · have := hJn.conj_mem _ hxJ t⁻¹
        simpa [mul_assoc] using this
  have hA1 : A ≠ ⊥ := fun h => by
    have h4 := hAK.card_four
    rw [h] at h4
    simp at h4
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (CFSG.Goldschmidt.Sec8.inf_center_ne_bot' hT.2.1 hAT hTN hA1)
  have hzA : z ∈ A := hzmem.1
  have hzc : z ∈ Subgroup.centralizer (T : Set (PGL2 K)) := hzmem.2.2
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz2 : orderOf z = 2 := kleinFour_orderOf hAK hzA hz1'
  have hzJ : z ∈ J := hzA.2
  have hzJ' : z ∈ commutator (PGL2 K) := hcomm ▸ hzJ
  have hTC : T ≤ Subgroup.centralizer ({z} : Set (PGL2 K)) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc t ht)
  have hD₁s := E22L2.pgl2_centralizer_inner_involution_isSolvable hodd hcard hz2 hzJ'
  have hD₁m := pgl2_centralizer_inner_involution_isCoatom_pm_three hK hp8 hp11 hz2 hzJ'
  have hD₂s := isSolvable_normalizer_of_kleinFour hAK
    (pgl2_kleinFour_centralizer_eq_self K hodd A hAK)
  have hperf : commutator ↥J = ⊤ := (E22L2.e22pl2pgl_perfect_J hcard).commutator_eq_top
  obtain ⟨g, hgN, hgz⟩ := exists_conj_ne_of_kleinFour_sylow hperf S hSK
    (v := ⟨z, hzJ⟩) (Subgroup.mem_subgroupOf.mpr hzA) (fun h => hz1' (congrArg Subtype.val h))
  have hgN' : ((g : ↥J) : PGL2 K) ∈ Subgroup.normalizer (A : Set (PGL2 K)) :=
    mem_normalizer_of_subgroupOf hAJ hgN
  have hnle : ¬ Subgroup.normalizer (A : Set (PGL2 K)) ≤
      Subgroup.centralizer ({z} : Set (PGL2 K)) := by
    intro hle
    have hgz' := Subgroup.mem_centralizer_singleton_iff.mp (hle hgN')
    apply hgz
    apply Subtype.ext
    change (g : PGL2 K) * z * (g : PGL2 K)⁻¹ = z
    rw [hgz', mul_inv_cancel_right]
  have hgen : Subgroup.centralizer ({z} : Set (PGL2 K)) ⊔
      Subgroup.normalizer (A : Set (PGL2 K)) = ⊤ :=
    hD₁m.2 _ (lt_of_le_of_ne le_sup_left fun h => hnle (h ▸ le_sup_right))
  exact inEFor_top_of_solvable_pair hT hTC hTN hD₁s hD₂s hgen

theorem nParam_pgl2_pm_three
    (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (hp11 : 11 ≤ p) : nParam (⊤ : Subgroup (PGL2 K)) ≤ 1 := by
  have := E22L2.e22pl2pgl_finite K
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup (PGL2 K))
  have h := (nParam_le_iff (H := (⊤ : Subgroup (PGL2 K))) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT).mpr (inEFor_pgl2_pm_three hK hp8 hp11 hT))
  simpa using h

theorem nParam_le_one_of_psl2_prime_ge_seven
    {G : Type} [Group G] [Finite G]
    (hp7 : 7 ≤ p) (hF : IsPSL 2 p 1 ↥(CFSG.generalizedFitting G)) :
    nParam (⊤ : Subgroup G) ≤ 1 := by
  by_cases hp8 : p % 8 = 1 ∨ p % 8 = 7
  · exact E22L2.nParam_le_one_of_psl2_prime hp8 hp7 hF
  have hodd : p % 2 = 1 :=
    Nat.odd_iff.mp (((Fact.out : p.Prime).eq_two_or_odd').resolve_left (by omega))
  have hp8' : p % 8 = 3 ∨ p % 8 = 5 := by omega
  have hp11 : 11 ≤ p := by omega
  have hK : Nat.card (ZMod p) = p := Nat.card_zmod p
  rcases E22L2.psl2_prime_transport hp7 hF with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [E1.Eleven.nParam_top_mulEquiv e]
    exact nParam_psl2_pm_three hK hp8' hp11
  · have := E22L2.e22pl2pgl_finite (ZMod p)
    rw [E1.Eleven.nParam_top_mulEquiv e]
    exact nParam_pgl2_pm_three hK hp8' hp11

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

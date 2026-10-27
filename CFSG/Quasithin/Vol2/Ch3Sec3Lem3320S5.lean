module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S4c
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_subnormal_of_le_sup {K₀ L M N : Subgroup G} (h : IsSubnormal L M)
    (hK₀ : ⁅K₀, K₀⁆ = K₀) (hN : Group.IsSolvable ↥N) :
    K₀ ≤ M → M ≤ Subgroup.normalizer (N : Set G) → K₀ ≤ L ⊔ N → K₀ ≤ L := by
  induction h with
  | refl => exact fun hK₀M _ _ => hK₀M
  | @step L M' M hle hLn hM'M ih =>
    intro hK₀M hMN hK₀LN
    have hK₀M' : K₀ ≤ M' := ih hK₀M hMN (hK₀LN.trans (sup_le_sup_right hle N))
    have hLN : L ≤ Subgroup.normalizer (N : Set G) :=
      hle.trans ((A3.subnormal_le hM'M).trans hMN)
    have hLY : L ≤ L ⊔ (N ⊓ M') := le_sup_left
    have hYM' : L ⊔ (N ⊓ M') ≤ M' := sup_le hle inf_le_right
    have hLnY : (L.subgroupOf (L ⊔ (N ⊓ M'))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mpr
        (hYM'.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hLn))
    have hNs : Group.IsSolvable ↥(N ⊓ M') :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
    have hK₀Y : K₀ ≤ L ⊔ (N ⊓ M') := by
      intro k hk
      have hk' := hK₀LN hk
      rw [sup_comm] at hk'
      obtain ⟨n, hn, l, hl, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hLN).mp hk'
      have hnM' : n ∈ M' := by
        have := M'.mul_mem (hK₀M' hk) (M'.inv_mem (hle hl))
        simpa using this
      rw [sup_comm]
      exact Subgroup.mul_mem_sup ⟨hn, hnM'⟩ hl
    exact (le_perfectCore_of_perfect hK₀Y hK₀).trans
      (perfectCore_le_of_sup_solvable hLY hLnY rfl hNs)

omit [Finite G] in
theorem eq_bot_or_eq_of_subnormal {L Q : Subgroup G} (hQ : CFSG.IsQuasisimple ↥Q)
    (h : IsSubnormal L Q) (hLp : ⁅L, L⁆ = L) : L = ⊥ ∨ L = Q := by
  have hLQ : L ≤ Q := A3.subnormal_le h
  have hsub : IsSubnormal (L.subgroupOf Q) ⊤ := by
    have h1 : IsSubnormal (L.subgroupOf Q) (Q.subgroupOf Q) := A3.subnormal_comap Q.subtype h
    rwa [Subgroup.subgroupOf_self] at h1
  have hQ' : CFSG.Open.IsQuasisimple ↥Q := by
    have := hQ.1
    exact ⟨Group.IsPerfect.commutator_eq_top, hQ.2.1⟩
  have hp : ⁅L.subgroupOf Q, L.subgroupOf Q⁆ = L.subgroupOf Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLQ, hLp]
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hQ' _ hsub with
    hZ | htop
  · left
    have : Group.IsPerfect ↥(L.subgroupOf Q) := ⟨by
      rw [commutator_def]
      apply Subgroup.map_injective (L.subgroupOf Q).subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hp]⟩
    have h1 := CFSG.ComponentClassification.Quasisimple.perfect_le_center_eq_bot _ hZ
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hLQ hx⟩ : ↥Q) ∈ L.subgroupOf Q := hx
    rw [h1, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  · right
    refine le_antisymm hLQ fun x hx => ?_
    have : (⟨x, hx⟩ : ↥Q) ∈ L.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact this

theorem perfectCore_mem_cComp {I : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥(perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))))
    (hs : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥I)) : perfectCore I ∈ cComp I := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  have hP : (perfectCore (⊤ : Subgroup ↥I)).map I.subtype = perfectCore I := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hQ : (perfectCore (⊤ : Subgroup ↥I)).map π =
      perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hne : perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hq.2.2
    apply hab
    have h1 : ∀ x : ↥(perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))), x = 1 := by
      intro x
      exact Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp h _ x.2)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [h1 a', h1 b']
  refine ⟨?_, perfectCore_perfect I,
    A3.subnormal_of_normal (perfectCore_le I) (perfectCore_normal I), ?_⟩
  · intro h
    apply hne
    rw [← hQ, eq_bot_iff]
    intro q hq'
    obtain ⟨x, hx, rfl⟩ := hq'
    have hx' : (x : G) ∈ perfectCore I := hP ▸ Subgroup.mem_map_of_mem I.subtype hx
    rw [h, Subgroup.mem_bot] at hx'
    have : x = 1 := Subtype.ext hx'
    rw [this, map_one]
    exact Subgroup.one_mem _
  · intro L hLK₀ hL1 hLp hLsub
    have hLI : L ≤ I := hLK₀.le.trans (perfectCore_le I)
    have hsub : IsSubnormal (L.subgroupOf I) ⊤ := by
      have h1 : IsSubnormal (L.subgroupOf I) (I.subgroupOf I) := A3.subnormal_comap I.subtype hLsub
      rwa [Subgroup.subgroupOf_self] at h1
    have hLp' : ⁅L.subgroupOf I, L.subgroupOf I⁆ = L.subgroupOf I := by
      apply Subgroup.map_injective I.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLI, hLp]
    have hsubP : IsSubnormal ((L.subgroupOf I).map π) ⊤ := by
      have h1 := A3.subnormal_map π hsub
      rwa [← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h1
    have hLpP : ⁅(L.subgroupOf I).map π, (L.subgroupOf I).map π⁆ = (L.subgroupOf I).map π := by
      rw [← Subgroup.map_commutator, hLp']
    have hLQP := le_perfectCore_of_perfect (le_top : (L.subgroupOf I).map π ≤ ⊤) hLpP
    rcases eq_bot_or_eq_of_subnormal hq (A3.subnormal_of_le_of_le hsubP hLQP le_top) hLpP with
      h1 | h1
    ·
      apply hL1
      have hLN : L.subgroupOf I ≤ CFSG.pPrimeCore 3 ↥I := by
        rw [← QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 ↥I), ← Subgroup.map_eq_bot_iff]
        exact h1
      have hLs : Group.IsSolvable ↥(L.subgroupOf I) :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLN)
      have h3 : L.subgroupOf I = ⊥ := by
        rw [← perfectCore_eq_self_of_perfect hLp']
        exact (isSolvable_iff_perfectCore_eq_bot _).mp hLs
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hLI hx⟩ : ↥I) ∈ L.subgroupOf I := hx
      rw [h3, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
    ·
      apply hLK₀.not_ge
      have hK : perfectCore (⊤ : Subgroup ↥I) ≤ L.subgroupOf I ⊔ CFSG.pPrimeCore 3 ↥I := by
        intro x hx
        have hx' : π x ∈ (L.subgroupOf I).map π := by
          rw [h1, ← hQ]
          exact Subgroup.mem_map_of_mem π hx
        obtain ⟨y, hy, hyx⟩ := hx'
        have hyx' : y⁻¹ * x ∈ CFSG.pPrimeCore 3 ↥I := QuotientGroup.eq.mp hyx
        have e : x = y * (y⁻¹ * x) := by group
        rw [e]
        exact Subgroup.mul_mem_sup hy hyx'
      have h2 := le_of_subnormal_of_le_sup hsub (perfectCore_perfect _) hs le_top
        (Subgroup.normalizer_eq_top (H := CFSG.pPrimeCore 3 ↥I)).ge hK
      rw [← hP]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact h2 hy

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem isSolvable_B₀ (hB : IsB₀ X T D B₀) : Group.IsSolvable ↥B₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : IsSubnormal B₀ (X ⊔ T ⊔ D) :=
    A3.subnormal_of_normal hB.le (Subgroup.normal_subgroupOf_of_le_normalizer hB.nor)
  have hsyl := A312.isSylowTwoOf_inf_of_subnormal hsub H.isSylowTwoOf_B
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  have hTB : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((T ⊓ B₀ : Subgroup G) : Set G) := by
    rw [hT₀]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hn : ((T ⊓ B₀).subgroupOf B₀).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hB.le.trans hTB)
  have hP : Group.IsSolvable ↥((T ⊓ B₀).subgroupOf B₀) := by
    have h2 : IsPGroup 2 ↥((T ⊓ B₀).subgroupOf B₀) :=
      hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have := h2.isNilpotent
    infer_instance
  have hQ : Group.IsSolvable (↥B₀ ⧸ (T ⊓ B₀).subgroupOf B₀) := by
    refine CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.mp fun he => hsyl.2.2 ?_)
    rw [← Subgroup.index_eq_card] at he
    exact even_iff_two_dvd.mp he
  exact Group.isSolvable_of_ker_le_range ((T ⊓ B₀).subgroupOf B₀).subtype
    (QuotientGroup.mk' ((T ⊓ B₀).subgroupOf B₀))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem exists_K (hF : F6.TheoremF618Cat) (hIF : F6.InspF618Rest) (hIW : InspWalter3320)
    (hA21 : AsA21SQTKSection) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hA : AS_A_1_31)
    (hB : IsB₀ X T D B₀) :
    ∃ g ∈ D, g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) ∧
      (F6.IsF618CaseRestCat (plus (gZero X T g) (X ⊔ T))
          (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
        F6.IsF618CaseRestCat (plus (gZero X T g) (conjByElt g (X ⊔ T)))
          (plus (gZero X T g) (X ⊔ T))) ∧
      perfectCore (gZero X T g) ∈ cComp (gZero X T g) ∧
      ∃ K ∈ cComp (X ⊔ T ⊔ D), perfectCore (gZero X T g) ≤ K ∧
        X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) ∧ ¬ K ≤ B₀ := by
  have := H.h.simple
  have hKc : LocalSQTK G := (qtkeCore_of_cat H.h.nonabelian H.h.qtke).1
  obtain ⟨g, hg, hgR, hnot2⟩ := H.exists_not_caseTwo hIW hA21 h37 h38 h39 hA hB
  have hgX := H.not_mem_normalizer_X hg hgR
  obtain ⟨-, -, -, hconc⟩ := H.f618 hF hg hgR
  have h1 := H.not_caseOne hg hgR
  have hrest : F6.IsF618CaseRestCat (plus (gZero X T g) (X ⊔ T))
        (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
      F6.IsF618CaseRestCat (plus (gZero X T g) (conjByElt g (X ⊔ T)))
        (plus (gZero X T g) (X ⊔ T)) := by
    rcases hconc with h | h
    · exact Or.inl (F6.isF618CaseRestCat_of_oriented h h1.1 hnot2)
    · exact Or.inr (F6.isF618CaseRestCat_of_oriented h h1.2 hnot2)
  have hq : CFSG.IsQuasisimple ↥(perfectCore (⊤ : Subgroup
      (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)))) := by
    rcases hrest with h | h
    · exact (hIF _ _ _).1 h
    · exact (hIF _ _ _).1 h
  have hs := (H.isGoldschmidtTripleIn hg hgX).isSolvable_pPrimeCore
  have hK₀ : perfectCore (gZero X T g) ∈ cComp (gZero X T g) := perfectCore_mem_cComp hq hs
  have hTI : T ≤ gZero X T g := le_sup_right.trans le_sup_left
  have hK₀B : perfectCore (gZero X T g) ≤ X ⊔ T ⊔ D :=
    (perfectCore_le _).trans (gZero_le hg)
  have hK₀L : perfectCore (gZero X T g) ∈ lFamily T := cComp_subset_lFamily hTI hK₀
  obtain ⟨K, hK, hK₀K⟩ :=
    Vol2Native.lemma_1_2_4_exists hKc h37 h39 H.hB.2 H.isSylowTwoOf_B hK₀B hK₀L
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := by
    intro t ht
    have htB : t ∈ X ⊔ T ⊔ D := (le_sup_right.trans le_sup_left : T ≤ X ⊔ T ⊔ D) ht
    have hK' := C2Nine.conjByElt_mem_cComp hK (Subgroup.le_normalizer htB)
    have htK₀ : t ∈ Subgroup.normalizer (perfectCore (gZero X T g) : Set G) :=
      normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer (hTI ht))
    have hK₀K' : perfectCore (gZero X T g) ≤ conjByElt t K := by
      have h2 : conjByElt t (perfectCore (gZero X T g)) = perfectCore (gZero X T g) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htK₀
      rw [← h2]
      exact Subgroup.map_mono hK₀K
    have h3 := Vol2Native.lemma_1_2_4_unique hKc h37 H.hB.2 hK₀L hK' hK hK₀K' hK₀K
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3
  refine ⟨g, hg, hgR, hrest, hK₀, K, hK, hK₀K, H.le_normalizer_of_T_le h37 h38 hK hTK, ?_⟩
  intro hKB₀
  apply ne_bot_of_mem_cComp hK₀
  have hs₀ := H.isSolvable_B₀ hB
  have hK₀B₀ : perfectCore (gZero X T g) ≤ B₀ := hK₀K.trans hKB₀
  have h2 : Group.IsSolvable ↥(perfectCore (gZero X T g)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK₀B₀)
  have h4 := (isSolvable_iff_perfectCore_eq_bot (perfectCore (gZero X T g))).mp h2
  rwa [perfectCore_eq_self_of_perfect (perfectCore_perfect _)] at h4

end Hyp3320

end S3320

end CFSG.Quasithin.H13

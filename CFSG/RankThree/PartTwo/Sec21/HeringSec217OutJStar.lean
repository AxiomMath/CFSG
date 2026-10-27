module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutJ

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section JStar


set_option linter.unusedSectionVars false

theorem isSolvable_of_eq_sup_theta {X : Type*} [Group X] [Finite X] {J P : Subgroup X}
    (hJ : J = P ⊔ inSubgroup (aschbacherSolvableCore 3) J) (hP : Group.IsSolvable ↥P) :
    Group.IsSolvable ↥J := by
  set T : Subgroup X := inSubgroup (aschbacherSolvableCore 3) J with hT
  have hTJ : T ≤ J := Subgroup.map_subtype_le _
  have hPJ : P ≤ J := hJ ▸ le_sup_left
  have hJnT : J ≤ normalizer (T : Set X) := fun x hx =>
    Sec6.normalizer_le_normalizer_theta J (Subgroup.le_normalizer hx)
  haveI hNn : (T.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).2 hJnT
  haveI hTs : Group.IsSolvable ↥T := isSolvable_inSubgroup_theta J
  haveI hNs : Group.IsSolvable ↥(T.subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hTJ).toMonoidHom)
      (MulEquiv.injective _)
  haveI hPs : Group.IsSolvable ↥(P.subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hPJ).toMonoidHom)
      (MulEquiv.injective _)
  set φ : ↥(P.subgroupOf J) →* ↥J ⧸ T.subgroupOf J :=
    (QuotientGroup.mk' (T.subgroupOf J)).comp (P.subgroupOf J).subtype with hφ
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have hjmem : (j : X) ∈ P ⊔ T := hJ ▸ j.2
    have hPN : P ≤ normalizer (T : Set X) := hPJ.trans hJnT
    have hle : P ⊔ T ≤ prodSubgroup T P hPN :=
      sup_le (fun p hp => ⟨1, T.one_mem, p, hp, by simp⟩)
        (fun t ht => ⟨t, ht, 1, P.one_mem, by simp⟩)
    obtain ⟨t, ht, p, hp, hjtp⟩ := hle hjmem
    have hpJ : p ∈ J := hPJ hp
    have htJ : t ∈ J := hTJ ht
    refine ⟨⟨⟨p, hpJ⟩, Subgroup.mem_subgroupOf.2 hp⟩, ?_⟩
    show (QuotientGroup.mk (⟨p, hpJ⟩ : ↥J) : ↥J ⧸ T.subgroupOf J) = QuotientGroup.mk j
    have hjeq : j = ⟨t, htJ⟩ * ⟨p, hpJ⟩ := Subtype.ext hjtp
    rw [hjeq, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (⟨t, htJ⟩ : ↥J) : ↥J ⧸ T.subgroupOf J) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ht)
    rw [this, one_mul]
  haveI hQs : Group.IsSolvable (↥J ⧸ T.subgroupOf J) :=
    Group.isSolvable_of_surjective (f := φ) hφsurj
  exact Group.isSolvable_of_subgroup_quotient (T.subgroupOf J)

section JStar2

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.mem_lZeroStarAt_component (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {d : G} (hd : Subgroup.zpowers d = dGroup a c ⊓ L)
    {U₀ : Subgroup G} (hU₀ : U₀ ∈ fourGroupsMinus E) (hU₀I : U₀ ≤ iCore L a)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 d) (hIJ : iCore L a ≤ J)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hAQ : A ⊓ Sec4.thetaQuotCentralizer J = Subgroup.zpowers d) :
    J ∈ lZeroStarAt A d := by
  obtain ⟨⟨e⟩, hIA, hIcen, hIcomm, hcardAI, hAC⟩ := h.iCore_structure h45 hfr
  obtain ⟨hd1, hfrd⟩ := h.frame_of_zpowers_eq_inf h45 hfr hd
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hdDL : d ∈ dGroup a c ⊓ L := hd ▸ Subgroup.mem_zpowers d
  have hdE : d ∈ E := hDE hdDL.1
  have hdA : d ∈ A := hDA hdDL.1
  have hd3 : d ^ 3 = 1 := (isElemAbelian_iff.1 h.isElemAbelian_A).2 d hdA
  have hIperf : ⁅iCore L a, iCore L a⁆ = iCore L a := perfect_of_equiv_alt6 _ e
  have hIs : ¬ Group.IsSolvable ↥(iCore L a) := not_isSolvable_of_equiv_alt6 e
  have hfam : J ∈ thetaComponentFamily 3 A := mem_thetaComponentFamily_iff.2 ⟨d, hdA, hd1, hJ⟩
  refine ⟨hJ, ⟨?_, ?_⟩⟩
  ·
    rw [mem_lZeroUnion_iff]
    refine ⟨E, h.pair.mem_E.1, h.pair.mem_E.2, ?_⟩
    rw [mem_lZero_iff]
    refine ⟨mem_thetaComponentFamily_iff.2 ⟨d, hdE, hd1, hJ⟩, U₀, ?_, ?_⟩
    · rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
      have hU₀' := mem_fourGroups_iff.1 hU₀.1
      exact ⟨hU₀I.trans hIJ, IsPGroup.of_card (n := 2) (by rw [hU₀'.2.2]; norm_num), hU₀'.1⟩
    · intro hle
      rw [← hU₀.2] at hle
      have h2 : U₀ ≤ iCore L a ⊓ inSubgroup (aschbacherSolvableCore 3) J := le_inf hU₀I hle
      rw [inf_theta_eq_bot_of_A6 hIJ e, le_bot_iff] at h2
      have h1 : Nat.card U₀ = 1 := by rw [h2]; exact Subgroup.card_bot
      have h4 := (mem_fourGroups_iff.1 hU₀.1).2.2
      omega
  ·
    refine ⟨hfam, ?_⟩
    intro K hK hJK
    obtain ⟨x, hxA, hx1, hKx⟩ := mem_thetaComponentFamily_iff.1 hK
    have hKC : K ≤ Subgroup.centralizer ({x} : Set G) :=
      Sec6.le_centralizer_of_mem_thetaComponentsAt hKx
    set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) J with hT
    set P : Subgroup G := inSubgroup perfectResidual (J ⊓ K) with hP
    have hJeq : J = P ⊔ T := hJK
    have hPK : P ≤ K := (Sec6.inSubgroup_perfectResidual_le (J ⊓ K)).trans inf_le_right
    have hPJ : P ≤ J := (Sec6.inSubgroup_perfectResidual_le (J ⊓ K)).trans inf_le_left
    have hxJ : x ∈ Subgroup.normalizer (J : Set G) := hAJ hxA
    have hxT : x ∈ Subgroup.normalizer (T : Set G) := Sec6.normalizer_le_normalizer_theta J hxJ
    have hJnT : J ≤ normalizer (T : Set G) := fun y hy =>
      Sec6.normalizer_le_normalizer_theta J (Subgroup.le_normalizer hy)
    have hxQ : x ∈ Sec4.thetaQuotCentralizer J := by
      refine Sec6.mem_thetaQuotCentralizer_iff.2 ⟨hxJ, fun l' hl' => ?_⟩
      have hPN : P ≤ normalizer (T : Set G) := hPJ.trans hJnT
      have hle : P ⊔ T ≤ prodSubgroup T P hPN :=
        sup_le (fun p hp => ⟨1, T.one_mem, p, hp, by simp⟩)
          (fun t ht => ⟨t, ht, 1, P.one_mem, by simp⟩)
      obtain ⟨t, ht, p, hp, hl'eq⟩ := hle (hJeq ▸ hl')
      have hpx : p * x = x * p := Subgroup.mem_centralizer_singleton_iff.1 (hKC (hPK hp))
      have hxpx : x * p * x⁻¹ = p := by rw [← hpx]; group
      rw [hl'eq]
      have e1 : (t * p)⁻¹ * (x * (t * p) * x⁻¹) = p⁻¹ * (t⁻¹ * (x * t * x⁻¹)) * p := by
        calc (t * p)⁻¹ * (x * (t * p) * x⁻¹)
            = (t * p)⁻¹ * ((x * t * x⁻¹) * (x * p * x⁻¹)) := by group
          _ = (t * p)⁻¹ * ((x * t * x⁻¹) * p) := by rw [hxpx]
          _ = p⁻¹ * (t⁻¹ * (x * t * x⁻¹)) * p := by group
      rw [e1]
      have h1 : t⁻¹ * (x * t * x⁻¹) ∈ T :=
        T.mul_mem (T.inv_mem ht) ((Subgroup.mem_normalizer_iff.1 hxT t).1 ht)
      have := (Subgroup.mem_normalizer_iff.1 (hJnT (hPJ (P.inv_mem hp))) _).1 h1
      simpa using this
    have hxd : x ∈ Subgroup.zpowers d := hAQ ▸ ⟨hxA, hxQ⟩
    have hdx : d ∈ Subgroup.zpowers x := mem_zpowers_of_mem_zpowers hd3 hx1 hxd
    have hcent : Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({d} : Set G) :=
      centralizer_singleton_eq_of_mem_zpowers hxd hdx
    have hKd : K ∈ thetaComponentsAt 3 d := by
      rw [thetaComponentsAt_eq_thetaComponentsIn] at hKx ⊢
      rwa [hcent] at hKx
    have hPperf : ⁅P, P⁆ = P := by
      have hperf : Group.IsPerfect ↥(perfectResidual ↥(J ⊓ K)) :=
        (perfect_residual_characterization (G := ↥(J ⊓ K))).2.2.1
      have hperf' : Group.IsPerfect ↥P := Group.IsPerfect.ofSurjective
        (f := ((perfectResidual ↥(J ⊓ K)).equivMapOfInjective _
          (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)
      exact (isPerfect_iff_commutator_eq _).1 hperf'
    have hPns : ¬ Group.IsSolvable ↥P := by
      intro hPs
      haveI : Group.IsSolvable ↥J := isSolvable_of_eq_sup_theta hJeq hPs
      exact hIs (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIJ)
        (Subgroup.inclusion_injective hIJ))
    have hJK' : J = K := eq_of_perfect_le_inf_thetaComponentsAt hJ hKd (le_inf hPJ hPK) hPperf hPns
    subst hJK'
    exact llRel_self_of_mem_thetaComponentFamily hfam

end JStar2

end JStar

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

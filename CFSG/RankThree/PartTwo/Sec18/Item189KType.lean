module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.RankThree.LocalRank

theorem three_dvd_of_pRank_eq_one {X : Type} [Group X] [Finite X]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1) : 3 ∣ Nat.card X := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup X)
  rw [h, pow_one] at hE
  have hd := Subgroup.card_subgroup_dvd_card E
  rw [hE] at hd
  exact hd

theorem quasisimple_of_mem_thetaComponentsIn {G : Type} [Group G] [Finite G] {M K : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) :
    CFSG.IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  obtain ⟨hKM, hθ⟩ := mem_thetaComponentsIn_iff.mp hK
  obtain ⟨-, -, hQ⟩ := hθ
  let e : ↥(K.subgroupOf M) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKM
  have hmap : Subgroup.map e.toMonoidHom (aschbacherSolvableCore 3 ↥(K.subgroupOf M)) =
      aschbacherSolvableCore 3 ↥K :=
    aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  let e2 : ↥(K.subgroupOf M) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf M) ≃*
      ↥K ⧸ aschbacherSolvableCore 3 ↥K :=
    QuotientGroup.congr _ _ e hmap
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e2 hQ

theorem central_normal_eq_bot {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hsolv : Group.IsSolvable ↥N) (hndvd : ¬ 3 ∣ Nat.card ↥N)
    (hmax : ∀ T : Subgroup X, T.Normal → Group.IsSolvable ↥T → ¬ 3 ∣ Nat.card ↥T → T ≤ N)
    (R : Subgroup (X ⧸ N)) [R.Normal] (hRc : R ≤ Subgroup.center (X ⧸ N))
    (hRp : ¬ 3 ∣ Nat.card ↥R) : R = ⊥ := by
  obtain ⟨T, hT⟩ : ∃ T : Subgroup X, T = R.comap (QuotientGroup.mk' N) := ⟨_, rfl⟩
  have hmemT : ∀ x : X, x ∈ T ↔ (QuotientGroup.mk' N x) ∈ R := fun x => by
    rw [hT]; exact Iff.rfl
  have hTn : T.Normal := by rw [hT]; infer_instance
  have hNT : N ≤ T := by
    intro x hx
    rw [hmemT, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact R.one_mem
  let f : ↥(N.subgroupOf T) →* ↥T := (N.subgroupOf T).subtype
  let g : ↥T →* ↥R := ((QuotientGroup.mk' N).comp T.subtype).codRestrict R
    (fun t => (hmemT (t : X)).mp t.2)
  have hker : g.ker ≤ f.range := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have h1 : (QuotientGroup.mk' N) (t : X) = 1 := congrArg Subtype.val ht
    have h2 : (t : X) ∈ N := (QuotientGroup.eq_one_iff (t : X)).mp h1
    exact MonoidHom.mem_range.mpr ⟨⟨t, Subgroup.mem_subgroupOf.mpr h2⟩, rfl⟩
  have hker' : N.subgroupOf T = g.ker := by
    ext t
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (t : X)).mpr h)
    · intro h
      exact (QuotientGroup.eq_one_iff (t : X)).mp (congrArg Subtype.val h)
  have hgs : Function.Surjective g := by
    intro r
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (r : X ⧸ N)
    have hxT : x ∈ T := (hmemT x).mpr (by rw [QuotientGroup.mk'_apply, hx]; exact r.2)
    refine ⟨⟨x, hxT⟩, Subtype.ext ?_⟩
    show QuotientGroup.mk' N x = (r : X ⧸ N)
    rw [QuotientGroup.mk'_apply, hx]
  letI hcommR : CommGroup ↥R :=
    { (inferInstance : Group ↥R) with
      mul_comm := fun a b =>
        Subtype.ext ((Subgroup.mem_center_iff.mp (hRc a.2) (b : X ⧸ N)).symm) }
  have hsolvR : Group.IsSolvable ↥R := inferInstance
  have hsolvNT : Group.IsSolvable ↥(N.subgroupOf T) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNT).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNT).symm.surjective
  have hsolvT : Group.IsSolvable ↥T :=
    Group.isSolvable_of_ker_le_range f g hker
  let eR : (↥T ⧸ N.subgroupOf T) ≃* ↥R :=
    (QuotientGroup.quotientMulEquivOfEq hker').trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgs)
  have hcardT : Nat.card ↥T = Nat.card ↥R * Nat.card ↥N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf T),
      Nat.card_congr eR.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv]
  have hT3 : ¬ 3 ∣ Nat.card ↥T := by
    rw [hcardT]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h1
    · exact hRp h1
    · exact hndvd h1
  have hTN : T ≤ N := hmax T hTn hsolvT hT3
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
  have hxT : x ∈ T := (hmemT x).mpr (by rw [QuotientGroup.mk'_apply]; exact hr)
  have hxN : x ∈ N := hTN hxT
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr hxN

theorem pPrimeCore_quot_eq_bot {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hsolv : Group.IsSolvable ↥N) (hndvd : ¬ 3 ∣ Nat.card ↥N)
    (hmax : ∀ T : Subgroup X, T.Normal → Group.IsSolvable ↥T → ¬ 3 ∣ Nat.card ↥T → T ≤ N)
    (hQ : CFSG.IsQuasisimple (X ⧸ N)) (h3Y : 3 ∣ Nat.card (X ⧸ N)) :
    CFSG.pPrimeCore 3 (X ⧸ N) = ⊥ := by
  unfold CFSG.pPrimeCore
  refine le_antisymm (sSup_le fun R hR => ?_) bot_le
  obtain ⟨hRn, hRcop⟩ := hR
  have hRp : ¬ 3 ∣ Nat.card ↥R := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hRcop
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hRn with hRtop | hRcen
  · exfalso
    rw [hRtop, Subgroup.card_top] at hRp
    exact hRp h3Y
  · exact (central_normal_eq_bot N hsolv hndvd hmax R hRcen hRp).le

theorem center_eq_bot_of_quasisimple_pPrime {Y : Type} [Group Y] [Finite Y]
    (hQ : CFSG.IsQuasisimple Y) (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) : Subgroup.center Y = ⊥ := by
  have hE : CFSG.IsComponent (⊤ : Subgroup Y) := by
    unfold CFSG.IsComponent
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ, ?_⟩
    exact Subgroup.Normal.isSubnormal inferInstance
  have hc := CFSG.RankThree.PartTwo.Sec20.Res5.center_eq_bot_of_isComponent hO hr hE
  rw [eq_bot_iff]
  intro z hz
  have hzt : (⟨z, Subgroup.mem_top z⟩ : ↥(⊤ : Subgroup Y)) ∈
      Subgroup.center ↥(⊤ : Subgroup Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz g.1)
  rw [hc, Subgroup.mem_bot] at hzt
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hzt

theorem isSimpleGroup_of_quasisimple_centerless {Q : Type} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (hz : Subgroup.center Q = ⊥) : IsSimpleGroup Q := by
  haveI := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  refine ⟨fun H _ => ?_⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (N := H) inferInstance with h | h
  · exact Or.inr h
  · rw [hz] at h
    exact Or.inl (eq_bot_iff.mpr h)

theorem simple_of_quasisimple_quotient {X : Type} [Group X] [Finite X]
    (hQ : CFSG.IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (h3 : 3 ∣ Nat.card X) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) :
    IsSimpleGroup (X ⧸ aschbacherSolvableCore 3 X) := by
  obtain ⟨hsolv, -, hndvd, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have h3Y : 3 ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 X)] at h3
    exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h3).resolve_right hndvd
  have hpY := pPrimeCore_quot_eq_bot (aschbacherSolvableCore 3 X) hsolv hndvd hmax hQ h3Y
  have hrY : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ aschbacherSolvableCore 3 X)) ≤ 1 := by
    have hk : Nat.Coprime 3
        (Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).ker) := by
      rw [QuotientGroup.ker_mk']
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd
    have heq := CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3
      Nat.prime_three (QuotientGroup.mk' (aschbacherSolvableCore 3 X))
      (QuotientGroup.mk'_surjective _) hk
    rw [← heq]
    exact hr
  have hcen := center_eq_bot_of_quasisimple_pPrime hQ hpY hrY
  exact isSimpleGroup_of_quasisimple_centerless hQ hcen

theorem ktype_simple {G : Type} [Group G] [Finite G] {M K : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) (hr : CFSG.Open.pRank 3 K = 1) :
    IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  have hr' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 1 :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3
      (by norm_num) K).symm.trans hr
  exact simple_of_quasisimple_quotient (quasisimple_of_mem_thetaComponentsIn hK)
    (three_dvd_of_pRank_eq_one hr') hr'.le

end CFSG.RankThree.PartTwo.Sec18

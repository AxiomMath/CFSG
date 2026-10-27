module

public import CFSG.RankThree.ThetaFree.OrbitProduct
public import CFSG.RankThree.ThetaFree.Assembly
public import CFSG.RankThree.OddKernel.TransitiveCoverKernel
public import CFSG.RankThree.OddKernel.SemisimpleSectionTransport
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.Census3.Interface
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.ThetaFree

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

theorem pRank_le_of_isPGroup_quotient {T : Type*} [Group T] [Finite T] {S : Subgroup T}
    [S.Normal] (hTS : IsPGroup 3 (T ⧸ S)) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    CFSG.pRank r T ≤ CFSG.pRank r S := by
  rw [SectionRank.pRank_eq_open_pRank_top, pRank_coe_eq_assembly_pRank]
  obtain ⟨E, -, hE, hEcard⟩ := SectionRank.exists_pRank hr.one_lt (⊤ : Subgroup T)
  refine SectionRank.le_pRank hr.one_lt (fun e he => ?_) hE hEcard
  obtain ⟨k, hk⟩ := hTS (e : T ⧸ S)
  have h1 : orderOf (e : T ⧸ S) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (e : T ⧸ S) ∣ r := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, hE.2 e he, QuotientGroup.mk_one])
  have hcop : Nat.Coprime (3 ^ k) r :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3))
  have h := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
  exact h

theorem rank_bounds_of_minimal_cover {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2)
    {T : Type} [Group T] [Finite T] {Γ : Subgroup R} (π : Γ →* T) (hπ : Function.Surjective π)
    (hmin : ∀ Y : Subgroup Γ, Y ≠ ⊤ → Y.map π ≠ ⊤) (hnil : Group.IsNilpotent π.ker)
    (h3C : ¬ 3 ∣ Nat.card π.ker)
    (hsyl : ∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q π.ker),
      ((Q : Subgroup π.ker).map π.ker.subtype).Normal)
    (e : Γ ⧸ π.ker ≃* T) (S : Subgroup T) [S.Normal] (hES : layer S = ⊤)
    (hTS : IsPGroup 3 (T ⧸ S)) (hZS : IsPGroup 3 (center S))
    (hd : 3 ≤ Nat.card (LocalCores.ComponentIndex S)) (A : Subgroup Γ)
    (hA : ∀ L₁ L₂ : Subgroup S, IsComponent L₁ → IsComponent L₂ →
      ∃ a ∈ A, L₁.map (MulAut.conjNormal (π a)).toMonoidHom = L₂) :
    twoLocalOddRank T ≤ 3 ∧ ∀ r : ℕ, r.Prime → 3 < r → localRank r T ≤ 2 := by
  have hqΓ : ∀ r : ℕ, r.Prime → 3 < r → localRank r Γ ≤ 2 := fun r hr hr3 =>
    ((PartTwo.localRank_subgroup_le hr Γ).trans (PartTwo.localRank_subgroup_le hr R)).trans
      (hq r hr hr3)
  have heΓ : twoLocalOddRank Γ ≤ 3 := by
    rw [GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    refine ((PartTwo.evenRank_subgroup_le Γ).trans (PartTwo.evenRank_subgroup_le R)).trans ?_
    rw [← GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    exact he
  obtain ⟨heq, -, -, -, hrq⟩ :=
    (OddKernel.rank_three_three_complement_quotient_sharp_local_bounds π.ker).2.2 h3C heΓ hqΓ
  have heT : twoLocalOddRank T ≤ 3 := by
    rw [← Census3.twoLocalOddRank_eq_of_mulEquiv e]
    exact heq
  refine ⟨heT, fun r hr hr3 => ?_⟩
  by_cases hC2 : Even (Nat.card π.ker)
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hC2)
    have hc2 : IsPGroup 2 (zpowers c) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
    obtain ⟨Q, hcQ⟩ := hc2.exists_le_sylow
    set Q' := (Q : Subgroup π.ker).map π.ker.subtype with hQ'def
    have hQn : Q'.Normal := hsyl 2 Q
    have hQ2 : IsPGroup 2 Q' := Q.isPGroup'.map _
    have hQne : Q' ≠ ⊥ := by
      intro hb
      have hcQ' : (c : Γ) ∈ Q' := ⟨c, hcQ (mem_zpowers c), rfl⟩
      rw [hb, mem_bot] at hcQ'
      have hc1 : c = 1 := Subtype.ext hcQ'
      rw [hc1, orderOf_one] at hc
      exact absurd hc (by norm_num)
    have htop : Assembly.IsTwoLocal (⊤ : Subgroup Γ) :=
      ⟨Q', hQne, hQ2, (normalizer_eq_top_iff.2 hQn).symm⟩
    have hpΓ : CFSG.pRank r Γ ≤ 2 := by
      rw [SectionRank.pRank_eq_open_pRank_top]
      exact (RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr ⊤ htop).trans
        (hqΓ r hr hr3)
    set H := S.comap π with hHdef
    let φ : H →* S := (π.comp H.subtype).codRestrict S fun h => h.2
    have hφ : Function.Surjective φ := by
      intro s
      obtain ⟨γ, hγ⟩ := hπ (s : T)
      exact ⟨⟨γ, show π γ ∈ S by rw [hγ]; exact s.2⟩, Subtype.ext hγ⟩
    let ψ : (H ⧸ φ.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    have hlayer : CFSG.layer (H ⧸ φ.ker) = ⊤ :=
      LocalCores.layer_eq_top_of_surjective hES ψ.symm.toMonoidHom ψ.symm.surjective
    have hsec := OddKernel.large_prime_rank_two_semisimple_section_transport hr hr3 hpΓ H
      φ.ker hlayer
    have hpS : CFSG.pRank r S ≤ 2 :=
      (OddKernel.pRank_le_of_injective hr.one_lt ψ.symm.toMonoidHom ψ.symm.injective).trans hsec
    have hpT : CFSG.pRank r T ≤ 2 :=
      (pRank_le_of_isPGroup_quotient hTS hr (by omega)).trans hpS
    have h := RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank r hr T
    rw [← SectionRank.pRank_eq_open_pRank_top] at h
    exact h.trans hpT
  ·
    have hodd : Odd (Nat.card π.ker) := Nat.not_even_iff_odd.1 hC2
    have hC3 : Nat.Coprime (Nat.card π.ker) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3C).symm
    have hbot := (OddKernel.odd_three_complement_transitive_semisimple_minimal_cover_trivial_kernel
      π hπ hmin hnil hodd hC3 hqΓ S hES hTS hZS hd A hA).2.2.2.1
    have hr' : ¬ r ∣ Nat.card π.ker := by
      rw [hbot, card_bot]
      exact hr.not_dvd_one
    rw [← PartTwo.Census.localRank_eq_of_mulEquiv e hr]
    exact (hrq r hr hr3).1 hr'

section Lift

variable {X : Type*} [Group X] [Finite X] {B J : Subgroup X} {T : Subgroup X}

abbrev liftHom (S T : Subgroup X) : (S.subgroupOf T) →* X :=
  T.subtype.comp (S.subgroupOf T).subtype

omit [Finite X] in
theorem liftHom_injective (S T : Subgroup X) : Function.Injective (liftHom S T) :=
  T.subtype_injective.comp (S.subgroupOf T).subtype_injective

omit [Finite X] in
theorem map_conjNormal_liftHom {S : Subgroup X} [(S.subgroupOf T).Normal] (t : T)
    (L : Subgroup (S.subgroupOf T)) :
    (L.map (MulAut.conjNormal t).toMonoidHom).map (liftHom S T) =
      (L.map (liftHom S T)).map (MulAut.conj (t : X)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1

omit [Finite X] in
theorem liftHom_eq_comp (hST : orbitProd B J ≤ T) :
    liftHom (orbitProd B J) T =
      (orbitProd B J).subtype.comp (subgroupOfEquivOfLe hST).toMonoidHom :=
  rfl

theorem map_liftHom_mem_conjOrbit (hJ : IsComponent J) (hST : orbitProd B J ≤ T)
    {L : Subgroup ((orbitProd B J).subgroupOf T)} (hL : IsComponent L) :
    L.map (liftHom (orbitProd B J) T) ∈ conjOrbit B J := by
  have hLc : IsComponent (L.map (subgroupOfEquivOfLe hST).toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv _ hL
  obtain ⟨K, hK, hKe⟩ := exists_eq_subgroupOf_of_isComponent hJ hLc
  rw [liftHom_eq_comp hST, ← map_map, hKe, subgroupOf_map_subtype,
    inf_of_le_left (le_orbitProd hK)]
  exact hK

theorem exists_isComponent_map_liftHom (hJ : IsComponent J) (hST : orbitProd B J ≤ T)
    {K : Subgroup X} (hK : K ∈ conjOrbit B J) :
    ∃ L : Subgroup ((orbitProd B J).subgroupOf T), IsComponent L ∧
      L.map (liftHom (orbitProd B J) T) = K := by
  refine ⟨(K.subgroupOf (orbitProd B J)).map (subgroupOfEquivOfLe hST).symm.toMonoidHom,
    LocalCores.isComponent_map_mulEquiv _ (isComponent_subgroupOf_orbitProd hJ hK), ?_⟩
  rw [liftHom_eq_comp hST, map_map]
  have h : ((orbitProd B J).subtype.comp (subgroupOfEquivOfLe hST).toMonoidHom).comp
      (subgroupOfEquivOfLe hST).symm.toMonoidHom = (orbitProd B J).subtype := by
    ext x
    simp
  rw [h, subgroupOf_map_subtype, inf_of_le_left (le_orbitProd hK)]

theorem ncard_conjOrbit_le_card_componentIndex (hJ : IsComponent J) (hST : orbitProd B J ≤ T) :
    (conjOrbit B J).ncard ≤
      Nat.card (LocalCores.ComponentIndex ((orbitProd B J).subgroupOf T)) := by
  classical
  choose L hL hLK using fun K : conjOrbit B J => exists_isComponent_map_liftHom hJ hST K.2
  let f : conjOrbit B J → LocalCores.ComponentIndex ((orbitProd B J).subgroupOf T) :=
    fun K => ⟨L K, hL K⟩
  have hf : Function.Injective f := fun K₁ K₂ h => by
    have h' : L K₁ = L K₂ := congrArg Subtype.val h
    apply Subtype.ext
    rw [← hLK K₁, ← hLK K₂, h']
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective f hf

theorem transitive_components_subgroupOf (hJ : IsComponent J) (hST : orbitProd B J ≤ T)
    [((orbitProd B J).subgroupOf T).Normal] {Γ : Type*} [Group Γ] (π : Γ →* T)
    {A : Subgroup Γ} (hAB : ∀ b ∈ B, ∃ a ∈ A, ((π a : T) : X) = b)
    (L₁ L₂ : Subgroup ((orbitProd B J).subgroupOf T)) (h₁ : IsComponent L₁)
    (h₂ : IsComponent L₂) :
    ∃ a ∈ A, L₁.map (MulAut.conjNormal (π a)).toMonoidHom = L₂ := by
  obtain ⟨b₁, hb₁⟩ := map_liftHom_mem_conjOrbit hJ hST h₁
  obtain ⟨b₂, hb₂⟩ := map_liftHom_mem_conjOrbit hJ hST h₂
  obtain ⟨a, haA, hab⟩ := hAB ((b₂ : X) * (b₁ : X)⁻¹) (B.mul_mem b₂.2 (B.inv_mem b₁.2))
  refine ⟨a, haA, map_injective (liftHom_injective _ _) ?_⟩
  rw [map_conjNormal_liftHom, ← hb₁, ← hb₂, hab, map_conj_map_conj, inv_mul_cancel_right]

end Lift

theorem three_le_ncard_conjOrbit {X : Type*} [Group X] [Finite X] {B J : Subgroup X}
    (hB : IsPGroup 3 B) (hJB : ¬ B ≤ normalizer (J : Set X)) : 3 ≤ (conjOrbit B J).ncard := by
  let := Theta.conjAction B
  have hstab := stabilizer_conjAction_eq B J
  rw [conjOrbit_eq_orbit, ← MulAction.index_stabilizer]
  obtain ⟨j, hj⟩ := hB.index (MulAction.stabilizer B J)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, index_eq_one, hstab] at hj
    apply hJB
    intro a ha
    have h : (⟨a, ha⟩ : B) ∈ (normalizer (J : Set X)).subgroupOf B := hj ▸ mem_top _
    exact mem_subgroupOf.1 h
  rw [hj]
  calc 3 = 3 ^ 1 := (pow_one 3).symm
    _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hj0)

theorem card_map_eq_of_injOn {G H : Type*} [Group G] [Group H] (f : G →* H) {A : Subgroup G}
    (hf : Set.InjOn f A) : Nat.card (A.map f) = Nat.card A :=
  (Nat.card_congr (Equiv.ofBijective (f.subgroupMap A)
    ⟨fun x y h => Subtype.ext (hf x.2 y.2 (congrArg Subtype.val h)),
      f.subgroupMap_surjective A⟩)).symm

theorem exists_theta_free_overgroup {G : Type} [Group G] [Finite G]
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2)
    {A : Subgroup G} (hA : IsPGroup 3 A) {J : Subgroup (G ⧸ aschbacherSolvableCore 3 G)}
    (hJ : IsComponent J)
    (hJA : ¬ A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤
      normalizer (J : Set (G ⧸ aschbacherSolvableCore 3 G))) :
    ∃ T : Subgroup (G ⧸ aschbacherSolvableCore 3 G), J ≤ T ∧
      A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤ T ∧
      (pCore 3 G).map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤ T ∧
      aschbacherSolvableCore 3 T = ⊥ ∧ twoLocalOddRank T ≤ 3 ∧
      ∀ r : ℕ, r.Prime → 3 < r → localRank r T ≤ 2 := by
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := pCore 3 G with hPdef
  have hPn : P.Normal := inferInstance
  have hP3 : IsPGroup 3 P := pCore_isPGroup
  have hU3 : IsPGroup 3 (A ⊔ P : Subgroup G) := hA.to_sup_of_normal_right hP3
  set B := A.map ρ with hBdef
  set V := (A ⊔ P).map ρ with hVdef
  have hB3 : IsPGroup 3 B := hA.map ρ
  have hV3 : IsPGroup 3 V := hU3.map ρ
  have hθX : aschbacherSolvableCore 3 (G ⧸ N) = ⊥ := theta_quotient_core_and_ranks.1
  have hPnX : (P.map ρ).Normal := hPn.map ρ (QuotientGroup.mk'_surjective N)
  have hPs : Group.IsSolvable (P.map ρ) := by
    have := (hP3.map ρ).isNilpotent
    infer_instance
  have hPc := (LocalCores.component_solvable_centralizer hPs hPnX.isSubnormal).1
  set S := orbitProd B J with hSdef
  have hPS : P.map ρ ≤ centralizer (S : Set (G ⧸ N)) := by
    rw [le_centralizer_iff]
    exact sSup_le fun K hK =>
      commutator_eq_bot_iff_le_centralizer.1 (hPc K (isComponent_of_mem_conjOrbit hJ hK))
  have hVN : V ≤ normalizer (S : Set (G ⧸ N)) := by
    rw [hVdef, Subgroup.map_sup]
    exact sup_le (le_normalizer_orbitProd B J) (hPS.trans (centralizer_le_normalizer _))
  set T := S ⊔ V with hTdef
  have hZS : IsPGroup 3 (center S) := isPGroup_center_orbitProd hθX hJ
  have hθT : aschbacherSolvableCore 3 T = ⊥ := aschbacherSolvableCore_sup_eq_bot hJ hVN hV3 hZS
  have hST : S ≤ T := le_sup_left
  have hVT : V ≤ T := le_sup_right
  have hJS : J ≤ S := le_orbitProd (self_mem_conjOrbit B J)
  have hBV : B ≤ V := map_mono le_sup_left
  have hPV : P.map ρ ≤ V := map_mono le_sup_right
  refine ⟨T, hJS.trans hST, hBV.trans hVT, hPV.trans hVT, hθT, ?_⟩
  have : (S.subgroupOf T).Normal := normal_subgroupOf_sup hVN
  have hTS : IsPGroup 3 (T ⧸ S.subgroupOf T) := isPGroup_quotient_sup hVN hV3
  set R := T.comap ρ with hRdef
  let ρ' : R →* T := (ρ.comp R.subtype).codRestrict T fun x => x.2
  have hρ' : Function.Surjective ρ' := by
    intro t
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (t : G ⧸ N)
    exact ⟨⟨g, show ρ g ∈ T by rw [hg]; exact t.2⟩, Subtype.ext hg⟩
  have hker : ¬ 3 ∣ Nat.card ρ'.ker := by
    intro h3
    apply three_not_dvd_card_aschbacherSolvableCore (G := G)
    have h1 : Nat.card ρ'.ker ∣ Nat.card ρ.ker := by
      rw [show ρ'.ker = (ρ.comp R.subtype).ker from MonoidHom.ker_codRestrict _ _ _]
      exact PerfectCover.card_ker_comp_subtype_dvd ρ R
    rw [QuotientGroup.ker_mk'] at h1
    exact h3.trans h1
  have hUR : (A ⊔ P : Subgroup G) ≤ R := fun u hu => hVT (mem_map_of_mem ρ hu)
  have hU'3 : IsPGroup 3 ((A ⊔ P : Subgroup G).subgroupOf R) :=
    hU3.of_equiv (subgroupOfEquivOfLe hUR).symm
  obtain ⟨Γ, hUΓ, -, hmin, hsurj, -, hnil, h3C, hsyl, ⟨e, -⟩, -⟩ :=
    PerfectCover.prime_complement_minimal_cover_preserving_prime_subgroup Nat.prime_three ρ' hρ'
      hker _ hU'3
  set π : Γ →* T := ρ'.comp Γ.subtype with hπdef
  have hmin' : ∀ Y : Subgroup Γ, Y ≠ ⊤ → Y.map π ≠ ⊤ := by
    intro Y hY hYm
    refine hmin (Y.map Γ.subtype) (lt_of_le_of_ne (map_subtype_le Y) fun h => hY ?_) ?_
    · apply map_injective Γ.subtype_injective
      rw [h, ← MonoidHom.range_eq_map, range_subtype]
    · rw [map_map]
      exact hYm
  set AΓ : Subgroup Γ := (A.subgroupOf R).subgroupOf Γ with hAΓdef
  have hAB : ∀ b ∈ B, ∃ a ∈ AΓ, ((π a : T) : G ⧸ N) = b := by
    rintro _ ⟨a, haA, rfl⟩
    have haR : a ∈ R := hUR ((le_sup_left : A ≤ A ⊔ P) haA)
    have haΓ : (⟨a, haR⟩ : R) ∈ Γ := hUΓ (mem_subgroupOf.2 ((le_sup_left : A ≤ A ⊔ P) haA))
    exact ⟨⟨⟨a, haR⟩, haΓ⟩, mem_subgroupOf.2 (mem_subgroupOf.2 haA), rfl⟩
  have hES' : layer (S.subgroupOf T) = ⊤ :=
    LocalCores.layer_eq_top_of_surjective (layer_orbitProd_eq_top hJ)
      (subgroupOfEquivOfLe hST).symm.toMonoidHom (subgroupOfEquivOfLe hST).symm.surjective
  have hZS' : IsPGroup 3 (center (S.subgroupOf T)) :=
    hZS.of_equiv (Subgroup.centerCongr (subgroupOfEquivOfLe hST).symm)
  have hd : 3 ≤ Nat.card (LocalCores.ComponentIndex (S.subgroupOf T)) :=
    (three_le_ncard_conjOrbit hB3 hJA).trans (ncard_conjOrbit_le_card_componentIndex hJ hST)
  exact rank_bounds_of_minimal_cover he hq π hsurj hmin' hnil h3C hsyl e (S.subgroupOf T) hES'
    hTS hZS' hd AΓ (transitive_components_subgroupOf hJ hST π hAB)

theorem le_normalizer_of_subgroupOf {X : Type*} [Group X] {J B T : Subgroup X} (hJT : J ≤ T)
    (hBT : B ≤ T) (h : B.subgroupOf T ≤ normalizer ((J.subgroupOf T : Subgroup T) : Set T)) :
    B ≤ normalizer (J : Set X) := by
  have key : ∀ c : T, c ∈ normalizer ((J.subgroupOf T : Subgroup T) : Set T) →
      J.map (MulAut.conj (c : X)).toMonoidHom ≤ J := by
    rintro c hc _ ⟨y, hy, rfl⟩
    have h := (mem_normalizer_iff.1 hc ⟨y, hJT hy⟩).1 (mem_subgroupOf.2 hy)
    exact mem_subgroupOf.1 h
  intro b hb
  have hb' : (⟨b, hBT hb⟩ : T) ∈ normalizer ((J.subgroupOf T : Subgroup T) : Set T) :=
    h (mem_subgroupOf.2 hb)
  exact Theta.mem_normalizer_of_map_conj_le (key _ hb') (key _ (inv_mem hb'))

theorem actor_hyp_of_overgroup {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsPGroup 3 A)
    (hor : pCore 3 G ≠ ⊥ ∨
      (Assembly.IsElemAbelian 3 A ∧ ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n))
    {T : Subgroup (G ⧸ aschbacherSolvableCore 3 G)}
    (hBT : A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤ T)
    (hPT : (pCore 3 G).map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤ T) :
    pCore 3 T ≠ ⊥ ∨
      (Assembly.IsElemAbelian 3
          ((A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))).subgroupOf T) ∧
        ∃ n : ℕ, 3 ≤ n ∧
          Nat.card ((A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))).subgroupOf T) =
            3 ^ n) := by
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hor with hP | ⟨hAe, n, hn, hAc⟩
  · left
    have hPn : (pCore 3 G).Normal := inferInstance
    have hP3 : IsPGroup 3 (pCore 3 G) := pCore_isPGroup
    have hPX : ((pCore 3 G).map ρ).Normal := hPn.map ρ (QuotientGroup.mk'_surjective N)
    have hP'n : (((pCore 3 G).map ρ).subgroupOf T).Normal := inferInstance
    have hP'3 : IsPGroup 3 (((pCore 3 G).map ρ).subgroupOf T) :=
      (hP3.map ρ).of_equiv (subgroupOfEquivOfLe hPT).symm
    have hle : ((pCore 3 G).map ρ).subgroupOf T ≤ pCore 3 T := le_sSup ⟨hP'n, hP'3⟩
    intro hbot
    rw [hbot, le_bot_iff] at hle
    have hPmap : (pCore 3 G).map ρ = ⊥ := by
      have h := congrArg (fun H : Subgroup T => H.map T.subtype) hle
      simp only [subgroupOf_map_subtype, Subgroup.map_bot] at h
      rwa [inf_of_le_left hPT] at h
    apply hP
    have hinjP := (theta_quotient_three_subgroups (G := G)).2.2.1
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    have hx1 : ρ x = 1 := by
      have h : ρ x ∈ (pCore 3 G).map ρ := mem_map_of_mem ρ hx
      rw [hPmap, mem_bot] at h
      exact h
    exact hinjP hx (pCore 3 G).one_mem (by rw [hx1, map_one])
  · right
    have hBe : Assembly.IsElemAbelian 3 (A.map ρ) := SectionRank.isElemAbelian_map hAe ρ
    have : IsMulCommutative (A.map ρ) := hBe.1
    refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, n, hn,
      ?_⟩
    · show ((x : T) : G ⧸ N) * ((y : T) : G ⧸ N) = ((y : T) : G ⧸ N) * ((x : T) : G ⧸ N)
      exact congrArg Subtype.val
        (mul_comm' (⟨((x : T) : G ⧸ N), mem_subgroupOf.1 x.2⟩ : A.map ρ)
          ⟨((y : T) : G ⧸ N), mem_subgroupOf.1 y.2⟩)
    · rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hBe.2 _ (mem_subgroupOf.1 hx)
    · rw [Nat.card_congr (subgroupOfEquivOfLe hBT).toEquiv, ← hAc]
      exact card_map_eq_of_injOn ρ ((theta_quotient_three_subgroups (G := G)).1 A hA)

theorem normalizes_components_theta_quotient_of
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) {G : Type} [Group G] [Finite G]
    (hK : SectionRank.IsKGroupCat G) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) {A : Subgroup G} (hA : IsPGroup 3 A)
    (hor : pCore 3 G ≠ ⊥ ∨
      (Assembly.IsElemAbelian 3 A ∧ ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n))
    {J : Subgroup (G ⧸ aschbacherSolvableCore 3 G)} (hJ : IsComponent J) :
    A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤
      normalizer (J : Set (G ⧸ aschbacherSolvableCore 3 G)) := by
  by_contra hJA
  obtain ⟨T, hJT, hBT, hPT, hθT, heT, hqT⟩ := exists_theta_free_overgroup he hq hA hJ hJA
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKT : SectionRank.IsKGroupCat T := (hK.quotient _).subgroup T
  have hB'3 : IsPGroup 3
      ((A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))).subgroupOf T) :=
    (hA.map _).of_equiv (subgroupOfEquivOfLe hBT).symm
  have hJT' : IsComponent (J.subgroupOf T) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJT).symm hJ.1, hJ.2.subgroupOf⟩
  have hnorm := (theta_free_K_group_source_four_five_component_normalization_of hB hM hKT hθT
    heT hqT hB'3 (actor_hyp_of_overgroup hA hor hBT hPT)).2 _ hJT'
  exact hJA (le_normalizer_of_subgroupOf hJT hBT hnorm)

end CFSG.RankThree.ThetaFree

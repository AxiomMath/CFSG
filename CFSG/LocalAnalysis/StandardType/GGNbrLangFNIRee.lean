module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRestr
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIReeCore
public import CFSG.CGT.Timmesfeld75.ListWCLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private theorem fniRee_no_mem_ge5 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {s : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a} (hs : orderOf s = p)
    {φ : MulAut (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)} (hφp : φ ^ p = 1)
    (hφout : ∀ g, φ ≠ MulAut.conj g) (hφs : φ s = s)
    {J : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s)))
    {f' : MulAut J} (hf' : ∀ j : J, (f' j : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) = φ j) :
    GGMarkingAll (K := J) fun _ _ _ I _ θ => kgInducedAut θ f' ∉ I := by
  obtain ⟨hJq, hZJ, hdvd, hty⟩ := kgfniRee_layer_ge5 ha hK hp hp5 hs hJ
  obtain ⟨P, hsp, hspI⟩ : ∃ P : LargeEvenMarkProp J, LargeEvenMarking J P ∧
      ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
        (θ : J ⧸ Subgroup.center J ≃* R), P lab R I F θ → I ⊆ LargeEvenInnSet R := by
    rcases hty with h | h
    · obtain ⟨e⟩ := h
      exact kgfniRee_specialMarking_sl2 ha hK hJq.1 e
    · obtain ⟨e⟩ := h
      exact kgfniRee_specialMarking_sz ha hK hJq.1 hZJ e
  apply kgFieldRestriction_of_oneMarking f'
  refine largeEvenMarking_mono (fun lab R _ I F θ hP hEx => ?_) hsp
  have hIinn : I ⊆ LargeEvenInnSet R := hspI lab R I F θ hP
  obtain ⟨φ, hφcl, hind⟩ := hEx
  have hφinn : φ ∈ (MulAut.conj : R →* MulAut R).range := by
    have hle : Subgroup.closure I ≤ (MulAut.conj : R →* MulAut R).range := by
      rw [Subgroup.closure_le]
      exact fun x hx => hIinn hx
    exact hle hφcl
  have hφeq : φ = kgInducedAut θ f' := by
    ext x
    obtain ⟨q, rfl⟩ := θ.surjective x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hind k (f' k) rfl]
    exact (ggInducedAut_apply θ f' k).symm
  subst hφeq
  have hα : ∀ s : R, θ.symm ((kgInducedAut θ f') s) =
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient f' (θ.symm s) := by
    intro x
    obtain ⟨q, rfl⟩ := θ.surjective x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : kgInducedAut θ f' (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (f' k)) := by
      simpa [kgInducedAut, ggInducedAut] using ggInducedAut_apply θ f' k
    rw [h1, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk f' k).symm
  obtain ⟨j, hj⟩ := CFSG.LocalAnalysis.GLTheoremA.K155X.l154_inner_of_induced θ.symm hZJ f'
    (kgInducedAut θ f') hα hφinn
  refine CFSG.LocalAnalysis.GLTheoremA.K155X.l154_ree_descent
    (j := (j : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))
    ha hK hp hp5 hφp hφout hZJ j.2 ?_ hdvd
  intro t ht
  have h1 := hj ⟨t, ht⟩
  have h2 := congrArg Subtype.val h1
  have h3 := hf' ⟨t, ht⟩
  simpa using h3.symm.trans h2

private theorem fniRee_no_mem_three_C {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {s : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a} (hs : orderOf s = 3)
    {φ : MulAut (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)} (hφ3 : φ ^ 3 = 1)
    (hφout : ∀ g, φ ≠ MulAut.conj g) (hφs : φ s = s)
    {f' : MulAut ↥(Subgroup.centralizer ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)))}
    (hf' : ∀ j : ↥(Subgroup.centralizer ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))),
      (f' j : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) = φ j) :
    GGMarkingAll (K := ↥(Subgroup.centralizer
      ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))))
      fun _ _ _ I _ θ => kgInducedAut θ f' ∉ I := by
  let C := Subgroup.centralizer ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))
  have hCq : CFSG.IsQuasisimple ↥C :=
    CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_isQuasisimple_centralizer ha hK s hs
  let S : LargeEvenLabel → Prop := fun lab =>
    markTag lab = .PSU ∧ markRank lab = 3 ∧ markChar lab = 2 ∧ markDeg lab = 2 * a + 1
  have hperfC : commutator ↥C = ⊤ := by
    haveI : Group.IsPerfect ↥C := hCq.1
    exact Group.IsPerfect.commutator_eq_top
  have hmark : LargeEvenMarking ↥C (fun lab _ _ _ _ _ => S lab) := by
    simpa only [S] using largeEvenMarking_of_lieModel_centerQuot hperfC
      (CFSG.LocalAnalysis.GLTheoremA.K155X.l154_ree_three_lieModel ha hK hs)
  have hall : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (GGRawInnField 3) :=
    fun lab hlab _ => ggRawInnFieldInput_holds 3 Nat.prime_three (by norm_num) lab hlab
  have hsp := largeEvenMarking_and_labelAll_simple hall (fun _ _ _ _ _ _ h => h) hmark
  have hspP : LargeEvenMarking ↥C (fun lab R _ I F θ => S lab ∧
      ((∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) ∧ (∀ φ ∈ I, φ⁻¹ ∈ I) ∧
        (∀ r : R, MulAut.conj r ∈ I) ∧ ∀ f ∈ F, orderOf f = 3 → f ∉ I)) := hsp
  apply kgFieldRestriction_of_oneMarking f'
  obtain ⟨hX, lab, hlab, hraw⟩ := hspP
  obtain ⟨R0, _, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ0, hP0⟩ := hQ0
  obtain ⟨hS0, -⟩ := hP0
  have htwA : lab = (⟨.twA, 2, 2 * a + 1⟩ : LargeEvenLabel) :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154_label_twA_of_mark hS0.1 hS0.2.1
      hS0.2.2.1 hS0.2.2.2
  rw [htwA] at hraw
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hraw
  obtain ⟨K', hF', hfin', hK', hQ0⟩ := hraw
  letI := hF'
  haveI := hfin'
  obtain ⟨hsimple, hna, θ, hP⟩ := hQ0
  refine ⟨hX, lab, hlab, ?_⟩
  rw [htwA]
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary]
  refine ⟨K', inferInstance, inferInstance, hK', ?_⟩
  refine ⟨hsimple, hna, θ, ?_⟩
  intro hEx
  have hP' := hP
  obtain ⟨hS, hmul, hinv, hconj, -⟩ := hP
  obtain ⟨ψ, hψcl, hind⟩ := hEx
  let H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K' (2 ^ (2 * a + 1))))) :=
    { carrier := LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K' (2 ^ (2 * a + 1))))
        (LargeEvenGUSet (Fin 3) K' (2 ^ (2 * a + 1))),
      one_mem' := by simpa using hconj 1
      mul_mem' := fun ha hb => hmul _ ha _ hb
      inv_mem' := fun ha => hinv _ ha }
  have hψI : ψ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K' (2 ^ (2 * a + 1))))
      (LargeEvenGUSet (Fin 3) K' (2 ^ (2 * a + 1))) := by
    have hle : Subgroup.closure (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K' (2 ^ (2 * a + 1))))
        (LargeEvenGUSet (Fin 3) K' (2 ^ (2 * a + 1)))) ≤ H := by
      rw [Subgroup.closure_le]
      exact fun y hy => by simpa [H] using hy
    simpa [H] using hle hψcl
  have hψeq : ψ = kgInducedAut θ f' := by
    ext x
    obtain ⟨q, rfl⟩ := θ.surjective x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hind k (f' k) rfl]
    exact (ggInducedAut_apply θ f' k).symm
  have hindφ : LargeEvenInduces θ (fun z z' : ↥C =>
      φ (z : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) =
        (z' : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) ψ := by
    subst hψeq
    intro z z' hz
    have hzz : f' z = z' := Subtype.ext ((hf' z).trans hz)
    subst hzz
    exact kgInducedAut_induces θ f' z (f' z) rfl
  have hcan : CFSG.Assembly.LargeEvenMarking ↥C (fun _ _ _ I _ θ =>
      ∃ ψ ∈ I, LargeEvenInduces θ (fun z z' : ↥C =>
        φ (z : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) =
          (z' : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) ψ) := by
    have hsp' : LargeEvenMarking ↥C (fun lab R _ I F θ =>
        ((S lab ∧ ((∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) ∧ (∀ φ ∈ I, φ⁻¹ ∈ I) ∧
          (∀ r : R, MulAut.conj r ∈ I) ∧ ∀ f ∈ F, orderOf f = 3 → f ∉ I)) ∧
          ∃ ψ ∈ I, LargeEvenInduces θ (fun z z' : ↥C =>
          φ (z : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) =
            (z' : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) ψ) ∧ lab.tag = .twA) := by
      refine ⟨hX, lab, hlab, ?_⟩
      rw [htwA]
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary]
      refine ⟨K', inferInstance, inferInstance, hK', hsimple, hna, θ, ?_⟩
      exact ⟨⟨hP', ⟨ψ, hψI, hindφ⟩⟩, rfl⟩
    have hsp'' : LargeEvenMarking ↥C (fun lab R _ I F θ =>
        (∃ ψ ∈ I, LargeEvenInduces θ (fun z z' : ↥C =>
          φ (z : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) =
            (z' : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) ψ) ∧ lab.tag = .twA) :=
      largeEvenMarking_mono (fun lab R _ I F θ h => ⟨h.1.2, h.2⟩) hsp'
    exact kgfniRee_canonical_of_twA hsp''
  exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154ReeThreeRes_holds a K inferInstance inferInstance
    inferInstance ha hK s φ hs hφ3 hφout hφs hcan

private theorem fniRee_no_mem_three {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {s : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a} (hs : orderOf s = 3)
    {φ : MulAut (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)} (hφ3 : φ ^ 3 = 1)
    (hφout : ∀ g, φ ≠ MulAut.conj g) (hφs : φ s = s)
    {J : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s)))
    {f' : MulAut J} (hf' : ∀ j : J, (f' j : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) = φ j) :
    GGMarkingAll (K := J) fun _ _ _ I _ θ => kgInducedAut θ f' ∉ I := by
  have hJC : J = Subgroup.centralizer ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) :=
    kgfniRee_component_three ha hK hs hJ
  subst hJC
  exact fniRee_no_mem_three_C ha hK hs hφ3 hφout hφs hf'


theorem kgFieldRestrictionOn_ree : KGFieldRestrictionOn (kgfniRow .ree) := by
  intro p lab hp hp2 hlab ht3 hrow
  obtain ⟨htag, hdvd⟩ := hrow
  obtain ⟨t, l, n⟩ := lab
  have htag' : t = .twF4 := htag
  subst htag'
  obtain ⟨hn1, hl0, hnodd, hn3⟩ := hlab
  subst hl0
  have hlab0 : LargeEvenInLambda2 (⟨.twF4, 0, n⟩ : LargeEvenLabel) :=
    ⟨hn1, rfl, hnodd, hn3⟩
  have hj : n = 2 * ((n - 1) / 2) + 1 := by
    obtain ⟨k, rfl⟩ := hnodd
    simp
  have ha : 1 ≤ (n - 1) / 2 := by
    obtain ⟨k, rfl⟩ := hnodd
    have hn3' : 3 ≤ 2 * k + 1 := hn3
    have hk : 1 ≤ k := by omega
    simpa using hk
  have hrawSimple : LargeEvenLabelAll (⟨.twF4, 0, n⟩ : LargeEvenLabel)
      (fun R _ _ _ => IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) :=
    kgfni_rawSimple_twisted (⟨.twF4, 0, n⟩ : LargeEvenLabel) hlab0 (by simp [KGFNITwistedLabel])
  have hrawField : LargeEvenLabelAll (⟨.twF4, 0, n⟩ : LargeEvenLabel) (GGRawInnField p) :=
    ggRawInnFieldInput_holds p hp hp2 (⟨.twF4, 0, n⟩ : LargeEvenLabel) hlab0
  intro Q hQ
  have hQstrong : LargeEvenRawDatum (⟨.twF4, 0, n⟩ : LargeEvenLabel)
      (fun R _ I F => Q R I F ∧
        ((IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) ∧ GGRawInnField p R I F)) :=
    largeEvenLabelAll_and hrawSimple hrawField _ hQ
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQstrong ⊢
  obtain ⟨K, hF, hfin, hK, hQ', ⟨hsimple, hna⟩, hfield⟩ := hQstrong
  letI := hF
  haveI := hfin
  refine ⟨K, inferInstance, inferInstance, ?_, hQ', ?_⟩
  · exact hK
  · dsimp only [KGFieldRestrictionCont]
    intro f hf hford h hI hhp hcomm J₀ hJ f' hf'
    haveI hchar : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := by
      have h2 : CharP K 2 := CFSG.CGT.Timmesfeld75.charP_two_of_card hK
      simpa [CFSG.LieType.Ree.ReeTag.prime] using h2
    have hIinn : LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H ((n - 1) / 2) K) ⊆
        (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) →*
          MulAut (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K))).range :=
      chevIDImage_subset_inn_twF4 ha K hK
    have hInnI : ∀ r : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K),
        MulAut.conj r ∈ LargeEvenChevIDImage LargeEvenCartanF4 K
          (LargeEvenTwF4H ((n - 1) / 2) K) :=
      fun r => Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)
    have hcenter : Subgroup.center (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) = ⊥ :=
      center_twF4Row_eq_bot ha hK
    have hconj_inj : Function.Injective
        (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) →*
          MulAut (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K))) :=
      mulAut_conj_injective hcenter
    by_cases hh : h = 1
    · subst hh
      have hself : LargeEvenRawDatum (⟨.twF4, 0, n⟩ : LargeEvenLabel) (fun R' _ _ F' =>
          ∃ e : (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) ≃* R',
            F' = MulAut.congr e ''
              LargeEvenChevFieldImage LargeEvenCartanF4 K
                (LargeEvenTwF4H ((n - 1) / 2) K)) := by
        dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4]
        refine ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _, ?_⟩⟩
        ext φ
        constructor
        · intro h
          exact ⟨φ, h, by ext x; rfl⟩
        · rintro ⟨x, hx, hxφ⟩
          have hx' : (MulEquiv.refl _).trans (x.trans (MulEquiv.refl _)) = x := by
            ext y; rfl
          have hxφ' : x = φ := by simpa [hx'] using hxφ
          rwa [← hxφ']
      exact kgFieldRestriction_hOne_of_rawImage hp hp2 hlab0 hrawSimple hself f hf hford J₀ hJ
        f' hf'
    · obtain ⟨s, hs⟩ := hIinn hI
      have hord : orderOf h = p := by
        have hdvd : orderOf h ∣ p := orderOf_dvd_of_pow_eq_one hhp
        rcases hp.eq_one_or_self_of_dvd (orderOf h) hdvd with h1 | hp'
        · exfalso
          exact hh (orderOf_eq_one_iff.mp h1)
        · exact hp'
      have hsord : orderOf s = p := by
        have hconjord : orderOf (MulAut.conj s) = orderOf s :=
          orderOf_injective (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) →*
            MulAut (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K))) hconj_inj s
        rw [← hconjord, hs, hord]
      have hfnot : f ∉ LargeEvenChevIDImage LargeEvenCartanF4 K
          (LargeEvenTwF4H ((n - 1) / 2) K) :=
        (hfield hsimple hna).2.2.2 f hf hford
      obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma ha hK
      let sΓ := eR s
      let φ : MulAut (CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2)) := MulAut.congr eR f
      have hsΓ : orderOf sΓ = p := by
        show orderOf (eR s) = p
        rw [eR.orderOf_eq s, hsord]
      have hφp : φ ^ p = 1 := by
        have hfp : f ^ p = 1 := by rw [← hford]; exact pow_orderOf_eq_one f
        show (MulAut.congr eR f) ^ p = 1
        rw [← map_pow, hfp, map_one]
      have hfs : f s = s := by
        have hcomm' : MulAut.conj s * f = f * MulAut.conj s := by
          rw [hs]
          exact hcomm
        have h1 : MulAut.conj (f s) = f * MulAut.conj s * f⁻¹ := by
          rw [← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj f s]
          ext x
          simp [MulAut.congr_apply, MulAut.mul_apply]
        have h2 : MulAut.conj (f s) = MulAut.conj s := by
          calc MulAut.conj (f s) = f * MulAut.conj s * f⁻¹ := h1
            _ = MulAut.conj s := by rw [← hcomm']; group
        exact hconj_inj h2
      have hφout : ∀ g, φ ≠ MulAut.conj g := by
        intro g hg
        have hfinner : f = MulAut.conj (eR.symm g) := by
          have h := congrArg (MulAut.congr eR.symm) hg
          have h1 : MulAut.congr eR.symm (MulAut.congr eR f) = f := by
            ext x
            simp [MulAut.congr_apply, MulEquiv.trans_apply]
          have h2 : MulAut.congr eR.symm (MulAut.conj g) = MulAut.conj (eR.symm g) := by
            simpa using CFSG.ComponentClassification.OuterAutomorphisms.congr_conj eR.symm g
          rw [h1, h2] at h
          exact h
        exact hfnot (hfinner.symm ▸ hInnI (eR.symm g))
      have hφs : φ sΓ = sΓ := by
        show MulAut.congr eR f (eR s) = eR s
        rw [show MulAut.congr eR f (eR s) = eR (f s) by simp [MulAut.congr, MulEquiv.trans_apply],
          hfs]
      have hJopen : CFSG.Open.IsComponentOf J₀
          (MonoidHom.eqLocus (h : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) →* _)
            (MonoidHom.id _)) := by
        exact isComponentOf_iff_open.mp hJ
      let JΓ : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2)) :=
        J₀.map eR.toMonoidHom
      have hfix : (MonoidHom.eqLocus (h : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) →* _)
            (MonoidHom.id _)).map eR.toMonoidHom =
          CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj sΓ) := by
        rw [← hs]
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          have hy' : MulAut.conj s y = y := by simpa [hs] using hy
          show MulAut.conj sΓ (eR y) = eR y
          rw [show sΓ = eR s from rfl,
            ← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj eR s]
          simp [MulAut.congr_apply, hy']
        · intro hx
          refine ⟨eR.symm x, ?_, by simp⟩
          have := congrArg eR.symm hx
          simpa [sΓ] using this
      have hJΓ : CFSG.Open.IsComponentOf JΓ
          (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj sΓ)) := by
        have hmap := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv eR hJopen
        rw [hfix] at hmap
        exact hmap
      let eJ : J₀ ≃* JΓ := Subgroup.equivMapOfInjective J₀ eR.toMonoidHom eR.injective
      let f'Γ : MulAut JΓ := eJ.symm.trans (f'.trans eJ)
      have hf'Γ : ∀ j : JΓ,
          (f'Γ j : CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2)) = φ j := by
        intro j
        obtain ⟨j0, rfl⟩ := eJ.surjective j
        have h1' : f'Γ (eJ j0) = eJ (f' j0) := by
          show (f'.trans eJ) (eJ.symm (eJ j0)) = eJ (f' j0)
          rw [MulEquiv.symm_apply_apply]
          rfl
        have h1 : (f'Γ (eJ j0) :
            CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2)) = eR (f' j0) := by
          have h1'' := congrArg (fun x : JΓ =>
            (x : CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2))) h1'
          exact h1''.trans rfl
        have h2 : (φ (eJ j0) :
            CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2)) = eR (f j0) := by
          have h3 : (eJ j0 :
              CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2)) =
              eR (j0 : LargeEvenCenterQuot
                (LargeEvenTwF4H ((n - 1) / 2) K)) := rfl
          rw [h3]
          simp [φ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        rw [h1, h2, hf' j0]
      have hΓ : GGMarkingAll (K := JΓ)
          fun _ _ _ I _ θ => kgInducedAut θ f'Γ ∉ I := by
        have hp3 : p = 3 ∨ 5 ≤ p := by
          have hp4 : p ≠ 4 := by
            intro h
            subst h
            norm_num at hp
          have h3 : 3 ≤ p := by
            have := hp.two_le
            omega
          rcases eq_or_lt_of_le h3 with h | h
          · left; omega
          · right; omega
        rcases hp3 with rfl | hp5
        · exact fniRee_no_mem_three ha hK hsΓ hφp hφout hφs hJΓ hf'Γ
        · exact fniRee_no_mem_ge5 ha hK hp hp5 hsΓ hφp hφout hφs hJΓ hf'Γ
      exact ggMarkingAll_congr eJ.symm
        (Q := fun _ _ _ I _ θ => kgInducedAut θ f'Γ ∉ I)
        (Q' := fun _ _ _ I _ θ => kgInducedAut θ f' ∉ I)
        (fun lab R' _ I' F' θ hmem => by
          simpa [centerQuotCongr_symm, f'Γ, kgfniRee_kgInducedAut_congr eJ θ f'] using hmem) hΓ

end CFSG.StandardType

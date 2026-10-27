module

public import CFSG.RankThree.PartTwo.Sec15.Item156Proof
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec15.Wales154KJ2
import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofTwoInner
import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofPoint
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec18.Components

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev act (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom

private theorem act_apply {L : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hx : x ∈ L) :
    act L ⟨g, hg⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨x, hx⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)
        ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hx⟩ := rfl

private theorem act_eq_one_iff {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    act L ⟨g, hg⟩ = 1 ↔ g ∈ Sec4.thetaQuotCentralizer L := by
  constructor
  · intro h
    exact ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr h, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    have : y = ⟨g, hg⟩ := Subtype.ext hyg
    rw [← this]
    exact MonoidHom.mem_ker.mp hy

private theorem act_mem_normalizer {L U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    act L ⟨g, hg⟩ ∈ Subgroup.normalizer
      (((U.subgroupOf (Subgroup.normalizer (L : Set G))).map (act L) : Subgroup _) : Set _) := by
  refine Subgroup.le_normalizer_map (act L) ⟨⟨g, hg⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hgU x

private theorem facts_of_j2
    {Q : Type} [Group Q] [Finite Q]
    (hQ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.J2)) {E Ks : Subgroup Q}
    (hE9 : Nat.card E = 9) (hKs1 : Ks ≠ ⊥) (hKsp : Group.IsPerfect Ks)
    (hEK : E ≤ Subgroup.normalizer (Ks : Set Q)) {P : Subgroup (MulAut Q)} (hP2 : IsPGroup 2 P)
    (hEP : E.map (MulAut.conj : Q →* MulAut Q) ≤ Subgroup.normalizer (P : Set (MulAut Q)))
    (hKP : Ks.map (MulAut.conj : Q →* MulAut Q) ≤ Subgroup.normalizer (P : Set (MulAut Q))) :
    P ≤ (MulAut.conj : Q →* MulAut Q).range ∧
      (∀ k ∈ Ks, ∀ u ∈ P, MulAut.conj k * u = u * MulAut.conj k) ∧
      ∀ e ∈ E, ∀ u ∈ P, u ≠ 1 → MulAut.conj e * u = u * MulAut.conj e →
        e ∈ Ks ∧ Nonempty (Ks ≃* alternatingGroup (Fin 5)) := by
  classical
  obtain ⟨φJ⟩ := hQ
  have hZ : Subgroup.center Q = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φJ⟩
  have hconj := Wales154.conj_injective_of_center_eq_bot hZ
  have hinn : P ≤ (MulAut.conj : Q →* MulAut Q).range :=
    Sec16.ks162J2TwoInner Q ⟨φJ⟩ E hE9 P hP2 hEP
  refine ⟨hinn, ?_⟩
  by_cases hbot : P = ⊥
  · subst hbot
    refine ⟨fun k _ u hu => ?_, fun e _ u hu hu1 _ => absurd (Subgroup.mem_bot.mp hu) hu1⟩
    rw [Subgroup.mem_bot] at hu
    subst hu
    simp
  · set Rs := P.comap (MulAut.conj : Q →* MulAut Q)
    have hRsmap : Rs.map (MulAut.conj : Q →* MulAut Q) = P := Subgroup.map_comap_eq_self hinn
    have hRs1 : Rs ≠ ⊥ := by
      intro h1
      apply hbot
      rw [← hRsmap, h1, Subgroup.map_bot]
    have hRs2 : IsPGroup 2 Rs := hP2.of_equiv
      ((Subgroup.equivMapOfInjective Rs _ hconj).trans (MulEquiv.subgroupCongr hRsmap)).symm
    have hEN : E ≤ Subgroup.normalizer (Rs : Set Q) := fun e he =>
      Wales154.mem_normalizer_comap_conj (hEP (Subgroup.mem_map_of_mem _ he))
    have hKN : Ks ≤ Subgroup.normalizer (Rs : Set Q) := fun k hk =>
      Wales154.mem_normalizer_comap_conj (hKP (Subgroup.mem_map_of_mem _ hk))
    have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
    obtain ⟨hRs4, -, ⟨eK⟩, hfix⟩ := Wales154.ks154J2PerfNorm_of_four Wales154.ks154J2Four Q
      ⟨φJ⟩ E Ks Rs hE3 hE9.ge hKs1 hKsp hEK hRs1 hRs2 hEN hKN
    have hKC : Ks ≤ Subgroup.centralizer (Rs : Set Q) :=
      Proof155w3.le_centralizer_of_isPerfect_of_card_four hKsp hKN hRs4
    refine ⟨fun k hk u hu => ?_, fun e he u hu hu1 hcomm => ?_⟩
    · rw [← hRsmap] at hu
      obtain ⟨s, hs, rfl⟩ := hu
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hKC hk) s hs]
    · rw [← hRsmap] at hu
      obtain ⟨s, hs, rfl⟩ := hu
      have hs1 : s ≠ 1 := fun h1 => hu1 (by rw [h1, map_one])
      have hes : e * s = s * e := hconj (by rw [map_mul, map_mul]; exact hcomm)
      exact ⟨hfix e he s hs hs1 hes, ⟨eK⟩⟩

private theorem eq_one_of_commutator_mem {Q : Type} [Group Q] {Ks T : Subgroup Q}
    (eK : Ks ≃* alternatingGroup (Fin 5)) (hTK : T ≤ Ks)
    (hTN : Ks ≤ Subgroup.normalizer (T : Set Q)) (hT2 : IsPGroup 2 T) {e : Q} (heK : e ∈ Ks)
    (h : ∀ s ∈ Ks, e * s * e⁻¹ * s⁻¹ ∈ T) : e = 1 := by
  classical
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hsimple : IsSimpleGroup Ks := eK.isSimpleGroup
  have hTn : (T.subgroupOf Ks).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTK).mpr hTN
  have hT1 : ∀ t ∈ T, t = 1 := by
    rcases hTn.eq_bot_or_eq_top with hb | ht
    · intro t htT
      have : (⟨t, hTK htT⟩ : Ks) ∈ T.subgroupOf Ks := Subgroup.mem_subgroupOf.mpr htT
      rw [hb, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have h2 : IsPGroup 2 (T.subgroupOf Ks) :=
        hT2.comap_of_injective Ks.subtype Ks.subtype_injective
      rw [ht] at h2
      have h2' : IsPGroup 2 (alternatingGroup (Fin 5)) :=
        (h2.of_equiv Subgroup.topEquiv).of_equiv eK
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2'
      rw [card_alternatingGroup_five] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hZ : Subgroup.center Ks = ⊥ := by
    have hZA : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have hmap := Subgroup.map_center_eq eK
    rw [hZA] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ eK.injective).mp hmap
  have heZ : (⟨e, heK⟩ : Ks) ∈ Subgroup.center Ks := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have h1 := hT1 _ (h s s.2)
    change (s : Q) * e = e * (s : Q)
    have h2 : e * (s : Q) * e⁻¹ = (s : Q) := mul_inv_eq_one.mp h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  rw [hZ, Subgroup.mem_bot] at heZ
  exact congrArg Subtype.val heZ

private theorem exists_perfect_cover {A X Lf : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAL : A ≤ Subgroup.normalizer (Lf : Set G))
    (hXp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hcov : X ≤ (X ⊓ Lf) ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    ∃ K : Subgroup G, K ≤ X ⊓ Lf ∧ X ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
      Group.IsPerfect K ∧ A ≤ Subgroup.normalizer (K : Set G) := by
  have hW := Proof152Gen.map_subgroupOf_eq_top_of_le_sup (inf_le_left : X ⊓ Lf ≤ X) hcov
  obtain ⟨D, hDW, hDp, hDtop⟩ := Proof152Gen.exists_isPerfect_cover hXp hW
  have hDK : D ≤ inSubgroup perfectResidual (X ⊓ Lf) :=
    Sec18.le_inSubgroup_perfectResidual (Subgroup.isPerfect_iff.mp hDp) hDW
  have : (perfectResidual ↥(X ⊓ Lf)).Characteristic :=
    (CFSG.perfect_residual_characterization (G := ↥(X ⊓ Lf))).2.1
  refine ⟨inSubgroup perfectResidual (X ⊓ Lf), Subgroup.map_subtype_le _, ?_,
    Subgroup.isPerfect_iff.mpr (Sec18.commutator_inSubgroup_perfectResidual _),
    (Late.le_normalizer_inf hAX hAL).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)⟩
  refine Proof155w.le_sup_theta_of_map_eq_top (eq_top_iff.mpr ?_)
  rw [← hDtop]
  exact Subgroup.map_mono (Subgroup.comap_mono hDK)

private theorem card_map_act {A Lf : Subgroup G} {f : G}
    (hAN : A ≤ Subgroup.normalizer (Lf : Set G)) (hA27 : Nat.card A = 27) (hfA : f ∈ A)
    (hf3 : Nat.card (Subgroup.zpowers f) = 3)
    (hker : ∀ a ∈ A, a ∈ Sec4.thetaQuotCentralizer Lf ↔ a ∈ Subgroup.zpowers f) :
    Nat.card ((A.subgroupOf (Subgroup.normalizer (Lf : Set G))).map (act Lf)) = 9 := by
  classical
  set fA : ↥A →* MulAut (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf) :=
    (act Lf).comp (Subgroup.inclusion hAN) with hfA'
  have hrange : fA.range = (A.subgroupOf (Subgroup.normalizer (Lf : Set G))).map (act Lf) := by
    rw [hfA', MonoidHom.range_comp, Subgroup.inclusion_range]
  have hcard : Nat.card A = Nat.card fA.ker * Nat.card fA.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup fA.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange fA).toEquiv]
  have hkermap : fA.ker.map A.subtype = Subgroup.zpowers f := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hker a a.2).mp ((act_eq_one_iff (hAN a.2)).mp (MonoidHom.mem_ker.mp ha))
    · intro hx
      have hxA : x ∈ A := Subgroup.zpowers_le.mpr hfA hx
      exact ⟨⟨x, hxA⟩, MonoidHom.mem_ker.mpr ((act_eq_one_iff (hAN hxA)).mpr ((hker x hxA).mpr hx)),
        rfl⟩
  have hkercard : Nat.card fA.ker = 3 := by
    have h := Subgroup.card_map_of_injective (K := fA.ker) A.subtype_injective
    rw [hkermap, hf3] at h
    exact h.symm
  rw [← hrange]
  rw [hkercard, hA27] at hcard
  omega

private theorem core
    {A Lf U K P₀ : Subgroup G} {f d : G}
    (hJ : Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAN : A ≤ Subgroup.normalizer (Lf : Set G)) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hA27 : Nat.card A = 27) (hfA : f ∈ A) (hf3 : Nat.card (Subgroup.zpowers f) = 3)
    (hker : ∀ a ∈ A, a ∈ Sec4.thetaQuotCentralizer Lf ↔ a ∈ Subgroup.zpowers f)
    (hU2 : IsPGroup 2 U) (hUN : U ≤ Subgroup.normalizer (Lf : Set G))
    (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hfaith : U ⊓ Sec4.thetaQuotCentralizer Lf = ⊥)
    (hKL : K ≤ Lf) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKA : A ≤ Subgroup.normalizer (K : Set G)) (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (hdA : d ∈ A) (hP₀2 : IsPGroup 2 P₀) (hKP₀ : K ≤ Subgroup.normalizer (P₀ : Set G))
    (hdK : ∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ P₀) :
    (∀ k ∈ K, ∀ u ∈ U, k * u = u * k) ∧
      ∀ u ∈ U, u ≠ 1 → d * u = u * d → d ∈ Sec4.thetaQuotCentralizer Lf := by
  classical
  obtain ⟨φJ⟩ := hJ
  set θ := aschbacherSolvableCore 3 ↥Lf
  set ρ := QuotientGroup.mk' θ
  set N := Subgroup.normalizer (Lf : Set G)
  set R := (U.subgroupOf N).map (act Lf)
  set Ab := (A.subgroupOf N).map (act Lf)
  have hZ : Subgroup.center (↥Lf ⧸ θ) = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φJ⟩
  have hconj := Wales154.conj_injective_of_center_eq_bot hZ
  have hAb9 : Nat.card Ab = 9 := card_map_act hAN hA27 hfA hf3 hker
  have hAinn : Ab ≤ (MulAut.conj : (↥Lf ⧸ θ) →* MulAut (↥Lf ⧸ θ)).range := by
    rintro _ ⟨a, ha, rfl⟩
    refine Proof155w3.mem_range_conj_of_pow_three ⟨φJ⟩ ?_
    rw [← map_pow]
    have ha3 : a ^ 3 = 1 := Subtype.ext (hA3 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [ha3, map_one]
  set E := Ab.comap (MulAut.conj : (↥Lf ⧸ θ) →* MulAut (↥Lf ⧸ θ))
  have hEmap : E.map (MulAut.conj : (↥Lf ⧸ θ) →* MulAut (↥Lf ⧸ θ)) = Ab :=
    Subgroup.map_comap_eq_self hAinn
  have hEcard : Nat.card E = Nat.card Ab := by
    rw [← hEmap, Subgroup.card_map_of_injective hconj]
  have hE9 : Nat.card E = 9 := hEcard.trans hAb9
  set Ks := (K.subgroupOf Lf).map ρ
  have hKsmem : ∀ x (hx : x ∈ K), ρ ⟨x, hKL hx⟩ ∈ Ks := fun x hx =>
    ⟨⟨x, hKL hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hKs1 : Ks ≠ ⊥ := by
    intro hbot
    apply hK1
    have hKθ : K.subgroupOf Lf ≤ θ := by
      intro x hx
      have h1 : ρ x ∈ Ks := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hθsol : Group.IsSolvable θ :=
      (solvable_prime_complement_core_characterization (H := ↥Lf) Nat.prime_three).1
    have hKsol' : Group.IsSolvable (K.subgroupOf Lf) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKθ)
    have hKsol : Group.IsSolvable K := Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom) (MulEquiv.surjective _)
    by_contra hne
    have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
    have := hKp
    exact Group.IsPerfect.not_isSolvable K hKsol
  have hKsp : Group.IsPerfect Ks := by
    have : Group.IsPerfect (K.subgroupOf Lf) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.IsPerfect.map ρ
  have hEK : E ≤ Subgroup.normalizer (Ks : Set (↥Lf ⧸ θ)) := by
    intro e he
    obtain ⟨a, ha, hae⟩ := (Subgroup.mem_comap.mp he : MulAut.conj e ∈ Ab)
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    obtain ⟨⟨x, hxL⟩, hxK, rfl⟩ := hs
    have hxK' : x ∈ K := Subgroup.mem_subgroupOf.mp hxK
    have h1 : e * ρ ⟨x, hxL⟩ * e⁻¹ = act Lf a (ρ ⟨x, hxL⟩) := by
      rw [hae, MulAut.conj_apply]
    rw [h1, act_apply a.2 hxL]
    exact ⟨⟨_, (Subgroup.mem_normalizer_iff.mp a.2 x).mp hxL⟩,
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hKA haA) x).mp hxK'), rfl⟩
  have hR2 : IsPGroup 2 R :=
    (hU2.comap_of_injective N.subtype N.subtype_injective).map (act Lf)
  have hEP : E.map (MulAut.conj : (↥Lf ⧸ θ) →* MulAut (↥Lf ⧸ θ)) ≤
      Subgroup.normalizer (R : Set (MulAut (↥Lf ⧸ θ))) := by
    rw [hEmap]
    rintro _ ⟨a, ha, rfl⟩
    exact act_mem_normalizer a.2 (hAU (Subgroup.mem_subgroupOf.mp ha))
  have hKP : Ks.map (MulAut.conj : (↥Lf ⧸ θ) →* MulAut (↥Lf ⧸ θ)) ≤
      Subgroup.normalizer (R : Set (MulAut (↥Lf ⧸ θ))) := by
    rintro _ ⟨s, ⟨⟨x, hxL⟩, hxK, rfl⟩, rfl⟩
    have hxK' : x ∈ K := Subgroup.mem_subgroupOf.mp hxK
    have hxN : x ∈ N := Subgroup.le_normalizer hxL
    have h1 : act Lf ⟨x, hxN⟩ = MulAut.conj (ρ ⟨x, hxL⟩) := Proof156.thetaQuotMulAut_eq_conj hxL
    rw [← h1]
    exact act_mem_normalizer hxN (hKU hxK')
  obtain ⟨hinn, hcent, hfix⟩ := facts_of_j2 ⟨φJ⟩ hE9 hKs1 hKsp hEK hR2 hEP hKP
  refine ⟨fun k hk u hu => ?_, fun u hu hu1 hdu => ?_⟩
  ·
    have hkL : k ∈ Lf := hKL hk
    have hkN : k ∈ N := Subgroup.le_normalizer hkL
    have huN : u ∈ N := hUN hu
    have hcU : k * u * k⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKU hk) u).mp hu) (U.inv_mem hu)
    have hcN : k * u * k⁻¹ * u⁻¹ ∈ N := hUN hcU
    have h1 : act Lf ⟨k * u * k⁻¹ * u⁻¹, hcN⟩ = 1 := by
      have e1 : (⟨k * u * k⁻¹ * u⁻¹, hcN⟩ : ↥N) =
          ⟨k, hkN⟩ * ⟨u, huN⟩ * ⟨k, hkN⟩⁻¹ * ⟨u, huN⟩⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hk' : act Lf ⟨k, hkN⟩ = MulAut.conj (ρ ⟨k, hkL⟩) :=
        Proof156.thetaQuotMulAut_eq_conj hkL
      have hv : act Lf ⟨u, huN⟩ ∈ R := ⟨⟨u, huN⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
      have hcm := hcent (ρ ⟨k, hkL⟩) (hKsmem k hk) _ hv
      rw [hk']
      calc MulAut.conj (ρ ⟨k, hkL⟩) * act Lf ⟨u, huN⟩ * (MulAut.conj (ρ ⟨k, hkL⟩))⁻¹ *
            (act Lf ⟨u, huN⟩)⁻¹
          = (act Lf ⟨u, huN⟩ * MulAut.conj (ρ ⟨k, hkL⟩)) * (MulAut.conj (ρ ⟨k, hkL⟩))⁻¹ *
            (act Lf ⟨u, huN⟩)⁻¹ := by rw [hcm]
        _ = 1 := by group
    have hmem : k * u * k⁻¹ * u⁻¹ ∈ U ⊓ Sec4.thetaQuotCentralizer Lf :=
      ⟨hcU, (act_eq_one_iff hcN).mp h1⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    calc k * u = k * u * k⁻¹ * u⁻¹ * (u * k) := by group
      _ = u * k := by rw [hmem, one_mul]
  ·
    have huN : u ∈ N := hUN hu
    have hdN : d ∈ N := hAN hdA
    have hφu : act Lf ⟨u, huN⟩ ≠ 1 := by
      intro h1
      have hmem : u ∈ U ⊓ Sec4.thetaQuotCentralizer Lf := ⟨hu, (act_eq_one_iff huN).mp h1⟩
      rw [hfaith, Subgroup.mem_bot] at hmem
      exact hu1 hmem
    have hφuR : act Lf ⟨u, huN⟩ ∈ R := ⟨⟨u, huN⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    have hφd : act Lf ⟨d, hdN⟩ ∈ Ab := ⟨⟨d, hdN⟩, Subgroup.mem_subgroupOf.mpr hdA, rfl⟩
    obtain ⟨e, he⟩ := hAinn hφd
    have heE : e ∈ E := by
      show MulAut.conj e ∈ Ab
      rw [he]
      exact hφd
    have hcomm : MulAut.conj e * act Lf ⟨u, huN⟩ = act Lf ⟨u, huN⟩ * MulAut.conj e := by
      rw [he, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hdu
    obtain ⟨heKs, ⟨eK⟩⟩ := hfix e heE _ hφuR hφu hcomm
    set T := ((K ⊓ P₀).subgroupOf Lf).map ρ
    have hTK : T ≤ Ks := Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
    have hTN : Ks ≤ Subgroup.normalizer (T : Set (↥Lf ⧸ θ)) := by
      intro s hs
      refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      obtain ⟨⟨x, hxL⟩, hxK, rfl⟩ := hs
      obtain ⟨⟨p, hpL⟩, hpP, rfl⟩ := ht
      have hxK' : x ∈ K := Subgroup.mem_subgroupOf.mp hxK
      have hpP' : p ∈ K ⊓ P₀ := Subgroup.mem_subgroupOf.mp hpP
      have hxpL : x * p * x⁻¹ ∈ Lf := Lf.mul_mem (Lf.mul_mem hxL hpL) (Lf.inv_mem hxL)
      refine ⟨⟨x * p * x⁻¹, hxpL⟩, Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact K.mul_mem (K.mul_mem hxK' hpP'.1) (K.inv_mem hxK')
      · exact (Subgroup.mem_normalizer_iff.mp (hKP₀ hxK') p).mp hpP'.2
      · rw [← map_inv, ← map_mul, ← map_mul]
        rfl
    have hT2 : IsPGroup 2 T :=
      ((hP₀2.to_le inf_le_right).comap_of_injective Lf.subtype Lf.subtype_injective).map ρ
    have hcomm_e : ∀ s ∈ Ks, e * s * e⁻¹ * s⁻¹ ∈ T := by
      rintro _ ⟨⟨x, hxL⟩, hxK, rfl⟩
      have hxK' : x ∈ K := Subgroup.mem_subgroupOf.mp hxK
      have hdxL : d * x * d⁻¹ ∈ Lf := (Subgroup.mem_normalizer_iff.mp hdN x).mp hxL
      have hdxK : d * x * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKA hdA) x).mp hxK'
      have hcL : d * x * d⁻¹ * x⁻¹ ∈ Lf := Lf.mul_mem hdxL (Lf.inv_mem hxL)
      have hcK : d * x * d⁻¹ * x⁻¹ ∈ K := K.mul_mem hdxK (K.inv_mem hxK')
      refine ⟨⟨d * x * d⁻¹ * x⁻¹, hcL⟩, Subgroup.mem_subgroupOf.mpr ⟨hcK, hdK x hxK'⟩, ?_⟩
      have h1 : e * ρ ⟨x, hxL⟩ * e⁻¹ = ρ ⟨d * x * d⁻¹, hdxL⟩ := by
        rw [← MulAut.conj_apply, he]
        exact act_apply hdN hxL
      calc ρ ⟨d * x * d⁻¹ * x⁻¹, hcL⟩ = ρ ⟨d * x * d⁻¹, hdxL⟩ * (ρ ⟨x, hxL⟩)⁻¹ := by
            rw [← map_inv, ← map_mul]
            rfl
        _ = e * ρ ⟨x, hxL⟩ * e⁻¹ * (ρ ⟨x, hxL⟩)⁻¹ := by rw [h1]
    have he1 : e = 1 := eq_one_of_commutator_mem eK hTK hTN hT2 heKs hcomm_e
    have hφd1 : act Lf ⟨d, hdN⟩ = 1 := by rw [← he, he1, map_one]
    exact (act_eq_one_iff hdN).mp hφd1

private theorem mem_zpowers_of_mem_zpowers {f d : G} (hf3 : Nat.card (Subgroup.zpowers f) = 3)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hdf : d ∈ Subgroup.zpowers f) : f ∈ Subgroup.zpowers d := by
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hle : Subgroup.zpowers d ≤ Subgroup.zpowers f := Subgroup.zpowers_le.mpr hdf
  have heq : Subgroup.zpowers d = Subgroup.zpowers f :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hf3, Nat.card_zpowers, hdord])
  exact heq ▸ Subgroup.mem_zpowers f

theorem exists_centralizes_cq_of_point
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h142 : Item142AllS14)
    {Y : Subgroup G} {c₀ : G} {L₀ : Subgroup G} {d : G} {X₁ : Subgroup G}
    (D : Data156 A (lB A) Y c₀ L₀ d X₁)
    (hX5 : Nonempty (↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* alternatingGroup (Fin 5)))
    {M : Subgroup G} (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    {f : G} {Lf : Subgroup G} (hfΩ : Subgroup.zpowers f ∈ omegaA A)
    (hfcd : f ∈ Subgroup.closure ({c₀, d} : Set G)) (hfd : f ∉ Subgroup.zpowers d)
    (hLf : Lf ∈ lA A f)
    (hJf : Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hfaith : CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) ⊓
      Sec4.thetaQuotCentralizer Lf = ⊥) :
    ∃ K : Subgroup G, K ≤ X₁ ⊓ Lf ∧ X₁ ≤ K ⊔ CFSG.Open.pCoreOf 2 X₁ ∧
      K ≤ Subgroup.centralizer
        ((CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) : Set G) ∧
      CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G) = ⊥ := by
  classical
  have hf : Sec14Std G A f Lf := { h with zpowers_mem_omegaA := hfΩ, mem_lA := hLf }
  have hS13 := hf.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  obtain ⟨hAX, hXΔ, hθO, hXq, -, hX3, hcent, -, -, hAnc⟩ := Proof156.facts_of_data156 D hA
  have hfsc : f ∈ Late.sectionCentralizer A X₁ (inSubgroup (aschbacherSolvableCore 3) X₁) := by
    rw [hcent]
    exact hfcd
  have hfC := Proof156.mem_thetaQuotCentralizer_of_mem_sectionCentralizer hAX hfsc
  have hcov :=
    Proof156.le_inf_sup_theta_of_item142 hf hJf (h142 G A f Lf hf) hAX hXΔ hXq hX3 hfC hAnc
  obtain ⟨K, hKW, hKcov, hKp, hKA⟩ := exists_perfect_cover hAX hS13.le_normalizer hXq.1 hcov
  rw [hθO] at hKcov
  have hKX : K ≤ X₁ := hKW.trans inf_le_left
  have hKL : K ≤ Lf := hKW.trans inf_le_right
  have hXM : X₁ ≤ M := fun x hx => hM.2 (Subgroup.mem_sup_left (D.le_x hx))
  have hAM : A ≤ M := fun a ha => hM.2 (Subgroup.mem_sup_right ha)
  have hMQ : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hLC : Lf ≤ Subgroup.centralizer ({f} : Set G) := hS13.le_centralizer
  have hAC : A ≤ Subgroup.centralizer ({f} : Set G) := hS13.A_le_centralizer
  have hCN : Subgroup.centralizer ({f} : Set G) ≤ Subgroup.normalizer (Lf : Set G) :=
    Sec14.centralizer_le_normalizer_of_j2 hf hJf
  set U := CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G)
  have hU2 : IsPGroup 2 U :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le inf_le_left
  have hUN : U ≤ Subgroup.normalizer (Lf : Set G) := inf_le_right.trans hCN
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    Late.le_normalizer_inf (hAM.trans hMQ) (hAC.trans Subgroup.le_normalizer)
  have hKU : K ≤ Subgroup.normalizer (U : Set G) :=
    Late.le_normalizer_inf ((hKX.trans hXM).trans hMQ)
      ((hKL.trans hLC).trans Subgroup.le_normalizer)
  have hker : ∀ a ∈ A, a ∈ Sec4.thetaQuotCentralizer Lf ↔ a ∈ Subgroup.zpowers f := by
    intro a ha
    constructor
    · intro hθ
      have h1 : a ∈ Late.sectionCentralizer A Lf ((aschbacherSolvableCore 3 Lf).map Lf.subtype) :=
        Proof156.mem_sectionCentralizer_of_mem_thetaQuotCentralizer ha hθ
      rw [hS13.sectionCentralizer_eq] at h1
      exact h1
    · intro hz
      have hfN : f ∈ Subgroup.normalizer (Lf : Set G) :=
        hCN (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      have hfθ : f ∈ Sec4.thetaQuotCentralizer Lf := by
        refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hfN, fun l hl => ?_⟩
        have hlf : l * f = f * l := Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
        rw [← hlf, mul_inv_cancel_right, inv_mul_cancel]
        exact Subgroup.one_mem _
      exact (Subgroup.zpowers_le.mpr hfθ) hz
  have hK1 : K ≠ ⊥ := by
    intro hbot
    obtain ⟨e⟩ := hX5
    have hcard : Nat.card (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) = 60 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]
    have htop : CFSG.pCore 2 ↥X₁ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ CFSG.Open.pCoreOf 2 X₁ := by
        have h1 := hKcov x.2
        rwa [hbot, bot_sup_eq] at h1
      exact (CFSG.mem_openPCoreOf_iff x).mp hx
    have h1 : (CFSG.pCore 2 ↥X₁).index = 1 := by
      rw [htop]
      exact Subgroup.index_top
    have h2 : Nat.card (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) = 1 := h1
    omega
  have hdsc : d ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem c₀ (Set.mem_singleton d))
  obtain ⟨hcen, hd⟩ := core hJf hS13.le_normalizer hS13.isElemAbelian.2 hS13.card_eq
    hS13.mem_A hS13.card_zpowers hker hU2 hUN hAU hfaith hKL hKU hKA hKp hK1 D.mem_d
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X₁)
    (hKX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X₁))
    (fun k hk => hdsc.2 k (hKX hk))
  refine ⟨K, hKW, hKcov, fun k hk => ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hcen k hk u hu).symm
  · rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    by_contra hu1
    have hdu : d * u = u * d := (Subgroup.mem_centralizer_singleton_iff.mp hu.2).symm
    have hdf : d ∈ Subgroup.zpowers f := (hker d D.mem_d).mp (hd u hu.1 hu1 hdu)
    exact hfd (mem_zpowers_of_mem_zpowers hS13.card_zpowers (hS13.isElemAbelian.2 d D.mem_d)
      D.ne_d hdf)

end CFSG.RankThree.PartTwo.Sec15.Liebeck156

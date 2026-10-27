module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NThmA
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Data
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
open scoped commutatorElement Pointwise

private theorem teNSyl_wordAct_fix
    {k : Type} [Field k] (θ : k →+* k)
    (ω : List (Fin (twistedDatum k θ).rank))
    (h : ∀ i ∈ ω, reflection (twistedDatum k θ).cartan i
        (twE6Alpha : Fin (twistedDatum k θ).rank → ℤ) = twE6Alpha) :
    wordAct (fun i => (reflection (twistedDatum k θ).cartan i).toAddMonoidHom) ω
      (twE6Alpha : Fin (twistedDatum k θ).rank → ℤ) = twE6Alpha := by
  induction ω with
  | nil => rfl
  | cons i l ih =>
    simp only [wordAct]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem i hj))]
    exact h i List.mem_cons_self

private theorem teNSyl_reflection_fix_w0L :
    ∀ i ∈ ([nf 0, nf 1, nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2] : List (Fin (Tag.rank .F4))),
      reflection (Tag.cartan .F4) i twE6Alpha = twE6Alpha := by
  decide +kernel

private theorem teNSyl_w0L_alpha
    {k : Type} [Field k] (θ : k →+* k) :
    weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ) twE6Alpha = twE6Alpha := by
  change weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ)
      (twE6Alpha : Fin (twistedDatum k θ).rank → ℤ) = twE6Alpha
  rw [twE6W0L]
  set ω : List (Fin (twistedDatum k θ).rank) :=
    [nf 0, nf 1, nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2] with hω
  have hwp := CFSG.LieType.Steinberg.OfCartan.weylAction_wordProd
    (A := (twistedDatum k θ).cartan) (twistedDatum k θ).isFiniteType
    (ω := ω) (v := (twE6Alpha : Fin (twistedDatum k θ).rank → ℤ))
  refine hwp.trans ?_
  rw [hω]
  refine teNSyl_wordAct_fix θ _ (fun i hi => ?_)
  exact teNSyl_reflection_fix_w0L i hi

private theorem teNSyl_longPos0_cases {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ twE6LongPos0) :
    γ = ![0, 1, 0, 0] ∨ γ = ![0, 1, 2, 0] ∨ γ = ![1, 0, 0, 0] ∨ γ = ![1, 1, 0, 0] ∨
      γ = ![1, 1, 2, 0] ∨ γ = ![1, 2, 2, 0] := by
  simp only [twE6LongPos0, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  tauto

private theorem teNSyl_longPos0_isRoot
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ twE6LongPos0) : IsRoot .F4 γ := by
  rcases teNSyl_longPos0_cases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (StringData.memDec_iff (Tag.rootCertificate_check .F4)
      (Tag.stringData_check .F4)).1 (by change memF4 _ = true; decide +kernel)

private theorem teNSyl_longPos0_last {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ twE6LongPos0) : γ twE6Last = 0 := by
  rcases teNSyl_longPos0_cases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem teNSyl_longPos0_ht_ge_one {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ twE6LongPos0) : 1 ≤ ht γ := by
  rcases teNSyl_longPos0_cases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem teNSyl_longPos0_ne_zero {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ twE6LongPos0) : γ ≠ 0 := by
  intro h
  have h1 := teNSyl_longPos0_ht_ge_one hγ
  rw [h] at h1
  simp only [ht, Pi.zero_apply, Finset.sum_const_zero] at h1
  omega

private theorem teNSyl_alpha_last : twE6Alpha twE6Last = 2 := by decide +kernel

private theorem teNSyl_alpha_ht : ht twE6Alpha = 8 := by decide +kernel

private theorem teNSyl_longPos0_linIndep {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ twE6LongPos0) : LinIndepPair γ twE6Alpha := by
  intro a b hab
  have hcoord : (b : ℤ) * 2 = 0 := by
    have h := congrFun hab twE6Last
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      teNSyl_longPos0_last hγ, teNSyl_alpha_last, mul_zero, zero_add] at h
    exact h
  have hb : b = 0 := by omega
  refine ⟨?_, hb⟩
  have hsmul : a • γ = 0 := by
    rw [← hab, hb, zero_smul, add_zero]
  exact (smul_eq_zero.1 hsmul).resolve_right (teNSyl_longPos0_ne_zero hγ)

private theorem teNSyl_f4_level_le_two :
    ∀ v ∈ rootFinset Tag.F4, v twE6Last ≤ 2 := by decide +kernel

private theorem teNSyl_f4_height_le :
    ∀ v ∈ rootFinset Tag.F4, ht v ≤ 11 := by decide +kernel

private theorem teNSyl_no_longPos0_add_alpha
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ twE6LongPos0) {a b : ℕ}
    (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hb : b = 1) :
    ¬ IsRoot .F4 (a • γ + b • twE6Alpha) := by
  subst hb
  rcases teNSyl_longPos0_cases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases a <;>
    exact fun h => by
      have h' := (StringData.memDec_iff (Tag.rootCertificate_check .F4)
        (Tag.stringData_check .F4)).2 h
      change memF4 _ = true at h'
      exact absurd h' (by decide +kernel)

private theorem teNSyl_openCone_empty
    {k : Type} [Field k] (θ : k →+* k)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ twE6LongPos0) :
    openCone (twistedDatum k θ).roots γ twE6Alpha = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  rw [twistedDatum_roots] at hε
  have hlev : (a • γ + b • twE6Alpha) twE6Last = (b : ℤ) * 2 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, teNSyl_longPos0_last hγ,
      teNSyl_alpha_last, mul_zero, zero_add]
    ring
  have hb1 : b = 1 := by
    have h := teNSyl_f4_level_le_two _ (mem_rootFinset.2 hε)
    omega
  have hht : ht (a • γ + b • twE6Alpha) =
      (a : ℤ) * ht γ + (b : ℤ) * ht twE6Alpha := by
    simp only [ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> try exact Finset.sum_congr rfl fun x _ => by ring
  have ha3 : a ≤ 3 := by
    have hle := teNSyl_f4_height_le _ (mem_rootFinset.2 hε)
    have hle' : (a : ℤ) * ht γ + (b : ℤ) * ht twE6Alpha ≤ 11 := hht ▸ hle
    rw [hb1, teNSyl_alpha_ht] at hle'
    norm_num at hle'
    have hγ1 := teNSyl_longPos0_ht_ge_one hγ
    nlinarith [hle', hγ1]
  exact teNSyl_no_longPos0_add_alpha hγ (Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 ha))
    ha3 hb1 hε

private theorem teNSyl_commute_longPos0_alpha
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ twE6LongPos0) :
    ∀ x ∈ (twistedDatum k θ).rootGroup γ,
      ∀ y ∈ (twistedDatum k θ).rootGroup twE6Alpha, Commute x y := by
  intro x hx y hy
  have hγroot : γ ∈ (twistedDatum k θ).roots := by
    rw [twistedDatum_roots]
    exact teNSyl_longPos0_isRoot hγ
  have hαroot : twE6Alpha ∈ (twistedDatum k θ).roots := twE6_alpha_mem_roots θ
  have hli : LinIndepPair γ twE6Alpha := teNSyl_longPos0_linIndep hγ
  have hc := (twistedDatum_steinbergExtras θ hθ).commutator_mem γ hγroot twE6Alpha hαroot hli
    x hx y hy
  have hempty : openCone (twistedDatum k θ).roots γ twE6Alpha = ∅ :=
    teNSyl_openCone_empty θ hγ
  rw [hempty] at hc
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at hc
  exact commutatorElement_eq_one_iff_commute.1 hc

theorem twE6Rad_le_pCoreOf_normalizer
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Rad θ ≤ pCoreOf 2 (twE6NA θ) := by
  refine GGRootNorm.le_pCoreOf_of_normalized (twE6Rad_le_normalizer_alpha θ)
    (isPGroup_two_twE6Rad θ hθ) ?_
  intro m hm t ht
  exact (Subgroup.mem_normalizer_iff.mp (twE6_normalizer_alpha_le θ hθ hm) t).mp ht

theorem twE6UM_le_normalizer_alpha
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6UM θ ≤ twE6NA θ := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  have hx' : x ∈ ⨆ γ ∈ twE6LongPos0, (twistedDatum k θ).rootGroup γ := hx
  have hcomm : x * y * x⁻¹ = y := by
    refine CFSG.LieType.TitsSimplicity.iSup₂_induction (C := fun x => x * y * x⁻¹ = y)
      hx' ?_ ?_ ?_
    · intro γ hγ x hx
      have hc := teNSyl_commute_longPos0_alpha θ hθ hγ x hx y hy
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    · rw [one_mul, inv_one, mul_one]
    · intro x z hx hz
      calc (x * z) * y * (x * z)⁻¹ = x * (z * y * z⁻¹) * x⁻¹ := by group
        _ = x * y * x⁻¹ := by rw [hz]
        _ = y := hx
  rwa [hcomm]

theorem twE6N0_mem_normalizer_alpha
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6N θ hθ (twE6W0L k θ) ∈ twE6NA θ := by
  rw [twE6NA, Subgroup.mem_normalizer_iff_map_conj_eq]
  have h := (actsAs_nrep (twE6_hct θ hθ) (twE6W0L k θ)) twE6Alpha (twE6_alpha_mem_roots θ)
  rw [teNSyl_w0L_alpha θ] at h
  simpa [twE6RA, twE6N] using h

private theorem teNSyl_UM_le_U
    {k : Type} [Field k] (θ : k →+* k) :
    twE6UM θ ≤ twE6PosUnip θ := by
  refine iSup₂_le fun γ hγ => ?_
  refine rootGroup_le_posUnipotent (D := twistedDatum k θ) ?_ (teNSyl_longPos0_ht_ge_one hγ)
  rw [twistedDatum_roots]
  exact teNSyl_longPos0_isRoot hγ

private theorem teNSyl_sylow_conj_map {p : ℕ} {G : Type} [Group G] {g : G} {P Q : Sylow p G}
    (h : g • P = Q) : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G) := by
  have hsub : (Q : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
    rw [← h]
    exact Sylow.coe_subgroup_smul
  rw [hsub]
  rfl

theorem twE6_exists_conj_sylow
    {k : Type} [Field k] [Finite k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ∃ g : fixedGroup k θ, pCoreOf 2 (twE6NA θ) ≤ twE6Cj g (twE6PosUnip θ) ∧
      ∀ γ ∈ (twistedDatum k θ).roots, γ ∈ twE6Psi →
        (twistedDatum k θ).rootGroup γ ≤ twE6Cj g (twE6PosUnip θ) := by
  classical
  haveI : Finite (fixedGroup k θ) := by
    have : Finite (Module.End k (Fin e6Data.d →₀ k)) := Module.finite_of_finite k
    have : Finite ↥(e6Data_valid.minGroup k) := inferInstance
    infer_instance
  have hX : ∀ γ ∈ (twistedDatum k θ).roots, IsPGroup 2 ((twistedDatum k θ).rootGroup γ) :=
    fun γ hγ => isPGroup_two_twistedRootGroup θ hγ
  have hT : Nat.Coprime 2 (Nat.card (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ))) :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.coprime_card_torus θ hθ
  have hU2 : IsPGroup 2 (twE6PosUnip θ) :=
    isPGroup_iSup_pos (twistedDatum_steinbergExtras θ hθ) hX
  have hUidx : Nat.Coprime 2 (twE6PosUnip θ).index :=
    CFSG.LieType.Steinberg.CentralExt.BorelIndex.coprime_index_posUnipotent
      (twE6_hct θ hθ) (twistedDatum_steinbergExtras θ hθ) (twistedDatum_bruhatExtras θ) hX hT
  have hUnDvd : ¬ 2 ∣ (twE6PosUnip θ).index :=
    (Nat.prime_two.coprime_iff_not_dvd).1 hUidx
  let Usyl : Sylow 2 (fixedGroup k θ) := hU2.toSylow hUnDvd
  have hUM2 : IsPGroup 2 (twE6UM θ) := hU2.to_le (teNSyl_UM_le_U θ)
  have hnorm : twE6UM θ ≤ Subgroup.normalizer (pCoreOf 2 (twE6NA θ) : Set (fixedGroup k θ)) :=
    (twE6UM_le_normalizer_alpha θ hθ).trans (GGRootNorm.le_normalizer_pCoreOf _)
  have hP2 : IsPGroup 2 (pCoreOf 2 (twE6NA θ) ⊔ twE6UM θ : Subgroup (fixedGroup k θ)) :=
    (GGRootNorm.isPGroup_pCoreOf _).to_sup_of_normal_left' hUM2 hnorm
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (fixedGroup k θ) Usyl Q
  have hQ : twE6Cj g (twE6PosUnip θ) = (Q : Subgroup (fixedGroup k θ)) := by
    rw [twE6Cj]
    simpa only [Usyl, IsPGroup.toSylow_coe] using teNSyl_sylow_conj_map hg
  refine ⟨g, ?_, ?_⟩
  · rw [hQ]
    exact le_sup_left.trans hPQ
  · intro γ hγroot hγPsi
    rw [hQ]
    have hle : (twistedDatum k θ).rootGroup γ ≤
        pCoreOf 2 (twE6NA θ) ⊔ twE6UM θ := by
      rcases hγPsi with hlev | hlong
      · refine (rootGroup_le_ggSub (D := twistedDatum k θ)
          (S := {δ | δ ∈ (twistedDatum k θ).roots ∧ 1 ≤ δ twE6Last})
          ⟨hγroot, hlev⟩).trans ?_
        exact (twE6Rad_le_pCoreOf_normalizer θ hθ).trans le_sup_left
      · exact (rootGroup_le_ggSub (D := twistedDatum k θ) (S := twE6LongPos0) hlong).trans
          le_sup_right
    exact hle.trans hPQ

end CFSG.StandardType.LieKnownR2.Short

module

public import CFSG.RankThree.Chevalley.SteinbergBMG2CanonicalFieldAllOrders
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.LieType.Chevalley.G2SolvableNormalTrivial

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.LocalRank CFSG.GroupTheory
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)

theorem aschbacherSolvableCore_centralizer_eq_bot_of_conj_of_solvable {A : Type*} [Group A]
    {B : Subgroup A} [Finite B] {p : ℕ} (hp : p.Prime) (a : B) (hap : orderOf a = p) (ψ : A)
    (N : Subgroup A) (hNB : ∀ n ∈ N, ψ⁻¹ * n * ψ ∈ B)
    (hNa : N ≤ Subgroup.centralizer {ψ * (a : A) * ψ⁻¹})
    (hNnormal : (N.subgroupOf (Subgroup.centralizer {ψ * (a : A) * ψ⁻¹})).Normal)
    (hsolv : ∀ R : Subgroup N, R.Normal → Group.IsSolvable R → R = ⊥)
    (hcent : Subgroup.centralizer {ψ * (a : A) * ψ⁻¹} ⊓ Subgroup.centralizer (N : Set A) ≤
      Subgroup.zpowers (ψ * (a : A) * ψ⁻¹)) :
    aschbacherSolvableCore p (Subgroup.centralizer {a} : Subgroup B) = ⊥ := by
  classical
  set H := (Subgroup.centralizer {a} : Subgroup B) with hH
  set a' : A := ψ * (a : A) * ψ⁻¹ with ha'
  let κ : H →* A := (MulAut.conj ψ).toMonoidHom.comp (B.subtype.comp H.subtype)
  have hκ : ∀ h : H, κ h = ψ * ((h : B) : A) * ψ⁻¹ := fun h => rfl
  have hκinj : Function.Injective κ := fun h₁ h₂ e => by
    rw [hκ, hκ] at e
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel e)))
  have hκa : ∀ h : H, κ h ∈ Subgroup.centralizer {a'} := by
    intro h
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : ((h : B) : A) * (a : A) = (a : A) * ((h : B) : A) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 h.2)
    rw [hκ, ha']
    calc ψ * ((h : B) : A) * ψ⁻¹ * (ψ * (a : A) * ψ⁻¹) = ψ * (((h : B) : A) * a) * ψ⁻¹ := by
          group
      _ = ψ * ((a : A) * ((h : B) : A)) * ψ⁻¹ := by rw [h2]
      _ = ψ * (a : A) * ψ⁻¹ * (ψ * ((h : B) : A) * ψ⁻¹) := by group
  have hsurj : ∀ n ∈ N, ∃ h : H, κ h = n := by
    intro n hn
    have h1 : n * a' = a' * n := Subgroup.mem_centralizer_singleton_iff.1 (hNa hn)
    refine ⟨⟨⟨ψ⁻¹ * n * ψ, hNB n hn⟩, Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext ?_)⟩, ?_⟩
    · change ψ⁻¹ * n * ψ * (a : A) = (a : A) * (ψ⁻¹ * n * ψ)
      calc ψ⁻¹ * n * ψ * (a : A) = ψ⁻¹ * (n * a') * ψ := by rw [ha']; group
        _ = ψ⁻¹ * (a' * n) * ψ := by rw [h1]
        _ = (a : A) * (ψ⁻¹ * n * ψ) := by rw [ha']; group
    · change ψ * (ψ⁻¹ * n * ψ) * ψ⁻¹ = n
      group
  set NH : Subgroup H := N.comap κ with hNH
  have hNHnormal : NH.Normal := by
    refine ⟨fun n hn h => ?_⟩
    have hn' : κ n ∈ N := hn
    have h1 := hNnormal.conj_mem ⟨κ n, hNa hn'⟩ (Subgroup.mem_subgroupOf.2 hn') ⟨κ h, hκa h⟩
    rw [Subgroup.mem_subgroupOf] at h1
    change κ (h * n * h⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact h1
  let eN : NH ≃* N := MulEquiv.ofBijective ((κ.comp NH.subtype).codRestrict N fun h => h.2)
    ⟨fun h₁ h₂ e => Subtype.ext (hκinj (congrArg Subtype.val e)), fun n => by
      obtain ⟨h, hh⟩ := hsurj n n.2
      exact ⟨⟨h, show κ h ∈ N by rw [hh]; exact n.2⟩, Subtype.ext hh⟩⟩
  have : Finite H := Subtype.finite
  obtain ⟨hsolvD, hchar, hpd, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set D := aschbacherSolvableCore p H with hD
  have hDnormal : D.Normal := Subgroup.normal_of_characteristic D
  have hDN : D ⊓ NH = ⊥ := by
    set R : Subgroup NH := D.subgroupOf NH with hR
    have hRn : R.Normal := hDnormal.subgroupOf NH
    have hRs : Group.IsSolvable R := by
      have : Group.IsSolvable D := hsolvD
      let ρ : R →* D :=
        { toFun := fun r => ⟨((r : NH) : H), r.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine Group.isSolvable_of_isSolvable_injective (f := ρ) fun r₁ r₂ e => ?_
      have h1 : ((r₁ : NH) : H) = ((r₂ : NH) : H) := congrArg (fun z : D => (z : H)) e
      exact Subtype.ext (Subtype.ext h1)
    have hR' : R.map eN.toMonoidHom = ⊥ := by
      refine hsolv _ (hRn.map _ eN.surjective) ?_
      have : Group.IsSolvable R := hRs
      let eR := R.equivMapOfInjective eN.toMonoidHom eN.injective
      exact Group.isSolvable_of_isSolvable_injective (f := eR.symm.toMonoidHom)
        eR.symm.injective
    have hR1 : R = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (f := eN.toMonoidHom) R eN.injective).1 hR'
    exact disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 hR1)
  have hcomm : ∀ d ∈ D, ∀ n ∈ NH, d * n = n * d := by
    have hle : ⁅D, NH⁆ ≤ D ⊓ NH := Subgroup.commutator_le_inf D NH
    rw [hDN, le_bot_iff] at hle
    intro d hd n hn
    have h1 := Subgroup.commutator_mem_commutator hd hn
    rwa [hle, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have hDa : D.map κ ≤ Subgroup.zpowers a' := by
    rintro _ ⟨d, hd, rfl⟩
    refine hcent (Subgroup.mem_inf.2 ⟨hκa d, Subgroup.mem_centralizer_iff.2 fun n hn => ?_⟩)
    obtain ⟨h, rfl⟩ := hsurj n hn
    have h1 := hcomm d hd h hn
    rw [← map_mul, ← map_mul, h1]
  have hcard : Nat.card D ∣ p := by
    have h1 := Subgroup.card_dvd_of_le hDa
    rwa [Subgroup.card_map_of_injective hκinj, Nat.card_zpowers, ha',
      show ψ * (a : A) * ψ⁻¹ = MulAut.conj ψ (a : A) from rfl, MulEquiv.orderOf_eq,
      Subgroup.orderOf_coe, hap] at h1
  rcases (Nat.dvd_prime hp).1 hcard with h1 | h1
  · exact Subgroup.card_eq_one.1 h1
  · exact absurd (h1 ▸ dvd_refl p) hpd

theorem aschbacherSolvableCore_centralizer_eq_bot_of_inner_of_solvable {M : Type*} [Group M]
    {C J : Subgroup M} [Finite C] {p : ℕ} (hp : p.Prime) (hJC : J ≤ C)
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (α : B)
    (hαp : orderOf α = p) (ψ δ : MulAut C) (hψ : ψ * (α : MulAut C) * ψ⁻¹ = δ)
    (hsolv : ∀ R : Subgroup J, R.Normal → Group.IsSolvable R → R = ⊥)
    (ι : ↥(J.subgroupOf C) ≃* ↥((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)))
    (hNδ : (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer {δ})
    (hnormal : (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer {δ})).Normal)
    (hcent : Subgroup.centralizer {δ} ⊓ Subgroup.centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = Subgroup.zpowers δ) :
    aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  have : Finite (MulAut C) := Finite.of_injective (fun β : MulAut C => (β : C → C))
    fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite B := Subtype.finite
  set N := (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) with hN
  have e : N ≃* J := ι.symm.trans (Subgroup.subgroupOfEquivOfLe hJC)
  refine aschbacherSolvableCore_centralizer_eq_bot_of_conj_of_solvable hp α hαp ψ N ?_
    (hψ ▸ hNδ) (hψ ▸ hnormal) (fun R hRn hRs => ?_) (hψ ▸ hcent.le)
  · rintro _ ⟨j, -, rfl⟩
    have h := mulAut_mul_conj_mul_inv ψ⁻¹ j
    rw [inv_inv] at h
    change ψ⁻¹ * MulAut.conj j * ψ ∈ B
    rw [h]
    exact hB ⟨_, rfl⟩
  ·
    have hR' : R.map e.toMonoidHom = ⊥ := by
      refine hsolv _ (hRn.map _ e.surjective) ?_
      have : Group.IsSolvable R := hRs
      let eR := R.equivMapOfInjective e.toMonoidHom e.injective
      exact Group.isSolvable_of_isSolvable_injective (f := eR.symm.toMonoidHom)
        eR.symm.injective
    exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) R e.injective).1 hR'

theorem exists_inner_conj_eq_entrywiseAdjointAut_G2 {f d p : ℕ} (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ f) (hd : 1 ≤ d) (hp : 1 ≤ p) (hdp : d * p = f)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (2 ^ d)) (y : adjointGroup .G2 K)
    (hβp : (MulAut.conj y * entrywiseAdjointAut .G2 T) ^ p = 1) :
    ∃ h : adjointGroup .G2 K, MulAut.conj h * (MulAut.conj y * entrywiseAdjointAut .G2 T) *
      (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 T := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hTp : T ^ p = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_apply, RingAut.one_apply]
    have hit : ∀ n : ℕ, (⇑T)^[n] c = c ^ ((2 ^ d) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hT, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hdp, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hβp' := hβp
  rw [conj_mul_pow, ← entrywiseAdjointAut_pow, hTp, entrywiseAdjointAut_one, mul_one] at hβp'
  generalize hNdef : ((List.range p).map fun i => (entrywiseAdjointAut .G2 T ^ i) y).prod = N
    at hβp'
  have hN1 : N = 1 := by
    have hc : N ∈ Subgroup.center (adjointGroup .G2 K) := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have h1 : N * g * N⁻¹ = g := by
        have := congrArg (fun φ : MulAut (adjointGroup .G2 K) => φ g) hβp'
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * N = N * g * N⁻¹ * N := by rw [h1]
        _ = N * g := by group
    rw [center_adjointGroup_eq_bot] at hc
    exact Subgroup.mem_bot.1 hc
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity 2 L d hd).1 .G2
  have hS1 : ∀ g, ((S.toMonoidHom g : adjointGroup .G2 L) : ModGL .G2 L) =
      Units.map (entrywiseHom (iterateFrobenius L 2 d)) g := hS
  let ι : adjointGroup .G2 K →* adjointGroup .G2 L :=
    ((baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype).codRestrict
      (adjointGroup .G2 L) fun u => baseChangeGL_mem_adjointGroup (algebraMap K L) u.2
  have hι : ∀ u, (ι u : ModGL .G2 L) = baseChangeGL (algebraMap K L) u := fun _ => rfl
  have hιinj : Function.Injective ι := fun u v h =>
    Subtype.ext (baseChangeGL_injective (algebraMap K L) (congrArg Subtype.val h))
  have hFrc : (iterateFrobenius L 2 d).comp (algebraMap K L) =
      (algebraMap K L).comp T.toRingHom := by
    ext c
    simp [iterateFrobenius_def, hT, map_pow]
  have hSι : ∀ u, S (ι u) = ι (entrywiseAdjointAut .G2 T u) := by
    intro u
    apply Subtype.ext
    rw [hS, hι, hι, coe_entrywiseAdjointAut, units_map_entrywiseHom_eq_baseChangeGL,
      units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      baseChangeGL_baseChangeGL, hFrc]
  have hSιi : ∀ (i : ℕ) (u : adjointGroup .G2 K),
      (⇑S.toMonoidHom)^[i] (ι u) = ι ((entrywiseAdjointAut .G2 T ^ i) u) := by
    intro i
    induction i with
    | zero => intro u; rfl
    | succ i ih =>
      intro u
      rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
      exact hSι _
  have hnorm : ((List.range p).map fun i => (⇑S.toMonoidHom)^[i] (ι y)).prod = 1 := by
    have h1 : ((List.range p).map fun i => (⇑S.toMonoidHom)^[i] (ι y)) =
        ((List.range p).map fun i => (entrywiseAdjointAut .G2 T ^ i) y).map ι := by
      rw [List.map_map]
      exact List.map_congr_left fun i _ => hSιi i y
    rw [h1, ← map_list_prod, hNdef, hN1, map_one]
  obtain ⟨h, hR, hyh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom hp hLang (ι y) hnorm
  have hFrK : ∀ c : L, ((iterateFrobenius L 2 d) ^ p) c = c ^ Nat.card K := by
    intro c
    rw [RingHom.coe_pow]
    have hit : ∀ n : ℕ, (⇑(iterateFrobenius L 2 d))^[n] c = c ^ ((2 ^ d) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, iterateFrobenius_def, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hdp, hK]
  have hiterS : ∀ (n : ℕ) (g : adjointGroup .G2 L),
      (((⇑S.toMonoidHom)^[n] g : adjointGroup .G2 L) : ModGL .G2 L) =
        Units.map (entrywiseHom ((iterateFrobenius L 2 d) ^ n)) g := by
    intro n
    induction n with
    | zero =>
      intro g
      refine Units.ext ?_
      rw [Function.iterate_zero, id_eq, Units.coe_map, pow_zero, RingHom.one_def]
      exact (entrywise_id (R := L) _).symm
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply', hS1, ih]
      refine Units.ext ?_
      rw [Units.coe_map, Units.coe_map, Units.coe_map, pow_succ', RingHom.mul_def]
      exact entrywise_entrywise (R := L) _ _ _
  have hhfix : (h : ModGL .G2 L) ∈ adjointGroup .G2 L ⊓
      (Units.map (entrywiseHom ((iterateFrobenius L 2 d) ^ p))).eqLocus (MonoidHom.id _) := by
    refine ⟨h.2, ?_⟩
    change Units.map (entrywiseHom ((iterateFrobenius L 2 d) ^ p)) (h : ModGL .G2 L) = h
    rw [← hiterS p h, mem_iterateFixedSubgroup.1 hR]
  rw [(G2_F4_exact_finite_field_fixed_root_matrices .G2 (Or.inl rfl) K L _ hFrK).1] at hhfix
  obtain ⟨h₀, hh₀, hh₀h⟩ := hhfix
  set h₁ : adjointGroup .G2 K := ⟨h₀, hh₀⟩ with hh₁
  have hιh : ι h₁ = h := Subtype.ext hh₀h
  have hy : y = h₁⁻¹ * entrywiseAdjointAut .G2 T h₁ := by
    apply hιinj
    rw [map_mul, map_inv, ← hSι, hιh]
    exact hyh
  refine ⟨h₁, ?_⟩
  have key : MulAut.conj h₁ * MulAut.conj y *
      MulAut.conj (entrywiseAdjointAut .G2 T h₁⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, hy, map_inv]
    have h1 : h₁ * (h₁⁻¹ * entrywiseAdjointAut .G2 T h₁) * (entrywiseAdjointAut .G2 T h₁)⁻¹ =
        1 := by group
    rw [h1, map_one]
  calc MulAut.conj h₁ * (MulAut.conj y * entrywiseAdjointAut .G2 T) * (MulAut.conj h₁)⁻¹ =
        MulAut.conj h₁ * MulAut.conj y *
          (entrywiseAdjointAut .G2 T * MulAut.conj h₁⁻¹) := by
        rw [map_inv]
        group
    _ = MulAut.conj h₁ * MulAut.conj y *
          (MulAut.conj (entrywiseAdjointAut .G2 T h₁⁻¹) * entrywiseAdjointAut .G2 T) := by
        rw [mulAut_mul_conj (entrywiseAdjointAut .G2 T) h₁⁻¹]
    _ = MulAut.conj h₁ * MulAut.conj y * MulAut.conj (entrywiseAdjointAut .G2 T h₁⁻¹) *
          entrywiseAdjointAut .G2 T := by group
    _ = entrywiseAdjointAut .G2 T := by rw [key, one_mul]

theorem even_G2_noninner_prime_local_core_trivial {f p : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B) (α : B)
    (hα : (α : MulAut (adjointGroup .G2 K)) ∉
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range)
    (hαp : orderOf α = p) (x : adjointGroup .G2 K) (σ : K ≃+* K)
    (hxσ : (α : MulAut (adjointGroup .G2 K)) = MulAut.conj x * entrywiseAdjointAut .G2 σ) :
    orderOf σ = p ∧ p ∣ f ∧
      (∃ h : adjointGroup .G2 K, MulAut.conj h * (α : MulAut (adjointGroup .G2 K)) *
        (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 σ) ∧
      aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have : Finite (ModGL .G2 K) := finite_modGL
  set α' : MulAut (adjointGroup .G2 K) := (α : MulAut (adjointGroup .G2 K)) with hα'
  have hα'p : orderOf α' = p := by rw [hα', Subgroup.orderOf_coe, hαp]
  have hα'pow : α' ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one α'
  obtain ⟨hNF, Θ, hΘ, -, -, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  have hform : ∀ (g : adjointGroup .G2 K) (η : K ≃+* K) (u : adjointGroup .G2 K),
      ((MulAut.conj g * entrywiseAdjointAut .G2 η) u : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom η.toRingHom) (u : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹ :=
    fun g η u => by
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_entrywiseAdjointAut, Subgroup.coe_inv]
  have hΘα : Θ α' = σ := hΘ α' x σ fun u => by
    have h1 := hform x σ u
    rw [← hxσ] at h1
    exact h1
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hα
    rw [hxσ, entrywiseAdjointAut_one, mul_one]
    exact ⟨x, rfl⟩
  have hσp : σ ^ p = 1 := by rw [← hΘα, ← map_pow, hα'pow, map_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hdvd, -⟩ := SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK σ
  rw [hσord] at hdvd
  obtain ⟨d, hd⟩ := hdvd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  obtain ⟨fr, hfr, hord, htop, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK
  have hσmem : σ ∈ Subgroup.zpowers fr := by
    rw [htop]
    exact Subgroup.mem_top σ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hσmem
  have hmn : m % (f : ℤ) = ((m % (f : ℤ)).toNat : ℤ) :=
    (Int.toNat_of_nonneg (Int.emod_nonneg m (by omega))).symm
  set n := (m % (f : ℤ)).toNat with hn_def
  have hσn : σ = fr ^ n := by
    rw [← hm, ← zpow_mod_orderOf, hord, hmn, zpow_natCast]
  have hnf : n < f := by
    have h1 := Int.emod_lt_of_pos m (show (0 : ℤ) < f by omega)
    omega
  have hfn : f ∣ n * p := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_mul, ← hσn, hσp])
  have hdn : d ∣ n := by
    have h1 : d * p ∣ n * p := by rw [show d * p = f by rw [hd]; ring]; exact hfn
    exact Nat.dvd_of_mul_dvd_mul_right hp.pos h1
  obtain ⟨j, hj⟩ := hdn
  have hjp : j < p := by
    by_contra hjp
    have h1 : d * p ≤ d * j := Nat.mul_le_mul_left _ (not_lt.1 hjp)
    have h2 : d * p = f := by rw [hd]; ring
    omega
  have hj0 : 0 < j := Nat.pos_of_ne_zero fun h0 => hσ1 (by rw [hσn, hj, h0, mul_zero, pow_zero])
  set T := fr ^ d with hTdef
  have hT : ∀ c, T c = c ^ 2 ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hσT : σ = T ^ j := by rw [hσn, hj, hTdef, pow_mul]
  have hTp : T ^ p = 1 := by
    rw [hTdef, ← pow_mul, show d * p = f by rw [hd]; ring, ← hord, pow_orderOf_eq_one]
  have hT1 : T ≠ 1 := fun h1 => hσ1 (by rw [hσT, h1, one_pow])
  have hTord : orderOf T = p := orderOf_eq_prime hTp hT1
  obtain ⟨r, hr⟩ := exists_mul_mod_eq_one hp hj0 hjp
  obtain ⟨⟨y, η⟩, hyη, -⟩ := hNF (α' ^ r)
  dsimp only at hyη
  have hηT : η = T := by
    have h1 : Θ (α' ^ r) = η := hΘ _ y η hyη
    rw [map_pow, hΘα, hσT, ← pow_mul, mul_comm, pow_eq_self_of_mod_eq_one hTord hr] at h1
    exact h1.symm
  have hβ : α' ^ r = MulAut.conj y * entrywiseAdjointAut .G2 T := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hyη u, hform, hηT]
  have hβp : (MulAut.conj y * entrywiseAdjointAut .G2 T) ^ p = 1 := by
    rw [← hβ, ← pow_mul, mul_comm, pow_mul, hα'pow, one_pow]
  obtain ⟨h, hh⟩ := exists_inner_conj_eq_entrywiseAdjointAut_G2 K hK hd0 hp.one_lt.le
    (show d * p = f by rw [hd]; ring) T hT y hβp
  have hhα : MulAut.conj h * α' * (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 σ := by
    have hαβ : α' = (α' ^ r) ^ j := by rw [← pow_mul, pow_eq_self_of_mod_eq_one hα'p hr]
    rw [hαβ, ← conj_pow, hβ, hh, ← entrywiseAdjointAut_pow, ← hσT]
  obtain ⟨-, -, hJC, -, ⟨ι, -⟩, -, -, hNδ, hnormal, -, hcent, -, -⟩ :=
    even_G2_canonical_field_centralizer_all_orders hf hK σ
  have hsolv : ∀ R : Subgroup (fixedFieldImage .G2 σ), R.Normal → Group.IsSolvable R →
      R = ⊥ := by
    intro R hRn hRs
    let eJ : ↥(adjointGroup .G2 (fixSubfield σ)) ≃* ↥(fixedFieldImage .G2 σ) :=
      (adjointGroup .G2 (fixSubfield σ)).equivMapOfInjective _ (baseChangeGL_injective _)
    have hR' : R.map eJ.symm.toMonoidHom = ⊥ := by
      have : (R.map eJ.symm.toMonoidHom).Normal := hRn.map _ eJ.symm.surjective
      refine G2_solvable_normal_subgroups_trivial _ _ ?_
      have : Group.IsSolvable R := hRs
      let eR := R.equivMapOfInjective eJ.symm.toMonoidHom eJ.symm.injective
      exact Group.isSolvable_of_isSolvable_injective (f := eR.symm.toMonoidHom)
        eR.symm.injective
    exact (Subgroup.map_eq_bot_iff_of_injective (f := eJ.symm.toMonoidHom) R
      eJ.symm.injective).1 hR'
  exact ⟨hσord, ⟨d, hd⟩, ⟨h, hhα⟩,
    aschbacherSolvableCore_centralizer_eq_bot_of_inner_of_solvable hp hJC hB α hαp
      (MulAut.conj h) (entrywiseAdjointAut .G2 σ) hhα hsolv ι hNδ hnormal hcent⟩

end CFSG.RankThree.Chevalley

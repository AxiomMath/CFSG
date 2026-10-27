module

public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups CFSG.GroupTheory

theorem mem_zpowers_of_pow_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} (hp : 0 < p) {η ε : G} (hη : orderOf η = p) (hε : ε ^ p = 1) :
    ε ∈ Subgroup.zpowers η := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set S := (Finset.univ : Finset G).filter fun x => x ^ p = 1 with hS
  have hSle : S.card ≤ p := IsCyclic.card_pow_eq_one_le hp
  have hsub : (Subgroup.zpowers η : Set G).toFinset ⊆ S := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hη, pow_orderOf_eq_one,
      one_zpow]
  have hcard : (Subgroup.zpowers η : Set G).toFinset.card = p := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← hη,
      ← Nat.card_zpowers]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hSle)
  have hεS : ε ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hε⟩
  rw [← heq, Set.mem_toFinset] at hεS
  exact hεS

theorem exists_inner_conj_eq_of_pow_eq_twisted_frobenius (t : TwistTag) {m : ℕ} (hm : 1 ≤ m)
    (K : Type) [Field K] (σ : K →+* K) (L : Type) [Field L] [Algebra K L] (Fr : L →+* L)
    (hcomm : (algebraMap K L).comp σ = Fr.comp (algebraMap K L))
    (S : MulAut (adjointGroup t.tag L))
    (hSm : ∀ g, (((⇑S)^[m] g : adjointGroup t.tag L) : ModGL t.tag L) = twistHom t L Fr g)
    (hLang : ∀ y : adjointGroup t.tag L, ∃ h, y = h⁻¹ * S h)
    (ιH : graphFixedRootGroup t K σ →* adjointGroup t.tag L)
    (hιH : ∀ u, (ιH u : ModGL t.tag L) = baseChangeGL (algebraMap K L) u)
    (hGF : ∀ g : adjointGroup t.tag L, twistHom t L Fr (g : ModGL t.tag L) = g → ∃ u, ιH u = g)
    (hZ : Subgroup.center (graphFixedRootGroup t K σ) = ⊥)
    (β : MulAut (graphFixedRootGroup t K σ)) (hβ : ∀ u, S (ιH u) = ιH (β u))
    (x : graphFixedRootGroup t K σ) (hαm : (MulAut.conj x * β) ^ m = 1) :
    ∃ h : graphFixedRootGroup t K σ,
      MulAut.conj h * (MulAut.conj x * β) * (MulAut.conj h)⁻¹ = β := by
  classical
  have hι : Function.Injective ιH := fun u v huv => Subtype.ext (baseChangeGL_injective
    (algebraMap K L) (by rw [← hιH, ← hιH, huv]))
  have hFfix : ∀ u, (⇑S)^[m] (ιH u) = ιH u := fun u => Subtype.ext (by
    rw [hSm, hιH, twistHom_baseChangeGL (algebraMap K L) hcomm]
    congr 1
    exact (graphFixedRootGroup_le t K σ u.2).2)
  have hβi : ∀ (i : ℕ) (u : graphFixedRootGroup t K σ),
      (⇑S)^[i] (ιH u) = ιH ((β ^ i) u) := by
    intro i
    induction i with
    | zero => intro u; rfl
    | succ i ih =>
      intro u
      rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply, hβ]
  have hβm : β ^ m = 1 := MulEquiv.ext fun u => hι (by rw [← hβi, hFfix]; rfl)
  have h1 := hαm
  rw [conj_mul_pow, hβm, mul_one] at h1
  generalize hNdef : ((List.range m).map fun i => (β ^ i) x).prod = N at h1
  have hN : N = 1 := by
    have hc : N ∈ Subgroup.center (graphFixedRootGroup t K σ) := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have h2 : N * g * N⁻¹ = g := by
        have := congrArg (fun φ : MulAut (graphFixedRootGroup t K σ) => φ g) h1
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * N = N * g * N⁻¹ * N := by rw [h2]
        _ = N * g := by group
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  have hnorm : ((List.range m).map fun i => (⇑S.toMonoidHom)^[i] (ιH x)).prod = 1 := by
    have h2 : ((List.range m).map fun i => (⇑S.toMonoidHom)^[i] (ιH x)) =
        ((List.range m).map fun i => (β ^ i) x).map ιH := by
      rw [List.map_map]
      exact List.map_congr_left fun i _ => hβi i x
    rw [h2, ← map_list_prod, hNdef, hN, map_one]
  obtain ⟨h, hR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom hm hLang (ιH x) hnorm
  have hhF : twistHom t L Fr (h : ModGL t.tag L) = h := by
    rw [← hSm]
    exact congrArg Subtype.val (mem_iterateFixedSubgroup.1 hR)
  obtain ⟨h₀, rfl⟩ := hGF h hhF
  have hx : x = h₀⁻¹ * β h₀ := hι (by
    rw [map_mul, map_inv, ← hβ]
    exact hxh)
  refine ⟨h₀, ?_⟩
  rw [hx, map_mul, map_inv]
  calc MulAut.conj h₀ * ((MulAut.conj h₀)⁻¹ * MulAut.conj (β h₀) * β) * (MulAut.conj h₀)⁻¹ =
      MulAut.conj (β h₀) * (β * MulAut.conj h₀⁻¹) := by rw [map_inv]; group
    _ = MulAut.conj (β h₀) * (MulAut.conj (β h₀⁻¹) * β) := by rw [mulAut_mul_conj]
    _ = β := by rw [← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, one_mul]

theorem diagramMap_pow_conj_eq_entrywise {K : Type} [Field K] (σ : K ≃+* K) {r : ℕ}
    (hr12 : r = 1 ∨ r = 2) (w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    diagramMap TwistTag.D4 K ^ r * (w : ModGL TwistTag.D4.tag K) *
        (diagramMap TwistTag.D4 K ^ r)⁻¹ =
      Units.map (entrywiseHom (σ ^ (3 - r)).toRingHom) (w : ModGL TwistTag.D4.tag K) := by
  have hPK3 : diagramMap TwistTag.D4 K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hPKinv : (diagramMap TwistTag.D4 K)⁻¹ = diagramMap TwistTag.D4 K ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hPK3]
  have hσw : ∀ w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      Units.map (entrywiseHom σ.toRingHom) (w : ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * w * diagramMap TwistTag.D4 K := by
    intro w
    have hfix : twistHom TwistTag.D4 K σ.toRingHom (w : ModGL TwistTag.D4.tag K) = w :=
      (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom w.2).2
    rw [twistHom_apply] at hfix
    calc Units.map (entrywiseHom σ.toRingHom) (w : ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * (diagramMap TwistTag.D4 K *
          Units.map (entrywiseHom σ.toRingHom) (w : ModGL TwistTag.D4.tag K) *
            (diagramMap TwistTag.D4 K)⁻¹) * diagramMap TwistTag.D4 K := by group
      _ = _ := by rw [hfix]
  rcases hr12 with rfl | rfl
  ·
    have h2 : (σ ^ (3 - 1)).toRingHom = σ.toRingHom.comp σ.toRingHom := RingHom.ext fun c => rfl
    rw [h2, ← units_map_entrywiseHom_comp, hσw, map_mul, map_mul, map_inv,
      units_map_entrywiseHom_diagramMap, hσw, pow_one, hPKinv]
    have h4 : diagramMap TwistTag.D4 K ^ 2 * diagramMap TwistTag.D4 K ^ 2 =
        diagramMap TwistTag.D4 K := by
      rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, hPK3, one_mul, pow_one]
    calc diagramMap TwistTag.D4 K * (w : ModGL TwistTag.D4.tag K) *
          diagramMap TwistTag.D4 K ^ 2 =
        (diagramMap TwistTag.D4 K ^ 2 * diagramMap TwistTag.D4 K ^ 2) *
          (w : ModGL TwistTag.D4.tag K) *
            (diagramMap TwistTag.D4 K * diagramMap TwistTag.D4 K) := by rw [h4, ← sq]
      _ = diagramMap TwistTag.D4 K ^ 2 * (diagramMap TwistTag.D4 K ^ 2 *
          (w : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K) *
            diagramMap TwistTag.D4 K := by group
  ·
    have h1 : (σ ^ (3 - 2)).toRingHom = σ.toRingHom := RingHom.ext fun c => by simp
    rw [h1, hσw, ← hPKinv, inv_inv]

theorem iterate_twisted_frobenius_D4 {L : Type} [Field L] (Fr : L →+* L) (r : ℕ)
    (S : MulAut (adjointGroup TwistTag.D4.tag L))
    (hS : ∀ g : adjointGroup TwistTag.D4.tag L,
      (S g : ModGL TwistTag.D4.tag L) = diagramMap TwistTag.D4 L ^ r *
        Units.map (entrywiseHom Fr) (g : ModGL TwistTag.D4.tag L) *
          (diagramMap TwistTag.D4 L ^ r)⁻¹)
    (n : ℕ) (g : adjointGroup TwistTag.D4.tag L) :
    (((⇑S)^[n] g : adjointGroup TwistTag.D4.tag L) : ModGL TwistTag.D4.tag L) =
      diagramMap TwistTag.D4 L ^ (r * n) *
        Units.map (entrywiseHom (Fr ^ n)) (g : ModGL TwistTag.D4.tag L) *
          (diagramMap TwistTag.D4 L ^ (r * n))⁻¹ := by
  induction n generalizing g with
  | zero =>
    refine Units.ext ?_
    rw [Function.iterate_zero, id_eq, mul_zero, pow_zero, inv_one, one_mul, mul_one,
      Units.coe_map, pow_zero, RingHom.one_def]
    exact (entrywise_id (R := L) _).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', hS, ih, map_mul, map_mul, map_inv, map_pow,
      units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp,
      show Fr.comp (Fr ^ n) = Fr ^ (n + 1) by rw [pow_succ', RingHom.mul_def],
      show r * (n + 1) = r + r * n by ring, pow_add]
    group

theorem exists_inner_conj_triality_field_actor {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥) (hp : 1 ≤ p)
    (hpf : p ∣ f) {r : ℕ} (hr12 : r = 1 ∨ r = 2) (hrp : r * p % 3 = 1) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ ℓ) (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hgp : (MulAut.conj g * fieldActor σ (σ ^ (3 - r) * φ ^ (f / p))) ^ p = 1) :
    ∃ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj h * (MulAut.conj g * fieldActor σ (σ ^ (3 - r) * φ ^ (f / p))) *
        (MulAut.conj h)⁻¹ = fieldActor σ (σ ^ (3 - r) * φ ^ (f / p)) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hdp : f / p * p = f := Nat.div_mul_cancel hpf
  have hd1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by omega)
  set d := f / p with hd
  set L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι := algebraMap K L with hιdef
  set Fd := iterateFrobenius L ℓ d with hFddef
  have hFd : ∀ c, Fd c = c ^ ℓ ^ d := fun c => by rw [hFddef, iterateFrobenius_def]
  set Ff := iterateFrobenius L ℓ f with hFfdef
  have hFf : ∀ c, Ff c = c ^ ℓ ^ f := fun c => by rw [hFfdef, iterateFrobenius_def]
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity ℓ L d hd1).2 TwistTag.D4 (r : ℤ)
  have hS' : ∀ g' : adjointGroup TwistTag.D4.tag L,
      (S g' : ModGL TwistTag.D4.tag L) = diagramMap TwistTag.D4 L ^ r *
        Units.map (entrywiseHom Fd) (g' : ModGL TwistTag.D4.tag L) *
          (diagramMap TwistTag.D4 L ^ r)⁻¹ := fun g' => by rw [hS, zpow_natCast]
  have hP3 : diagramMap TwistTag.D4 L ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  have hFdp : Fd ^ p = Ff := RingHom.ext fun c => by
    rw [RingHom.coe_pow, hFf, ← hdp]
    have hit : ∀ n : ℕ, (⇑Fd)^[n] c = c ^ ((ℓ ^ d) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hFd, ← pow_mul, ← pow_succ]
    rw [hit, ← pow_mul]
  have hPrp : diagramMap TwistTag.D4 L ^ (r * p) = diagramMap TwistTag.D4 L := by
    rw [show r * p = 3 * (r * p / 3) + 1 by omega, pow_add, pow_mul, hP3, one_pow, one_mul,
      pow_one]
  have hSm : ∀ g' : adjointGroup TwistTag.D4.tag L,
      (((⇑S)^[p] g' : adjointGroup TwistTag.D4.tag L) : ModGL TwistTag.D4.tag L) =
        twistHom TwistTag.D4 L Ff g' := fun g' => by
    rw [iterate_twisted_frobenius_D4 Fd r S hS', hPrp, hFdp, twistHom_apply]
  have hcomm : ι.comp σ.toRingHom = Ff.comp ι := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hFf]
    change ι (σ c) = _
    rw [hσ, map_pow]
  have hC0le : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤ adjointGroup TwistTag.D4.tag K :=
    (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom).trans inf_le_left
  set ιH : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* adjointGroup TwistTag.D4.tag L :=
    (adjointBaseChangeHom TwistTag.D4.tag ι).comp (Subgroup.inclusion hC0le) with hιHdef
  have hιH : ∀ u, (ιH u : ModGL TwistTag.D4.tag L) = baseChangeGL ι u := fun _ => rfl
  have hGF : ∀ g' : adjointGroup TwistTag.D4.tag L,
      twistHom TwistTag.D4 L Ff (g' : ModGL TwistTag.D4.tag L) = g' → ∃ u, ιH u = g' := by
    intro g' hg'
    obtain ⟨-, hset, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f hℓ
      hf K hK L 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) Ff hFf
    have hmem : (g' : ModGL TwistTag.D4.tag L) ∈ {g : ModGL TwistTag.D4.tag L |
        g ∈ adjointGroup TwistTag.D4.tag L ∧ diagramMap TwistTag.D4 L ^ 1 *
          Units.map (entrywiseHom Ff) g * (diagramMap TwistTag.D4 L ^ 1)⁻¹ = g} :=
      ⟨g'.2, by rw [pow_one, ← twistHom_apply]; exact hg'⟩
    rw [hset] at hmem
    obtain ⟨u, hu, hug⟩ := hmem
    exact ⟨⟨u, hu⟩, Subtype.ext hug⟩
  have hφdι : Fd.comp ι = ι.comp (φ ^ d).toRingHom := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hFd]
    change _ = ι ((φ ^ d) c)
    rw [ringAut_pow_apply_of_frobenius hφ, map_pow]
  have hFdGL : ∀ u : ModGL TwistTag.D4.tag K, Units.map (entrywiseHom Fd) (baseChangeGL ι u) =
      baseChangeGL ι (Units.map (entrywiseHom (φ ^ d).toRingHom) u) := fun u => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hφdι]
  have hεcomp : (σ ^ (3 - r) * φ ^ d).toRingHom =
      (σ ^ (3 - r)).toRingHom.comp (φ ^ d).toRingHom := RingHom.ext fun c => rfl
  have hβ : ∀ u, S (ιH u) = ιH (fieldActor σ (σ ^ (3 - r) * φ ^ d) u) := fun u => by
    apply Subtype.ext
    rw [hS', hιH, hιH, coe_fieldActor, hFdGL, ← baseChangeGL_diagramMap ι TwistTag.D4,
      ← map_pow, ← map_inv, ← map_mul, ← map_mul, hεcomp, ← units_map_entrywiseHom_comp]
    congr 1
    have h1 := diagramMap_pow_conj_eq_entrywise σ hr12 (fieldActor σ (φ ^ d) u)
    rw [coe_fieldActor] at h1
    exact h1
  exact exists_inner_conj_eq_of_pow_eq_twisted_frobenius TwistTag.D4 hp K σ.toRingHom L Ff hcomm
    S hSm hLang ιH hιH hGF hZ _ hβ g hgp

theorem triality_core_eq_bot_of_conj {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK3 : Nat.card K = ℓ ^ (3 * f)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ ℓ) (hφord : orderOf φ = 3 * f) {p : ℕ} (hpf : p ∣ f)
    (hp : p.Prime) (hp3 : 3 < p)
    (B : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hB : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ≤ B) (α : B)
    (hαp : orderOf α = p) (h₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) {η : K ≃+* K}
    (hηp : orderOf η = p)
    (hconjα : MulAut.conj h₀ * (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) *
      (MulAut.conj h₀)⁻¹ = fieldActor σ η) :
    aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ', -, -, hgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ (by omega : 1 ≤ 3 * f) hK3
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ', hgen⟩
  have hdp : f / p * p = f := Nat.div_mul_cancel hpf
  have hd1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  set d := f / p with hd
  set δc := φ ^ (3 * d) with hδcdef
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * d) := fun c => ringAut_pow_apply_of_frobenius hφ _ c
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = ℓ ^ (3 * d * p) := by rw [hK3, mul_assoc, hdp]
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hdp]; exact hσ c
  obtain ⟨hδord, -, -, -, -, hJC, -, hsimple, hnc, ⟨ι', -⟩, -, hNδ, hnormal, hcent, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd1 hp.two_le hm3 K hK' σ
      hσ' δc hδc
  have hδcp : δc ^ p = 1 := by
    rw [hδcdef, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hφord, mul_assoc, hdp]
  have hδc1 : δc ≠ 1 := fun h => by
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact hp.one_lt.ne hδord
  obtain ⟨t, -, ht⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hηp hδcp))
  replace ht : η ^ t = δc := ht
  have htp : ¬p ∣ t := fun h => hδc1 (by
    obtain ⟨u, rfl⟩ := h
    rw [← ht, pow_mul, ← hηp, pow_orderOf_eq_one, one_pow])
  have hψ : MulAut.conj h₀ * ((α ^ t : B) : MulAut (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) * (MulAut.conj h₀)⁻¹ = fieldActor σ δc := by
    rw [Subgroup.coe_pow, ← conj_pow, hconjα, ← ht]
    exact (map_pow (fieldActorHom (t := TwistTag.D4) σ) η t).symm
  have hαtp : orderOf (α ^ t) = p := by
    rw [← Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq (MulAut.conj (MulAut.conj h₀)),
      MulAut.conj_apply, hψ, hδord]
  have hcore := aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB (α ^ t) hαtp
    (MulAut.conj h₀) (fieldActor σ δc) hψ hsimple hnc ι' hNδ hnormal hcent
  have hcentEq : (Subgroup.centralizer {α ^ t} : Subgroup B) = Subgroup.centralizer {α} := by
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 htp)) hp.one_lt
    have hαα : (α ^ t) ^ u = α := by
      rw [← pow_mul]
      have h1 : α ^ (t * u) = α ^ 1 := by
        rw [pow_eq_pow_iff_modEq, hαp]
        unfold Nat.ModEq
        rw [hu, Nat.one_mod_eq_one.mpr hp.one_lt.ne']
      rwa [pow_one] at h1
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      rw [← hαα]
      exact (Commute.pow_right (show Commute x (α ^ t) from hx) u).eq
    · intro hx
      exact (Commute.pow_right (show Commute x α from hx) t).eq
  rw [← hcentEq]
  exact hcore

theorem triality_noninner_large_prime_field_descent_and_local_core_trivial {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K))
    (hΘ : ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (B : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hB : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ≤ B) (α : B)
    (hα : (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (hαp : orderOf α = p) :
    orderOf (Θ α) = p ∧ p ∣ f ∧
    (∃ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj h * (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) *
        (MulAut.conj h)⁻¹ = fieldActor σ (Θ α)) ∧
    aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  obtain ⟨hNF, hcardAut, hZ⟩ :
      (∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        ∃! gδ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom × (K ≃+* K),
          β = MulAut.conj gδ.1 * fieldActor σ gδ.2) ∧ Nat.card (K ≃+* K) = 3 * f ∧
        Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ := by
    rcases eq_or_ne ℓ 2 with rfl | hℓ2
    · obtain ⟨-, hNF, -, -, hcard, -, hZ, -⟩ :=
        even_triality_exact_automorphism_normal_form hf K hK σ hσ
      exact ⟨hNF, hcard, hZ⟩
    · obtain ⟨-, hNF, -, -, hcard, -, hZ, -⟩ :=
        odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
      exact ⟨hNF, hcard, hZ⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨φ, hφ, hφord, hφgen, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ (by omega : 1 ≤ 3 * f) hK3
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφgen⟩
  have hα'p : orderOf (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = p := by
    rw [Subgroup.orderOf_coe, hαp]
  have hαpow : (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one _
  have hΘker : ∀ β, Θ β = 1 → β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    intro β hβ
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF β
    have h1 := hΘ β g δ hgδ
    rw [hβ] at h1
    refine ⟨g, ?_⟩
    rw [hgδ, ← h1, fieldActor_one, mul_one]
  set η := Θ α with hηdef
  have hηp : orderOf η = p :=
    orderOf_eq_prime (by rw [hηdef, ← map_pow, hαpow, map_one]) fun h => hα (hΘker _ h)
  have hpf : p ∣ f := by
    have h1 : p ∣ 3 * f := by
      rw [← hηp, ← hcardAut]
      exact orderOf_dvd_natCard η
    exact ((Nat.Prime.dvd_mul hp).1 h1).resolve_left fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
  have hdp : f / p * p = f := Nat.div_mul_cancel hpf
  have hd1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  set d := f / p with hd
  have hσφ : σ = φ ^ f := RingEquiv.ext fun c => by rw [hσ, ringAut_pow_apply_of_frobenius hφ]
  obtain ⟨r, hr12, hrp⟩ : ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ r * p % 3 = 1 := by
    have h3 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h
    · exact ⟨1, Or.inl rfl, by omega⟩
    · exact ⟨2, Or.inr rfl, by omega⟩
  set ε : K ≃+* K := σ ^ (3 - r) * φ ^ d with hεdef
  have hεφ : ε = φ ^ (f * (3 - r) + d) := by rw [hεdef, hσφ, ← pow_mul, ← pow_add]
  have hεp : ε ^ p = 1 := by
    rw [hεφ, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hφord]
    rcases hr12 with rfl | rfl
    · obtain ⟨j, hj⟩ : ∃ j, p = 3 * j + 1 := ⟨p / 3, by omega⟩
      exact ⟨2 * j + 1, by rw [← hdp, hj]; ring⟩
    · obtain ⟨j, hj⟩ : ∃ j, p = 3 * j + 2 := ⟨p / 3, by omega⟩
      exact ⟨j + 1, by rw [← hdp, hj]; ring⟩
  have hε1 : ε ≠ 1 := by
    intro h
    rw [hεφ, ← orderOf_dvd_iff_pow_eq_one, hφord, ← hdp] at h
    have h2 := Nat.le_of_dvd (by positivity) h
    rcases hr12 with rfl | rfl <;> nlinarith
  have hεord : orderOf ε = p := orderOf_eq_prime hεp hε1
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hηp hεp))
  replace hk : η ^ k = ε := hk
  obtain ⟨s, -, hs⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hεord
      (by rw [← hηp]; exact pow_orderOf_eq_one η)))
  replace hs : ε ^ s = η := hs
  obtain ⟨⟨g, δ'⟩, hgδ', -⟩ :=
    hNF ((α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ^ k)
  simp only at hgδ'
  have hδ' : δ' = ε := by
    rw [← hΘ _ g δ' hgδ', map_pow, ← hηdef, hk]
  rw [hδ'] at hgδ'
  obtain ⟨h₀, hh₀⟩ := exists_inner_conj_triality_field_actor hℓ hf K hK σ hσ hZ hp.one_lt.le hpf
    hr12 hrp hφ g (by rw [← hgδ', ← pow_mul, mul_comm, pow_mul, hαpow, one_pow])
  rw [← hgδ'] at hh₀
  have hks : (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ^ (k * s) = α := by
    have h1 : η ^ (k * s) = η ^ 1 := by rw [pow_mul, hk, hs, pow_one]
    rw [pow_eq_pow_iff_modEq, hηp] at h1
    have h2 : (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ^ (k * s) =
        (α : MulAut _) ^ 1 := by
      rw [pow_eq_pow_iff_modEq, hα'p]
      exact h1
    rwa [pow_one] at h2
  have hconjα : MulAut.conj h₀ * (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) *
      (MulAut.conj h₀)⁻¹ = fieldActor σ η := by
    rw [← hks, pow_mul, ← conj_pow, hh₀, ← hs]
    exact (map_pow (fieldActorHom (t := TwistTag.D4) σ) ε s).symm
  refine ⟨hηp, hpf, ⟨h₀, hconjα⟩, ?_⟩
  exact triality_core_eq_bot_of_conj hℓ hf K hK3 σ hσ hφ hφord hpf hp hp3 B hB α hαp h₀ hηp
    hconjα

end CFSG.RankThree.Chevalley

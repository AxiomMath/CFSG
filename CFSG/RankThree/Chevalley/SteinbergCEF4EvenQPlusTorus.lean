module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 CFSG.RankThree.E6
open scoped Pointwise

namespace EvenF4QPlus

@[expose] def qplusRoot : Fin 4 → Fin Tag.F4.rank → ℤ :=
  ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]]

theorem isRoot_qplusRoot (i : Fin 4) : IsRoot .F4 (qplusRoot i) := by
  rw [isRoot_iff_mem_f4RootList]
  revert i
  decide

theorem iform_qplusRoot (i j : Fin 4) :
    iform (qplusRoot i) (qplusRoot j) = if i = j then 4 else 0 := by
  revert i j
  decide

theorem not_mem_add_sub_qplusRoot :
    ∀ i j : Fin 4, i ≠ j → qplusRoot i + qplusRoot j ∉ f4RootList ∧
      qplusRoot i - qplusRoot j ∉ f4RootList := by
  decide

theorem iform_qplusRoot_eq_zero {i j : Fin 4} (hij : i ≠ j) :
    iform (qplusRoot i) (qplusRoot j) = 0 := by
  rw [iform_qplusRoot, ite_eq_right hij]

theorem rootReflection_qplusRoot_prod_smul (v : Fin Tag.F4.rank → ℤ) :
    (rootReflection (qplusRoot 0) * rootReflection (qplusRoot 1) * rootReflection (qplusRoot 2) *
      rootReflection (qplusRoot 3)) • v = -v := by
  set w := rootReflection (qplusRoot 0) * rootReflection (qplusRoot 1) *
    rootReflection (qplusRoot 2) * rootReflection (qplusRoot 3) with hw
  have hcol : ∀ k : Fin Tag.F4.rank,
      w • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) = -Pi.single k 1 := by
    intro k
    simp only [hw, mul_smul, rootReflection_smul (isRoot_qplusRoot _)]
    revert k
    decide
  have hM : weylMatrix w = -1 := by
    ext i j
    rw [weylMatrix_apply, hcol j, Matrix.neg_apply, Matrix.one_apply, Pi.neg_apply,
      Pi.single_apply]
  rw [← weylMatrix_mulVec, hM, Matrix.neg_mulVec, Matrix.one_mulVec]

section Hom

variable (L : Type) [Field L]

theorem commute_rootSL2_qplusRoot
    {i j : Fin 4} (hij : i ≠ j) (A B : SL2 L) :
    Commute (rootSL2 .F4 L (qplusRoot i) A) (rootSL2 .F4 L (qplusRoot j) B) := by
  obtain ⟨hp, hm⟩ := not_mem_add_sub_qplusRoot i j hij
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .F4 L
    (isRoot_qplusRoot i) (isRoot_qplusRoot j) (iform_qplusRoot_eq_zero hij)
    (fun h => hp (isRoot_iff_mem_f4RootList.1 h)) (fun h => hm (isRoot_iff_mem_f4RootList.1 h))
    _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

@[expose] def qplusHom :
    SL2 L →* ModGL .F4 L where
  toFun A := rootSL2 .F4 L (qplusRoot 0) A * rootSL2 .F4 L (qplusRoot 1) A *
    rootSL2 .F4 L (qplusRoot 2) A * rootSL2 .F4 L (qplusRoot 3) A
  map_one' := by simp only [map_one, mul_one]
  map_mul' A B := by
    have c : ∀ i j : Fin 4, i ≠ j →
        Commute (rootSL2 .F4 L (qplusRoot i) B) (rootSL2 .F4 L (qplusRoot j) A) :=
      fun i j h => commute_rootSL2_qplusRoot L h B A
    simp only [map_mul]
    rw [(c 0 1 (by decide)).mul_mul_mul_comm,
      ((c 0 2 (by decide)).mul_left (c 1 2 (by decide))).mul_mul_mul_comm,
      (((c 0 3 (by decide)).mul_left (c 1 3 (by decide))).mul_left
        (c 2 3 (by decide))).mul_mul_mul_comm]

theorem qplusHom_apply
    (A : SL2 L) :
    qplusHom L A = rootSL2 .F4 L (qplusRoot 0) A * rootSL2 .F4 L (qplusRoot 1) A *
      rootSL2 .F4 L (qplusRoot 2) A * rootSL2 .F4 L (qplusRoot 3) A :=
  rfl

theorem qplusHom_mem_adjointGroup
    (A : SL2 L) : qplusHom L A ∈ adjointGroup .F4 L := by
  have h := fun i => (exceptional_Lang_root_rank_one_data .F4 L (qplusRoot i)).2.2.2.2.1 A
  rw [qplusHom_apply]
  exact mul_mem (mul_mem (mul_mem (h 0) (h 1)) (h 2)) (h 3)

theorem entrywise_qplusHom
    (σ : L →+* L) (A : SL2 L) :
    Units.map (entrywiseHom σ) (qplusHom L A) =
      qplusHom L (Matrix.SpecialLinearGroup.map σ A) := by
  simp only [qplusHom_apply, map_mul, entrywise_rootSL2_of_field]

theorem qplusHom_mul_entrywise_inv_eq
    (σ : L →+* L) {A B : SL2 L}
    (hAB : A * B = Matrix.SpecialLinearGroup.map σ A) :
    qplusHom L A⁻¹ * (Units.map (entrywiseHom σ) (qplusHom L A⁻¹))⁻¹ = qplusHom L B := by
  rw [entrywise_qplusHom, ← map_inv (qplusHom L), ← map_mul (qplusHom L),
    map_inv (Matrix.SpecialLinearGroup.map σ), inv_inv, ← hAB, inv_mul_cancel_left]

theorem qplusHom_nSL_mem_monomial :
    ∃ hz : qplusHom L (nSL 1) ∈ monomialSubgroup .F4 L,
      ∀ v : Fin Tag.F4.rank → ℤ, weylQuotientHom .F4 L ⟨_, hz⟩ • v = -v := by
  have h := fun i =>
    (exceptional_Lang_root_rank_one_torus_transport .F4 L (isRoot_qplusRoot i)).2.2.1 1
  obtain ⟨h0, e0⟩ := h 0
  obtain ⟨h1, e1⟩ := h 1
  obtain ⟨h2, e2⟩ := h 2
  obtain ⟨h3, e3⟩ := h 3
  have hz : qplusHom L (nSL 1) ∈ monomialSubgroup .F4 L := mul_mem (mul_mem (mul_mem h0 h1) h2) h3
  refine ⟨hz, fun v => ?_⟩
  have e : (⟨qplusHom L (nSL 1), hz⟩ : monomialSubgroup .F4 L) =
      ⟨_, h0⟩ * ⟨_, h1⟩ * ⟨_, h2⟩ * ⟨_, h3⟩ := rfl
  rw [e, map_mul, map_mul, map_mul, e0, e1, e2, e3]
  exact rootReflection_qplusRoot_prod_smul v

end Hom

section Fixed

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem conjEntrywiseImage_eq_fixed_of_tag
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) [Finite K₂]
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL τ K₂}
    (hg : g ∈ adjointGroup τ K₂) (hz : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹) :
    conjEntrywiseImage K g = adjointGroup τ K₂ ⊓
      (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) := by
  have hfix := frobenius_fixed_eq_map_of_bijective (k := K) (τ := τ) hτ
    (σ : K₂ →+* K₂) hσ (Finite.injective_iff_bijective.1 σ.injective)
  have hzg : z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g = g := by
    rw [hz, inv_mul_cancel_right]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxF : baseChangeGL (algebraMap K K₂) x ∈ adjointGroup τ K₂ ⊓
        (Units.map (entrywiseHom (σ : K₂ →+* K₂))).eqLocus (MonoidHom.id _) := by
      rw [hfix]
      exact ⟨x, hx, rfl⟩
    obtain ⟨hxC, hxσ⟩ := Subgroup.mem_inf.1 hxF
    have hxσ' : Units.map (entrywiseHom (σ : K₂ →+* K₂)) (baseChangeGL (algebraMap K K₂) x) =
        baseChangeGL (algebraMap K K₂) x := hxσ
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hg hxC) (inv_mem hg)
    · change twistedEntrywise z (σ : K₂ →+* K₂)
          (g * baseChangeGL (algebraMap K K₂) x * g⁻¹) =
        g * baseChangeGL (algebraMap K K₂) x * g⁻¹
      rw [twistedEntrywise_apply, map_mul, map_mul, map_inv, hxσ']
      calc z * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g * baseChangeGL (algebraMap K K₂) x *
            (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹) * z⁻¹ =
          (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g) * baseChangeGL (algebraMap K K₂) x *
            (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := by group
        _ = g * baseChangeGL (algebraMap K K₂) x * g⁻¹ := by rw [hzg]
  · intro hy
    obtain ⟨hyC, hyF⟩ := Subgroup.mem_inf.1 hy
    have hyF' : z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) y * z⁻¹ = y := hyF
    have hσy : Units.map (entrywiseHom (σ : K₂ →+* K₂)) y = z⁻¹ * y * z := by
      calc Units.map (entrywiseHom (σ : K₂ →+* K₂)) y =
            z⁻¹ * (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) y * z⁻¹) * z := by group
        _ = z⁻¹ * y * z := by rw [hyF']
    have hσg : Units.map (entrywiseHom (σ : K₂ →+* K₂)) g = z⁻¹ * g := by
      calc Units.map (entrywiseHom (σ : K₂ →+* K₂)) g =
            z⁻¹ * (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g) := by group
        _ = z⁻¹ * g := by rw [hzg]
    have hu : g⁻¹ * y * g ∈ adjointGroup τ K₂ ⊓
        (Units.map (entrywiseHom (σ : K₂ →+* K₂))).eqLocus (MonoidHom.id _) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hg) hyC) hg, ?_⟩
      change Units.map (entrywiseHom (σ : K₂ →+* K₂)) (g⁻¹ * y * g) = g⁻¹ * y * g
      rw [map_mul, map_mul, map_inv, hσy, hσg]
      group
    rw [hfix] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxu]
    group

end Fixed

section Torus

variable {L : Type} [Field L]

variable (L) in
@[expose] def torusTorsionHomF4 (n : ℕ) : (Fin Tag.F4.rank → rootsOfUnity n L) →* ModGL .F4 L :=
  (rootDiagUnitHom .F4 L).comp (MonoidHom.compLeft (rootsOfUnity n L).subtype (Fin Tag.F4.rank))

theorem torusTorsionHomF4_injective (n : ℕ) : Function.Injective (torusTorsionHomF4 L n) :=
  fun _ _ h => funext fun i => Subtype.ext (congrFun (rootDiagUnit_injective h) i)

variable (L) in
@[expose] def torusTorsionF4 (n : ℕ) : Subgroup (ModGL .F4 L) :=
  (torusTorsionHomF4 L n).range

theorem rootDiagUnit_mem_torusTorsionF4_iff (n : ℕ) (c : Fin Tag.F4.rank → Lˣ) :
    rootDiagUnit .F4 c ∈ torusTorsionF4 L n ↔ c ^ n = 1 := by
  constructor
  · rintro ⟨s, hs⟩
    have hc : (fun i => ((s i : rootsOfUnity n L) : Lˣ)) = c := rootDiagUnit_injective hs
    rw [← hc]
    funext i
    simpa using (mem_rootsOfUnity _ _).1 (s i).2
  · intro h
    exact ⟨fun i => ⟨c i, (mem_rootsOfUnity _ _).2 (by simpa using congrFun h i)⟩, rfl⟩

theorem torusTorsionF4_le_torusGroup (n : ℕ) : torusTorsionF4 L n ≤ torusGroup .F4 L := by
  rintro _ ⟨s, rfl⟩
  exact F4_rootDiagUnit_mem_torusGroup _

theorem torusTorsionF4_mono {m n : ℕ} (h : m ∣ n) : torusTorsionF4 L m ≤ torusTorsionF4 L n := by
  rintro _ ⟨s, rfl⟩
  exact ⟨fun i => ⟨s i, rootsOfUnity_le_of_dvd h (s i).2⟩, rfl⟩

theorem mem_torusTorsionF4_iff {n : ℕ} {h : ModGL .F4 L} :
    h ∈ torusTorsionF4 L n ↔ h ∈ torusGroup .F4 L ∧ h ^ n = 1 := by
  constructor
  · intro hh
    refine ⟨torusTorsionF4_le_torusGroup n hh, ?_⟩
    obtain ⟨s, rfl⟩ := hh
    have hs : s ^ n = 1 := funext fun i => Subtype.ext (by
      simpa using (mem_rootsOfUnity _ _).1 (s i).2)
    rw [← map_pow, hs, map_one]
  · rintro ⟨hH, hn⟩
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
    refine (rootDiagUnit_mem_torusTorsionF4_iff n c).2 (rootDiagUnit_injective ?_)
    change rootDiagUnitHom .F4 L (c ^ n) = rootDiagUnitHom .F4 L 1
    rw [map_pow, map_one]
    exact hn

theorem nonempty_torusTorsionF4_mulEquiv [Finite L] {n : ℕ} [NeZero n]
    (hn : n ∣ Nat.card L - 1) :
    Nonempty (torusTorsionF4 L n ≃* (Fin 4 → Multiplicative (ZMod n))) := by
  have e : rootsOfUnity n L ≃* Multiplicative (ZMod n) :=
    mulEquivOfCyclicCardEq (by rw [card_rootsOfUnity_of_dvd_card_sub_one hn]; simp)
  exact ⟨(MonoidHom.ofInjective (torusTorsionHomF4_injective n)).symm.trans
    (MulEquiv.piCongrRight fun _ => e)⟩

theorem natCard_torusTorsionF4 [Finite L] {n : ℕ} [NeZero n] (hn : n ∣ Nat.card L - 1) :
    Nat.card (torusTorsionF4 L n) = n ^ 4 := by
  rw [torusTorsionF4,
    ← Nat.card_congr (MonoidHom.ofInjective (torusTorsionHomF4_injective n)).toEquiv,
    Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    card_rootsOfUnity_of_dvd_card_sub_one hn]
  rfl

theorem torusGroup_inf_eq_torusTorsionF4
    {z : ModGL .F4 L} (hz : z ∈ monomialSubgroup .F4 L)
    (hw : ∀ v : Fin Tag.F4.rank → ℤ, weylQuotientHom .F4 L ⟨z, hz⟩ • v = -v) (σ : L →+* L)
    {q : ℕ} (hσ : ∀ c, σ c = c ^ q) {Γ : Subgroup (ModGL .F4 L)}
    (hΓ : Γ = adjointGroup .F4 L ⊓ (twistedEntrywise z σ).eqLocus (MonoidHom.id _)) :
    torusGroup .F4 L ⊓ Γ = torusTorsionF4 L (q + 1) := by
  have key : ∀ c : Fin Tag.F4.rank → Lˣ,
      twistedEntrywise z σ (rootDiagUnit .F4 c) = rootDiagUnit .F4 c ↔ c ^ (q + 1) = 1 := by
    intro c
    rw [twistedEntrywise_rootDiagUnit hz hw σ hσ]
    constructor
    · intro h
      rw [pow_succ]
      exact inv_eq_iff_mul_eq_one.1 (rootDiagUnit_injective h)
    · intro h
      rw [inv_eq_iff_mul_eq_one.2 (by rw [← pow_succ]; exact h)]
  ext x
  constructor
  · rintro ⟨hxH, hxΓ⟩
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxH
    rw [hΓ] at hxΓ
    exact (rootDiagUnit_mem_torusTorsionF4_iff _ c).2 ((key c).1 hxΓ.2)
  · intro hx
    obtain ⟨s, rfl⟩ := hx
    have hc := (rootDiagUnit_mem_torusTorsionF4_iff (q + 1)
      (fun i => ((s i : rootsOfUnity (q + 1) L) : Lˣ))).1 ⟨s, rfl⟩
    refine ⟨F4_rootDiagUnit_mem_torusGroup _, ?_⟩
    rw [hΓ]
    exact ⟨torusGroup_le_adjointGroup_F4 (F4_rootDiagUnit_mem_torusGroup _), (key _).2 hc⟩

end Torus

theorem not_dvd_of_pow_four_mul_eq_ordF4 {q I p : ℕ} (hq : 1 ≤ q) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ q + 1) (h : (q + 1) ^ 4 * I = CFSG.Open.ordF4 q) : ¬ p ∣ I := by
  have hZ : ((q : ℤ) + 1) ^ 4 * I = (q : ℤ) ^ 24 * ((q : ℤ) ^ 12 - 1) * ((q : ℤ) ^ 8 - 1) *
      ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 2 - 1) := by
    have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ hq
    have h8 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ hq
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    rw [CFSG.Open.ordF4] at h'
    push_cast [Nat.cast_sub h12, Nat.cast_sub h8, Nat.cast_sub h6, Nat.cast_sub h2] at h'
    exact h'
  have hI : (I : ℤ) = (q : ℤ) ^ 24 * ((q : ℤ) - 1) ^ 4 *
      ((q : ℤ) ^ 10 + (q : ℤ) ^ 8 + (q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) *
      ((q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) := by
    have hne : ((q : ℤ) + 1) ^ 4 ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    rw [hZ]
    ring
  intro hdvd
  have hI0 : (I : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff I p).2 hdvd
  have hqp : (q : ZMod p) = -1 := by
    have h1 := (ZMod.natCast_eq_zero_iff (q + 1) p).2 hpq
    push_cast at h1
    linear_combination h1
  have h1152 : ((1152 : ℕ) : ZMod p) = 0 := by
    have h' := congrArg (Int.cast : ℤ → ZMod p) hI
    push_cast at h'
    rw [hqp, hI0] at h'
    rw [h']
    norm_num
  have hp1152 := (ZMod.natCast_eq_zero_iff 1152 p).1 h1152
  rw [show (1152 : ℕ) = 2 ^ 7 * 3 ^ 2 by norm_num] at hp1152
  rcases hp.dvd_mul.1 hp1152 with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega

section RankOne

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem rootSL2_comap_fixed_eq_of_tag
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) [CharP K₂ 2]
    (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K)
    {g z : ModGL τ K₂} (hg : g ∈ adjointGroup τ K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup τ K₂)
    (hw : ∀ v : Fin τ.rank → ℤ, weylQuotientHom τ K₂ ⟨z, hz⟩ • v = -v)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ P : GL (Fin 2) K₂,
      (rootRankOneGroup τ K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 τ K₂ α) =
        (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P) := by
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  obtain ⟨M, hM⟩ := exists_semilinearConj_rootSL2 hz hw σ hα
  have hΓ := conjEntrywiseImage_eq_fixed_of_tag hτ σ hσ hg hzdef
  have hinv : ∀ c, σ (σ c) = c := (exists_frobenius_eq_neg hdeg σ hσ).1
  have hinj : Function.Injective (rootSL2 τ K₂ α) := rootSL2_injective_of_field α
  have hinvol : ∀ A, semilinearConj M σ (semilinearConj M σ A) = A := fun A => hinj (by
    rw [hM, hM, twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv hzdef])
  have hfix : (semilinearConj M σ).eqLocus (MonoidHom.id _) =
      (rootRankOneGroup τ K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 τ K₂ α) := by
    ext A
    change semilinearConj M σ A = A ↔
      rootSL2 τ K₂ α A ∈ rootRankOneGroup τ K₂ α ⊓ conjEntrywiseImage K g
    rw [hΓ]
    constructor
    · intro h
      refine ⟨⟨A, rfl⟩, (exceptional_Lang_root_rank_one_data τ K₂ α).2.2.2.2.1 A, ?_⟩
      change twistedEntrywise z (σ : K₂ →+* K₂) (rootSL2 τ K₂ α A) = rootSL2 τ K₂ α A
      rw [← hM, h]
    · rintro ⟨-, -, h⟩
      exact hinj (by rw [hM]; exact h)
  obtain ⟨P, -, hP, -, -⟩ :=
    even_quadratic_semilinear_SL2_fixed_matrix_group K K₂ hdeg σ hσ M hinvol
  exact ⟨P, by rw [← hfix]; exact hP⟩

omit [Finite K] in
theorem specialLinearGroup_map_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K K₂)) := by
  intro A B h
  ext i j
  have h1 := congrArg (fun X : SL2 K₂ => (X : Matrix (Fin 2) (Fin 2) K₂) i j) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at h1
  exact (algebraMap K K₂).injective h1

theorem conjSL_injective (P : GL (Fin 2) K₂) : Function.Injective (conjSL P) := fun A B h => by
  have h1 := congrArg (conjSL P⁻¹) h
  rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1

theorem isSimpleGroup_of_rootSL2_comap_eq_of_tag
    [CharP K 2] (hK4 : 4 ≤ Nat.card K) {τ : Tag}
    {α : Fin τ.rank → ℤ} {R : Subgroup (ModGL τ K₂)} (hR : R ≤ rootRankOneGroup τ K₂ α)
    {P : GL (Fin 2) K₂}
    (hRP : R.comap (rootSL2 τ K₂ α) =
      (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P)) :
    IsSimpleGroup R ∧ Group.IsPerfect R ∧ ∃ x y : R, x * y ≠ y * x := by
  have hinj : Function.Injective (rootSL2 τ K₂ α) := rootSL2_injective_of_field α
  have hmap : (R.comap (rootSL2 τ K₂ α)).map (rootSL2 τ K₂ α) = R := by
    rw [Subgroup.map_comap_eq]
    exact inf_of_le_right hR
  let e : SL2 K ≃* R :=
    ((((MonoidHom.ofInjective (specialLinearGroup_map_injective (K := K) (K₂ := K₂))).trans
      (Subgroup.equivMapOfInjective _ _ (conjSL_injective P))).trans
      (MulEquiv.subgroupCongr hRP.symm)).trans
        (Subgroup.equivMapOfInjective _ _ hinj)).trans (MulEquiv.subgroupCongr hmap)
  have h4 := exists_finset_card_four hK4
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl (Or.inr h4)
  have : IsSimpleGroup (SL2 K) :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup
  have : Group.IsPerfect (SL2 K) := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  refine ⟨e.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective,
    e (uSL 1), e (vSL 1), fun h => uSL_mul_vSL_ne (K := K) ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact e.injective h

omit [Finite K] in
theorem orderOf_uSL_one [CharP K 2] : orderOf (uSL (1 : K)) = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [pow_two]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [uSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · have h1 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [uSL] at h1

end RankOne

section Criterion

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem torusRootChar_rootDiagUnit {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (rootDiagUnit τ a) α = ((rootChar a α : Lˣ) : L) :=
  torusRootChar_eq_of_apply hα (rootDiag_rootVec a hα)

theorem qplus_odd_centralizer_criterion
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K)
    {g z : ModGL .F4 K₂} (hg : g ∈ adjointGroup .F4 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup .F4 K₂)
    (hw : ∀ v : Fin Tag.F4.rank → ℤ, weylQuotientHom .F4 K₂ ⟨z, hz⟩ • v = -v)
    (hTodd : Odd (Nat.card (torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g :
      Subgroup (ModGL .F4 K₂))))
    {x : ModGL .F4 K₂} (hxT : x ∈ torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g)
    (hx : orderOf x = p) :
    (Odd (Nat.card (conjEntrywiseImage K g ⊓ Subgroup.centralizer {x} :
        Subgroup (ModGL .F4 K₂))) ↔ ∀ α, IsRoot .F4 α → torusRootChar x α ≠ 1) ∧
    ((∀ α, IsRoot .F4 α → torusRootChar x α ≠ 1) →
      conjEntrywiseImage K g ⊓ Subgroup.centralizer {x} =
        torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g) := by
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT.1
  have hΓ := conjEntrywiseImage_eq_fixed_of_tag (Or.inr rfl) σ hσ hg hzdef
  have hΓC : conjEntrywiseImage K g ≤ adjointGroup .F4 K₂ := by
    rw [hΓ]
    exact inf_le_left
  have hreg : (∀ α, IsRoot .F4 α → torusRootChar (rootDiagUnit .F4 a) α ≠ 1) ↔
      ∀ α, IsRoot .F4 α → rootChar a α ≠ 1 := by
    refine forall_congr' fun α => imp_congr_right fun hα => ?_
    rw [torusRootChar_rootDiagUnit a hα, Ne, Units.val_eq_one]
  have hcent : (∀ α, IsRoot .F4 α → torusRootChar (rootDiagUnit .F4 a) α ≠ 1) →
      conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .F4 a} =
        torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g := by
    intro h
    have hCA := F4_centralizer_eq_torusGroup_of_regular hp hp3 hx (hreg.1 h)
    calc conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .F4 a} =
          conjEntrywiseImage K g ⊓
            (adjointGroup .F4 K₂ ⊓ Subgroup.centralizer {rootDiagUnit .F4 a}) := by
          rw [← inf_assoc, inf_of_le_left hΓC]
      _ = torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g := by rw [hCA, inf_comm]
  refine ⟨⟨fun hodd => ?_, fun h => by rw [hcent h]; exact hTodd⟩, hcent⟩
  by_contra hne
  push Not at hne
  obtain ⟨α, hα, hα1⟩ := hne
  rw [torusRootChar_rootDiagUnit a hα, Units.val_eq_one] at hα1
  obtain ⟨P, hP⟩ := rootSL2_comap_fixed_eq_of_tag (Or.inr rfl) hdeg σ hσ hg hzdef hz hw hα
  set t := conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K K₂) (uSL 1)) with ht
  have htR : rootSL2 .F4 K₂ α t ∈ rootRankOneGroup .F4 K₂ α ⊓ conjEntrywiseImage K g := by
    have : t ∈ (rootRankOneGroup .F4 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .F4 K₂ α) := by
      rw [hP]
      exact ⟨_, ⟨uSL 1, rfl⟩, rfl⟩
    exact this
  have hcomm := (exceptional_Lang_root_rank_one_torus_transport .F4 K₂ hα).2.2.2.2.2.2.2 a hα1
    _ htR.1
  have hD : rootSL2 .F4 K₂ α t ∈ conjEntrywiseImage K g ⊓
      Subgroup.centralizer {rootDiagUnit .F4 a} :=
    ⟨htR.2, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩
  have hord : orderOf (rootSL2 .F4 K₂ α t) = 2 := by
    rw [orderOf_injective _ (rootSL2_injective_of_field α), ht,
      orderOf_injective _ (conjSL_injective P),
      orderOf_injective _ (specialLinearGroup_map_injective (K := K) (K₂ := K₂)),
      orderOf_uSL_one]
  have h2 := orderOf_dvd_natCard (⟨_, hD⟩ : ↥(conjEntrywiseImage K g ⊓
    Subgroup.centralizer {rootDiagUnit .F4 a}))
  rw [Subgroup.orderOf_mk, hord] at h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

end Criterion

end EvenF4QPlus

open EvenF4QPlus

theorem even_F4_qplus_torus_and_odd_inner_centralizer_criterion
    (K : Type) [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1)
    (K₂ : Type) [Field K₂] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    (∀ i, IsRoot .F4 (qplusRoot i)) ∧
    (∀ i j, iform (qplusRoot i) (qplusRoot j) = if i = j then 4 else 0) ∧
    (∃ ω : K₂, ω + σ ω = 1) ∧
    (∀ ω : K₂, ∃ P : SL2 K₂, (P : Matrix (Fin 2) (Fin 2) K₂) = !![ω, ω + 1; 1, 1]) ∧
    ∀ (ω : K₂) (P : SL2 K₂), ω + σ ω = 1 →
      (P : Matrix (Fin 2) (Fin 2) K₂) = !![ω, ω + 1; 1, 1] →
    ∀ g z : ModGL .F4 K₂,
      g = rootSL2 .F4 K₂ (qplusRoot 0) P⁻¹ * rootSL2 .F4 K₂ (qplusRoot 1) P⁻¹ *
        rootSL2 .F4 K₂ (qplusRoot 2) P⁻¹ * rootSL2 .F4 K₂ (qplusRoot 3) P⁻¹ →
      z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ →
      g ∈ adjointGroup .F4 K₂ ∧ z ∈ adjointGroup .F4 K₂ ∧
      (∃ hz : z ∈ monomialSubgroup .F4 K₂,
        ∀ v : Fin Tag.F4.rank → ℤ, weylQuotientHom .F4 K₂ ⟨z, hz⟩ • v = -v) ∧
      (∀ y, twistedEntrywise z (σ : K₂ →+* K₂) (twistedEntrywise z (σ : K₂ →+* K₂) y) = y) ∧
      conjEntrywiseImage K g =
        adjointGroup .F4 K₂ ⊓ (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) ∧
      Nonempty ((torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .F4 K₂)) ≃*
        (Fin 4 → Multiplicative (ZMod (Nat.card K + 1)))) ∧
      Odd (Nat.card (torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .F4 K₂))) ∧
      (∃ S : Sylow p (conjEntrywiseImage K g), (S : Subgroup (conjEntrywiseImage K g)) ≤
        (torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g).subgroupOf (conjEntrywiseImage K g)) ∧
      (∃ V : Subgroup (ModGL .F4 K₂), (∀ h, h ∈ V ↔ h ∈ torusGroup .F4 K₂ ∧ h ^ p = 1) ∧
        (∀ h, h ∈ V ↔ h ∈ torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g ∧ h ^ p = 1) ∧
        Nat.card V = p ^ 4) ∧
      (∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → ∃ Pα : GL (Fin 2) K₂,
        (rootRankOneGroup .F4 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .F4 K₂ α) =
          (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL Pα) ∧
        IsSimpleGroup
          (rootRankOneGroup .F4 K₂ α ⊓ conjEntrywiseImage K g : Subgroup (ModGL .F4 K₂)) ∧
        Group.IsPerfect
          (rootRankOneGroup .F4 K₂ α ⊓ conjEntrywiseImage K g : Subgroup (ModGL .F4 K₂)) ∧
        ∃ x y : (rootRankOneGroup .F4 K₂ α ⊓ conjEntrywiseImage K g : Subgroup (ModGL .F4 K₂)),
          x * y ≠ y * x) ∧
      ∀ x ∈ torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g, orderOf x = p →
        (Odd (Nat.card (conjEntrywiseImage K g ⊓ Subgroup.centralizer {x} :
            Subgroup (ModGL .F4 K₂))) ↔ ∀ α, IsRoot .F4 α → torusRootChar x α ≠ 1) ∧
        ((∀ α, IsRoot .F4 α → torusRootChar x α ≠ 1) →
          conjEntrywiseImage K g ⊓ Subgroup.centralizer {x} =
            torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd₂ : Nat.card K + 1 ∣ Nat.card K₂ - 1 := by
    refine ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hq4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have := five_le_of_prime_of_three_lt hp hp3
    omega
  have hinv : ∀ c, σ (σ c) = c := (exists_frobenius_eq_neg hdeg σ hσ).1
  refine ⟨isRoot_qplusRoot, iform_qplusRoot, ?_, fun ω => ⟨evenQuadraticP ω, rfl⟩,
    fun ω P hω hP g z hgdef hzdef => ?_⟩
  · obtain ⟨-, ω, hσω⟩ := exists_frobenius_eq_add_one hdeg σ hσ
    exact ⟨ω, by rw [hσω, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]⟩
  have h2 : (2 : K₂) = 0 := CharTwo.two_eq_zero
  have hσω : σ ω = ω + 1 := by linear_combination hω - ω * h2
  have hPeq : P = evenQuadraticP ω := Subtype.ext (by rw [hP]; rfl)
  have hPn := evenQuadraticP_mul_nSL σ hσω
  rw [← hPeq] at hPn
  have hg' : g = qplusHom K₂ P⁻¹ := hgdef
  have hg : g ∈ adjointGroup .F4 K₂ := by
    rw [hg']
    exact qplusHom_mem_adjointGroup K₂ _
  have hzeq : z = qplusHom K₂ (nSL 1) := by
    rw [hzdef, hg']
    exact qplusHom_mul_entrywise_inv_eq K₂ (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .F4 K₂,
      ∀ v : Fin Tag.F4.rank → ℤ, weylQuotientHom .F4 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact qplusHom_nSL_mem_monomial K₂
  have hzC : z ∈ adjointGroup .F4 K₂ := by
    rw [hzeq]
    exact qplusHom_mem_adjointGroup K₂ _
  have hΓ := conjEntrywiseImage_eq_fixed_of_tag (Or.inr rfl) σ hσ hg hzdef
  have hT := torusGroup_inf_eq_torusTorsionF4 hzN hw (σ : K₂ →+* K₂) hσ hΓ
  have hTΓ : torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g ≤ conjEntrywiseImage K g := inf_le_right
  have hcardΓ : Nat.card (conjEntrywiseImage K g) = CFSG.Open.ordF4 (Nat.card K) := by
    rw [natCard_conjEntrywiseImage, card_adjointGroup_F4]
  have hcardT : Nat.card (torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .F4 K₂)) =
      (Nat.card K + 1) ^ 4 := by
    rw [hT]
    exact natCard_torusTorsionF4 hdvd₂
  have hidx : ¬ p ∣ ((torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g).subgroupOf
      (conjEntrywiseImage K g)).index := by
    refine not_dvd_of_pow_four_mul_eq_ordF4 hq1 hp hp3 hpq ?_
    rw [← hcardΓ, ← hcardT, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTΓ).toEquiv]
    exact Subgroup.card_mul_index _
  have hTodd : Odd (Nat.card (torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g :
      Subgroup (ModGL .F4 K₂))) := by
    rw [hcardT]
    exact (even_card_of_charTwo (K := K)).add_one.pow
  refine ⟨hg, hzC, ⟨hzN, hw⟩, twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv hzdef,
    hΓ, ?_, hTodd, exists_sylow_le_of_not_dvd_index hidx, ?_, fun α hα => ?_,
    fun x hx hxp => qplus_odd_centralizer_criterion hp hp3 hdeg σ hσ hg hzdef hzN hw hTodd hx hxp⟩
  · rw [hT]
    exact nonempty_torusTorsionF4_mulEquiv hdvd₂
  · have : NeZero p := ⟨hp.ne_zero⟩
    refine ⟨torusTorsionF4 K₂ p, fun h => mem_torusTorsionF4_iff, fun h => ?_,
      natCard_torusTorsionF4 (hpq.trans hdvd₂)⟩
    rw [mem_torusTorsionF4_iff]
    constructor
    · rintro ⟨hH, hp1⟩
      refine ⟨?_, hp1⟩
      rw [hT]
      exact torusTorsionF4_mono hpq (mem_torusTorsionF4_iff.2 ⟨hH, hp1⟩)
    · rintro ⟨hT', hp1⟩
      exact ⟨hT'.1, hp1⟩
  · obtain ⟨Pα, hPα⟩ := rootSL2_comap_fixed_eq_of_tag (Or.inr rfl) hdeg σ hσ hg hzdef hzN hw hα
    exact ⟨Pα, hPα, isSimpleGroup_of_rootSL2_comap_eq_of_tag hq4 inf_le_left hPα⟩

end CFSG.RankThree.Chevalley

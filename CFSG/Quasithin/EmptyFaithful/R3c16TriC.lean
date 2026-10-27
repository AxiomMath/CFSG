module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTriality
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTrialityAlgebra
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.Quasithin.EmptyFaithful.R3c16Cl
public import CFSG.Quasithin.EmptyFaithful.R3c11Core

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.ExceptionalCat CFSG.Blueprint
  CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15 CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.B113Lie
open scoped commutatorElement

section Center

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

include hσ3 in
theorem triality_center_x6
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hz : z ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hzc : ∀ q ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), q * z = z * q) :
    ∃ c : trialityFixedField K σ.toRingHom, (z : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨⟨f₁, hf₁i, hf₁⟩, ⟨f₂, hf₂i, hf₂⟩, ⟨f₃, hf₃i, hf₃⟩, ⟨f₄, hf₄i, hf₄⟩,
    ⟨f₅, hf₅i, hf₅⟩, ⟨f₆, hf₆i, hf₆⟩, hbij, -, -⟩ :=
    even_triality_positive_orbit_parametrization K σ hσ3
  obtain ⟨k14, k34, k25, c15, c16, -, -, c26, c35, -, c45, c46, c56, htr, hnd⟩ :=
    even_triality_trace_commutators K σ.toRingHom hσ3
  have hCle := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hzP : (z : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ := hz
  have a₁ := add_of_hom f₁ (trialityX₁ K τ₀) hf₁
  have a₂ := add_of_hom f₂ (trialityX₂ K τ₀) hf₂
  have a₃ := add_of_hom f₃ (trialityX₃ K τ₀) hf₃
  have a₄ := add_of_hom f₄ (trialityX₄ K τ₀) hf₄
  have a₅ := add_of_hom f₅ (trialityX₅ K τ₀) hf₅
  have a₆ := add_of_hom f₆ (trialityX₆ K τ₀) hf₆
  have mP : ∀ {M : Type} [AddCommGroup M] (f : Multiplicative M →* ↥(graphFixedPosUnipotent
      TwistTag.D4 K τ₀)) (X : M → adjointGroup TwistTag.D4.tag K),
      (∀ c : M, ((f (Multiplicative.ofAdd c) : graphFixedPosUnipotent TwistTag.D4 K τ₀) :
        ModGL TwistTag.D4.tag K) = (X c : ModGL TwistTag.D4.tag K)) →
      ∀ c, (X c : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ :=
    fun f X hf c => by rw [← hf c]; exact (f (Multiplicative.ofAdd c)).2
  have mP₁ := mP f₁ (trialityX₁ K τ₀) hf₁
  have mP₂ := mP f₂ (trialityX₂ K τ₀) hf₂
  have mP₄ := mP f₄ (trialityX₄ K τ₀) hf₄
  have mP₅ := mP f₅ (trialityX₅ K τ₀) hf₅
  obtain ⟨⟨a, b, c, d, e, f⟩, -, hzN⟩ := hbij.2.2 hzP
  have hzz' : (z : ModGL TwistTag.D4.tag K) =
      ((trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
        trialityX₅ K τ₀ e * trialityX₆ K τ₀ f : adjointGroup TwistTag.D4.tag K) :
          ModGL TwistTag.D4.tag K) := hzN.symm
  set Z' : adjointGroup TwistTag.D4.tag K :=
    trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
      trialityX₅ K τ₀ e * trialityX₆ K τ₀ f with hZ'
  have hcent : ∀ y : adjointGroup TwistTag.D4.tag K,
      (y : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ →
      y * Z' = Z' * y := by
    intro y hy
    have h := congrArg Subtype.val (hzc ⟨(y : ModGL TwistTag.D4.tag K), hCle hy⟩ hy)
    apply Subtype.ext
    have e1 : ((y * Z' : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
        (y : ModGL TwistTag.D4.tag K) * (Z' : ModGL TwistTag.D4.tag K) := rfl
    have e2 : ((Z' * y : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
        (Z' : ModGL TwistTag.D4.tag K) * (y : ModGL TwistTag.D4.tag K) := rfl
    rw [e1, e2, ← hzz']
    exact h
  have hnd₁ : ∀ s : K, (∀ t : K, trialityTrace K τ₀ hσ3 (s * t) = 0) → s = 0 := fun s hs =>
    hnd.1 s fun t => (htr s t).trans (hs t)
  have hnd₂ : ∀ t : K, (∀ s : K, trialityTrace K τ₀ hσ3 (s * t) = 0) → t = 0 := fun t ht =>
    hnd.2 t fun s => (htr s t).trans (ht s)
  have inj : ∀ (a a' : K) (b b' : trialityFixedField K τ₀) (c c' d d' : K)
      (e e' f f' : trialityFixedField K τ₀),
      trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
        trialityX₅ K τ₀ e * trialityX₆ K τ₀ f =
      trialityX₁ K τ₀ a' * trialityX₂ K τ₀ b' * trialityX₃ K τ₀ c' * trialityX₄ K τ₀ d' *
        trialityX₅ K τ₀ e' * trialityX₆ K τ₀ f' →
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
    intro a a' b b' c c' d d' e e' f f' h
    have := hbij.2.1 (Set.mem_univ (a, b, c, d, e, f)) (Set.mem_univ (a', b', c', d', e', f'))
      (congrArg Subtype.val h)
    simp only [Prod.mk.injEq] at this
    exact this
  have key := triality_center_aux (trialityX₁ K τ₀) (trialityX₃ K τ₀) (trialityX₄ K τ₀)
    (trialityX₂ K τ₀) (trialityX₅ K τ₀) (trialityX₆ K τ₀)
    (fun s t => trialityTrace K τ₀ hσ3 (s * t)) (fun b e => b * e) (1 : trialityFixedField K τ₀)
    a₁ a₂ a₃ a₄ a₅ a₆ inj c15 c16 c26 c35 c45 c46 c56 k14 k34 k25 hnd₁ hnd₂
    (fun e => one_mul e) (fun b => mul_one b) a b c d e f
    (hcent _ (mP₅ 1)) (fun t => hcent _ (mP₄ t)) (fun t => hcent _ (mP₁ t))
    (hcent _ (mP₂ 1))
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := key
  have z1 := zero_of_add (trialityX₁ K τ₀) a₁
  have z2 := zero_of_add (trialityX₂ K τ₀) a₂
  have z3 := zero_of_add (trialityX₃ K τ₀) a₃
  have z4 := zero_of_add (trialityX₄ K τ₀) a₄
  have z5 := zero_of_add (trialityX₅ K τ₀) a₅
  have z6 := zero_of_add (trialityX₆ K τ₀) a₆
  have hz6 : (z : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) (f : K) := by
    rw [hzz', hZ', z1, z2, z3, z4, z5]
    simp only [one_mul]
    rfl
  exact ⟨f, hz6⟩

include hσ3 in
theorem triality_center_unique
    (hfix : ∀ c : K, σ c = c → c = 0 ∨ c = 1)
    {z z' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hz : z ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hzc : ∀ q ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), q * z = z * q) (hz1 : z ≠ 1)
    (hz' : z' ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hzc' : ∀ q ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), q * z' = z' * q) (hz1' : z' ≠ 1) :
    z = z' := by
  obtain ⟨c, hc⟩ := triality_center_x6 σ hσ3 hz hzc
  obtain ⟨c', hc'⟩ := triality_center_x6 σ hσ3 hz' hzc'
  have key : ∀ (w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (d : trialityFixedField K σ.toRingHom),
      w ≠ 1 → (w : ModGL TwistTag.D4.tag K) =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) (d : K) →
      (w : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K (trialityRoot 5) 1 := by
    intro w d hw1 hwd
    have hd0 : (d : K) ≠ 0 := by
      intro h0
      apply hw1
      apply Subtype.ext
      rw [hwd, h0, pinnedX_zero]
      rfl
    have hdfix : σ (d : K) = d := d.2
    rcases hfix _ hdfix with h0 | h1
    · exact absurd h0 hd0
    · rw [hwd, h1]
  exact Subtype.ext ((key z c hz1 hc).trans (key z' c' hz1' hc').symm)

end Center

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem not_elData_of_zeta_route {T V H : Subgroup G} {ζ : MulAut G} (hT : IsSylowTwoOf T ⊤)
    (hA : ∀ β : G ≃* G, (∀ q ∈ T, β q = q) → ∃ x : G, ∀ y : G, β y = x⁻¹ * y * x)
    (hOdd : ∀ φ : MulAut G, (∀ u ∈ T, φ u = u) → Odd (orderOf φ) → φ = 1)
    (hZ : ∀ g : G, (∀ y : G, g * y = y * g) → g = 1)
    (hU : ∀ z ∈ T, ∀ z' ∈ T, z ≠ 1 → z' ≠ 1 → (∀ t ∈ T, t * z = z * t) →
      (∀ t ∈ T, t * z' = z' * t) → z = z')
    (h : ElData T V H ζ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
  obtain ⟨x, hx⟩ := hA ζ h.fixT
  have hxT : ∀ t ∈ T, t * x = x * t := fun t ht => by
    have h1 := hx t
    rw [h.fixT t ht] at h1
    calc t * x = x * (x⁻¹ * t * x) := by group
      _ = x * t := by rw [← h1]
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply h.ne
    ext y
    rw [hx y]
    simp
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hg : x ^ (2 ^ k) = 1 := by
    have hgo : orderOf (x ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hkm]; exact dvd_mul_right _ _),
        hkm, Nat.mul_div_cancel_left _ (by positivity)]
    have hcomm : ∀ t ∈ T, t * x ^ (2 ^ k) = x ^ (2 ^ k) * t := fun t ht =>
      ((show Commute t x from hxT t ht).pow_right (2 ^ k)).eq
    have hodd : Odd (orderOf (MulAut.conj (x ^ (2 ^ k)))) :=
      Odd.of_dvd_nat (hgo ▸ hm) (orderOf_map_dvd (MulAut.conj : G →* MulAut G) (x ^ (2 ^ k)))
    have h1 := hOdd (MulAut.conj (x ^ (2 ^ k))) (fun u hu => by
      rw [MulAut.conj_apply]
      calc x ^ (2 ^ k) * u * (x ^ (2 ^ k))⁻¹ = (u * x ^ (2 ^ k)) * (x ^ (2 ^ k))⁻¹ := by
            rw [← hcomm u hu]
        _ = u := by group) hodd
    refine hZ _ fun y => ?_
    have h2 := DFunLike.congr_fun h1 y
    rw [MulAut.conj_apply, MulAut.one_apply] at h2
    calc x ^ (2 ^ k) * y = (x ^ (2 ^ k) * y * (x ^ (2 ^ k))⁻¹) * x ^ (2 ^ k) := by group
      _ = y * x ^ (2 ^ k) := by rw [h2]
  have hZ2 : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    rintro ⟨g, hg'⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxT)
  have hsup : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers x) :=
    hp.to_sup_of_normal_left' hZ2 (Subgroup.zpowers_le.2 hxN)
  have hxTT : x ∈ T := by
    have hmax : T ⊔ Subgroup.zpowers x = T := (hp.toSylow hi).is_maximal' hsup le_sup_left
    have hx' : x ∈ T ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rwa [hmax] at hx'
  have hV0 : V ≠ ⊥ := by
    intro hb0
    have h4 := h.V4
    rw [hb0, Subgroup.card_bot] at h4
    omega
  obtain ⟨v, hvV, hv1, hvc⟩ := exists_central_of_normal hp h.VT hV0 h.TV
  have hvx : v = x := hU v (h.VT hvV) x hxTT hv1 hx1 hvc hxT
  refine hv1 (h.fix v hvV fun k hk => ?_)
  have hk' := h.fixH k hk
  rw [hx k] at hk'
  rw [hvx]
  calc k * x = x * (x⁻¹ * k * x) := by group
    _ = x * k := by rw [hk']

theorem false_of_unique_central {T V₁ V₂ : Subgroup G} (hT : IsPGroup 2 ↥T) (hV₁T : V₁ ≤ T)
    (hV₂T : V₂ ≤ T) (h4₁ : Nat.card V₁ = 4) (h4₂ : Nat.card V₂ = 4)
    (hN₁ : T ≤ Subgroup.normalizer (V₁ : Set G)) (hN₂ : T ≤ Subgroup.normalizer (V₂ : Set G))
    (hinf : V₁ ⊓ V₂ = ⊥)
    (hU : ∀ z ∈ T, ∀ z' ∈ T, z ≠ 1 → z' ≠ 1 → (∀ t ∈ T, t * z = z * t) →
      (∀ t ∈ T, t * z' = z' * t) → z = z') : False := by
  have hne : ∀ V : Subgroup G, Nat.card V = 4 → V ≠ ⊥ := fun V h4 hb => by
    rw [hb, Subgroup.card_bot] at h4
    omega
  obtain ⟨v₁, hv₁, hv₁1, hv₁c⟩ := exists_central_of_normal hT hV₁T (hne V₁ h4₁) hN₁
  obtain ⟨v₂, hv₂, hv₂1, hv₂c⟩ := exists_central_of_normal hT hV₂T (hne V₂ h4₂) hN₂
  have hvv : v₁ = v₂ := hU v₁ (hV₁T hv₁) v₂ (hV₂T hv₂) hv₁1 hv₂1 hv₁c hv₂c
  have hmem : v₁ ∈ V₁ ⊓ V₂ := ⟨hv₁, hvv ▸ hv₂⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact hv₁1 hmem

end Abstract

section One

theorem triality_one_setup
    {X : Type} [Group X] [Finite X] (hX : ChevalleyExceptionalModel X .trialityD4 2 1)
    {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (φ : X ≃* G),
      IsSylowTwoOf (T.map φ.toMonoidHom) ⊤ ∧
      (∀ β : G ≃* G, (∀ q ∈ T.map φ.toMonoidHom, β q = q) →
        ∃ x : G, ∀ y : G, β y = x⁻¹ * y * x) ∧
      (∀ α : MulAut G, (∀ u ∈ T.map φ.toMonoidHom, α u = u) → Odd (orderOf α) → α = 1) ∧
      (∀ g : G, (∀ y : G, g * y = y * g) → g = 1) ∧
      (∀ z ∈ T.map φ.toMonoidHom, ∀ z' ∈ T.map φ.toMonoidHom, z ≠ 1 → z' ≠ 1 →
        (∀ t ∈ T.map φ.toMonoidHom, t * z = z * t) →
        (∀ t ∈ T.map φ.toMonoidHom, t * z' = z' * t) → z = z') := by
  obtain ⟨K, hF, hFin, σ, φ, hK, hσ, hφ, -, -⟩ := even_rank_two_residual_triality hX hT
  have hK3 : Nat.card K = 2 ^ (3 * 1) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have hσ3 : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => by
    rw [ringHom_pow_three_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  have hfix : ∀ c : K, σ c = c → c = 0 ∨ c = 1 := by
    intro c hc
    have h2 : c * (c - 1) = 0 := by
      have h : c ^ (2 ^ 1) = c := (hσ c).symm.trans hc
      rw [pow_one, sq] at h
      rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.1 h2 with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  have hT' : IsSylowTwoOf (T.map φ.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map φ.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
    exact hi
  refine ⟨_, inferInstance, inferInstance, φ, hT', ?_, ?_, ?_, ?_⟩
  · exact sylowCentralizingAutInner_triality σ (le_refl 1) hK hσ _ hT'
  · exact OddAutAt.map φ (B113Lie.d4_sylowFacts (le_refl 1) hX hT).2.2
  · intro g hg
    have hgc : g ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      Subgroup.mem_center_iff.2 fun z => (hg z).symm
    rw [exceptional_fixed_center_trivial TwistTag.D4 K σ] at hgc
    exact Subgroup.mem_bot.1 hgc
  · intro z hz z' hz' hz1 hz1' hzc hzc'
    rw [hφ] at hz hz' hzc hzc'
    exact triality_center_unique σ hσ3 hfix hz hzc hz1 hz' hzc' hz1'

theorem not_elConfig_of_triality_one
    {X : Type} [Group X] [Finite X] (hX : ChevalleyExceptionalModel X .trialityD4 2 1) :
    ¬ ElConfig X := by
  rintro ⟨T, V, H, ζ, hT, hd⟩
  obtain ⟨G, _, _, φ, -, hA, hOdd, hZ, hU⟩ := triality_one_setup hX hT
  exact not_elData_of_zeta_route (K1.isSylowTwoOf_top_iff.mpr ⟨
    (K1.isSylowTwoOf_top_iff.mp hT).1.map φ.toMonoidHom, by
      rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
      exact (K1.isSylowTwoOf_top_iff.mp hT).2⟩) hA hOdd hZ hU (hd.map φ)

theorem noTwoKlein_of_triality_one
    {X : Type} [Group X] [Finite X] (hX : ChevalleyExceptionalModel X .trialityD4 2 1) :
    NoTwoKlein X := by
  intro T V₁ V₂ hT hV₁T hV₂T h4₁ h4₂ _ _ hN₁ hN₂ hinf
  obtain ⟨G, _, _, φ, hT', -, -, -, hU⟩ := triality_one_setup hX hT
  have key : ∀ V : Subgroup X, V ≤ T → Nat.card V = 4 → T ≤ Subgroup.normalizer (V : Set X) →
      V.map φ.toMonoidHom ≤ T.map φ.toMonoidHom ∧ Nat.card (V.map φ.toMonoidHom) = 4 ∧
        T.map φ.toMonoidHom ≤ Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup G) : Set G) := by
    intro V hVT hV4 hNV
    refine ⟨Subgroup.map_mono hVT, ?_, ?_⟩
    · rw [← hV4]
      exact (Nat.card_congr (V.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm
    · rintro _ ⟨t₀, ht₀, rfl⟩
      exact (R3c11.mem_normalizer_map_equiv_iff φ V t₀).mpr (hNV ht₀)
  obtain ⟨k₁, k₂, k₃⟩ := key V₁ hV₁T h4₁ hN₁
  obtain ⟨l₁, l₂, l₃⟩ := key V₂ hV₂T h4₂ hN₂
  refine false_of_unique_central (K1.isSylowTwoOf_top_iff.mp hT').1 k₁ l₁ k₂ l₂ k₃ l₃ ?_ hU
  rw [← Subgroup.map_inf _ _ _ φ.injective, hinf, Subgroup.map_bot]

variable {G : Type} [Group G] [Finite G]

theorem elim15343_of_triality_one
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L)
    (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 1) : False :=
  not_elConfig_of_triality_one h (elConfig_of_ctx1 c o hN hYL)

theorem cl15335_of_triality_one
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 1) :
    False := by
  rcases c.hyp.cases with hY | hU
  · exact cl_case1_of_noTwoKlein h113 c hN hYL hY (noTwoKlein_of_triality_one h)
  · exact not_elConfig_of_triality_one h (elConfig_of_ctx2 h113 c hN hYL hU)

end One

end CFSG.Quasithin.R3c16

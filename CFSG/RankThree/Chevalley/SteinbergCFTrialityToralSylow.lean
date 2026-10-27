module

public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem comm_and_two_generated_of_injective_prod {M₁ M₂ G : Type*} [CommGroup M₁] [IsCyclic M₁]
    [CommGroup M₂] [IsCyclic M₂] [Group G] (ι : G →* M₁ × M₂) (hι : Function.Injective ι) :
    (∀ x y : G, x * y = y * x) ∧ ∃ x y : G, Subgroup.closure {x, y} = ⊤ := by
  refine ⟨fun x y => hι (by rw [map_mul, map_mul, mul_comm]), ?_⟩
  set f : G →* M₂ := (MonoidHom.snd M₁ M₂).comp ι
  set f₀ : G →* M₁ := (MonoidHom.fst M₁ M₂).comp ι
  obtain ⟨⟨m, x₀, rfl⟩, hm⟩ := IsCyclic.exists_generator (α := f.range)
  have hinj₀ : Function.Injective (f₀.comp f.ker.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨g, hg⟩ hg0
    rw [MonoidHom.mem_ker] at hg hg0
    rw [Subgroup.mem_bot]
    refine Subtype.ext (hι (Prod.ext ?_ ?_))
    · simpa [f₀] using hg0
    · simpa [f] using hg
  have : IsCyclic f.ker := isCyclic_of_injective _ hinj₀
  obtain ⟨⟨y₀, hy₀⟩, hy⟩ := IsCyclic.exists_generator (α := f.ker)
  refine ⟨x₀, y₀, eq_top_iff.2 fun g _ => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hm ⟨f g, g, rfl⟩)
  have hk' : f (g * x₀ ^ (-k)) = 1 := by
    have := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_zpow] at this
    rw [map_mul, map_zpow, ← this, zpow_neg, mul_inv_cancel]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hy ⟨_, hk'⟩)
  have hj' : y₀ ^ j = g * x₀ ^ (-k) := by
    have := congrArg Subtype.val hj
    simpa only [SubgroupClass.coe_zpow] using this
  have hg : g = y₀ ^ j * x₀ ^ k := by
    rw [hj', zpow_neg, inv_mul_cancel_right]
  have hx₀ : x₀ ∈ Subgroup.closure ({x₀, y₀} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy₀' : y₀ ∈ Subgroup.closure ({x₀, y₀} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rw [hg]
  exact mul_mem (zpow_mem hy₀' _) (zpow_mem hx₀ _)

variable {K : Type} [Field K]

theorem index_graphFixedRootTorus_D4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ((graphFixedRootTorus TwistTag.D4 K σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ)).index =
      (ℓ ^ f) ^ 12 * (ℓ ^ f + 1) * ((ℓ ^ f) ^ 3 + 1) * ((ℓ ^ f) ^ 8 + (ℓ ^ f) ^ 4 + 1) := by
  obtain ⟨hC, hH, -⟩ := triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1
    (Or.inl rfl) σ (by simpa using hσ)
  set q := ℓ ^ f with hqdef
  have hq2 : 2 ≤ q := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hcard := ((graphFixedRootTorus TwistTag.D4 K σ).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (graphFixedRootTorus_le _ _ _)).toEquiv, hC,
    hH] at hcard
  have hpos : 0 < (q ^ 3 - 1) * (q - 1) := by
    have h3 : 2 ≤ q ^ 3 := le_trans hq2 (Nat.le_self_pow (by norm_num) q)
    exact Nat.mul_pos (by omega) (by omega)
  refine Nat.eq_of_mul_eq_mul_left hpos (hcard.trans ?_)
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h6]
  ring

theorem not_dvd_index_graphFixedRootTorus_D4 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f - 1) :
    ¬ p ∣ ((graphFixedRootTorus TwistTag.D4 K σ).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ)).index := by
  rw [index_graphFixedRootTorus_D4 hℓ hf hK σ hσ]
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hqp : ((ℓ ^ f : ℕ) : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (ℓ ^ f - 1) p).2 hpq
    rwa [Nat.cast_sub hq1, Nat.cast_one, sub_eq_zero] at h
  intro hdvd
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, hqp, one_pow, Nat.cast_one] at h0
  have h12 : ((12 : ℕ) : ZMod p) = 0 := by
    rw [← h0]
    norm_num
  have hp12 := (ZMod.natCast_eq_zero_iff 12 p).1 h12
  have := Nat.le_of_dvd (by norm_num) hp12
  interval_cases p <;> first | (norm_num at hp; done) | norm_num at hp12

theorem triality_split_prime_toral_Sylow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f - 1) :
    (∀ P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p P →
      ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        P.map (MulAut.conj g).toMonoidHom ≤
          (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
    (∃ e : (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) ≃*
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ a b, (e (a, b) : ModGL TwistTag.D4.tag K) =
        trialityOuterTorus K σ a * trialityMiddleTorus K σ b) ∧
    (∀ S : Sylow 2 (graphFixedRootTorus TwistTag.D4 K σ.toRingHom),
      (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) ∧
    (ℓ = 2 → Odd (Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ ^ 3 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    refine RingEquiv.ext fun c => ?_
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul,
      show ℓ ^ f * (ℓ ^ f * ℓ ^ f) = (ℓ ^ f) ^ 3 by ring, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  obtain ⟨-, ⟨e, he⟩, -, -, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have : IsCyclic (trialityFixedField K σ.toRingHom)ˣ := inferInstance
  refine ⟨fun P hP => exists_conj_map_le_of_not_dvd_index
      (not_dvd_index_graphFixedRootTorus_D4 hℓ hf hK σ.toRingHom hσ hp hp3 hpq) hP,
    ⟨e, he⟩, fun S => comm_and_two_generated_of_injective_prod
      (e.symm.toMonoidHom.comp
        (S : Subgroup (graphFixedRootTorus TwistTag.D4 K σ.toRingHom)).subtype)
      (e.symm.injective.comp Subtype.val_injective), fun hℓ2 => ?_⟩
  obtain ⟨-, hH, -⟩ := triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1
    (Or.inl rfl) σ.toRingHom (by simpa using hσ)
  subst hℓ2
  rw [hH]
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h3 : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have he1 : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have he3 : Even ((2 ^ f) ^ 3) := (Nat.even_pow.2 ⟨he1, by norm_num⟩)
  exact Nat.odd_mul.2 ⟨Nat.Even.sub_odd h3 he3 odd_one, Nat.Even.sub_odd h1 he1 odd_one⟩

end CFSG.RankThree.Chevalley

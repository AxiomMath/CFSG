module

public import CFSG.Quasithin.H13.NQCatLieCartanTools
public import CFSG.Quasithin.H13.NQCatD4Center
public import CFSG.Quasithin.Background.SmithB42D4Main
public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.GraphFixedBorelCoreCenter

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan.D4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  CFSG.Quasithin.B42D4

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

omit [Finite K] in
theorem torus_ab_ox₆
    (hσ3 : σ.toRingHom ^ 3 = 1) (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ)
    (f : trialityFixedField K σ.toRingHom) :
    trialityTorusHom σ (a, b) * ox₆ σ f * (trialityTorusHom σ (a, b))⁻¹ =
      ox₆ σ (((b : (trialityFixedField K σ.toRingHom)ˣ) : trialityFixedField K σ.toRingHom) *
        f) := by
  rw [torusHom_eq, torus_ox₆ (twistFixed_torus σ hσ3 a b)]
  congr 1
  apply Subtype.ext
  have hb := ne_zero_coe_unit σ b
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hσa : σ (a : K) ≠ 0 := (map_ne_zero σ).2 ha
  have hσσa : σ (σ (a : K)) ≠ 0 := (map_ne_zero σ).2 hσa
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  change ((a : K) ^ 2 * (((b : trialityFixedField K σ.toRingHom) : K))⁻¹ *
      (σ (a : K) ^ 2 * (((b : trialityFixedField K σ.toRingHom) : K))⁻¹) *
      (((a : K) * σ (a : K) * σ (σ (a : K)))⁻¹ *
        ((b : trialityFixedField K σ.toRingHom) : K) ^ 2) ^ 2 *
      (σ (σ (a : K)) ^ 2 * (((b : trialityFixedField K σ.toRingHom) : K))⁻¹)) * (f : K) =
    ((b : trialityFixedField K σ.toRingHom) : K) * (f : K)
  field_simp

theorem torusConcl_d4
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    TorusConcl ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) False := by
  have : CharP K 2 := charP_two_of_card hn hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hk := card_fixedField hn hK σ hσ
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3'
  have he' : ∀ p, (e p : ModGL TwistTag.D4.tag K) = trialityTorusHom σ p := fun p => he p.1 p.2
  refine torusConcl_of_le hUC (graphFixedRootTorus_le _ _ _) hUsyl
    graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent ?_ ?_
    (fun a ha b hb => graphFixedRootTorus_mul_comm ha hb) ?_
  · rw [graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent,
      CFSG.LieType.Chevalley.graphFixedRootBorel_eq_sup σ.surjective, sup_comm]
    exact σ.surjective
  · rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_units, Nat.card_units, hK, hk]
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h3 : 2 ∣ (2 ^ n) ^ 3 := dvd_pow h2 (by norm_num)
    have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h5 : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    refine Odd.mul ?_ ?_ <;> rw [Nat.odd_iff] <;> omega
  intro E hEU hE hE16 hEC
  obtain ⟨-, -, -, hsc⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  have hUP : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ P0 σ :=
    graphFixedPosUnipotent_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
  have hQU : Q0 σ ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedPosUnipotent _
  have hb : ∀ x : E, ∃ f : trialityFixedField K σ.toRingHom,
      (x : ModGL TwistTag.D4.tag K) = ox₆ σ f := fun x => by
    have hxC : (x : ModGL TwistTag.D4.tag K) ∈
        Subgroup.centralizer (Q0 σ : Set (ModGL TwistTag.D4.tag K)) :=
      Subgroup.centralizer_le hQU (hEC x.2)
    exact D4Center.eq_ox₆_of_mem_center_a0 σ hσ3 ⟨hsc ⟨hUP (hEU x.2), hxC⟩, hxC⟩
  choose β hβ using hb
  have hβinj : Function.Injective β := fun x y hxy => Subtype.ext (by rw [hβ x, hβ y, hxy])
  have h16 : 16 ≤ 2 ^ n := by
    rw [← hk, ← hE16]
    exact Nat.card_le_card_of_injective β hβinj
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, x₀ ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE16]; norm_num)
    exact exists_ne 1
  have hf₀ : β x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply Subtype.ext
    rw [hβ x₀, h0, Subgroup.coe_one]
    exact ox₆_zero σ hσ3
  let χ : ↥(graphFixedRootTorus TwistTag.D4 K σ.toRingHom) →* (trialityFixedField K σ.toRingHom)ˣ :=
    (MonoidHom.snd _ _).comp e.symm.toMonoidHom
  have hχ : Function.Surjective χ := fun b => ⟨e (1, b), by
    show (e.symm (e (1, b))).2 = b
    rw [MulEquiv.symm_apply_apply]⟩
  refine ⟨lt_relIndex_of_hom χ (fun h hh => ?_) ?_, fun h0 => ?_⟩
  ·
    have hc := Subgroup.mem_centralizer_iff.1 hh (x₀ : ModGL TwistTag.D4.tag K) x₀.2
    have hh' : (h : ModGL TwistTag.D4.tag K) = trialityTorusHom σ (e.symm h) := by
      rw [← he', MulEquiv.apply_symm_apply]
    rw [hβ x₀, hh'] at hc
    have h2 : trialityTorusHom σ ((e.symm h).1, (e.symm h).2) * ox₆ σ (β x₀) *
        (trialityTorusHom σ ((e.symm h).1, (e.symm h).2))⁻¹ = ox₆ σ (β x₀) := by
      rw [← hc]
      group
    rw [torus_ab_ox₆ σ hσ3] at h2
    have h3 := ox₆_inj σ hσ3 h2
    exact Units.ext ((mul_left_eq_self₀.1 h3).resolve_right hf₀)
  · rw [MonoidHom.range_eq_top.2 hχ, Subgroup.card_top, Nat.card_units, hk]
    omega
  ·
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Kˣ, a₀ ≠ 1 := by
      have h8 : 8 ≤ Nat.card K := by
        rw [hK]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3
      have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 (by rw [Nat.card_units]; omega)
      exact exists_ne 1
    have hg : (e (a₀, 1) : ModGL TwistTag.D4.tag K) ∈
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊓
          Subgroup.centralizer (E : Set (ModGL TwistTag.D4.tag K)) := by
      refine ⟨(e (a₀, 1)).2, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
      rw [he', show w = ox₆ σ (β ⟨w, hw⟩) from hβ ⟨w, hw⟩]
      have h1 := torus_ab_ox₆ σ hσ3 a₀ 1 (β ⟨w, hw⟩)
      rw [Units.val_one, one_mul] at h1
      calc ox₆ σ (β ⟨w, hw⟩) * trialityTorusHom σ (a₀, 1) =
          (trialityTorusHom σ (a₀, 1) * ox₆ σ (β ⟨w, hw⟩) * (trialityTorusHom σ (a₀, 1))⁻¹) *
            trialityTorusHom σ (a₀, 1) := by rw [h1]
        _ = trialityTorusHom σ (a₀, 1) * ox₆ σ (β ⟨w, hw⟩) := by group
    rw [h0, Subgroup.mem_bot, he'] at hg
    have h1 := trialityTorusHom_injective_all hσ3' (hg.trans (map_one _).symm)
    exact ha₀ (congrArg Prod.fst h1)

end CFSG.Quasithin.H13.NQCat.LieCartan.D4

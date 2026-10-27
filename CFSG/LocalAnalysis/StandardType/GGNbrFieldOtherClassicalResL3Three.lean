module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3ThreeFix
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestVac
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace L3Three

theorem ggCenterKp_of_mulEquiv {Kp : ℕ → Prop} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGCenterKp Kp R') : GGCenterKp Kp R := by
  intro L' _ _ ψ hψ hker hperf
  have h1 := h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ)
    ((TypeA.ker_comp_mulEquiv e ψ).symm ▸ hker) hperf
  rwa [TypeA.ker_comp_mulEquiv e ψ] at h1

theorem ggCenterKp_projectiveSL {K : Type} [Field K] [Finite K] (h2 : Nat.card K ≠ 2)
    (h4 : Nat.card K ≠ 4) : GGCenterKp (fun k => k ∣ 3) (projectiveSL 3 K) := by
  intro L' _ _ ψ hψ hker hperf
  have hsec : TypeA.SLHasSections 3 K :=
    TypeA.slHasSections_of_card le_rfl h2 (fun h => h4 h.2) (fun h => absurd h.1 (by norm_num))
  obtain ⟨φ, hφs, hφ⟩ := TypeA.exists_sl_cover hsec ψ hψ hker hperf
  have hkerMap : ψ.ker ≤ (Subgroup.center (SpecialLinearGroup (Fin 3) K)).map φ := by
    intro l hl
    obtain ⟨g, rfl⟩ := hφs l
    rw [MonoidHom.mem_ker, hφ g] at hl
    refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
    rw [← scalars_eq_center 3 K]
    exact proj_eq_one_iff.mp hl
  calc Nat.card ψ.ker ∣ Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 3) K)).map φ) :=
        Subgroup.card_dvd_of_le hkerMap
    _ ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) :=
        Subgroup.card_map_dvd (H := Subgroup.center (SpecialLinearGroup (Fin 3) K)) φ
    _ ∣ Nat.gcd 3 (Nat.card K - 1) :=
        CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by norm_num) K
    _ ∣ 3 := Nat.gcd_dvd_left _ _

theorem two_pow_ne_two_four {n : ℕ} (hn : 3 ≤ n) : 2 ^ n ≠ 2 ∧ 2 ^ n ≠ 4 := by
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  constructor <;> omega

theorem three_dvd_two_pow_div_three_sub_one {n : ℕ} (h3n : 3 ∣ n) (h : 3 ∣ 2 ^ n - 1) :
    3 ∣ 2 ^ (n / 3) - 1 := by
  obtain ⟨m, rfl⟩ := h3n
  rw [Nat.mul_div_cancel_left m (by norm_num)]
  have h8 : 2 ^ (3 * m) = 8 ^ m := by rw [pow_mul]; norm_num
  rw [h8] at h
  have h1 : 1 ≡ 8 ^ m [MOD 3] := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr h
  have h2 : 8 ^ m ≡ 2 ^ m [MOD 3] := Nat.ModEq.pow m (by decide)
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp (h1.trans h2)

end L3Three

theorem L3Three.largeEvenLabelAll_rowKX_of_dvd {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∧ lab.rank = 2 ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 3 ∣ lab.n) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift 3 0 R ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusNoLineComp 3 0 R I ∧ GGCenterKp (fun k => k ∣ 3) R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, h3, h3n⟩ := h
  dsimp only at ht hl h3 h3n ⊢
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  have hn3 : 3 ≤ n := by
    obtain ⟨m, rfl⟩ := h3n
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ', hlt⟩ :=
    recipeLinear_card_lt_three (N := 2 ^ n) Nat.prime_three dvd_rfl h3 hQ
  haveI : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  obtain ⟨hK2, hK4⟩ := L3Three.two_pow_ne_two_four hn3
  refine ⟨K, inferInstance, inferInstance, hK, hQ', fun g => ?_, ?_, fun _ _ => ⟨?_, ?_⟩⟩
  · have := RecipeFieldLinear.conj_mem_recI (d := 2 + 1) (K := K) g
    rwa [← SetLike.mem_coe, RecipeFieldLinear.coe_recI] at this
  · exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 3 K)
      (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num)))
  · exact ggTorusNoLineComp_of_ggTorusNoLine (ggTorusNoLine_of_card_lt hlt)
  · exact L3Three.ggCenterKp_of_mulEquiv (TypeA.recipeEquiv 3 K)
      (L3Three.ggCenterKp_projectiveSL (by rw [hK]; exact hK2) (by rw [hK]; exact hK4))

theorem largeEvenLabelAll_rowKX_l3Three {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∧ lab.rank = 2 ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 3 ∣ lab.n ∧ lab.n ≠ 6) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift 3 0 R ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusNoLineComp 3 0 R I ∧ GGCenterKp (fun k => k ∣ 3) R) :=
  L3Three.largeEvenLabelAll_rowKX_of_dvd hlab ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem largeEvenLabelAll_fixKX_l3Three {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∧ lab.rank = 2 ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 3 ∣ lab.n ∧ lab.n ≠ 6) :
    LargeEvenLabelAll lab (GGRawFieldFixKX 3 (fun k => k ∣ 3)) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, h3, h3n, h6⟩ := h
  dsimp only at ht hl h3 h3n h6 ⊢
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  have hq₀ : 3 ∣ 2 ^ (n / 3) - 1 := L3Three.three_dvd_two_pow_div_three_sub_one h3n h3
  obtain ⟨m, rfl⟩ := h3n
  have hm : 3 * m / 3 = m := Nat.mul_div_cancel_left m (by norm_num)
  have h1 : 1 ≤ 3 * m / 3 := by omega
  have h2 : 3 * m / 3 ≠ 1 := by
    rw [hm]
    rintro rfl
    norm_num at h3
  have h4 : 3 * m / 3 ≠ 2 := by
    rw [hm]
    rintro rfl
    exact h6 rfl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ f hf hord =>
    L3Three.ggFixDataKX_linear hn hK hq₀ h1 h2 h4 _ hf hord⟩

end CFSG.StandardType

end

module

public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace WitnessG2

variable {K : Type} [Field K]

theorem ringEquiv_apply_eq_self {σ : K ≃+* K} (hσ : σ ^ 3 = 1) {ω : K} (hω : ω ^ 3 = 1) :
    σ ω = ω := by
  by_cases hω1 : ω = 1
  · rw [hω1, map_one]
  have hq : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hω1
    · exact h
  have hx : σ ω ^ 2 + σ ω + 1 = 0 := by
    rw [← map_pow, ← map_one σ, ← map_add, ← map_add, hq, map_zero]
  have hσ3 : σ (σ (σ ω)) = ω := by
    have h1 := congrArg (fun τ : K ≃+* K => τ ω) hσ
    simpa only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply] using h1
  have h2 : (σ ω - ω) * (σ ω + ω + 1) = 0 := by linear_combination hx - hq
  rcases mul_eq_zero.1 h2 with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have h3 : σ ω = ω ^ 2 := by linear_combination h - hq
    have h4 : σ (σ (σ ω)) = ω ^ 2 := by
      rw [h3, map_pow, h3, map_pow, map_pow, h3]
      linear_combination (ω ^ 5 + ω ^ 2) * hω
    rw [hσ3] at h4
    have h5 : ω * (ω - 1) = 0 := by linear_combination -h4
    rcases mul_eq_zero.1 h5 with h | h
    · rw [h] at hω
      norm_num at hω
    · exact hω1 (sub_eq_zero.1 h)

theorem exists_orderOf_eq_three [Finite K] {k : ℕ} (hK : Nat.card K = 2 ^ (2 * k)) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine exists_prime_orderOf_dvd_card' 3 ?_
  rw [Nat.card_units, hK, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 k

@[expose] def i₀ : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def i₁ : Fin Tag.G2.rank := ⟨1, by decide⟩

section Diag


theorem rootDiagUnit_mem_adjointGroup (a : Fin Tag.G2.rank → Kˣ) :
    rootDiagUnit Tag.G2 a ∈ adjointGroup Tag.G2 K := by
  obtain ⟨⟨B, hB, -⟩, h⟩ := G2_F4_root_character_diagonals_inner Tag.G2 (Or.inl rfl) K
  exact (h B hB a).2.2.1

variable (K) in
@[expose] noncomputable def g2DiagHom : (Fin Tag.G2.rank → Kˣ) →* adjointGroup Tag.G2 K where
  toFun a := ⟨rootDiagUnit Tag.G2 a, rootDiagUnit_mem_adjointGroup a⟩
  map_one' := Subtype.ext rootDiagUnit_one
  map_mul' a b := Subtype.ext (rootDiagUnit_mul a b)

theorem coe_g2DiagHom (a : Fin Tag.G2.rank → Kˣ) :
    ((g2DiagHom K a : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) = rootDiagUnit Tag.G2 a :=
  rfl

theorem coe_g2DiagHom_conj (a : Fin Tag.G2.rank → Kˣ) (u : adjointGroup Tag.G2 K)
    {i : Fin Tag.G2.rank} {c : K} (hu : (u : ModGL Tag.G2 K) = xUnit Tag.G2 K i c) :
    ((g2DiagHom K a * u * (g2DiagHom K a)⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      xUnit Tag.G2 K i ((a i : K) * c) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_g2DiagHom, hu]
  exact (root_diagonal_conjugation Tag.G2 K a).1 i c

theorem g2DiagHom_injective : Function.Injective (g2DiagHom K) := by
  intro a b hab
  funext i
  have h := congrArg (fun g : adjointGroup Tag.G2 K =>
    ((g * ⟨xUnit Tag.G2 K i 1, xUnit_mem_adjointGroup i 1⟩ * g⁻¹ : adjointGroup Tag.G2 K) :
      ModGL Tag.G2 K)) hab
  rw [coe_g2DiagHom_conj a _ rfl, coe_g2DiagHom_conj b _ rfl, mul_one, mul_one] at h
  have h2 := congrArg Units.val h
  rw [coe_xUnit, coe_xUnit] at h2
  exact Units.ext (xOp_injective (τ := Tag.G2) (R := K) i h2)

end Diag

section Field


theorem g2FieldHom_g2DiagHom (σ : K ≃+* K) (a : Fin Tag.G2.rank → Kˣ) :
    g2FieldHom K σ (g2DiagHom K a) =
      g2DiagHom K (fun i => Units.map (σ : K →* K) (a i)) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_g2FieldHom, Units.coe_map, coe_g2DiagHom, coe_g2DiagHom]
  exact entrywise_rootDiag σ.toRingHom a

theorem coe_g2FieldHom_of_coe_eq_xUnit (σ : K ≃+* K) {u : adjointGroup Tag.G2 K}
    {i : Fin Tag.G2.rank} {c : K} (hu : (u : ModGL Tag.G2 K) = xUnit Tag.G2 K i c) :
    (g2FieldHom K σ u : ModGL Tag.G2 K) = xUnit Tag.G2 K i (σ c) := by
  refine Units.ext ?_
  rw [coe_g2FieldHom, Units.coe_map, hu, coe_xUnit, coe_xUnit]
  exact entrywise_xOp σ.toRingHom i c

theorem hasLocalWitness_g2FieldHom [CharP K 2] {σ : K ≃+* K} (hσ : σ ^ 3 = 1) {ω : Kˣ}
    (hω : orderOf ω = 3) : HasLocalWitness (g2FieldHom K σ) := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω, pow_orderOf_eq_one]
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  have hσω : Units.map (σ : K →* K) ω = ω := Units.ext (by
    rw [Units.coe_map]
    exact ringEquiv_apply_eq_self hσ (by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]))
  have hi : i₀ ≠ i₁ := by decide
  set a : Fin Tag.G2.rank → Kˣ := Pi.mulSingle i₀ ω with ha
  set b : Fin Tag.G2.rank → Kˣ := Pi.mulSingle i₁ ω with hb
  have hfix : ∀ (j : Fin Tag.G2.rank) (i : Fin Tag.G2.rank),
      Units.map (σ : K →* K) ((Pi.mulSingle j ω : Fin Tag.G2.rank → Kˣ) i) =
        (Pi.mulSingle j ω : Fin Tag.G2.rank → Kˣ) i := by
    intro j i
    by_cases hij : i = j
    · rw [hij, Pi.mulSingle_eq_same, hσω]
    · rw [Pi.mulSingle_eq_of_ne hij, map_one]
  have hcube : ∀ j : Fin Tag.G2.rank, (Pi.mulSingle j ω : Fin Tag.G2.rank → Kˣ) ^ 3 = 1 := by
    intro j
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases hij : i = j
    · rw [hij, Pi.mulSingle_eq_same, hω3]
    · rw [Pi.mulSingle_eq_of_ne hij, one_pow]
  refine ⟨g2DiagHom K a, g2DiagHom K b, simplePosSubgroup Tag.G2 K i₀, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g2FieldHom_g2DiagHom]
    exact congrArg (g2DiagHom K) (funext (hfix i₀))
  · rw [g2FieldHom_g2DiagHom]
    exact congrArg (g2DiagHom K) (funext (hfix i₁))
  · rw [← map_pow, hcube, map_one]
  · rw [← map_pow, hcube, map_one]
  · rw [← map_mul, ← map_mul, mul_comm]
  · intro h1
    have h2 : a = 1 := g2DiagHom_injective (h1.trans (map_one _).symm)
    have h3 := congrFun h2 i₀
    rw [ha, Pi.mulSingle_eq_same, Pi.one_apply] at h3
    exact hω1 h3
  · rintro ⟨j, hj⟩
    have h2 : b = a ^ j := g2DiagHom_injective (by rw [map_zpow]; exact hj.symm)
    have h3 := congrFun h2 i₁
    rw [hb, Pi.mulSingle_eq_same, Pi.pow_apply, ha, Pi.mulSingle_eq_of_ne hi.symm,
      one_zpow] at h3
    exact hω1 h3
  · intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    obtain ⟨c, hc⟩ := (mem_simplePosSubgroup (i := i₀)).1 g.2
    rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_mul, hc, ← xUnit_add,
      CharTwo.add_self_eq_zero, xUnit_zero]
    rfl
  · intro h1
    have hmem : (⟨xUnit Tag.G2 K i₀ 1, xUnit_mem_adjointGroup i₀ 1⟩ : adjointGroup Tag.G2 K) ∈
        simplePosSubgroup Tag.G2 K i₀ := ⟨1, rfl⟩
    rw [h1, Subgroup.mem_bot] at hmem
    have h2 := congrArg (fun g : adjointGroup Tag.G2 K => ((g : ModGL Tag.G2 K) :
      Module.End K (RootModule Tag.G2 K))) hmem
    simp only [Subgroup.coe_one, Units.val_one] at h2
    rw [coe_xUnit, ← xOp_zero (τ := Tag.G2) (R := K) i₀] at h2
    exact one_ne_zero (xOp_injective (τ := Tag.G2) (R := K) i₀ h2)
  · intro u hu
    obtain ⟨c, hc⟩ := (mem_simplePosSubgroup (i := i₀)).1 hu
    exact ⟨_, coe_g2DiagHom_conj a u hc⟩
  · intro u hu
    obtain ⟨c, hc⟩ := (mem_simplePosSubgroup (i := i₀)).1 hu
    exact ⟨_, coe_g2DiagHom_conj b u hc⟩
  · intro u hu
    obtain ⟨c, hc⟩ := (mem_simplePosSubgroup (i := i₀)).1 hu
    exact ⟨_, coe_g2FieldHom_of_coe_eq_xUnit σ hc⟩

end Field

end WitnessG2

section Main


open WitnessG2 in
theorem inputs47Core_witnessG2 :
    ∀ (X : Type) [Group X] (k : ℕ), Blueprint.ChevalleyExceptionalModel X .G2 2 (2 * k) →
      ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → HasLocalWitness α := by
  intro X _ k hX α hα hout
  obtain ⟨-, hk, -⟩ := hX.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_G2 hX
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hk hK
  rw [← hasLocalWitness_congr_iff e]
  have hβ : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hβout : ¬ IsInnerAut (MulAut.congr e α) := fun h => hout ((isInnerAut_congr e α).mp h)
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨σ, hσ, g, hβeq⟩ := g2_order_three_field_descent hK3 hK4 hβ hβout
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_three hK
  rw [hβeq]
  exact (hasLocalWitness_g2FieldHom hσ3 hω).conj (MulAut.conj g)

end Main

end CFSG.RankThree.PartTwo.Sec4

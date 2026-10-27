module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofCore

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

namespace Res424Six

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem centMod_mul_scalar {n : ℕ} (L : Subgroup (GL (Fin n) K)) (y : GL (Fin n) K)
    {z : GL (Fin n) K} (hz : z ∈ StatedScalars (Fin n) K) : centMod L (y * z) = centMod L y :=
  CFSG.RankThree.PartTwo.Sec21.Item228Census4Proof.centMod_mul_scalar L y hz

@[expose] noncomputable def commScalarHom {n : ℕ} (L : Subgroup (GL (Fin n) K))
    (y : GL (Fin n) K) : centMod L y →* StatedScalars (Fin n) K where
  toFun l := ⟨(l : GL (Fin n) K) * y * (l : GL (Fin n) K)⁻¹ * y⁻¹, by
    obtain ⟨-, w, hw, hwy⟩ := mem_centMod_iff_scalar.mp l.2
    rw [hwy, mul_inv_cancel_right]
    exact hw⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' l₁ l₂ := by
    apply Subtype.ext
    obtain ⟨-, w, hw, hwy⟩ := mem_centMod_iff_scalar.mp l₂.2
    have h2 : (l₂ : GL (Fin n) K) * y * (l₂ : GL (Fin n) K)⁻¹ * y⁻¹ = w := by
      rw [hwy, mul_inv_cancel_right]
    have hc1 := commute_of_mem_statedScalars hw (l₁ : GL (Fin n) K)
    have hc2 := commute_of_mem_statedScalars hw
      ((l₁ : GL (Fin n) K) * y * (l₁ : GL (Fin n) K)⁻¹ * y⁻¹)
    change ((l₁ : GL (Fin n) K) * l₂) * y * ((l₁ : GL (Fin n) K) * l₂)⁻¹ * y⁻¹ =
      ((l₁ : GL (Fin n) K) * y * (l₁ : GL (Fin n) K)⁻¹ * y⁻¹) *
        ((l₂ : GL (Fin n) K) * y * (l₂ : GL (Fin n) K)⁻¹ * y⁻¹)
    rw [h2]
    calc ((l₁ : GL (Fin n) K) * l₂) * y * ((l₁ : GL (Fin n) K) * l₂)⁻¹ * y⁻¹ =
        (l₁ : GL (Fin n) K) * ((l₂ : GL (Fin n) K) * y * (l₂ : GL (Fin n) K)⁻¹) *
          (l₁ : GL (Fin n) K)⁻¹ * y⁻¹ := by group
      _ = ((l₁ : GL (Fin n) K) * w) * y * (l₁ : GL (Fin n) K)⁻¹ * y⁻¹ := by
          rw [hwy, ← mul_assoc]
      _ = w * ((l₁ : GL (Fin n) K) * y * (l₁ : GL (Fin n) K)⁻¹ * y⁻¹) := by
          rw [hc1]
          group
      _ = ((l₁ : GL (Fin n) K) * y * (l₁ : GL (Fin n) K)⁻¹ * y⁻¹) * w := by rw [hc2]

theorem isSolvable_centMod_of_comm {n : ℕ} {L : Subgroup (GL (Fin n) K)} {y : GL (Fin n) K}
    (hC : ∀ a ∈ L ⊓ Subgroup.centralizer {y}, ∀ b ∈ L ⊓ Subgroup.centralizer {y},
      a * b = b * a) :
    Group.IsSolvable (centMod L y) := by
  have hmem : ∀ l : (commScalarHom L y).ker,
      ((l : centMod L y) : GL (Fin n) K) ∈ L ⊓ Subgroup.centralizer {y} := by
    intro l
    have h1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp l.2)
    change ((l : centMod L y) : GL (Fin n) K) * y * ((l : centMod L y) : GL (Fin n) K)⁻¹ * y⁻¹ =
      1 at h1
    refine Subgroup.mem_inf.mpr ⟨((l : centMod L y)).2.1,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc ((l : centMod L y) : GL (Fin n) K) * y =
        ((l : centMod L y) : GL (Fin n) K) * y * ((l : centMod L y) : GL (Fin n) K)⁻¹ * y⁻¹ *
          (y * (l : centMod L y)) := by group
      _ = y * (l : centMod L y) := by rw [h1, one_mul]
  have hker : Group.IsSolvable (commScalarHom L y).ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact hC _ (hmem a) _ (hmem b)
  have hS : Group.IsSolvable (StatedScalars (Fin n) K) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (commute_of_mem_statedScalars b.2 a)
  exact Group.isSolvable_of_ker_le_range (commScalarHom L y).ker.subtype (commScalarHom L y)
    (by rw [Subgroup.range_subtype])

theorem isSolvable_centMod_of_type13 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (hyZ : y ∉ zPi π 3 (p ^ f) K)
    (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K)
    (h13 : Type123 π (p ^ f) K y 1 ∨ Type123 π (p ^ f) K y 3) :
    Group.IsSolvable (centMod (slPi π 3 (p ^ f) K) y) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨y', ⟨z, hz, rfl⟩, h⟩ := rank3II_4_10_one hK hq hτ hτ1 hyH hyZ hy3
  have hzS : z ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  rw [← centMod_mul_scalar _ y hzS]
  refine isSolvable_centMod_of_comm ?_
  rcases h with ⟨-, ⟨φ⟩, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -, -⟩ | ⟨-, -, -, hcyc, -⟩
  · intro a ha b hb
    have h1 : φ (⟨a, ha⟩ * ⟨b, hb⟩) = φ (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (φ.injective h1)
  · exfalso
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, ← he, div_one]
    have h2 : Type123 π (p ^ f) K y 2 := ⟨e, he3, he1, z, hz, g, hg, hD⟩
    rcases h13 with h1 | h3
    · exact not_type123_one_two hK hq h1 h2
    · exact not_type123_three_of_two hK hq h2 h3
  · intro a ha b hb
    have h1 := (IsCyclic.isMulCommutative (α := ↥(slPi π 3 (p ^ f) K ⊓
      Subgroup.centralizer {y * z}))).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h1

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]

theorem isSolvable_inf_centralizer_of_isPGLAtP {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {x : G} {y : GL (Fin 3) K} (hy : IsPGLAtP e x y)
    (hsol : Group.IsSolvable (centMod (slPi π 3 (p ^ f) K) y)) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer {x}) := by
  let F : centMod (slPi π 3 (p ^ f) K) y →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp ((projOf (slPi π 3 (p ^ f) K)).comp
      (Subgroup.inclusion (inf_le_left : centMod (slPi π 3 (p ^ f) K) y ≤ slPi π 3 (p ^ f) K))))
  have hF : ∀ (s : GL (Fin 3) K) (hs : s ∈ centMod (slPi π 3 (p ^ f) K) y),
      F ⟨s, hs⟩ = ((e.symm (projOf _ ⟨s, hs.1⟩) : L) : G) := fun s hs => rfl
  have hle : L ⊓ Subgroup.centralizer {x} ≤ F.range := by
    rintro l ⟨hlL, hlx⟩
    obtain ⟨s, hs, hsl⟩ := Subgroup.mem_map.mp (e ⟨l, hlL⟩).2
    have h1 := hy.2 (e ⟨l, hlL⟩)
    rw [coe_slAct_eqP] at h1
    simp only [MulEquiv.symm_apply_apply] at h1
    have hxl : x * l * x⁻¹ = l := by
      have hlx' : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.mp hlx
      rw [← hlx', mul_inv_cancel_right]
    have h2 : (⟨x * l * x⁻¹, hLn.conj_mem _ hlL x⟩ : L) = ⟨l, hlL⟩ := Subtype.ext hxl
    rw [h2, ← hsl] at h1
    have hsc : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars]
      simp only [map_mul, map_inv]
      rw [← h1, mul_inv_cancel]
    have hsC : s ∈ centMod (slPi π 3 (p ^ f) K) y := by
      refine mem_centMod_iff_scalar.mpr ⟨hs, (y * s * y⁻¹ * s⁻¹)⁻¹, inv_mem hsc, ?_⟩
      have hc := commute_of_mem_statedScalars (inv_mem hsc) (y * s * y⁻¹ * s⁻¹)
      calc s * y * s⁻¹ = (y * s * y⁻¹ * s⁻¹)⁻¹ * y := by group
        _ = _ := rfl
    refine ⟨⟨s, hsC⟩, ?_⟩
    rw [hF]
    have h3 : projOf (slPi π 3 (p ^ f) K) ⟨s, hs⟩ = e ⟨l, hlL⟩ := Subtype.ext (by
      rw [coe_projOf]
      exact hsl)
    rw [h3, MulEquiv.symm_apply_apply]
  have : Group.IsSolvable F.range := Group.isSolvable_of_surjective F.rangeRestrict_surjective
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end Res424Six

end CFSG.RankThree.PartTwo.Sec4

module

public import CFSG.Quasithin.EmptyFaithful.S151ZU
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Quasithin.FLc CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem flip4_r2_comm {w : SLt 4} (h1 : w ∈ Tgrp 4 1) (h3 : w ∈ Tgrp 4 3) :
    reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) * w =
      w * reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) := by
  set r := reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) with hr
  have hst : ∀ a : ℕ, a ≠ 2 → r ∈ stabilizer (flagSpace 4 (ZMod 2) a) := fun a ha =>
    reflection_mem_stabilizer_of_ne (by norm_num) (by norm_num) ha
  have hconj : ∀ a : ℕ, a ≠ 2 → ∀ g : SLt 4, g ∈ Tgrp 4 a → r * g * r⁻¹ ∈ Tgrp 4 a :=
    fun a ha g hg =>
      Tgrp_conj (bcond_of_mem_stabilizer (hst a ha))
        (bcond_of_mem_stabilizer (Subgroup.inv_mem _ (hst a ha))) hg
  by_cases hw : w = 1
  · rw [hw, mul_one, one_mul]
  have h1' : r * w * r⁻¹ ∈ Tgrp 4 1 := hconj 1 (by norm_num) w h1
  have h3' : r * w * r⁻¹ ∈ Tgrp 4 3 := hconj 3 (by norm_num) w h3
  have hne : r * w * r⁻¹ ≠ 1 := by
    intro h
    apply hw
    have := congrArg (fun x => r⁻¹ * x * r) h
    simpa [mul_assoc] using this
  have heq : r * w * r⁻¹ = w := corner_unique (n := 4) (by norm_num) h1' h3' h1 h3 hne hw
  calc r * w = r * w * r⁻¹ * r := by group
    _ = w * r := by rw [heq]

variable {A : Type} [Group A]

theorem flip4_cent_not_le {L B : Subgroup A} (hBL : B ≤ L) (D : BorelIso 4 L B) :
    ∃ x ∈ L, x ∈ Subgroup.centralizer (centerOf B : Set A) ∧ x ∉ B := by
  set r := reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) with hr
  refine ⟨((D.e.symm r : ↥L) : A), (D.e.symm r).2, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzB : z ∈ B := hz.1
    have hzC : z ∈ Subgroup.centralizer (B : Set A) := hz.2
    let z' : ↥L := ⟨z, hBL hzB⟩
    have hUt : ∀ g ∈ Ut 4, D.e z' * g = g * D.e z' := by
      intro g hg
      rw [← D.hB] at hg
      obtain ⟨b', hb', rfl⟩ := hg
      have hcomm : (b' : A) * z = z * (b' : A) := Subgroup.mem_centralizer_iff.mp hzC _ hb'
      have : z' * b' = b' * z' := Subtype.ext hcomm.symm
      show D.e z' * D.e b' = D.e b' * D.e z'
      rw [← map_mul, ← map_mul, this]
    obtain ⟨hw1, hw3⟩ := mem_corner_of_commute_Ut (by norm_num : 2 ≤ 4) hUt
    have hrw := flip4_r2_comm hw1 hw3
    have hx : D.e (D.e.symm r) = r := D.e.apply_symm_apply r
    have hcomm : D.e (z' * D.e.symm r) = D.e (D.e.symm r * z') := by
      rw [map_mul, map_mul, hx]
      exact hrw.symm
    have hcomm' : z' * D.e.symm r = D.e.symm r * z' := D.e.injective hcomm
    exact congrArg Subtype.val hcomm'
  · intro hxB
    have hmem : D.e (D.e.symm r) ∈ (B.subgroupOf L).map D.e.toMonoidHom :=
      ⟨D.e.symm r, hxB, rfl⟩
    rw [D.hB, D.e.apply_symm_apply] at hmem
    exact reflection_notMem_stabilizer (K := ZMod 2) (n := 4) (d := 2) (by norm_num) (by norm_num)
      (upperTriangular_le_stabilizer_flagSpace 2 (unitriangular_le_upperTriangular 4 (ZMod 2) hmem))

end CFSG.Quasithin

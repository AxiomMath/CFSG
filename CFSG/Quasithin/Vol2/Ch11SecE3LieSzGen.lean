module

public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.LieType.Ree.SuzukiPerfect

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.A1b CFSG.LieType.Ree
open scoped Pointwise

section Conj

variable {X : Type*} [Group X]

theorem conjSub_sup (g : X) (A B : Subgroup X) :
    A1b.conjSub g (A ⊔ B) = A1b.conjSub g A ⊔ A1b.conjSub g B :=
  Subgroup.map_sup A B _

theorem conjSub_top (g : X) : A1b.conjSub g (⊤ : Subgroup X) = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

end Conj

section Model

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiB_le_normalizer (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ≤ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
  sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)

theorem suzukiDElt_mul_W (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) :
    suzukiDElt a K l * suzukiWElt a K = suzukiWElt a K * suzukiDElt a K l⁻¹ := by
  have h := suzukiWElt_D_W hK l⁻¹
  rw [inv_inv] at h
  rw [← h, mul_assoc, mul_assoc, suzukiWElt_mul_self, mul_one]

theorem suzukiU_sup_conj_W (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiU a K ⊔ A1b.conjSub (suzukiWElt a K) (suzukiU a K) = ⊤ := by
  set H := suzukiU a K ⊔ A1b.conjSub (suzukiWElt a K) (suzukiU a K) with hHdef
  have hTU : ∀ t ∈ suzukiT a K, A1b.conjSub t (suzukiU a K) = suzukiU a K := fun t ht =>
    A1b.conjSub_eq_iff_mem_normalizer.mpr (suzukiT_le_normalizer hK ht)
  have hT : suzukiT a K ≤ Subgroup.normalizer (H : Set (suzukiGroup a K)) := by
    intro t ht
    rw [← A1b.conjSub_eq_iff_mem_normalizer]
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 ht
    rw [hHdef, conjSub_sup, hTU _ ht, ← A1b.conjSub_mul, suzukiDElt_mul_W hK, A1b.conjSub_mul,
      hTU _ (suzukiDElt_mem_suzukiT a K _)]
  have hW : suzukiWElt a K ∈ Subgroup.normalizer (H : Set (suzukiGroup a K)) := by
    rw [← A1b.conjSub_eq_iff_mem_normalizer, hHdef, conjSub_sup, ← A1b.conjSub_mul,
      suzukiWElt_mul_self, A1b.conjSub_one, sup_comm]
  have hB : suzukiB a K ≤ Subgroup.normalizer (H : Set (suzukiGroup a K)) :=
    sup_le (le_sup_left.trans Subgroup.le_normalizer) hT
  have hN : Subgroup.normalizer (H : Set (suzukiGroup a K)) = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    rcases suzukiGroup_mem_cells hK g with hg | ⟨b, hb, x, hx, rfl⟩
    · exact hB hg
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hB hb) hW)
        (Subgroup.le_normalizer (le_sup_left (a := suzukiU a K) hx))
  exact suzuki_unipotent_normal_generation hK H (Subgroup.normalizer_eq_top_iff.mp hN)
    le_sup_left

theorem suzukiU_sup_conj_eq_top (hK : Nat.card K = 2 ^ (2 * a + 1)) {M : suzukiGroup a K}
    (hM : A1b.conjSub M (suzukiU a K) ≠ suzukiU a K) :
    suzukiU a K ⊔ A1b.conjSub M (suzukiU a K) = ⊤ := by
  rcases suzukiGroup_mem_cells hK M with hb | ⟨b, hb, x, hx, rfl⟩
  · exact absurd (A1b.conjSub_eq_iff_mem_normalizer.mpr (suzukiB_le_normalizer hK hb)) hM
  · have hbU : A1b.conjSub b (suzukiU a K) = suzukiU a K :=
      A1b.conjSub_eq_iff_mem_normalizer.mpr (suzukiB_le_normalizer hK hb)
    have hxU : A1b.conjSub x (suzukiU a K) = suzukiU a K :=
      A1b.conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hx)
    rw [A1b.conjSub_mul (b * suzukiWElt a K) x, hxU, A1b.conjSub_mul b (suzukiWElt a K)]
    set W := suzukiWElt a K with hW
    calc suzukiU a K ⊔ A1b.conjSub b (A1b.conjSub W (suzukiU a K))
        = A1b.conjSub b (suzukiU a K) ⊔ A1b.conjSub b (A1b.conjSub W (suzukiU a K)) := by
          rw [hbU]
      _ = ⊤ := by rw [← conjSub_sup, hW, suzukiU_sup_conj_W hK, conjSub_top]

theorem isElemAbelian_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsElemAbelian 2 (suzukiZ0 a K) := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  have hcomm := (suzuki_unipotent_structure hK).2.2.2.2.1
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hx
  rw [sq, suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK, suzukiSElt_inj]
  refine ⟨by simp, ?_⟩
  linear_combination v * h2

theorem card_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiZ0 a K) = Nat.card K := by
  have hinj : Function.Injective fun v : K => suzukiSElt a K 0 v := fun v w h =>
    (suzukiSElt_inj.mp h).2
  calc Nat.card (suzukiZ0 a K) = Nat.card ((suzukiZ0 a K : Set (suzukiGroup a K))) := rfl
    _ = Nat.card (Set.range fun v : K => suzukiSElt a K 0 v) := by rw [coe_suzukiZ0 hK]
    _ = Nat.card K := Nat.card_range_of_injective hinj

end Model

end CFSG.Quasithin.Vol2.Ch11.SecE3

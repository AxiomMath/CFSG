module

public import CFSG.RankThree.SubgroupLists.LinearThreeFamily

public section

namespace CFSG.Quasithin.RonanE114.Seven.L35

open scoped MatrixGroups
open CFSG.Wreathed CFSG.Wreathed.BrauerWong

@[expose] def u35 : SL(3, ZMod 5) := ⟨!![2, 0, 0; 0, 1, 0; 0, 0, 3], by decide⟩

@[expose] def v35 : SL(3, ZMod 5) := ⟨!![1, 0, 0; 0, 2, 0; 0, 0, 3], by decide⟩

@[expose] def s35 : SL(3, ZMod 5) := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 4], by decide⟩

@[expose] def p23 : SL(3, ZMod 5) := ⟨!![4, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

@[expose] def c3 : SL(3, ZMod 5) := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

@[expose] def x1 : SL(3, ZMod 5) := ⟨!![1, 4, 0; 3, 3, 0; 0, 0, 1], by decide⟩

theorem u35_pow : u35 ^ 2 ^ 2 = 1 := by decide
theorem v35_pow : v35 ^ 2 ^ 2 = 1 := by decide
theorem s35_sq : s35 ^ 2 = 1 := by decide
theorem u35_comm : u35 * v35 = v35 * u35 := by decide
theorem s35_conj : s35⁻¹ * u35 * s35 = v35 := by decide

@[expose] noncomputable def phi35 : Wreath (2 ^ 2) →* SL(3, ZMod 5) :=
  presentationHom u35_pow v35_pow s35_sq u35_comm s35_conj

theorem phi35_injective : Function.Injective phi35 := by
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ 2)).symm.surjective w
  change phi35 (element _ a b e) = 1 at hw
  rw [phi35, presentationHom_element] at hw
  have key : ∀ (a b : ZMod (2 ^ 2)) (e : ZMod 2),
      u35 ^ a.val * v35 ^ b.val * s35 ^ e.val = 1 → a = 0 ∧ b = 0 ∧ e = 0 := by decide
  obtain ⟨rfl, rfl, rfl⟩ := key a b e hw
  exact element_zero _

@[expose] def S35 : Subgroup SL(3, ZMod 5) := Subgroup.closure {u35, v35, s35}

theorem phi35_range : phi35.range = S35 :=
  presentationHom_range u35_pow v35_pow s35_sq u35_comm s35_conj (by norm_num)

theorem card_S35 : Nat.card S35 = 2 ^ (2 * 2 + 1) := by
  rw [← phi35_range, ← Nat.card_congr (MonoidHom.ofInjective phi35_injective).toEquiv, card_wreath]
  norm_num

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem card_SL35 : Nat.card SL(3, ZMod 5) = 372000 := by
  have h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 5) (n := 3)
    (by norm_num)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num), Nat.card_zmod] at h
  exact h.trans (by norm_num)

theorem center_SL35 : Subgroup.center SL(3, ZMod 5) = ⊥ := by
  have h := CFSG.RankThree.SubgroupLists.card_center_sl3 (K := ZMod 5)
  rw [Nat.card_zmod] at h
  have h1 : Nat.card (Subgroup.center SL(3, ZMod 5)) = 1 := h.trans (by norm_num)
  exact Subgroup.card_eq_one.mp h1

theorem isPGroup_S35 : IsPGroup 2 S35 :=
  IsPGroup.of_card (n := 5) (by rw [card_S35])

theorem not_two_dvd_index_S35 : ¬ 2 ∣ S35.index := by
  have h := S35.card_mul_index
  rw [card_S35, card_SL35] at h
  have : S35.index = 11625 := by omega
  rw [this]
  decide

@[expose] noncomputable def sylowS35 : Sylow 2 SL(3, ZMod 5) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isPGroup_S35.toSylow not_two_dvd_index_S35

theorem wg35 : WreathGenerators 2 (sylowS35 : Subgroup SL(3, ZMod 5)) u35 v35 s35 :=
  ⟨rfl, card_S35, u35_pow, v35_pow, s35_sq, u35_comm, s35_conj⟩

@[expose] noncomputable def e35 : ↥(sylowS35 : Subgroup SL(3, ZMod 5)) ≃* Wreath (2 ^ 2) :=
  wg35.equiv (by norm_num)

theorem wreathModelHom_e35 : wreathModelHom sylowS35 e35 = phi35 :=
  wg35.modelHom_eq (by norm_num)

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hf : Function.Injective (fun y : H => (⟨g * y * g⁻¹, h y y.2⟩ : H)) := by
    intro y z hyz
    have h1 : g * (y : G) * g⁻¹ = g * (z : G) * g⁻¹ := congrArg Subtype.val hyz
    apply Subtype.ext
    simpa using h1
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨g * x * g⁻¹, hx⟩
  have h2 : g * (y : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hy
  have h3 : (y : G) = x := by simpa using h2
  rw [← h3]
  exact y.2

end CFSG.Quasithin.RonanE114.Seven.L35

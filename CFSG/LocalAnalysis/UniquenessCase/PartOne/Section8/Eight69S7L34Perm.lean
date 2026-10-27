module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
import CFSG.RankThree.GF2n.Stroth80.Sec93CentFixedPoints

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.RankThree.GF2n.Stroth80

private theorem exists_common_fixed_card {T α : Type} [Group T] [Finite α]
    {E : Subgroup T} [Fintype E] (hEcard : Nat.card E = 16)
    (hEconj : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 → ∃ g : T, g * x * g⁻¹ = y)
    (f : T →* Equiv.Perm α) :
    ∃ k : ℕ, (∀ x : E, x ≠ 1 →
        Nat.card {a : α // (f.comp E.subtype) x a = a} = k) ∧ k ≤ Nat.card α := by
  classical
  have hEcard' : Fintype.card E = 16 := by rw [← Nat.card_eq_fintype_card, hEcard]
  obtain ⟨e₀, he₀⟩ := Fintype.exists_ne_of_one_lt_card (α := E)
    (by rw [hEcard']; norm_num) (1 : E)
  have he₀T : (e₀ : T) ≠ 1 := fun h => he₀ (Subtype.ext h)
  set k : ℕ := Nat.card {a : α // (f.comp E.subtype) e₀ a = a} with hk
  have hfix : ∀ x : E, x ≠ 1 →
      Nat.card {a : α // (f.comp E.subtype) x a = a} = k := by
    intro x hx
    have hxT : (x : T) ≠ 1 := fun h => hx (Subtype.ext h)
    obtain ⟨g, hg⟩ := hEconj (x : T) x.2 hxT (e₀ : T) e₀.2 he₀T
    have hc := card_fixed_points_conj f g (x : T)
    rw [hg] at hc
    rw [hk]
    change Nat.card {a : α // f (x : T) a = a} = Nat.card {a : α // f (e₀ : T) a = a}
    exact hc.symm
  have hk_le : k ≤ Nat.card α := by
    rw [hk]
    exact Finite.card_subtype_le (fun a : α => (f.comp E.subtype) e₀ a = a)
  exact ⟨k, hfix, hk_le⟩

private theorem card_dvd_of_common_fixed_card {T α : Type} [Group T] [Finite α]
    {E : Subgroup T} [Fintype E] (hEcard : Nat.card E = 16) (f : T →* Equiv.Perm α)
    {k : ℕ} (hfix : ∀ x : E, x ≠ 1 →
      Nat.card {a : α // (f.comp E.subtype) x a = a} = k)
    (hk_le : k ≤ Nat.card α) : 16 ∣ Nat.card α - k := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  have hEcard' : Fintype.card E = 16 := by rw [← Nat.card_eq_fintype_card, hEcard]
  have hfix1 : Nat.card {a : α // (f.comp E.subtype) (1 : E) a = a} = Nat.card α := by
    refine Nat.card_congr
      (Equiv.subtypeUnivEquiv (p := fun a : α => (f.comp E.subtype) (1 : E) a = a) ?_)
    intro a
    simp
  have hsum : (∑ x : E, Nat.card {a : α // (f.comp E.subtype) x a = a}) =
      Nat.card α + 15 * k := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : E)), hfix1]
    have h2 : (∑ x ∈ Finset.univ.erase (1 : E),
        Nat.card {a : α // (f.comp E.subtype) x a = a}) = (Fintype.card E - 1) * k := by
      rw [Finset.sum_congr rfl (fun x hx => hfix x (Finset.ne_of_mem_erase hx)),
        Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
    rw [h2, hEcard']
  have hdvd_sum : Nat.card E ∣
      ∑ x : E, Nat.card {a : α // (f.comp E.subtype) x a = a} := by
    simpa only [← Nat.card_eq_fintype_card] using card_dvd_sum_card_fixed (φ := f.comp E.subtype)
  have h16 : 16 ∣ Nat.card α + 15 * k := by
    rw [hEcard] at hdvd_sum
    rwa [hsum] at hdvd_sum
  have hsub : Nat.card α + 15 * k = 16 * k + (Nat.card α - k) := by omega
  have h16' : 16 ∣ 16 * k + (Nat.card α - k) := by
    rwa [hsub] at h16
  exact (Nat.dvd_add_right (show 16 ∣ 16 * k from ⟨k, rfl⟩)).mp h16'

private theorem not_injective_of_fused_sixteen {T α : Type} [Group T] [Finite α]
    {E : Subgroup T} [Fintype E] (hEcard : Nat.card E = 16)
    (hEconj : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 → ∃ g : T, g * x * g⁻¹ = y)
    (hα : Nat.card α < 16) (f : T →* Equiv.Perm α) : ¬ Function.Injective f := by
  obtain ⟨k, hfix, hk_le⟩ := exists_common_fixed_card hEcard hEconj f
  have hdvd : 16 ∣ Nat.card α - k := card_dvd_of_common_fixed_card hEcard f hfix hk_le
  have hk_eq : k = Nat.card α := by
    have hlt : Nat.card α - k < 16 := by omega
    have hzero : Nat.card α - k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  obtain ⟨e₀, he₀⟩ := Fintype.exists_ne_of_one_lt_card (α := E)
    (by rw [← Nat.card_eq_fintype_card, hEcard]; norm_num) (1 : E)
  intro hinj
  have hfa_card : Nat.card {a : α // (f.comp E.subtype) e₀ a = a} = Nat.card α := by
    rw [hfix e₀ he₀, hk_eq]
  have hf1 : (f.comp E.subtype) e₀ = 1 := by
    have hset : {a : α | (f.comp E.subtype) e₀ a = a} = Set.univ := by
      rw [Set.eq_univ_iff_ncard, ← Nat.card_coe_set_eq]
      exact hfa_card
    ext a
    have ha : a ∈ ({a : α | (f.comp E.subtype) e₀ a = a} : Set α) := by
      rw [hset]
      exact Set.mem_univ a
    simpa using ha
  have hf1' : f (e₀ : T) = 1 := by
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply] using hf1
  have heq : (e₀ : T) = 1 := hinj (by rw [hf1', map_one])
  exact he₀ (Subtype.ext heq)

private theorem exists_e16_fused {T : Type} [Group T] (hT : IsL3 T 2) :
    ∃ E : Subgroup T, Nat.card E = 16 ∧
      ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 → ∃ g : T, g * x * g⁻¹ = y := by
  have hmodel : CFSG.Blueprint.LieModel T .PSL 3 2 2 := by
    simpa only [CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3] using hT
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (Q := T) (n := 3) (p := 2) (f := 2) hmodel
  have hK4 : Nat.card K = 4 := by
    rw [hKcard]
    norm_num
  let E : Subgroup T := (projRad K 0).map e.symm.toMonoidHom
  refine ⟨E, ?_, ?_⟩
  · dsimp only [E]
    rw [Subgroup.card_map_of_injective e.symm.injective, card_projRad (k := K) 0, hK4]
  · intro x hx hx1 y hy hy1
    dsimp only [E] at hx hy
    obtain ⟨rx, hrx, hxeq⟩ := Subgroup.mem_map.mp hx
    obtain ⟨ry, hry, hyeq⟩ := Subgroup.mem_map.mp hy
    have hrx1 : rx ≠ 1 := fun h => hx1 (by rw [← hxeq, h, map_one])
    have hry1 : ry ≠ 1 := fun h => hy1 (by rw [← hyeq, h, map_one])
    obtain ⟨g, hg⟩ := projRad_transitive (k := K) 0 hrx hry hrx1 hry1
    refine ⟨e.symm g, ?_⟩
    rw [← hxeq, ← hyeq]
    change e.symm g * e.symm rx * (e.symm g)⁻¹ = e.symm ry
    rw [← map_inv, ← map_mul, ← map_mul, hg]

theorem not_injective_of_isL3_two {T : Type} [Group T] (hT : IsL3 T 2) {α : Type} [Finite α]
    (hα : Nat.card α < 16) (f : T →* Equiv.Perm α) : ¬ Function.Injective f := by
  classical
  obtain ⟨E, hEcard, hEconj⟩ := exists_e16_fused hT
  have hEfin : Finite E := (Nat.card_ne_zero.mp (by rw [hEcard]; norm_num)).2
  let _ : Fintype E := Fintype.ofFinite E
  exact not_injective_of_fused_sixteen hEcard hEconj hα f

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end

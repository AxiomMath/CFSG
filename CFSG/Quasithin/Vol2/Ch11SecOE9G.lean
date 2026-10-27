module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.RankThree.PartOne.KCRootAxis CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Fin257.Sp4 (U_le_normalizer_radA1 U_le_normalizer_radA2
  normalizer_radA1_lt_top normalizer_radA2_lt_top normalizer_U_le_normalizer_radA1
  normalizer_U_le_normalizer_radA2)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
abbrev parN (i : Axis) : Subgroup (antiSp K) :=
  Subgroup.normalizer (CFSG.RankThree.PartOne.KCRootAxis.rootU K i : Set (antiSp K))

variable (K) in
abbrev parC (i : Axis) : Subgroup (antiSp K) :=
  Subgroup.centralizer (CFSG.RankThree.PartOne.KCRootAxis.rootU K i : Set (antiSp K))

omit [Finite K] in
theorem parC_le_parN (i : Axis) : parC K i ≤ parN K i := fun g hg => by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  rw [Subgroup.mem_centralizer_iff] at hg
  constructor
  · intro hu
    rw [← hg u hu, mul_inv_cancel_right]
    exact hu
  · intro hu
    have h1 := hg _ hu
    have h2 : u = g * u * g⁻¹ := by
      calc u = g⁻¹ * ((g * u * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * u * g⁻¹)) := by rw [h1]
        _ = g * u * g⁻¹ := by group
    rw [h2]
    exact hu

omit [Finite K] in
theorem parN_le_normalizer_parC (i : Axis) :
    parN K i ≤ Subgroup.normalizer (parC K i : Set (antiSp K)) := fun g hg => by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ x ∈ parN K i, ∀ c ∈ parC K i, x * c * x⁻¹ ∈ parC K i := by
    intro x hx c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro u hu
    have hu' : x⁻¹ * u * x ∈ CFSG.RankThree.PartOne.KCRootAxis.rootU K i := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) u).mp hu
      simpa using this
    have h1 := hc _ hu'
    calc u * (x * c * x⁻¹) = x * ((x⁻¹ * u * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * u * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * u := by group
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using this

variable {n : ℕ}

theorem commutator_parN_le (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    ⁅parN K i, parN K i⁆ ≤ parC K i := by
  have hS := even_symplectic_four_root_axis_centralizer_structure hK hn i
  have hH : (dHom K i).range ≤ Subgroup.normalizer (parC K i : Set (antiSp K)) := by
    rintro _ ⟨l, rfl⟩
    refine parN_le_normalizer_parC i ?_
    have h := hS.ds_mem_N l 1
    rwa [map_one, mul_one] at h
  have hcomm : ∀ a ∈ (dHom K i).range, ∀ b ∈ (dHom K i).range, a * b = b * a := by
    rintro _ ⟨l, rfl⟩ _ ⟨m, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  refine (Subgroup.commutator_mono ?_ ?_).trans (commutator_le_of_sup_normalizer hH hcomm) <;>
  · intro g hg
    obtain ⟨a, ha, l, M, rfl⟩ := hS.N_decomp g hg
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (hS.A_le_C ha))
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨l, rfl⟩)
        (Subgroup.mem_sup_right (hS.s_mem_C M)))

theorem dInf_parN (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    dInf (parN K i) = parC K i := by
  have hS := even_symplectic_four_root_axis_centralizer_structure hK hn i
  rw [← dInf_eq_of_commutator_le (parC_le_parN i) (commutator_parN_le hK hn i)]
  exact le_antisymm (dInf_le _) (le_dInf_of_perfect hS.C_perfect le_rfl)

theorem not_isSolvable_parC (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    ¬ Group.IsSolvable ↥(parC K i) := by
  have hS := even_symplectic_four_root_axis_centralizer_structure hK hn i
  have := hS.C_perfect
  intro hs
  obtain ⟨k, hk⟩ := hs.solvable
  rw [Group.IsPerfect.derivedSeries_eq_top] at hk
  set M : SL₂ K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ with hMdef
  have hM : M ≠ 1 := fun h => by
    have := congrArg (fun M : SL₂ K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [hMdef] at this
  have hx : (⟨sHom K i M, hS.s_mem_C M⟩ : ↥(parC K i)) = 1 := by
    have : (⟨sHom K i M, hS.s_mem_C M⟩ : ↥(parC K i)) ∈ (⊤ : Subgroup ↥(parC K i)) :=
      Subgroup.mem_top _
    rw [hk] at this
    exact this
  have hs1 : sHom K i M = 1 := congrArg Subtype.val hx
  apply hM
  exact (hS.C_unique 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) M 1
    (by rw [hs1, map_one])).2

theorem exists_leviHom (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    ∃ φ : ↥(parC K i) →* SL₂ K, Function.Surjective φ ∧
      φ.ker = (rootA K i).subgroupOf (parC K i) := by
  have hS := even_symplectic_four_root_axis_centralizer_structure hK hn i
  obtain ⟨hsC, hbij⟩ := hS.quot_bijective
  have hA : ((rootA K i).subgroupOf (parC K i)).Normal :=
    ⟨fun a ha g => Subgroup.mem_subgroupOf.mpr (by
      simpa using hS.A_normal_C g g.2 a (Subgroup.mem_subgroupOf.mp ha))⟩
  set ℓ : SL₂ K →* ↥(parC K i) ⧸ (rootA K i).subgroupOf (parC K i) :=
    (QuotientGroup.mk' _).comp ((sHom K i).codRestrict (parC K i) hsC) with hℓ
  set e := MulEquiv.ofBijective ℓ hbij
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _),
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [Finite K] in
theorem mul_self_of_mem_rootA {i : Axis} {g : antiSp K} (hg : g ∈ rootA K i) : g * g = 1 := by
  cases i
  · exact mul_self_of_mem_radA1 hg
  · exact mul_self_of_mem_radA2 hg

theorem parN_eq (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    parN K i = Subgroup.normalizer (rootA K i : Set (antiSp K)) :=
  (even_symplectic_four_root_axis_centralizer_structure hK hn i).N_eq

theorem le_parN (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    antiUnipotent K ≤ parN K i := by
  rw [parN_eq hK hn i]
  cases i
  · exact U_le_normalizer_radA1
  · exact U_le_normalizer_radA2

theorem parN_ne_top (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) : parN K i ≠ ⊤ := by
  rw [parN_eq hK hn i]
  cases i
  · exact normalizer_radA1_lt_top.ne
  · exact normalizer_radA2_lt_top.ne

theorem not_isSolvable_parN (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    ¬ Group.IsSolvable ↥(parN K i) := fun _ =>
  not_isSolvable_parC hK hn i
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (parC_le_parN i)))

theorem mem_normalizer_sup' {X : Type*} [Group X] {A B : Subgroup X} {g : X}
    (hA : g ∈ Subgroup.normalizer (A : Set X)) (hB : g ∈ Subgroup.normalizer (B : Set X)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [← A1b.conjSub_eq_iff_mem_normalizer] at hA hB ⊢
  rw [A1b.conjSub, Subgroup.map_sup, ← A1b.conjSub, ← A1b.conjSub, hA, hB]

theorem parN_inf_eq (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    parN K .one ⊓ parN K .two = Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
  rw [parN_eq hK hn, parN_eq hK hn]
  refine le_antisymm (fun g hg => ?_) (le_inf normalizer_U_le_normalizer_radA1
    normalizer_U_le_normalizer_radA2)
  rw [antiUnipotent_eq_radA1_sup_radA2]
  exact mem_normalizer_sup' hg.1 hg.2

theorem eq_radA_of_card {B : Subgroup (antiSp K)} (hBU : B ≤ antiUnipotent K)
    (hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = Nat.card K ^ 3) : B = radA1 K ∨ B = radA2 K := by
  refine (abelian_omega_card B hBU hab).2 ?_
  rw [← hcard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨fun h => h.1, fun h => ⟨h, h2 x h⟩⟩)

theorem map_radA_of_map_U (θ : MulAut (antiSp K))
    (hθ : (antiUnipotent K).map θ.toMonoidHom = antiUnipotent K) :
    ((radA1 K).map θ.toMonoidHom = radA1 K ∧ (radA2 K).map θ.toMonoidHom = radA2 K) ∨
      ((radA1 K).map θ.toMonoidHom = radA2 K ∧ (radA2 K).map θ.toMonoidHom = radA1 K) := by
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := K)
  have key : ∀ B : Subgroup (antiSp K), B ≤ antiUnipotent K → (∀ x ∈ B, x * x = 1) →
      Nat.card B = Nat.card K ^ 3 → B.map θ.toMonoidHom = radA1 K ∨
        B.map θ.toMonoidHom = radA2 K := by
    intro B hBU hB2 hBc
    refine eq_radA_of_card (hθ ▸ Subgroup.map_mono hBU) ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hxy : x * y = y * x := by
        have h := hB2 _ (B.mul_mem hx hy)
        calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h
          _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
          _ = y * x := by
            rw [inv_eq_of_mul_eq_one_right (hB2 y hy), inv_eq_of_mul_eq_one_right (hB2 x hx)]
      rw [← map_mul, ← map_mul, hxy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hB2 x hx, map_one]
    · rw [Subgroup.card_map_of_injective θ.injective, hBc]
  have hne : (radA1 K).map θ.toMonoidHom ≠ (radA2 K).map θ.toMonoidHom := fun h =>
    CFSG.QuasithinUnique.Fin257.Sp4.radA1_ne_radA2 (Subgroup.map_injective θ.injective h)
  rcases key _ radA1_le_antiUnipotent (fun _ hx => mul_self_of_mem_radA1 hx) h1 with ha | ha <;>
    rcases key _ radA2_le_antiUnipotent (fun _ hx => mul_self_of_mem_radA2 hx) h2 with hb | hb
  · exact absurd (ha.trans hb.symm) hne
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact absurd (ha.trans hb.symm) hne

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

module

public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.RankThree.Asc83Table.PermWords
public import CFSG.RankThree.Asc83Table.M22Check
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.Asc83Table.M22

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Certificates Subgroup

abbrev gens : List (Equiv.Perm (Fin 22)) := [m22gA, m22gB]

theorem gens_mem : ∀ g ∈ gens, g ∈ NativeSporadic.M22 := by
  intro g hg
  rw [m22_eq]
  simp only [gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem x_eq : x = permWord gens [(0, -1), (1, -2), (0, -1), (1, -1), (0, 1), (1, 2), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -2),
    (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, -2), (0, 1), (1, -1), (0, 1)] := by
  decide +kernel

theorem y_eq : y = permWord gens [(0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, -2), (0, -1), (1, -3), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -2), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, -3), (0, 1), (1, 1), (0, 1), (1, -2), (0, -1), (1, -1),
    (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -2), (0, -1), (1, -1), (0, -1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1)] := by
  decide +kernel

theorem gI_eq : gI = permWord gens [(0, -1), (1, 1), (0, -1), (1, -3), (0, -1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, -1), (0, 1), (1, 2), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1)] := by
  decide +kernel

theorem gJ_eq : gJ = permWord gens [(1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1),
    (0, 1), (1, 2), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 2),
    (1, 1), (0, 1), (1, 1), (0, 1)] := by
  decide +kernel

theorem x_mem : x ∈ NativeSporadic.M22 := x_eq ▸ permWord_mem gens_mem _

theorem y_mem : y ∈ NativeSporadic.M22 := y_eq ▸ permWord_mem gens_mem _

theorem gI_mem : gI ∈ NativeSporadic.M22 := gI_eq ▸ permWord_mem gens_mem _

theorem gJ_mem : gJ ∈ NativeSporadic.M22 := gJ_eq ▸ permWord_mem gens_mem _

abbrev X : NativeSporadic.M22 := ⟨x, x_mem⟩

abbrev Y : NativeSporadic.M22 := ⟨y, y_mem⟩

abbrev GI : NativeSporadic.M22 := ⟨gI, gI_mem⟩

abbrev GJ : NativeSporadic.M22 := ⟨gJ, gJ_mem⟩

theorem X_cube : X ^ 3 = 1 := Subtype.ext (show x ^ 3 = 1 by decide +kernel)

theorem Y_cube : Y ^ 3 = 1 := Subtype.ext (show y ^ 3 = 1 by decide +kernel)

theorem XY_comm : Commute X Y := Subtype.ext (show x * y = y * x by decide +kernel)

theorem X_ne : X ≠ 1 := fun h => absurd (congrArg Subtype.val h) (show x ≠ 1 by decide +kernel)

theorem Y_ne : Y ≠ 1 := fun h => absurd (congrArg Subtype.val h) (show y ≠ 1 by decide +kernel)

theorem Y_ne_X : Y ≠ X := fun h => absurd (congrArg Subtype.val h) (show y ≠ x by decide +kernel)

theorem Y_ne_X2 : Y ≠ X ^ 2 := fun h =>
  absurd (congrArg Subtype.val h) (show y ≠ x ^ 2 by decide +kernel)

@[expose] noncomputable def E : E9Basis NativeSporadic.M22 :=
  E9Basis.ofNe X_cube Y_cube XY_comm X_ne Y_ne Y_ne_X Y_ne_X2

theorem E_a : E.a = X := rfl

theorem E_b : E.b = Y := rfl

theorem GI_X : GI * X * GI⁻¹ = X ^ 0 * Y ^ 1 :=
  Subtype.ext (show gI * x * gI⁻¹ = x ^ 0 * y ^ 1 by decide +kernel)

theorem GI_Y : GI * Y * GI⁻¹ = X ^ 2 * Y ^ 0 :=
  Subtype.ext (show gI * y * gI⁻¹ = x ^ 2 * y ^ 0 by decide +kernel)

theorem GJ_X : GJ * X * GJ⁻¹ = X ^ 1 * Y ^ 1 :=
  Subtype.ext (show gJ * x * gJ⁻¹ = x ^ 1 * y ^ 1 by decide +kernel)

theorem GJ_Y : GJ * Y * GJ⁻¹ = X ^ 1 * Y ^ 2 :=
  Subtype.ext (show gJ * y * gJ⁻¹ = x ^ 1 * y ^ 2 by decide +kernel)

theorem qI_mem : qI ∈ E.rhoE.range := E.mem_range_of_conj 0 2 1 0 GI_X GI_Y (by decide)

theorem qJ_mem : qJ ∈ E.rhoE.range := E.mem_range_of_conj 1 1 1 2 GJ_X GJ_Y (by decide)

def Bad (g : Equiv.Perm (Fin 22)) : Prop :=
  g 0 = 0 ∧ ∃ k, k < 9 ∧ ∃ l, l < 9 ∧ g * x = w k * g ∧ g * y = w l * g ∧
    m22Q8.contains (k, l) = false

theorem not_bad {g : Equiv.Perm (Fin 22)} (hg : g ∈ NativeSporadic.M22) : ¬ Bad g := by
  rintro ⟨h0, k, hk, l, hl, hx, hy, hc⟩
  rw [m22_noBad g hg h0 k hk l hl hx hy] at hc
  exact Bool.noConfusion hc

theorem q8_of_contains : ∀ p q r s : Fin 3,
    m22Q8.contains (3 * p.val + r.val, 3 * q.val + s.val) = true →
      ∃ u : QuaternionGroup 2, ((quatHom u : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        !![((p.val : ℕ) : ZMod 3), (q.val : ℕ); (r.val : ℕ), (s.val : ℕ)] := by
  decide +kernel

theorem fix_xy : ∀ p : Fin 22, x p = p → y p = p → p = 0 := by decide +kernel

theorem fix_zero {g : NativeSporadic.M22}
    (hg : g ∈ normalizer (closure (Set.range E.vec) : Set NativeSporadic.M22)) :
    (g : Equiv.Perm (Fin 22)) 0 = 0 := by
  have hstab : closure (Set.range E.vec) ≤
      MulAction.stabilizer NativeSporadic.M22 (0 : Fin 22) := by
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · show (x : Equiv.Perm (Fin 22)) 0 = 0
      decide +kernel
    · show (y : Equiv.Perm (Fin 22)) 0 = 0
      decide +kernel
  have hginv : g⁻¹ ∈ normalizer (closure (Set.range E.vec) : Set NativeSporadic.M22) :=
    inv_mem hg
  have hfix : ∀ c : NativeSporadic.M22, c ∈ closure (Set.range E.vec) →
      (c : Equiv.Perm (Fin 22)) ((g : Equiv.Perm (Fin 22)) 0) = (g : Equiv.Perm (Fin 22)) 0 := by
    intro c hc
    have hc' := (mem_normalizer_iff.1 hginv c).1 hc
    have h := hstab hc'
    rw [MulAction.mem_stabilizer_iff] at h
    have h' : ((g⁻¹ * c * g⁻¹⁻¹ : NativeSporadic.M22) : Equiv.Perm (Fin 22)) 0 = 0 := h
    simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul,
      Function.comp_apply] at h'
    have := congrArg (g : Equiv.Perm (Fin 22)) h'
    simpa using this
  refine fix_xy _ (hfix X (subset_closure ⟨0, rfl⟩)) (hfix Y (subset_closure ⟨1, rfl⟩))

theorem range_le : E.rhoE.range ≤ quatHom.range := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  obtain ⟨p, q, r, s, hp, hq, hr, hs, e₁, e₂, hM⟩ := E.exists_conj_of_mem_normalizer hg
  have h0 := fix_zero hg
  have hc : m22Q8.contains (3 * p + r, 3 * q + s) = true := by
    by_contra hc
    rw [Bool.not_eq_true] at hc
    apply not_bad g.2
    have hk : (3 * p + r) / 3 = p ∧ (3 * p + r) % 3 = r := by omega
    have hl : (3 * q + s) / 3 = q ∧ (3 * q + s) % 3 = s := by omega
    refine ⟨h0, 3 * p + r, by omega, 3 * q + s, by omega, ?_, ?_, hc⟩
    · rw [w, hk.1, hk.2]
      rw [E_a, E_b] at e₁
      have h := congrArg Subtype.val e₁
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at h
      rw [← h]
      group
    · rw [w, hl.1, hl.2]
      rw [E_a, E_b] at e₂
      have h := congrArg Subtype.val e₂
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at h
      rw [← h]
      group
  obtain ⟨u, hu⟩ := q8_of_contains ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩ ⟨s, hs⟩ hc
  exact ⟨u, Units.ext (hu.trans hM.symm)⟩

theorem automizer_P0 : Nonempty (Automizer E.sub ≃* QuaternionGroup 2) :=
  E.nonempty_quaternion qI_mem qJ_mem range_le

theorem factorization_card : (Nat.card NativeSporadic.M22).factorization 3 = 2 := by
  rw [card_M22]
  exact factorization_eq_of_eq Nat.prime_three (show 443520 = 3 ^ 2 * 49280 by norm_num)
    (by norm_num)

theorem table {L : Type} [Group L] (hL : NativeSporadic.IsSporadic L .M22) :
    (∀ P : Sylow 3 L, IsElementaryAbelian 3 (P : Subgroup L) ∧ Nat.card P = 9) ∧
      CFSG.pRank 3 L = 2 ∧
      ∀ B : Subgroup L, IsElementaryAbelian 3 B → Nat.card B = 9 →
        ActsNontriviallyOnTwoSubgroup B → Nonempty (Automizer B ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := hL
  obtain ⟨h₁, h₂, h₃⟩ := e9_transport E factorization_card (e : L ≃* NativeSporadic.M22)
  obtain ⟨q⟩ := automizer_P0
  exact ⟨h₁, h₂, fun B _ hB _ => (h₃ B hB).map fun f => f.trans q⟩

end CFSG.RankThree.Asc83Table.M22

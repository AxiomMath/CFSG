module

public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open Matrix

abbrev Mat33 : Type := Matrix (Fin 3) (Fin 3) (ZMod 3)

@[expose] def tr01 : Mat33 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]
@[expose] def tr01i : Mat33 := !![1, 2, 0; 0, 1, 0; 0, 0, 1]
@[expose] def tr02 : Mat33 := !![1, 0, 1; 0, 1, 0; 0, 0, 1]
@[expose] def tr02i : Mat33 := !![1, 0, 2; 0, 1, 0; 0, 0, 1]
@[expose] def tr12 : Mat33 := !![1, 0, 0; 0, 1, 1; 0, 0, 1]
@[expose] def tr12i : Mat33 := !![1, 0, 0; 0, 1, 2; 0, 0, 1]
@[expose] def tr21 : Mat33 := !![1, 0, 0; 0, 1, 0; 0, 1, 1]
@[expose] def tr21i : Mat33 := !![1, 0, 0; 0, 1, 0; 0, 2, 1]

@[expose] def Moves (g gi s : Mat33) : Prop := g * s * gi ≠ s ∧ g * s * gi ≠ s * s

instance (g gi s : Mat33) : Decidable (Moves g gi s) := by
  unfold Moves
  infer_instance

theorem exists_moves : ∀ a b c d e f g : ZMod 3,
    (!![a, b, c; 0, d, e; 0, f, g] : Mat33) * !![a, b, c; 0, d, e; 0, f, g] *
        !![a, b, c; 0, d, e; 0, f, g] = 1 →
    (!![a, b, c; 0, d, e; 0, f, g] : Mat33) ≠ 1 →
      Moves tr01 tr01i !![a, b, c; 0, d, e; 0, f, g] ∨
        Moves tr02 tr02i !![a, b, c; 0, d, e; 0, f, g] ∨
        Moves tr12 tr12i !![a, b, c; 0, d, e; 0, f, g] ∨
        Moves tr21 tr21i !![a, b, c; 0, d, e; 0, f, g] := by
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] (b : Module.Basis (Fin 3) (ZMod 3) V)

@[expose] noncomputable def matHom : (V ≃ₗ[ZMod 3] V) →* Mat33 :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem matHom_apply (s : V ≃ₗ[ZMod 3] V) :
    matHom b s = LinearMap.toMatrix b b (s : V →ₗ[ZMod 3] V) :=
  rfl

theorem matHom_injective : Function.Injective (matHom b) := by
  intro s s' h
  apply LinearEquiv.toLinearMap_injective
  exact (LinearMap.toMatrix b b).injective h

@[expose] noncomputable def ofMat {M Mi : Mat33} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    V ≃ₗ[ZMod 3] V :=
  Matrix.toLinOfInv b b h1 h2

theorem matHom_ofMat {M Mi : Mat33} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    matHom b (ofMat b h1 h2) = M :=
  LinearMap.toMatrix_toLin b b M

theorem matHom_ofMat_inv {M Mi : Mat33} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    matHom b (ofMat b h1 h2)⁻¹ = Mi :=
  LinearMap.toMatrix_toLin b b Mi

theorem det_ofMat {M Mi : Mat33} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    LinearMap.det (ofMat b h1 h2 : V →ₗ[ZMod 3] V) = M.det :=
  LinearMap.det_toLin b M

theorem ofMat_apply_zero {M Mi : Mat33} (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (h00 : M 0 0 = 1) (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) : ofMat b h1 h2 (b 0) = b 0 := by
  change Matrix.toLin b b M (b 0) = b 0
  rw [Matrix.toLin_self, Fin.sum_univ_three, h00, h10, h20, one_smul, zero_smul, zero_smul,
    add_zero, add_zero]

theorem tr_facts :
    (tr01 * tr01i = 1 ∧ tr01i * tr01 = 1 ∧ tr01.det = 1 ∧ tr01 0 0 = 1 ∧ tr01 1 0 = 0 ∧
      tr01 2 0 = 0) ∧
    (tr02 * tr02i = 1 ∧ tr02i * tr02 = 1 ∧ tr02.det = 1 ∧ tr02 0 0 = 1 ∧ tr02 1 0 = 0 ∧
      tr02 2 0 = 0) ∧
    (tr12 * tr12i = 1 ∧ tr12i * tr12 = 1 ∧ tr12.det = 1 ∧ tr12 0 0 = 1 ∧ tr12 1 0 = 0 ∧
      tr12 2 0 = 0) ∧
    (tr21 * tr21i = 1 ∧ tr21i * tr21 = 1 ∧ tr21.det = 1 ∧ tr21 0 0 = 1 ∧ tr21 1 0 = 0 ∧
      tr21 2 0 = 0) := by
  decide +kernel

theorem not_moves {G N : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hSL : ∀ g : V ≃ₗ[ZMod 3] V, LinearMap.det (g : V →ₗ[ZMod 3] V) = 1 → g ∈ G)
    (hnorm : ∀ g ∈ G, g (b 0) = b 0 → ∀ s ∈ N, g * s * g⁻¹ ∈ N)
    {s : V ≃ₗ[ZMod 3] V} (hs : s ∈ N) (hs1 : s ≠ 1)
    (hNs : ∀ y ∈ N, y = 1 ∨ y = s ∨ y = s ^ 2) {M Mi : Mat33} (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hdet : M.det = 1) (h00 : M 0 0 = 1) (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) :
    ¬ Moves M Mi (matHom b s) := by
  rintro ⟨hm1, hm2⟩
  set g := ofMat b h1 h2
  have hg : g ∈ G := hSL g (by rw [det_ofMat, hdet])
  have hge : g (b 0) = b 0 := ofMat_apply_zero b h1 h2 h00 h10 h20
  have hconj : matHom b (g * s * g⁻¹) = M * matHom b s * Mi := by
    rw [map_mul, map_mul, matHom_ofMat, matHom_ofMat_inv]
  rcases hNs _ (hnorm g hg hge s hs) with h | h | h
  · apply hs1
    apply matHom_injective b
    have h' : M * matHom b s * Mi = 1 := by rw [← hconj, h, map_one]
    rw [map_one]
    calc matHom b s = Mi * (M * matHom b s * Mi) * M := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2,
            Matrix.mul_one]
      _ = 1 := by rw [h', Matrix.mul_one, h2]
  · exact hm1 (by rw [← hconj, h])
  · exact hm2 (by rw [← hconj, h, map_pow, pow_two])

theorem false_of_normal_card_three {G N : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hSL : ∀ g : V ≃ₗ[ZMod 3] V, LinearMap.det (g : V →ₗ[ZMod 3] V) = 1 → g ∈ G)
    (hN3 : Nat.card N = 3)
    (hNfix : ∀ s ∈ N, ∃ l : ZMod 3, s (b 0) = l • b 0)
    (hnorm : ∀ g ∈ G, g (b 0) = b 0 → ∀ s ∈ N, g * s * g⁻¹ ∈ N) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite N := Nat.finite_of_card_ne_zero (by rw [hN3]; norm_num)
  have : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by rw [hN3]; norm_num)
  obtain ⟨⟨s, hs⟩, hs1⟩ := exists_ne (1 : N)
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hs3 : s ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := N) (x := ⟨s, hs⟩)
    rw [hN3] at h
    exact congrArg Subtype.val h
  have hNs : ∀ y ∈ N, y = 1 ∨ y = s ∨ y = s ^ 2 := by
    have hle : Subgroup.zpowers s ≤ N := Subgroup.zpowers_le.mpr hs
    have hord : orderOf s = 3 := orderOf_eq_prime hs3 hs1'
    have hcard : Nat.card (Subgroup.zpowers s) = 3 := by rw [Nat.card_zpowers, hord]
    have heq : Subgroup.zpowers s = N := Subgroup.eq_of_le_of_card_ge hle (by rw [hN3, hcard])
    intro y hy
    rw [← heq] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hs3' : s ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hs3]
    rw [zpow_eq_zpow_emod k hs3']
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h | h | h <;> rw [h]
    · left; rfl
    · right; left; exact zpow_one s
    · right; right; exact zpow_two s
  set M := matHom b s with hMdef
  have hM3 : M * M * M = 1 := by
    rw [← map_mul, ← map_mul, ← pow_two, ← pow_succ, hs3, map_one]
  have hM1 : M ≠ 1 := fun h => hs1' (matHom_injective b (by rw [← hMdef, h, map_one]))
  obtain ⟨l, hl⟩ := hNfix s hs
  have hcol : ∀ i, M i 0 = b.repr (s (b 0)) i := fun i => LinearMap.toMatrix_apply b b _ i 0
  have hM10 : M 1 0 = 0 := by
    rw [hcol, hl, map_smul, Module.Basis.repr_self]
    simp
  have hM20 : M 2 0 = 0 := by
    rw [hcol, hl, map_smul, Module.Basis.repr_self]
    simp
  have hMeta : M = !![M 0 0, M 0 1, M 0 2; 0, M 1 1, M 1 2; 0, M 2 1, M 2 2] := by
    have h := Matrix.eta_fin_three M
    rw [hM10, hM20] at h
    exact h
  rw [hMeta] at hM3 hM1
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c1, c2, c3, c4, c5, c6⟩,
    ⟨d1, d2, d3, d4, d5, d6⟩⟩ := tr_facts
  rcases exists_moves _ _ _ _ _ _ _ hM3 hM1 with h | h | h | h <;> rw [← hMeta] at h
  · exact not_moves b hSL hnorm hs hs1' hNs a1 a2 a3 a4 a5 a6 h
  · exact not_moves b hSL hnorm hs hs1' hNs b1 b2 b3 b4 b5 b6 h
  · exact not_moves b hSL hnorm hs hs1' hNs c1 c2 c3 c4 c5 c6 h
  · exact not_moves b hSL hnorm hs hs1' hNs d1 d2 d3 d4 d5 d6 h

end CFSG.RankThree.PartTwo.KFacts

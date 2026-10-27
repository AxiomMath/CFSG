module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H30
public import CFSG.Quasithin.Vol2.Ch10SecQ9H28

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

theorem invStd_of_invStd_one {X : Subgroup (Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2))}
    (h1 : InvStd X 1)
    (hU : uniSL (1 + 4) ≤ Subgroup.normalizer
      (X : Set (Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2))))
    (e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ m', 1 ≤ m' ∧ m' < 4 ∧ InvStd X (1 + m') := by
  have hX1 : X ≤ stabStd 1 4 := le_stabStd_of_invStd h1
  obtain ⟨φ, hφd⟩ : ∃ φ : ↥X →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2),
      φ = (botH 1 4).comp (Subgroup.inclusion hX1) := ⟨_, rfl⟩
  have hφx : ∀ x : ↥X, φ x = botH 1 4 ⟨x.1, hX1 x.2⟩ := fun x => by rw [hφd]; rfl
  have hφ : ∀ x, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    rw [hφx] at hx
    exact sq_eq_one_of_blocks (hX1 x.2) (topB_eq_one_of_one ⟨x.1, hX1 x.2⟩)
      (congrArg Subtype.val hx))⟩
  have hconj : ∀ u ∈ uniSL 4, ∀ x : ↥X, ∃ x' : ↥X, φ x' = u * φ x * u⁻¹ ∧
      (x ∈ CFSG.pCore 2 ↥X → x' ∈ CFSG.pCore 2 ↥X) := by
    intro u hu x
    have ht5 : blkSL 1 u ∈ uniSL (1 + 4) := blkSL_mem_uniSL (uniSL 1).one_mem hu
    have hxt : blkSL 1 u * x.1 * (blkSL 1 u)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hU ht5) _).mp x.2
    refine ⟨⟨_, hxt⟩, ?_, fun hx => (mem_pCore_iff _).mpr
      (conj_o2G_mem (hU ht5) ((mem_pCore_iff x).mp hx))⟩
    rw [hφx, hφx, show (⟨blkSL 1 u * x.1 * (blkSL 1 u)⁻¹, hX1 hxt⟩ : ↥(stabStd 1 4)) =
      ⟨blkSL 1 u, blkSL_mem 1 u⟩ * ⟨x.1, hX1 x.2⟩ * (⟨blkSL 1 u, blkSL_mem 1 u⟩)⁻¹ from rfl,
      map_mul, map_mul, map_inv, botH_blkSL]
  obtain ⟨m', hm1, hm4, hinv⟩ := exists_invStd_four e φ hφ hconj
  refine ⟨m', hm1, hm4, fun x hx v hv i hi => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b : Fin 4, i = Fin.natAdd 1 b :=
    ⟨⟨(i : ℕ) - 1, by omega⟩, Fin.ext (by simp; omega)⟩
  rw [bot_smul (hX1 hx)]
  have hvb : (fun j : Fin 4 => v (Fin.natAdd 1 j)) ∈ stdE 4 m' := fun j hj => hv _ (by simp; omega)
  have h := hinv (φ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ _ hvb b (by simp at hi; omega)
  rwa [smul_eq_mulVec', hφx] at h

theorem invStd_of_invStd_four {X : Subgroup (Matrix.SpecialLinearGroup (Fin (4 + 1)) (ZMod 2))}
    (h4 : InvStd X 4)
    (hU : uniSL (4 + 1) ≤ Subgroup.normalizer
      (X : Set (Matrix.SpecialLinearGroup (Fin (4 + 1)) (ZMod 2))))
    (e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ m', 1 ≤ m' ∧ m' < 4 ∧ InvStd X m' := by
  have hX4 : X ≤ stabStd 4 1 := le_stabStd_of_invStd h4
  obtain ⟨φ, hφd⟩ : ∃ φ : ↥X →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2),
      φ = (topH 4 1).comp (Subgroup.inclusion hX4) := ⟨_, rfl⟩
  have hφx : ∀ x : ↥X, φ x = topH 4 1 ⟨x.1, hX4 x.2⟩ := fun x => by rw [hφd]; rfl
  have hφ : ∀ x, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    rw [hφx] at hx
    exact sq_eq_one_of_blocks (hX4 x.2) (congrArg Subtype.val hx)
      (botB_eq_one_of_one ⟨x.1, hX4 x.2⟩))⟩
  have hconj : ∀ u ∈ uniSL 4, ∀ x : ↥X, ∃ x' : ↥X, φ x' = u * φ x * u⁻¹ ∧
      (x ∈ CFSG.pCore 2 ↥X → x' ∈ CFSG.pCore 2 ↥X) := by
    intro u hu x
    have ht5 : blkSL u 1 ∈ uniSL (4 + 1) := blkSL_mem_uniSL hu (uniSL 1).one_mem
    have hxt : blkSL u 1 * x.1 * (blkSL u 1)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hU ht5) _).mp x.2
    refine ⟨⟨_, hxt⟩, ?_, fun hx => (mem_pCore_iff _).mpr
      (conj_o2G_mem (hU ht5) ((mem_pCore_iff x).mp hx))⟩
    rw [hφx, hφx, show (⟨blkSL u 1 * x.1 * (blkSL u 1)⁻¹, hX4 hxt⟩ : ↥(stabStd 4 1)) =
      ⟨blkSL u 1, blkSL_mem u 1⟩ * ⟨x.1, hX4 x.2⟩ * (⟨blkSL u 1, blkSL_mem u 1⟩)⁻¹ from rfl,
      map_mul, map_mul, map_inv, topH_blkSL]
  obtain ⟨m', hm1, hm4, hinv⟩ := exists_invStd_four e φ hφ hconj
  refine ⟨m', hm1, hm4, fun x hx v hv i hi => ?_⟩
  have hv4 : v ∈ stdE (4 + 1) 4 := stdE_mono (by omega) hv
  rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [top_smul_of_mem hv4]
    have hva : (fun j : Fin 4 => v (Fin.castAdd 1 j)) ∈ stdE 4 m' := fun j hj =>
      hv _ (by simpa using hj)
    have h := hinv (φ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ _ hva a (by simpa using hi)
    rwa [smul_eq_mulVec', hφx] at h
  · exact h4 x hx v hv4 _ (by simp)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

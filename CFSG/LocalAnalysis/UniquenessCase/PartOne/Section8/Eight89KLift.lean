module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCoverHom
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KParams
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KNormParams
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KGen
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem k91lift_pi {K : Type} [Group K] (hA : IsAlt (K ⧸ center K) 6) :
    ∃ π : K →* alternatingGroup (Fin 6), Function.Surjective π ∧ π.ker = center K := by
  obtain ⟨eA⟩ := hA
  refine ⟨eA.toMonoidHom.comp (QuotientGroup.mk' (center K)),
    eA.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext g
  simp

private theorem k91lift_rel {K : Type} [Group K] {π : K →* alternatingGroup (Fin 6)} {x y : K}
    (hx : π x = ⟨CFSG.CGT.T75JM.a6x, CFSG.CGT.T75JM.a6x_mem⟩)
    (hy : π y = ⟨CFSG.CGT.T75JM.a6y, CFSG.CGT.T75JM.a6y_mem⟩) :
    x ^ 2 ∈ π.ker ∧ y ^ 4 ∈ π.ker ∧ (x * y) ^ 5 ∈ π.ker ∧ (x * y * y) ^ 5 ∈ π.ker := by
  obtain ⟨h1, h2, h3, h4⟩ := CFSG.CGT.T75JM.a6_rel
  simp only [MonoidHom.mem_ker, map_pow, map_mul, hx, hy]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Subtype.ext <;> simp [h1, h2, h3, h4, sq]

private theorem k91lift_pow9 {G : Type*} [Group G] {g : G} {m c : ℕ} (hg : g ^ m = 1)
    (hm : m * c = 8) : g ^ 9 = g := by
  rw [show 9 = m * c + 1 by omega, pow_succ, pow_mul, hg, one_pow, one_mul]

theorem exists_surjective_coverHom (hn6 : CFSG.CGT.T75JM.A6Nodup) {K : Type} [Group K] [Finite K]
    {n : ℕ} (hn : n = 3 ∨ n = 6) (hZ : Nat.card (center K) = n) (hA : IsAlt (K ⧸ center K) 6) :
    ∃ i j k l : ℕ, (n = 3 → i = 0 ∧ j = 0) ∧ i < 2 ∧ j < 2 ∧ k < 2 ∧ l < 3 ∧
      ∃ φ : CoverPG n i j k l →* K, Function.Surjective φ ∧
        center K = zpowers (φ (PresentedGroup.of (2 : Fin 3))) := by
  obtain ⟨π, hπs, hker⟩ := k91lift_pi hA
  obtain ⟨x, hx⟩ := hπs ⟨CFSG.CGT.T75JM.a6x, CFSG.CGT.T75JM.a6x_mem⟩
  obtain ⟨y, hy⟩ := hπs ⟨CFSG.CGT.T75JM.a6y, CFSG.CGT.T75JM.a6y_mem⟩
  obtain ⟨hx2, hy4, hxy5, hxyy5⟩ := k91lift_rel hx hy
  obtain ⟨z, hz⟩ := exists_zpowers_eq_center hn hZ
  have hzc : z ∈ center K := hz ▸ mem_zpowers z
  have hzn : z ^ n = 1 := by
    have ho : orderOf z = n := by rw [← Nat.card_zpowers, ← hz, hZ]
    rw [← ho, pow_orderOf_eq_one]
  have hcomm : ∀ g : K, Commute g z := fun g => mem_center_iff.mp hzc g
  obtain ⟨i, j, k, l, h3, hi, hj, -, -, e1, e2, e3, e4⟩ :=
    exists_cover_params hn hz hZ (hker ▸ hx2) (hker ▸ hy4) (hker ▸ hxy5) (hker ▸ hxyy5)
  obtain ⟨a, b, z', k', l', hz', hk', hl', f1, f2, f3, f4⟩ :=
    exists_normalized_params hn (x := x ^ 9) (y := y ^ 9) (hcomm _) (hcomm _) hzn e1 e2 e3 e4
  have hzz : zpowers z' = center K := by
    rcases hz' with rfl | rfl
    · exact hz.symm
    · rw [zpowers_inv, hz]
  have hz'c : ∀ g : K, Commute g z' := by
    rcases hz' with rfl | rfl
    · exact hcomm
    · exact fun g => (hcomm g).inv_right
  have hz'n : z' ^ n = 1 := by
    rcases hz' with rfl | rfl
    · exact hzn
    · rw [inv_pow, hzn, inv_one]
  obtain ⟨φ, -, -, hφ2, hφr⟩ := exists_coverHom n i j k' l' (x ^ 9 * z ^ a) (y ^ 9 * z ^ b) z'
    hz'n (hz'c _) (hz'c _) f1 f2 f3 f4
  refine ⟨i, j, k', l', h3, hi, hj, hk', hl', φ, ?_, by rw [hφ2, hzz]⟩
  have hπz : π z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hzc
  have hπx : π (x ^ 9 * z ^ a) = ⟨CFSG.CGT.T75JM.a6x, CFSG.CGT.T75JM.a6x_mem⟩ := by
    rw [map_mul, map_pow, map_pow, hπz, one_pow, mul_one, ← hx]
    exact k91lift_pow9 (m := 2) (c := 4) (by rw [← map_pow]; exact hx2) rfl
  have hπy : π (y ^ 9 * z ^ b) = ⟨CFSG.CGT.T75JM.a6y, CFSG.CGT.T75JM.a6y_mem⟩ := by
    rw [map_mul, map_pow, map_pow, hπz, one_pow, mul_one, ← hy]
    exact k91lift_pow9 (m := 4) (c := 2) (by rw [← map_pow]; exact hy4) rfl
  rw [← MonoidHom.range_eq_top, hφr]
  exact closure_eq_top_of_map π (by rw [hker, hzz]) (by rw [hπx, hπy]; exact closure_a6_eq_top hn6)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

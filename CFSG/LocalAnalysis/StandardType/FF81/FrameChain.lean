module

public import CFSG.LocalAnalysis.StandardType.FF81.FrameModel

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT
open CFSG.StandardType.FrameRoute.FS81 (IsConjLine)
open scoped MatrixGroups

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] def frameK (φ : ↥L ≃* SL(n + 1, ZMod 2)) (K0 K1 : Subgroup G) : ℕ → Subgroup G
  | 0 => K0
  | 1 => K1
  | j + 2 => if h : j < n then pullSL φ (blockSL2 (ZMod 2) n (⟨j, h⟩ : Fin n).rev).range else ⊥

theorem frameK_add_two (φ : ↥L ≃* SL(n + 1, ZMod 2)) (K0 K1 : Subgroup G) (i : Fin n) :
    frameK φ K0 K1 ((i : ℕ) + 2) = pullSL φ (blockSL2 (ZMod 2) n i.rev).range := by
  rw [frameK, dif_pos i.isLt, Fin.eta]

theorem a2System_frameK_L (φ : ↥L ≃* SL(n + 1, ZMod 2)) (K0 K1 : Subgroup G) :
    A2System adjA (fun i : Fin n => frameK φ K0 K1 ((i : ℕ) + 2)) L := by
  have h : (fun i : Fin n => frameK φ K0 K1 ((i : ℕ) + 2)) =
      fun i : Fin n => pullSL φ (blockSL2 (ZMod 2) n i.rev).range := by
    funext i
    exact frameK_add_two φ K0 K1 i
  rw [h]
  exact a2System_pullSL (a2System_blockSL2_rev n) φ

theorem a2System_frameK_conj [NeZero n] (h1 : 1 < n) (φ : ↥L ≃* SL(n + 1, ZMod 2)) {g : G}
    {K0 : Subgroup G}
    (hK0 : (pullSL φ (blockSL2 (ZMod 2) n 0).range).map (MulAut.conj g).toMonoidHom = K0)
    (hfix : ∀ i : Fin n, 2 ≤ (i : ℕ) →
      (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj g).toMonoidHom =
        pullSL φ (blockSL2 (ZMod 2) n i).range) :
    A2System adjA (fun i : Fin n =>
        frameK φ K0 ((pullSL φ (frameSys n ⟨1, h1⟩)).map (MulAut.conj g).toMonoidHom) (i : ℕ))
      (L.map (MulAut.conj g).toMonoidHom) := by
  have hfam : (fun i : Fin n =>
      frameK φ K0 ((pullSL φ (frameSys n ⟨1, h1⟩)).map (MulAut.conj g).toMonoidHom) (i : ℕ)) =
      fun i : Fin n => (pullSL φ (frameSys n i)).map (MulAut.conj g).toMonoidHom := by
    funext i
    by_cases h2 : 2 ≤ (i : ℕ)
    · obtain ⟨j, hj⟩ : ∃ j : Fin n, (j : ℕ) + 2 = (i : ℕ) :=
        ⟨⟨(i : ℕ) - 2, by omega⟩, by simp; omega⟩
      have hjrev : j.rev = ⟨n + 1 - (i : ℕ), by omega⟩ := by
        apply Fin.ext
        rw [Fin.val_rev]
        change n - ((j : ℕ) + 1) = n + 1 - (i : ℕ)
        omega
      have hi' : (2 : ℕ) ≤ ((⟨n + 1 - (i : ℕ), by omega⟩ : Fin n) : ℕ) := by
        show (2 : ℕ) ≤ n + 1 - (i : ℕ)
        omega
      rw [← hj, frameK_add_two φ K0 _, hjrev, frameSys_of_two_le i h2]
      exact (hfix ⟨n + 1 - (i : ℕ), by omega⟩ hi').symm
    · have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
      rcases hi01 with hi | hi
      · have hi0 : i = 0 := Fin.ext hi
        subst hi0
        rw [frameSys_zero n, hK0]
        rfl
      · have hi1 : i = ⟨1, h1⟩ := Fin.ext hi
        subst hi1
        rfl
  rw [hfam]
  simpa only [pullSL_top] using
    A2System.map (a2System_pullSL (a2System_frameSys n) φ)
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

private theorem mem_pullSL_conj [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)} {w : ↥L}
    (hw : φ w = tOne n) {H : Subgroup SL(n + 1, ZMod 2)} {c : SL(n + 1, ZMod 2)}
    (hc : c * tOne n * c⁻¹ ∈ H) :
    (↑(φ.symm c) * (w : G) * (↑(φ.symm c))⁻¹) ∈ pullSL φ H := by
  have h : (↑(φ.symm c * w * (φ.symm c)⁻¹) : G) ∈ pullSL φ H := by
    apply (mem_pullSL_iff φ H (φ.symm c * w * (φ.symm c)⁻¹)).mpr
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hw]
    exact hc
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem exists_conj_mem_frameK [NeZero n] (h1 : 1 < n) {b : G} (hb : orderOf b = 3)
    {φ : ↥L ≃* SL(n + 1, ZMod 2)} {w : ↥L} (hw : φ w = tOne n) {τ : G} (hτ : τ * b * τ⁻¹ = w)
    (t g : G) :
    ∀ i : ℕ, i < n + 2 → ∃ x ∈ frameK φ (Subgroup.zpowers b ⊔ Subgroup.zpowers t)
        ((pullSL φ (frameSys n ⟨1, h1⟩)).map (MulAut.conj g).toMonoidHom) i,
      orderOf x = 3 ∧ IsConjLine b (Subgroup.zpowers x) := by
  intro i hi
  by_cases h2 : 2 ≤ i
  · obtain ⟨j, hj⟩ : ∃ j : Fin n, (j : ℕ) + 2 = i :=
      ⟨⟨i - 2, by omega⟩, by simp; omega⟩
    obtain ⟨c, hc⟩ := exists_conj_tOne_mem_range n j.rev
    let c' : ↥L := φ.symm c
    let y : G := ↑c' * (w : G) * (↑c')⁻¹
    have hy : y ∈ pullSL φ (blockSL2 (ZMod 2) n j.rev).range := mem_pullSL_conj hw hc
    have hyconj : y = (↑c' * τ) * b * (↑c' * τ)⁻¹ := by
      dsimp [y]
      rw [← hτ]
      group
    refine ⟨y, ?_, ?_, ⟨↑c' * τ, by rw [hyconj]⟩⟩
    · rw [← hj, frameK_add_two φ (Subgroup.zpowers b ⊔ Subgroup.zpowers t) _ j]
      exact hy
    · rw [hyconj, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hb]
  · have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · exact ⟨b, Subgroup.mem_sup_left (Subgroup.mem_zpowers b), hb, ⟨1, by simp⟩⟩
    · obtain ⟨c, hc⟩ := exists_conj_tOne_mem_range n ⟨1, h1⟩
      let P : SL(n + 1, ZMod 2) := ggPermSL (F := ZMod 2) (framePerm n)
      let cP : SL(n + 1, ZMod 2) := P * c
      have hcP : cP * tOne n * cP⁻¹ ∈ frameSys n ⟨1, h1⟩ := by
        have h : P * (c * tOne n * c⁻¹) * P⁻¹ ∈ frameSys n ⟨1, h1⟩ := by
          have h' := Subgroup.mem_map_of_mem (MulAut.conj P).toMonoidHom hc
          simpa [frameSys, P, MulAut.conj_apply] using h'
        have heq : P * (c * tOne n * c⁻¹) * P⁻¹ = cP * tOne n * cP⁻¹ := by
          dsimp [cP]
          group
        rwa [heq] at h
      let c' : ↥L := φ.symm cP
      let y : G := ↑c' * (w : G) * (↑c')⁻¹
      have hy : y ∈ pullSL φ (frameSys n ⟨1, h1⟩) := mem_pullSL_conj hw hcP
      let x : G := g * y * g⁻¹
      have hxconj : x = (g * ↑c' * τ) * b * (g * ↑c' * τ)⁻¹ := by
        dsimp [x, y]
        rw [← hτ]
        group
      refine ⟨x, ?_, ?_, ⟨g * ↑c' * τ, by rw [hxconj]⟩⟩
      · refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
        change (MulAut.conj g) y = g * y * g⁻¹
        exact MulAut.conj_apply g y
      · rw [hxconj, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hb]

end CFSG.StandardType.FF81

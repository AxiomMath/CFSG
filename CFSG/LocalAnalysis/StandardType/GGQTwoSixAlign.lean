module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixLem62
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixWin

public section
namespace CFSG.StandardType.QTwo.SixPoint
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {H : Subgroup G}

theorem qTwoSix_align (hK : Nat.card K = 4) (B : QTwoCanonBlocks K 5 6 H) {s : ℕ}
    (hs : s + 5 ≤ 6) {φ φ' : Su K 2 1 4 →* G}
    (h : QTwoFourChart B s (by omega) φ) (h' : QTwoFourChart B (s + 1) (by omega) φ') :
    ∃ ψ : Su K 2 1 4 →* G, QTwoFourChart B (s + 1) (by omega) ψ ∧
      ∀ u : Su K 2 1 3, φ (blockEmb K 2 1 4 3 1 (by norm_num) u) =
        ψ (blockEmb K 2 1 4 3 0 (by norm_num) u) := by
  classical
  let e₁ := blockEmb K 2 1 4 3 1 (by norm_num)
  let e₂ := blockEmb K 2 1 4 3 0 (by norm_num)
  let A₁ := φ.comp e₁
  let A₂ := φ'.comp e₂
  have hA₁ : Function.Injective A₁ := h.1.comp (blockEmb_injective (by norm_num))
  have hA₂ : Function.Injective A₂ := h'.1.comp (blockEmb_injective (by norm_num))
  have hwin : (qTwoSixWinEmb (by norm_num : 1 + 3 ≤ 4)).trans
      (qTwoSixWinEmb (by omega : s + 4 ≤ 6)) =
      (qTwoSixWinEmb (by norm_num : 0 + 3 ≤ 4)).trans
      (qTwoSixWinEmb (by omega : s + 1 + 4 ≤ 6)) := by
    ext i
    change (i.val + 1) + s = (i.val + 0) + (s + 1)
    omega
  have hmaps (J : Finset (Fin 3)) (hJ : 2 ≤ J.card) :
      (coordBlockSU K 2 1 J).map A₁ = (coordBlockSU K 2 1 J).map A₂ := by
    change (coordBlockSU K 2 1 J).map (φ.comp e₁) =
      (coordBlockSU K 2 1 J).map (φ'.comp e₂)
    rw [← Subgroup.map_map, ← Subgroup.map_map]
    change ((coordBlockSU K 2 1 J).map (blockEmb K 2 1 4 3 1 _)).map φ =
      ((coordBlockSU K 2 1 J).map (blockEmb K 2 1 4 3 0 _)).map φ'
    rw [qTwoSix_map_win_coordBlock, qTwoSix_map_win_coordBlock,
      ← h.2 _ (by simpa using hJ), ← h'.2 _ (by simpa using hJ),
      Finset.map_map, Finset.map_map, hwin]
  have htop : coordBlockSU K 2 1 (Finset.univ : Finset (Fin 3)) = ⊤ := by
    ext u
    simp [mem_coordBlockSU_iff]
  have hr : A₁.range = A₂.range := by
    simpa only [htop, Subgroup.map_top] using hmaps Finset.univ (by decide)
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq hA₁ hA₂ hr
  have hαmap (J : Finset (Fin 3)) (hJ : 2 ≤ J.card) :
      (coordBlockSU K 2 1 J).map α.toMonoidHom = coordBlockSU K 2 1 J := by
    apply Subgroup.map_injective hA₂
    rw [Subgroup.map_map]
    have he : A₂.comp α.toMonoidHom = A₁ := by ext u; exact hα u
    rw [he]
    exact hmaps J hJ
  obtain ⟨d, σ, hd⟩ := qTwoSix_lem62 hK α
    (hαmap {0, 1} (by decide)) (hαmap {1, 2} (by decide))
  obtain ⟨β, hβblocks, hβrestrict⟩ := qTwoSix_ext hK d σ
  refine ⟨φ'.comp β.toMonoidHom, ⟨h'.1.comp β.injective, ?_⟩, ?_⟩
  · intro J hJ
    rw [← Subgroup.map_map, hβblocks]
    exact h'.2 J hJ
  · intro u
    have he : β (e₂ u) = e₂ (α u) := by
      apply Subtype.ext
      apply Units.ext
      change (((β (blockEmb K 2 1 4 3 0 _ u) : Su K 2 1 4) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = _
      rw [hβrestrict, coe_coe_blockEmb, hd u]
    change A₁ u = φ' (β (e₂ u))
    rw [he]
    exact (hα u).symm

end CFSG.StandardType.QTwo.SixPoint
end

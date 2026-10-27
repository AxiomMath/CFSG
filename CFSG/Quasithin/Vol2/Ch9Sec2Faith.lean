module

public import CFSG.Quasithin.Vol2.Ch9Sec2Elt

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem le_centerOf (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h1 : zQ T I = fsuV T I) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    quasithinOmegaOneCenter T ≤ centerOf H := by
  have h318 : Hyp318 T (fsuM T L) (fsuL0 T L) (fsuV T I) := h1 ▸ S.hyp318_zQ h37c h38c hH
  rcases theorem318_three hC58 h317 S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke
      S.hyp.fsu.sylow h318 with ⟨hJ, -⟩ | ⟨-, hZ, -⟩
  · exact absurd (le_inf (iSup₂_le fun A hA => hA.1) S.hJ) hJ
  · exact hZ H hH

theorem hall_faithful (h4414 : Stmt4_4_14) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1 : zQ T I = fsuV T I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn : 1 < E1.nParam H) :
    (∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (oTwoUpper H ⊓ fsuM T L) ∧
        oTwoUpper H ⊓ fsuM T L ≤ Subgroup.normalizer (P : Set G)) ∧
      ∀ B : Subgroup G, B ≤ H ⊓ fsuM T L → Odd (Nat.card B) →
        (∃ k : ℕ, B.relIndex (H ⊓ fsuM T L) = 2 ^ k) → ∀ b ∈ B,
          (∀ m ∈ fsuL0 T L, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 (fsuL0 T L)) → b = 1 := by
  obtain ⟨K, _, _, _, e, ψ, hc⟩ := S.exists_isCoord
  have hcomm := commutator_fsuV_fsuL0 S.hyp.fsu S.hN
  rcases h4414 G T (fsuM T L) L (fsuV T I) H S.hyp.fsu.simple S.hyp.fsu.nonabelian
      S.hyp.fsu.qtke S.hyp.fsu.sylow S.uniq.1.1 (le_sup_right.trans S.uniq.1.2) S.hyp.fsu.maximal
      S.hyp.fsu.faithful (le_sup_left.trans S.uniq.1.2) S.hyp.fsu.quasisimple S.hVLT S.hRed hH
      (by rw [hcomm]; exact S.fsuV_ne_bot) (hc.fsuV_eq_conjClosure h1)
      (by rw [hcomm]; exact not_isFFModule_autOn_supA h37 h38 h39 S.hyp S.hV S.hN) hn with
    h | ⟨n', hn1, -, h2⟩ | ⟨-, h3⟩
  · exact h
  · rw [hcomm] at h2
    exact (not_orthA S.hyp hn1 h2).elim
  · rw [hcomm] at h3
    exfalso
    obtain ⟨hc', h3⟩ := h3
    have h64 := Fano.FanoCoreModule.card h3
    rw [Vol2.Ch10.SecA.card_fsuV_of_omegaPlus (h := S.row)] at h64
    have h6 : 2 ^ (4 * n) = 2 ^ 6 := by rw [h64]; norm_num
    have h4n : 4 * n = 6 := Nat.pow_right_injective (le_refl 2) h6
    omega

end Setup

end CFSG.Quasithin.H13.Ch9

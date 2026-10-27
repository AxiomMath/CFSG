module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4f
public import CFSG.Quasithin.Vol2.Ch10SecKRSh

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.commutator_VI_eq (c : Conf T L I t w J) (hV1W : fsuUL T L I ≤ VI T L I J w) :
    ⁅VI T L I J w, J⁆ = VI T L I J w := by
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G)
  set W := VI T L I J w
  have hJN : J ≤ Subgroup.normalizer (W : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  refine le_antisymm (C10KH.commutator_le_left hJN) ?_
  have hN : J ⊔ Tw ≤ Subgroup.normalizer ((⁅W, J⁆ : Subgroup G) : Set G) :=
    C10KH.le_normalizer_commutator (le_normalizer_VI T L I J w)
      (sup_le (Subgroup.le_normalizer) c.Tw_le_normalizer)
  have hV1 : fsuUL T L I ≤ ⁅W, J⁆ := by
    rw [← commutator_fsuUL_eq c.hyp]
    exact Subgroup.commutator_mono hV1W c.le
  refine conjClosure_le fun h hh z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) z).mp (hV1 hz.1)

omit [Finite G] in
theorem commV_autOn_eq_top {W : Subgroup G} [IsMulCommutative ↥W]
    (hJN : J ≤ Subgroup.normalizer (W : Set G)) (hcomm : ⁅W, J⁆ = W) :
    commV (autOn J W) = ⊤ :=
  CFSG.Quasithin.AutOn.commV_autOn_eq_top hJN hcomm

omit [Finite G] in
theorem coords_of_altL5 {W : Subgroup G} [IsMulCommutative ↥W]
    (hJN : J ≤ Subgroup.normalizer (W : Set G)) (hcomm : ⁅W, J⁆ = W)
    (h : AltL5 (autOn J W) (commV (autOn J W))) :
    Nonempty (KGH91.NatCoord J W 5) ∨ Nonempty (AltCoord J W) ∨
      SumNatDual (autOn J W) ⊤ 5 ∨
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ 4 ∧ DirectSumOfCopies (autOn J W) ⊤ ⊥
        (FFModel.nat (Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) k := by
  rw [commV_autOn_eq_top hJN hcomm] at h
  rcases h with h | ⟨π, hπ⟩ | h | ⟨k, hk1, hk4, hds⟩
  · exact Or.inr (Or.inl (exists_altCoord hJN ⟨inferInstance, h⟩))
  · exact Or.inl (KGH91.exists_natCoord hJN ⟨inferInstance, ZMod 2, inferInstance, inferInstance,
      by simp, π, hπ⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases Nat.lt_or_ge k 2 with hk | hk
    · have hk1' : k = 1 := by omega
      subst hk1'
      obtain ⟨I, π, -, -, hsup, hreal⟩ := hds
      have hI : I 0 = ⊤ := by
        rw [← hsup, bot_sup_eq]
        exact le_antisymm (le_iSup I 0) (iSup_le fun i => by rw [Subsingleton.elim i 0])
      have h0 := hreal 0
      rw [hI] at h0
      exact Or.inl (KGH91.exists_natCoord hJN ⟨inferInstance, ZMod 2, inferInstance, inferInstance,
        by simp, π, h0⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨k, hk, hk4, hds⟩))

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS

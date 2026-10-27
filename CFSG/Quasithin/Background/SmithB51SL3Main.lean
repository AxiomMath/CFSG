module

public import CFSG.Quasithin.Background.SmithB51SL3N
public import CFSG.Quasithin.Background.SmithB51SL3M

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

@[expose] def B51Case1iiFixed {V : Type} [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)) :
    Prop :=
  G = L ∧ ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    ∃ (I : Fin 2 → Subgroup V) (π : ↥(StatedSL 3 K) →* ↥L),
      iSupIndep I ∧ (⨆ i, I i) = commV L ∧
      (∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia L (I i) ⊥ π) ∧
      (∀ A : Subgroup (MulAut V), IsFFStarOffenderOn G A (commV L) ↔
        A ≤ L ∧ ∃ W : Submodule K (Fin 3 → K), Module.finrank K W = 2 ∧
          ∀ g : ↥(StatedSL 3 K), g ∈ (A.subgroupOf L).comap π ↔
            (∀ w ∈ W,
              ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w) ∧
              ∀ v, ((g : Matrix.GeneralLinearGroup (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K).mulVec v - v ∈ W) ∧
      qOf G = ((1 : ℚ) : WithTop ℚ)

section Realize

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

theorem NatSec.realizesVia {W : Subgroup V} (c : NatSec L W ⊥ K) (hLW : L ≤ stabSub W) :
    (FFModel.nat (StatedSL 3 K)).RealizesVia L W ⊥ c.π :=
  FFC.realizesVia_nat_of c.hπ.2 bot_le (fun h u hu => ((hLW h.2) u).2 hu)
    (fun h z hz => by rw [Subgroup.mem_bot.1 hz, map_one]; exact Subgroup.one_mem _) c.f c.hfs
    c.hfk c.hfe

end Realize

theorem asB51NonirrSL3Ind_holds (hB42 : AsB42) (hA21 : AsA21SQTKSection)
    (hA36 : AsA36NoOddCover) :
    ∀ (V : Type) [CommGroup V] [Finite V], B51Part1Below (Nat.card V) → (∀ v : V, v ^ 2 = 1) →
      ∀ G L : Subgroup (MulAut V), B51Hyp G L → commV L ∉ IrrPlus L ⊤ →
        (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥L ≃* ↥(StatedSL 3 K))) →
        B51Case1iiFixed G L := by
  intro V _ _ hIH hV G L h hU hT
  obtain ⟨n, K, _, _, hK, ⟨eL⟩⟩ := hT
  obtain ⟨s⟩ := exists_sl3Split hA21 hB42 hA36 hIH hV h hU hK eL
  have hGL := s.eq_L hA21 hB42 hA36 hV h
  refine ⟨hGL, s.n, s.K, inferInstance, inferInstance, s.hK, ![s.I, s.I'], s.e₁.π, ?_, ?_,
    fun i => ?_, s.offender_iff hGL, s.qOf_eq_one hV hGL⟩
  · rw [iSupIndep_pair (show (0 : Fin 2) ≠ 1 by decide) (fun k => by fin_cases k <;> simp),
      disjoint_iff]
    show s.I ⊓ s.I' = ⊥
    rw [inf_comm]
    exact s.inf_eq_bot
  · refine le_antisymm (iSup_le fun i => ?_) ?_
    · fin_cases i
      · exact s.hIU
      · exact s.I'_le
    · rw [← s.sup_eq]
      exact sup_le (le_iSup (![s.I, s.I'] : Fin 2 → Subgroup V) 1)
        (le_iSup (![s.I, s.I'] : Fin 2 → Subgroup V) 0)
  · fin_cases i
    · exact s.e₁.realizesVia s.hLI
    · show (FFModel.nat (StatedSL 3 s.K)).RealizesVia L s.I' ⊥ s.e₁.π
      rw [← s.e₁'_π]
      exact s.e₁'.realizesVia s.hLI'

end B5

end CFSG.Quasithin

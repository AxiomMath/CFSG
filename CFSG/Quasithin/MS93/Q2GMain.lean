module

public import CFSG.Quasithin.MS93.Q2GEnd
public import CFSG.Quasithin.MS93.S5Q2EvenZ

public section

namespace CFSG.Quasithin.MS93.Q2G

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} {l : Submodule F (MSP.V4 F)}

theorem evenData_of (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L 1 F a)
    (hxu : Xq M = Uq M T L ⊔ Zq M L) (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {δ : Vtx (puAmalgam h.le)} (hl : S5.Case56 h 2 a δ l)
    (hJe : S5.vIm h.le a (S5.jOff h.le L 2 (baseA _) (baseB _)) ≤ commutator (MSP.Sp4 F)) :
    EvenData M T L a l := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  have hJT : S5.jOffM M T L 2 ≤ T := EvenData.jOffM_le
  have hJM : S5.jOffM M T L 2 ≤ M := hJT.trans h.le
  have hJ := S5.jOff_baseA h 2
  have hJl : S5.imSp a (S5.jOffM M T L 2) ≤ MSP.qLine l := by
    have := S5B.vIm_le_of_le_vPre h.le hl.2.2.2
    rwa [hJ, S5.vIm_imM h] at this
  have hJc : S5.imSp a (S5.jOffM M T L 2) ≤ commutator (MSP.Sp4 F) := by
    rwa [hJ, S5.vIm_imM h] at hJe
  have h54' := h54 G M T L h hmin hb 1 F _ _ a hd
  simp only [pow_one] at h54'
  have hJ4 : 4 ≤ Nat.card (S5.imSp a (S5.jOffM M T L 2)) := by
    rcases h54' with ⟨-, -, h4⟩ | ⟨-, hJQ, p, hp, hTp⟩
    · rw [hJ, S5.qv_baseA_eq h, S5.relIndex_imM h.le hJM, ← hd.card_imSp h hJT] at h4
      norm_num at h4
      exact h4
    · exfalso
      rw [hJQ, hTp] at hJe
      exact MSP.qPoint_not_le_commutator hK hp hJe
  have hTl : S5.imSp a T ≤ MSP.stab l := by
    rintro _ ⟨m, hm, rfl⟩
    have hmT : (puAmalgam h.le).ofA m ∈ Qv _ (baseB (puAmalgam h.le)) := by
      rw [puAmalgam.qv_baseB]
      exact ⟨m, hm, rfl⟩
    obtain ⟨m', hm', he⟩ := hl.2.2.1 hmT
    rw [(puAmalgam h.le).ofA_injective he] at hm'
    exact hm'
  have hlift := (S5.sp4Lift G M T L h 1 F _ _ a hd).2.2
  obtain ⟨A₀, hA₀⟩ := S5.candMax_nonempty (S5.imSp a T)
  exact
    { sp4 := hd
      xu := hxu
      notCent := hC
      line := hl.2.1
      tStab := hTl
      jEq := MSP.eq_qLine_inf_commutator hK hl.2.1 hJl hJc hJ4
      offNe := ⟨_, hd.liftT_mem_offSetM h hlift hA₀⟩ }

theorem q2EvenZ_of (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h54 : S54) : S5Q2.Q2EvenZ := by
  intro G _ _ M T L h hmin hb F _ _ a hd hxu hC δ l _ hl hJe
  exact (EvenData.false h14 hSQ hT h hb (evenData_of h54 h hmin hb hd hxu hC hl hJe)).elim

end CFSG.Quasithin.MS93.Q2G

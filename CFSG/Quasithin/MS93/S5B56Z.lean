module

public import CFSG.Quasithin.MS93.S5BAux

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S5C56

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem lt_card_vIm_jOff (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hJl : S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) :
    2 ^ k < Nat.card
      (S5.vIm h.le a (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _))) := by
  have hk1 := hd.1
  have hJT : S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ Qv _ (baseB _) :=
    S5B.jOff_le_qv h.le L _ _ _
  rcases h54 G M T L h hmin hb k F _ _ a hd with ⟨-, -, hJq⟩ | ⟨-, hJT', p₀, hp₀, hTq⟩
  · have h1 := S5B.relIndex_le_card_vIm h hd hJT
    have h2 : 2 ^ k < (2 ^ k) ^ 2 := by
      have : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
      nlinarith
    omega
  · exfalso
    have hle : S5.vIm h.le a (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ≤
        MSP.qLine l := S5B.vIm_le_of_le_vPre h.le hJl
    rw [hJT', hTq] at hle
    have h1 := MSP.fixSp_antitone hle
    rw [MSP.fixSp_qLine hl, MSP.fixSp_qPoint hp₀] at h1
    have h2 := Submodule.finrank_mono h1
    rw [hl.1, show Module.finrank F p₀ = 1 from hp₀] at h2
    omega

theorem relIndex_centralizer_le_of_lt_fixSp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hlE : l < MSP.fixSp ((E.subgroupOf M).map a)) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ 2 ^ k := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hrel := S5B.relIndex_centralizer_mul_card h hlift c hEM
  rw [MSP.card_V4, hFq, Module.natCard_eq_pow_finrank (K := F), hFq] at hrel
  have h3 : 3 ≤ Module.finrank F ↥(MSP.fixSp ((E.subgroupOf M).map a)) := by
    have := Submodule.finrank_lt_finrank_of_lt hlE
    rw [hl.1] at this
    omega
  set r := (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) with hr
  set d := Module.finrank F ↥(MSP.fixSp ((E.subgroupOf M).map a)) with hdd
  have hpos : 0 < 2 ^ k := by positivity
  have hqd : (2 ^ k) ^ 3 ≤ (2 ^ k) ^ d := Nat.pow_le_pow_right hpos h3
  have h1 : r * (2 ^ k) ^ 3 ≤ 2 ^ k * (2 ^ k) ^ 3 := by
    calc r * (2 ^ k) ^ 3 ≤ r * (2 ^ k) ^ d := Nat.mul_le_mul_left r hqd
      _ = (2 ^ k) ^ 4 := hrel
      _ = 2 ^ k * (2 ^ k) ^ 3 := by ring
  exact Nat.le_of_mul_le_mul_right h1 (by positivity)

theorem relIndex_centralizer_le_of_not_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ S5.vPre h.le a (MSP.qLine l))
    (hn : ¬ S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E : Set _) ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set _)) :
    (Subgroup.centralizer (E : Set _)).relIndex (S5.uSub h.le L (baseA (puAmalgam h.le))) ≤
      2 ^ k := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  set J₀ : Subgroup G := ((MSP.qLine l).comap a).map M.subtype with hJ₀
  have hJ₀M : J₀ ≤ M := Subgroup.map_subtype_le _
  have hQ₁ : S5.vPre h.le a (MSP.qLine l) = imM h.le J₀ := S5B.vPre_eq_imM h.le _
  have hEst : E ≤ imM h.le M := hE.trans (hQ₁.le.trans (imM_mono h.le hJ₀M))
  obtain ⟨E₁, -, hE₁M, rfl⟩ := S5B.exists_eq_imM h.le hEst
  have hEl : (E₁.subgroupOf M).map a ≤ MSP.qLine l := by
    have := S5B.vIm_le_of_le_vPre h.le hE
    rwa [S5B.vIm_imM] at this
  have hlE : l ≤ MSP.fixSp ((E₁.subgroupOf M).map a) := by
    have := MSP.fixSp_antitone hEl
    rwa [MSP.fixSp_qLine hl] at this
  have hne : l ≠ MSP.fixSp ((E₁.subgroupOf M).map a) := by
    intro heq
    apply hn
    rw [hQ₁, S5B.uSub_baseA h, ← imM_inf_centralizer h.le _ hE₁M]
    have hsub : Uq M T L ⊓ Subgroup.centralizer (E₁ : Set G) ≤
        Uq M T L ⊓ Subgroup.centralizer (J₀ : Set G) := by
      rintro u ⟨hu, huE⟩
      refine ⟨hu, (S5B.mem_centralizer_iff_vec h hlift c hJ₀M ⟨u, hu⟩).2 ?_⟩
      rw [S5B.map_preimage_eq hd.2.2.1, MSP.fixSp_qLine hl, heq]
      exact (S5B.mem_centralizer_iff_vec h hlift c hE₁M ⟨u, hu⟩).1 huE
    refine (imM_mono h.le hsub).trans ?_
    rw [imM_inf_centralizer h.le _ hJ₀M]
    exact inf_le_right
  rw [S5B.uSub_baseA h, S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₁M]
  exact relIndex_centralizer_le_of_lt_fixSp h hd hE₁M hl (lt_of_le_of_ne hlE hne)

theorem commutator_xm_puTrans_le_uSub (h32 : S32) (h : PUHyp M T L) :
    ⁅XM _ (baseA (puAmalgam h.le)), puTrans h.le L (baseA (puAmalgam h.le))⁆ ≤
      S5.uSub h.le L (baseA (puAmalgam h.le)) := by
  rw [S5B.xm_baseA_eq h, S5B.puTrans_L_baseA h, S5B.uSub_baseA h,
    ← imM_commutator h.le (Xq_le M) h.L_le]
  exact imM_mono h.le (h32 G M T L h).2.1

end S5C56

end CFSG.Quasithin.MS93

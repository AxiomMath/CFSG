module

public import CFSG.Quasithin.Vol2.Ch11SecFMult
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch11SecFFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₂ : Subgroup G}

theorem commutator_fsuV_L_eq (hF : Sp4Facts) (h : Hyp11 G T L I n)
    (hset : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n)
    (hV₂ : IsVi T L I n 2 V₂) : ⁅fsuV T I, L⁆ = fsuV T I := by
  have hle : ⁅fsuV T I, L⁆ ≤ fsuV T I ⊓ L :=
    commutator_le_inf_of_le_normalizer ((SecA.fsuV_le_T h).trans h.normal)
      (SecA.L_le_normalizer_fsuV h)
  refine le_antisymm (hle.trans inf_le_left) ?_
  calc fsuV T I = ⁅fsuV T I, LOf L V₂⁆ := (hF.vL2 G T L I n V₂ hset hk hV₂).symm
    _ ≤ ⁅fsuV T I, L⁆ := Subgroup.commutator_mono le_rfl ((perfectCore_le _).trans inf_le_left)

theorem fsuV_le_pCoreOf_L (hF : Sp4Facts) (h : Hyp11 G T L I n)
    (hset : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n)
    (hV₂ : IsVi T L I n 2 V₂) : fsuV T I ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL : fsuV T I ≤ L := by
    rw [← commutator_fsuV_L_eq hF h hset hk hV₂]
    exact (commutator_le_inf_of_le_normalizer ((SecA.fsuV_le_T h).trans h.normal)
      (SecA.L_le_normalizer_fsuV h)).trans inf_le_right
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL
    (SecA.L_le_normalizer_fsuV h) (SecA.isPGroup_fsuV h)

theorem pCoreOf_eq_fsuV_of_isSp4Block (hF : Sp4Facts) (h13 : ASInputs.AS_I_1_3_Sp4)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hset : SecD.NatSetting11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n) (hV₂ : IsVi T L I n 2 V₂) (hblock : IsSp4Block L) :
    pCoreOf 2 L = fsuV T I := by
  obtain ⟨-, -, -, -, hZU, hirr⟩ := hblock.1
  have hmult := pCoreOf_eq_commutator h13 hset hk
  have hU : blockU L = pCoreOf 2 L := hmult.symm
  have hVU : fsuV T I ≤ blockU L := hU ▸ fsuV_le_pCoreOf_L hF h hset hk hV₂
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV h
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    (le_sup_right : L ≤ blockQ L ⊔ L).trans (A3.sup_le_normalizer_commutator (blockQ L) L)
  have hLZ : L ≤ Subgroup.normalizer (blockZ L : Set G) := fun l hl =>
    SecD.mem_normalizer_inf (hLU hl) (SecA.mem_normalizer_centralizer (Subgroup.le_normalizer hl))
  have hsup : fsuV T I ⊔ blockZ L = blockU L := by
    rcases hirr (fsuV T I ⊔ blockZ L) le_sup_right (sup_le hVU inf_le_left)
        (SecD.le_normalizer_sup hLV hLZ) with heq | heq
    · exfalso
      have hVZ : fsuV T I ≤ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
        le_inf le_rfl ((le_sup_left.trans heq.le).trans inf_le_right)
      rw [hset.cV] at hVZ
      exact SecA.fsuV_ne_bot h (le_bot_iff.mp hVZ)
    · exact heq
  have hcomm : ⁅blockU L, L⁆ ≤ fsuV T I := by
    rw [← hsup, Subgroup.commutator_comm]
    have hOV : pCoreOf 2 L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
      rw [← SecA.centralizer_eq_pCoreOf h1102 h]
      exact inf_le_right
    have hZV : blockZ L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
      ((inf_le_left.trans hU.le).trans hOV).trans (Subgroup.centralizer_le_normalizer _)
    refine commutator_sup_right_le Subgroup.le_normalizer hZV ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact (commutator_le_inf_of_le_normalizer ((SecA.fsuV_le_T h).trans h.normal) hLV).trans
        inf_le_left
    · have hb : ⁅L, blockZ L⁆ = ⊥ := by
        rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact inf_le_right
      rw [hb]
      exact bot_le
  have hUV : blockU L ≤ fsuV T I := by
    have h1 : blockU L = ⁅blockU L, L⁆ := by
      conv_lhs => rw [hU, hmult]
      rw [← hU]
    rw [h1]
    exact hcomm
  rw [← hU]
  exact le_antisymm hUV hVU

end CFSG.Quasithin.Vol2.Ch11.SecF

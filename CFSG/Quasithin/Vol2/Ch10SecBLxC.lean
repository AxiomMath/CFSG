module

public import CFSG.Quasithin.Vol2.Ch10SecBLxB
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkZ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C11AmS

variable {G : Type} [Group G] [Finite G]

namespace C11AmS.BLx

theorem false_of_blockQ_eq (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {T L I : Subgroup G} (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6) {H K L₁ : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hLi : IsLi T L L₁)
    (hL₁c : L₁ ∈ cComp (fsuL0 T L ⊔ T)) (hs : IsShort2 L₁)
    (hq : CFSG.IsQuasisimple (↥L₁ ⧸ CFSG.pCore 2 ↥L₁)) (hW : blockQ L₁ = blockQ K)
    (hW2 : IsPGroup 2 (blockQ L₁)) (hW1 : blockQ L₁ ≠ ⊥) : False := by
  have hLc : L ∈ cComp (fsuL0 T L ⊔ T) := SecE.mem_cComp_L0T hyp
  have hLs : IsShort2 L := by
    rcases hLi with h | ⟨t, -, -, h⟩ <;> rw [h] at hs
    · exact hs
    · exact (Lin2.isShort2_map_equiv_iff (MulAut.conj t⁻¹) L).mp hs
  have hL₁W : L₁ ≤ Subgroup.normalizer (blockQ L₁ : Set G) := C1.le_normalizer_blockQ L₁
  have hWL₁ : (blockQ L₁ : Set G) ⊆ L₁ := C1.blockQ_le L₁
  have hL0W : fsuL0 T L ≤ Subgroup.normalizer (blockQ L₁ : Set G) := by
    show conjClosure L T ≤ _
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨s, hsT, l, hl, rfl⟩
    have hmem : s * l * s⁻¹ ∈ L.map (MulAut.conj s).toMonoidHom := ⟨l, hl, rfl⟩
    by_cases heq : L.map (MulAut.conj s).toMonoidHom = L₁
    · rw [heq] at hmem
      exact hL₁W hmem
    · have hLsc : L.map (MulAut.conj s).toMonoidHom ∈ cComp (fsuL0 T L ⊔ T) :=
        H13.LocDbl.map_conj_mem_cComp hLc
          (Subgroup.le_normalizer (le_sup_right (a := fsuL0 T L) hsT))
      have hc := SecF.C10P4F.commutator_eq_bot_of_mem_cComp hL₁c hLsc hs
        ((Lin2.isShort2_map_equiv_iff (MulAut.conj s) L).mpr hLs) hq (Ne.symm heq)
      rw [Subgroup.commutator_comm] at hc
      have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hmem
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hWL₁ hcent)
  have hT1W : T1 T L ≤ Subgroup.normalizer (blockQ L₁ : Set G) := by
    have hT1L₁ : T1 T L ≤ Subgroup.normalizer (L₁ : Set G) := by
      rcases hLi with h | ⟨t, ht, -, h⟩ <;> rw [h]
      · exact inf_le_right
      · exact T1_le_normalizer_conjugate h37 h38 hyp ht
    exact hT1L₁.trans (SecA.normalizer_le_normalizer_pCoreOf L₁)
  have hKW : K ≤ Subgroup.normalizer (blockQ L₁ : Set G) := by
    rw [hW]
    exact C1.le_normalizer_blockQ K
  have hNM := le_fsuM_of_unique (h1026 G T L I hyp).1 (sup_le hL0W hT1W)
    (pCoreOf_normalizer_ne_bot' hW2 hW1)
  apply hH.2.1
  rw [hHK]
  exact sup_le (hKW.trans hNM) (SecA.le_fsuM T L)

end C11AmS.BLx

theorem obl10_2_3BlocksLift_holds
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (h3228 : Ch10.TmpL6_3_2_2_eight) (he23 : E2.E23Statement)
    (h1021 : Ch10.Stmt10_2_1) (h331 : Stmt3_3_1) (hAS : Ch11.SecH.AS_I_1_3_L2)
    (h1026 : Ch10.Stmt10_2_6) : Obl10_2_3BlocksLift := by
  intro G _ _ T L I hyp n h1 H hH hn1 hZH K hKc hHK hKF hZL hZH' hCV hSL hSH hB0K hblk L₁ b hLi
    hSL₁ hSK hbL₁ hbK hbB0 hbS hbo hbD h2 Y hY _ _ _ _ hcard
  subst h2
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hST : baum T ≤ T := C1GN.baum_le T
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hn : 2 ≤ 2 := h1.1
  have hLc : L ∈ cComp (fsuL0 T L ⊔ T) := SecE.mem_cComp_L0T hyp
  have hnL := natData_L h37 h38 h3228 hyp h1 hCV
  obtain ⟨V₁, hnL₁, hL₁c, hL₁L0⟩ : ∃ V : Subgroup G, C11AmS.NatData L₁ V 2 ∧
      L₁ ∈ cComp (fsuL0 T L ⊔ T) ∧ L₁ ≤ fsuL0 T L := by
    rcases hLi with h | ⟨t, ht, -, h⟩ <;> rw [h]
    · exact ⟨_, hnL, hLc, SecA.le_fsuL0 T L⟩
    · refine ⟨_, hnL.map_equiv (MulAut.conj t⁻¹), H13.LocDbl.map_conj_mem_cComp hLc
        (Subgroup.le_normalizer (le_sup_right (a := fsuL0 T L) (T.inv_mem ht))), ?_⟩
      rintro _ ⟨l, hl, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure L T (T.inv_mem ht)) l).mp
        (SecA.le_fsuL0 T L hl)
  have hsubL := subnormal_of_mem_cComp hL₁c
  have hsylL : IsSylowTwoOf (baum T ⊓ L₁) L₁ := by
    have h := B113.isSubnormal_inf_of_le hsubL (sup_le_sup_left hST (fsuL0 T L))
    rw [inf_eq_right.mpr (hL₁L0.trans le_sup_left)] at h
    exact A312.isSylowTwoOf_inf_of_subnormal h hSL
  have mL : Mem T (baum T) (fsuL0 T L ⊔ T) L₁ V₁ b 2 :=
    ⟨hnL₁, perfect_of_mem_cComp hL₁c, A4.charTwo_of_subnormal hsubL (SecA.charTwo_L0T hyp), hL₁c,
      le_sup_right, hT2, hST, hsylL, hSL₁, hbL₁, hbS, hbo, hn, fun z hz hzs => by
        have h1 : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) :=
          ⟨hz, mem_centralizer_fsuL0 hLi hzs⟩
        rwa [hZL, Subgroup.mem_bot] at h1⟩
  obtain ⟨VK, hnK⟩ := exists_natData_K h37 h38 h322 he23 h1021 h331 hyp h1 hH hZH hZH' hKc hHK
    hKF hbK hbS hbo hbD
  have hKR : K ≤ oTwoUpper H := by
    have h1 := oTwoUpper_mono (le_of_mem_cComp hKc)
    rwa [← eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hKc)] at h1
  have hsubK := subnormal_of_mem_cComp hKc
  have hsylK : IsSylowTwoOf (baum T ⊓ K) K := by
    have h := B113.isSubnormal_inf_of_le hsubK (sup_le (oTwoUpper_le H) (hST.trans hTH))
    rw [inf_eq_right.mpr (hKR.trans le_sup_left)] at h
    exact A312.isSylowTwoOf_inf_of_subnormal h hSH
  have hchH : CharTwo H := SecD.charTwo_of_le hyp.fsu.qtke hyp.fsu.sylow hTH hH.1.2
  have mK : Mem T (baum T) H K VK b 2 :=
    ⟨hnK, perfect_of_mem_cComp hKc, A4.charTwo_of_subnormal hsubK hchH, hKc, hTH, hT2, hST,
      hsylK, hSK, hbK, hbS, hbo, hn, fun z hz hzs => by
        have hzK : z ∈ Subgroup.centralizer (K : Set G) := by
          have hK1 : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
            ext x
            simp
          have := hzs 1 T.one_mem
          rwa [hK1] at this
        have hzT := quasithinOmegaOneCenter_le_center T hz
        have hle : H ≤ Subgroup.centralizer ({z} : Set G) := by
          rw [hHK]
          refine sup_le (fun x hx => ?_) (fun x hx => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.mp hzK x hx
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.mp hzT.2 x hx
        have h1 : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (H : Set G) :=
          ⟨hz, Subgroup.mem_centralizer_iff.mpr fun x hx =>
            Subgroup.mem_centralizer_singleton_iff.mp (hle hx)⟩
        rwa [hZH', Subgroup.mem_bot] at h1⟩
  have key : (blockQ L₁ = blockU L₁ ∧ blockQ K = blockU K) ∨
      (Nat.card (blockQ L₁) = 2 * Nat.card (blockU L₁) ∧ blockU L₁ ≤ V₁ ∧
        blockQ L₁ = blockQ K) := by
    rcases hblk with hbl | hbl
    · have hs : IsShort2 L₁ := by
        rcases hLi with h | ⟨t, -, -, h⟩ <;> rw [h]
        · exact hbl.1.1
        · exact (Lin2.isShort2_map_equiv_iff (MulAut.conj t⁻¹) L).mpr hbl.1.1
      rcases BLx.both_or hAS mL mK hs with h | ⟨hc, -, hU, -, hQ⟩
      · exact Or.inl h
      · exact Or.inr ⟨hc, hU, hQ⟩
    · rcases BLx.both_or hAS mK mL hbl.1.1 with ⟨h, h'⟩ | ⟨-, hc, -, hU, hQ⟩
      · exact Or.inl ⟨h', h⟩
      · exact Or.inr ⟨hc, hU, hQ.symm⟩
  rcases key with ⟨hQL, hQK⟩ | ⟨hc, hU, hQ⟩
  · have hQY : blockQ Y = blockU Y := by
      rcases hY with h | h <;> rw [h]
      · exact hQL
      · exact hQK
    rw [hQY] at hcard
    have : 0 < Nat.card (blockU Y) := Nat.card_pos
    omega
  · obtain ⟨hs₁, -, -, -⟩ := block_of_natData mL.hn mL.perf mL.char mL.nat hU
    obtain ⟨-, -, hQ32⟩ := BLx.card_blockQ_of_shape mL hU hc
    have hW1 : blockQ L₁ ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hQ32
      norm_num at hQ32
    exact BLx.false_of_blockQ_eq h37 h38 hyp h1026 hH hHK hLi hL₁c hs₁ mL.quasisimple hQ
      (hT2.to_le mL.blockQ_le_T) hW1

end CFSG.Quasithin.Vol2.Ch10.SecB

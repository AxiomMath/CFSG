module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkG
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkK
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkL
public import CFSG.Quasithin.Vol2.Ch10SecD211B
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBk

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C11AmS

variable {G : Type} [Group G] [Finite G]

namespace C11AmS

omit [Finite G] in
theorem mem_centralizer_fsuL0 {T L L₁ : Subgroup G} (hLi : Ch10.IsLi T L L₁) {z : G}
    (hz : ∀ s ∈ T, z ∈ Subgroup.centralizer
      ((L₁.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G)) :
    z ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
  have hle : fsuL0 T L ≤ Subgroup.centralizer ({z} : Set G) := by
    show conjClosure L T ≤ _
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨h, hh, l, hl, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hLi with rfl | ⟨t, ht, -, rfl⟩
    · exact Subgroup.mem_centralizer_iff.mp (hz h hh) (h * l * h⁻¹) ⟨l, hl, rfl⟩
    · have hmem : h * l * h⁻¹ ∈ (CFSG.conjugate L t).map (MulAut.conj (h * t)).toMonoidHom := by
        refine ⟨t⁻¹ * l * t, ⟨l, hl, ?_⟩, ?_⟩
        · simp
        · simp [MulAut.conj_apply, mul_assoc]
      exact Subgroup.mem_centralizer_iff.mp (hz (h * t) (T.mul_mem hh ht)) _ hmem
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

end C11AmS

theorem obl10_2_3Blocks_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (h3228 : Ch10.TmpL6_3_2_2_eight) (he23 : E2.E23Statement)
    (h1021 : Ch10.Stmt10_2_1) (h331 : Stmt3_3_1) (hAS : Ch11.SecH.AS_I_1_3_L2)
    (hL : Obl10_2_3BlocksLift) : Obl10_2_3Blocks := by
  intro G _ _ T L I hyp n h1 H hH hn1 hZH K hKc hHK hKF hZL hZH' hCV hSL hSH hB0K hblk L₁ b hLi
    hSL₁ hSK hbL₁ hbK hbB0 hbS hbo hbD
  have hres : ∀ Y : Subgroup G, (Y = L₁ ∨ Y = K) → n = 2 → IsShort2 Y → IsLin2Type Y n →
      blockZ Y = ⊥ → blockQ Y ⊓ Subgroup.centralizer (Y : Set G) = ⊥ →
        Nat.card (blockQ Y) ≠ 2 * Nat.card (blockU Y) := fun Y hY h2 =>
    hL G T L I hyp n h1 H hH hn1 hZH K hKc hHK hKF hZL hZH' hCV hSL hSH hB0K hblk L₁ b hLi hSL₁
      hSK hbL₁ hbK hbB0 hbS hbo hbD h2 Y hY
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hST : baum T ≤ T := C1GN.baum_le T
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hn : 2 ≤ n := h1.1
  have hLc : L ∈ cComp (fsuL0 T L ⊔ T) := SecE.mem_cComp_L0T hyp
  have hnL := natData_L h37 h38 h3228 hyp h1 hCV
  obtain ⟨V₁, hnL₁, hL₁c, hL₁L0⟩ : ∃ V : Subgroup G, C11AmS.NatData L₁ V n ∧
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
  have mL : Mem T (baum T) (fsuL0 T L ⊔ T) L₁ V₁ b n :=
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
  have mK : Mem T (baum T) H K VK b n :=
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
  rcases hblk with hbl | hbl
  · have hs : IsShort2 L₁ := by
      rcases hLi with h | ⟨t, -, -, h⟩ <;> rw [h]
      · exact hbl.1.1
      · exact (Lin2.isShort2_map_equiv_iff (MulAut.conj t⁻¹) L).mpr hbl.1.1
    exact blocks_of_mems hAS mL mK hs (hres L₁ (Or.inl rfl)) (hres K (Or.inr rfl))
  · obtain ⟨h1, h2, h3, h4⟩ :=
      blocks_of_mems hAS mK mL hbl.1.1 (hres K (Or.inr rfl)) (hres L₁ (Or.inl rfl))
    exact ⟨h2, h1, h4, h3⟩

end CFSG.Quasithin.Vol2.Ch10.SecB

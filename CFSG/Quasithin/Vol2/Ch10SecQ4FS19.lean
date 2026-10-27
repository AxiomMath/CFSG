module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS18
public import CFSG.Quasithin.Vol2.Ch10SecFObl
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS15
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS3
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS9

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem obl10_2_2FourS5_of
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hshape : Stmt7_0_1_shape) (h3228 : Ch10.TmpL6_3_2_2_eight) (h1012 : Ch10.Stmt10_1_2)
    (h1013 : Ch10.Stmt10_1_3) (h1021 : Ch10.Stmt10_2_1) (he23 : E2.E23Statement)
    (he234 : E2.E23FourStatement) (h113 : ASInputs.AS_C_1_13) : Obl10_2_2FourS5 := by
  intro G _ _ T L I hyp h12 H hH hZH hsyl hbot
  obtain ⟨K, hKc, hKs, hKa, hHK⟩ := C10P4F.exists_A5Block_H he23 he234 h1021 h331 hyp hH hZH
    (SecB.not_case3_of_case12 h12) hsyl hbot
  obtain ⟨q, hqK, hq3, hqM, hqN⟩ := C10P4F.exists_three_elt_block h331 hyp hH hKc hKs hKa
  have hqH : q ∈ H := le_of_mem_cComp hKc hqK
  obtain ⟨hqL0, hqT0, -⟩ := C10P4F.mem_B0_of_three h1012 h1013 h331 hyp h12 hH hqH hqM hq3
  have h2 := C10P4F.case2_of_centralizer h1012 h1013 h331 hyp h12 hH hqH hqM hq3
    (C10P4F.mem_centralizer_of_block h331 hyp hH hKc hKs hKa hqK hq3 hqN)
  refine ⟨h2, ?_⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hKM : ¬ K ≤ fsuM T L := fun h => hH.2.1 (by rw [hHK]; exact sup_le h (SecA.le_fsuM T L))
  have htM := SecA.le_fsuM T L ht
  obtain ⟨K₁, q₁, hK₁c, hK₁s, hK₁a, hq₁K, hq₁L, hq₁3, hq₁T0, hK₁M⟩ : ∃ (K₁ : Subgroup G) (q₁ : G),
      K₁ ∈ cComp H ∧ IsShort2 K₁ ∧ IsAltType K₁ 5 ∧ q₁ ∈ K₁ ∧ q₁ ∈ L ∧ orderOf q₁ = 3 ∧
        q₁ ∈ Subgroup.normalizer (Ch10.T0 T L : Set G) ∧ ¬ K₁ ≤ fsuM T L := by
    rcases C10P4F.mem_L_or_of_block h37 h38 hyp h2 hH hKc hKs hKa hqK hq3 hqL0 hqT0 ht htn with
      hqL | hqL
    · exact ⟨K, q, hKc, hKs, hKa, hqK, hqL, hq3, hqT0, hKM⟩
    · have htT0 : t ∈ Subgroup.normalizer (Ch10.T0 T L : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, htM⟩
      refine ⟨K.map (MulAut.conj t).toMonoidHom, t * q * t⁻¹,
        LocDbl.map_conj_mem_cComp hKc (Subgroup.le_normalizer (hH.1.1 ht)),
        Lin2.IsShort2.map_equiv hKs _, L238.IsAltType.map_equiv hKa _,
        ⟨q, hqK, by simp [MulAut.conj_apply]⟩, hqL, ?_,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htT0 hqT0) (Subgroup.inv_mem _ htT0), ?_⟩
      · have h := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective q
        rw [← hq3, ← h]
        simp [MulAut.conj_apply]
      · intro h
        apply hKM
        intro k hk
        have h1 : t * k * t⁻¹ ∈ fsuM T L := by
          simpa [MulAut.conj_apply] using h (Subgroup.mem_map_of_mem _ hk)
        have e : k = t⁻¹ * (t * k * t⁻¹) * t := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htM) h1) htM
  have hqTL : q₁ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    have e : T ⊓ L = Ch10.T0 T L ⊓ L := by
      rw [Ch10.T0, inf_assoc, inf_eq_right.mpr (SecA.le_fsuL0 T L)]
    rw [e]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hq₁T0, Subgroup.le_normalizer hq₁L⟩
  have hc16 := C10P4F.relIndex_centralizer_T0_le hH.1.1 hK₁c hK₁s hK₁a hq₁K hq₁3 inf_le_left
    (hyp.fsu.sylow.1.to_le inf_le_left) hqTL
  have hb := C10P4F.isA5Block_of_relIndex h37 h38 h3228 hyp h2 hq₁L hq₁3 hc16
  obtain ⟨αL, hαLs, hαLk⟩ := C10P4F.exists_alpha h2.1.some
  have hT1K : Ch10.T1 T L ≤ Subgroup.normalizer (K₁ : Set G) := fun x hx =>
    C10P4F.mem_normalizer_of_three hK₁c hK₁s hK₁a hαLs hαLk hq₁K hq₁L hq₁3 (hH.1.1 hx.1) hx.2
  have D : C10P4F.S5Data T L I H K₁ q₁ t :=
    ⟨hyp, h2, hb, ht, htn, hH.1.1, hK₁c, hK₁s, hK₁a, hq₁K, hq₁L, hq₁3, hT1K, hK₁M⟩
  obtain ⟨X, J, hX, hsylX, hJ, hLJ, hT1J, hm3⟩ := D.exists_XJ h311 h331 h37 h38 h39 hshape h113
  exact ⟨L, Or.inl rfl, hb.1, hb.2, X, J, hX, hsylX, hJ, hLJ, hT1J, hm3⟩

end CFSG.Quasithin.Vol2.Ch10.SecF

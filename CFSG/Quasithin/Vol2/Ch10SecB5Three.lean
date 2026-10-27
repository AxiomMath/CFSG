module

public import CFSG.Quasithin.Vol2.Ch10SecBXi

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem isMax_T (h : MaxCtx T L I t Ψ c) (hA : A = L32.Pa ∨ A = L32.Pb) :
    IsMaxSubgroupIn (preIn Ψ (A.prod A) ⊔ T) T := by
  have hT := h.hyp.fsu.sylow
  have hUA : L32.U3 ≤ A := by rcases hA with rfl | rfl; exacts [L32.u3_le_pa, L32.u3_le_pb]
  have hAU : ¬ A ≤ L32.U3 := by rcases hA with rfl | rfl; exacts [pa_not_le_u3, pb_not_le_u3]
  refine ⟨lt_preIn_sup hT h.hC hAU, fun Y hY hYle => ?_⟩
  have hTY : T ≤ Y := hY.le
  obtain ⟨hT0, htY⟩ := inf_fsuL0_props (L := L) hTY h.ht
  obtain ⟨B, hB, hYB⟩ := classify_preIn hT h.hC hT0 inf_le_right htY
  have hBA : B ≤ A := le_of_preIn_le h.hC (by
    rw [← hYB, ← inf_preIn_sup h.h37 h.h38 h.hyp h.ht h.htn h.hC hUA]
    exact inf_le_inf_right _ hYle)
  have hYeq : Y = preIn Ψ (B.prod B) ⊔ T := by
    rw [← hYB]; exact eq_inf_sup (hYle.trans (sup_le_sup_right (preIn_le Ψ _) _)) hTY
  rcases hB with rfl | rfl | rfl | rfl
  · exfalso
    apply hY.ne
    rw [hYeq, ← T0_eq_preIn hT h.hC]
    exact (sup_eq_right.mpr inf_le_left).symm
  · rcases hA with rfl | rfl
    · exact hYeq
    · exact absurd hBA pa_not_le_pb
  · rcases hA with rfl | rfl
    · exact absurd hBA pb_not_le_pa
    · exact hYeq
  · exfalso
    rcases hA with rfl | rfl
    · exact pa_ne_top (top_le_iff.mp hBA)
    · exact pb_ne_top (top_le_iff.mp hBA)

theorem isUniqueMaxOver_T (h : MaxCtx T L I t Ψ c) (hA : A = L32.Pa ∨ A = L32.Pb) :
    IsUniqueMaxOver (preIn Ψ (A.prod A) ⊔ T) T T := by
  have hmax := isMax_T h hA
  ext N
  simp only [maxOver, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hTN⟩
    by_contra hne
    exact hN.1.ne (hmax.2 N (lt_of_le_of_ne hTN (Ne.symm hne)) hN.1.le)
  · rintro rfl
    exact ⟨hmax, le_rfl⟩

theorem T1_normal (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) : T ≤ Subgroup.normalizer (T1 T L : Set G) := by
  have h2 := SecA.index_T1 h37 h38 hyp
  have hn : ((T1 T L).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := hn.conj_mem ⟨x, hx.1⟩ hx ⟨s, hs⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hx
    have := hn.conj_mem ⟨s * x * s⁻¹, hx.1⟩ hx ⟨s⁻¹, T.inv_mem hs⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa [mul_assoc] using this

theorem pCoreOf_XOf_le_T (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    pCoreOf 2 (XOf T L Ψ A) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 (XOf T L Ψ A) : Set G) :=
    (isXi_XOf h hD).2.1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hTQ)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans
    (SecA.pCoreOf_le_of_sylow h.hyp.fsu.sylow le_sup_right)

theorem pCoreOf_XOf_le_T1 (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    pCoreOf 2 (XOf T L Ψ A) ≤ T1 T L :=
  (le_inf (pCoreOf_XOf_le_T h hD) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
    (XOf_le_fsuL0 h hD))).trans (SecA.T0_le_T1 h.hyp.fsu.maximal.1)

theorem inf_T_le_pCoreOf_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    T ⊓ XOf T L Ψ A ≤ pCoreOf 2 (XOf T L Ψ A) := by
  intro y ⟨hyT, hyX⟩
  have hXL0 := XOf_le_fsuL0 h hD
  have hyT0 : y ∈ T0 T L := ⟨hyT, hXL0 hyX⟩
  rw [T0_eq_preIn h.hyp.fsu.sylow h.hC] at hyT0
  obtain ⟨hyL0, hyU⟩ := mem_preIn.mp hyT0
  have hyK := mem_prod_of_mem_XOf h hD hyX
  have hU8 : ∀ u ∈ L32.U3, u ^ 2 ^ 3 = 1 := fun u hu => by
    have := pow_card_eq_one' (G := ↥L32.U3) (x := ⟨u, hu⟩)
    rw [card_U3] at this
    exact congrArg Subtype.val this
  rw [pCoreOf_XOf h hD]
  exact ⟨hyX, mem_preIn.mpr ⟨hyL0, hD.two _ hyK.1 3 (hU8 _ hyU.1),
    hD.two _ hyK.2 3 (hU8 _ hyU.2)⟩⟩

theorem inf_T_sup_T1 (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    T ⊓ (XOf T L Ψ A ⊔ T1 T L) = T1 T L := by
  have hT1N : T1 T L ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) :=
    inf_le_left.trans (isXi_XOf h hD).2.1
  refine le_antisymm (fun y ⟨hyT, hy⟩ => ?_) (le_inf inf_le_left le_sup_right)
  have hy' : y ∈ ((XOf T L Ψ A ⊔ T1 T L : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hT1N] at hy'
  obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_mul.mp hy'
  have hxT : x ∈ T := by simpa using T.mul_mem hyT (T.inv_mem hs.1)
  exact (T1 T L).mul_mem (pCoreOf_XOf_le_T1 h hD (inf_T_le_pCoreOf_XOf h hD ⟨hxT, hx⟩)) hs

theorem isSylowTwoOf_T1 (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    IsSylowTwoOf (T1 T L) (XOf T L Ψ A ⊔ T1 T L) := by
  have hT := h.hyp.fsu.sylow
  have hTs : IsSylowTwoOf T (XOf T L Ψ A ⊔ T) :=
    ⟨le_sup_right, hT.1, SecA.not_two_dvd_index_of_le hT le_sup_right⟩
  have hTX := (isXi_XOf h hD).2.1
  have hTT1 := T1_normal h.h37 h.h38 h.hyp
  have hN : XOf T L Ψ A ⊔ T ≤ Subgroup.normalizer ((XOf T L Ψ A ⊔ T1 T L : Subgroup G) :
      Set G) := by
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun s hs => ?_
    have hsX := hTX hs
    have hsT1 := hTT1 hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hsX hsT1 ⊢
    rw [Subgroup.map_sup, hsX, hsT1]
  have := A4.isSylowTwoOf_inf_normal hTs (sup_le_sup_left inf_le_left _) hN
  rwa [inf_T_sup_T1 h hD] at this

end CFSG.Quasithin.Vol2.Ch10.SecB

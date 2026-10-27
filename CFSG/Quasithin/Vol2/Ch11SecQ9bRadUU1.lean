module

public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Nonquasi2
public import CFSG.Quasithin.Vol2.Ch11SecA11Transport
public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUP1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₂ U : Subgroup G} {n : ℕ}

namespace C11P9B

omit [Finite G] in
theorem le_V2_of_sup_eq
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂) : U ≤ V₂ :=
  le_sup_left.trans hUV.le

theorem ne_bot_of_sup_eq (h : Hyp11 G T L I n) (hV₂ : IsVi T L I n 2 V₂)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂) : U ≠ ⊥ := by
  intro h0
  rw [h0, bot_sup_eq] at hUV
  have h1 := IsVi.relIndex_eq hV₂
  rw [← hUV, Subgroup.relIndex_self] at h1
  have h2 : 1 < 2 ^ (n * 2) := Nat.one_lt_two_pow (by have := h.one_lt; omega)
  omega

theorem cComp_U (hF11 : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h : Hyp11 G T L I n) (hV₂ : IsVi T L I n 2 V₂)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂)
    (hTU : T ≤ Subgroup.normalizer (U : Set G))
    (hLU : L ⊓ Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    ∃ K : Subgroup G, K ∈ cComp (Subgroup.normalizer (U : Set G)) ∧ LOf L V₂ ≤ K ∧
      Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
      (LOf L V₂ = K ∨ Concl1111 (↥K ⧸ CFSG.pCore 2 ↥K) n) := by
  have hUV' : U ≤ fsuV T I := (le_V2_of_sup_eq hUV).trans (IsVi.le_fsuV hV₂)
  have hS : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (U : Set G))
      (Subgroup.normalizer (U : Set G)) := by
    rw [inf_eq_left.mpr hTU]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTU
  have hH := pCoreOf_normalizer_ne_bot_of_le h hUV' (ne_bot_of_sup_eq h hV₂ hUV)
  have hBH : LOf L V₂ ≤ Subgroup.normalizer (U : Set G) := (perfectCore_le _).trans hLU
  have hB := lOf_mem_lFamily hN h1102 h hV₂ (Or.inr rfl)
    (inf_le_left : T ⊓ Subgroup.normalizer (U : Set G) ≤ T)
  obtain ⟨K, ⟨hK, hBK⟩, -⟩ := CFSG.Quasithin.lemma_1_2_4_existsUnique h.fsu.qtke h.fsu.simple
    h.fsu.nonabelian h37 h39 hH hS hBH hB
  have hSB : T ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (LOf L V₂ : Set G) :=
    inf_le_left.trans (T_le_normalizer_lOf h.normal (IsVi.le_normalizer hV₂))
  have hnorm := CFSG.Quasithin.lemma_1_2_4_normal h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37
    h38 hH hS hB hBK hK hSB
  have hKH := le_of_mem_cComp hK
  refine ⟨K, hK, hBK, (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hnorm, ?_⟩
  have hD : BarData (modO2Image (Subgroup.normalizer (U : Set G)) (LOf L V₂)) n := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inr rfl) hV₂
    obtain ⟨e₁⟩ := modO2Image_quotEquiv hBH
    exact barData_of_quot_SL2 h.one_lt hF (e₁.symm.trans e)
  obtain ⟨e⟩ := modO2_mulEquiv hK
  rcases CFSG.Quasithin.lemma_1_2_4_list h.fsu.qtke h.fsu.simple h.fsu.nonabelian h312 hH hS
    hBH hB hK hBK with heq | h2 | h3
  · exact Or.inl (eq_of_modO2Image_eq hS hKH hBK (perfect_of_mem_cComp hK) hSB heq)
  · exact Or.inr (Concl1111.of_mulEquiv e.symm (concl_of_a312Case hF11.parab hD h2))
  · have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot h.fsu.qtke h.fsu.simple h.fsu.nonabelian hH
    have h36s := h36 _ hQ _ (modO2Image_mem_cComp hK)
    have hBL : modO2Image (Subgroup.normalizer (U : Set G)) (LOf L V₂) ≤
        modO2Image (Subgroup.normalizer (U : Set G)) K :=
      Subgroup.map_mono fun x hx => hBK hx
    exact Or.inr (Concl1111.of_mulEquiv e.symm (concl_of_nonquasi hD hBL h36s h3))

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA

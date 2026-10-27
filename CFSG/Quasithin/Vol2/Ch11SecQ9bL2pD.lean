module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bL2pC
public import CFSG.Quasithin.Vol2.Ch11SecA12B
public import CFSG.Quasithin.Vol2.Ch11SecA12Out

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

namespace C11P9B

theorem not_isSL3_of_centralizes (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12)
    (h331 : Stmt3_3_1) (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2)
    (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₁ < K)
    (hcomm : ∀ x ∈ xOne X (LOf L V₁), ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    ¬ IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L) := by
  intro hSL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := L_le_normalizer_fsuV h
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hX1L : xOne X (LOf L V₁) ≤ L := fun x hx => (hX.1 hx.1).1
  obtain ⟨hX1N, hNle⟩ := zL_le_of_isSL3 hFb hC hF hN h1102 h hV₁ hV₂ hX hSL
  have hOLT : pCoreOf 2 L ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_inf_L h)).trans inf_le_left
  have hTN : T ≤
      Subgroup.normalizer ((L ⊓ sectionCentralizer L (pCoreOf 2 L) : Subgroup G) : Set G) :=
    h.normal.trans (normalizer_le_normalizer_zL L)
  have hXT : xOne X (LOf L V₁) ⊔ T = (L ⊓ sectionCentralizer L (pCoreOf 2 L)) ⊔ T :=
    le_antisymm (sup_le_sup_right hX1N T)
      (sup_le (hNle.trans (sup_le le_sup_left (hOLT.trans le_sup_right))) le_sup_right)
  have hYN : oTwoUpper (xOne X (LOf L V₁) ⊔ T) =
      oTwoUpper (L ⊓ sectionCentralizer L (pCoreOf 2 L)) := by
    rw [hXT]
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => ?_) (oTwoUpper_mono le_sup_left)
    exact mem_oTwoUpper_of_odd (SecS.mem_of_mem_sup_of_odd hT2 hTN hx.1 hx.2) hx.2
  set Y := oTwoUpper (xOne X (LOf L V₁) ⊔ T) with hYdef
  have hLTY : L ⊔ T ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hYN]
    exact (sup_le Subgroup.le_normalizer h.normal).trans ((normalizer_le_normalizer_zL L).trans
      (normalizer_le_normalizer_oTwoUpper _))
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := (IsVi.le_normalizer hV₁).trans hNK
  have hX1K : xOne X (LOf L V₁) ≤ Subgroup.normalizer (K : Set G) :=
    (xOne_le_normalizer_V1 hN h1102 h hV₁ hX).trans hNK
  have hTC : T ≤ Subgroup.normalizer (sectionCentralizer K (pCoreOf 2 K) : Set G) :=
    fun t ht => mem_normalizer_sectionCentralizer' (hTK ht)
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hTK ht))
  have hX1C : xOne X (LOf L V₁) ≤ sectionCentralizer K (pCoreOf 2 K) := fun x hx =>
    ⟨hX1K hx, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hX1K hx),
      fun k hk => hcomm x hx k hk⟩
  have hYC : Y ≤ sectionCentralizer K (pCoreOf 2 K) :=
    (oTwoUpper_mono (sup_le_sup_right hX1C T)).trans ((Subgroup.closure_le _).mpr
      fun x hx => SecS.mem_of_mem_sup_of_odd hT2 hTC hx.1 hx.2)
  have hOKT : pCoreOf 2 K ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_inf_K h hV₁ hK hNK)).trans inf_le_left
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := le_sup_right.trans hLTY
  have hYY : oTwoUpper (Y ⊔ pCoreOf 2 K) = Y := by
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx =>
      SecS.mem_of_mem_sup_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
        (hOKT.trans hTY) hx.1 hx.2) ?_
    exact (Subgroup.closure_le _).mpr fun x hx =>
      mem_oTwoUpper_of_odd (Subgroup.mem_sup_left (Subgroup.subset_closure hx)) hx.2
  have hKW : K ≤ Subgroup.normalizer ((Y ⊔ pCoreOf 2 K : Subgroup G) : Set G) := by
    intro k hk
    refine mem_normalizer_of_map_le (N := Y ⊔ pCoreOf 2 K) ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h1 : k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
        have := (pCoreOf 2 K).inv_mem ((hYC hy).2.2 k hk)
        simpa [mul_assoc] using this
      have e : (MulAut.conj k).toMonoidHom y = (k * y * k⁻¹ * y⁻¹) * y := by
        simp [MulAut.conj_apply]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hy)
    · rintro _ ⟨o, ho, rfl⟩
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) o).mp ho)
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← hYY]
    exact hKW.trans (normalizer_le_normalizer_oTwoUpper _)
  have hYLT : Y ≤ L ⊔ T := (oTwoUpper_le _).trans (sup_le_sup_right hX1L T)
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le hLV (T_le_normalizer_fsuV T I)
  have hYVP : Y ⊓ fsuV T I ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer (hYLT.trans hLTV)).trans
        Subgroup.inf_normalizer_le_normalizer_inf) ((isPGroup_fsuV h).to_le inf_le_right)
  obtain ⟨x, hx, hx1, hxo⟩ := exists_orderOf_eq_of_dvd Nat.prime_three
    (card_xOne hC hF hN h1102 h hV₁ hV₂ hX) (by norm_num)
  have hxnC : x ∉ Subgroup.centralizer (fsuV T I : Set G) := fun hc => hx1 (by
    have hm : x ∈ X ⊓ Subgroup.centralizer (fsuV T I : Set G) := ⟨hx.1, hc⟩
    rwa [cartan_inf_centralizer h1102 h hX, Subgroup.mem_bot] at hm)
  obtain ⟨v, hv, hvx⟩ : ∃ v ∈ fsuV T I, v * x ≠ x * v := by
    by_contra hcon
    exact hxnC (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      by_contra fun hne => hcon ⟨v, hv, hne⟩)
  have hodd3 : Odd (orderOf x) := by
    rw [hxo]
    exact ⟨1, rfl⟩
  have hvT := fsuV_le_T h hv
  have hxY : x ∈ Y := mem_oTwoUpper_of_odd (Subgroup.mem_sup_left hx) hodd3
  have hvxY : v * x * v⁻¹ ∈ Y := by
    refine mem_oTwoUpper_of_odd (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_right hvT) (Subgroup.mem_sup_left hx))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hvT))) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hodd3
  have hcY : v * x * v⁻¹ * x⁻¹ ∈ Y := Subgroup.mul_mem _ hvxY (Subgroup.inv_mem _ hxY)
  have hcV : v * x * v⁻¹ * x⁻¹ ∈ fsuV T I := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hLV (hX1L hx)) v⁻¹).mp
      (Subgroup.inv_mem _ hv)
    have e : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hv h1
  have hc1 : v * x * v⁻¹ * x⁻¹ ≠ 1 := by
    intro h0
    apply hvx
    calc v * x = (v * x * v⁻¹ * x⁻¹) * x * v := by group
      _ = x * v := by rw [h0, one_mul]
  have hP1 : pCoreOf 2 Y ≠ ⊥ := fun h0 => hc1 (by
    have hm := hYVP ⟨hcY, hcV⟩
    rwa [h0, Subgroup.mem_bot] at hm)
  have hPN := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y
  have hM := normalizer_le_of_isPGroup h331 h (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hP1
    (hLTY.trans hPN)
  exact not_le_normalizer_of_lt hN h1102 h hV₁ (Or.inl rfl) hK hlt (hKY.trans (hPN.trans hM))

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA

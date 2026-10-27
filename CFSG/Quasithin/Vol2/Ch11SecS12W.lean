module

public import CFSG.Quasithin.Vol2.Ch11SecS12K
public import CFSG.Quasithin.Vol2.Ch11SecSCartan
public import CFSG.Quasithin.Vol2.Ch11SecSSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecD
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem natural_star (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (hG2 : SecA.FactG2DerivedOrder)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hSL3 : KindSL3 L (fsuV T I) n) :
    IsNaturalSL3Module n L (pCoreOf 2 (L ⊔ T)) (fsuV T I) V₁ := by
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨_, -, -, -, hc⟩ := h1102 G T L I n h
  have hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rcases (h1103 G T L I n h).2.2.1 with ⟨h1, -⟩ | ⟨hk, -⟩
    · exact h1
    · rcases hk with hk | hk
      · exact (SecA.kind_not_SL3_Sp4 (by omega) hSL3 hk).elim
      · exact (SecA.kind_not_SL3_G2 hG2 hn hSL3 hk).elim
  rcases hc with ⟨K, _, _, hK, he, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩
  · exact isNaturalSL3Module_of_cV h1102 h hV₁ hCV hK he π hπ
  · exact (SecA.kind_not_SL3_Sp4 (by omega) hSL3 ⟨K, inferInstance, inferInstance, hK, he⟩).elim
  · exact (SecA.kind_not_SL3_G2 hG2 hn hSL3 ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem almostSpecialHyp_star (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (hG2 : SecA.FactG2DerivedOrder) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hSL3 : KindSL3 L (fsuV T I) n) :
    AlmostSpecialHyp (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨D⟩ := (natural_star h1102 h1103 hG2 h hV₁ hSL3).nonempty_data
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hLV := SecA.L_le_normalizer_fsuV h
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hlOne : LOf L V₁ ≤ lOne L V₁ := by
    have h1 : oTwoUpper (LOf L V₁) = LOf L V₁ :=
      C2Nine.oTwoUpper_eq_of_perfect (perfectCore_perfect _)
    rw [← h1]
    exact oTwoUpper_mono (perfectCore_le _)
  have hlOneL : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  have h1 : ∀ w : Fin 3 → GaloisField 2 n, D.θ ⟨1, L.one_mem⟩ • w = (1 : GaloisField 2 n) • w :=
    fun w => by
      rw [one_smul]
      have : (⟨1, L.one_mem⟩ : ↥L) = 1 := rfl
      rw [this, map_one, one_smul]
  have hnatV := NatData3'.natEig_V D hV₁V L.one_mem h1
  have hlt : V₁ < fsuV T I := lt_of_isNatEig hnatV hV₁V
  have hV₁O : V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      (h.fsu.sylow.1.to_le ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)))
  have hO2ne : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := fun hb =>
    SecA.IsVi.ne_bot h hV₁ le_rfl (le_bot_iff.mp (hb ▸ hV₁O))
  refine ⟨SecA.isElemAbelian_fsuV h, SecA.IsVi.ne_bot h hV₁ le_rfl, hV₁V,
    (C2Nine.oTwoUpper_eq_of_perfect (perfect_of_hyp11 h)).symm, SecA.fsuV_le_T h, hTN,
    SecA.T_le_normalizer_fsuV T I, h.normal,
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right, le_rfl,
    sup_le (hlOneL.trans inf_le_right) hTN, isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN,
    charTwo_of_inH h.fsu.qtke.2.1 (h.fsu.sylow.1.toSylow h.fsu.sylow.2)
      (H := Subgroup.normalizer (V₁ : Set G))
      (by rw [IsPGroup.toSylow_coe]; exact ⟨hTN, hO2ne⟩), ?_⟩
  refine ⟨hlt, sup_le ((hlOneL.trans inf_le_left).trans hLV) (SecA.T_le_normalizer_fsuV T I),
    sup_le (hlOneL.trans inf_le_right) hTN, fun W hV₁W hWV hWN => ?_⟩
  exact hnatV.eq_or_eq le_rfl (NatData3'.alpha0_surjective D hn hV₁V)
    (NatData3'.lOf_le.trans hLV) hV₁W hWV (hlOne.trans (le_sup_left.trans hWN))

variable {V₁ V₂ X K : Subgroup G}

theorem eq_one_of_commute_xOne (hC : CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h : StarHyp G T L I V₁ V₂ X K) (hSL3 : KindSL3 L (fsuV T I) 2)
    {v : G} (hv : v ∈ fsuV T I) (hvc : ∀ x ∈ SecA.xOne X (LOf L V₁), x * v = v * x) : v = 1 := by
  have hc := (cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  obtain ⟨D⟩ := (natural_star h1102 h1103 hG2 h.hyp h.v₁ hSL3).nonempty_data
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ SecA.xOne X (LOf L V₁), x ≠ 1 := by
    have : Nontrivial ↥(SecA.xOne X (LOf L V₁)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hc.cardX₁]
      norm_num
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : ↥(SecA.xOne X (LOf L V₁)))
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩
  have hxL : x ∈ L := (h.cartan.1 hx.1).1
  obtain ⟨c, -, hxc⟩ :=
    exists_scalar_of_xOne hFb hN h1102 h.hyp h.v₁ h.v₂ h.cartan hSL3 D hx hxL
  have hc1 : c ≠ 1 := scalar_ne_one_of_xOne D hc.cardX₁ hx hx1 hxL hxc
  have he := D.equiv ⟨x, hxL⟩ ⟨v, hv⟩
  have hfix : conjAct (fsuV T I) ⟨x, D.hnorm hxL⟩ ⟨v, hv⟩ = ⟨v, hv⟩ := by
    apply Subtype.ext
    show x * v * x⁻¹ = v
    rw [hvc x hx, mul_inv_cancel_right]
  rw [hfix, natAct3_apply, hxc] at he
  have h0 : Multiplicative.toAdd (D.ψ ⟨v, hv⟩) = 0 := by
    have h2 := congrArg Multiplicative.toAdd he
    rw [toAdd_ofAdd] at h2
    have h3 : (c - 1) • Multiplicative.toAdd (D.ψ ⟨v, hv⟩) = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hc1)
  have h4 : D.ψ ⟨v, hv⟩ = 1 := by
    rw [← ofAdd_toAdd (D.ψ ⟨v, hv⟩), h0, ofAdd_zero]
  have h5 : (⟨v, hv⟩ : ↥(fsuV T I)) = 1 := by
    rw [← D.ψ.map_eq_one_iff]
    exact h4
  exact congrArg Subtype.val h5

theorem isElemAbelian_cU (hC : CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h : StarHyp G T L I V₁ V₂ X K) (hSL3 : KindSL3 L (fsuV T I) 2) :
    IsElemAbelian 2 (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
      Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G)) := by
  have hb := almostSpecialHyp_star h1102 h1103 hG2 h.hyp h.v₁ hSL3
  have hV₁V := SecA.IsVi.le_fsuV h.v₁
  have key : ∀ z ∈ V₁, z ∈ Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G) → z = 1 :=
    fun z hz hzc => eq_one_of_commute_xOne hC hN hG2 hFb h1102 h1103 h hSL3 (hV₁V hz)
      fun x hx => Subgroup.mem_centralizer_iff.mp hzc x hx
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
  · have hc := hb.G22_commutator_mem a.2.1 b.2.1
    have hcc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈
        Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ a.2.2 b.2.2)
        (Subgroup.inv_mem _ a.2.2)) (Subgroup.inv_mem _ b.2.2)
    have h1 := key _ hc hcc
    simp only [Subgroup.coe_mul]
    calc (a : G) * b = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · have hs := hb.G22_sq_mem ha.1
    exact key _ hs (Subgroup.pow_mem _ ha.2 2)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

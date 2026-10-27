module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.HalphaNonsolvable
import CFSG.OddTranspositions.O4PairTenThreeTranspositions
import CFSG.Timmesfeld.Bridge.OddTranspSecondKind
import CFSG.HardMathSupport.Cooperstein.Proving.PermTwoCore
import CFSG.OddTranspositions.O4PairCommSet
import CFSG.HardMathSupport.Cooperstein.Proving.QuotientPCoreRigid

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem exists_mem_Yten_conj (i j : Fin 10) : ∃ g ∈ Yten, g * y i * g⁻¹ = y j := by
  induction y_nc_connected i j with
  | refl => exact ⟨1, Yten.one_mem, by simp⟩
  | @tail a b _ hab ih =>
    obtain ⟨g, hg, hgy⟩ := ih
    have ha2 : y a * y a = 1 := y_mul_self a
    have hb2 : y b * y b = 1 := y_mul_self b
    have hodd : Odd (orderOf (y a * y b)) := by
      have h := y_products_order a b
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h
      · exfalso
        apply hab.2
        have h1 : y a * y b = 1 := orderOf_eq_one_iff.mp h
        have hab' : y a = y b := by
          calc y a = y a * (y b * y b) := by rw [hb2, mul_one]
            _ = (y a * y b) * y b := by rw [mul_assoc]
            _ = y b := by rw [h1, one_mul]
        rw [hab']
      · exfalso
        apply hab.2
        have h2 : (y a * y b) * (y a * y b) = 1 := by
          have h2' := pow_orderOf_eq_one (y a * y b)
          rw [h, pow_two] at h2'
          exact h2'
        have hainv : (y a)⁻¹ = y a := inv_eq_of_mul_eq_one_right ha2
        have hbinv : (y b)⁻¹ = y b := inv_eq_of_mul_eq_one_right hb2
        have h3 : y a * y b = (y a * y b)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
        show y a * y b = y b * y a
        rw [h3, mul_inv_rev, hainv, hbinv]
      · rw [h]; decide
    obtain ⟨k, hk⟩ := OddTransp.exists_zpow_conj_eq ha2 hb2 hodd (-1)
    have hyb : (y a * y b) ^ (-1 : ℤ) * y a = y b := by
      rw [zpow_neg_one, mul_inv_rev, inv_eq_of_mul_eq_one_right hb2,
        inv_eq_of_mul_eq_one_right ha2, mul_assoc, ha2, mul_one]
    have hya : y a ∈ Yten := Subgroup.subset_closure (Set.mem_range_self a)
    have hyb' : y b ∈ Yten := Subgroup.subset_closure (Set.mem_range_self b)
    have hmem : (y a * y b) ^ k ∈ Yten := Subgroup.zpow_mem _ (Subgroup.mul_mem _ hya hyb') k
    refine ⟨(y a * y b) ^ k * g, Subgroup.mul_mem _ hmem hg, ?_⟩
    calc (y a * y b) ^ k * g * y i * ((y a * y b) ^ k * g)⁻¹ =
        (y a * y b) ^ k * (g * y i * g⁻¹) * ((y a * y b) ^ k)⁻¹ := by group
      _ = y b := by rw [hgy, hk, hyb]

private theorem Yten_le_centralizer :
    Yten ≤ Subgroup.centralizer ({SemidirectProduct.inr frob25} : Set PSigmaL225) := by
  rw [Yten, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (y_commute_base i).eq

private theorem pCore_two_FixK : CFSG.pCore 2 FixK = ⊥ := by
  obtain ⟨e, -⟩ := fixK_equiv_s5
  have h := CFSG.pCore_map_iso 2 e
  rw [CFSG.HardMathSupport.Cooperstein.Proving.pCore_two_perm_eq_bot_of_five_le le_rfl] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem pCore_two_Yten_le_center : CFSG.pCore 2 Yten ≤ Subgroup.center Yten := by
  intro w hw
  have hle : (CFSG.pCore 2 Yten).map leftHomYten ≤ CFSG.pCore 2 FixK :=
    CFSG.HardMathSupport.Cooperstein.Proving.le_pCore_of_normal_pGroup'
      (Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := Yten)) leftHomYten
        leftHomYten_surjective)
      ((CFSG.pCore_isPGroup (p := 2) (G := Yten)).map leftHomYten)
  have hw1 : leftHomYten w = 1 := by
    have hmem := hle ⟨w, hw, rfl⟩
    rwa [pCore_two_FixK, Subgroup.mem_bot] at hmem
  have hleft : (w : PSigmaL225).left = 1 := congrArg Subtype.val hw1
  rw [Subgroup.mem_center_iff]
  intro v
  apply Subtype.ext
  show (v : PSigmaL225) * w = w * v
  rcases right_mem_of_mem w.2 with hr | hr
  · rw [show (w : PSigmaL225) = 1 from SemidirectProduct.ext hleft hr, one_mul, mul_one]
  · rw [show (w : PSigmaL225) = SemidirectProduct.inr frob25 from SemidirectProduct.ext hleft hr]
    exact Subgroup.mem_centralizer_singleton_iff.mp (Yten_le_centralizer v.2)

theorem nonempty_Halpha_equiv_Yten (hC : HypothesisC D) (hO4 : O4PairData G D) :
    Nonempty (Halpha D hC.alpha ≃* Yten) := by
  classical
  obtain ⟨φ, hφD, hφd⟩ := exists_mulEquiv_of_mem hO4 hC.hd
  have hφcomm := image_commSet_eq_range_y hφD hφd
  have hYmap : Yten = (Subgroup.closure (commSet D hC.d)).map φ.toMonoidHom := by
    rw [MonoidHom.map_closure, Yten]
    congr 1
    exact hφcomm.symm
  obtain ⟨e₀, he₀, hE, -⟩ := hC.hE
  have hφE : φ '' hC.E = Set.range y := by
    apply le_antisymm
    · rw [← hφcomm]
      exact Set.image_mono (OddLocal.subset_commSet hC.setup.normal hC.hE)
    · rintro _ ⟨j, rfl⟩
      obtain ⟨i₀, hi₀⟩ : φ e₀ ∈ Set.range y := hφcomm ▸ ⟨e₀, he₀, rfl⟩
      obtain ⟨g', hg', hg'y⟩ := exists_mem_Yten_conj i₀ j
      rw [hYmap] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      refine ⟨g * e₀ * g⁻¹, ?_, ?_⟩
      · rw [hE]
        exact ⟨g, hg, rfl⟩
      · rw [← hg'y, hi₀]
        simp [map_mul, map_inv]
  have hmap : (Halpha D hC.alpha).map φ.toMonoidHom = Yten := by
    rw [Halpha, hC.DalphaStar_alpha, MonoidHom.map_closure, Yten]
    congr 1
  exact ⟨(φ.subgroupMap (Halpha D hC.alpha)).trans (MulEquiv.subgroupCongr hmap)⟩

theorem pCore_two_le_center_Halpha_of_o4PairData (hC : HypothesisC D) (hO4 : O4PairData G D) :
    CFSG.pCore 2 (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) := by
  obtain ⟨ψ⟩ := nonempty_Halpha_equiv_Yten hC hO4
  intro p hp
  have hψp : ψ p ∈ Subgroup.center Yten := by
    apply pCore_two_Yten_le_center
    rw [← CFSG.pCore_map_iso 2 ψ]
    exact ⟨p, hp, rfl⟩
  rw [Subgroup.mem_center_iff] at hψp ⊢
  intro h
  apply ψ.injective
  rw [map_mul, map_mul]
  exact hψp (ψ h)

end CFSG.OddTranspositions.PartThree

end

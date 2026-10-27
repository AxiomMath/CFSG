module

public import CFSG.Quasithin.Vol2.Ch7SL3Pair
public import CFSG.Quasithin.Background.HSp4Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_2_1_Sp4Pair_binary (G : Type) [Group G] [Finite G] (T L I : Subgroup G)
    (_hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) (_hc : IsMulCommutative ↥(fsuV T I))
    (htw : IsTwistedPair T L I) (n : ℕ) (hn2 : 2 ≤ n)
    (hnat : BinaryNaturalSp4 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
      (I.subgroupOf (fsuV T I)) ⊥ n) :
    aParam (autI hV ⊤) < 2 * n ∧ 3 * n ≤ mParam (autI hV ⊤) := by
  obtain ⟨t, htT, hsup, hinf, hniso⟩ := htw
  have hIV : I ≤ fsuV T I := le_fsuV I T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hItV : CFSG.conjugate I t ≤ fsuV T I := by
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem htT)) y).mp (hIV hy)
    simpa [mul_assoc] using this
  have htN : t⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) := hTV (T.inv_mem htT)
  set φ := convI hV ⟨t⁻¹, htN⟩ with hφ
  set V₁ : Subgroup (IntMod (fsuV T I) hV) := intSub hV I with hV₁
  have hL : BinaryNaturalSp4 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) V₁ ⊥ n := hnat
  have hmap : V₁.map φ.toMonoidHom = intSub hV (CFSG.conjugate I t) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_intSub]
      change (φ v).val ∈ CFSG.conjugate I t
      rw [hφ, convI_apply_val, mem_conjugate_iff']
      have : t * (t⁻¹ * v.val * t⁻¹⁻¹) * t⁻¹ = v.val := by group
      rw [this]
      exact hv
    · intro hx
      rw [mem_intSub] at hx
      have hx' := mem_conjugate_iff'.mp hx
      refine ⟨IntMod.mk hV ⟨t * x.val * t⁻¹, hIV hx'⟩, hx', ?_⟩
      apply IntMod.val_injective
      change (φ (IntMod.mk hV ⟨t * x.val * t⁻¹, hIV hx'⟩)).val = x.val
      rw [hφ, convI_apply_val]
      change t⁻¹ * (t * x.val * t⁻¹) * t⁻¹⁻¹ = x.val
      group
  have hφN : φ ∈ Subgroup.normalizer (autI hV (fsuL0 T L) :
      Set (MulAut (IntMod (fsuV T I) hV))) :=
    autI_top_le_normalizer hV hNM (convI_mem_autI hV (Subgroup.mem_top _) htN)
  have hinf' : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥ := by
    rw [hmap, eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have : x.val ∈ I ⊓ CFSG.conjugate I t := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact IntMod.val_injective this
  have hsup' : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤ := by
    rw [hmap]
    apply Subgroup.map_injective (valHom_injective hV)
    rw [Subgroup.map_sup, hV₁, map_valHom_intSub hV hIV, map_valHom_intSub hV hItV, hsup,
      map_valHom_top]
  have hniso' : ¬ Pair.IsoMod (autI hV (fsuL0 T L)) V₁ (V₁.map φ.toMonoidHom) := by
    rw [hmap]
    intro h
    exact hniso (isXSectionIso_of_isoMod hV hIV hItV (le_fsuL0 T L)
      ((le_fsuL0 T L).trans (le_sup_left.trans hN)) h)
  exact Sp4.H7_Sp4Pair hn2 hL hφN hinf' hsup' hniso' (autI_top_le_normalizer hV hNM)

@[expose] def Stmt7_2_1_Sp4PairA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      IsTwistedPair T L I →
        AlternatingNatural (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
            (I.subgroupOf (fsuV T I)) ⊥ 6 →
          aParam (autI hV ⊤) < 2 ∧ 3 ≤ mParam (autI hV ⊤)

theorem stmt7_2_1_Sp4Pair_of_A6 (hA6 : Stmt7_2_1_Sp4PairA6) : Stmt7_2_1_Sp4Pair := by
  intro G _ _ T L I hyp hV hN hNM hc htw
  exact ⟨fun n hn hnat => stmt7_2_1_Sp4Pair_binary G T L I hyp hV hN hNM hc htw n hn hnat,
    hA6 G T L I hyp hV hN hNM hc htw⟩

theorem stmt7_3_5_of_inputs (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h732 : Stmt7_3_2) (h734 : Stmt7_3_4)
    (hA6 : Stmt7_2_1_Sp4PairA6) : Stmt7_3_5 :=
  stmt7_3_5_of h37 h38 h39 hmod h732 h734 (stmt7_2_1_Sp4Pair_of_A6 hA6)

end CFSG.Quasithin.H13

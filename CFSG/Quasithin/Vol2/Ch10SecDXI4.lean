module

public import CFSG.Quasithin.Vol2.Ch10SecDXI3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem kOf_inf_le_pCoreOf
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) :
    Xz T L (v₁ * v₂) ⊓ kOf (fsuUL T L I) v₁ ⊓ kOf ⁅fsuVM T L I, CFSG.conjugate L t⁆ v₂ ≤
      pCoreOf 2 (Xz T L (v₁ * v₂)) := by
  have hconj : ∀ y ∈ Xz T L (v₁ * v₂), ∀ g ∈ Xz T L (v₁ * v₂) ⊓ kOf (fsuUL T L I) v₁ ⊓
      kOf ⁅fsuVM T L I, CFSG.conjugate L t⁆ v₂, y * g * y⁻¹ ∈ Xz T L (v₁ * v₂) ⊓
        kOf (fsuUL T L I) v₁ ⊓ kOf ⁅fsuVM T L I, CFSG.conjugate L t⁆ v₂ := by
    rintro y hy g ⟨⟨hgX, hg1⟩, hg2⟩
    obtain ⟨hyN1, hyv1, hyN2, hyv2⟩ := mem_normalizer_V12_of_mem_Xz h37 h38 h hc hd hy
    exact ⟨⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hgX) (Subgroup.inv_mem _ hy),
      conj_mem_kOf hyN1 hyv1 hg1⟩, conj_mem_kOf hyN2 hyv2 hg2⟩
  obtain ⟨ht, htn, hv1, -, hv2, -⟩ := hd
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
    (inf_le_left.trans inf_le_left) (fun y hy => ?_) ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconj y hy g, fun hg => ?_⟩
    have := hconj y⁻¹ (Subgroup.inv_mem _ hy) _ hg
    simpa [mul_assoc] using this
  · rintro ⟨g, ⟨hgX, hg1⟩, hg2⟩
    have hV := SecA.isElemAbelian_fsuVM h
    have hle2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
      commutator_le_left_of_le_normalizer
        ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
    have h1 := sq_mem_centralizer_of_mem_kOf (hV.2 v₁ (V1_le_V hv1.1)) hg1
    have h2 := sq_mem_centralizer_of_mem_kOf (hV.2 v₂ (hle2 hv2.1)) hg2
    have hVc : g ^ 2 ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
      have hle : fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤
          Subgroup.centralizer ({g ^ 2} : Set G) :=
        sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp h1) a ha))
          (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp h2) a ha))
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [SecA.fsuVM_eq_sup h37 h38 h ht htn] at hw
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    have hO2 := SecA.fsuL0_inf_centralizer_le h37 h38 h
      ⟨(fsuL0 T L).pow_mem (oTwoUpper_le _ hgX).1 2, hVc⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨_, hO2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (g ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_succ', pow_mul]
    exact hk'

theorem exists_mul_conj_mem_kOf
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) {x : G} (hxX : x ∈ Xz T L (v₁ * v₂))
    (hxo : Odd (orderOf x)) (hxC : x ∉ Subgroup.centralizer (fsuUL T L I : Set G)) :
    ∃ s ∈ T ⊓ L, x * (s * x * s⁻¹) ∈ kOf (fsuUL T L I) v₁ := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hv1 : v₁ ∈ fsuUL T L I := hd.2.2.1.1
  have hv11 : v₁ ≠ 1 := hd.2.2.2.1
  have hS := SecA.isSylowTwoOf_inf h.fsu.maximal.1
  have hLN : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1
  have hP8 : Nat.card (autOn (T ⊓ L) (fsuUL T L I)) = 8 :=
    D.card_sylow (isSylowTwoOf_autOn hS hLN)
  set P' := (autOn (T ⊓ L) (fsuUL T L I)).comap D.rho with hP'
  have hrange : autOn (T ⊓ L) (fsuUL T L I) ≤ D.rho.range := fun σ hσ => by
    obtain ⟨γ, hγ⟩ := D.exists_rho (A4.autOn_mono hS.1 hσ)
    exact ⟨γ, hγ⟩
  have hP'8 : Nat.card P' = 8 := by
    rw [← hP8, ← Subgroup.map_comap_eq_self hrange,
      Subgroup.card_map_of_injective D.rho_injective]
  have hc0 : coord D ⟨v₁, hv1⟩ ≠ 0 := fun h0 =>
    hv11 (congrArg Subtype.val (coord_injective D (h0.trans (coord_one D).symm)))
  obtain ⟨σ, hσP, hσA⟩ : ∃ σ ∈ P', σ ∉ L3.AS {0, coord D ⟨v₁, hv1⟩} := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card P' ≤ (L3.AS {0, coord D ⟨v₁, hv1⟩}).card := by
      rw [← Set.ncard_coe_finset,
        show Nat.card P' = (P' : Set L3.Γ).ncard from Nat.card_coe_set_eq (P' : Set L3.Γ)]
      exact Set.ncard_le_ncard (fun σ hσ => hcon σ hσ) (Finset.finite_toSet _)
    rw [L3.AS_card _ hc0, hP'8] at hle
    omega
  obtain ⟨⟨s, hsN⟩, hsTL, hsσ⟩ := (show D.rho σ ∈ autOn (T ⊓ L) (fsuUL T L I) from hσP)
  have hsTL' : s ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hsTL
  have hsv : s * v₁ = v₁ * s := (Subgroup.mem_centralizer_iff.mp hd.2.2.1.2) s (inf_le_T1 hsTL')
  have hσ8 : σ ^ 8 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥P') (x := ⟨σ, hσP⟩)
    rw [hP'8] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨hxN, hxv, -, -⟩ := mem_normalizer_V12_of_mem_Xz h37 h38 h hc hd hxX
  have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_mem h37 h38 h h3 hc hd (oTwoUpper_le _ hxX) hxo
  obtain ⟨δ, hδ⟩ := D.exists_rho (g := conjAct (fsuUL T L I) ⟨x, hxN⟩)
    (by rw [autOn_L_V1_eq_top h3 hc]; trivial)
  have hmem := L3.mul_conj_mem_AS _ hc0 δ (act_coord_of_rho D hxN hv1 hxv hδ)
    (pow_eq_one_of_rho D hxN hδ hx3) (ne_one_of_rho D hxN hδ hxC) σ
    (act_coord_of_rho D hsN hv1 hsv hsσ.symm) hσ8 hσA
  have hρ := rho_mul_of D hxN _ hδ (rho_mul_of D _ (Subgroup.inv_mem _ hsN)
    (rho_mul_of D hsN hxN hsσ.symm hδ) (rho_inv_of D hsN hsσ.symm))
  refine ⟨s, hsTL', mem_kOf_of_rho D _ hv1 ?_ hρ hmem⟩
  have hx : Commute x v₁ := hxv
  have hs : Commute s v₁ := hsv
  exact (hx.mul_left ((hs.mul_left hx).mul_left hs.inv_left)).eq

end CFSG.Quasithin.Vol2.Ch10.SecD

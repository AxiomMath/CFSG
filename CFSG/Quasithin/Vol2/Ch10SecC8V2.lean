module

public import CFSG.Quasithin.Vol2.Ch10SecC8Trans
public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Vol2.Ch10SecBL32
public import CFSG.Quasithin.Vol2.Ch10SecC8V1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 SecB.L32
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuUL_module_facts (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hnat : BinaryNaturalSL (autOn L (fsuUL T L I)) ⊤ (cV1 T L I) 3 1) (hne : cV1 T L I ≠ ⊥) :
    (∀ w : ↥(fsuUL T L I), w ^ 2 = 1) ∧ fixV (autOn L (fsuUL T L I)) = cV1 T L I ∧
      Nat.card ↥(cV1 T L I) = 2 ∧
      (∀ a ∈ autOn L (fsuUL T L I), a ≠ 1 → a ^ 2 = 1 →
        commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
          Nat.card (fixV (Subgroup.zpowers a)) = 4) ∧
      (∀ A : Subgroup (MulAut ↥(fsuUL T L I)), A ≤ autOn L (fsuUL T L I) → IsElemAbelian2 A →
        Nat.card A ≤ 4) := by
  have hsq := sq_eq_one_fsuUL hyp
  have hfix := fixV_autOn_fsuUL h37 h38 hyp h1011 (T := T) (L := L) (I := I)
  have hcard := card_fsuUL h37 h38 hyp h1011 h484 D hnat hne
  have hind := isIndecompModule_fsuUL h37 h38 hyp h1011 D
  have hnat' : BinaryNaturalSL (autOn L (fsuUL T L I)) ⊤ (fixV (autOn L (fsuUL T L I))) 3 1 := by
    rw [hfix]
    exact hnat
  have hB := B4_8_2 hsq hcard.1 hnat' hind
  refine ⟨hsq, hfix, hcard.2, fun a ha ha1 ha2 => ?_, fun A hA hAel =>
    (offHyp_fsuUL h37 h38 hyp h1011 h484 D hnat hne).E4 A hA hAel⟩
  obtain ⟨h1, h2⟩ := hB.2.2.2 a ha ha1 ha2
  refine ⟨h1, ?_⟩
  rw [card_eq_two_pow hsq, h2]
  norm_num

omit [Finite G] in
theorem mem_V2_iff {t : G} (ht : t ∈ T) (x : G) :
    x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ↔ t * x * t⁻¹ ∈ fsuUL T L I := by
  rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
  exact SecA.mem_conjugate_iff

theorem exists_V2_data (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hD : ∀ γ, ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
      autOn (T ⊓ L) (fsuUL T L I) ↔ γ ∈ SecB.L32.U3)
    (hnat : BinaryNaturalSL (autOn L (fsuUL T L I)) ⊤ (cV1 T L I) 3 1) (hne : cV1 T L I ≠ ⊥)
    {t : G} (ht : t ∈ T) [IsMulCommutative ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆)] :
    ∃ D₂ : L3Data (autOn (CFSG.conjugate L t) (⁅fsuVM T L I, CFSG.conjugate L t⁆)) ⊤
        ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
          (⁅fsuVM T L I, CFSG.conjugate L t⁆)),
      (∀ γ, ((D₂.π γ : ↥(autOn (CFSG.conjugate L t) (⁅fsuVM T L I, CFSG.conjugate L t⁆))) :
        MulAut ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆)) ∈
          autOn (T ⊓ CFSG.conjugate L t) (⁅fsuVM T L I, CFSG.conjugate L t⁆) ↔
          γ ∈ SecB.L32.U3) ∧
      fixV (autOn (CFSG.conjugate L t) (⁅fsuVM T L I, CFSG.conjugate L t⁆)) =
        (Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
          (⁅fsuVM T L I, CFSG.conjugate L t⁆) ∧
      Nat.card ↥((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
          (⁅fsuVM T L I, CFSG.conjugate L t⁆)) = 2 ∧
      (∀ a ∈ autOn (CFSG.conjugate L t) (⁅fsuVM T L I, CFSG.conjugate L t⁆), a ≠ 1 →
        a ^ 2 = 1 → commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
          Nat.card (fixV (Subgroup.zpowers a)) = 4) ∧
      (∀ A : Subgroup (MulAut ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆)),
        A ≤ autOn (CFSG.conjugate L t) (⁅fsuVM T L I, CFSG.conjugate L t⁆) →
          IsElemAbelian2 A → Nat.card A ≤ 4) := by
  have hW := mem_V2_iff (L := L) (I := I) ht
  have hX : ∀ x, x ∈ CFSG.conjugate L t ↔ t * x * t⁻¹ ∈ L := fun x => SecA.mem_conjugate_iff
  have hXT : ∀ x, x ∈ T ⊓ CFSG.conjugate L t ↔ t * x * t⁻¹ ∈ T ⊓ L := by
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hX]
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), hxL⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, hxL⟩
      have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [e]
      exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
  set e := conjIso t hW with he
  have hG := autOn_conjugate_eq_map t hX hW
  have hGT := autOn_conjugate_eq_map t hXT hW
  have hC : ∀ x : G, x ∈ Subgroup.centralizer (fsuL0 T L : Set G) ↔
      t * x * t⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
    have hN := SecA.le_normalizer_centralizer (V := fsuL0 T L) (SecA.le_fsuM T L)
    intro x
    constructor
    · intro h
      exact (Subgroup.mem_normalizer_iff.mp (hN ht) x).mp h
    · intro h
      have := (Subgroup.mem_normalizer_iff.mp (hN (T.inv_mem ht)) _).mp h
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [e] at this
  have hZ' : ∀ w : ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆),
      w ∈ (Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
        (⁅fsuVM T L I, CFSG.conjugate L t⁆) ↔ e.symm w ∈ cV1 T L I := by
    intro w
    rw [Subgroup.mem_subgroupOf, cV1, Subgroup.mem_subgroupOf, he, conjIso_symm_apply]
    exact hC w
  obtain ⟨D₂, hD₂⟩ := exists_L3Data_map e D hG hZ'
  obtain ⟨-, hfix1, hZc1, hFF1, hE41⟩ := fsuUL_module_facts h37 h38 hyp h1011 h484 D hnat hne
  have hZmap : (Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
      (⁅fsuVM T L I, CFSG.conjugate L t⁆) = (cV1 T L I).map e.toMonoidHom := by
    ext w
    rw [Subgroup.mem_map_equiv, hZ']
  refine ⟨D₂, fun γ => ?_, ?_, ?_, fun a ha ha1 ha2 => ?_, fun A hA hAel => ?_⟩
  · rw [hD₂ γ, hGT, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact hD γ
  · rw [hG, fixV_map_congr, hfix1, hZmap]
  · rw [hZmap, Subgroup.card_map_of_injective e.injective, hZc1]
  · rw [hG] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    have ha1' : a' ≠ 1 := fun h => ha1 (by rw [h, map_one])
    have ha2' : a' ^ 2 = 1 := (MulAut.congr e).injective (by
      rw [map_pow, map_one]
      exact ha2)
    obtain ⟨h1, h2⟩ := hFF1 a' ha' ha1' ha2'
    have hz : Subgroup.zpowers ((MulAut.congr e).toMonoidHom a') =
        (Subgroup.zpowers a').map (MulAut.congr e).toMonoidHom :=
      (MonoidHom.map_zpowers _ _).symm
    rw [hz, commV_map_congr, fixV_map_congr, h1]
    refine ⟨rfl, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective, h2]
  · have hA' : A.map (MulAut.congr e).symm.toMonoidHom ≤ autOn L (fsuUL T L I) := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 := hA ha
      rw [hG, Subgroup.mem_map_equiv] at h1
      exact h1
    have h1 := hE41 _ hA' (isElemAbelian2_map _ hAel)
    rwa [Subgroup.card_map_of_injective (MulAut.congr e).symm.injective] at h1

end CFSG.Quasithin.Vol2.Ch10.SecC

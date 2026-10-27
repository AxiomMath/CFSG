module

public import CFSG.Quasithin.Vol2.Ch3T326H
public import CFSG.Quasithin.Vol2.Ch3T326K
public import CFSG.Quasithin.Background.SmithD321Count
public import CFSG.Quasithin.Vol2.Ch3T326G

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative
open T325 (M_le_NVM)
open CFSG.Quasithin.Vol2.Ch10.SecA (conjugate_one)

section Abstract

variable {W : Type} [CommGroup W] [Finite W]

theorem d36c_label (hD36 : D36c) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) (hlt : V < orbSup T V) {t : MulAut W} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (ht2 : t * t ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hnt : ∃ g ∈ Mp, ∃ v ∈ V, g v ≠ v) :
    D36cConcl Mp T L V t ∨ D36cConcl Mp T L (V.map t.toMonoidHom) t := by
  rcases hD36 W M Mp T L V hD hlt t ht htn hMp with h | h
  · exact Or.inl h
  · right
    have hD' := SmithD321.d3Std_map hD ht
    have hcard : Nat.card ↥(V.map t.toMonoidHom) = Nat.card ↥V :=
      Subgroup.card_map_of_injective (f := t.toMonoidHom) t.injective
    have hlt' : V.map t.toMonoidHom < orbSup T (V.map t.toMonoidHom) := by
      rw [SmithD321.orbSup_map_of_mem ht]
      refine lt_of_le_of_ne (map_le_orbSup ht) fun he => hlt.ne ?_
      exact Subgroup.eq_of_le_of_card_ge (le_orbSup T V)
        (le_of_eq ((congrArg (fun H : Subgroup W => Nat.card ↥H) he).symm.trans hcard))
    rcases hD36 W M Mp T L _ hD' hlt' t ht htn hMp with h' | h'
    · exact h'
    · exfalso
      have hL1 := h.1
      have hL2 := h'.1
      rw [conjAutSub_inv_conjAutSub] at hL1 hL2
      have hLt : ∀ g ∈ conjAutSub t L, ∀ v ∈ V, g v = v := by
        intro g hg v hv
        rw [mem_conjAutSub_iff] at hg
        have hl : t * t * (t⁻¹ * g * t) * (t * t)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp ht2 _).mp hg
        have e : g = t⁻¹ * (t * t * (t⁻¹ * g * t) * (t * t)⁻¹) * t := by group
        have h1 := hL2 (t v) ⟨v, hv, rfl⟩ _ hl
        rw [e, MulAut.mul_apply, MulAut.mul_apply, h1]
        simp
      obtain ⟨g, hg, v, hv, hgv⟩ := hnt
      apply hgv
      have hle : Mp ≤ centSub V := by
        rw [hMp]
        exact sup_le (fun l hl => mem_centSub.mpr fun u hu => hL1 u hu l hl)
          (fun l hl => mem_centSub.mpr fun u hu => hLt l hl u hu)
      exact mem_centSub.mp (hle hg) v hv

end Abstract

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem exists_not_fix :
    ∃ g ∈ autOn (conjClosure L T)
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))),
      ∃ v ∈ V₀.subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))),
        g v ≠ v := by
  by_contra hcon
  push Not at hcon
  have hV₀VM := (T325.V₀_le_V T V₀).trans (T325.V_le_VM T (conjClosure L T) V₀)
  apply c.V₀_ne_bot
  rw [← c.comm_V₀, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := hcon _ (Setup.mem_autOn_iff.mpr ⟨⟨l, c.L₀_le_NVM hl⟩, hl, rfl⟩) ⟨v, hV₀VM hv⟩
    (Subgroup.mem_subgroupOf.mpr hv)
  have h2 : l * v * l⁻¹ = v := by
    have h3 := congrArg Subtype.val h1
    rwa [Setup.coe_conjAct_apply] at h3
  calc l * v = l * v * l⁻¹ * l := by group
    _ = v * l := by rw [h2]

theorem d36_label (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hD36 : D36c) [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hV₀ : V₀ ≠ conjClosure V₀ T)
    (hV : conjClosure V₀ T =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
    {s : G} (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    ∃ x ∈ T,
      D3Std (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) ∧
      D36cConcl
        (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (conjAct (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
          ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩) := by
  have hD := c.d3Std h316
  have hMp := c.autOn_L₀_eq hA37 hA38 hs hsn
  have htn := c.not_mem_normalizer hA37 hs hsn
  have horb := c.orbSup_eq
  have hnt := c.exists_not_fix
  have hV₀VM := (T325.V₀_le_V T V₀).trans (T325.V_le_VM T (conjClosure L T) V₀)
  have hss : s * s ∈ Subgroup.normalizer (L : Set G) :=
    Vol2.Ch10.SecA.mul_self_mem_normalizer_of_fsu hA37 hA38 c.fsu c.not_le_normalizer hs hsn
  have hlt : V₀.subgroupOf (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) <
      orbSup (autOn T (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))))
        (V₀.subgroupOf (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) := by
    rw [horb, Subgroup.subgroupOf_eq_top.mpr hV.ge]
    refine lt_of_le_of_ne le_top fun h => hV₀ ?_
    exact le_antisymm (T325.V₀_le_V T V₀) (hV.le.trans (Subgroup.subgroupOf_eq_top.mp h))
  have hsVM := c.T_le_NVM (T.inv_mem hs)
  have htT : conjAct (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ ∈
      autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :=
    Setup.mem_autOn_iff.mpr ⟨⟨s⁻¹, hsVM⟩, T.inv_mem hs, rfl⟩
  have ht2 : conjAct (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ *
      conjAct (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ ∈
      Subgroup.normalizer (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) : Set _) := by
    have hss' : s⁻¹ * s⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
      rw [← mul_inv_rev]
      exact Subgroup.inv_mem _ hss
    rw [← map_mul]
    exact H13.autOn_le_normalizer c.L_le_NVM inf_le_right inf_le_left
      (Setup.mem_autOn_iff.mpr ⟨⟨s⁻¹, hsVM⟩ * ⟨s⁻¹, hsVM⟩,
        ⟨hss', Subgroup.mul_mem _ hsVM hsVM⟩, rfl⟩)
  rcases d36c_label hD36 hD hlt htT htn hMp ht2 hnt with h | h
  · refine ⟨1, T.one_mem, ?_, ?_⟩ <;> rw [conjugate_one]
    · exact hD
    · exact h
  · have hmap : (V₀.subgroupOf (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))).map
          (conjAct (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))
            ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩).toMonoidHom =
        (CFSG.conjugate V₀ s).subgroupOf (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))) := by
      rw [map_conjAct_subgroupOf hV₀VM]
      show (CFSG.conjugate V₀ s⁻¹⁻¹).subgroupOf _ = _
      rw [inv_inv]
    refine ⟨s, hs, ?_, ?_⟩ <;> rw [← hmap]
    · exact SmithD321.d3Std_map hD htT
    · exact h

end Ctx

end CFSG.Quasithin.H13.T326

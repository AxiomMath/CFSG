module

public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch11SecA12Setup
public import CFSG.Quasithin.Vol2.Ch11SecA13Line2
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem lOf_ne_lOf (hF11 : Facts11) (hN : NatFacts) (hL3 : FactLineSL3) (hLp : FactLineSp4)
    (hLg : FactLineG2) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) : LOf L V₁ ≠ LOf L V₂ := by
  intro heq
  obtain ⟨v, hv, hvC⟩ : ∃ v ∈ V₁, v ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hcon
    have hle : V₁ ≤ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := fun v hv =>
      ⟨IsVi.le_fsuV hV₁ hv, by_contra fun h' => hcon ⟨v, hv, h'⟩⟩
    have h1 := IsVi.relIndex_eq hV₁
    rw [Subgroup.relIndex_eq_one.mpr hle] at h1
    have h2 : 1 < 2 ^ (n * 1) := Nat.one_lt_two_pow (by have := h.one_lt; omega)
    omega
  have hv2 : v ∈ V₂ := IsVi.mono₁₂ hN h1102 h hV₁ hV₂ hv
  refine hvC ((fixed_lOf_iff hL3 hLp hLg h1102 h hV₂ hv2).mp fun l hl => ?_)
  rw [← heq] at hl
  have hc : v * l = l * v :=
    Subgroup.mem_centralizer_iff.mp (lOf_one_le_centralizer hF11 h1102 h hV₁ hl) v hv
  rw [← hc, mul_inv_cancel_right]

theorem le_sup_lOf₁₂ (hPG : SecS.FactParabGen) (hF11 : Facts11) (hN : NatFacts)
    (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂) :
    L ≤ LOf L V₁ ⊔ LOf L V₂ ⊔ pCoreOf 2 L := by
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hSL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer h.normal)
  have hOL : pCoreOf 2 L ≤ T := (pCoreOf_two_le_of_isSylowTwoOf hSL).trans inf_le_left
  have hQs := isSolvable_pCoreOf_two L
  have hp₁ : ⁅LOf L V₁, LOf L V₁⁆ = LOf L V₁ := perfectCore_perfect _
  have hp₂ : ⁅LOf L V₂, LOf L V₂⁆ = LOf L V₂ := perfectCore_perfect _
  have hT₁ := T_le_normalizer_lOf h.normal (IsVi.le_normalizer hV₁)
  have hT₂ := T_le_normalizer_lOf h.normal (IsVi.le_normalizer hV₂)
  have hSL₁ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(modO2Image L (LOf L V₁)) ⧸ CFSG.pCore 2 ↥(modO2Image L (LOf L V₁)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inl rfl) hV₁
    obtain ⟨e₁⟩ := modO2Image_quotEquiv hL₁L
    exact ⟨F, inferInstance, inferInstance, hF.trans (by norm_num), ⟨e₁.symm.trans e⟩⟩
  have hSL₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(modO2Image L (LOf L V₂)) ⧸ CFSG.pCore 2 ↥(modO2Image L (LOf L V₂)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inr rfl) hV₂
    obtain ⟨e₁⟩ := modO2Image_quotEquiv hL₂L
    exact ⟨F, inferInstance, inferInstance, hF.trans (by norm_num), ⟨e₁.symm.trans e⟩⟩
  have hne : modO2Image L (LOf L V₁) ≠ modO2Image L (LOf L V₂) := by
    intro heq
    apply lOf_ne_lOf hF11 hN hL3 hLp hLg h1102 h hV₁ hV₂
    have h1 := sup_eq_of_modO2Image_eq hL₁L hL₂L heq
    rw [← perfectCore_sup_eq hp₁ hQs (hOL.trans hT₁), h1,
      perfectCore_sup_eq hp₂ hQs (hOL.trans hT₂)]
  have hgen := hPG _ h.shape _ (isSylowTwoOf_modO2Image hSL) _ _ hne
    (modO2Image_ne_bot hL₁L hp₁ (lOf_ne_bot hN h1102 h hV₁ (Or.inl rfl)))
    (modO2Image_ne_bot hL₂L hp₂ (lOf_ne_bot hN h1102 h hV₂ (Or.inr rfl)))
    (modO2Image_perfect hL₁L hp₁) (modO2Image_perfect hL₂L hp₂)
    (modO2Image_le_normalizer (inf_le_left.trans hT₁))
    (modO2Image_le_normalizer (inf_le_left.trans hT₂)) hSL₁ hSL₂
  have hsup : modO2Image L (LOf L V₁ ⊔ LOf L V₂) =
      modO2Image L (LOf L V₁) ⊔ modO2Image L (LOf L V₂) := by
    unfold modO2Image
    rw [Subgroup.subgroupOf_sup hL₁L hL₂L, Subgroup.map_sup]
  exact le_sup_of_modO2Image_eq_top (sup_le hL₁L hL₂L) (by rw [hsup, hgen])

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA

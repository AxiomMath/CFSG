module

public import CFSG.Quasithin.Vol2.Ch10SecC9U
public import CFSG.Quasithin.Vol2.Ch10SecC8Main4b
public import CFSG.Quasithin.Vol2.Ch10SecC9Comp
public import CFSG.Quasithin.Vol2.Ch10SecC9W

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique SecB.L32 L3F
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_act_eq_e0 : ∀ a : L3.Vec, a ≠ 0 → ∃ γ : L3.Γ, L3.act γ a = e0 := by
  decide +kernel

theorem centralizer_le_of_mem_fsuCVM_case3 (h1026 : Stmt10_2_6) (h1028 : Stmt10_2_8)
    (hyp : Hyp10 G T L I) (hL : LBarL32 L)
    (hne : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {x : G}
    (hx : x ∈ fsuCVM T L I) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ fsuM T L := by
  have hZT1 := (h1028 G T L I hyp hL hne).2.2.1
  have hxZ : x ∈ omegaOneCenterOf (T1 T L) := by
    rw [hZT1]
    exact ⟨fsuVM_le_omegaOneCenterOf hyp hx.1, hx.2⟩
  have hxT1 := (A4.omegaOneCenterOf_le_centerOf _ hxZ).2
  refine le_fsuM_of_le hyp h1026 (sup_le (mem_centralizer_iff_le.mp hx.2) fun s hs => ?_)
    (pCoreOf_centralizer_ne_bot hx1 ((SecA.isElemAbelian_fsuVM hyp).2 x hx.1))
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hxT1 s hs

theorem exists_conj_mem_U (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {U₂ : Subgroup G}
    (hU₂ : IsU10_2_8 T L I (CFSG.conjugate L t) U₂) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) :
    ∃ l ∈ CFSG.conjugate L t, l * v * l⁻¹ ∈ U₂ := by
  obtain ⟨hc1, hc2, D, D₂, hF1, hF2⟩ := exists_comp_data h37 h38 hyp h1011 h484 h3 hne ht htn
  obtain ⟨-, hKN, hTK, hD, hact, -⟩ := hF2
  have h0 : coordOf D₂ ⟨v, hv⟩ ≠ 0 := fun h0 => hvC (mem_fsuCVM_of_coord D₂ hKN hv h0).2
  obtain ⟨γ, hγ⟩ := exists_act_eq_e0 _ h0
  obtain ⟨⟨l, hlN⟩, hl, hlγ⟩ := SecB.mem_autOn_iff.mp (D₂.π γ).2
  have hlv : l * v * l⁻¹ ∈ Vi T L I (CFSG.conjugate L t) :=
    (Subgroup.mem_normalizer_iff.mp hlN v).mp hv
  have hc := coord_conj D₂ hlN hlγ hv hlv
  rw [hγ] at hc
  exact ⟨l, hl, (mem_U_iff D₂ hKN hD hTK hact hU₂ hlv).mpr (Or.inr hc)⟩

theorem thompsonJ_le_centralizer_of_mem_U (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h484 : ASInputs.AS_B_4_8_four) (h3210 : TmpL6_3_2_10_nine)
    (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {U₂ : Subgroup G}
    (hU₂ : IsU10_2_8 T L I (CFSG.conjugate L t) U₂) {u : G} (hu : u ∈ U₂)
    (huC : u ∉ Subgroup.centralizer (fsuL0 T L : Set G)) :
    thompsonJ T ≤ Subgroup.centralizer ({u} : Set G) := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2, -⟩ := hdec t ht htn
  have huW : u ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := hU₂.1 hu
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have huV : u ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) huW
  obtain ⟨U₁, hU₁⟩ := exists_isU hyp (commutator_le_left_of_le_normalizer hLN)
  obtain ⟨R₁, hR₁⟩ := exists_isR (T := T) (L := L) (I := I) L U₁
  obtain ⟨R₂, hR₂⟩ := exists_isR (T := T) (L := L) (I := I) (CFSG.conjugate L t) U₂
  have hRJ := R_sup_eq_thompsonJ_sup h37 h38 hyp h1011 h1012 h484 h3210 h3 hne ht htn hU₁ hU₂ hR₁
    hR₂
  have hCu := centralizer_v2_eq h37 h38 hyp h1011 h484 h3 hne ht htn hU₂ hR₂ hu huC
  have hR₁u : R₁ ≤ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    obtain ⟨hxN, hxP⟩ := (hR₁.2 x (hR₁.1 hx)).mp hx
    obtain ⟨⟨y, hyN⟩, hy, hyx⟩ := SecB.mem_autOn_iff.mp
      (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) _ hxP)
    have hyL : y ∈ L := centralizerSection_le_left _ _ _ hy
    have h1 : x * u * x⁻¹ = y * u * y⁻¹ := by
      have := congrArg (fun f : MulAut ↥(fsuVM T L I) => ((f ⟨u, huV⟩ : ↥(fsuVM T L I)) : G)) hyx
      exact this.symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : y * u * y⁻¹ = u := by
      rw [Subgroup.mem_centralizer_iff.mp (hV2 huW) y hyL, mul_inv_cancel_right]
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [h1, h2]
  have hQu : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤
      Subgroup.centralizer ({u} : Set G) := fun q hq => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hq.2 u huV).symm
  have hR₂u : R₂ ≤ Subgroup.centralizer ({u} : Set G) := by
    have : R₂ ≤ T ⊓ Subgroup.centralizer ({u} : Set G) := by
      rw [hCu]
      exact le_sup_right.trans le_sup_left
    exact this.trans inf_le_right
  calc thompsonJ T ≤ thompsonJ T ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) :=
        le_sup_left
    _ = R₁ ⊔ R₂ ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := hRJ.symm
    _ ≤ _ := sup_le (sup_le hR₁u hR₂u) hQu

theorem mem_U_of_thompsonJ_le (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h484 : ASInputs.AS_B_4_8_four) (h3210 : TmpL6_3_2_10_nine)
    (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {U₂ : Subgroup G}
    (hU₂ : IsU10_2_8 T L I (CFSG.conjugate L t) U₂) {w : G}
    (hw : w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hJ : thompsonJ T ≤ Subgroup.centralizer ({w} : Set G)) : w ∈ U₂ := by
  obtain ⟨hc1, hc2, D, D₂, hF1, hF2⟩ := exists_comp_data h37 h38 hyp h1011 h484 h3 hne ht htn
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, -, -, -⟩ := hdec t ht htn
  have hV21 : fsuVM T L I = Vi T L I (CFSG.conjugate L t) ⊔ Vi T L I L := by
    rw [hVeq, sup_comm]
  have hcap21 : Vi T L I (CFSG.conjugate L t) ⊓ Vi T L I L ≤ fsuCVM T L I := by
    rw [inf_comm]
    exact inf_V2_le_fsuCVM hyp h1011 ht htn
  obtain ⟨-, A₂, hA₂, hA₂W⟩ := exists_maxElemAbelian_not_le hyp h1011 h3210 hne ht htn
  have hfixw : ∀ γ, IsEa γ →
      ((D₂.π γ : ↥(autOn (CFSG.conjugate L t) (Vi T L I (CFSG.conjugate L t)))) :
        MulAut ↥(Vi T L I (CFSG.conjugate L t))) ⟨w, hw⟩ = ⟨w, hw⟩ := by
    intro γ hγ
    obtain ⟨a, haA, haN, haγ⟩ := exists_realize_ea hyp h1012 hF2 hF1 hV21 hcap21 hA₂ hA₂W hγ
    have haw : a * w * a⁻¹ = w := by
      have := Subgroup.mem_centralizer_singleton_iff.mp
        (hJ (le_thompsonJ_of_isMaxElemAbelian hA₂ haA.1))
      rw [this, mul_inv_cancel_right]
    rw [← haγ]
    exact Subtype.ext haw
  obtain ⟨-, hKN, hTK, hD, hact, hsq, hfix, -⟩ := hF2
  exact (mem_U_iff D₂ hKN hD hTK hact hU₂ hw).mpr ((fixes_ea_iff D₂ hsq hfix).mp hfixw)

end CFSG.Quasithin.Vol2.Ch10.SecC

module

public import CFSG.Quasithin.Background.C124YLBaum
public import CFSG.Quasithin.Background.C124YLPack
public import CFSG.Quasithin.Background.C124YLStab
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C124L2MP

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_autI {R : Subgroup G} {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hR : IsPGroup 2 R) : IsPGroup 2 ↥(autI hV R) := by
  intro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
  obtain ⟨k, hk⟩ := hR ⟨g, hg⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (g : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : convI hV (g ^ 2 ^ k) = 1 := (convI_eq_one_iff hV _).2 (by
    show ((g ^ 2 ^ k : Subgroup.normalizer (V : Set G)) : G) ∈ _
    rw [Subgroup.coe_pow, h1]
    exact Subgroup.one_mem _)
  simpa [map_pow] using h2

theorem two_elt_of_isPGroup {Γ : Type*} [Group Γ] {P : Subgroup Γ} (hP : IsPGroup 2 P) {x : Γ}
    (hx : x ∈ P) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem conjAut_conjAut {W : Type*} [CommGroup W] (a b : MulAut W) (K : Subgroup (MulAut W)) :
    B1.conjAut a (B1.conjAut b K) = B1.conjAut (a * b) K := by
  ext y
  rw [B1.mem_conjAut, B1.mem_conjAut, B1.mem_conjAut]
  have : b⁻¹ * (a⁻¹ * y * a) * b = (a * b)⁻¹ * y * (a * b) := by group
  rw [this]

theorem mem_normalizer_of_conjAut {W : Type*} [CommGroup W] {x : MulAut W}
    {K : Subgroup (MulAut W)} (h : B1.conjAut x K = K) :
    x ∈ Subgroup.normalizer (K : Set (MulAut W)) := by
  refine Subgroup.mem_normalizer_iff.2 fun k => ?_
  have h1 : x * k * x⁻¹ ∈ B1.conjAut x K ↔ k ∈ K := by
    rw [B1.mem_conjAut]
    simp [mul_assoc]
  rw [h] at h1
  exact h1.symm

theorem gen_of_class {W : Type*} [CommGroup W] {Xs Ls Y N : Subgroup (MulAut W)}
    (hLX : Ls ≤ Xs) (hY : Y ≤ Ls) (hgen : Ls = Y ⊔ (Ls ⊓ N))
    (hcl : ∀ x ∈ Xs, ∃ l ∈ Ls, l⁻¹ * x ∈ N) : Xs = Y ⊔ (Xs ⊓ N) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨l, hl, hn⟩ := hcl x hx
    have h1 : l ∈ Y ⊔ (Xs ⊓ N) := by
      have : l ∈ Y ⊔ (Ls ⊓ N) := hgen ▸ hl
      exact (sup_le_sup_left (inf_le_inf_right N hLX) Y) this
    have h2 : l⁻¹ * x ∈ Y ⊔ (Xs ⊓ N) :=
      le_sup_right (b := Xs ⊓ N) ⟨Xs.mul_mem (Xs.inv_mem (hLX hl)) hx, hn⟩
    have := (Y ⊔ (Xs ⊓ N)).mul_mem h1 h2
    simpa using this
  · exact sup_le (hY.trans hLX) inf_le_left

theorem starL2_of_package {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
    (E : Entry X T V L R m hV) {Pk P0 K0 Y0 : Subgroup (MulAut (IntMod V hV))}
    (hRPk : autI hV R ≤ Pk) (hPk : ∀ l ∈ autI hV L, ∀ x ∈ Pk, l⁻¹ * x * l ∈ Pk)
    (hP0 : IsSylowTwoOf P0 (autI hV L))
    (hK0 : ∀ B ≤ P0, WOff (commV (autI hV L)) (fixV (autI hV L) ⊓ commV (autI hV L)) B → B = K0)
    (hoff : ∀ B ∈ offenderImages hV R, B ≤ autI hV L)
    (hpkg : Package Pk (autI hV L) (commV (autI hV L)) (fixV (autI hV L) ⊓ commV (autI hV L))
      K0 Y0) :
    ∃ Ys, StarL2 X V L R hV Ys := by
  set Ls := autI hV L with hLs
  set U := commV Ls with hUdef
  set Z := fixV Ls ⊓ commV Ls with hZdef
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := E.red.2.1
  have hRX : R ≤ X := E.RT.trans E.sylow.1
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hXN
  have hVR : V ≤ R := (le_pCoreOf_of_reduced E.red).trans E.QR
  have hR2 : IsPGroup 2 ↥(autI hV R) := isPGroup_autI hV (E.sylow.2.1.to_le E.RT)
  have hnormX : ∀ x ∈ autI hV X, x ∈ Subgroup.normalizer (Ls : Set (MulAut (IntMod V hV))) :=
    fun x hx => L2.autI_le_normalizer_of_le_normalizer hV E.normal hx
  have hLX : Ls ≤ autI hV X := autI_mono hV (le_of_mem_cComp E.comp)
  have hstab : ∀ x ∈ autI hV X, (∀ u, u ∈ U ↔ x u ∈ U) ∧ (∀ z, z ∈ Z ↔ x z ∈ Z) :=
    fun x hx => sec_stable (hnormX x hx)
  have hstabL : ∀ l ∈ Ls, (∀ u, u ∈ U ↔ l u ∈ U) ∧ (∀ z, z ∈ Z ↔ l z ∈ Z) :=
    fun l hl => hstab l (hLX hl)
  have hwoff : ∀ B ∈ offenderImages hV R, WOff U Z B ∧
      Nat.card (IntMod V hV) ≤ Nat.card B * Nat.card (fixV B) ∧ B ≤ autI hV R := by
    intro B hB
    have h := offenderImages_isFFStarOffender hV hVR hRN hB
    have hW : Nat.card (IntMod V hV) ≤ Nat.card B * Nat.card (fixV B) := by
      have := h.2.2.2 ⊥ bot_le
      rwa [B1.card_bot_mul_card_fixV] at this
    exact ⟨⟨h.2.1, h.2.2.1, card_le_liftFix_of_offender U Z hW⟩, hW, h.1⟩
  obtain ⟨K1, hB1⟩ := (offenderImages_nonempty_iff_not_le hV).2 E.hJ
  obtain ⟨hw1, hW1, hB1R⟩ := hwoff K1 hB1
  have hB1L := hoff K1 hB1
  have hcl := fun {B : Subgroup (MulAut (IntMod V hV))} (hBL : B ≤ Ls) (hB : WOff U Z B) =>
    classify_of_sylow hP0 hK0 (fun l hl => (hstabL l hl).1) (fun l hl => (hstabL l hl).2) hBL hB
  obtain ⟨l, hl, hBl⟩ := hcl hB1L hw1
  have hpk : Package Pk Ls U Z K1 (B1.conjAut l Y0) := by
    rw [hBl]
    exact hpkg.conj hl (hstabL l hl).1 (hstabL l hl).2 (hPk l hl)
  have hrel : ∀ {B : Subgroup (MulAut (IntMod V hV))}, B ≤ Ls → WOff U Z B →
      ∃ l' ∈ Ls, B = B1.conjAut l' K1 := by
    intro B hBL hB
    obtain ⟨l2, hl2, hB2⟩ := hcl hBL hB
    refine ⟨l2 * l⁻¹, Ls.mul_mem hl2 (Ls.inv_mem hl), ?_⟩
    rw [hB2, hBl, conjAut_conjAut, inv_mul_cancel_right]
  have huniq : ∀ B ∈ offenderImages hV R, B = K1 := by
    intro B hB
    obtain ⟨hw, -, hBR⟩ := hwoff B hB
    exact unique_of_sylow hP0 hK0 (fun l hl => (hstabL l hl).1) (fun l hl => (hstabL l hl).2)
      (hoff B hB) hB1L hw hw1 (hR2.to_le (sup_le hBR hB1R))
  have hJ : autI hV (thompsonJ R) = K1 := by
    apply le_antisymm
    · rw [jst_eq_iSup hV hRN]
      refine iSup₂_le fun A hA => ?_
      rcases autI_eq_bot_or_mem hV hA with h | h
      · rw [h]
        exact bot_le
      · exact (huniq _ h).le
    · obtain ⟨A, hA, hAe⟩ := hB1
      rw [hAe, jst_eq_iSup hV hRN]
      exact le_iSup₂_of_le A hA.1 le_rfl
  have htight := inf_fixV_eq_liftFix U Z hW1 hpk.tight
  have hS : autI hV (baum R) = K1 := by
    apply le_antisymm
    · intro x hx
      have hxR : x ∈ autI hV R := baum_le_R hV R hx
      have hxN : x ∈ Subgroup.normalizer (K1 : Set (MulAut (IntMod V hV))) := by
        have := jst_normalizes hV hxR
        rw [hJ] at this
        exact mem_normalizer_of_conjAut this
      refine hpk.cent x (hRPk hxR) (two_elt_of_isPGroup hR2 hxR) hxN fun u hu => ?_
      have hu' : u ∈ U ⊓ fixV K1 := htight ▸ hu
      have hfix : u ∈ fixV (autI hV (thompsonJ R)) := by
        rw [hJ]
        exact hu'.2
      rw [fixes_of_baum hV hVR hRN hx hfix, mul_inv_cancel]
      exact Z.one_mem
    · rw [← hJ]
      exact jst_le_baum hV R
  refine ⟨B1.conjAut l Y0, ⟨⟨hpk.Y_le, ?_, ?_⟩, ?_, hpk.sl2⟩⟩
  · intro hle
    obtain ⟨u, hu, y, hy, hyu⟩ := hpk.moves
    have hu' : u ∈ U ⊓ fixV K1 := htight ▸ hu
    have hfix : u ∈ fixV (autI hV (thompsonJ R)) := by
      rw [hJ]
      exact hu'.2
    have := hle hfix y hy
    apply hyu
    rw [this, mul_inv_cancel]
    exact Z.one_mem
  · rw [hS]
    refine gen_of_class hLX hpk.Y_le hpk.gen fun x hx => ?_
    have hxL : B1.conjAut x K1 ≤ Ls := by
      intro y hy
      have h1 : x⁻¹ * y * x ∈ Ls := hB1L (B1.mem_conjAut.1 hy)
      have h2 := (Subgroup.mem_normalizer_iff.1 (hnormX x hx) _).1 h1
      simpa [mul_assoc] using h2
    obtain ⟨l', hl', hl'e⟩ := hrel hxL (hw1.conj x (hstab x hx).1 (hstab x hx).2)
    refine ⟨l', hl', mem_normalizer_of_conjAut ?_⟩
    rw [← conjAut_conjAut, hl'e]
    exact B1.conjAut_inv_conjAut l' K1
  · rw [hS]
    exact hpk.sylow

end CFSG.Quasithin.C124.YL

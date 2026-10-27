module

public import CFSG.RankThree.FFModules.ChiefFactors
public import CFSG.Quasithin.H13.L32AC44c
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Bridge

public section

namespace CFSG.RankThree.FFModules

open scoped MatrixGroups
open Matrix Module
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

section Basic

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def repGL (ρ : Representation (ZMod 2) G W) : G →* (W ≃ₗ[ZMod 2] W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp ρ.asGroupHom

theorem repGL_apply (ρ : Representation (ZMod 2) G W) (g : G) (w : W) : repGL ρ g w = ρ g w :=
  rfl

theorem rep_inv_apply (ρ : Representation (ZMod 2) G W) (g : G) (w : W) :
    ρ g⁻¹ (ρ g w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem rep_apply_inv (ρ : Representation (ZMod 2) G W) (g : G) (w : W) :
    ρ g (ρ g⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem isElementaryAbelian_two_of_le {A B : Subgroup G} [hB : CFSG.IsElementaryAbelian 2 ↥B]
    (h : A ≤ B) : CFSG.IsElementaryAbelian 2 ↥A where
  is_comm := ⟨fun x y => by
    have h1 : ((⟨x.1, h x.2⟩ : ↥B) * ⟨y.1, h y.2⟩ : ↥B) = ⟨y.1, h y.2⟩ * ⟨x.1, h x.2⟩ :=
      hB.toIsMulCommutative.is_comm.comm _ _
    have h2 : (x.1 * y.1 : G) = y.1 * x.1 := congrArg (Subtype.val : ↥B → G) h1
    exact Subtype.ext h2⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => by
    apply Subtype.ext
    simpa using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) x.1 (h x.2)

end Basic

section Kernel

variable {F : Type} [Field F] [Finite F] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem ker_le_scalars (ρ : Representation (ZMod 2) SL(3, F) W) (hnt : ∃ g, ρ g ≠ 1) :
    ∀ x : SL(3, F), ρ x = 1 →
      x ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F := by
  intro x hx
  have hq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hle := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple (φ := ρ.asGroupHom) hq
    (by
      obtain ⟨g, hg⟩ := hnt
      refine ⟨g, fun h => hg ?_⟩
      have := congrArg (fun u : (W →ₗ[ZMod 2] W)ˣ => (u : W →ₗ[ZMod 2] W)) h
      simpa [Representation.asGroupHom_apply] using this)
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
  apply hle
  rw [MonoidHom.mem_ker]
  exact Units.ext (by simpa [Representation.asGroupHom_apply] using hx)

theorem eq_one_of_ker {ρ : Representation (ZMod 2) SL(3, F) W} (hnt : ∃ g, ρ g ≠ 1)
    {g : SL(3, F)} (hg2 : g * g = 1) (hg : ρ g = 1) : g = 1 := by
  have hs := ker_le_scalars ρ hnt g hg
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center] at hs
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs
  rw [Fintype.card_fin] at hr
  have h3 : g ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrg, ← map_pow, hr, map_one]
    rfl
  calc g = g * (g * g) := by rw [hg2, mul_one]
    _ = g ^ 3 := (pow_three g).symm
    _ = 1 := h3

end Kernel

theorem ffClassificationSL3_of_card {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) : FFClassificationSL3.{0, 0} F := by
  classical
  intro W _ _ _ ρ hirr hnt B hBea hB1 hB
  have hNat : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  haveI hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hNat
  have hker := ker_le_scalars ρ hnt
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [← pow_two]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc => by
    have := hBea.toIsMulCommutative.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩
    exact congrArg Subtype.val this
  obtain ⟨k, hk⟩ : ∃ k, Nat.card B = 2 ^ k :=
    (IsPGroup.iff_card (p := 2)).mp (CFSG.IsElementaryAbelian.isPGroup 2 B)
  have hBoff : IsOffender ρ B := by
    refine (isOffender_iff_finrank hk).mpr ?_
    rw [hk, Nat.log_pow (by norm_num)] at hB
    exact hB
  obtain ⟨A, hAB, hA1, hAbest⟩ := exists_isBestOffender hBoff hB1
  have hAon : IsBestOffenderOn ρ A ⊤ := by
    refine ⟨fun a ha b hb => ⟨fun u _ => ?_, fun u _ => ?_⟩, fun B' hB' => ?_⟩
    · have : a * b * a⁻¹ * b⁻¹ = 1 := by
        rw [hBc a (hAB ha) b (hAB hb)]; group
      rw [this, map_one]; rfl
    · rw [hB2 a (hAB ha), map_one]; rfl
    · have := hAbest B' hB'
      simpa [fixOn] using this
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := timmesfeld_replacement ρ A hAon
  set A' : Subgroup SL(3, F) := cenOn ρ A (commOn ρ A ⊤) with hA'
  have hA'A : A' ≤ A := cenOn_le ρ A _
  have hcomm : commOn ρ A ⊤ ≠ ⊥ := by
    intro h
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    apply ha1
    apply Subtype.ext
    refine eq_one_of_ker hnt (hB2 a (hAB ha)) ?_
    exact LinearMap.ext fun u => commOn_eq_bot_iff.mp h a ha u Submodule.mem_top
  have hA'1 : A' ≠ ⊥ := by
    intro h
    apply h5 hcomm
    rw [commOn_eq_bot_iff]
    intro a ha u _
    have : a = 1 := by rw [h] at ha; exact Subgroup.mem_bot.mp ha
    rw [this, map_one]; rfl
  have hA'B : A' ≤ B := hA'A.trans hAB
  haveI hA'ea : CFSG.IsElementaryAbelian 2 ↥A' := isElementaryAbelian_two_of_le hA'B
  set Ā : Subgroup (W ≃ₗ[ZMod 2] W) := A'.map (repGL ρ) with hĀ
  haveI : CFSG.IsElementaryAbelian 2 ↥Ā := CFSG.IsElementaryAbelian.map (repGL ρ)
  have hinj : Function.Injective ((repGL ρ).domRestrict A') := by
    intro x y hxy
    have hxy' : repGL ρ (x : SL(3, F)) = repGL ρ (y : SL(3, F)) := hxy
    apply Subtype.ext
    have hxyB : (x : SL(3, F)) * (y : SL(3, F))⁻¹ ∈ B := B.mul_mem (hA'B x.2) (B.inv_mem (hA'B y.2))
    have hsq : ((x : SL(3, F)) * (y : SL(3, F))⁻¹) * ((x : SL(3, F)) * (y : SL(3, F))⁻¹) = 1 :=
      hB2 _ hxyB
    have hρ1 : ρ ((x : SL(3, F)) * (y : SL(3, F))⁻¹) = 1 := by
      refine LinearMap.ext fun u => ?_
      rw [map_mul, Module.End.mul_apply]
      have := congrArg (fun e : W ≃ₗ[ZMod 2] W => e (ρ (y : SL(3, F))⁻¹ u)) hxy'
      simp only [repGL_apply] at this
      rw [this, rep_apply_inv]
      rfl
    have := eq_one_of_ker hnt hsq hρ1
    exact mul_inv_eq_one.mp this
  have hcard : Nat.card ↥Ā = Nat.card ↥A' := by
    have hr : ((repGL ρ).domRestrict A').range = Ā := MonoidHom.domRestrict_range _ _
    rw [← hr]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hĀ1 : Ā ≠ ⊥ := by
    intro h
    apply hA'1
    rw [eq_bot_iff]
    intro g hg
    have : repGL ρ g ∈ Ā := ⟨g, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    have hρ : ρ g = 1 := LinearMap.ext fun u => by
      have := congrArg (fun e : W ≃ₗ[ZMod 2] W => e u) this
      simpa [repGL_apply] using this
    rw [Subgroup.mem_bot]
    exact eq_one_of_ker hnt (hB2 g (hA'B hg)) hρ
  have hAint : ∀ a ∈ Ā, ∀ x : SL(3, F),
      ∃ y, CFSG.QuasithinUnique.Setup.X7a.Intertwines ρ a x y := by
    rintro _ ⟨g, hg, rfl⟩ x
    refine ⟨g * x * g⁻¹, fun u => ?_⟩
    simp only [repGL_apply, map_mul, Module.End.mul_apply, rep_inv_apply]
  have hquad : ∀ a ∈ Ā, ∀ b ∈ Ā, ∀ w, b (a w - w) = a w - w := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ w
    have hmem : ρ g w - w ∈ commOn ρ A' ⊤ := Replacement.mem_commOn_of hg Submodule.mem_top
    have := h6 h (hA'A hh) _ hmem
    simpa [repGL_apply] using this
  have hoff : Nat.card W ≤ Nat.card ↥Ā * Nat.card {u : W // ∀ a ∈ Ā, a u = u} := by
    have hb := h4.2 ⊥ bot_le
    have hfix : Nat.card (fixOn ρ A' ⊤) = Nat.card {u : W // ∀ a ∈ Ā, a u = u} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
      simp only [mem_fixOn, Submodule.mem_top, true_and, hĀ, Subgroup.mem_map]
      constructor
      · rintro hu _ ⟨g, hg, rfl⟩
        exact hu g hg
      · intro hu g hg
        exact hu _ ⟨g, hg, rfl⟩
    rw [hcard, ← hfix]
    simpa [fixOn, fixSub_bot, Subgroup.card_bot, card_top_submodule] using hb
  obtain ⟨ψ, hψ, E, hE⟩ := CFSG.Quasithin.H13.L32A.C.SL3N.natural_of_offender' ρ hker Ā hAint hn hF
    hirr hĀ1 hquad hoff
  rcases hψ with rfl | rfl
  · left
    exact ⟨E, fun g w => by simpa using hE g w⟩
  · right
    refine ⟨E, fun g w => ?_⟩
    rw [hE g w]
    rfl

end CFSG.RankThree.FFModules

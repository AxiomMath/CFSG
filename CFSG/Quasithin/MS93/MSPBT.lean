module

public import CFSG.Quasithin.MS93.MSPRad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Open CFSG.LieType
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

theorem two_dvd_card [Finite F] [CharP F 2] : 2 ∣ Nat.card F := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact (CharP.cast_eq_zero_iff F 2 _).1 (FiniteField.cast_card_eq_zero F)

theorem exists_fixed_ne_zero [Finite F] [CharP F 2] {R : Subgroup (Sp4 F)} (hR : IsPGroup 2 R)
    {W : Submodule F (V4 F)} (hW : W ≠ ⊥) (hinv : ∀ r ∈ R, ∀ w ∈ W, mat r *ᵥ w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ r ∈ R, mat r *ᵥ w = w := by
  let _ : MulAction R W :=
    { smul := fun r w => ⟨mat r *ᵥ w, hinv r r.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        change mat ((1 : R) : Sp4 F) *ᵥ (w : V4 F) = (w : V4 F)
        rw [Subgroup.coe_one, mat_one, one_mulVec])
      mul_smul := fun r s w => Subtype.ext (mat_mul_mulVec (r : Sp4 F) s w) }
  have hmod := hR.card_modEq_card_fixedPoints (p := 2) W
  have hW2 : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    have hpos : 0 < Module.finrank F W :=
      Nat.pos_of_ne_zero fun h => hW (Submodule.finrank_eq_zero.1 h)
    exact (two_dvd_card (F := F)).pow hpos.ne'
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints R W) :=
    (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hW2)))
  have h0 : (0 : W) ∈ MulAction.fixedPoints R W := fun r => Subtype.ext (by
    change mat (r : Sp4 F) *ᵥ (0 : V4 F) = 0
    exact mulVec_zero _)
  by_contra hcon
  push Not at hcon
  have hsub : ∀ w ∈ MulAction.fixedPoints R W, w = 0 := by
    intro w hw
    refine Subtype.ext ?_
    by_contra hne
    obtain ⟨r, hr, hrw⟩ := hcon w w.2 hne
    exact hrw (congrArg Subtype.val (hw ⟨r, hr⟩))
  have hcard : Nat.card (MulAction.fixedPoints R W) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((hsub a a.2).trans (hsub b b.2).symm)⟩, ⟨⟨0, h0⟩⟩⟩
  omega

theorem normalizer_le_stab_fixSp (R : Subgroup (Sp4 F)) :
    Subgroup.normalizer (R : Set (Sp4 F)) ≤ stab (fixSp R) := fun g hg => by
  rw [mem_stab_iff, ← fixSp_map_conj, (mem_normalizer_iff_map_conj.1 hg)]

theorem fixSp_eq_top_iff {R : Subgroup (Sp4 F)} : fixSp R = ⊤ ↔ R = ⊥ := by
  constructor
  · intro h
    refine eq_bot_iff.2 fun r hr => Subgroup.mem_bot.2 (ext_mulVec fun v => ?_)
    rw [mat_one, one_mulVec]
    exact (h ▸ Submodule.mem_top : v ∈ fixSp R) r hr
  · rintro rfl
    refine eq_top_iff.2 fun v _ r hr => ?_
    rw [Subgroup.mem_bot.1 hr, mat_one, one_mulVec]

theorem fixSp_sylS : fixSp (sylS F) = pt₀ F := by
  ext v
  have h := (SymplecticHigher.unitriangular_invariant_isotropic_subspaces (r := 2)
    (K := F)).1
  rw [Set.ext_iff] at h
  exact h v

theorem pt₀_le_of_sylS_inv [Finite F] [CharP F 2] {W : Submodule F (V4 F)} (hW : W ≠ ⊥)
    (hinv : ∀ s ∈ sylS F, ∀ w ∈ W, mat s *ᵥ w ∈ W) : pt₀ F ≤ W := by
  obtain ⟨w, hw, hw0, hfix⟩ := exists_fixed_ne_zero isPGroup_sylS hW hinv
  have hw' : w ∈ pt₀ F := fixSp_sylS (F := F) ▸ (mem_fixSp.2 hfix)
  rw [pt₀_eq_span] at hw' ⊢
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw'
  have ha : a ≠ 0 := fun h => hw0 (by rw [h, zero_smul])
  rw [Submodule.span_singleton_le_iff_mem]
  have := W.smul_mem a⁻¹ hw
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this

theorem stab_inf_le_stab_inf (W W' : Submodule F (V4 F)) : stab W ⊓ stab W' ≤ stab (W ⊓ W') :=
  fun _ hg => mem_stab_of_le fun _ hv =>
    ⟨mulVec_mem_of_mem_stab hg.1 hv.1, mulVec_mem_of_mem_stab hg.2 hv.2⟩

theorem eq_pt₀_of_le {D : Submodule F (V4 F)} (hD : D ≤ pt₀ F) (hD0 : D ≠ ⊥) : D = pt₀ F := by
  refine Submodule.eq_of_le_of_finrank_le hD ?_
  rw [isPoint_pt₀]
  exact Nat.pos_of_ne_zero fun h => hD0 (Submodule.finrank_eq_zero.1 h)

theorem eq_pt₀_of_ge {D : Submodule F (V4 F)} (hD : pt₀ F ≤ D) (h1 : Module.finrank F D ≤ 1) :
    D = pt₀ F :=
  (Submodule.eq_of_le_of_finrank_le hD (by rw [isPoint_pt₀]; exact h1)).symm

theorem sub_mem_pt₀_of_mem_sylS {s : Sp4 F} (hs : s ∈ sylS F) {v : V4 F} (hv : v ∈ ln₀ F) :
    mat s *ᵥ v - v ∈ pt₀ F := by
  obtain ⟨a, C, -, hsC⟩ := exists_of_mem_sylS hs
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  obtain ⟨-, e1, e2, e3⟩ := mulVec_blockMat_unitri a C v
  refine mem_pt₀.2 ⟨?_, ?_, ?_⟩ <;> rw [Pi.sub_apply, hsC]
  · rw [e1, h0, h1]
    ring
  · rw [e2, sub_self]
  · rw [e3, h0, h1]
    ring

variable [Finite F] [CharP F 2]

theorem pCoreOf_le_sylS {Y : Subgroup (Sp4 F)} (hY : sylS F ≤ Y) : pCoreOf 2 Y ≤ sylS F := by
  obtain ⟨T, hT⟩ := exists_sylow_sylS (F := F)
  have : (CFSG.Open.pCore 2 Y).Normal := BorelTits.pCore_normal (G := Y) 2
  have h := (BorelTits.pCore_isPGroup (G := Y) 2).le_sylow_of_normal (T.subtype (hT ▸ hY))
  rw [Sylow.coe_subtype] at h
  have h' := Subgroup.map_mono (f := Y.subtype) h
  rw [Subgroup.subgroupOf_map_subtype, hT] at h'
  exact h'.trans inf_le_left

theorem le_P₁_or_le_P₂_of_stab {Y : Subgroup (Sp4 F)} (hY : sylS F ≤ Y)
    {W : Submodule F (V4 F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) (hYW : Y ≤ stab W) :
    Y ≤ P₁ F ∨ Y ≤ P₂ F := by
  have hSinv : ∀ W' : Submodule F (V4 F), Y ≤ stab W' →
      ∀ s ∈ sylS F, ∀ w ∈ W', mat s *ᵥ w ∈ W' :=
    fun W' h s hs w hw => mulVec_mem_of_mem_stab (h (hY hs)) hw
  have hpt : pt₀ F ≤ W := pt₀_le_of_sylS_inv hW0 (hSinv W hYW)
  have hYp : Y ≤ stab (perp W) := hYW.trans (stab_le_stab_perp W)
  have h4 := finrank_perp W
  have hWlt : Module.finrank F W < 4 := by
    have := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.2 hWt)
    simpa using this
  have hWpos : 0 < Module.finrank F W := Nat.pos_of_ne_zero fun h =>
    hW0 (Submodule.finrank_eq_zero.1 h)
  have hpW : perp W ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at h4
    omega
  have hpt' : pt₀ F ≤ perp W := pt₀_le_of_sylS_inv hpW (hSinv _ hYp)
  by_cases h1 : Module.finrank F W ≤ 1
  · right
    have h := eq_pt₀_of_ge hpt h1
    rw [h] at hYW
    exact hYW
  by_cases h3 : 3 ≤ Module.finrank F W
  · right
    have h := eq_pt₀_of_ge hpt' (by omega)
    rw [h] at hYp
    exact hYp
  have hYD : Y ≤ stab (W ⊓ perp W) := le_inf hYW hYp |>.trans (stab_inf_le_stab_inf _ _)
  by_cases hti : W ≤ perp W
  · left
    have hiso : IsTotallyIsotropic (form F) W := fun x hx y hy => mem_perp.1 (hti hy) x hx
    obtain ⟨d, hd, hWd⟩ := ((SymplecticHigher.unitriangular_invariant_isotropic_subspaces
      (r := 2) (K := F)).2.1 W).1 ⟨hiso, hSinv W hYW⟩
    have hfd : Module.finrank F W = d := by
      rw [hWd]
      exact (SymplecticHigher.unitriangular_invariant_isotropic_subspaces (r := 2)
        (K := F)).2.2.1.1 d hd
    have hd2 : d = 2 := by omega
    rw [hWd, hd2] at hYW
    exact hYW
  · right
    have hlt : W ⊓ perp W < W := lt_of_le_of_ne inf_le_left fun h => hti (calc
      W = W ⊓ perp W := h.symm
      _ ≤ perp W := inf_le_right)
    have := Submodule.finrank_lt_finrank_of_lt hlt
    have h := eq_pt₀_of_ge (le_inf hpt hpt') (by omega)
    rw [h] at hYD
    exact hYD

theorem le_P₁_or_le_P₂ {Y : Subgroup (Sp4 F)} (hY : sylS F ≤ Y) (hR : pCoreOf 2 Y ≠ ⊥) :
    Y ≤ P₁ F ∨ Y ≤ P₂ F := by
  have hRp := BorelTits.pCoreOf_isPGroup 2 Y
  refine le_P₁_or_le_P₂_of_stab hY (W := fixSp (pCoreOf 2 Y)) ?_ ?_ ?_
  · intro h
    obtain ⟨w, -, hw0, hw⟩ := exists_fixed_ne_zero hRp (W := ⊤) top_ne_bot
      fun _ _ _ _ => Submodule.mem_top
    exact hw0 (by rw [← Submodule.mem_bot F, ← h]; exact hw)
  · rwa [Ne, fixSp_eq_top_iff]
  · exact (BorelTits.le_normalizer_pCoreOf 2 Y).trans (normalizer_le_stab_fixSp _)

theorem Q₁_le_pCoreOf {Y : Subgroup (Sp4 F)} (hY : sylS F ≤ Y) (hY1 : Y ≤ P₁ F) :
    Q₁ F ≤ pCoreOf 2 Y :=
  BorelTits.le_pCoreOf_of_le_normalizer 2 (Q₁_le_sylS.trans hY) (hY1.trans P₁_le_normalizer_Q₁)
    (isPGroup_sylS.to_le Q₁_le_sylS)

theorem Q₂_le_pCoreOf {Y : Subgroup (Sp4 F)} (hY : sylS F ≤ Y) (hY2 : Y ≤ P₂ F) :
    Q₂ F ≤ pCoreOf 2 Y :=
  BorelTits.le_pCoreOf_of_le_normalizer 2 (Q₂_le_sylS.trans hY) (hY2.trans P₂_le_normalizer_Q₂)
    (isPGroup_sylS.to_le Q₂_le_sylS)

theorem le_borel_of_le_P₁ {Y : Subgroup (Sp4 F)} (hY : sylS F ≤ Y) (hY1 : Y ≤ P₁ F)
    (hR : pCoreOf 2 Y ≠ Q₁ F) : Y ≤ borel F := by
  set R := pCoreOf 2 Y with hRdef
  obtain ⟨r, hrR, hrQ⟩ : ∃ r ∈ R, r ∉ Q₁ F := by
    by_contra h
    push Not at h
    exact hR (le_antisymm h (Q₁_le_pCoreOf hY hY1))
  obtain ⟨a, C, hC, hrC⟩ := exists_of_mem_sylS (pCoreOf_le_sylS hY hrR)
  have ha : a ≠ 0 := by
    rintro rfl
    have hr : r = tau hC := mat_injective (hrC.trans (mat_tau hC).symm)
    exact hrQ (hr ▸ tau_mem_Q₁ hC)
  have hD : ln₀ F ⊓ fixSp R = pt₀ F := by
    refine eq_pt₀_of_le (fun v hv => ?_) ?_
    · obtain ⟨h0, h1⟩ := mem_ln₀.1 hv.1
      have hfix := congrFun (hv.2 r hrR) (.inl 0)
      rw [hrC, (mulVec_blockMat_unitri a C v).1, h0, h1] at hfix
      have hv1 : v (.inl 1) = 0 := by
        have : a * v (.inl 1) = 0 := by linear_combination hfix
        exact (mul_eq_zero.1 this).resolve_left ha
      exact mem_pt₀.2 ⟨hv1, h0, h1⟩
    · intro h
      obtain ⟨w, hw, hw0, hwfix⟩ := exists_fixed_ne_zero (BorelTits.pCoreOf_isPGroup 2 Y)
        (W := ln₀ F) (fun h' => by
          have := (isLine_ln₀ (F := F)).1
          rw [h', finrank_bot] at this
          omega)
        fun s hs w hw => mulVec_mem_of_mem_stab (sylS_le_P₁ (pCoreOf_le_sylS hY hs)) hw
      exact hw0 (by rw [← Submodule.mem_bot F, ← h]; exact ⟨hw, hwfix⟩)
  have hY2 : Y ≤ P₂ F := by
    have h := le_inf hY1 ((BorelTits.le_normalizer_pCoreOf 2 Y).trans
      (normalizer_le_stab_fixSp _)) |>.trans (stab_inf_le_stab_inf _ _)
    rw [hD] at h
    exact h
  rw [borel_eq_inf]
  exact le_inf hY1 hY2

theorem le_borel_of_le_P₂ {Y : Subgroup (Sp4 F)} (hY : sylS F ≤ Y) (hY2 : Y ≤ P₂ F)
    (hR : pCoreOf 2 Y ≠ Q₂ F) : Y ≤ borel F := by
  set R := pCoreOf 2 Y with hRdef
  obtain ⟨r, hrR, hrQ⟩ : ∃ r ∈ R, r ∉ Q₂ F := by
    by_contra h
    push Not at h
    exact hR (le_antisymm h (Q₂_le_pCoreOf hY hY2))
  have hrS := pCoreOf_le_sylS hY hrR
  obtain ⟨a, C, hC, hrC⟩ := exists_of_mem_sylS hrS
  have hC11 : C 1 1 ≠ 0 := fun h => hrQ (mem_Q₂_iff.2 ⟨hrS, by rw [entry_of_mem_sylS hrC, h]⟩)
  have hchar : ∀ u : V4 F, u ∈ perp (pt₀ F) → mat r *ᵥ u - u ∈ pt₀ F → u ∈ ln₀ F := by
    intro u hu hru
    have h0 := mem_perp_pt₀.1 hu
    have h1 := (mem_pt₀.1 hru).1
    rw [Pi.sub_apply, hrC, (mulVec_blockMat_unitri a C u).2.1, h0] at h1
    have : C 1 1 * u (.inr 1) = 0 := by linear_combination h1
    exact mem_ln₀.2 ⟨h0, (mul_eq_zero.1 this).resolve_left hC11⟩
  have hY1 : Y ≤ P₁ F := by
    intro y hy
    refine mem_stab_of_le fun v hv => hchar _ ?_ ?_
    · exact mulVec_mem_of_mem_stab (stab_le_stab_perp _ (hY2 hy)) (ln₀_le_perp_pt₀ hv)
    · have hr' : y⁻¹ * r * y ∈ R := by
        have := (Subgroup.mem_normalizer_iff.1 (BorelTits.le_normalizer_pCoreOf 2 Y
          (inv_mem hy)) r).1 hrR
        simpa [mul_assoc] using this
      have h1 := sub_mem_pt₀_of_mem_sylS (pCoreOf_le_sylS hY hr') hv
      have h2 := mulVec_mem_of_mem_stab (hY2 hy) h1
      rw [mulVec_sub, mat_mul_mulVec, mat_mul_mulVec, mat_mulVec_inv] at h2
      convert h2 using 2
  rw [borel_eq_inf]
  exact le_inf hY1 hY2

omit [Finite F] [CharP F 2] in
theorem borel_le_normalizer_sylS : borel F ≤ Subgroup.normalizer (sylS F : Set (Sp4 F)) :=
  normalizer_sylS.ge

theorem pCoreOf_of_sylS_le {Y : Subgroup (Sp4 F)} (hY : sylS F ≤ Y) :
    (Y ≤ borel F ∧ pCoreOf 2 Y = sylS F) ∨ (Y ≤ P₁ F ∧ ¬ Y ≤ borel F ∧ pCoreOf 2 Y = Q₁ F) ∨
      (Y ≤ P₂ F ∧ ¬ Y ≤ borel F ∧ pCoreOf 2 Y = Q₂ F) ∨
      (¬ Y ≤ P₁ F ∧ ¬ Y ≤ P₂ F ∧ pCoreOf 2 Y = ⊥) := by
  by_cases hB : Y ≤ borel F
  · refine Or.inl ⟨hB, le_antisymm (pCoreOf_le_sylS hY) ?_⟩
    exact BorelTits.le_pCoreOf_of_le_normalizer 2 hY (hB.trans borel_le_normalizer_sylS)
      isPGroup_sylS
  by_cases h1 : Y ≤ P₁ F
  · exact Or.inr (Or.inl ⟨h1, hB, by_contra fun h => hB (le_borel_of_le_P₁ hY h1 h)⟩)
  by_cases h2 : Y ≤ P₂ F
  · exact Or.inr (Or.inr (Or.inl ⟨h2, hB, by_contra fun h => hB (le_borel_of_le_P₂ hY h2 h)⟩))
  refine Or.inr (Or.inr (Or.inr ⟨h1, h2, by_contra fun h => ?_⟩))
  rcases le_P₁_or_le_P₂ hY h with h' | h'
  exacts [h1 h', h2 h']

theorem pCoreOf_of_sylow_le {Y : Subgroup (Sp4 F)} (T : Sylow 2 (Sp4 F))
    (hT : (T : Subgroup (Sp4 F)) ≤ Y) :
    ∃ g : Sp4 F, (sylS F).map (MulAut.conj g).toMonoidHom = T ∧
      (pCoreOf 2 Y = (sylS F).map (MulAut.conj g).toMonoidHom ∨
        pCoreOf 2 Y = (Q₁ F).map (MulAut.conj g).toMonoidHom ∨
        pCoreOf 2 Y = (Q₂ F).map (MulAut.conj g).toMonoidHom ∨ pCoreOf 2 Y = ⊥) := by
  obtain ⟨S₀, hS₀⟩ := exists_sylow_sylS (F := F)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp4 F) S₀ T
  have hgT : (sylS F).map (MulAut.conj g).toMonoidHom = T := by
    rw [← hg, ← hS₀]
    rfl
  refine ⟨g, hgT, ?_⟩
  set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'
  have hSY' : sylS F ≤ Y' := by
    intro s hs
    rw [hY', mem_map_conj, inv_inv]
    exact hT (hgT ▸ Subgroup.mem_map_of_mem _ hs)
  have hYY : Y = Y'.map (MulAut.conj g).toMonoidHom := by
    rw [hY', map_conj_map_conj, mul_inv_cancel]
    ext x
    simp
  have hcore : pCoreOf 2 Y = (pCoreOf 2 Y').map (MulAut.conj g).toMonoidHom := by
    rw [hYY, BorelTits.pCoreOf_map_mulEquiv]
  rw [hcore]
  rcases pCoreOf_of_sylS_le hSY' with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Subgroup.map_bot _)))

omit [Finite F] [CharP F 2] in
theorem transv_f₁_not_mem_P₂ : transv (f₁ F) 1 ∉ P₂ F := by
  intro h
  have he : e₁ F ∈ pt₀ F := by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _
  have := (mem_pt₀.1 (mulVec_mem_of_mem_stab h he)).2.1
  rw [transv_mulVec, form_apply] at this
  simp at this

omit [Finite F] [CharP F 2] in
theorem transv_f₁_not_mem_P₁ : transv (f₁ F) 1 ∉ P₁ F := by
  intro h
  have he : e₁ F ∈ ln₀ F :=
    pt₀_le_ln₀ (by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _)
  have := (mem_ln₀.1 (mulVec_mem_of_mem_stab h he)).1
  rw [transv_mulVec, form_apply] at this
  simp at this

theorem pCoreOf_top : pCoreOf 2 (⊤ : Subgroup (Sp4 F)) = ⊥ := by
  rcases pCoreOf_of_sylS_le (le_top : sylS F ≤ ⊤) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩
  · exact absurd (borel_le_P₁ (h (Subgroup.mem_top (transv (f₁ F) 1)))) transv_f₁_not_mem_P₁
  · exact absurd (h (Subgroup.mem_top (transv (f₁ F) 1))) transv_f₁_not_mem_P₁
  · exact absurd (h (Subgroup.mem_top (transv (f₁ F) 1))) transv_f₁_not_mem_P₂
  · exact h

omit [Finite F] [CharP F 2] in
theorem overgroups_borel {Y : Subgroup (Sp4 F)} (hB : borel F ≤ Y) :
    Y = borel F ∨ Y = P₁ F ∨ Y = P₂ F ∨ Y = ⊤ := by
  by_cases ht : Y = ⊤
  · exact Or.inr (Or.inr (Or.inr ht))
  have hP₂ : CFSG.QuasithinUnique.Setup.X7a.Q2 F 0 = P₂ F := rfl
  have hP₁ : CFSG.QuasithinUnique.Setup.X7a.Q2 F 1 = P₁ F := rfl
  rcases CFSG.QuasithinUnique.Setup.X7a.contained_in_Q2 (sylS_le_borel.trans hB) ht with h | h
  · rcases (CFSG.QuasithinUnique.Setup.X7a.covBy_Q2 (K := F) 0).eq_or_eq hB h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl (h'.trans hP₂)))
  · rcases (CFSG.QuasithinUnique.Setup.X7a.covBy_Q2 (K := F) 1).eq_or_eq hB h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.trans hP₁))

end CFSG.Quasithin.MS93.MSP

module

public import CFSG.Quasithin.Background.B3FourInst
public import CFSG.Quasithin.Background.B3FourConj

public section

namespace CFSG.Quasithin.B3

open scoped commutatorElement

variable {k : Mod}

theorem isTinv_flagCV {b : Bool} (hS : Std 6 b) : IsTinv (Tgrp 6 b) (flagCV 6 k b) := by
  intro t ht s hs'
  have h := (mem_fixV).1 hs' (Mod.act 6 k t) (Subgroup.mem_map_of_mem _ (hS.hTH ht))
  rw [h]
  exact hs'

theorem flagSpace_one_iff {b : Bool} {e : ℕ} (hs : StructOK k b e) (hS : Std 6 b)
    {W : Subgroup (Mod.V 6 k)} :
    IsFlagSpace 6 k (Hg 6 b) (Tgrp 6 b) 1 W ↔ W = flagF1V 6 k b := by
  obtain ⟨c1, c2⟩ := card_flag b hs.hT0 hs.hflag
  have hC := isTinv_flagCV (k := k) hS
  constructor
  · intro hW
    refine (eq_of_flag hS.hp hC c1 c2).1 W hW.1 hW.2.2 ?_
    rw [hW.2.1]
    unfold flagCV
    ring
  · rintro rfl
    refine ⟨le_Fm hC, ?_, Fm_isTinv hC⟩
    rw [c1]
    unfold flagCV
    ring

theorem flagSpace_two_iff {b : Bool} {e : ℕ} (hs : StructOK k b e) (hS : Std 6 b)
    {W : Subgroup (Mod.V 6 k)} :
    IsFlagSpace 6 k (Hg 6 b) (Tgrp 6 b) 2 W ↔ W = flagF2V 6 k b := by
  obtain ⟨c1, c2⟩ := card_flag b hs.hT0 hs.hflag
  have hC := isTinv_flagCV (k := k) hS
  have hF1 : IsTinv (Tgrp 6 b) (flagF1V 6 k b) := Fm_isTinv hC
  constructor
  · intro hW
    refine (eq_of_flag hS.hp hC c1 c2).2 W hW.1 hW.2.2 ?_
    rw [hW.2.1]
    unfold flagCV
    ring
  · rintro rfl
    refine ⟨(le_Fm hC).trans (le_Fm hF1), ?_, Fm_isTinv hF1⟩
    rw [c2, c1]
    unfold flagCV
    ring

theorem exists_std_conj {b : Bool} {e : ℕ} (hs : StructOK k b e) (hS : Std 6 b)
    {T : Subgroup (Gp 6)} (hT : IsSylow2In (Hg 6 b) T) :
    ∃ g ∈ Hg 6 b, T = cj g (Tgrp 6 b) ∧
      (∀ W : Subgroup (Mod.V 6 k), IsFlagSpace 6 k (Hg 6 b) T 1 W ↔ W = gmap g (flagF1V 6 k b)) ∧
      (∀ W : Subgroup (Mod.V 6 k), IsFlagSpace 6 k (Hg 6 b) T 2 W ↔ W = gmap g (flagF2V 6 k b)) := by
  obtain ⟨g, hg, hgT⟩ := exists_conj_eq_sylow hT ⟨hS.hTH, hS.hp, hS.hidx⟩
  have hginv : g⁻¹ ∈ Hg 6 b := (Hg 6 b).inv_mem hg
  have e1 : cj g⁻¹ T = Tgrp 6 b := by
    rw [← hgT]
    have := cj_cj_inv g⁻¹ (Tgrp 6 b)
    simpa using this
  have key : ∀ (i : ℕ) (W F : Subgroup (Mod.V 6 k)),
      (IsFlagSpace 6 k (Hg 6 b) (Tgrp 6 b) i (gmap g⁻¹ W) ↔ gmap g⁻¹ W = F) →
      (IsFlagSpace 6 k (Hg 6 b) T i W ↔ W = gmap g F) := by
    intro i W F h
    have hiff : IsFlagSpace 6 k (Hg 6 b) T i W ↔
        IsFlagSpace 6 k (Hg 6 b) (Tgrp 6 b) i (gmap g⁻¹ W) := by
      rw [← e1]
      exact (isFlagSpace_gmap (T := T) (i := i) (W := W) hginv).symm
    rw [hiff, h]
    constructor
    · intro hF
      rw [← hF, gmap_gmap_inv]
    · intro hW
      rw [hW]
      ext w
      rw [mem_gmap, mem_gmap, inv_inv, act_inv_act]
  refine ⟨g, hg, hgT.symm, fun W => key 1 W _ (flagSpace_one_iff hs hS),
    fun W => key 2 W _ (flagSpace_two_iff hs hS)⟩

theorem isSwap_ti : (ti 6 2).IsSwap :=
  ⟨⟨4, by norm_num⟩, ⟨5, by norm_num⟩, by simp [Fin.ext_iff], by simp [ti, swapN]⟩

theorem fourG_std
    (hk : k = Mod.u0 ∨ k = Mod.ut0)
    {P : Set (Subgroup (MulAut (Mod.V 6 k)))}
    (hP : IsStableFF ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) P) :
    FourG k P (Tgrp 6 true) (O2s (stabW ⊤ (flagF1V 6 k true)))
      (O2s (stabW ⊤ (flagF2V 6 k true)))
      (stabW ⊤ (flagF1V 6 k true) ⊓ alternatingGroup (Fin 6))
      (stabW ⊤ (flagF2V 6 k true) ⊓ alternatingGroup (Fin 6))
      (ffJP P ((Tgrp 6 true).map (Mod.act 6 k)))
      (ffJP P ((O2s (stabW ⊤ (flagF1V 6 k true))).map (Mod.act 6 k))) := by
  have hchk := chkG6_of_mem hk
  have hst : chkStruct6 k true 4 = true := (G_parts hchk).1
  have hs := structOK_of_chk hst
  have hS := std6_G hst
  have hcore := G_core hchk hP (T := Tgrp 6 true) (H₁ := stabW (Hg 6 true) (flagF1V 6 k true))
    (H₂ := stabW (Hg 6 true) (flagF2V 6 k true)) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hvi := G_vi hchk hP (T := Tgrp 6 true) (H₂ := stabW (Hg 6 true) (flagF2V 6 k true))
    (R₂ := O2s (stabW (Hg 6 true) (flagF2V 6 k true))) rfl rfl rfl
  refine ⟨G_i hk hchk, G_ii hk hchk, hcore.1, hcore.2.1, fun hJ1 => ?_, hvi⟩
  obtain ⟨hcomm, hrest⟩ := hcore.2.2 hJ1
  refine ⟨hcomm, ?_⟩
  rcases hrest with ⟨hA, hN⟩ | hB
  · refine Or.inl ⟨⟨ti 6 2, ?_, isSwap_ti, hA⟩, hN⟩
    have hle : ffJP P ((O2s (stabW (Hg 6 true) (flagF1V 6 k true))).map (Mod.act 6 k)) ≤
        (O2s (stabW (Hg 6 true) (flagF1V 6 k true))).map (Mod.act 6 k) := ffJP_le _ _
    rw [hA] at hle
    have h1 : Mod.act 6 k (ti 6 2) ∈
        (O2s (stabW (Hg 6 true) (flagF1V 6 k true))).map (Mod.act 6 k) :=
      hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers (ti 6 2)))
    obtain ⟨x, hx, hxe⟩ := h1
    have hinj := act_injective (n := 6) (by norm_num) k
    rw [← hinj hxe]
    exact hx
  · exact Or.inr hB

theorem B3_4_1 (hk : k = Mod.u0 ∨ k = Mod.ut0)
    {P : Set (Subgroup (MulAut (Mod.V 6 k)))}
    (hP : IsStableFF ((alternatingGroup (Fin 6)).map (Mod.act 6 k)) P)
    {T : Subgroup (Gp 6)} (hT : IsSylow2In (alternatingGroup (Fin 6)) T)
    {W₁ W₂ : Subgroup (Mod.V 6 k)} (hW₁ : IsFlagSpace 6 k (alternatingGroup (Fin 6)) T 1 W₁)
    (hW₂ : IsFlagSpace 6 k (alternatingGroup (Fin 6)) T 2 W₂)
    {H₁ H₂ R₁ R₂ : Subgroup (Gp 6)} (hH₁ : H₁ = stabW (alternatingGroup (Fin 6)) W₁)
    (hH₂ : H₂ = stabW (alternatingGroup (Fin 6)) W₂) (hR₁ : R₁ = O2s H₁) (hR₂ : R₂ = O2s H₂)
    {J J₁ : Subgroup (MulAut (Mod.V 6 k))} (hJ : J = ffJP P (T.map (Mod.act 6 k)))
    (hJ₁ : J₁ = ffJP P (R₁.map (Mod.act 6 k))) :
    J = R₂.map (Mod.act 6 k) ∧ rk R₂ = 2 ∧
      (∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ R₂.map (Mod.act 6 k) →
        ¬ IsStrongFFStarOffender ((alternatingGroup (Fin 6)).map (Mod.act 6 k)) A) ∧
      J₁ = ⊥ := by
  have hchk := chkL6_of_mem hk
  have hst : chkStruct6 k false 3 = true := by
    simp only [chkL6, Bool.and_eq_true] at hchk
    exact hchk.1.1
  have hs := structOK_of_chk hst
  have hS := std6_L hst
  obtain ⟨g, hg, rfl, h1, h2⟩ := exists_std_conj hs hS hT
  obtain rfl := (h1 W₁).1 hW₁
  obtain rfl := (h2 W₂).1 hW₂
  have hg' : g ∈ alternatingGroup (Fin 6) := hg
  have hγ : Mod.act 6 k g ∈ (alternatingGroup (Fin 6)).map (Mod.act 6 k) :=
    Subgroup.mem_map_of_mem _ hg'
  have h0 : FourL k (O2s (stabW (alternatingGroup (Fin 6)) (flagF2V 6 k false)))
      (ffJP P ((Tgrp 6 false).map (Mod.act 6 k)))
      (ffJP P ((O2s (stabW (alternatingGroup (Fin 6)) (flagF1V 6 k false))).map
        (Mod.act 6 k))) := four_L_std hchk hP
  have hconj := FourL_conj hg' h0
  have eR₂ : R₂ = cj g (O2s (stabW (alternatingGroup (Fin 6)) (flagF2V 6 k false))) := by
    rw [hR₂, hH₂, stabW_gmap hg', O2s_cj]
  have eJ : J = B1.conjAut (Mod.act 6 k g) (ffJP P ((Tgrp 6 false).map (Mod.act 6 k))) := by
    rw [hJ, map_cj, ffJP_conjAut hP hγ]
  have eJ₁ : J₁ = B1.conjAut (Mod.act 6 k g) (ffJP P
      ((O2s (stabW (alternatingGroup (Fin 6)) (flagF1V 6 k false))).map (Mod.act 6 k))) := by
    rw [hJ₁, hR₁, hH₁, stabW_gmap hg', O2s_cj, map_cj, ffJP_conjAut hP hγ]
  rw [eR₂, eJ, eJ₁]
  exact hconj

theorem B3_4_2
    (hk : k = Mod.u0 ∨ k = Mod.ut0)
    {P : Set (Subgroup (MulAut (Mod.V 6 k)))}
    (hP : IsStableFF ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) P)
    {T : Subgroup (Gp 6)} (hT : IsSylow2In ⊤ T)
    {W₁ W₂ : Subgroup (Mod.V 6 k)} (hW₁ : IsFlagSpace 6 k ⊤ T 1 W₁)
    (hW₂ : IsFlagSpace 6 k ⊤ T 2 W₂)
    {H₁ H₂ R₁ R₂ L₁ L₂ : Subgroup (Gp 6)} (hH₁ : H₁ = stabW ⊤ W₁) (hH₂ : H₂ = stabW ⊤ W₂)
    (hR₁ : R₁ = O2s H₁) (hR₂ : R₂ = O2s H₂) (hL₁ : L₁ = H₁ ⊓ alternatingGroup (Fin 6))
    (hL₂ : L₂ = H₂ ⊓ alternatingGroup (Fin 6))
    {J J₁ : Subgroup (MulAut (Mod.V 6 k))} (hJ : J = ffJP P (T.map (Mod.act 6 k)))
    (hJ₁ : J₁ = ffJP P (R₁.map (Mod.act 6 k))) :
    FourG k P T R₁ R₂ L₁ L₂ J J₁ := by
  have hchk := chkG6_of_mem hk
  have hst : chkStruct6 k true 4 = true := (G_parts hchk).1
  have hs := structOK_of_chk hst
  have hS := std6_G hst
  obtain ⟨g, hg, rfl, h1, h2⟩ := exists_std_conj hs hS hT
  obtain rfl := (h1 W₁).1 hW₁
  obtain rfl := (h2 W₂).1 hW₂
  have hg' : g ∈ (⊤ : Subgroup (Gp 6)) := hg
  have hγ : Mod.act 6 k g ∈ (⊤ : Subgroup (Gp 6)).map (Mod.act 6 k) :=
    Subgroup.mem_map_of_mem _ hg'
  have h0 := fourG_std hk hP
  have hconj := FourG_conj hP g h0
  have eR₁ : R₁ = cj g (O2s (stabW ⊤ (flagF1V 6 k true))) := by
    rw [hR₁, hH₁, stabW_gmap hg', O2s_cj]
  have eR₂ : R₂ = cj g (O2s (stabW ⊤ (flagF2V 6 k true))) := by
    rw [hR₂, hH₂, stabW_gmap hg', O2s_cj]
  have eL₁ : L₁ = cj g (stabW ⊤ (flagF1V 6 k true) ⊓ alternatingGroup (Fin 6)) := by
    rw [hL₁, hH₁, stabW_gmap hg', cj_inf, cj_normal g (alternatingGroup (Fin 6))]
  have eL₂ : L₂ = cj g (stabW ⊤ (flagF2V 6 k true) ⊓ alternatingGroup (Fin 6)) := by
    rw [hL₂, hH₂, stabW_gmap hg', cj_inf, cj_normal g (alternatingGroup (Fin 6))]
  have eJ : J = B1.conjAut (Mod.act 6 k g) (ffJP P ((Tgrp 6 true).map (Mod.act 6 k))) := by
    rw [hJ, map_cj, ffJP_conjAut hP hγ]
  have eJ₁ : J₁ = B1.conjAut (Mod.act 6 k g) (ffJP P
      ((O2s (stabW ⊤ (flagF1V 6 k true))).map (Mod.act 6 k))) := by
    rw [hJ₁, eR₁, map_cj, ffJP_conjAut hP hγ]
  rw [eR₁, eR₂, eL₁, eL₂, eJ, eJ₁]
  exact hconj

end CFSG.Quasithin.B3

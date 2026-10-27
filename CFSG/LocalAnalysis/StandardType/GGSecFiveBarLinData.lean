module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleBarAbs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleRestrict
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleReflRestrict

public section

namespace CFSG.StandardType

theorem ggLin_bar_linear_data
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (hp2 : p ≠ 2) {I : Type*} [Nonempty I]
    (AX : I → Subgroup (V ≃ₗ[ZMod p] V)) (hX : ∀ X, GGLinConnGen (AX X))
    (AJ : Subgroup (V ≃ₗ[ZMod p] V)) (hJ : ∀ X, AJ ≤ AX X) (hJr : ∃ r ∈ AJ, GGLinRefl r)
    (Ag : Subgroup (V ≃ₗ[ZMod p] V)) (hAg : Ag = ⨆ X, AX X)
    (hfix : ggLinFix (Ag : Set (V ≃ₗ[ZMod p] V)) = ⊥)
    (hnotr : ∀ g ∈ Ag, g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}))
    (U : Submodule (ZMod p) V) (hU : U = ggLinCom (Ag : Set (V ≃ₗ[ZMod p] V)))
    (hdim : 3 ≤ Module.finrank (ZMod p) U) :
    ∃ (Abar : Subgroup (↥U ≃ₗ[ZMod p] ↥U)) (ρ : ↥Ag ≃* ↥Abar),
      ZS.ReflGen p Abar ∧ ZS.AbsIrred p Abar ∧
      (∀ (a : ↥Ag) (u : ↥U), (((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) u : V) = (a : V ≃ₗ[ZMod p] V) u) ∧
      (∀ a ∈ Ag, ∀ v : V, a v - v ∈ U) ∧
      (∀ a : ↥Ag, GGLinRefl (a : V ≃ₗ[ZMod p] V) ↔ ZS.IsRefl p ((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U)) ∧
      ((LinearEquiv.neg (ZMod p) : ↥U ≃ₗ[ZMod p] ↥U) ∈ Abar → U = ⊤) := by
  subst hAg
  subst hU
  obtain ⟨hprop, hirr, hend, htriv, hfaith, heps⟩ :=
    ggLin_bar_abstract hp2 AX hX AJ hJ hJr hfix hnotr
  set A : Subgroup (V ≃ₗ[ZMod p] V) := ⨆ X, AX X with hA
  set U' : Submodule (ZMod p) V := ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) with hU'
  have hUstab : ∀ a ∈ A, ∀ u ∈ U', a u ∈ U' := by
    intro a ha u hu
    have h := htriv a ha u
    have huv : a u = u + (a u - u) := by abel
    rw [huv]
    exact add_mem hu h
  obtain ⟨r, hr⟩ := ggLin_restrict_exists A U' hUstab
  have hrinj : Function.Injective r := by
    intro a b hab
    have hagree : ∀ u ∈ U', (a : V ≃ₗ[ZMod p] V) u = (b : V ≃ₗ[ZMod p] V) u := by
      intro u hu
      calc (a : V ≃ₗ[ZMod p] V) u
          = ((r a ⟨u, hu⟩ : ↥U') : V) := (hr a ⟨u, hu⟩).symm
        _ = ((r b ⟨u, hu⟩ : ↥U') : V) := by rw [hab]
        _ = (b : V ≃ₗ[ZMod p] V) u := hr b ⟨u, hu⟩
    have hmem : (a : V ≃ₗ[ZMod p] V)⁻¹ * (b : V ≃ₗ[ZMod p] V) ∈ A :=
      A.mul_mem (A.inv_mem a.2) b.2
    have hfixU : ∀ u ∈ U', ((a : V ≃ₗ[ZMod p] V)⁻¹ * (b : V ≃ₗ[ZMod p] V)) u = u := by
      intro u hu
      rw [LinearEquiv.mul_apply, ← hagree u hu]
      exact LinearEquiv.symm_apply_apply (a : V ≃ₗ[ZMod p] V) u
    have h1 : (a : V ≃ₗ[ZMod p] V)⁻¹ * (b : V ≃ₗ[ZMod p] V) = 1 := hfaith _ hmem hfixU
    have hb : (b : V ≃ₗ[ZMod p] V) = (a : V ≃ₗ[ZMod p] V) := by
      have h2 := congrArg (fun g : V ≃ₗ[ZMod p] V => (a : V ≃ₗ[ZMod p] V) * g) h1
      simpa [mul_assoc] using h2
    exact Subtype.ext hb.symm
  refine ⟨r.range, MonoidHom.ofInjective hrinj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hX' : ∀ X : I, ∃ S : Set (V ≃ₗ[ZMod p] V),
        (∀ r ∈ S, GGLinRefl r) ∧ AX X = Subgroup.closure S := by
      intro X
      obtain ⟨S, hrefl, _, hcl⟩ := hX X
      exact ⟨S, hrefl, hcl⟩
    choose S hSrefl hSeq using hX'
    have hAgen : A = Subgroup.closure (⋃ X, S X) := by
      rw [hA, iSup_congr hSeq, (Subgroup.closure_iUnion S).symm]
    let G' : Set ↥A := {a | (a : V ≃ₗ[ZMod p] V) ∈ ⋃ X, S X}
    let K : Subgroup ↥A := Subgroup.closure G'
    let R : Set (↥U' ≃ₗ[ZMod p] ↥U') := {t | t ∈ r.range ∧ ZS.IsRefl p t}
    have hGens_le : (⋃ X, S X) ≤ A := by
      intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨X, hxX⟩ := hx
      exact hAgen.symm ▸ Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨X, hxX⟩)
    have hKmap : K.map A.subtype = A := by
      change (Subgroup.closure G').map A.subtype = A
      rw [MonoidHom.map_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x ⟨a, ha, rfl⟩
        exact a.2
      · refine (le_of_eq hAgen).trans ?_
        apply Subgroup.closure_mono
        intro x hx
        exact ⟨⟨x, hGens_le hx⟩, hx, rfl⟩
    have hKtop : K = ⊤ := by
      apply (Subgroup.map_subtype_inj (H := A)).mp
      rw [hKmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hrange_le : r.range ≤ Subgroup.closure R := by
      rw [MonoidHom.range_eq_map, ← hKtop]
      change (Subgroup.closure G').map r ≤ Subgroup.closure R
      rw [MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro t ⟨a, ha, rfl⟩
      refine Subgroup.subset_closure ⟨⟨a, rfl⟩, ?_⟩
      have hrefl : GGLinRefl (a : V ≃ₗ[ZMod p] V) := by
        change (a : V ≃ₗ[ZMod p] V) ∈ ⋃ X, S X at ha
        rw [Set.mem_iUnion] at ha
        obtain ⟨X, haX⟩ := ha
        exact hSrefl X (a : V ≃ₗ[ZMod p] V) haX
      exact (ggLin_refl_iff_restrict hp2 A hfaith r hr a).mp hrefl
    have hclosure_le : Subgroup.closure R ≤ r.range := by
      rw [Subgroup.closure_le]
      rintro t ⟨ht, _⟩
      exact ht
    change r.range = Subgroup.closure R
    exact le_antisymm hrange_le hclosure_le
  ·
    refine ⟨?_, ?_⟩
    ·
      intro W hWstab
      set Wv : Submodule (ZMod p) V := W.map U'.subtype with hWv
      have hWv_le : Wv ≤ U' := Submodule.map_subtype_le U' W
      have hWv_stab : ∀ a ∈ A, ∀ w ∈ Wv, a w ∈ Wv := by
        intro a ha w hw
        rw [hWv, Submodule.mem_map] at hw
        obtain ⟨y, hyW, hyw⟩ := hw
        refine Submodule.mem_map.mpr ⟨r ⟨a, ha⟩ y, hWstab (r ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ y hyW, ?_⟩
        rw [← hyw]
        exact hr ⟨a, ha⟩ y
      rcases hirr Wv hWv_le hWv_stab with hbot | htop
      · left
        rw [← le_bot_iff]
        intro w hw
        have hmem : (w : V) ∈ Wv := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
        rw [hbot] at hmem
        exact Subtype.ext (by simpa using hmem)
      · right
        rw [← top_le_iff]
        intro x hx
        have hmem : (x : V) ∈ Wv := by rw [htop]; exact x.2
        rw [hWv, Submodule.mem_map] at hmem
        obtain ⟨y, hyW, hyx⟩ := hmem
        have hyx' : y = x := Subtype.ext hyx
        rw [← hyx']
        exact hyW
    ·
      intro T hT
      obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl U'
      let proj : V →ₗ[ZMod p] ↥U' := U'.projectionOnto Q hQ
      let f : V →ₗ[ZMod p] V := U'.subtype ∘ₗ T ∘ₗ proj
      have hfrange : LinearMap.range f ≤ U' := by
        rintro _ ⟨v, rfl⟩
        exact Submodule.coe_mem _
      have hfcomm : ∀ a ∈ A, ∀ u ∈ U', f (a u) = a (f u) := by
        intro a ha u hu
        let a' : ↥A := ⟨a, ha⟩
        have hproj1 : proj (a u) = r a' ⟨u, hu⟩ := by
          rw [Submodule.projectionOnto_apply_of_mem_left hQ (hUstab a ha u hu)]
          apply Subtype.ext
          exact (hr a' ⟨u, hu⟩).symm
        have hproj2 : proj u = ⟨u, hu⟩ :=
          Submodule.projectionOnto_apply_of_mem_left hQ hu
        have hTcomm : T (r a' ⟨u, hu⟩) = r a' (T ⟨u, hu⟩) :=
          congrArg (fun (L : ↥U' →ₗ[ZMod p] ↥U') => L ⟨u, hu⟩) (hT (r a') ⟨a', rfl⟩)
        change U'.subtype (T (proj (a u))) = a (U'.subtype (T (proj u)))
        rw [hproj1, hproj2, hTcomm]
        exact hr a' (T ⟨u, hu⟩)
      obtain ⟨c, hc⟩ := hend f hfrange hfcomm
      refine ⟨c, ?_⟩
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      have hfw : f (w : V) = c • (w : V) := hc (w : V) w.2
      have hproj : proj (w : V) = w :=
        Submodule.projectionOnto_apply_of_mem_left hQ w.2
      have h1 : (T w : V) = f (w : V) := by
        change (T w : V) = (U'.subtype (T (proj (w : V))) : V)
        rw [hproj]
        rfl
      rw [h1, hfw, LinearMap.smul_apply, LinearMap.id_apply]
      rfl
  ·
    intro a u
    rw [MonoidHom.ofInjective_apply]
    exact hr a u
  ·
    intro a ha v
    exact htriv a ha v
  ·
    intro a
    rw [MonoidHom.ofInjective_apply]
    exact ggLin_refl_iff_restrict hp2 A hfaith r hr a
  ·
    intro hneg
    rw [MonoidHom.mem_range] at hneg
    obtain ⟨a, ha⟩ := hneg
    have hact : ∀ u ∈ U', (a : V ≃ₗ[ZMod p] V) u = -u := by
      intro u hu
      have h1 : ((r a ⟨u, hu⟩ : ↥U') : V) = -u := by
        rw [ha]
        rfl
      exact (hr a ⟨u, hu⟩).symm.trans h1
    have hsq : (a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V) = 1 := by
      apply hfaith
      · exact A.mul_mem a.2 a.2
      · intro u hu
        rw [LinearEquiv.mul_apply, hact u hu, map_neg, hact u hu, neg_neg]
    exact heps ⟨(a : V ≃ₗ[ZMod p] V), a.2, hsq, hact⟩

end CFSG.StandardType

end

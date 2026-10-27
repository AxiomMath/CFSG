module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6ks_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
  have hp2 : p = 2 := by
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact hp hp2

private noncomputable def l6ks_neg {p : ℕ} [Fact p.Prime] (M : Type*) [AddCommGroup M]
    [Module (ZMod p) M] : M ≃ₗ[ZMod p] M where
  toFun := fun v => -v
  invFun := fun v => -v
  map_add' := by intro a b; abel
  map_smul' := by intro c v; simp
  left_inv := by intro v; simp
  right_inv := by intro v; simp

private lemma l6ks_restrict_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (T : Submodule (ZMod p) V) (g : ↥(ggLinStab T)) (v : ↥T) :
    (((ggLinRestrictHom T g) v : ↥T) : V) = (g : V ≃ₗ[ZMod p] V) (v : V) := by
  simp [ggLinRestrictHom, LinearEquiv.ofSubmodules_apply]

theorem ggFixLine_not_slpm {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x)
    (hQ : ∀ g : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s),
      g ∈ ggFixLineQ S ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) : False := by
  classical
  haveI : Finite ι := S.finite_family
  haveI : Module.Finite (ZMod p) V :=
    ggFixLine_finite (p := p) s S.s_refl S.fix_H
  obtain ⟨hA, hspanT, hd_lower, hd_upper⟩ := ggFixLine_T_props S
  let T := ggFixLineT r s
  let A := Subgroup.closure (Set.range r ∪ Set.range s)
  let R : ↥A →* (↥T ≃ₗ[ZMod p] ↥T) :=
    (ggLinRestrictHom T).comp (Subgroup.inclusion (ggFixLine_A_le_stab S))
  have hRinj : Function.Injective R := ggFixLine_restrict_injective S
  let d := Module.finrank (ZMod p) ↥T
  have hd4 : 4 ≤ d := by
    have h5 : 5 ≤ N := S.five_le
    dsimp [d, T]
    omega
  let f := Module.finBasis (ZMod p) ↥T
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro hh
    have hv := congrArg Fin.val hh
    simp [i0, i1] at hv
  have hfv : f.coord i1 (f i0) = 0 := by
    simp [Ne.symm hi01, i0, i1]
  let u : ↥T ≃ₗ[ZMod p] ↥T := LinearEquiv.transvection hfv
  have hu_apply : ∀ y, u y = y + f.coord i1 y • f i0 :=
    fun y => LinearEquiv.transvection.apply hfv y
  have hu_f0 : u (f i0) = f i0 := by
    rw [hu_apply, hfv, zero_smul, add_zero]
  have hu_coord_i1 : f.coord i1 (f i1) = 1 := by
    simp [Ne.symm hi01, i0, i1]
  have hu_f1_sub : u (f i1) - f i1 = f i0 := by
    rw [hu_apply, hu_coord_i1, one_smul, add_sub_cancel_left]
  have hu_move : ∀ y, u y - y = f.coord i1 y • f i0 := by
    intro y
    rw [hu_apply]
    abel
  have hu_mem_span : ∀ y : ↥T, u y - y ∈ Submodule.span (ZMod p) ({f i0} : Set ↥T) := by
    intro y
    rw [hu_move y]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hu_mem_spanV : ∀ y : ↥T,
      ((u y - y : ↥T) : V) ∈ Submodule.span (ZMod p) ({(f i0 : V)} : Set V) := by
    intro y
    rw [hu_move y]
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hu_fix_move : ∀ y : ↥T, u (u y - y) = u y - y := by
    intro y
    rw [hu_move y, map_smul, hu_f0]
  have hu_move_eq : ggLinMove u = Submodule.span (ZMod p) ({f i0} : Set ↥T) := by
    apply le_antisymm
    · rw [ggLinMove]
      rintro y ⟨z, hz⟩
      rw [← hz]
      simpa [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap] using hu_mem_span z
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [ggLinMove]
      refine ⟨f i1, ?_⟩
      simpa [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap] using hu_f1_sub
  have hf0_ne : f i0 ≠ 0 := f.ne_zero i0
  have hu_rank : Module.finrank (ZMod p) (ggLinMove u) = 1 := by
    rw [hu_move_eq, finrank_span_singleton hf0_ne]
  have hu_det : LinearEquiv.det u = 1 := by
    dsimp [u]
    exact LinearEquiv.transvection.det_eq_one hfv
  have huQ : u ∈ ggFixLineQ S := (hQ u).mpr (Or.inl hu_det)
  let σ : ↥T ≃ₗ[ZMod p] ↥T := l6ks_neg ↥T
  have hσ2 : σ * σ = 1 := by
    ext y
    simp [σ, l6ks_neg]
  have hσ_det : LinearEquiv.det σ = 1 ∨ LinearEquiv.det σ = -1 := by
    have hdet2 : LinearEquiv.det σ * LinearEquiv.det σ = 1 := by
      rw [← map_mul, hσ2, map_one]
    have h2R : ((LinearEquiv.det σ : ZMod p)) * ((LinearEquiv.det σ : ZMod p)) = 1 := by
      have hh := congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hdet2
      simpa using hh
    have hfac : ((LinearEquiv.det σ : ZMod p) - 1) *
        ((LinearEquiv.det σ : ZMod p) + 1) = 0 := by
      calc ((LinearEquiv.det σ : ZMod p) - 1) * ((LinearEquiv.det σ : ZMod p) + 1)
          = ((LinearEquiv.det σ : ZMod p)) * ((LinearEquiv.det σ : ZMod p)) - 1 := by ring
        _ = 0 := by rw [h2R]; ring
    rcases mul_eq_zero.mp hfac with hh | hh
    · left
      ext
      simpa using sub_eq_zero.mp hh
    · right
      ext
      change (LinearEquiv.det σ : ZMod p) = -1
      rw [eq_neg_iff_add_eq_zero]
      exact hh
  have hσQ : σ ∈ ggFixLineQ S := (hQ σ).mpr hσ_det
  have hQmem : ∀ g : ↥T ≃ₗ[ZMod p] ↥T, g ∈ ggFixLineQ S ↔ ∃ a : ↥A, R a = g := by
    intro g
    change g ∈ MonoidHom.range R ↔ ∃ a : ↥A, R a = g
    exact MonoidHom.mem_range
  obtain ⟨uhat, huhat⟩ := (hQmem u).mp huQ
  obtain ⟨shat, hshat⟩ := (hQmem σ).mp hσQ
  have hR_apply : ∀ (a : ↥A) (y : ↥T),
      (a : V ≃ₗ[ZMod p] V) (y : V) = (((R a) y : ↥T) : V) := by
    intro a y
    have hh := l6ks_restrict_apply (V := V) T
      (Subgroup.inclusion (ggFixLine_A_le_stab S) a) y
    simpa [R, Subgroup.coe_inclusion] using hh.symm
  have hT_apply : ∀ (a : ↥A) (y : V), (a : V ≃ₗ[ZMod p] V) y - y ∈ T := by
    intro a y
    exact hA a.1 a.2 y
  have hcommA : uhat * shat = shat * uhat := by
    apply hRinj
    rw [map_mul, map_mul, huhat, hshat]
    ext y
    simp only [LinearEquiv.mul_apply]
    rw [show σ y = -y from rfl, map_neg]
    rfl
  have hcommV : (uhat : V ≃ₗ[ZMod p] V) * (shat : V ≃ₗ[ZMod p] V) =
      (shat : V ≃ₗ[ZMod p] V) * (uhat : V ≃ₗ[ZMod p] V) := by
    simpa using congrArg (fun a : ↥A => (a : V ≃ₗ[ZMod p] V)) hcommA
  have hcomm_apply : ∀ y : V, (uhat : V ≃ₗ[ZMod p] V) ((shat : V ≃ₗ[ZMod p] V) y) =
      (shat : V ≃ₗ[ZMod p] V) ((uhat : V ≃ₗ[ZMod p] V) y) := by
    intro y
    have hh := congrArg (fun e : V ≃ₗ[ZMod p] V => e y) hcommV
    simpa [LinearEquiv.mul_apply] using hh
  have hshat2 : shat * shat = 1 := by
    apply hRinj
    rw [map_mul, hshat, hσ2, map_one]
  have hshatV2 : (shat : V ≃ₗ[ZMod p] V) * (shat : V ≃ₗ[ZMod p] V) = 1 := by
    simpa using congrArg (fun a : ↥A => (a : V ≃ₗ[ZMod p] V)) hshat2
  have hshat_apply_T : ∀ y : ↥T, (shat : V ≃ₗ[ZMod p] V) (y : V) = -(y : V) := by
    intro y
    rw [hR_apply shat y, hshat]
    rfl
  have htrans : Module.finrank (ZMod p) (ggLinMove (uhat : V ≃ₗ[ZMod p] V)) = 1 ∧
      ∀ w, (uhat : V ≃ₗ[ZMod p] V) ((uhat : V ≃ₗ[ZMod p] V) w - w) =
        (uhat : V ≃ₗ[ZMod p] V) w - w := by
    obtain ⟨e'', hefix, hdecomp⟩ : ∃ e'' : V,
        (uhat : V ≃ₗ[ZMod p] V) e'' = e'' ∧
        (∀ w : V, ∃ t : ↥T, ∃ c : ZMod p, w = (t : V) + c • e'') := by
      by_cases htop : T = ⊤
      · refine ⟨0, map_zero _, ?_⟩
        intro w
        have hw : w ∈ T := by rw [htop]; exact Submodule.mem_top
        exact ⟨⟨w, hw⟩, 0, by simp⟩
      · have hex : ∃ w : V, w ∉ T := by
          by_contra hc
          push Not at hc
          apply htop
          ext w
          exact ⟨fun _ => Submodule.mem_top, fun _ => hc w⟩
        obtain ⟨e', he'⟩ := hex
        have hmem : (uhat : V ≃ₗ[ZMod p] V) e' - e' ∈ T := hT_apply uhat e'
        have hσmem : (shat : V ≃ₗ[ZMod p] V) e' - e' ∈ T := hT_apply shat e'
        have h2p : (2 : ZMod p) ≠ 0 := l6ks_two_ne_zero S.odd
        have htwo : (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 := by
          rw [← two_mul, mul_inv_cancel₀ h2p]
        let e'' : V := (2 : ZMod p)⁻¹ • (e' + (shat : V ≃ₗ[ZMod p] V) e')
        have he''diff : e'' - e' ∈ T := by
          have hce : (2 : ZMod p)⁻¹ • e' + (2 : ZMod p)⁻¹ • e' = e' := by
            rw [← add_smul, htwo, one_smul]
          have hsub : e'' - e' =
              (2 : ZMod p)⁻¹ • ((shat : V ≃ₗ[ZMod p] V) e' - e') := by
            dsimp [e'']
            rw [smul_add, smul_sub]
            calc (2 : ZMod p)⁻¹ • e' + (2 : ZMod p)⁻¹ • ((shat : V ≃ₗ[ZMod p] V) e') - e'
                = (2 : ZMod p)⁻¹ • e' + (2 : ZMod p)⁻¹ • ((shat : V ≃ₗ[ZMod p] V) e')
                    - ((2 : ZMod p)⁻¹ • e' + (2 : ZMod p)⁻¹ • e') := by rw [hce]
              _ = (2 : ZMod p)⁻¹ • ((shat : V ≃ₗ[ZMod p] V) e') - (2 : ZMod p)⁻¹ • e' := by abel
          rw [hsub]
          exact T.smul_mem _ hσmem
        have he''ne : e'' ∉ T := by
          intro hh
          apply he'
          have : e' = e'' - (e'' - e') := by abel
          rw [this]
          exact T.sub_mem hh he''diff
        have hshat_e'' : (shat : V ≃ₗ[ZMod p] V) e'' = e'' := by
          have hs2 : (shat : V ≃ₗ[ZMod p] V) ((shat : V ≃ₗ[ZMod p] V) e') = e' := by
            have hh := congrArg (fun e : V ≃ₗ[ZMod p] V => e e') hshatV2
            simpa [LinearEquiv.mul_apply] using hh
          dsimp [e'']
          rw [map_smul, map_add, hs2, add_comm]
        have hefix : (uhat : V ≃ₗ[ZMod p] V) e'' = e'' := by
          have huhat_e' : (uhat : V ≃ₗ[ZMod p] V) e' =
              e' + ((uhat : V ≃ₗ[ZMod p] V) e' - e') := by abel
          have hshat_d : (shat : V ≃ₗ[ZMod p] V) ((uhat : V ≃ₗ[ZMod p] V) e' - e') =
              -((uhat : V ≃ₗ[ZMod p] V) e' - e') := by
            have hh := hshat_apply_T ⟨(uhat : V ≃ₗ[ZMod p] V) e' - e', hmem⟩
            simpa using hh
          dsimp [e'']
          rw [map_smul, map_add, hcomm_apply, huhat_e', map_add, hshat_d]
          congr 1
          abel
        have hfinV : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) ↥T + 1 := by
          have h1 : Module.finrank (ZMod p) V ≤ N := S.dim_le
          change Module.finrank (ZMod p) V ≤
            Module.finrank (ZMod p) ↥(ggFixLineT r s) + 1
          omega
        have hspan_eq : T ⊔ Submodule.span (ZMod p) ({e''} : Set V) = ⊤ := by
          have hdim_sup : Module.finrank (ZMod p) ↥(T ⊔ Submodule.span (ZMod p) ({e''} : Set V))
              = Module.finrank (ZMod p) ↥T + 1 := by
            have hh := Submodule.finrank_sup_add_finrank_inf_eq T
              (Submodule.span (ZMod p) ({e''} : Set V))
            have hinf : T ⊓ Submodule.span (ZMod p) ({e''} : Set V) = ⊥ := by
              rw [Submodule.eq_bot_iff]
              intro y hy
              obtain ⟨hyT, hyspan⟩ := hy
              obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyspan
              by_cases hc : c = 0
              · simp [hc]
              · exfalso
                apply he''ne
                have hcc : e'' = c⁻¹ • (c • e'') := by
                  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
                rw [hcc]
                exact T.smul_mem _ hyT
            have hspan1 : Module.finrank (ZMod p)
                ↥(Submodule.span (ZMod p) ({e''} : Set V)) = 1 := by
              rw [finrank_span_singleton]
              intro h0
              exact he''ne (by rw [h0]; exact T.zero_mem)
            rw [hinf, finrank_bot, hspan1] at hh
            omega
          have htop' : Module.finrank (ZMod p)
              ↥(T ⊔ Submodule.span (ZMod p) ({e''} : Set V)) = Module.finrank (ZMod p) V := by
            apply le_antisymm
            · exact Submodule.finrank_le _
            · rw [hdim_sup]; exact hfinV
          exact Submodule.eq_top_of_finrank_eq htop'
        have hdecomp' : ∀ w : V, ∃ t : ↥T, ∃ c : ZMod p, w = (t : V) + c • e'' := by
          intro w
          have hw : w ∈ T ⊔ Submodule.span (ZMod p) ({e''} : Set V) := by
            rw [hspan_eq]; exact Submodule.mem_top
          obtain ⟨t, ht, y, hy, hty⟩ := Submodule.mem_sup.mp hw
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
          exact ⟨⟨t, ht⟩, c, hty.symm⟩
        exact ⟨e'', hefix, hdecomp'⟩
    have hdisp : ∀ (t : ↥T) (c : ZMod p),
        (uhat : V ≃ₗ[ZMod p] V) ((t : V) + c • e'') - ((t : V) + c • e'') =
          ((u t - t : ↥T) : V) := by
      intro t c
      have hmap : (uhat : V ≃ₗ[ZMod p] V) ((t : V) + c • e'') =
          ((u t : ↥T) : V) + c • e'' := by
        rw [map_add, map_smul, hefix]
        congr 1
        rw [hR_apply uhat t, huhat]
      rw [hmap]
      simp
    have hdisp_mem : ∀ w : V,
        (uhat : V ≃ₗ[ZMod p] V) w - w ∈ Submodule.span (ZMod p) ({(f i0 : V)} : Set V) := by
      intro w
      obtain ⟨t, c, rfl⟩ := hdecomp w
      rw [hdisp t c]
      exact hu_mem_spanV t
    have hf0_mem : (f i0 : V) ∈ ggLinMove (uhat : V ≃ₗ[ZMod p] V) := by
      rw [ggLinMove]
      refine ⟨((f i1 : ↥T) : V), ?_⟩
      have h' : ((u (f i1) - f i1 : ↥T) : V) = (f i0 : V) := by rw [hu_f1_sub]
      change (uhat : V ≃ₗ[ZMod p] V) ((f i1 : ↥T) : V) - ((f i1 : ↥T) : V) = (f i0 : V)
      rw [hR_apply uhat (f i1), huhat]
      simpa using h'
    have hmove_eq : ggLinMove (uhat : V ≃ₗ[ZMod p] V) =
        Submodule.span (ZMod p) ({(f i0 : V)} : Set V) := by
      apply le_antisymm
      · rw [ggLinMove]
        rintro y ⟨w, hw⟩
        rw [← hw]
        simpa [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap] using hdisp_mem w
      · rw [Submodule.span_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hf0_mem
    have hrank : Module.finrank (ZMod p) (ggLinMove (uhat : V ≃ₗ[ZMod p] V)) = 1 := by
      rw [hmove_eq, finrank_span_singleton]
      intro h0
      exact hf0_ne (Subtype.ext h0)
    have hfixed : ∀ w, (uhat : V ≃ₗ[ZMod p] V) ((uhat : V ≃ₗ[ZMod p] V) w - w) =
        (uhat : V ≃ₗ[ZMod p] V) w - w := by
      intro w
      obtain ⟨t, c, rfl⟩ := hdecomp w
      rw [hdisp t c]
      rw [hR_apply uhat (u t - t), huhat]
      have hh := hu_fix_move t
      simpa using congrArg (fun z : ↥T => (z : V)) hh
    exact ⟨hrank, hfixed⟩
  exact S.no_transvection (uhat : V ≃ₗ[ZMod p] V) uhat.2 htrans

end CFSG.StandardType

end

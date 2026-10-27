module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2CoreKAux
public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsGeneral

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {k : Type} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q] [Module k Q]

section Helpers

private theorem w183b2_top_ne_bot {Q : Type*} [AddCommGroup Q] [Module k Q] [Nontrivial Q] :
    (⊤ : Submodule k Q) ≠ ⊥ := by
  intro h
  haveI : Subsingleton Q := by
    refine ⟨fun x y => ?_⟩
    have hx : x ∈ (⊥ : Submodule k Q) := by rw [← h]; exact Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule k Q) := by rw [← h]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy]
  exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial Q›) this

private theorem w183b2_rho_injective (ρ : Representation k G Q) (d : G) :
    Function.Injective (ρ d) := by
  have hl : Function.LeftInverse (ρ d⁻¹) (ρ d) := by
    intro u
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  exact hl.injective

private theorem w183b2_conj_mul (ρ : Representation k G Q) (n d : G) :
    ρ n * ρ d = ρ d * ρ (d⁻¹ * n * d) := by
  rw [← map_mul, ← map_mul]
  congr 1
  group

private theorem w183b2_conj_mul_inv (ρ : Representation k G Q) (n d : G) :
    ρ n * ρ d⁻¹ = ρ d⁻¹ * ρ (d * n * d⁻¹) := by
  rw [← map_mul, ← map_mul]
  congr 1
  group

private theorem w183b2_conj_mul_left (ρ : Representation k G Q) (n x : G) :
    ρ (x * n * x⁻¹) * ρ x = ρ x * ρ n := by
  rw [← map_mul, ← map_mul]
  congr 1
  group

private theorem w183b2_conj_mul_left_inv (ρ : Representation k G Q) (n x : G) :
    ρ x⁻¹ * ρ (x * n * x⁻¹) = ρ n * ρ x⁻¹ := by
  rw [← map_mul, ← map_mul]
  congr 1
  group

private theorem w183b2_map_translate_le {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {U : Submodule k Q} (hU : w183b2InvSub ρ (A₁ ⊔ A₂) U)
    {n d : G} (hn : n ∈ A₁ ⊔ A₂) (hd : d ∈ Δ) :
    Submodule.map (ρ n) (U.map (ρ d)) ≤ U.map (ρ d) := by
  have hN : (A₁ ⊔ A₂).Normal := w183b2_normal_sup h
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
  have h1 : ρ n (ρ d u) = ρ d (ρ (d⁻¹ * n * d) u) := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun F : Module.End k Q => F u) (w183b2_conj_mul ρ n d)
  rw [h1]
  exact Submodule.mem_map.mpr ⟨ρ (d⁻¹ * n * d) u,
    hU _ (hN.conj_mem' n hn d) u hu, rfl⟩

end Helpers

theorem w183b2_simple_inf_eq_bot {ρ : Representation k G Q} {N : Subgroup G}
    {U V : Submodule k Q} (hU : w183b2SimpleSub ρ N U) (hV : w183b2SimpleSub ρ N V)
    (hne : U ≠ V) : U ⊓ V = ⊥ := by
  obtain ⟨hU0, hUinv, hUmin⟩ := hU
  obtain ⟨hV0, hVinv, hVmin⟩ := hV
  have hInv : w183b2InvSub ρ N (U ⊓ V) :=
    fun n hn u hu => ⟨hUinv n hn u hu.1, hVinv n hn u hu.2⟩
  rcases hUmin (U ⊓ V) hInv inf_le_left with h | h
  · exact h
  · exfalso
    have hle : U ≤ V := by
      intro u hu
      have hu' : u ∈ U ⊓ V := by rw [h]; exact hu
      exact hu'.2
    rcases hVmin U hUinv hle with hUbot | hUV
    · exact hU0 hUbot
    · exact hne hUV

theorem w183b2_exists_simple [FiniteDimensional k Q] [Nontrivial Q] (ρ : Representation k G Q)
    (N : Subgroup G) : ∃ U : Submodule k Q, w183b2SimpleSub ρ N U := by
  classical
  have hex : ∃ n, ∃ U : Submodule k Q, w183b2InvSub ρ N U ∧ U ≠ ⊥ ∧ Module.finrank k U = n :=
    ⟨_, ⊤, (fun _ _ _ _ => Submodule.mem_top), w183b2_top_ne_bot, rfl⟩
  obtain ⟨U, hUinv, hU0, hUn⟩ := Nat.find_spec hex
  refine ⟨U, hU0, hUinv, fun V hV hle => ?_⟩
  by_cases hV0 : V = ⊥
  · exact Or.inl hV0
  · right
    have h1 : Module.finrank k U ≤ Module.finrank k V := by
      have h2 := Nat.find_min' hex (m := Module.finrank k V) ⟨V, hV, hV0, rfl⟩
      rwa [← hUn] at h2
    exact Submodule.eq_of_le_of_finrank_le hle h1

theorem w183b2_simple_translate {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {U : Submodule k Q} (hU : w183b2SimpleSub ρ (A₁ ⊔ A₂) U)
    {d : G} (hd : d ∈ Δ) : w183b2SimpleSub ρ (A₁ ⊔ A₂) (U.map (ρ d)) := by
  obtain ⟨hU0, hUinv, hUmin⟩ := hU
  have hN : (A₁ ⊔ A₂).Normal := w183b2_normal_sup h
  refine ⟨?_, ?_, ?_⟩
  · intro hbot
    apply hU0
    rw [eq_bot_iff]
    intro u hu
    have hmem : ρ d u ∈ U.map (ρ d) := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact w183b2_rho_injective ρ d (by rw [hmem, map_zero])
  · intro n hn w hw
    exact w183b2_map_translate_le h hUinv hn hd (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)
  · intro V hV hle
    have hVinv' : w183b2InvSub ρ (A₁ ⊔ A₂) (V.map (ρ d⁻¹)) := by
      intro n hn w hw
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
      have h1 : ρ n (ρ d⁻¹ v) = ρ d⁻¹ (ρ (d * n * d⁻¹) v) := by
        simpa only [Module.End.mul_apply] using
          congrArg (fun F : Module.End k Q => F v) (w183b2_conj_mul_inv ρ n d)
      rw [h1]
      exact Submodule.mem_map.mpr ⟨ρ (d * n * d⁻¹) v,
        hV _ (hN.conj_mem n hn d) v hv, rfl⟩
    have hle' : V.map (ρ d⁻¹) ≤ U := by
      rintro w ⟨v, hv, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp (hle hv)
      have h2 : ρ d⁻¹ (ρ d u) = u := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rwa [h2]
    rcases hUmin (V.map (ρ d⁻¹)) hVinv' hle' with hbot | hU'
    · left
      rw [eq_bot_iff]
      intro v hv
      have hmem : ρ d⁻¹ v ∈ V.map (ρ d⁻¹) := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact w183b2_rho_injective ρ d⁻¹ (by rw [hmem, map_zero])
    · right
      have hmapid : (V.map (ρ d⁻¹)).map (ρ d) = V := by
        have hcomp : (ρ d).comp (ρ d⁻¹) = LinearMap.id := by
          ext w
          rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply]
          rfl
        rw [← Submodule.map_comp, hcomp, Submodule.map_id]
      rw [← hmapid, hU']

theorem w183b2_cover_translates {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {U : Submodule k Q} (hU : w183b2SimpleSub ρ (A₁ ⊔ A₂) U) :
    (⨆ d ∈ Δ, U.map (ρ d)) = ⊤ := by
  obtain ⟨hU0, hUinv, _⟩ := hU
  let S : Submodule k Q := ⨆ d : Δ, U.map (ρ (d : G))
  have hmapN : ∀ n ∈ A₁ ⊔ A₂, Submodule.map (ρ n) S ≤ S := by
    intro n hn
    rw [Submodule.map_iSup]
    refine iSup_le (fun d => ?_)
    exact le_trans (w183b2_map_translate_le h hUinv hn d.2)
      (le_iSup (fun d : Δ => U.map (ρ (d : G))) d)
  have hmapD : ∀ d ∈ Δ, Submodule.map (ρ d) S ≤ S := by
    intro d hd
    rw [Submodule.map_iSup]
    refine iSup_le (fun e => ?_)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    have hmem : ρ d (ρ (e : G) u) ∈ U.map (ρ (d * (e : G))) := by
      refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    exact le_iSup (fun f : Δ => U.map (ρ (f : G)))
      ⟨d * (e : G), Δ.mul_mem hd e.2⟩ hmem
  let St : Subgroup G :=
    { carrier := {g : G | ∀ s ∈ S, ρ g s ∈ S ∧ ρ g⁻¹ s ∈ S}
      mul_mem' := by
        intro a b ha hb s hs
        refine ⟨?_, ?_⟩
        · have h2 : ρ a (ρ b s) ∈ S := (ha (ρ b s) (hb s hs).1).1
          simpa only [map_mul, Module.End.mul_apply] using h2
        · have h2 : ρ b⁻¹ (ρ a⁻¹ s) ∈ S := (hb (ρ a⁻¹ s) (ha s hs).2).2
          have h3 : ρ (a * b)⁻¹ s = ρ b⁻¹ (ρ a⁻¹ s) := by
            rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          rw [h3]
          exact h2
      one_mem' := by
        intro s hs
        exact ⟨by simpa using hs, by simpa using hs⟩
      inv_mem' := by
        intro a ha s hs
        exact ⟨(ha s hs).2, by simpa using (ha s hs).1⟩ }
  have hNSt : A₁ ⊔ A₂ ≤ St := by
    intro n hn s hs
    exact ⟨hmapN n hn (Submodule.mem_map.mpr ⟨s, hs, rfl⟩),
      hmapN n⁻¹ ((A₁ ⊔ A₂).inv_mem hn) (Submodule.mem_map.mpr ⟨s, hs, rfl⟩)⟩
  have hΔSt : Δ ≤ St := by
    intro d hd s hs
    exact ⟨hmapD d hd (Submodule.mem_map.mpr ⟨s, hs, rfl⟩),
      hmapD d⁻¹ (Δ.inv_mem hd) (Submodule.mem_map.mpr ⟨s, hs, rfl⟩)⟩
  have hle : A₁ ⊔ A₂ ⊔ Δ ≤ St := sup_le hNSt hΔSt
  have hSttop : St = ⊤ := top_le_iff.mp (h.gen ▸ hle)
  have hSinv : CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits.IsInv ρ S := by
    intro g s hs
    have hg : g ∈ St := by rw [hSttop]; exact Subgroup.mem_top g
    exact (hg s hs).1
  have hSle : U ≤ S := by
    have h1 : (1 : G) ∈ Δ := Δ.one_mem
    have h2 : U = U.map (ρ (1 : G)) := by
      rw [map_one]
      exact (Submodule.map_id (p := U)).symm
    rw [h2]
    exact le_iSup (fun d : Δ => U.map (ρ (d : G))) ⟨1, h1⟩
  have hSne : S ≠ ⊥ := by
    intro hbot
    exact hU0 (le_bot_iff.mp (hSle.trans (le_of_eq hbot)))
  obtain ⟨_, hIrred⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits.isIrreducible_iff ρ).1 h.irr
  rcases hIrred S hSinv with hbot | htop
  · exact absurd hbot hSne
  · have hStop : (⨆ d : Δ, U.map (ρ (d : G))) = ⊤ := htop
    exact (iSup_subtype'' (Δ : Set G) (fun d => U.map (ρ d))).symm.trans hStop

theorem w183b2_stab_triv {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {U : Submodule k Q} (hU : w183b2SimpleSub ρ (A₁ ⊔ A₂) U)
    (hmove : ∃ d ∈ Δ, U.map (ρ d) ≠ U) : ∀ f ∈ Δ, U.map (ρ f) = U → f = 1 := by
  obtain ⟨d, hd, hdU⟩ := hmove
  intro f hf hfU
  have hUd : w183b2SimpleSub ρ (A₁ ⊔ A₂) (U.map (ρ d)) := w183b2_simple_translate h hU hd
  have hdisj : U.map (ρ d) ⊓ U = ⊥ := w183b2_simple_inf_eq_bot hUd hU hdU
  have hfU' : ∀ u ∈ U, ρ f u ∈ U := by
    intro u hu
    have hmem : ρ f u ∈ U.map (ρ f) := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    rwa [hfU] at hmem
  have hfixU : ∀ u ∈ U, ρ f u = u := w183b2_fixes_of_disjoint_image h hd hf hfU' hdisj
  have hfixall : ∀ q : Q, ρ f q = q := by
    have hker : (⨆ e ∈ Δ, U.map (ρ e)) ≤ LinearMap.ker (ρ f - 1) := by
      refine iSup_le (fun e => iSup_le (fun he => ?_))
      rintro w ⟨u, hu, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      have hcomm : ρ f (ρ e u) = ρ e (ρ f u) := by
        simpa only [Module.End.mul_apply] using
          congrArg (fun F : Module.End k Q => F u) (w183b2_rho_comm h hf he)
      rw [hcomm, hfixU u hu]
    intro q
    have hq : q ∈ (⨆ e ∈ Δ, U.map (ρ e)) := by
      rw [w183b2_cover_translates h hU]
      exact Submodule.mem_top
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      using hker hq
  exact h.faith f hf hfixall

theorem w183b2_twist_iso {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {U : Submodule k Q} (hU : w183b2InvSub ρ (A₁ ⊔ A₂) U) {x y : G}
    (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hiso : w183b2NIso ρ (A₁ ⊔ A₂) (U.map (ρ x)) (U.map (ρ y))) :
    w183b2NIso ρ (A₁ ⊔ A₂) U (U.map (ρ (x⁻¹ * y))) := by
  obtain ⟨e, he_inj, he_range, he_lin⟩ := hiso
  have hN : (A₁ ⊔ A₂).Normal := w183b2_normal_sup h
  have hxinj : Function.Injective (ρ x) := w183b2_rho_injective ρ x
  let φ := Submodule.equivMapOfInjective (ρ x) hxinj U
  let e' : U →ₗ[k] Q := (ρ x⁻¹).comp (e.comp φ.toLinearMap)
  have he'_apply : ∀ u : U, e' u = ρ x⁻¹ (e (φ u)) := fun _ => rfl
  refine ⟨e', ?_, ?_, ?_⟩
  · intro u v huv
    have h1 : ρ x⁻¹ (e (φ u)) = ρ x⁻¹ (e (φ v)) := by simpa only [he'_apply] using huv
    have h2 : e (φ u) = e (φ v) := w183b2_rho_injective ρ x⁻¹ h1
    exact φ.injective (he_inj h2)
  · ext w
    constructor
    · rintro ⟨u, rfl⟩
      have heu : e (φ u) ∈ U.map (ρ y) := by
        rw [← he_range]
        exact LinearMap.mem_range.mpr ⟨φ u, rfl⟩
      obtain ⟨u', hu', heu'⟩ := Submodule.mem_map.mp heu
      have hthis : e' u = ρ (x⁻¹ * y) u' := by
        rw [he'_apply, ← heu']
        simp only [← Module.End.mul_apply, ← map_mul]
      rw [hthis]
      exact Submodule.mem_map.mpr ⟨u', hu', rfl⟩
    · rintro ⟨u, hu, rfl⟩
      have hyu : ρ y u ∈ LinearMap.range e := by
        rw [he_range]
        exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hyu
      refine LinearMap.mem_range.mpr ⟨φ.symm v, ?_⟩
      have hφv : φ (φ.symm v) = v := LinearEquiv.apply_symm_apply φ v
      have hthis : e' (φ.symm v) = ρ (x⁻¹ * y) u := by
        rw [he'_apply, hφv, hv]
        simp only [← Module.End.mul_apply, ← map_mul]
      exact hthis
  · intro n hn u v huv
    have hn' : x * n * x⁻¹ ∈ A₁ ⊔ A₂ := hN.conj_mem n hn x
    have hrel : ρ (x * n * x⁻¹) ((φ u : U.map (ρ x)) : Q) = ((φ v : U.map (ρ x)) : Q) := by
      rw [Submodule.coe_equivMapOfInjective_apply, Submodule.coe_equivMapOfInjective_apply]
      rw [show ρ x (v : Q) = ρ x (ρ n (u : Q)) from by rw [huv]]
      simpa only [Module.End.mul_apply] using
        congrArg (fun F : Module.End k Q => F (u : Q)) (w183b2_conj_mul_left ρ n x)
    have hev : e (φ v) = ρ (x * n * x⁻¹) (e (φ u)) :=
      he_lin (x * n * x⁻¹) hn' (φ u) (φ v) hrel
    calc e' v = ρ x⁻¹ (e (φ v)) := he'_apply v
      _ = ρ x⁻¹ (ρ (x * n * x⁻¹) (e (φ u))) := by rw [hev]
      _ = (ρ x⁻¹ * ρ (x * n * x⁻¹)) (e (φ u)) := by rw [Module.End.mul_apply]
      _ = (ρ n * ρ x⁻¹) (e (φ u)) := by rw [w183b2_conj_mul_left_inv]
      _ = ρ n (ρ x⁻¹ (e (φ u))) := by rw [Module.End.mul_apply]
      _ = ρ n (e' u) := by rw [he'_apply]

end CFSG.LocalAnalysis.WeakClosure81

end

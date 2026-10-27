module

public import CFSG.LocalAnalysis.StandardType.GGSmallD2Ctx
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
import CFSG.LocalAnalysis.StandardType.GGDepAOdd
import CFSG.LocalAnalysis.StandardType.GGExtCtxAbsIrred
import CFSG.LocalAnalysis.StandardType.ZS.Adapter

public section

namespace CFSG.StandardType

private theorem ggSmallD2_hdisp {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} (hr : ∀ i v, r i v = v - α i v • h i)
    {ra : V ≃ₗ[ZMod p] V} {ha : V} {αa : Module.Dual (ZMod p) V}
    (hra : ∀ v, ra v = v - αa v • ha) {T : Submodule (ZMod p) V}
    (hH_le : Submodule.span (ZMod p) (Set.range h) ≤ T) (hha_mem : ha ∈ T) :
    ∀ a ∈ Subgroup.closure (Set.range r ∪ {ra}), ∀ v, a v - v ∈ T := by
  intro a ha_mem
  refine Subgroup.closure_induction (p := fun a _ => ∀ v, a v - v ∈ T) ?_ ?_ ?_ ?_ ha_mem
  · rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      intro v
      rw [hr i v]
      simp only [sub_sub_cancel_left]
      have hmem : h i ∈ T := hH_le (Submodule.subset_span (Set.mem_range_self i))
      exact T.neg_mem (Submodule.smul_mem _ _ hmem)
    · simp only [Set.mem_singleton_iff] at hx
      subst hx
      intro v
      rw [hra v]
      simp only [sub_sub_cancel_left]
      exact T.neg_mem (Submodule.smul_mem _ _ hha_mem)
  · intro v
    simp
  · rintro x y hx hy hpx hpy v
    rw [LinearEquiv.mul_apply]
    have h1 : x (y v) - y v ∈ T := hpx (y v)
    have h2 : y v - v ∈ T := hpy v
    have h3 : x (y v) - v = (x (y v) - y v) + (y v - v) := by abel
    rw [h3]
    exact T.add_mem h1 h2
  · rintro x hx hpx v
    have h1 : x (x⁻¹ v) - x⁻¹ v ∈ T := hpx (x⁻¹ v)
    have h2 : x (x⁻¹ v) = v := x.apply_symm_apply v
    have h3 : x⁻¹ v - v = -(x (x⁻¹ v) - x⁻¹ v) := by
      rw [h2]
      abel
    rw [h3]
    exact T.neg_mem h1

private theorem ggSmallD2_h_le_ggLinCom {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (F : GGDepAFrame p N h α x) {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    (hr : ∀ i v, r i v = v - α i v • h i) {ra : V ≃ₗ[ZMod p] V}
    (hp2z : (2 : ZMod p) ≠ 0) :
    Submodule.span (ZMod p) (Set.range h) ≤
      ggLinCom (Subgroup.closure (Set.range r ∪ {ra}) : Set (V ≃ₗ[ZMod p] V)) := by
  let A := Subgroup.closure (Set.range r ∪ {ra})
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  have hαii : α i (h i) = 2 := by
    rw [F.pair i i]
    simp [CartanMatrix.A]
  have hri_mem : r i ∈ A := Subgroup.subset_closure (Or.inl (Set.mem_range_self i))
  have h_le : ggLinMove (r i) ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) :=
    le_iSup₂_of_le (r i) hri_mem le_rfl
  have hmem : h i ∈ ggLinMove (r i) := by
    refine LinearMap.mem_range.mpr ⟨-((2 : ZMod p)⁻¹) • h i, ?_⟩
    change r i (-((2 : ZMod p)⁻¹) • h i) - (-((2 : ZMod p)⁻¹) • h i) = h i
    rw [hr i]
    have hα : α i (-((2 : ZMod p)⁻¹) • h i) = -1 := by
      rw [map_smul, hαii, smul_eq_mul]
      field_simp
    rw [hα]
    rw [← sub_smul, ← sub_smul]
    have hc : (-((2 : ZMod p)⁻¹) - (-1)) - (-((2 : ZMod p)⁻¹)) = 1 := by
      field_simp
      ring
    rw [hc, one_smul]
  exact h_le hmem

private theorem ggSmallD2_hfix {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (F : GGDepAFrame p N h α x) {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    (hr : ∀ i v, r i v = v - α i v • h i) {ra : V ≃ₗ[ZMod p] V} {ha : V}
    {αa : Module.Dual (ZMod p) V} (hra : ∀ v, ra v = v - αa v • ha)
    (hαa : αa ha = 2) (hw : αa x ≠ 0) (hp2z : (2 : ZMod p) ≠ 0) :
    ∀ v, (∀ a ∈ Subgroup.closure (Set.range r ∪ {ra}), a v = v) → v = 0 := by
  intro v hv
  have hr_fix : ∀ i, r i v = v := fun i =>
    hv (r i) (Subgroup.subset_closure (Or.inl (Set.mem_range_self i)))
  have hα_fix : ∀ i, α i v = 0 := by
    intro i
    have h1 : r i v = v := hr_fix i
    rw [hr i v] at h1
    have h2 : α i v • h i = 0 := by
      have h := congrArg (fun w => w - v) h1
      simp only [sub_sub_cancel_left, sub_self] at h
      exact neg_eq_zero.mp h
    have hhi_ne : h i ≠ 0 := by
      intro hzero
      have hαii : α i (h i) = 2 := by
        rw [F.pair i i]
        simp [CartanMatrix.A]
      rw [hzero, map_zero] at hαii
      exact hp2z hαii.symm
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hhi_ne
  have hvx : v ∈ Submodule.span (ZMod p) ({x} : Set V) := F.fix v hα_fix
  rw [Submodule.mem_span_singleton] at hvx
  obtain ⟨c, hc⟩ := hvx
  have hra_fix : ra v = v := hv ra (Subgroup.subset_closure (Or.inr rfl))
  have hαa_fix : αa v = 0 := by
    have h1 : ra v = v := hra_fix
    rw [hra v] at h1
    have h2 : αa v • ha = 0 := by
      have h := congrArg (fun w => w - v) h1
      simp only [sub_sub_cancel_left, sub_self] at h
      exact neg_eq_zero.mp h
    have hha_ne : ha ≠ 0 := by
      intro hzero
      have h := hαa
      rw [hzero, map_zero] at h
      exact hp2z h.symm
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hha_ne
  have hc0 : c = 0 := by
    have h1 : αa (c • x) = 0 := by
      rwa [← hc] at hαa_fix
    rw [map_smul] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hw
  rw [← hc, hc0, zero_smul]

private theorem ggSmallD2_card_ne {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (hp2 : p ≠ 2) (hN : 5 ≤ N)
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepAFrame p N h α x) (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (ra : V ≃ₗ[ZMod p] V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hra : ∀ v, ra v = v - αa v • ha)
    (hαa : αa ha = 2) (hw : αa x ≠ 0) :
    Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≠ Nat.factorial N := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V)) DFunLike.coe_injective
  obtain ⟨ρ, -, hρA, hρx, hρfaith⟩ := ggDepAOdd_perm_embed hp2 hN F r hr
  let A := Subgroup.closure (Set.range r ∪ {ra})
  have hρrange_le : ρ.range ≤ A := by
    rintro _ ⟨σ, rfl⟩
    exact Subgroup.closure_mono (Set.subset_union_left) (hρA σ)
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have h1 : ρ (σ * τ⁻¹) = 1 := by
      rw [map_mul, map_inv, hστ]
      simp
    have h2 : σ * τ⁻¹ = 1 := by
      apply hρfaith
      intro i
      have h3 := congrArg (fun e => e (h i)) h1
      simpa using h3
    exact mul_inv_eq_one.mp h2
  have hcard_range : Nat.card ↥ρ.range = Nat.factorial N := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    rw [Nat.card_perm, Nat.card_fin]
  intro hcardA
  have hρeqA : ρ.range = A := by
    apply Subgroup.eq_of_le_of_card_ge hρrange_le
    rw [hcard_range, hcardA]
  have hra_mem : ra ∈ ρ.range := by
    rw [hρeqA]
    exact Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨σ, hσ⟩ := hra_mem
  have hrax : ra x = x := by rw [← hσ]; exact hρx σ
  have hαa_x_ha : αa x • ha = 0 := by
    have h1 : ra x = x := hrax
    rw [hra x] at h1
    have h := congrArg (fun w => w - x) h1
    simp only [sub_sub_cancel_left, sub_self] at h
    exact neg_eq_zero.mp h
  have hha_ne : ha ≠ 0 := by
    intro hzero
    have h := hαa
    rw [hzero, map_zero] at h
    have hp2z : (2 : ZMod p) ≠ 0 :=
      Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    exact hp2z h.symm
  rcases smul_eq_zero.mp hαa_x_ha with h | h
  · exact hw h
  · exact hha_ne h

theorem ggSmallD2Ctx_of_caseI {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = N) {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hjoin : ∃ c, αa (h c) ≠ 0)
    (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (hnH : ha ∉ Submodule.span (ZMod p) (Set.range h)) :
    ∃ (T : Submodule (ZMod p) V) (AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)),
      GGSmallD2Ctx p N (Subgroup.closure (Set.range r ∪ {ra})) T AT := by
  let A := Subgroup.closure (Set.range r ∪ {ra})
  let H := Submodule.span (ZMod p) (Set.range h)
  let T := H ⊔ Submodule.span (ZMod p) ({ha} : Set V)
  obtain ⟨AU, ψ, hdimT, hAbs, hGen, -, hInjψ, hrestrT⟩ :=
    ggDepAOdd_caseI_data hp2 hN F r hr ra ha αa hra hαa hjoin hw hnt hcard hnH T rfl
  have hp2z : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hdisp : ∀ a ∈ A, ∀ v, a v - v ∈ T :=
    ggSmallD2_hdisp hr hra le_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self ha))
  have hT : T ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
    have hH_le : H ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) :=
      ggSmallD2_h_le_ggLinCom F hr hp2z
    have hha_mem : ha ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
      have hra_mem : ra ∈ A := Subgroup.subset_closure (Or.inr rfl)
      have h_le : ggLinMove ra ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) :=
        le_iSup₂_of_le ra hra_mem le_rfl
      have hmem : ha ∈ ggLinMove ra := by
        refine LinearMap.mem_range.mpr ⟨-((2 : ZMod p)⁻¹) • ha, ?_⟩
        change ra (-((2 : ZMod p)⁻¹) • ha) - (-((2 : ZMod p)⁻¹) • ha) = ha
        rw [hra]
        have hα : αa (-((2 : ZMod p)⁻¹) • ha) = -1 := by
          rw [map_smul, hαa, smul_eq_mul]
          field_simp
        rw [hα]
        rw [← sub_smul, ← sub_smul]
        have hc : (-((2 : ZMod p)⁻¹) - (-1)) - (-((2 : ZMod p)⁻¹)) = 1 := by
          field_simp
          ring
        rw [hc, one_smul]
      exact h_le hmem
    exact sup_le hH_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hha_mem))
  have hfix : ∀ v, (∀ a ∈ A, a v = v) → v = 0 :=
    ggSmallD2_hfix F hr hra hαa hw hp2z
  have hcard_ne : Nat.card ↥A ≠ Nat.factorial N :=
    ggSmallD2_card_ne hp2 hN F r hr ra ha αa hra hαa hw
  refine ⟨T, AU, ?_⟩
  refine {
    p_ne_two := hp2
    N_ge := hN
    dvd := F.dvd
    finite := inferInstance
    ext := GGExtCtx.of_absIrred hdisp hT hfix hnt hrestrT hAbs
    finrank_eq := hdim
    finrank_T := Or.inl (by rw [hdimT]; omega)
    card_le := hcard
    card_ne := hcard_ne
    perm := ⟨ψ, hInjψ⟩
    absIrred := hAbs
    reflGen := (ZS.reflGen_iff_eq_closure_ggLinRefl AU).mpr hGen
  }

theorem ggSmallD2Ctx_of_caseII {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = N) {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (hH : ha ∈ Submodule.span (ZMod p) (Set.range h)) :
    ∃ (T : Submodule (ZMod p) V) (AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)),
      GGSmallD2Ctx p N (Subgroup.closure (Set.range r ∪ {ra})) T AT := by
  let A := Subgroup.closure (Set.range r ∪ {ra})
  let H := Submodule.span (ZMod p) (Set.range h)
  obtain ⟨ρ, -, hρA, -, hρfaith⟩ := ggDepAOdd_perm_embed hp2 hN F r hr
  obtain ⟨AH, ψ, -, hdimH, hAbs, hGen, -, hInjψ, -, -, -, hrestrH⟩ :=
    ggDepAOdd_caseII_data hp2 hN F r hr ra ha αa hra hαa hw hnt hcard H rfl hH ρ hρA hρfaith
  have hp2z : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hdisp : ∀ a ∈ A, ∀ v, a v - v ∈ H :=
    ggSmallD2_hdisp hr hra le_rfl hH
  have hT : H ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) :=
    ggSmallD2_h_le_ggLinCom F hr hp2z
  have hfix : ∀ v, (∀ a ∈ A, a v = v) → v = 0 :=
    ggSmallD2_hfix F hr hra hαa hw hp2z
  have hcard_ne : Nat.card ↥A ≠ Nat.factorial N :=
    ggSmallD2_card_ne hp2 hN F r hr ra ha αa hra hαa hw
  refine ⟨H, AH, ?_⟩
  refine {
    p_ne_two := hp2
    N_ge := hN
    dvd := F.dvd
    finite := inferInstance
    ext := GGExtCtx.of_absIrred hdisp hT hfix hnt hrestrH hAbs
    finrank_eq := hdim
    finrank_T := Or.inr (by rw [hdimH]; omega)
    card_le := hcard
    card_ne := hcard_ne
    perm := ⟨ψ, hInjψ⟩
    absIrred := hAbs
    reflGen := (ZS.reflGen_iff_eq_closure_ggLinRefl AH).mpr hGen
  }

end CFSG.StandardType

end

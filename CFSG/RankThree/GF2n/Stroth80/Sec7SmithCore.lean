module

public import CFSG.RankThree.GF2n.Stroth80.Sec7SmithRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

theorem sec7_smith_core_abstract (hSmith : SmithOmegaPlusEightStatement)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Type} [AddCommGroup E] [Module K E] [Module.Finite K E]
    (B : LinearMap.BilinForm K E) (hr : B.IsRefl)
    (U W' R₀ P : Submodule K E) (hW' : W' = B.orthogonal U)
    (hUiso : ∀ x ∈ U, ∀ y ∈ U, B x y = 0)
    (ψ : E →ₗ[K] E) (hψadj : ∀ e e', B (ψ e) e' = B e (ψ e'))
    (hψU : ∀ u ∈ U, ψ u = 0) (hψW : ∀ e, ψ e ∈ W') (hR₀ : R₀ = W'.map ψ) (hP : P = R₀ ⊔ U)
    (hUψ : U ⊓ R₀ = ⊥)
    (hfU : Module.finrank K U = 8) (hfψ : Module.finrank K R₀ = 8)
    {H : Type} [Group H] (T : H →* Module.End K E)
    (hTU : ∀ h, ∀ u ∈ U, T h u ∈ U) (hTW : ∀ h, ∀ w ∈ W', T h w ∈ W')
    (hTψ : ∀ h, ∀ w ∈ W', T h (ψ w) - ψ (T h w) ∈ U)
    (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hker : ∀ h ∈ φ.ker, ∀ w ∈ W', T h w - w ∈ U)
    (hirr : ∀ A : AddSubgroup E, A ≤ P.toAddSubgroup → U.toAddSubgroup ≤ A →
      (∀ h, ∀ a ∈ A, T h a ∈ A) → A = U.toAddSubgroup ∨ A = P.toAddSubgroup)
    (L : Subgroup H) {u : Fin 4 ⊕ Fin 4 → K} (hu : StatedQuadPlus 4 K u = 0) (hu0 : u ≠ 0)
    (hL : L.map φ = rootGroupGL (quadPlus 4 K) u)
    (hLn : ∀ h : H, (∃ c : K, ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec u = c • u) →
      ∀ l ∈ L, h⁻¹ * l * h ∈ L)
    (A : Submodule K E) (hA : ∀ e, e ∈ A ↔ e ∈ W' ∧ ∀ l ∈ L, T l e - e ∈ U)
    (hAperp : B.orthogonal A = A) (hψA : ∀ a ∈ A, ψ a ∈ A)
    (S : Submodule K E) (hSW : S ≤ W') (hSiso : ∀ x ∈ S, ∀ y ∈ S, B x y = 0)
    (hψS : ∀ s ∈ S, ψ s ∈ S)
    (hTS : ∀ h : H,
      (∃ c : K, ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec u = c • u) →
      ∀ s ∈ S, T h s ∈ S) :
    ∀ s ∈ S, ψ s ∈ A := by
  classical
  have hUW : U ≤ W' := by
    rw [hW']
    intro x hx n hn
    exact hUiso n hn x hx
  have hUP : U ≤ P := hP ▸ le_sup_right
  have hR₀W : R₀ ≤ W' := by
    rw [hR₀]
    rintro _ ⟨w, -, rfl⟩
    exact hψW w
  have hPW : P ≤ W' := hP ▸ sup_le hR₀W hUW
  have hψSP : ∀ s ∈ S, ψ s ∈ P := fun s hs =>
    hP ▸ Submodule.mem_sup_left (hR₀ ▸ ⟨s, hSW hs, rfl⟩)
  have hTP : ∀ h, ∀ p ∈ P, T h p ∈ P := by
    intro h p hp
    rw [hP] at hp ⊢
    obtain ⟨r, hr', u', hu', rfl⟩ := Submodule.mem_sup.mp hp
    rw [hR₀] at hr'
    obtain ⟨w, hw, rfl⟩ := hr'
    rw [map_add]
    refine (R₀ ⊔ U).add_mem ?_ (Submodule.mem_sup_right (hTU h u' hu'))
    have h1 := hTψ h w hw
    have e : T h (ψ w) = ψ (T h w) + (T h (ψ w) - ψ (T h w)) := by abel
    rw [e]
    exact (R₀ ⊔ U).add_mem (Submodule.mem_sup_left (hR₀ ▸ ⟨T h w, hTW h w hw, rfl⟩))
      (Submodule.mem_sup_right h1)
  obtain ⟨ρ', hρ'⟩ := sec7_omega_subquotient_rep T P U hTP hTU φ hφ
    (fun h hh p hp => hker h hh p (hPW hp))
  have hsurj : ∀ g : StatedOmega (StatedQuadPlus 4 K), ∃ h : H,
      (g : GL (Fin 4 ⊕ Fin 4) K) = φ h := by
    intro g
    have hg : (g : GL (Fin 4 ⊕ Fin 4) K) ∈ φ.range := by
      rw [hφ]
      exact g.2
    obtain ⟨h, hh⟩ := hg
    exact ⟨h, hh.symm⟩
  have hfinP : Module.finrank K P = 16 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq R₀ U
    rw [inf_comm, hUψ, finrank_bot, hfU, hfψ, ← hP] at h
    omega
  have hfinY : Module.finrank K (↥P ⧸ U.submoduleOf P) = 8 := by
    have h1 := Submodule.finrank_quotient_add_finrank (U.submoduleOf P)
    have h2 : Module.finrank K (U.submoduleOf P) = Module.finrank K U :=
      (Submodule.comapSubtypeEquivOfLe hUP).finrank_eq
    omega
  have hbig : 2 < Nat.card (↥P ⧸ U.submoduleOf P) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥P ⧸ U.submoduleOf P), hfinY]
    have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ Nat.card K ^ 8 := Nat.pow_le_pow_left hK2 8
  have hmem : ∀ h : H, φ h ∈ StatedOmega (StatedQuadPlus 4 K) := fun h =>
    hφ ▸ MonoidHom.mem_range.mpr ⟨h, rfl⟩
  have hirrY : ∀ A' : AddSubgroup (↥P ⧸ U.submoduleOf P),
      (∀ g y, y ∈ A' → ρ' g y ∈ A') → A' = ⊥ ∨ A' = ⊤ := by
    intro A' hA'
    obtain ⟨ρR, hρR⟩ := sec7_subquotient_rep T P U hTP hTU
    refine sec7_subquotient_irred T P U hUP hTP ρR hρR hirr A' ?_
    intro h y hy
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective (U.submoduleOf P) y
    have h1 := hA' ⟨φ h, hmem h⟩ _ hy
    rwa [hρ' h ⟨φ h, hmem h⟩ rfl p, ← hρR h p] at h1
  obtain ⟨D, hDmem⟩ : ∃ D : Submodule K (↥P ⧸ U.submoduleOf P),
      ∀ y, y ∈ D ↔ ∃ p : ↥P, (p : E) ∈ S.map ψ ∧ Submodule.Quotient.mk p = y :=
    ⟨Submodule.map (Submodule.mkQ (U.submoduleOf P)) ((S.map ψ).submoduleOf P), fun y => by
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, rfl⟩⟩
  obtain ⟨F, hF⟩ : ∃ F : Submodule K (↥P ⧸ U.submoduleOf P),
      ∀ y, y ∈ F ↔ ∀ g, Sec7Siegel u g → ρ' g y = y :=
    ⟨{ carrier := {y | ∀ g, Sec7Siegel u g → ρ' g y = y}
       add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
       zero_mem' := fun g _ => map_zero _
       smul_mem' := fun c a ha g hg => by rw [map_smul, ha g hg] }, fun _ => Iff.rfl⟩
  have hsieg_of_L : ∀ l ∈ L, Sec7Siegel u ⟨φ l, hmem l⟩ := by
    intro l hl
    refine (sec7Siegel_iff hu hu0 _).mpr ?_
    rw [← hL]
    exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
  have hL_of_sieg : ∀ g, Sec7Siegel u g → ∃ l ∈ L, (g : GL (Fin 4 ⊕ Fin 4) K) = φ l := by
    intro g hg
    have hg' : (g : GL (Fin 4 ⊕ Fin 4) K) ∈ L.map φ := by
      rw [hL]
      exact (sec7Siegel_iff hu hu0 g).mp hg
    obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.mp hg'
    exact ⟨l, hl, hlg.symm⟩
  have hFmem : ∀ p : ↥P, (Submodule.Quotient.mk p : ↥P ⧸ U.submoduleOf P) ∈ F ↔
      ∀ l ∈ L, T l p - p ∈ U := by
    intro p
    constructor
    · intro hp l hl
      have h1 := (hF _).mp hp _ (hsieg_of_L l hl)
      rw [hρ' l ⟨φ l, hmem l⟩ rfl p] at h1
      exact (Submodule.Quotient.eq (U.submoduleOf P)).mp h1
    · intro hp
      refine (hF _).mpr fun g hg => ?_
      obtain ⟨l, hl, hlg⟩ := hL_of_sieg g hg
      rw [hρ' l g hlg p]
      exact (Submodule.Quotient.eq _).mpr (hp l hl)
  have hFA : ∀ p : ↥P, (Submodule.Quotient.mk p : ↥P ⧸ U.submoduleOf P) ∈ F ↔ (p : E) ∈ A := by
    intro p
    rw [hFmem, hA]
    exact ⟨fun h => ⟨hPW p.2, h⟩, fun h => h.2⟩
  have hD : ∀ g : StatedOmega (StatedQuadPlus 4 K),
      (∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec u = c • u) →
      ∀ y ∈ D, ρ' g y ∈ D := by
    intro g hg y hy
    obtain ⟨h, hh⟩ := hsurj g
    obtain ⟨p, ⟨s, hs, hsp⟩, rfl⟩ := (hDmem y).mp hy
    rw [hρ' h g hh p]
    rw [hh] at hg
    have hTs := hTS h hg s hs
    refine (hDmem _).mpr ⟨⟨ψ (T h s), hψSP _ hTs⟩, ⟨T h s, hTs, rfl⟩, ?_⟩
    refine (Submodule.Quotient.eq _).mpr ?_
    show ψ (T h s) - T h p ∈ U
    have h1 := hTψ h s (hSW hs)
    rw [← hsp]
    have e : ψ (T h s) - T h (ψ s) = -(T h (ψ s) - ψ (T h s)) := by abel
    rw [e]
    exact U.neg_mem h1
  have hFinv : ∀ g : StatedOmega (StatedQuadPlus 4 K),
      (∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec u = c • u) →
      ∀ y ∈ F, ρ' g y ∈ F := by
    intro g hg y hy
    obtain ⟨h, hh⟩ := hsurj g
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective (U.submoduleOf P) y
    rw [hρ' h g hh p]
    rw [hh] at hg
    rw [hFmem] at hy ⊢
    intro l hl
    have hl' := hLn h hg l hl
    have h1 := hy _ hl'
    have e : T h (T (h⁻¹ * l * h) p) = T l (T h p) := by
      rw [← Module.End.mul_apply, ← map_mul, show h * (h⁻¹ * l * h) = l * h by group, map_mul,
        Module.End.mul_apply]
    show T l (T h p) - T h p ∈ U
    have e2 : T l (T h p) - T h p = T h (T (h⁻¹ * l * h) p - p) := by
      rw [map_sub, e]
    rw [e2]
    exact hTU h _ h1
  have hfix := sec7_smith_fix hSmith ρ' hirrY hbig hu hu0 D F hF hD hFinv
  have hS'iso : ∀ x ∈ S ⊔ U, ∀ y ∈ S ⊔ U, B x y = 0 := by
    intro x hx y hy
    obtain ⟨s, hs, u₁, hu₁, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s', hs', u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hy
    have hus : ∀ u' ∈ U, ∀ s ∈ S, B u' s = 0 := fun u' hu' s hs => by
      have h1 := hSW hs
      rw [hW'] at h1
      exact h1 u' hu'
    have hsu : ∀ s ∈ S, ∀ u' ∈ U, B s u' = 0 := fun s hs u' hu' => hr _ _ (hus u' hu' s hs)
    simp only [map_add, LinearMap.add_apply, hSiso s hs s' hs', hsu s hs u₂ hu₂,
      hus u₁ hu₁ s' hs', hUiso u₁ hu₁ u₂ hu₂, add_zero]
  have hclosure := sec7_closure_of_fixed B ψ hψadj (S ⊔ U) A hS'iso hAperp ?_
  · intro s hs
    exact hclosure s (Submodule.mem_sup_left hs)
  · rcases hfix with hD0 | hFD
    · left
      intro x hx
      obtain ⟨s, hs, u₁, hu₁, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add, hψU u₁ hu₁, add_zero]
      have hmem1 : (Submodule.Quotient.mk (⟨ψ s, hψSP s hs⟩ : ↥P) :
          ↥P ⧸ U.submoduleOf P) ∈ D :=
        (hDmem _).mpr ⟨⟨ψ s, hψSP s hs⟩, ⟨s, hs, rfl⟩, rfl⟩
      rw [hD0, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem1
      have hψsU : ψ s ∈ U := hmem1
      have hψsR : ψ s ∈ R₀ := hR₀ ▸ ⟨s, hSW hs, rfl⟩
      have hboth : ψ s ∈ U ⊓ R₀ := ⟨hψsU, hψsR⟩
      rw [hUψ] at hboth
      exact (Submodule.mem_bot K).mp hboth
    · right
      intro a ha
      have hψaP : ψ a ∈ P := hP ▸ Submodule.mem_sup_left (hR₀ ▸ ⟨a, ((hA a).mp ha).1, rfl⟩)
      have hmemF : (Submodule.Quotient.mk (⟨ψ a, hψaP⟩ : ↥P) : ↥P ⧸ U.submoduleOf P) ∈ F :=
        (hFA _).mpr (hψA a ha)
      obtain ⟨p', ⟨s, hs, hsp⟩, hp'⟩ := (hDmem _).mp (hFD hmemF)
      have h2 := (Submodule.Quotient.eq (U.submoduleOf P)).mp hp'
      have h3 : (p' : E) - ψ a ∈ U := h2
      rw [← hsp] at h3
      refine Submodule.mem_sup.mpr ⟨ψ s, hψS s hs, ψ a - ψ s, ?_, ?_⟩
      · have : ψ a - ψ s = -(ψ s - ψ a) := by abel
        rw [this]
        exact U.neg_mem h3
      · abel

end

section

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

section Twist

variable {K K' E : Type*} [Field K] [Field K'] [AddCommGroup E] [Module K E] [Module K' E]
  (θ : K ≃+* K') (hsm : ∀ (c : K') (x : E), c • x = θ.symm c • x)

@[expose] def sec7TwistSub (N : Submodule K E) : Submodule K' E where
  carrier := N
  add_mem' := N.add_mem
  zero_mem' := N.zero_mem
  smul_mem' c x hx := by
    rw [hsm]
    exact N.smul_mem _ hx

@[expose] def sec7TwistLin (f : E →ₗ[K] E) : E →ₗ[K'] E where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    simp only [hsm, RingHom.id_apply]
    exact f.map_smul _ _

@[expose] def sec7TwistBil (B : LinearMap.BilinForm K E) : LinearMap.BilinForm K' E :=
  LinearMap.mk₂ K' (fun x y => θ (B x y))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply])
    (fun c x y => by
      simp only [hsm, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul,
        RingEquiv.apply_symm_apply])
    (fun x y y' => by simp only [map_add])
    (fun c x y => by
      simp only [hsm, map_smul, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply])

theorem sec7TwistSub_toAddSubgroup (N : Submodule K E) :
    (sec7TwistSub θ hsm N).toAddSubgroup = N.toAddSubgroup :=
  AddSubgroup.ext fun _ => Iff.rfl

end Twist


theorem sec7_smith_core_twisted (hSmith : SmithOmegaPlusEightStatement)
    {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K'] [CharP K' 2] (θ : K ≃+* K')
    {E : Type} [AddCommGroup E] [Module K E] [Module.Finite K E]
    (B : LinearMap.BilinForm K E) (hr : B.IsRefl)
    (U W' R₀ P : Submodule K E) (hW' : W' = B.orthogonal U)
    (hUiso : ∀ x ∈ U, ∀ y ∈ U, B x y = 0)
    (ψ : E →ₗ[K] E) (hψadj : ∀ e e', B (ψ e) e' = B e (ψ e'))
    (hψU : ∀ u ∈ U, ψ u = 0) (hψW : ∀ e, ψ e ∈ W') (hR₀ : R₀ = W'.map ψ) (hP : P = R₀ ⊔ U)
    (hUψ : U ⊓ R₀ = ⊥)
    (hfU : Nat.card U = Nat.card K ^ 8) (hfψ : Nat.card R₀ = Nat.card K ^ 8)
    {H : Type} [Group H] (T : H →* Module.End K E)
    (hTU : ∀ h, ∀ u ∈ U, T h u ∈ U) (hTW : ∀ h, ∀ w ∈ W', T h w ∈ W')
    (hTψ : ∀ h, ∀ w ∈ W', T h (ψ w) - ψ (T h w) ∈ U)
    (φ : H →* GL (Fin 4 ⊕ Fin 4) K') (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K'))
    (hker : ∀ h ∈ φ.ker, ∀ w ∈ W', T h w - w ∈ U)
    (hirr : ∀ A : AddSubgroup E, A ≤ P.toAddSubgroup → U.toAddSubgroup ≤ A →
      (∀ h, ∀ a ∈ A, T h a ∈ A) → A = U.toAddSubgroup ∨ A = P.toAddSubgroup)
    (L : Subgroup H) {u : Fin 4 ⊕ Fin 4 → K'} (hu : StatedQuadPlus 4 K' u = 0) (hu0 : u ≠ 0)
    (hL : L.map φ = rootGroupGL (quadPlus 4 K') u)
    (hLn : ∀ h : H, (∃ c : K', ((φ h : GL (Fin 4 ⊕ Fin 4) K') : Matrix _ _ K').mulVec u = c • u) →
      ∀ l ∈ L, h⁻¹ * l * h ∈ L)
    (A : Submodule K E) (hA : ∀ e, e ∈ A ↔ e ∈ W' ∧ ∀ l ∈ L, T l e - e ∈ U)
    (hAperp : B.orthogonal A = A) (hψA : ∀ a ∈ A, ψ a ∈ A)
    (S : Submodule K E) (hSW : S ≤ W') (hSiso : ∀ x ∈ S, ∀ y ∈ S, B x y = 0)
    (hψS : ∀ s ∈ S, ψ s ∈ S)
    (hTS : ∀ h : H,
      (∃ c : K', ((φ h : GL (Fin 4 ⊕ Fin 4) K') : Matrix _ _ K').mulVec u = c • u) →
      ∀ s ∈ S, T h s ∈ S) :
    ∀ s ∈ S, ψ s ∈ A := by
  classical
  letI : Module K' E := Module.compHom E θ.symm.toRingHom
  have hsm : ∀ (c : K') (x : E), c • x = θ.symm c • x := fun c x => rfl
  haveI hfinE : Finite E := Module.finite_of_finite K
  haveI : Module.Finite K' E := Module.Finite.of_finite
  have hcard : Nat.card K = Nat.card K' := Nat.card_congr θ.toEquiv
  have hK2 : 2 ≤ Nat.card K' := Finite.one_lt_card
  have hfin8 : ∀ N : Submodule K E, Nat.card N = Nat.card K ^ 8 →
      Module.finrank K' (sec7TwistSub θ hsm N) = 8 := by
    intro N hN
    have h := Module.natCard_eq_pow_finrank (K := K') (V := ↥(sec7TwistSub θ hsm N))
    have h2 : Nat.card ↥(sec7TwistSub θ hsm N) = Nat.card ↥N := rfl
    rw [h2, hN, hcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  let T' : H →* Module.End K' E :=
    { toFun := fun h => sec7TwistLin θ hsm (T h)
      map_one' := LinearMap.ext fun x => by simp [sec7TwistLin]
      map_mul' := fun h h' => LinearMap.ext fun x => by simp [sec7TwistLin, map_mul] }
  have hT' : ∀ h x, T' h x = T h x := fun h x => rfl
  have hW'' : sec7TwistSub θ hsm W' =
      (sec7TwistBil θ hsm B).orthogonal (sec7TwistSub θ hsm U) := by
    ext x
    show x ∈ W' ↔ ∀ n ∈ U, θ (B n x) = 0
    rw [hW']
    refine forall₂_congr fun n _ => ?_
    exact (map_eq_zero_iff θ θ.injective).symm
  have key := sec7_smith_core_abstract (K := K') hSmith (E := E) (sec7TwistBil θ hsm B)
    (fun x y h => by
      show θ (B y x) = 0
      rw [map_eq_zero_iff θ θ.injective]
      exact hr x y ((map_eq_zero_iff θ θ.injective).mp h))
    (sec7TwistSub θ hsm U) (sec7TwistSub θ hsm W') (sec7TwistSub θ hsm R₀)
    (sec7TwistSub θ hsm P) hW''
    (fun x hx y hy => by
      show θ (B x y) = 0
      rw [hUiso x hx y hy, map_zero])
    (sec7TwistLin θ hsm ψ) (fun e e' => by
      show θ (B (ψ e) e') = θ (B e (ψ e'))
      rw [hψadj])
    hψU hψW
    (by ext x; rw [hR₀]; exact Iff.rfl)
    (by
      ext x
      show x ∈ P ↔ x ∈ sec7TwistSub θ hsm R₀ ⊔ sec7TwistSub θ hsm U
      rw [hP, Submodule.mem_sup, Submodule.mem_sup]
      exact Iff.rfl)
    (by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h : x ∈ U ⊓ R₀ := hx
      rw [hUψ] at h
      exact h)
    (hfin8 U hfU) (hfin8 R₀ hfψ) T' hTU hTW hTψ φ hφ hker
    (by
      rw [sec7TwistSub_toAddSubgroup, sec7TwistSub_toAddSubgroup]
      exact hirr)
    L hu hu0 hL hLn (sec7TwistSub θ hsm A) hA
    (by
      ext x
      have h1 : x ∈ (sec7TwistBil θ hsm B).orthogonal (sec7TwistSub θ hsm A) ↔
          x ∈ B.orthogonal A := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.mem_orthogonal_iff]
        exact forall₂_congr fun n _ => (map_eq_zero_iff θ θ.injective)
      rw [h1, hAperp]
      exact Iff.rfl)
    hψA (sec7TwistSub θ hsm S) hSW
    (fun x hx y hy => by
      show θ (B x y) = 0
      rw [hSiso x hx y hy, map_zero])
    hψS hTS
  exact key

end

end CFSG.RankThree.GF2n.Stroth80

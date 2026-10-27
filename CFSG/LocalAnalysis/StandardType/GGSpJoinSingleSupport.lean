module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinTorusPerms
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermOrbit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCentralizerLam

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LieType.Universal.Symplectic
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {G : Type} [Group G] [Finite G]

theorem coord_eq_one_of_ncard_le {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {tor : (Fin n → Multiplicative (ZMod p)) →* G} (htor : Function.Injective tor) (c : G)
    (v : Fin n → Multiplicative (ZMod p)) (S : Set G) (hS : S.ncard ≤ 2 * n + 2)
    (hmem : ∀ h ∈ spSignedGroup n p, tor (h v) * c ∈ S) {i j : Fin n} (hij : i ≠ j) :
    v i = 1 ∨ v j = 1 := by
  by_contra hcon
  obtain ⟨hi, hj⟩ := not_or.mp hcon
  have hbig := two_mul_add_two_lt_ncard_image (H := spSignedGroup n p) hp hp2 hn
    (fun σ => coordPerm_mem_spSignedGroup σ) (fun k => coordInv_mem_spSignedGroup k) hij hi hj
  set O : Set (Fin n → Multiplicative (ZMod p)) :=
    (fun h : Equiv.Perm (Fin n → Multiplicative (ZMod p)) => h v) '' (spSignedGroup n p : Set _)
    with hO
  have hsub : (fun w => tor w * c) '' O ⊆ S := by
    rintro _ ⟨w, ⟨h, hh, rfl⟩, rfl⟩
    exact hmem h hh
  have hinj : Function.Injective (fun w => tor w * c) := fun a b hab =>
    htor (mul_right_cancel hab)
  have hle : O.ncard ≤ S.ncard := by
    rw [← Set.ncard_image_of_injective O hinj]
    exact Set.ncard_le_ncard hsub (Set.toFinite S)
  omega

theorem coord_eq_one_of_orbit {F : Type} [Field F] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (h2 : (2 : F) = 0) {Bs X Y : Subgroup G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F} {φ : StatedSp n F →* G}
    (hlift : IsPlaneTorusLift p Bs X ζ φ) {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (n + 1)) A) (hXA : ggAutomizer X Bs ≤ A)
    (hYA : ggAutomizer Y Bs ≤ A)
    (hY : 2 ^ n * n.factorial ≤ Nat.card (ggAutomizer Y Bs)) {z : G} (hz : z ∈ Bs)
    (hzY : z ∈ Subgroup.centralizer (Y : Set G)) {v : Fin n → Multiplicative (ZMod p)} {c : G}
    (hc : c ∈ Subgroup.centralizer (X : Set G))
    (hzv : z = (φ.comp (spPlaneTorus n ζ)) v * c) {i j : Fin n} (hij : i ≠ j) :
    v i = 1 ∨ v j = 1 := by
  classical
  have hfix := ggAutomizer_fixes_of_mem_centralizer hz hzY
  have hncard := ncard_automizer_orbit_le hA hYA hz hfix hY
  refine coord_eq_one_of_ncard_le hp hp2 hn hlift.torus_injective c v
    {w : G | ∃ ψ ∈ A, ((ψ ⟨z, hz⟩ : ↥Bs) : G) = w} hncard ?_ hij
  intro h hh
  obtain ⟨g, hg, hgconj⟩ := spSignedGroup_le_torusPerms h2 hlift hh
  refine ⟨(Subgroup.normalizerMonoidHom (H := Bs)) ⟨g, hg.2⟩, ?_, ?_⟩
  · exact hXA (Subgroup.subset_closure ⟨g, hg.1, hg.2, fun b => rfl⟩)
  · show g * z * g⁻¹ = (φ.comp (spPlaneTorus n ζ)) (h v) * c
    have hcomm : g * c * g⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc g hg.1]
      group
    rw [hzv]
    calc g * ((φ.comp (spPlaneTorus n ζ)) v * c) * g⁻¹
        = (g * (φ.comp (spPlaneTorus n ζ)) v * g⁻¹) * (g * c * g⁻¹) := by group
      _ = (φ.comp (spPlaneTorus n ζ)) (h v) * c := by rw [hgconj v, hcomm]

theorem exists_lift_lam_zero_eq_tor_mulSingle {F : Type} [Field F] {p m : ℕ} (h2 : (2 : F) = 0)
    {Bs X : Subgroup G} {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    {φ : StatedSp (m + 1) F →* G} (hlift : IsPlaneTorusLift p Bs X ζ φ) (i : Fin (m + 1))
    (a : Multiplicative (ZMod p)) :
    ∃ ψ : StatedSp (m + 1) F →* G, Function.Injective ψ ∧ ψ.range = X ∧
      ψ (lam (0 : Fin (m + 1)) (ζ a)) =
        (φ.comp (spPlaneTorus (m + 1) ζ)) (Pi.mulSingle i a) := by
  classical
  obtain ⟨h, hh, hhv⟩ := exists_mem_spSignedGroup_mulSingle (n := m + 1) (p := p) i 0 a
  obtain ⟨g, hg, hgconj⟩ := spSignedGroup_le_torusPerms h2 hlift hh
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp φ, ?_, ?_, ?_⟩
  · exact (MulAut.conj g⁻¹).injective.comp hlift.injective
  · ext x
    constructor
    · rintro ⟨s, rfl⟩
      have hφs : φ s ∈ X := by
        rw [← hlift.range_eq]
        exact ⟨s, rfl⟩
      show g⁻¹ * φ s * g⁻¹⁻¹ ∈ X
      exact mul_mem (mul_mem (inv_mem hg.1) hφs) (by rw [inv_inv]; exact hg.1)
    · intro hx
      have hgx : g * x * g⁻¹ ∈ φ.range := by
        rw [hlift.range_eq]
        exact mul_mem (mul_mem hg.1 hx) (inv_mem hg.1)
      obtain ⟨s, hs⟩ := hgx
      refine ⟨s, ?_⟩
      show g⁻¹ * φ s * g⁻¹⁻¹ = x
      rw [hs]
      group
  · have e1 : φ (lam (0 : Fin (m + 1)) (ζ a)) =
        (φ.comp (spPlaneTorus (m + 1) ζ)) (Pi.mulSingle 0 a) := by
      show φ (lam (0 : Fin (m + 1)) (ζ a)) = φ (spPlaneTorus (m + 1) ζ (Pi.mulSingle 0 a))
      rw [spPlaneTorus_mulSingle]
    show g⁻¹ * φ (lam (0 : Fin (m + 1)) (ζ a)) * g⁻¹⁻¹ =
      (φ.comp (spPlaneTorus (m + 1) ζ)) (Pi.mulSingle i a)
    rw [e1, ← hhv, ← hgconj]
    group

theorem exists_lift_lam_zero_of_orbit {F : Type} [Field F] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 3 ≤ m) (h2 : (2 : F) = 0) {Bs X Y : Subgroup G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F} {φ : StatedSp (m + 1) F →* G}
    (hlift : IsPlaneTorusLift p Bs X ζ φ) {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1 + 1)) A) (hXA : ggAutomizer X Bs ≤ A)
    (hYA : ggAutomizer Y Bs ≤ A)
    (hY : 2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer Y Bs)) {z : G} (hz : z ∈ Bs)
    (hzY : z ∈ Subgroup.centralizer (Y : Set G)) {v : Fin (m + 1) → Multiplicative (ZMod p)}
    {c : G} (hc : c ∈ Subgroup.centralizer (X : Set G))
    (hzv : z = (φ.comp (spPlaneTorus (m + 1) ζ)) v * c) (hv : v ≠ 1) :
    ∃ (ψ : StatedSp (m + 1) F →* G) (g : SpecialLinearGroup (Fin 2) F),
      Function.Injective ψ ∧ ψ.range = X ∧ (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 ∧
        ψ (lam (0 : Fin (m + 1)) g) = (φ.comp (spPlaneTorus (m + 1) ζ)) v := by
  classical
  haveI : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
  obtain ⟨i, hi0⟩ := Function.ne_iff.mp hv
  have hi : v i ≠ 1 := hi0
  have hsingle : ∀ j, j ≠ i → v j = 1 := fun j hji =>
    (coord_eq_one_of_orbit hp hp2 (by omega) h2 hlift hA hXA hYA hY hz hzY hc hzv
      hji.symm).resolve_left hi
  have hv_eq : v = Pi.mulSingle i (v i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [Pi.mulSingle_eq_of_ne hj, hsingle j hj]
  obtain ⟨ψ, hψinj, hψrange, hψval⟩ := exists_lift_lam_zero_eq_tor_mulSingle h2 hlift i (v i)
  have htor : (φ.comp (spPlaneTorus (m + 1) ζ)) v = φ (lam i (ζ (v i))) := by
    conv_lhs => rw [hv_eq]
    show φ (spPlaneTorus (m + 1) ζ (Pi.mulSingle i (v i))) = _
    rw [spPlaneTorus_mulSingle]
  have hg1 : ζ (v i) ≠ 1 := by
    intro h1
    apply hv
    apply hlift.torus_injective
    rw [htor, h1, map_one, map_one, map_one]
  have hvp : (v i) ^ p = 1 := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have h := pow_card_eq_one' (G := Multiplicative (ZMod p)) (x := v i)
    rwa [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
      Nat.card_zmod] at h
  have hgp : (ζ (v i)) ^ p = 1 := by rw [← map_pow, hvp, map_one]
  have htr := trace_ne_zero_of_pow_eq_one hg1 (hp.odd_of_ne_two hp2) hgp
  refine ⟨ψ, ζ (v i), hψinj, hψrange, htr, ?_⟩
  rw [hψval]
  exact congrArg (φ.comp (spPlaneTorus (m + 1) ζ)) hv_eq.symm

end CFSG.StandardType.SpJoin

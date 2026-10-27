module

public import CFSG.LocalAnalysis.StandardType.PhanEStdLevi
public import CFSG.LieType.Steinberg.Collection

import CFSG.LieType.Steinberg.Bridge
import CFSG.LieType.Steinberg.BruhatTwist

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀) (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)

open scoped MatrixGroups commutatorElement

private theorem p9uFD_map_sl2Upper (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀) (c : L.Fld) :
    Matrix.SpecialLinearGroup.map L.θ (sl2Upper c) = sl2Upper (L.θ c) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [sl2Upper]

private theorem p9uFD_map_sl2Lower (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀) (c : L.Fld) :
    Matrix.SpecialLinearGroup.map L.θ (sl2Lower c) = sl2Lower (L.θ c) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [sl2Lower]

private theorem p9uFD_map_torusHom (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀)
    (a : L.Fldˣ) :
    Matrix.SpecialLinearGroup.map L.θ (WeakCT.torusHom L.Fld a) =
      WeakCT.torusHom L.Fld (Units.map L.θ.toMonoidHom a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WeakCT.coe_torusHom, Matrix.SpecialLinearGroup.map_apply_coe, Units.coe_map,
      Units.val_inv_eq_inv_val, map_inv₀]

private theorem p9uFD_phi_ε (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀)
    (hop : ∀ i, F.op i = i) (i : Fin D.rank) (A : SL(2, L.Fld)) :
    F.φ (L.ε i A) = L.ε i (Matrix.SpecialLinearGroup.map L.θ A) := by
  have h : (F.φ).comp (L.ε i) = (L.ε i).comp (Matrix.SpecialLinearGroup.map L.θ) := by
    apply sl2_hom_ext
    · intro c
      simp only [MonoidHom.coe_comp, Function.comp_apply, L.phi_upper i c, hop i,
        p9uFD_map_sl2Upper F L c]
    · intro c
      simp only [MonoidHom.coe_comp, Function.comp_apply, L.phi_lower i c, hop i,
        p9uFD_map_sl2Lower F L c]
  exact DFunLike.congr_fun h A

private theorem p9uFD_isTwist (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀)
    (hop : ∀ i, F.op i = i)
    (hφX : ∀ γ ∈ D.roots, (D.rootGroup γ).map F.φ ≤ D.rootGroup γ) :
    IsTwist D n H 1 F.φ where
  cartan_perm := fun _ _ => rfl
  divisible_perm := fun _ hi => hi
  map_rootGroup := fun γ hγ x hx => hφX γ hγ (Subgroup.mem_map_of_mem F.φ hx)
  map_n := fun i => by rw [F.n_map, hop i]; rfl
  map_torus := fun i h hh => by
    have hh' : h ∈ (H i : Set K) := hh
    rw [← L.diag i] at hh'
    obtain ⟨s, rfl⟩ := hh'
    show F.φ (L.ε i (WeakCT.torusHom L.Fld s)) ∈ H i
    rw [p9uFD_phi_ε F L hop i, p9uFD_map_torusHom F L s]
    exact L.ε_torusHom_mem i _

private theorem p9uFD_upper_mem (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀)
    (hop : ∀ i, F.op i = i) {Y : Type} [Group Y] (β : Y →* K)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range)
    (i : Fin D.rank) (c : L.Fld) (hc : L.θ c = c) :
    L.ε i (sl2Upper c) ∈ β.range := by
  refine hX (Pi.single i 1) ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
    (L.ε i (sl2Upper c)) ?_ ?_
  · change L.ε i (sl2Upper c) ∈ (D.rootGroup (Pi.single i 1) : Set K)
    rw [← L.upper i]
    exact ⟨c, rfl⟩
  · simp only [L.phi_upper i c, hop i, hc]

private theorem p9uFD_lower_mem (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀)
    (hop : ∀ i, F.op i = i) {Y : Type} [Group Y] (β : Y →* K)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range)
    (i : Fin D.rank) (c : L.Fld) (hc : L.θ c = c) :
    L.ε i (sl2Lower c) ∈ β.range := by
  refine hX (-Pi.single i 1)
    ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem (Pi.single i 1)
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i))
    (L.ε i (sl2Lower c)) ?_ ?_
  · change L.ε i (sl2Lower c) ∈ (D.rootGroup (-Pi.single i 1) : Set K)
    rw [← L.lower i]
    exact ⟨c, rfl⟩
  · simp only [L.phi_lower i c, hop i, hc]

private theorem p9uFD_n_mem (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀)
    (hop : ∀ i, F.op i = i) {Y : Type} [Group Y] (β : Y →* K)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range)
    (i : Fin D.rank) : n i ∈ β.range := by
  rw [← L.weyl i, map_mul, map_mul]
  exact mul_mem (mul_mem (p9uFD_upper_mem F L hop β hX i 1 (by simp))
    (p9uFD_lower_mem F L hop β hX i (-1) (by simp)))
    (p9uFD_upper_mem F L hop β hX i 1 (by simp))

private theorem p9uFD_nrep_mem
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀) (hop : ∀ i, F.op i = i)
    {Y : Type} [Group Y] (β : Y →* K)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range)
    (w : W) : nrep hct w ∈ β.range := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced w
  rw [nrep_wordProd hct hω]
  exact Subgroup.list_prod_mem β.range (fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact p9uFD_n_mem F L hop β hX i)

private theorem p9uFD_torusHom_mem (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀)
    (hop : ∀ i, F.op i = i) {Y : Type} [Group Y] (β : Y →* K)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range)
    (i : Fin D.rank) (a : L.Fldˣ) (ha : L.θ a = a) :
    L.ε i (WeakCT.torusHom L.Fld a) ∈ β.range := by
  have hm : WeakCT.torusHom L.Fld a *
      (sl2Upper (1 : L.Fld) * sl2Lower (-1) * sl2Upper (1 : L.Fld)) =
      sl2Upper (a : L.Fld) * sl2Lower (-((a⁻¹ : L.Fldˣ) : L.Fld)) *
        sl2Upper (a : L.Fld) := by
    ext p q
    simp only [Matrix.SpecialLinearGroup.coe_mul, WeakCT.coe_torusHom]
    simp only [sl2Upper, sl2Lower]
    fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmain : L.ε i (WeakCT.torusHom L.Fld a) * n i =
      L.ε i (sl2Upper (a : L.Fld)) * L.ε i (sl2Lower (-((a⁻¹ : L.Fldˣ) : L.Fld))) *
        L.ε i (sl2Upper (a : L.Fld)) := by
    calc L.ε i (WeakCT.torusHom L.Fld a) * n i
        = L.ε i (WeakCT.torusHom L.Fld a *
            (sl2Upper (1 : L.Fld) * sl2Lower (-1) * sl2Upper (1 : L.Fld))) := by
          rw [← L.weyl i, ← map_mul]
      _ = L.ε i (sl2Upper (a : L.Fld) * sl2Lower (-((a⁻¹ : L.Fldˣ) : L.Fld)) *
            sl2Upper (a : L.Fld)) := by rw [hm]
      _ = L.ε i (sl2Upper (a : L.Fld)) * L.ε i (sl2Lower (-((a⁻¹ : L.Fldˣ) : L.Fld))) *
            L.ε i (sl2Upper (a : L.Fld)) := by rw [map_mul, map_mul]
  have hneg : L.θ (-((a⁻¹ : L.Fldˣ) : L.Fld)) = -((a⁻¹ : L.Fldˣ) : L.Fld) := by
    rw [map_neg, Units.val_inv_eq_inv_val, map_inv₀, ha]
  have hθa : L.θ (a : L.Fld) = (a : L.Fld) := ha
  rw [eq_mul_inv_of_mul_eq hmain]
  exact mul_mem (mul_mem (mul_mem (p9uFD_upper_mem F L hop β hX i (a : L.Fld) hθa)
    (p9uFD_lower_mem F L hop β hX i (-((a⁻¹ : L.Fldˣ) : L.Fld)) hneg))
    (p9uFD_upper_mem F L hop β hX i (a : L.Fld) hθa))
    (inv_mem (p9uFD_n_mem F L hop β hX i))

private theorem p9uFD_torus_mem (hext : SteinbergExtras D n H) (F : FrobData D n H w₀)
    {n₀ : K} (L : StdLevi F n₀) (hop : ∀ i, F.op i = i) {Y : Type} [Group Y] (β : Y →* K)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range)
    {t : K} (ht : t ∈ ⨆ i, H i) (htφ : F.φ t = t) : t ∈ β.range := by
  rw [← L.range_torusMap hext] at ht
  obtain ⟨a, rfl⟩ := ht
  have hmap : F.φ (L.torusMap hext a) =
      L.torusMap hext (fun i => Units.map L.θ.toMonoidHom (a i)) := by
    change F.φ (MonoidHom.noncommPiCoprod
        (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld)) (L.torus_commute hext) a) =
      MonoidHom.noncommPiCoprod (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld))
        (L.torus_commute hext) (fun i => Units.map L.θ.toMonoidHom (a i))
    rw [MonoidHom.noncommPiCoprod_apply, MonoidHom.noncommPiCoprod_apply,
      Finset.map_noncommProd]
    apply Finset.noncommProd_congr rfl
    intro i _
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [p9uFD_phi_ε F L hop i, p9uFD_map_torusHom F L (a i)]
  have hfixeq : (fun i => Units.map L.θ.toMonoidHom (a i)) = a :=
    L.torusMap_injective hext (hmap.symm.trans htφ)
  have ha : ∀ i, L.θ (a i) = a i := fun i => by
    have h2 := congrArg (fun u : L.Fldˣ => (u : L.Fld)) (congrFun hfixeq i)
    exact h2
  change MonoidHom.noncommPiCoprod (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld))
    (L.torus_commute hext) a ∈ β.range
  rw [MonoidHom.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem β.range _ (fun i _ => ?_)
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  exact p9uFD_torusHom_mem F L hop β hX i (a i) (ha i)

private theorem p9uFD_pos_mem
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (F : FrobData D n H w₀) {n₀ : K} (L : StdLevi F n₀)
    (hop : ∀ i, F.op i = i) (hdiv : D.divisible = ∅)
    (hφX : ∀ γ ∈ D.roots, (D.rootGroup γ).map F.φ ≤ D.rootGroup γ)
    {Y : Type} [Group Y] (β : Y →* K)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range)
    {u : K} (hu : u ∈ posUnipotent D) (huφ : F.φ u = u) : u ∈ β.range := by
  obtain ⟨l, hnd, hl, hs, hinj⟩ := (isSteinberg_of hct hext).exists_posList
  have hr : ∀ γ ∈ l, γ ∈ D.roots := fun γ hγ => ((hl γ).1 hγ).1.1
  have hle : posUnipotent D ≤ ⨆ v ∈ l, D.rootGroup v := by
    refine iSup₂_le fun γ hγ => ?_
    by_cases hind : (RootSystem.ofCartan D.isFiniteType D.divisible).IsIndiv γ
    · exact le_iSup₂_of_le γ ((hl γ).2 ⟨hγ, hind⟩) le_rfl
    · obtain ⟨δ, hδ, hδ', rfl⟩ :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).exists_eq_two_smul hγ.1 hind
      exact (hext.two_smul_le δ hδ hγ.1).trans (le_iSup₂_of_le δ ((hl δ).2 ⟨
        (RootSystem.ofCartan D.isFiniteType D.divisible).mem_pos_of_two_smul_mem_pos hγ hδ,
        hδ'⟩) le_rfl)
  have hc : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ D.rootGroup a, ∀ y ∈ D.rootGroup b,
      ⁅x, y⁆ ∈ ⨆ c ∈ l, ⨆ (_ : min (ht a) (ht b) < ht c), D.rootGroup c := by
    intro a ha b hb hab x hx y hy
    have hxy := hext.commutator_mem a (hr a ha) b (hr b hb)
      ((RootSystem.ofCartan D.isFiniteType D.divisible).linIndepPair_of_mem_pos ((hl a).1 ha).1
        ((hl a).1 ha).2 ((hl b).1 hb).1 ((hl b).1 hb).2 hab) x hx y hy
    have hle' : (⨆ ε ∈ openCone D.roots a b, D.rootGroup ε) ≤
        ⨆ c ∈ l, ⨆ (_ : min (ht a) (ht b) < ht c), D.rootGroup c := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨c, hc, hlt, hcε⟩ :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).exists_of_mem_openCone_pos
          ((hl a).1 ha).1 ((hl a).1 ha).2 ((hl b).1 hb).1 ((hl b).1 hb).2 hab hε
      have hcL : c ∈ l := (hl c).2 hc
      have hle : D.rootGroup ε ≤ D.rootGroup c := by
        rcases hcε with rfl | rfl
        · exact le_rfl
        · exact hext.two_smul_le c (hr c hcL) hε.1
      exact hle.trans (le_iSup₂_of_le c hcL (le_iSup_of_le hlt le_rfl))
    exact hle' hxy
  obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem D.rootGroup (fun γ => ht γ) hnd hs hc
    u (hle hu)
  have hfix : ∀ γ ∈ l, F.φ (f γ) = f γ := by
    refine hinj (fun γ => F.φ (f γ)) f (fun γ hγ => ?_) hf ?_
    · exact hφX γ (hr γ hγ) (Subgroup.mem_map_of_mem F.φ (hf γ hγ))
    · rw [show (fun γ => F.φ (f γ)) = F.φ ∘ f from rfl, ← List.map_map, ← map_list_prod]
      exact huφ
  refine Subgroup.list_prod_mem β.range (fun x hx => ?_)
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  exact hX γ (hr γ hγ) (f γ) (hf γ hγ) (hfix γ hγ)

include hct hext hw₀ in
theorem frobFix_eq_range_of_descent (hBU : BruhatExtras D H) {n₀ : K} (L : StdLevi F n₀)
    (hop : ∀ i, F.op i = i) (hdiv : D.divisible = ∅)
    (hφX : ∀ γ ∈ D.roots, (D.rootGroup γ).map F.φ ≤ D.rootGroup γ)
    {Y : Type} [Group Y] (β : Y →* K) (hβ : ∀ y, F.φ (β y) = β y)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range) :
    frobFix F = β.range := by
  have hσ : IsTwist D n H 1 F.φ := p9uFD_isTwist F L hop hφX
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨w, -, b, hb, hbφ, u, hu, huφ, rfl⟩ := hσ.fixed_normalForm hct hext hBU hg
    obtain ⟨t, ht, htφ, v, hv, hvφ, rfl⟩ := hσ.fixed_borel hct hext hb hbφ
    exact mul_mem (mul_mem (mul_mem (p9uFD_torus_mem hext F L hop β hX ht htφ)
      (p9uFD_pos_mem hct hext F L hop hdiv hφX β hX hv hvφ))
      (p9uFD_nrep_mem hct F L hop β hX w))
      (p9uFD_pos_mem hct hext F L hop hdiv hφX β hX
        (inversionUnipotent_le_posUnipotent w hu) huφ)
  · rintro _ ⟨y, rfl⟩
    exact hβ y

@[expose] noncomputable def frobFixEquivOfDescent (hBU : BruhatExtras D H) {n₀ : K}
    (L : StdLevi F n₀) (hop : ∀ i, F.op i = i) (hdiv : D.divisible = ∅)
    (hφX : ∀ γ ∈ D.roots, (D.rootGroup γ).map F.φ ≤ D.rootGroup γ)
    {Y : Type} [Group Y] (β : Y →* K) (hβi : Function.Injective β) (hβ : ∀ y, F.φ (β y) = β y)
    (hX : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, F.φ x = x → x ∈ β.range) : Y ≃* frobFix F :=
  (MonoidHom.ofInjective hβi).trans (MulEquiv.subgroupCongr
    (frobFix_eq_range_of_descent hct F hext hw₀ hBU L hop hdiv hφX β hβ hX).symm)

end CFSG.ClassicalInvolution.Phan.PhanE

module

public import CFSG.LocalAnalysis.StandardType.ZS.Support

public section

namespace CFSG.StandardType.ZS

@[expose] def reflSubgroupIn (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (F : Subgroup (U ≃ₗ[ZMod p] U)) (W : Submodule (ZMod p) U) : Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure {g | g ∈ F ∧ IsRefl p g ∧ ∀ v, g v - v ∈ W}

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private def translateSub (W : Submodule (ZMod p) U) : Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {g | ∀ v, g v - v ∈ W}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro g k hg hk v
    have h1 : g (k v) - k v ∈ W := hg (k v)
    have h2 : k v - v ∈ W := hk v
    have h3 : (g * k) v - v = (g (k v) - k v) + (k v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [h3]; exact W.add_mem h1 h2
  inv_mem' := by
    intro g hg v
    change g.symm v - v ∈ W
    have h : g (g.symm v) - g.symm v ∈ W := hg (g.symm v)
    rw [g.apply_symm_apply] at h
    simpa [neg_sub] using W.neg_mem h

theorem reflSubgroupIn_le (F : Subgroup (U ≃ₗ[ZMod p] U)) (W : Submodule (ZMod p) U) :
    reflSubgroupIn p F W ≤ F :=
  (Subgroup.closure_le _).mpr fun _ hg => hg.1

theorem commutatorSpace_reflSubgroupIn_le (F : Subgroup (U ≃ₗ[ZMod p] U))
    (W : Submodule (ZMod p) U) :
    HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p F W) ≤ W := by
  have hle : reflSubgroupIn p F W ≤ translateSub W := by
    rw [reflSubgroupIn]
    exact (Subgroup.closure_le _).mpr fun _ hg => hg.2.2
  rw [commutatorSpace_le_iff]
  intro h hh v
  exact hle hh v

theorem le_reflSubgroupIn {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) (hH : ReflGen p H)
    {W : Submodule (ZMod p) U} (hHW : HardMathSupport.Kantor79.commutatorSpace H ≤ W) :
    H ≤ reflSubgroupIn p F W := by
  rw [hH, reflSubgroupIn]
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨htH, htr⟩
  exact Subgroup.subset_closure ⟨hHF htH, htr, commutatorSpace_le_iff.mp hHW t htH⟩

theorem fixing_sup_reflSubgroupIn_eq {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : ReflGen p F)
    {W : Submodule (ZMod p) U} (hW : ∀ g ∈ F, ∀ w ∈ W, g w ∈ W) :
    (F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U)) ⊔ reflSubgroupIn p F W = F := by
  apply le_antisymm
  · exact sup_le inf_le_left (reflSubgroupIn_le F W)
  · calc F = Subgroup.closure {t | t ∈ F ∧ IsRefl p t} := hF
      _ ≤ (F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U)) ⊔ reflSubgroupIn p F W := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro t ⟨htF, htr⟩
        by_cases hle : HardMathSupport.Kantor79.movedSpace t ≤ W
        · exact Subgroup.mem_sup_right
            (Subgroup.subset_closure ⟨htF, htr, fun v => hle ⟨v, rfl⟩⟩)
        · refine Subgroup.mem_sup_left ⟨htF, ?_⟩
          have htfix : t ∈ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U) := by
            rw [mem_fixingSubgroup_iff]
            intro w hw
            simpa using apply_eq_self_of_not_movedSpace_le (t := t) htr.2
              (fun w hw => hW t htF w hw) hle hw
          exact htfix

private theorem commute_of_mem_fixing_of_isRefl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : QTwoLin.TransvectionFree F) {W : Submodule (ZMod p) U}
    {x y : U ≃ₗ[ZMod p] U} (hxF : x ∈ F) (hxfix : ∀ w ∈ W, x w = w) (hyF : y ∈ F)
    (hyr : IsRefl p y) (hyW : ∀ v, y v - v ∈ W) : Commute x y := by
  have hle_W : HardMathSupport.Kantor79.movedSpace y ≤ W := by
    rintro w ⟨v, rfl⟩
    exact hyW v
  have hconj : ((x * y * x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1 =
      (x : U →ₗ[ZMod p] U).comp
        ((((y : U →ₗ[ZMod p] U) - 1).comp (x.symm : U →ₗ[ZMod p] U))) := by
    ext v
    simp
  have hmoved : HardMathSupport.Kantor79.movedSpace (x * y * x⁻¹) =
      (HardMathSupport.Kantor79.movedSpace y).map (x : U →ₗ[ZMod p] U) := by
    rw [HardMathSupport.Kantor79.movedSpace, HardMathSupport.Kantor79.movedSpace, hconj,
      LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (LinearEquiv.surjective x.symm), Submodule.map_top]
  have hfix_moved : (HardMathSupport.Kantor79.movedSpace y).map (x : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.movedSpace y := by
    apply le_antisymm
    · rintro w ⟨u, hu, rfl⟩
      have hxu : (x : U →ₗ[ZMod p] U) u = u := hxfix u (hle_W hu)
      rw [hxu]
      exact hu
    · intro w hw
      exact ⟨w, hw, hxfix w (hle_W hw)⟩
  have hmoved_eq : HardMathSupport.Kantor79.movedSpace (x * y * x⁻¹) =
      HardMathSupport.Kantor79.movedSpace y := by
    rw [hmoved, hfix_moved]
  have hxyF : x * y * x⁻¹ ∈ F := F.mul_mem (F.mul_mem hxF hyF) (F.inv_mem hxF)
  have hconjRefl : IsRefl p (x * y * x⁻¹) := by
    refine ⟨?_, ?_⟩
    · have hmul : (x * y * x⁻¹) * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
      rw [hmul, hyr.1]; group
    · change Module.finrank (ZMod p)
        (HardMathSupport.Kantor79.movedSpace (x * y * x⁻¹)) = 1
      rw [hmoved_eq]
      exact hyr.2
  have hconj_eq : x * y * x⁻¹ = y :=
    eq_of_movedSpace_eq hp hF hxyF hyF hconjRefl hyr hmoved_eq
  have hxy : x * y = y * x := by
    have h2 : (x * y * x⁻¹) * x = y * x := congrArg (fun z => z * x) hconj_eq
    rw [show (x * y * x⁻¹) * x = x * y by group] at h2
    exact h2
  exact hxy

theorem commute_of_mem_fixing_of_mem_reflSubgroupIn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : QTwoLin.TransvectionFree F) {W : Submodule (ZMod p) U}
    {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U))
    (hy : y ∈ reflSubgroupIn p F W) : Commute x y := by
  have hxF : x ∈ F := hx.1
  have hx2 : x ∈ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U) := hx.2
  have hxfix : ∀ w ∈ W, x w = w :=
    (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)).mp hx2
  have hle : reflSubgroupIn p F W ≤ Subgroup.centralizer ({x} : Set (U ≃ₗ[ZMod p] U)) := by
    rw [reflSubgroupIn]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyF, hyr, hyW⟩
    change y ∈ Subgroup.centralizer ({x} : Set (U ≃ₗ[ZMod p] U))
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact commute_of_mem_fixing_of_isRefl hp hF hxF hxfix hyF hyr hyW
  have hyc : y ∈ Subgroup.centralizer ({x} : Set (U ≃ₗ[ZMod p] U)) := hle hy
  rw [Subgroup.mem_centralizer_iff] at hyc
  exact hyc x (Set.mem_singleton x)

private theorem commutatorSpace_le_centralizerSpace_reflSubgroupIn
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {W : Submodule (ZMod p) U}
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH : H ≤ F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U))
    (hc : ∀ h ∈ H, ∀ y ∈ reflSubgroupIn p F W, Commute h y) :
    HardMathSupport.Kantor79.commutatorSpace H ≤ centralizerSpace (reflSubgroupIn p F W) := by
  rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
  rintro w ⟨h, hh, v, rfl⟩
  change h v - v ∈ centralizerSpace (reflSubgroupIn p F W)
  rw [mem_centralizerSpace]
  intro y hy
  have hhfix : ∀ u ∈ W, h u = u := by
    have hh2 : h ∈ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U) := (hH hh).2
    intro u hu
    simpa using (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)).mp hh2 u hu
  have hyW : y v - v ∈ W :=
    commutatorSpace_le_iff.mp (commutatorSpace_reflSubgroupIn_le F W) y hy v
  have hcomm : Commute h y := hc h hh y hy
  calc y (h v - v) = y (h v) - y v := by rw [map_sub]
    _ = h (y v) - y v := by
          rw [← LinearEquiv.mul_apply, hcomm.eq.symm, LinearEquiv.mul_apply]
    _ = h v - v := by
          have h1 : h (y v) - h v = y v - v := by
            have := hhfix (y v - v) hyW
            rwa [map_sub] at this
          calc h (y v) - y v = (h (y v) - h v) + (h v - y v) := by abel
            _ = (y v - v) + (h v - y v) := by rw [h1]
            _ = h v - v := by abel

theorem inf_commutatorSpace_eq_bot_of_commute {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : ReflGen p F)
    {W : Submodule (ZMod p) U} (hW : ∀ g ∈ F, ∀ w ∈ W, g w ∈ W)
    (hWF : W ⊓ centralizerSpace F = ⊥) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH : H ≤ F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U))
    (hc : ∀ h ∈ H, ∀ y ∈ reflSubgroupIn p F W, Commute h y) :
    W ⊓ HardMathSupport.Kantor79.commutatorSpace H = ⊥ := by
  have hle_cs := commutatorSpace_le_centralizerSpace_reflSubgroupIn hH hc
  have hle : W ⊓ HardMathSupport.Kantor79.commutatorSpace H ≤ centralizerSpace F := by
    rintro u ⟨huW, huH⟩
    have huF2 : u ∈ centralizerSpace (reflSubgroupIn p F W) := hle_cs huH
    have hsub : (F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U)) ⊔
        reflSubgroupIn p F W ≤ fixingSubgroup (U ≃ₗ[ZMod p] U) ({u} : Set U) := by
      refine sup_le ?_ ?_
      · rintro g ⟨hgF, hgW⟩
        have hgW' : g ∈ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U) := hgW
        rw [mem_fixingSubgroup_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        simpa using (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)).mp hgW' u huW
      · intro g hg
        rw [mem_fixingSubgroup_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        simpa using mem_centralizerSpace.mp huF2 g hg
    rw [mem_centralizerSpace]
    intro g hg
    have hgF : g ∈ F := hg
    rw [← fixing_sup_reflSubgroupIn_eq hF hW] at hgF
    have hgu := hsub hgF
    simpa using (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)).mp hgu
  refine (Submodule.eq_bot_iff _).mpr ?_
  intro u hu
  have huF : u ∈ centralizerSpace F := hle ⟨hu.1, hu.2⟩
  have hu' : u ∈ W ⊓ centralizerSpace F := ⟨hu.1, huF⟩
  rw [hWF] at hu'
  simpa using hu'

theorem inf_commutatorSpace_fixing_eq_bot (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) {W : Submodule (ZMod p) U}
    (hW : ∀ g ∈ F, ∀ w ∈ W, g w ∈ W) (hWF : W ⊓ centralizerSpace F = ⊥) :
    W ⊓ HardMathSupport.Kantor79.commutatorSpace
      (F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U) (W : Set U)) = ⊥ :=
  inf_commutatorSpace_eq_bot_of_commute hF.1 hW hWF le_rfl
    (fun _ hh _ hy => commute_of_mem_fixing_of_mem_reflSubgroupIn hp hF.2 hh hy)

theorem fixing_commutatorSpace_eq_bot (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F)
    (hWF : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F = ⊥) :
    F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.commutatorSpace F : Set U) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hWinv : ∀ g ∈ F, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F,
      g w ∈ HardMathSupport.Kantor79.commutatorSpace F := by
    intro g hg w hw
    have hmap := map_commutatorSpace_of_mem_normalizer (H := F) (Subgroup.le_normalizer hg)
    rw [← hmap]
    exact ⟨w, hw, rfl⟩
  have hle : HardMathSupport.Kantor79.movedSpace x ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊓ HardMathSupport.Kantor79.commutatorSpace
        (F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U)
          (HardMathSupport.Kantor79.commutatorSpace F : Set U)) :=
    le_inf (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hx.1)
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hx)
  have hbot : HardMathSupport.Kantor79.movedSpace x = ⊥ := by
    rw [inf_commutatorSpace_fixing_eq_bot hp hF hWinv hWF] at hle
    exact le_antisymm hle bot_le
  have hxsub : ((x : U →ₗ[ZMod p] U) - 1) = 0 := by
    rw [HardMathSupport.Kantor79.movedSpace, LinearMap.range_eq_bot] at hbot
    exact hbot
  ext v
  have := congrArg (fun f : U →ₗ[ZMod p] U => f v) hxsub
  simpa [sub_eq_zero] using this

end CFSG.StandardType.ZS

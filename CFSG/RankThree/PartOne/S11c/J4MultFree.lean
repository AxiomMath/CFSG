module

public import CFSG.RankThree.GroupTheory.SteinbergCEMultiplicityFreeIsometry

public section

namespace CFSG.RankThree.PartOne

section Raw

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] {A : Type*} [Group A]
  {ρ : Representation k A V}

private theorem isIrreducible_of_raw {U : Subrepresentation ρ} (hU0 : U.toSubmodule ≠ ⊥)
    (hirr : ∀ S : Submodule k V, S ≤ U.toSubmodule → (∀ a, ∀ s ∈ S, ρ a s ∈ S) →
      S = ⊥ ∨ S = U.toSubmodule) : U.toRepresentation.IsIrreducible := by
  have hnt : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hU0
  obtain ⟨x, hx⟩ := exists_ne (0 : U.toSubmodule)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : x ∈ (⊤ : Subrepresentation U.toRepresentation).toSubmodule := Submodule.mem_top
    rw [← h] at h1
    exact hx ((Submodule.mem_bot k).mp h1)
  · let T : Submodule k V := S.toSubmodule.map U.toSubmodule.subtype
    have hTle : T ≤ U.toSubmodule := by
      rintro _ ⟨s, _, rfl⟩
      exact s.2
    have hTinv : ∀ a, ∀ t ∈ T, ρ a t ∈ T := by
      rintro a _ ⟨s, hs, rfl⟩
      exact ⟨U.toRepresentation a s, S.apply_mem_toSubmodule a hs, rfl⟩
    rcases hirr T hTle hTinv with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro s hs
      have h1 : (s : V) ∈ T := ⟨s, hs, rfl⟩
      rw [h, Submodule.mem_bot] at h1
      rw [Submodule.mem_bot]
      exact Subtype.ext h1
    · right
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊤
      rw [eq_top_iff]
      intro s _
      have h1 : (s : V) ∈ T := by
        rw [h]
        exact s.2
      obtain ⟨s', hs', hs'e⟩ := h1
      have : s' = s := Subtype.ext hs'e
      rwa [← this]

private theorem nonempty_equiv_dual_of_raw {U : Subrepresentation ρ}
    [FiniteDimensional k U.toSubmodule] (B : U.toSubmodule →ₗ[k] U.toSubmodule →ₗ[k] k)
    (hB1 : ∀ a, (∀ c, B a c = 0) → a = 0) (hB2 : ∀ c, (∀ a, B a c = 0) → c = 0)
    (hB3 : ∀ (e : A) (x y : U.toSubmodule),
      B (U.toRepresentation e x) (U.toRepresentation e y) = B x y) :
    Nonempty (U.toRepresentation.Equiv U.toRepresentation.dual) := by
  have hnd : LinearMap.BilinForm.Nondegenerate B := ⟨hB1, hB2⟩
  refine ⟨Representation.Equiv.mk (LinearMap.BilinForm.toDual B hnd) fun g => ?_⟩
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply]
  have hinv : U.toRepresentation g (U.toRepresentation g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h := hB3 g x (U.toRepresentation g⁻¹ y)
  rw [hinv] at h
  exact h

private theorem isEmpty_equiv_of_raw {U₁ U₂ : Subrepresentation ρ}
    (hne : ∀ φ : U₁.toSubmodule ≃ₗ[k] U₂.toSubmodule, ¬ ∀ (a : A) (m : U₁.toSubmodule),
      φ (U₁.toRepresentation a m) = U₂.toRepresentation a (φ m)) :
    IsEmpty (U₁.toRepresentation.Equiv U₂.toRepresentation) :=
  ⟨fun e => hne e.toLinearEquiv fun a m => e.toIntertwiningMap.isIntertwining _ _ a m⟩

end Raw

section Restrict

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] {A : Type*} [Group A]

private def restrictRep (ρ : Representation k A V) (V' : Submodule k V)
    (hV' : ∀ a, ∀ v ∈ V', ρ a v ∈ V') : Representation k A V' :=
  (Subrepresentation.mk V' fun a _ hv => hV' a _ hv : Subrepresentation ρ).toRepresentation

private def restrictSub (ρ : Representation k A V) (V' : Submodule k V)
    (hV' : ∀ a, ∀ v ∈ V', ρ a v ∈ V') (N : Submodule k V) (hN : ∀ a, ∀ m ∈ N, ρ a m ∈ N) :
    Subrepresentation (restrictRep ρ V' hV') :=
  ⟨N.comap V'.subtype, fun a _ hv => hN a _ hv⟩

private theorem iSupIndep_comap_subtype {ι : Type*} (M : ι → Submodule k V) (hind : iSupIndep M)
    (V' : Submodule k V) : iSupIndep fun i => (M i).comap V'.subtype := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h1 : (x : V) ∈ M i := hx
  have h2 : (x : V) ∈ ⨆ j ≠ i, M j := by
    have : (⨆ j ≠ i, (M j).comap V'.subtype) ≤ (⨆ j ≠ i, M j).comap V'.subtype :=
      iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => M j) j hj)
    exact this hx'
  exact Subtype.ext ((Submodule.disjoint_def.mp (hind i)) _ h1 h2)

private theorem iSup_comap_subtype_eq_top {ι : Type*} (M : ι → Submodule k V)
    (V' : Submodule k V) (hMV' : ∀ i, M i ≤ V') (hsup : ⨆ i, M i = V') :
    ⨆ i, (M i).comap V'.subtype = ⊤ := by
  apply Submodule.map_injective_of_injective (Submodule.injective_subtype V')
  rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
  calc ⨆ i, ((M i).comap V'.subtype).map V'.subtype = ⨆ i, M i :=
        iSup_congr fun i => by rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hMV' i)]
    _ = V' := hsup

section Transport

variable (ρ : Representation k A V) (V' : Submodule k V) (hV' : ∀ a, ∀ v ∈ V', ρ a v ∈ V')
  {N : Submodule k V} (hN : ∀ a, ∀ m ∈ N, ρ a m ∈ N)

private theorem restrictSub_ne_bot (hNV' : N ≤ V') (hN0 : N ≠ ⊥) :
    (restrictSub ρ V' hV' N hN).toSubmodule ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  intro h
  have h1 : (⟨x, hNV' hx⟩ : V') ∈ (restrictSub ρ V' hV' N hN).toSubmodule := hx
  rw [h, Submodule.mem_bot] at h1
  exact hx0 (congrArg Subtype.val h1)

private theorem restrictSub_irred
    (hirr : ∀ S : Submodule k V, S ≤ N → (∀ a, ∀ s ∈ S, ρ a s ∈ S) → S = ⊥ ∨ S = N) :
    ∀ S : Submodule k V', S ≤ (restrictSub ρ V' hV' N hN).toSubmodule →
      (∀ a, ∀ s ∈ S, restrictRep ρ V' hV' a s ∈ S) →
        S = ⊥ ∨ S = (restrictSub ρ V' hV' N hN).toSubmodule := by
  intro S hSN hSinv
  have hmapN : S.map V'.subtype ≤ N := by
    rintro _ ⟨s, hs, rfl⟩
    exact hSN hs
  have hmapinv : ∀ a, ∀ s ∈ S.map V'.subtype, ρ a s ∈ S.map V'.subtype := by
    rintro a _ ⟨s, hs, rfl⟩
    exact ⟨restrictRep ρ V' hV' a s, hSinv a s hs, rfl⟩
  rcases hirr _ hmapN hmapinv with h | h
  · left
    rw [eq_bot_iff]
    intro s hs
    have h1 : (s : V) ∈ S.map V'.subtype := ⟨s, hs, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact Subtype.ext h1
  · right
    refine le_antisymm hSN fun x hx => ?_
    have h1 : (x : V) ∈ S.map V'.subtype := by
      rw [h]
      exact hx
    obtain ⟨s, hs, hsx⟩ := h1
    have : s = x := Subtype.ext hsx
    rwa [← this]

variable {N₁ N₂ : Submodule k V} (hN₁ : ∀ a, ∀ m ∈ N₁, ρ a m ∈ N₁)
  (hN₂ : ∀ a, ∀ m ∈ N₂, ρ a m ∈ N₂)

private theorem isEmpty_equiv_restrictSub (hN₁V' : N₁ ≤ V') (hN₂V' : N₂ ≤ V')
    (hne : ∀ φ : N₁ ≃ₗ[k] N₂, ¬ ∀ (a : A) (m : N₁),
      φ ⟨ρ a m, hN₁ a m m.2⟩ = ⟨ρ a (φ m), hN₂ a _ (φ m).2⟩) :
    IsEmpty ((restrictSub ρ V' hV' N₁ hN₁).toRepresentation.Equiv
      (restrictSub ρ V' hV' N₂ hN₂).toRepresentation) := by
  apply isEmpty_equiv_of_raw
  intro φ hφ
  apply hne ((Submodule.comapSubtypeEquivOfLe hN₁V').symm.trans
    (φ.trans (Submodule.comapSubtypeEquivOfLe hN₂V')))
  intro a m
  apply Subtype.ext
  exact congrArg (fun x : (restrictSub ρ V' hV' N₂ hN₂).toSubmodule => ((x : V') : V))
    (hφ a ((Submodule.comapSubtypeEquivOfLe hN₁V').symm m))

private theorem nonempty_equiv_dual_restrictSub [FiniteDimensional k V] (hNV' : N ≤ V')
    (B : N →ₗ[k] N →ₗ[k] k)
    (hB1 : ∀ a, (∀ c, B a c = 0) → a = 0) (hB2 : ∀ c, (∀ a, B a c = 0) → c = 0)
    (hB3 : ∀ (e : A) (x y : N), B ⟨ρ e x, hN e x x.2⟩ ⟨ρ e y, hN e y y.2⟩ = B x y) :
    Nonempty ((restrictSub ρ V' hV' N hN).toRepresentation.Equiv
      (restrictSub ρ V' hV' N hN).toRepresentation.dual) := by
  let θ : (restrictSub ρ V' hV' N hN).toSubmodule ≃ₗ[k] N :=
    Submodule.comapSubtypeEquivOfLe hNV'
  apply nonempty_equiv_dual_of_raw (B.compl₁₂ θ.toLinearMap θ.toLinearMap)
  · intro a ha
    apply θ.injective
    rw [map_zero]
    apply hB1
    intro c
    have := ha (θ.symm c)
    simpa using this
  · intro c hc
    apply θ.injective
    rw [map_zero]
    apply hB2
    intro a
    have := hc (θ.symm a)
    simpa using this
  · intro e x y
    exact hB3 e (θ x) (θ y)

end Transport

private def restrictAutHom (V' : Submodule k V) (R : Subgroup (V ≃ₗ[k] V))
    (hRV' : ∀ r ∈ R, ∀ v ∈ V', r v ∈ V') : R →* Module.End k V' where
  toFun r := (r.1.toLinearMap).restrict (hRV' r.1 r.2)
  map_one' := by
    ext v
    rfl
  map_mul' x y := by
    ext v
    rfl

end Restrict

theorem multiplicity_free_trivial_on_subspace
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : LinearMap.BilinForm (ZMod 2) V} {A : Type*} [Group A]
    (ρ : Representation (ZMod 2) A V) (hρb : ∀ a x y, b (ρ a x) (ρ a y) = b x y)
    (V' : Submodule (ZMod 2) V) (hV'inv : ∀ a, ∀ v ∈ V', ρ a v ∈ V')
    (hbV' : ∀ v ∈ V', (∀ w ∈ V', b v w = 0) → v = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (ZMod 2) V)
    (hMV' : ∀ i, M i ≤ V') (hMinv : ∀ i, ∀ a, ∀ m ∈ M i, ρ a m ∈ M i)
    (hind : iSupIndep M) (hsup : ⨆ i, M i = V')
    (hirr : ∀ i, ∀ S : Submodule (ZMod 2) V, S ≤ M i → (∀ a, ∀ s ∈ S, ρ a s ∈ S) →
      S = ⊥ ∨ S = M i)
    (hne : ∀ i j, i ≠ j → ∀ φ : M i ≃ₗ[ZMod 2] M j,
      ¬ ∀ (a : A) (m : M i), φ ⟨ρ a m, hMinv i a m m.2⟩ = ⟨ρ a (φ m), hMinv j a _ (φ m).2⟩)
    (hdual : ∀ i, ∃ B : M i →ₗ[ZMod 2] M i →ₗ[ZMod 2] ZMod 2,
      (∀ a, (∀ c, B a c = 0) → a = 0) ∧ (∀ c, (∀ a, B a c = 0) → c = 0) ∧
      ∀ (e : A) (x y : M i), B ⟨ρ e x, hMinv i e x x.2⟩ ⟨ρ e y, hMinv i e y y.2⟩ = B x y)
    (R : Subgroup (V ≃ₗ[ZMod 2] V)) (hRb : ∀ r ∈ R, ∀ x y, b (r x) (r y) = b x y)
    (hR : IsPGroup 2 R) (hRV' : ∀ r ∈ R, ∀ v ∈ V', r v ∈ V')
    (hRA : ∀ (a : A), ∀ r ∈ R, ∃ r' ∈ R, ∀ v : V, r' v = ρ a (r (ρ a⁻¹ v))) :
    ∀ r ∈ R, ∀ v ∈ V', r v = v := by
  let ρ' : Representation (ZMod 2) A V' := restrictRep ρ V' hV'inv
  let b' : LinearMap.BilinForm (ZMod 2) V' := b.compl₁₂ V'.subtype V'.subtype
  have hb' : b'.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply Subtype.ext
    exact hbV' x x.2 fun w hw => hx ⟨w, hw⟩
  have hρb' : ∀ a x y, b' (ρ' a x) (ρ' a y) = b' x y := fun a x y => hρb a x y
  let ι' := {i : ι // M i ≠ ⊥}
  let U : ι' → Subrepresentation ρ' := fun i => restrictSub ρ V' hV'inv (M i.1) (hMinv i.1)
  have hU : DirectSum.IsInternal fun i => (U i).toSubmodule := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact iSupIndep_comap_subtype (fun i : ι' => M i.1) (hind.comp Subtype.val_injective) V'
    · apply iSup_comap_subtype_eq_top (fun i : ι' => M i.1) V' (fun i => hMV' i.1)
      rw [iSup_ne_bot_subtype M]
      exact hsup
  have hirr' : ∀ i, (U i).toRepresentation.IsIrreducible := fun i =>
    isIrreducible_of_raw (restrictSub_ne_bot ρ V' hV'inv (hMinv i.1) (hMV' i.1) i.2)
      (restrictSub_irred ρ V' hV'inv (hMinv i.1) (hirr i.1))
  have hne' : ∀ i j, i ≠ j → IsEmpty ((U i).toRepresentation.Equiv (U j).toRepresentation) :=
    fun i j hij => isEmpty_equiv_restrictSub ρ V' hV'inv (hMinv i.1) (hMinv j.1) (hMV' i.1)
      (hMV' j.1) (hne i.1 j.1 fun h => hij (Subtype.ext h))
  have hdual' : ∀ i, Nonempty ((U i).toRepresentation.Equiv (U i).toRepresentation.dual) := by
    intro i
    obtain ⟨B, hB1, hB2, hB3⟩ := hdual i.1
    exact nonempty_equiv_dual_restrictSub ρ V' hV'inv (hMinv i.1) (hMV' i.1) B hB1 hB2 hB3
  let ψ : R →* LinearMap.GeneralLinearGroup (ZMod 2) V' :=
    (restrictAutHom V' R hRV').toHomUnits
  let R' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V') := ψ.range
  have hRb' : ∀ r ∈ R', ∀ x y,
      b' ((r : Module.End (ZMod 2) V') x) ((r : Module.End (ZMod 2) V') y) = b' x y := by
    rintro _ ⟨s, rfl⟩ x y
    exact hRb s s.2 x y
  have hR' : IsPGroup 2 R' :=
    hR.of_surjective ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
  have hRA' : ∀ a : A, ∀ r ∈ R', ρ'.asGroupHom a * r * (ρ'.asGroupHom a)⁻¹ ∈ R' := by
    rintro a _ ⟨⟨r, hr⟩, rfl⟩
    obtain ⟨r₂, hr₂, hr₂v⟩ := hRA a r hr
    refine ⟨⟨r₂, hr₂⟩, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ← map_inv,
      Representation.asGroupHom_apply, Representation.asGroupHom_apply]
    exact hr₂v x
  open CFSG.RankThree.GroupTheory in
  have hbot :=
    multiplicity_free_self_dual_isometry_action_excludes_normalized_defining_prime_subgroups
      (R := R') hb' ρ' hρb' U hU hirr' hne' hdual' hRb' hR' hRA'
  intro r hr v hv
  have h1 : ψ ⟨r, hr⟩ ∈ R' := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 := congrArg
    (fun u : (Module.End (ZMod 2) V')ˣ => (u : Module.End (ZMod 2) V') ⟨v, hv⟩) h1
  exact congrArg Subtype.val h2

end CFSG.RankThree.PartOne

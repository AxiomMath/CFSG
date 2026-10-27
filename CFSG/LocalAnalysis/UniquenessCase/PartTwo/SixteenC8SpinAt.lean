module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Par
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def SpinEquivariant {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]
    {H₁ : Subgroup (MulAut W₁)} {H₂ : Subgroup (MulAut W₂)} (α : ↥H₁ ≃* ↥H₂) (φ : W₁ ≃* W₂) :
    Prop :=
  ∀ (h : ↥H₁) (w : W₁), φ ((h : MulAut W₁) w) = ((α h : ↥H₂) : MulAut W₂) (φ w)

@[expose] def SpinCentAt (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) : Prop :=
  ∀ c : MulAut W, (∀ h ∈ H, c * h = h * c) → c = 1

@[expose] def SpinFormAt (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) : Prop :=
  ∃ Q : W → ZMod 2, IsPlusQuadF2 Q ∧ QuadInvariant Q H

@[expose] def SpinStabAt (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) : Prop :=
  ∀ Q : W → ZMod 2, IsPlusQuadF2 Q → QuadInvariant Q H →
    (∀ w : W, w ≠ 1 → Q w = 0 → IsE64L3 ↥(ptCent H w)) ∧
      ∀ w : W, Q w ≠ 0 → IsG2Two ↥(ptCent H w)

private lemma spinAt_congr_apply {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]
    (φ : W₁ ≃* W₂) (c : MulAut W₁) (w : W₁) :
    MulAut.congr φ c (φ w) = φ (c w) := by
  simp [MulAut.congr, MulEquiv.trans_apply]

private lemma spinAt_polarQ_comp {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]
    (Q : W₂ → ZMod 2) (φ : W₁ ≃* W₂) (x y : W₁) :
    polarQ (Q ∘ φ) x y = polarQ Q (φ x) (φ y) := by
  simp [polarQ, map_mul]

private lemma spinAt_isQuadF2_comp {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]
    (Q : W₂ → ZMod 2) (φ : W₁ ≃* W₂) (h : IsQuadF2 Q) : IsQuadF2 (Q ∘ φ) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro x y z
    simp only [spinAt_polarQ_comp]
    rw [map_mul, h1]
  · intro x y z
    simp only [spinAt_polarQ_comp]
    rw [map_mul, h2]

private lemma spinAt_isNondegQuadF2_comp {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]
    (Q : W₂ → ZMod 2) (φ : W₁ ≃* W₂) (h : IsNondegQuadF2 Q) :
    IsNondegQuadF2 (Q ∘ φ) := by
  obtain ⟨hq, hnd⟩ := h
  refine ⟨spinAt_isQuadF2_comp Q φ hq, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hnd (φ x) (fun hφx => hx (φ.injective (by simpa using hφx)))
  exact ⟨φ.symm y, by rwa [spinAt_polarQ_comp, φ.apply_symm_apply]⟩

private lemma spinAt_isPlusQuadF2_comp {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]
    (Q : W₂ → ZMod 2) (φ : W₁ ≃* W₂) (h : IsPlusQuadF2 Q) : IsPlusQuadF2 (Q ∘ φ) := by
  obtain ⟨hnd, U, hU, hUrk⟩ := h
  refine ⟨spinAt_isNondegQuadF2_comp Q φ hnd, U.comap φ.toMonoidHom, ?_, ?_⟩
  · intro u hu
    exact hU (φ u) hu
  · have h1 : rk ↥(U.comap φ.toMonoidHom) = rk ↥U := by
      unfold rk
      rw [← Subgroup.card_map_of_injective (K := U.comap φ.toMonoidHom)
        (f := φ.toMonoidHom) φ.injective,
        Subgroup.map_comap_eq_self_of_surjective (f := φ.toMonoidHom) φ.surjective U]
    have h2 : rk ↥(⊤ : Subgroup W₁) = rk ↥(⊤ : Subgroup W₂) := by
      unfold rk
      rw [← Subgroup.card_map_of_injective (K := (⊤ : Subgroup W₁))
        (f := φ.toMonoidHom) φ.injective,
        Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective]
    rw [h1, h2, hUrk]

theorem isE64L3_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsE64L3 Y) :
    IsE64L3 X := by
  obtain ⟨N, hN, hE, hL⟩ := h
  refine ⟨N.comap e.toMonoidHom, hN.comap e.toMonoidHom, ?_, ?_⟩
  · obtain ⟨f⟩ := hE
    refine ⟨(MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm' e N)).trans
      ((MulEquiv.subgroupMap e.symm N).symm.trans f)⟩
  · have he : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
      Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (N.comap e.toMonoidHom) N e he).symm hL

variable {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂] {H₁ : Subgroup (MulAut W₁)}
  {H₂ : Subgroup (MulAut W₂)} {α : ↥H₁ ≃* ↥H₂} {φ : W₁ ≃* W₂}

private noncomputable def spinAt_ptCentEquiv (hφ : SpinEquivariant α φ) (w : W₁) :
    ↥(ptCent H₁ w) ≃* ↥(ptCent H₂ (φ w)) := by
  have hα : ∀ h : ↥H₁, MulAut.congr φ h.1 = ((α h : ↥H₂) : MulAut W₂) := by
    intro h
    ext x
    obtain ⟨y, rfl⟩ := φ.surjective x
    rw [spinAt_congr_apply]
    exact hφ h y
  have hH : H₂ = H₁.map (MulAut.congr φ).toMonoidHom := by
    ext k
    constructor
    · intro hk
      let h : ↥H₁ := α.symm ⟨k, hk⟩
      refine ⟨h.1, h.2, ?_⟩
      have hk' : (α h : ↥H₂) = ⟨k, hk⟩ := α.apply_symm_apply ⟨k, hk⟩
      change MulAut.congr φ h.1 = k
      rw [hα h]
      exact congrArg Subtype.val hk'
    · rintro ⟨h, hh, rfl⟩
      change MulAut.congr φ h ∈ H₂
      rw [hα ⟨h, hh⟩]
      exact (α ⟨h, hh⟩).2
  have hstab : MulAction.stabilizer (MulAut W₂) (φ w) =
      (MulAction.stabilizer (MulAut W₁) w).map (MulAut.congr φ).toMonoidHom := by
    ext k
    constructor
    · intro hk
      refine ⟨(MulAut.congr φ).symm k, ?_, (MulAut.congr φ).apply_symm_apply k⟩
      change (MulAut.congr φ).symm k • w = w
      have hk' : k (φ w) = φ w := by
        simpa [MulAut.smul_def] using (MulAction.mem_stabilizer_iff.mp hk)
      have h2 := congrArg (fun f : MulAut W₂ => f (φ w))
        ((MulAut.congr φ).apply_symm_apply k)
      rw [spinAt_congr_apply] at h2
      rw [hk'] at h2
      simpa [MulAut.smul_def] using φ.injective h2
    · rintro ⟨f, hf, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      have hf' : f w = w := by
        simpa [MulAut.smul_def] using (MulAction.mem_stabilizer_iff.mp hf)
      change MulAut.congr φ f (φ w) = φ w
      rw [spinAt_congr_apply, hf']
  have hpc : ptCent H₂ (φ w) = (ptCent H₁ w).map (MulAut.congr φ).toMonoidHom := by
    rw [ptCent, ptCent, hH, hstab, Subgroup.map_inf _ _ _ (MulAut.congr φ).injective]
  exact (MulEquiv.subgroupMap (MulAut.congr φ) (ptCent H₁ w)).trans
    (MulEquiv.subgroupCongr hpc.symm)

theorem spinCentAt_of_equivariant (hφ : SpinEquivariant α φ) (h : SpinCentAt W₂ H₂) :
    SpinCentAt W₁ H₁ := by
  intro c hc
  have hmain : ∀ x : ↥H₁,
      MulAut.congr φ c * ((α x : ↥H₂) : MulAut W₂) =
        ((α x : ↥H₂) : MulAut W₂) * MulAut.congr φ c := by
    intro x
    ext w
    obtain ⟨y, rfl⟩ := φ.surjective w
    have hcx : c ((x : MulAut W₁) y) = (x : MulAut W₁) (c y) := by
      have h2 := congrArg (fun f : MulAut W₁ => f y) (hc (x : MulAut W₁) x.2)
      simpa [MulAut.mul_apply] using h2
    rw [MulAut.mul_apply, MulAut.mul_apply, ← hφ x y, spinAt_congr_apply, spinAt_congr_apply,
      ← hφ x (c y), hcx]
  have hc' : MulAut.congr φ c = 1 := by
    apply h
    intro k hk
    obtain ⟨x, hx⟩ := α.surjective ⟨k, hk⟩
    have hxk : ((α x : ↥H₂) : MulAut W₂) = k := congrArg Subtype.val hx
    rw [← hxk]
    exact hmain x
  exact (MulAut.congr φ).injective (by rw [hc', map_one])

theorem spinFormAt_of_equivariant (hφ : SpinEquivariant α φ) (h : SpinFormAt W₂ H₂) :
    SpinFormAt W₁ H₁ := by
  obtain ⟨Q₂, hQ₂, hinv₂⟩ := h
  refine ⟨Q₂ ∘ φ, spinAt_isPlusQuadF2_comp Q₂ φ hQ₂, ?_⟩
  intro h hx x
  simp only [Function.comp_apply]
  rw [hφ ⟨h, hx⟩ x]
  exact hinv₂ ((α ⟨h, hx⟩ : ↥H₂) : MulAut W₂) (α ⟨h, hx⟩).2 (φ x)

theorem spinStabAt_of_equivariant (hφ : SpinEquivariant α φ) (h : SpinStabAt W₂ H₂) :
    SpinStabAt W₁ H₁ := by
  intro Q₁ hQ₁ hinv₁
  have hQ₂ : IsPlusQuadF2 (Q₁ ∘ φ.symm) := spinAt_isPlusQuadF2_comp Q₁ φ.symm hQ₁
  have hinv₂ : QuadInvariant (Q₁ ∘ φ.symm) H₂ := by
    intro k hk y
    obtain ⟨x, hx⟩ := α.surjective ⟨k, hk⟩
    have hkx : ((α x : ↥H₂) : MulAut W₂) = k := congrArg Subtype.val hx
    simp only [Function.comp_apply]
    have h1 : φ.symm (k y) = (x : MulAut W₁) (φ.symm y) := by
      apply φ.injective
      rw [MulEquiv.apply_symm_apply, hφ x (φ.symm y), MulEquiv.apply_symm_apply, hkx]
    rw [h1]
    exact hinv₁ (x : MulAut W₁) x.2 (φ.symm y)
  have hres := h (Q₁ ∘ φ.symm) hQ₂ hinv₂
  constructor
  · intro w hw hQw
    have hφw : φ w ≠ 1 := fun h1 => hw (φ.injective (by simpa using h1))
    have h0 : (Q₁ ∘ φ.symm) (φ w) = 0 := by simpa using hQw
    exact isE64L3_of_equiv (spinAt_ptCentEquiv hφ w) (hres.1 (φ w) hφw h0)
  · intro w hQw
    have h0 : (Q₁ ∘ φ.symm) (φ w) ≠ 0 := by simpa using hQw
    exact CFSG.Quasithin.H13.U3.GC137.isG2Two_of_equiv (spinAt_ptCentEquiv hφ w)
      (hres.2 (φ w) h0)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

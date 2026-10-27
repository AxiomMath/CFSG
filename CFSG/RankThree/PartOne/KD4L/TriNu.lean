module

public import CFSG.RankThree.PartOne.KD4T.Normal
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent
public import CFSG.RankThree.PartOne.KD4T.Certs

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KD4T

section Nu

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L]

theorem nuQ_xUnit (k : Fin Tag.D4.rank) (c : L) :
    nuQ τ L ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ =
      xUnit Tag.E6 L (d4Idx k) c :=
  e6Res_xUnit (fun _ hi => lt_six_of_mem_d4Set hi) (d4Idx k) (d4Id_mem k) c

theorem nuQ_yUnit (k : Fin Tag.D4.rank) (c : L) :
    nuQ τ L ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ =
      yUnit Tag.E6 L (d4Idx k) c :=
  e6Res_yUnit (fun _ hi => lt_six_of_mem_d4Set hi) (d4Idx k) (d4Id_mem k) c

omit hτ in
theorem closure_Q_generators : Subgroup.closure
    (((↑) : subsystemGroup τ L (d4Set τ) → ModGL τ L) ⁻¹'
      {g | ∃ i ∈ d4Set τ, ∃ c : L, g = xUnit τ L i c ∨ g = yUnit τ L i c}) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

theorem hom_ext_Q {M : Type*} [Group M] {f g : subsystemGroup τ L (d4Set τ) →* M}
    (hx : ∀ (k : Fin Tag.D4.rank) (c : L),
      f ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ =
        g ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩)
    (hy : ∀ (k : Fin Tag.D4.rank) (c : L),
      f ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ =
        g ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩) : f = g := by
  refine MonoidHom.eq_of_eqOn_dense closure_Q_generators ?_
  rintro ⟨x, hx'⟩ ⟨i, hi, c, h | h⟩
  · obtain ⟨k, rfl⟩ := exists_d4Id_eq hi
    have e : (⟨x, hx'⟩ : subsystemGroup τ L (d4Set τ)) =
        ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ := Subtype.ext h
    rw [e]
    exact hx k c
  · obtain ⟨k, rfl⟩ := exists_d4Id_eq hi
    have e : (⟨x, hx'⟩ : subsystemGroup τ L (d4Set τ)) =
        ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ := Subtype.ext h
    rw [e]
    exact hy k c

theorem nuQ_mem (g : subsystemGroup τ L (d4Set τ)) :
    nuQ τ L g ∈ subsystemGroup Tag.E6 L d4Support := by
  have hle : (⊤ : Subgroup (subsystemGroup τ L (d4Set τ))) ≤
      (subsystemGroup Tag.E6 L d4Support).comap (nuQ τ L) := by
    rw [← closure_Q_generators (τ := τ) (L := L), Subgroup.closure_le]
    rintro ⟨x, hx'⟩ ⟨i, hi, c, h | h⟩
    · obtain ⟨k, rfl⟩ := exists_d4Id_eq hi
      have e : (⟨x, hx'⟩ : subsystemGroup τ L (d4Set τ)) =
          ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ := Subtype.ext h
      rw [SetLike.mem_coe, Subgroup.mem_comap, e, nuQ_xUnit]
      exact xUnit_mem_subsystemGroup (d4Idx_mem k) c
    · obtain ⟨k, rfl⟩ := exists_d4Id_eq hi
      have e : (⟨x, hx'⟩ : subsystemGroup τ L (d4Set τ)) =
          ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ := Subtype.ext h
      rw [SetLike.mem_coe, Subgroup.mem_comap, e, nuQ_yUnit]
      exact yUnit_mem_subsystemGroup (d4Idx_mem k) c
  exact hle (Subgroup.mem_top g)

variable (τ L) in
@[expose] def nuE : subsystemGroup τ L (d4Set τ) →* subsystemGroup Tag.E6 L d4Support :=
  (nuQ τ L).codRestrict _ nuQ_mem

theorem coe_nuE (g : subsystemGroup τ L (d4Set τ)) :
    ((nuE τ L g : subsystemGroup Tag.E6 L d4Support) : ModGL Tag.E6 L) = nuQ τ L g := rfl

theorem nuE_xUnit (k : Fin Tag.D4.rank) (c : L) :
    nuE τ L ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ = d4QX k c :=
  Subtype.ext (nuQ_xUnit k c)

theorem nuE_yUnit (k : Fin Tag.D4.rank) (c : L) :
    nuE τ L ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ = d4QY k c :=
  Subtype.ext (nuQ_yUnit k c)

theorem nuE_injective : Function.Injective (nuE τ L) := fun _ _ h =>
  nuQ_injective (congrArg (fun z : subsystemGroup Tag.E6 L d4Support => (z : ModGL Tag.E6 L)) h)

theorem nuE_surjective : Function.Surjective (nuE τ L) := by
  have hle : (⊤ : Subgroup (subsystemGroup Tag.E6 L d4Support)) ≤ (nuE τ L).range := by
    rw [← closure_d4Q_generators (K := L), Subgroup.closure_le]
    rintro ⟨x, hx'⟩ ⟨i, hi, c, h | h⟩
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      have e : (⟨x, hx'⟩ : subsystemGroup Tag.E6 L d4Support) = d4QX k c := Subtype.ext h
      exact ⟨⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩, by
        rw [nuE_xUnit, e]⟩
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      have e : (⟨x, hx'⟩ : subsystemGroup Tag.E6 L d4Support) = d4QY k c := Subtype.ext h
      exact ⟨⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩, by
        rw [nuE_yUnit, e]⟩
  intro z
  exact hle (Subgroup.mem_top z)

variable (τ L) in
@[expose] def nuEquiv : subsystemGroup τ L (d4Set τ) ≃* subsystemGroup Tag.E6 L d4Support :=
  MulEquiv.ofBijective (nuE τ L) ⟨nuE_injective, nuE_surjective⟩

end Nu

section Frob

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

@[expose] def rhoE (e : ℕ) (k : Fin Tag.D4.rank) : Fin Tag.D4.rank :=
  if e = 1 then d4Rho k else d4Rho (d4Rho k)

theorem d4Theta_d4QX' {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {e : ℕ} (he : e = 1 ∨ e = 2)
    (k : Fin Tag.D4.rank) (c : Ω) : d4Theta Ω Fr e (d4QX k c) = d4QX (rhoE e k) (Fr c) := by
  rcases he with rfl | rfl
  · simpa [rhoE] using (d4Theta_d4QX Fr k c).1
  · simpa [rhoE] using (d4Theta_d4QX Fr k c).2

theorem d4Theta_d4QY' {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {e : ℕ} (he : e = 1 ∨ e = 2)
    (k : Fin Tag.D4.rank) (c : Ω) : d4Theta Ω Fr e (d4QY k c) = d4QY (rhoE e k) (Fr c) := by
  rcases he with rfl | rfl
  · simpa [rhoE] using (d4Theta_d4QY Fr k c).1
  · simpa [rhoE] using (d4Theta_d4QY Fr k c).2

omit hτ [IsAlgClosed L] in
theorem entrywise_xUnit (j : Fin τ.rank) (c : L) :
    Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (xUnit τ L j c) =
      xUnit τ L j (c ^ ℓ ^ f) :=
  (baseChangeGL_eq_entrywise (iterateFrobenius L ℓ f) _).symm.trans
    ((baseChangeGL_xUnit (iterateFrobenius L ℓ f) j c).trans
      (by rw [iterateFrobenius_def]))

omit hτ [IsAlgClosed L] in
theorem entrywise_yUnit (j : Fin τ.rank) (c : L) :
    Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (yUnit τ L j c) =
      yUnit τ L j (c ^ ℓ ^ f) :=
  (baseChangeGL_eq_entrywise (iterateFrobenius L ℓ f) _).symm.trans
    ((baseChangeGL_yUnit (iterateFrobenius L ℓ f) j c).trans
      (by rw [iterateFrobenius_def]))

theorem nuE_psi {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hA : n₁ ∈ Subgroup.normalizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)))
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c)
    {e : ℕ} (he : e = 1 ∨ e = 2) (hπe : ∀ k, π (d4Id k) = d4Id (rhoE e k))
    (g : subsystemGroup τ L (d4Set τ)) :
    nuE τ L (supportedFrobTwistAut ℓ f hA g) =
      d4Theta L (iterateFrobenius L ℓ f) e (nuE τ L g) := by
  have h : (nuE τ L).comp (supportedFrobTwistAut ℓ f hA).toMonoidHom =
      (d4Theta L (iterateFrobenius L ℓ f) e).comp (nuE τ L) := by
    refine hom_ext_Q (fun k c => ?_) (fun k c => ?_)
    · have e1 : (supportedFrobTwistAut ℓ f hA
          ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ : subsystemGroup τ L (d4Set τ)) =
          ⟨xUnit τ L (d4Id (rhoE e k)) (c ^ ℓ ^ f),
            xUnit_mem_subsystemGroup (d4Id_mem _) _⟩ := by
        apply Subtype.ext
        rw [coe_supportedFrobTwistAut, frobTwistGL_apply]
        change n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (xUnit τ L (d4Id k) c) *
          n₁⁻¹ = _
        rw [entrywise_xUnit, (hgen _ (d4Id_mem k) _).1, hπe]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [e1, nuE_xUnit, nuE_xUnit, d4Theta_d4QX' he]
      simp [iterateFrobenius_def]
    · have e1 : (supportedFrobTwistAut ℓ f hA
          ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ : subsystemGroup τ L (d4Set τ)) =
          ⟨yUnit τ L (d4Id (rhoE e k)) (c ^ ℓ ^ f),
            yUnit_mem_subsystemGroup (d4Id_mem _) _⟩ := by
        apply Subtype.ext
        rw [coe_supportedFrobTwistAut, frobTwistGL_apply]
        change n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (yUnit τ L (d4Id k) c) *
          n₁⁻¹ = _
        rw [entrywise_yUnit, (hgen _ (d4Id_mem k) _).2, hπe]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [e1, nuE_yUnit, nuE_yUnit, d4Theta_d4QY' he]
      simp [iterateFrobenius_def]
  exact DFunLike.congr_fun h g

theorem fixed_iff_nuE_mem {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hA : n₁ ∈ Subgroup.normalizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)))
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c)
    {e : ℕ} (he : e = 1 ∨ e = 2) (hπe : ∀ k, π (d4Id k) = d4Id (rhoE e k))
    (g : subsystemGroup τ L (d4Set τ)) :
    n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (g : ModGL τ L) * n₁⁻¹ = g ↔
      nuE τ L g ∈ d4ThetaFixed L (iterateFrobenius L ℓ f) e := by
  rw [mem_d4ThetaFixed, ← nuE_psi (f := f) hA hgen he hπe g]
  constructor
  · intro h
    have h' : supportedFrobTwistAut ℓ f hA g = g := Subtype.ext (by
      rw [coe_supportedFrobTwistAut, frobTwistGL_apply]
      exact h)
    rw [h']
  · intro h
    have h' : supportedFrobTwistAut ℓ f hA g = g := nuE_injective h
    have := congrArg (fun z : subsystemGroup τ L (d4Set τ) => (z : ModGL τ L)) h'
    rw [coe_supportedFrobTwistAut, frobTwistGL_apply] at this
    exact this

end Frob

end CFSG.RankThree.PartOne.KD4L

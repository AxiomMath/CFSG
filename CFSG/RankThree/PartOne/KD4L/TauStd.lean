module

public import CFSG.RankThree.PartOne.KD4L.Layer
public import CFSG.RankThree.PartOne.KD4L.TauComm2

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section E6Level

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

variable (ℓ) in
@[expose] def fixE6 (f : ℕ) (n₂ : ModGL Tag.E6 L) : Subgroup (ModGL Tag.E6 L) :=
  subsystemGroup Tag.E6 L d4Support ⊓
    twistedFixedPoints n₂ (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

omit [IsAlgClosed L] in
theorem mem_fixE6 {f : ℕ} {n₂ z : ModGL Tag.E6 L} :
    z ∈ fixE6 ℓ f n₂ ↔ z ∈ subsystemGroup Tag.E6 L d4Support ∧
      n₂ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) z * n₂⁻¹ = z := by
  rw [fixE6, Subgroup.mem_inf, mem_twistedFixedPoints]

@[expose] def E6Fix (f : ℕ) (n₂ : ModGL Tag.E6 L) : Prop :=
  Finite (fixE6 ℓ f n₂) ∧ CFSG.IsQuasisimple (fixE6 ℓ f n₂) ∧
    ∀ X : Module.End L (RootModule Tag.E6 L),
      X ∈ e6Commutant ((fixE6 ℓ f n₂ : Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) →
      X ∈ e6Commutant ((subsystemGroup Tag.E6 L d4Support : Subgroup (ModGL Tag.E6 L)) :
        Set (ModGL Tag.E6 L))

variable {f : ℕ} (hf : 1 ≤ f)

theorem finite_orbitGroup_tau : Finite (tauDatum L ℓ f hf).orbitGroup := by
  have h1 : Finite (tauDatum L ℓ f hf).fixedGroup := (tauDatum L ℓ f hf).finite_fixedGroup
  rw [fixedGroup_eq_orbitGroupC (L := L) (ℓ := ℓ) hf] at h1
  exact @Finite.of_equiv _ _ h1
    (Subgroup.subgroupOfEquivOfLe (tauDatum L ℓ f hf).orbitGroup_le_adjointGroup).toEquiv

variable (L) in
@[expose] def dN : ModGL Tag.E6 L := diagramMap TwistTag.E6 L

theorem fixE6_dN :
    fixE6 ℓ f (dN L) = (tauDatum L ℓ f hf).orbitGroup := by
  set D := tauDatum L ℓ f hf with hD
  have hQ : D.rootSpanJ = subsystemGroup Tag.E6 L d4Support := rootSpanJ_tau (L := L) (ℓ := ℓ) hf
  have hQA : subsystemGroup Tag.E6 L d4Support ≤ adjointGroup Tag.E6 L := by
    rw [subsystemGroup_eq_rootSpan]
    exact rootSpan_le_adjointGroup L _
  ext z
  rw [mem_fixE6]
  constructor
  · rintro ⟨hz, hzF⟩
    have hzA : z ∈ adjointGroup Tag.E6 L := hQA hz
    have hx : (⟨z, hzA⟩ : adjointGroup Tag.E6 L) ∈ D.fixedGroup := by
      rw [D.mem_fixedGroup]
      refine ⟨hQ ▸ hz, Subtype.ext ?_⟩
      have h1 := tauF_apply (L := L) (ℓ := ℓ) f hf ⟨z, hzA⟩
      exact h1.trans hzF
    rw [fixedGroup_eq_orbitGroupC (L := L) (ℓ := ℓ) hf] at hx
    exact hx
  · intro hz
    have hzA : z ∈ adjointGroup Tag.E6 L := D.orbitGroup_le_adjointGroup hz
    have hx : (⟨z, hzA⟩ : adjointGroup Tag.E6 L) ∈ D.orbitGroupC := hz
    rw [← fixedGroup_eq_orbitGroupC (L := L) (ℓ := ℓ) hf, D.mem_fixedGroup] at hx
    obtain ⟨hz1, hz2⟩ := hx
    refine ⟨hQ ▸ hz1, ?_⟩
    have h1 := tauF_apply (L := L) (ℓ := ℓ) f hf ⟨z, hzA⟩
    have hz2' : tauF L ℓ f hf ⟨z, hzA⟩ = ⟨z, hzA⟩ := hz2
    rw [hz2'] at h1
    exact h1.symm

include hf in
theorem E6Fix_dN : E6Fix (ℓ := ℓ) f (dN L) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fixE6_dN hf]
    exact finite_orbitGroup_tau hf
  · rw [fixE6_dN hf]
    exact tau_isQuasisimple hf
  · intro X hX
    rw [fixE6_dN hf] at hX
    exact e6Commutant_tauLayer hf hX

end E6Level

section Acts

variable {L : Type} [Field L]

@[expose] def Acts (n : ModGL Tag.E6 L) (κ : Equiv.Perm (Fin Tag.D4.rank)) : Prop :=
  ∀ (k : Fin Tag.D4.rank) (c : L),
    n * xUnit Tag.E6 L (d4Idx k) c * n⁻¹ = xUnit Tag.E6 L (d4Idx (κ k)) c ∧
      n * yUnit Tag.E6 L (d4Idx k) c * n⁻¹ = yUnit Tag.E6 L (d4Idx (κ k)) c

theorem Acts.mul {a b : ModGL Tag.E6 L} {α β : Equiv.Perm (Fin Tag.D4.rank)} (ha : Acts a α)
    (hb : Acts b β) : Acts (a * b) (α * β) := by
  intro k c
  refine ⟨?_, ?_⟩
  · calc a * b * xUnit Tag.E6 L (d4Idx k) c * (a * b)⁻¹ =
          a * (b * xUnit Tag.E6 L (d4Idx k) c * b⁻¹) * a⁻¹ := by group
      _ = a * xUnit Tag.E6 L (d4Idx (β k)) c * a⁻¹ := by rw [(hb k c).1]
      _ = xUnit Tag.E6 L (d4Idx ((α * β) k)) c := (ha (β k) c).1
  · calc a * b * yUnit Tag.E6 L (d4Idx k) c * (a * b)⁻¹ =
          a * (b * yUnit Tag.E6 L (d4Idx k) c * b⁻¹) * a⁻¹ := by group
      _ = a * yUnit Tag.E6 L (d4Idx (β k)) c * a⁻¹ := by rw [(hb k c).2]
      _ = yUnit Tag.E6 L (d4Idx ((α * β) k)) c := (ha (β k) c).2

theorem Acts.inv {a : ModGL Tag.E6 L} {α : Equiv.Perm (Fin Tag.D4.rank)} (ha : Acts a α) :
    Acts a⁻¹ α⁻¹ := by
  intro k c
  have hαk : α (α⁻¹ k) = k := by
    rw [Equiv.Perm.inv_def]
    exact Equiv.apply_symm_apply α k
  refine ⟨?_, ?_⟩
  · have h := (ha (α⁻¹ k) c).1
    rw [hαk] at h
    calc a⁻¹ * xUnit Tag.E6 L (d4Idx k) c * a⁻¹⁻¹ =
          a⁻¹ * (a * xUnit Tag.E6 L (d4Idx (α⁻¹ k)) c * a⁻¹) * a := by rw [h]; group
      _ = xUnit Tag.E6 L (d4Idx (α⁻¹ k)) c := by group
  · have h := (ha (α⁻¹ k) c).2
    rw [hαk] at h
    calc a⁻¹ * yUnit Tag.E6 L (d4Idx k) c * a⁻¹⁻¹ =
          a⁻¹ * (a * yUnit Tag.E6 L (d4Idx (α⁻¹ k)) c * a⁻¹) * a := by rw [h]; group
      _ = yUnit Tag.E6 L (d4Idx (α⁻¹ k)) c := by group

theorem Acts.conj {R n₀ : ModGL Tag.E6 L} {κ σ₀ : Equiv.Perm (Fin Tag.D4.rank)} (hR : Acts R κ)
    (h₀ : Acts n₀ σ₀) : Acts (R * n₀ * R⁻¹) (κ * σ₀ * κ⁻¹) :=
  (hR.mul h₀).mul hR.inv

theorem gam_d4Idx : ∀ k : Fin Tag.D4.rank, gam (d4Idx k) = d4Idx (Equiv.swap 1 3 k) := by
  intro k
  fin_cases k <;> decide

theorem dN_mul_xOp (i : Fin Tag.E6.rank) (c : L) :
    (dN L : Module.End L (RootModule Tag.E6 L)) * xOp Tag.E6 L i c =
      xOp Tag.E6 L (gam i) c * (dN L : Module.End L (RootModule Tag.E6 L)) :=
  diagramMap_mul_xOp TwistTag.E6 L i c

theorem dN_mul_yOp (i : Fin Tag.E6.rank) (c : L) :
    (dN L : Module.End L (RootModule Tag.E6 L)) * yOp Tag.E6 L i c =
      yOp Tag.E6 L (gam i) c * (dN L : Module.End L (RootModule Tag.E6 L)) :=
  diagramMap_mul_yOp TwistTag.E6 L i c

theorem acts_dN : Acts (dN L) (Equiv.swap 1 3) := by
  intro k c
  have hk := gam_d4Idx k
  refine ⟨?_, ?_⟩
  · rw [← hk]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_xUnit, dN_mul_xOp, mul_assoc,
      Units.mul_inv, mul_one]
  · rw [← hk]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_yUnit, coe_yUnit, dN_mul_yOp, mul_assoc,
      Units.mul_inv, mul_one]

@[expose] def rhoPerm : Equiv.Perm (Fin Tag.D4.rank) :=
  ⟨d4Rho, d4RhoInv, d4RhoInv_d4Rho, d4Rho_d4RhoInv⟩

theorem acts_d4TrialityRep : Acts (d4TrialityRep L) rhoPerm := fun k c =>
  ⟨d4TrialityRep_conj_xUnit k c, d4TrialityRep_conj_yUnit k c⟩

end Acts

section Conj

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}

omit [IsAlgClosed L] in
theorem fixE6_conj {n₀ R : ModGL Tag.E6 L}
    (hR : (subsystemGroup Tag.E6 L d4Support).map (MulAut.conj R).toMonoidHom =
      subsystemGroup Tag.E6 L d4Support)
    (hFr : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) R = R) :
    fixE6 ℓ f (R * n₀ * R⁻¹) = (fixE6 ℓ f n₀).map (MulAut.conj R).toMonoidHom := by
  ext z
  rw [mem_fixE6, Subgroup.mem_map]
  constructor
  · rintro ⟨hz, hzF⟩
    have hz' : z ∈ (subsystemGroup Tag.E6 L d4Support).map (MulAut.conj R).toMonoidHom :=
      hR.symm ▸ hz
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.1 hz'
    refine ⟨z₀, mem_fixE6.2 ⟨hz₀, ?_⟩, rfl⟩
    have h1 : R * n₀ * R⁻¹ * Units.map (entrywiseHom (iterateFrobenius L ℓ f))
        (R * z₀ * R⁻¹) * (R * n₀ * R⁻¹)⁻¹ = R * z₀ * R⁻¹ := hzF
    rw [map_mul, map_mul, map_inv, hFr] at h1
    calc n₀ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) z₀ * n₀⁻¹ =
          R⁻¹ * (R * n₀ * R⁻¹ * (R * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) z₀ * R⁻¹) *
            (R * n₀ * R⁻¹)⁻¹) * R := by group
      _ = R⁻¹ * (R * z₀ * R⁻¹) * R := by rw [h1]
      _ = z₀ := by group
  · rintro ⟨z₀, hz₀, rfl⟩
    obtain ⟨hz₀Q, hz₀F⟩ := mem_fixE6.1 hz₀
    refine ⟨hR ▸ Subgroup.mem_map_of_mem _ hz₀Q, ?_⟩
    change R * n₀ * R⁻¹ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (R * z₀ * R⁻¹) *
      (R * n₀ * R⁻¹)⁻¹ = R * z₀ * R⁻¹
    rw [map_mul, map_mul, map_inv, hFr]
    calc R * n₀ * R⁻¹ * (R * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) z₀ * R⁻¹) *
          (R * n₀ * R⁻¹)⁻¹ =
        R * (n₀ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) z₀ * n₀⁻¹) * R⁻¹ := by group
      _ = R * z₀ * R⁻¹ := by rw [hz₀F]

omit [IsAlgClosed L] in
theorem E6Fix.conj {n₀ R : ModGL Tag.E6 L}
    (hR : (subsystemGroup Tag.E6 L d4Support).map (MulAut.conj R).toMonoidHom =
      subsystemGroup Tag.E6 L d4Support)
    (hFr : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) R = R) (h : E6Fix (ℓ := ℓ) f n₀) :
    E6Fix (ℓ := ℓ) f (R * n₀ * R⁻¹) := by
  obtain ⟨hfin, hqs, hcomm⟩ := h
  have hinj : Function.Injective (MulAut.conj R).toMonoidHom := (MulAut.conj R).injective
  let e : fixE6 ℓ f n₀ ≃* fixE6 ℓ f (R * n₀ * R⁻¹) :=
    ((fixE6 ℓ f n₀).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr (fixE6_conj (n₀ := n₀) hR hFr).symm)
  refine ⟨Finite.of_equiv _ e.toEquiv, isQuasisimple_of_mulEquiv' e hqs, fun X hX => ?_⟩
  rw [fixE6_conj hR hFr] at hX
  have h' : e6Commutant (((fixE6 ℓ f n₀).map (MulAut.conj R).toMonoidHom : Subgroup _) :
      Set (ModGL Tag.E6 L)) =
      (fun X => (R : Module.End L (RootModule Tag.E6 L)) * X * ((R⁻¹ : ModGL Tag.E6 L) :
        Module.End L (RootModule Tag.E6 L))) '' e6Commutant ((fixE6 ℓ f n₀ : Subgroup _) :
          Set (ModGL Tag.E6 L)) := by
    have := e6Commutant_conj R ((fixE6 ℓ f n₀ : Subgroup _) : Set (ModGL Tag.E6 L))
    rw [← this]
    congr 1
  rw [h'] at hX
  obtain ⟨X₀, hX₀, rfl⟩ := hX
  have hset : (fun g => R * g * R⁻¹) '' ((subsystemGroup Tag.E6 L d4Support : Subgroup _) :
      Set (ModGL Tag.E6 L)) = ((subsystemGroup Tag.E6 L d4Support : Subgroup _) :
      Set (ModGL Tag.E6 L)) := by
    have h1 := congrArg (fun H : Subgroup (ModGL Tag.E6 L) => (H : Set (ModGL Tag.E6 L))) hR
    simp only [Subgroup.coe_map] at h1
    exact h1
  have hQ : e6Commutant ((subsystemGroup Tag.E6 L d4Support : Subgroup _) :
      Set (ModGL Tag.E6 L)) =
      (fun X => (R : Module.End L (RootModule Tag.E6 L)) * X * ((R⁻¹ : ModGL Tag.E6 L) :
        Module.End L (RootModule Tag.E6 L))) '' e6Commutant ((subsystemGroup Tag.E6 L d4Support :
          Subgroup _) : Set (ModGL Tag.E6 L)) := by
    rw [← e6Commutant_conj R, hset]
  rw [hQ]
  exact ⟨X₀, hcomm X₀ hX₀, rfl⟩

end Conj

section Tau

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ] {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
  {σ : Equiv.Perm (Fin Tag.D4.rank)} {n₂ : ModGL Tag.E6 L}

structure StdSwap (n₁ : ModGL τ L) (π : Equiv.Perm (Fin τ.rank))
    (σ : Equiv.Perm (Fin Tag.D4.rank)) : Prop where
  hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ
  hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ
  hπσ : ∀ k, π (d4Id k) = d4Id (σ k)
  hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
    n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c

omit [IsAlgClosed L] in
theorem StdSwap.normalizes (h : StdSwap n₁ π σ) :
    n₁ ∈ Subgroup.normalizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)) :=
  mem_normalizer_subsystemGroup_of_conj h.hπ h.hπ' h.hgen

theorem nuQ_frobTwist (h : StdSwap n₁ π σ) (h₂ : Acts n₂ σ) (g : subsystemGroup τ L (d4Set τ)) :
    nuQ τ L (supportedFrobTwistAut ℓ f h.normalizes g) =
      frobTwistGL Tag.E6 L ℓ f n₂ (nuQ τ L g) := by
  have key : (nuQ τ L).comp (supportedFrobTwistAut ℓ f h.normalizes).toMonoidHom =
      (frobTwistGL Tag.E6 L ℓ f n₂).comp (nuQ τ L) := by
    refine hom_ext_Q (fun k c => ?_) (fun k c => ?_)
    · have e1 : (supportedFrobTwistAut ℓ f h.normalizes
          ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ :
            subsystemGroup τ L (d4Set τ)) =
          ⟨xUnit τ L (d4Id (σ k)) (c ^ ℓ ^ f), xUnit_mem_subsystemGroup (d4Id_mem _) _⟩ := by
        apply Subtype.ext
        rw [coe_supportedFrobTwistAut, frobTwistGL_apply]
        change n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (xUnit τ L (d4Id k) c) *
          n₁⁻¹ = _
        rw [entrywise_xUnit, (h.hgen _ (d4Id_mem k) _).1, h.hπσ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [e1, nuQ_xUnit, nuQ_xUnit]
      change _ = n₂ * Units.map (entrywiseHom (iterateFrobenius L ℓ f))
        (xUnit Tag.E6 L (d4Idx k) c) * n₂⁻¹
      rw [entrywise_xUnit, (h₂ k _).1]
    · have e1 : (supportedFrobTwistAut ℓ f h.normalizes
          ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ :
            subsystemGroup τ L (d4Set τ)) =
          ⟨yUnit τ L (d4Id (σ k)) (c ^ ℓ ^ f), yUnit_mem_subsystemGroup (d4Id_mem _) _⟩ := by
        apply Subtype.ext
        rw [coe_supportedFrobTwistAut, frobTwistGL_apply]
        change n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (yUnit τ L (d4Id k) c) *
          n₁⁻¹ = _
        rw [entrywise_yUnit, (h.hgen _ (d4Id_mem k) _).2, h.hπσ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [e1, nuQ_yUnit, nuQ_yUnit]
      change _ = n₂ * Units.map (entrywiseHom (iterateFrobenius L ℓ f))
        (yUnit Tag.E6 L (d4Idx k) c) * n₂⁻¹
      rw [entrywise_yUnit, (h₂ k _).2]
  exact DFunLike.congr_fun key g

theorem StdSwap.nuQ_mem_fixE6_iff (h : StdSwap n₁ π σ) (h₂ : Acts n₂ σ)
    (g : subsystemGroup τ L (d4Set τ)) :
    nuQ τ L g ∈ fixE6 ℓ f n₂ ↔
      n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (g : ModGL τ L) * n₁⁻¹ = g := by
  rw [mem_fixE6]
  constructor
  · rintro ⟨-, hz⟩
    have h1 : frobTwistGL Tag.E6 L ℓ f n₂ (nuQ τ L g) = nuQ τ L g := hz
    rw [← nuQ_frobTwist h h₂ g] at h1
    have h2 : supportedFrobTwistAut ℓ f h.normalizes g = g := nuQ_injective h1
    have := congrArg (fun z : subsystemGroup τ L (d4Set τ) => (z : ModGL τ L)) h2
    rw [coe_supportedFrobTwistAut, frobTwistGL_apply] at this
    exact this
  · intro hg
    refine ⟨nuQ_mem g, ?_⟩
    have h2 : supportedFrobTwistAut ℓ f h.normalizes g = g :=
      Subtype.ext (by rw [coe_supportedFrobTwistAut, frobTwistGL_apply]; exact hg)
    have h3 := nuQ_frobTwist (ℓ := ℓ) (f := f) h h₂ g
    rw [h2] at h3
    exact h3.symm

@[expose] def StdSwap.layerHom (h : StdSwap n₁ π σ) (h₂ : Acts n₂ σ) :
    stdLayer ℓ f n₁ →* fixE6 ℓ f n₂ :=
  ((nuQ τ L).comp (Subgroup.inclusion (inf_le_left :
      stdLayer ℓ f n₁ ≤ subsystemGroup τ L (d4Set τ)))).codRestrict (fixE6 ℓ f n₂)
    (fun u => (h.nuQ_mem_fixE6_iff h₂ ⟨u, u.2.1⟩).2 u.2.2)

theorem StdSwap.coe_layerHom (h : StdSwap n₁ π σ) (h₂ : Acts n₂ σ) (u : stdLayer ℓ f n₁) :
    ((h.layerHom (ℓ := ℓ) (f := f) h₂ u : fixE6 ℓ f n₂) : ModGL Tag.E6 L) =
      nuQ τ L ⟨(u : ModGL τ L), u.2.1⟩ :=
  rfl

@[expose] def StdSwap.layerEquiv (h : StdSwap n₁ π σ) (h₂ : Acts n₂ σ) :
    stdLayer ℓ f n₁ ≃* fixE6 ℓ f n₂ :=
  MulEquiv.ofBijective (h.layerHom (ℓ := ℓ) (f := f) h₂)
    ⟨fun a b hab => by
      have h1 : nuQ τ L ⟨(a : ModGL τ L), a.2.1⟩ = nuQ τ L ⟨(b : ModGL τ L), b.2.1⟩ := by
        rw [← h.coe_layerHom h₂, ← h.coe_layerHom h₂, hab]
      have h2 := nuQ_injective h1
      exact Subtype.ext (congrArg (fun z : subsystemGroup τ L (d4Set τ) => (z : ModGL τ L)) h2),
    fun z => by
      obtain ⟨g, hg⟩ := nuE_surjective (τ := τ) (L := L) ⟨(z : ModGL Tag.E6 L), (mem_fixE6.1 z.2).1⟩
      have hgz : nuQ τ L g = (z : ModGL Tag.E6 L) := congrArg Subtype.val hg
      have hgf : (g : ModGL τ L) ∈ stdLayer ℓ f n₁ :=
        ⟨g.2, (h.nuQ_mem_fixE6_iff h₂ g).1 (hgz ▸ z.2)⟩
      exact ⟨⟨(g : ModGL τ L), hgf⟩, Subtype.ext (by rw [h.coe_layerHom h₂]; exact hgz)⟩⟩

theorem StdSwap.finite_quasisimple (h : StdSwap n₁ π σ) (h₂ : Acts n₂ σ)
    (hfix : E6Fix (ℓ := ℓ) f n₂) :
    Finite (stdLayer ℓ f n₁) ∧ CFSG.IsQuasisimple (stdLayer ℓ f n₁) := by
  obtain ⟨hfin, hqs, -⟩ := hfix
  let e := h.layerEquiv (ℓ := ℓ) (f := f) h₂
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, isQuasisimple_of_mulEquiv' e.symm hqs⟩

omit [IsAlgClosed L] in
theorem StdSwap.middle_SL2 (h : StdSwap n₁ π σ) (hσ2 : σ 2 = 2) {k : Type} [Field k]
    [Algebra k L] (hk : Nat.card k = ℓ ^ f) (Y : SL(2, k)) :
    simpleRootSL2 τ L (d4Id 2) (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) ∈
      stdLayer ℓ f n₁ :=
  middle_SL2_mem_stdLayer h.hgen (by rw [h.hπσ 2, hσ2]) hk Y

theorem StdSwap.commute_of_commute (h : StdSwap n₁ π σ) (h₂ : Acts n₂ σ)
    (hfix : E6Fix (ℓ := ℓ) f n₂) {q' : ModGL τ L} (hq' : q' ∈ subsystemGroup τ L (d4Set τ))
    (hc : ∀ u ∈ stdLayer ℓ f n₁, q' * u = u * q') :
    ∀ g ∈ subsystemGroup τ L (d4Set τ), q' * g = g * q' := by
  have hX : ((nuQ τ L ⟨q', hq'⟩ : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) ∈
      e6Commutant ((fixE6 ℓ f n₂ : Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) := by
    intro z hz
    obtain ⟨g, hg⟩ := nuE_surjective (τ := τ) (L := L) ⟨z, (mem_fixE6.1 hz).1⟩
    have hgz : nuQ τ L g = z := congrArg Subtype.val hg
    have hgf : (g : ModGL τ L) ∈ stdLayer ℓ f n₁ :=
      ⟨g.2, (h.nuQ_mem_fixE6_iff h₂ g).1 (hgz ▸ hz)⟩
    have hcomm := hc _ hgf
    have h2 : nuQ τ L ⟨q', hq'⟩ * nuQ τ L g = nuQ τ L g * nuQ τ L ⟨q', hq'⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg (nuQ τ L) (Subtype.ext hcomm)
    rw [hgz] at h2
    exact Commute.units_val h2
  have hX' := hfix.2.2 _ hX
  intro g hg
  have h1 := hX' _ (nuQ_mem ⟨g, hg⟩)
  have h1' : Commute (nuQ τ L ⟨q', hq'⟩) (nuQ τ L ⟨g, hg⟩) := by simpa using h1
  have h3 : (⟨q', hq'⟩ * ⟨g, hg⟩ : subsystemGroup τ L (d4Set τ)) =
      ⟨g, hg⟩ * ⟨q', hq'⟩ := nuQ_injective (by rw [map_mul, map_mul]; exact h1'.eq)
  exact congrArg Subtype.val h3

theorem layer_of_swap (h : StdSwap n₁ π σ) (h₂ : Acts n₂ σ) (hσ2 : σ 2 = 2)
    (hfix : E6Fix (ℓ := ℓ) f n₂) {h₀ n : ModGL τ L}
    (hh : h₀ ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h₀ * g * h₀⁻¹) * n₁⁻¹ =
          h₀ * g * h₀⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ subsystemGroup τ L (d4Set τ), (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L))) ∧
      ∀ m : Fin τ.rank, m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  refine layer_of_facts (h.finite_quasisimple h₂ hfix)
    (fun q' hq' hc => h.commute_of_commute h₂ hfix hq' hc) ?_ hh hlang hP
  intro k _ _ hk Y
  exact h.middle_SL2 hσ2 hk Y

end Tau

end CFSG.RankThree.PartOne.KD4L

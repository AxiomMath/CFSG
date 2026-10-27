module

public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

@[expose] def restrictAut {X : Type*} [Group X] {M : Subgroup (MulAut X)} {Y : Subgroup X}
    (hM : ∀ m ∈ M, ∀ y ∈ Y, m y ∈ Y) : ↥M →* MulAut ↥Y where
  toFun m :=
    { toFun := fun y => ⟨(m : MulAut X) y, hM m m.2 y y.2⟩
      invFun := fun y => ⟨(m : MulAut X)⁻¹ y, hM _ (inv_mem m.2) y y.2⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun y y' => Subtype.ext (map_mul _ _ _) }
  map_one' := MulEquiv.ext fun y => Subtype.ext rfl
  map_mul' m m' := MulEquiv.ext fun y => Subtype.ext rfl

theorem exists_trivial_not_mem {X : Type*} [Group X] [Finite X] {M S : Subgroup (MulAut X)}
    {Y : Subgroup X} (hM : ∀ m ∈ M, ∀ y ∈ Y, m y ∈ Y)
    (hidx : Nat.card (MulAut ↥Y) < S.relIndex M) :
    ∃ m ∈ M, m ∉ S ∧ ∀ y ∈ Y, m y = y := by
  classical
  have : Finite (MulAut ↥Y) :=
    Finite.of_injective (fun σ : MulAut ↥Y => (σ : ↥Y → ↥Y)) DFunLike.coe_injective
  by_contra hcon
  push Not at hcon
  have hker : (restrictAut hM).ker ≤ S.subgroupOf M := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    by_contra hmS
    obtain ⟨y, hy, hne⟩ := hcon m m.2 hmS
    apply hne
    have := congrArg (fun σ : MulAut ↥Y => ((σ ⟨y, hy⟩ : ↥Y) : X)) hm
    exact this
  have h1 : (S.subgroupOf M).index ∣ (restrictAut hM).ker.index := Subgroup.index_dvd_of_le hker
  have h2 : (restrictAut hM).ker.index = Nat.card (restrictAut hM).range := Subgroup.index_ker _
  have h3 : Nat.card (restrictAut hM).range ≤ Nat.card (MulAut ↥Y) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have h4 : 0 < (restrictAut hM).ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have := Nat.le_of_dvd h4 h1
  have h5 : S.relIndex M = (S.subgroupOf M).index := rfl
  omega

theorem binaryNaturalSL_map {N : Type} [CommGroup N] [Finite N] {X : Subgroup (MulAut N)}
    {U : Subgroup N} {d a : ℕ} (hX : BinaryNaturalSL X U ⊥ d a) {τ : MulAut N}
    (hτ : τ ∈ Subgroup.normalizer (X : Set (MulAut N))) :
    BinaryNaturalSL X (U.map τ.toMonoidHom) ⊥ d a := by
  classical
  obtain ⟨F, _, _, hF, π, hπ⟩ := hX
  obtain ⟨f, hfs, hfk, hfe⟩ := G64.RealizesVia.exists_secMap rfl hπ
  have hUinv : ∀ h : ↥X, ∀ u ∈ U, (h : MulAut N) u ∈ U := hπ.2.2.2.1
  have hcX : ∀ x ∈ X, τ * x * τ⁻¹ ∈ X := fun x hx => (Subgroup.mem_normalizer_iff.mp hτ x).mp hx
  have hcX' : ∀ x ∈ X, τ⁻¹ * x * τ ∈ X := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hτ) x).mp hx
    simpa using this
  let c : ↥X →* ↥X :=
    { toFun := fun x => ⟨τ * x * τ⁻¹, hcX x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hcsurj : Function.Surjective c := fun x =>
    ⟨⟨τ⁻¹ * x * τ, hcX' x x.2⟩, Subtype.ext (by simp [c, mul_assoc])⟩
  have hmem : ∀ u' ∈ U.map τ.toMonoidHom, τ⁻¹ u' ∈ U := by
    rintro _ ⟨u, hu, rfl⟩
    simpa using hu
  let f' : ↥(U.map τ.toMonoidHom) →* Multiplicative (Fin d → F) :=
    { toFun := fun u' => ((f ⟨τ⁻¹ u', hmem u' u'.2⟩ :
        ↥(FFModel.nat (StatedSL d F)).sec) : (FFModel.nat (StatedSL d F)).Amb)
      map_one' := by
        have : (⟨τ⁻¹ 1, hmem 1 (one_mem _)⟩ : ↥U) = 1 := Subtype.ext (map_one _)
        show ((f ⟨τ⁻¹ 1, hmem 1 (one_mem _)⟩ : ↥(FFModel.nat (StatedSL d F)).sec) :
          (FFModel.nat (StatedSL d F)).Amb) = 1
        rw [this, map_one]
        rfl
      map_mul' := fun u v => by
        have : (⟨τ⁻¹ ((u * v : ↥(U.map τ.toMonoidHom)) : N), hmem _ (u * v).2⟩ : ↥U) =
            ⟨τ⁻¹ u, hmem u u.2⟩ * ⟨τ⁻¹ v, hmem v v.2⟩ := Subtype.ext (map_mul _ _ _)
        simp only [this, map_mul]
        rfl }
  refine ⟨F, inferInstance, inferInstance, hF, c.comp π, G64.realizesVia_nat_of
    (hcsurj.comp hπ.1) bot_le ?_ ?_ f' ?_ ?_ ?_⟩
  · rintro h _ ⟨u, hu, rfl⟩
    refine ⟨((⟨τ⁻¹ * h * τ, hcX' h h.2⟩ : ↥X) : MulAut N) u,
      hUinv ⟨τ⁻¹ * h * τ, hcX' h h.2⟩ u hu, ?_⟩
    simp [MulAut.mul_apply]
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro w
    obtain ⟨u, hu⟩ := hfs ⟨w, Subgroup.mem_top w⟩
    refine ⟨⟨τ u, ⟨u, u.2, rfl⟩⟩, ?_⟩
    have e : (⟨τ⁻¹ (τ u), hmem _ ⟨u, u.2, rfl⟩⟩ : ↥U) = u := Subtype.ext (by simp)
    show ((f ⟨τ⁻¹ (τ u), _⟩ : ↥(FFModel.nat (StatedSL d F)).sec) :
      (FFModel.nat (StatedSL d F)).Amb) = w
    rw [e, hu]
  · intro u'
    have h1 := hfk ⟨τ⁻¹ u', hmem u' u'.2⟩
    constructor
    · intro h
      have h2 : f ⟨τ⁻¹ u', hmem u' u'.2⟩ = 1 := Subtype.ext h
      have h3 := h1.mp h2
      rw [Subgroup.mem_bot] at h3 ⊢
      have := congrArg τ h3
      simpa using this
    · intro h
      rw [Subgroup.mem_bot] at h
      have h2 : τ⁻¹ (u' : N) ∈ (⊥ : Subgroup N) := by
        rw [Subgroup.mem_bot, h, map_one]
      have h3 := h1.mpr h2
      show ((f ⟨τ⁻¹ u', hmem u' u'.2⟩ : ↥(FFModel.nat (StatedSL d F)).sec) :
        (FFModel.nat (StatedSL d F)).Amb) = 1
      rw [h3]
      rfl
  · intro γ u' hu'
    have hU' : ((π γ : ↥X) : MulAut N) (τ⁻¹ u') ∈ U := hUinv _ _ (hmem u' u'.2)
    have e : (⟨τ⁻¹ ((((c.comp π) γ : ↥X) : MulAut N) u'), hmem _ hu'⟩ : ↥U) =
        ⟨((π γ : ↥X) : MulAut N) (τ⁻¹ u'), hU'⟩ := Subtype.ext (by
      show τ⁻¹ ((τ * (π γ : MulAut N) * τ⁻¹) u') = ((π γ : ↥X) : MulAut N) (τ⁻¹ u')
      simp [MulAut.mul_apply])
    show ((f ⟨τ⁻¹ ((((c.comp π) γ : ↥X) : MulAut N) u'), _⟩ :
      ↥(FFModel.nat (StatedSL d F)).sec) : (FFModel.nat (StatedSL d F)).Amb) = _
    rw [e]
    exact hfe γ ⟨τ⁻¹ u', hmem u' u'.2⟩ hU'

end CFSG.Quasithin.H13.L32A.C

module

public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.Background.G93ApplyRestrict
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace G117

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem faithfulOn_top (K : Subgroup (GLV V)) : FaithfulOn K ⊤ :=
  faithfulOn_iff.2 fun _ _ hk => LinearEquiv.ext fun v => hk v Submodule.mem_top

@[expose] noncomputable def restrictRangeTop (K : Subgroup (GLV V)) :
    ↥K ≃* ↥(restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) :=
  restrictRangeEquiv (invariant_top K) (faithfulOn_top K)

theorem natCard_restrictRangeTop (K : Subgroup (GLV V)) :
    Nat.card ↥(restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) = Nat.card ↥K :=
  natCard_restrictRange (invariant_top K) (faithfulOn_top K)

theorem isPermCoreModule_of_restrictRange_top {n : ℕ} {G₀ : Subgroup (Equiv.Perm (Fin n))}
    {K : Subgroup (GLV V)}
    (h : IsPermCoreModule (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) G₀) :
    IsPermCoreModule K G₀ := by
  obtain ⟨φ, β, hsurj, hker, hequ⟩ := h
  refine ⟨(restrictRangeTop K).trans φ,
    (Submodule.topEquiv (R := ZMod 2) (M := V)).toLinearMap ∘ₗ β, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ := hsurj ((Submodule.topEquiv (R := ZMod 2) (M := V)).symm v)
    exact ⟨u, by simp [hu]⟩
  · intro u
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, hker]
  · intro γ u u' hu
    have := hequ (restrictRangeTop K γ) u u' (by simpa using hu)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [this]
    rfl

theorem isNaturalMatrixModule_of_restrictRange_top {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Algebra (ZMod 2) F] {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {K : Subgroup (GLV V)}
    (h : IsNaturalMatrixModule (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) Γ₀) :
    IsNaturalMatrixModule K Γ₀ := by
  obtain ⟨φ, ψ, hψ⟩ := h
  refine ⟨(restrictRangeTop K).trans φ, (Submodule.topEquiv (R := ZMod 2) (M := V)).symm.trans ψ,
    fun k v => ?_⟩
  have e : (Submodule.topEquiv (R := ZMod 2) (M := V)).symm ((k : GLV V) v) =
      ((restrictRangeTop K k : ↥(restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K))) :
        GLV ↥(⊤ : Submodule (ZMod 2) V)) ((Submodule.topEquiv (R := ZMod 2) (M := V)).symm v) :=
    Subtype.ext rfl
  show ψ ((Submodule.topEquiv (R := ZMod 2) (M := V)).symm ((k : GLV V) v)) = _
  rw [e]
  exact hψ (restrictRangeTop K k) _

theorem isG2NaturalModule_of_restrictRange_top {F : Type} [Field F] [Algebra (ZMod 2) F]
    {G₀ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)} {K : Subgroup (GLV V)}
    (h : IsG2NaturalModule (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) G₀) :
    IsG2NaturalModule K G₀ := by
  obtain ⟨φ, π, h1, h2, h3⟩ := h
  refine ⟨(restrictRangeTop K).trans φ,
    (Submodule.topEquiv (R := ZMod 2) (M := V)).toLinearMap ∘ₗ π, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨x, hx, hπ⟩ := h1 ((Submodule.topEquiv (R := ZMod 2) (M := V)).symm v)
    exact ⟨x, hx, by simp [hπ]⟩
  · intro x hx
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]
    exact h2 x hx
  · intro k x hx
    have := h3 (restrictRangeTop K k) x hx
    show (Submodule.topEquiv (R := ZMod 2) (M := V)) (π (((φ (restrictRangeTop K k) : ↥G₀) :
      quasithinZorn F ≃ₗ[F] quasithinZorn F) x)) = _
    rw [this]
    rfl

section Centralizer

variable {K : Subgroup (GLV V)}

theorem restrictEquiv_mem_endCommutant {c : GLV V} (hc : ∀ k ∈ K, k * c = c * k) :
    ((restrictEquiv c ⊤ (conjSub_top c) : GLV ↥(⊤ : Submodule (ZMod 2) V)) :
        ↥(⊤ : Submodule (ZMod 2) V) →ₗ[ZMod 2] ↥(⊤ : Submodule (ZMod 2) V)) ∈
      endCommutant (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) := by
  rw [endCommutant, Subalgebra.mem_centralizer_iff]
  rintro g ⟨h', hh', rfl⟩
  obtain ⟨h, hh, rfl⟩ := (mem_restrictRange_iff' (invariant_top K)).1 hh'
  ext i
  show h (c (i : V)) = c (h (i : V))
  exact congrArg (fun g : GLV V => g (i : V)) (hc h hh)

@[expose] noncomputable def centralizerToEnd (K : Subgroup (GLV V)) :
    ↥(Subgroup.centralizer (K : Set (GLV V))) →*
      ↥(endCommutant (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K))) where
  toFun c := ⟨((restrictEquiv (c : GLV V) ⊤ (conjSub_top _) : GLV ↥(⊤ : Submodule (ZMod 2) V)) :
      ↥(⊤ : Submodule (ZMod 2) V) →ₗ[ZMod 2] ↥(⊤ : Submodule (ZMod 2) V)),
    restrictEquiv_mem_endCommutant fun k hk => Subgroup.mem_centralizer_iff.1 c.2 k hk⟩
  map_one' := Subtype.ext (LinearMap.ext fun _ => Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (LinearMap.ext fun _ => Subtype.ext rfl)

theorem centralizerToEnd_injective (K : Subgroup (GLV V)) :
    Function.Injective (centralizerToEnd K) := by
  intro a b h
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have := congrArg (fun z : ↥(endCommutant (restrictRange K (⊤ : Submodule (ZMod 2) V)
    (invariant_top K))) => ((z : Module.End (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V))
      ⟨v, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) V))) h
  exact congrArg Subtype.val this

theorem exists_centralizer_embedding {e : ℕ}
    (hE : EndIsField (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) e) :
    ∃ f : ↥(Subgroup.centralizer (K : Set (GLV V))) →* (GaloisField 2 e)ˣ,
      Function.Injective f := by
  obtain ⟨ε⟩ := hE
  refine ⟨((ε : _ →* GaloisField 2 e).comp (centralizerToEnd K)).toHomUnits, ?_⟩
  intro a b hab
  have h1 : (ε : _ →* GaloisField 2 e) (centralizerToEnd K a) =
      (ε : _ →* GaloisField 2 e) (centralizerToEnd K b) := congrArg Units.val hab
  exact centralizerToEnd_injective K (ε.injective h1)

theorem natCard_centralizer_dvd {e : ℕ} (he : e ≠ 0)
    (hE : EndIsField (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) e) :
    Nat.card ↥(Subgroup.centralizer (K : Set (GLV V))) ∣ 2 ^ e - 1 := by
  obtain ⟨f, hf⟩ := exists_centralizer_embedding hE
  have h1 := Subgroup.card_dvd_of_injective f hf
  have h2 : Nat.card (GaloisField 2 e)ˣ = 2 ^ e - 1 := by
    rw [Nat.card_units, GaloisField.card 2 e he]
  rwa [h2] at h1

theorem centralizer_pow_eq_one {e : ℕ} (he : e ≠ 0)
    (hE : EndIsField (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) e) {c : GLV V}
    (hc : c ∈ Subgroup.centralizer (K : Set (GLV V))) : c ^ (2 ^ e - 1) = 1 := by
  obtain ⟨f, hf⟩ := exists_centralizer_embedding hE
  have h2 : Nat.card (GaloisField 2 e)ˣ = 2 ^ e - 1 := by
    rw [Nat.card_units, GaloisField.card 2 e he]
  have h3 : f ⟨c, hc⟩ ^ (2 ^ e - 1) = 1 := by
    rw [← h2]
    exact pow_card_eq_one'
  have h4 : f (⟨c, hc⟩ ^ (2 ^ e - 1)) = f 1 := by rw [map_pow, map_one, h3]
  have h5 := congrArg Subtype.val (hf h4)
  simpa using h5

theorem eq_one_of_commute_of_endIsField_one
    (hE : EndIsField (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K)) 1) {c : GLV V}
    (hc : ∀ k ∈ K, k * c = c * k) : c = 1 := by
  have h := centralizer_pow_eq_one one_ne_zero hE (c := c) (Subgroup.mem_centralizer_iff.2 hc)
  simpa using h

end Centralizer

@[expose] def conjAutHom {Γ H : Subgroup (GLV V)} (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) :
    ↥Γ →* MulAut ↥H where
  toFun γ :=
    { toFun := fun h => ⟨(γ : GLV V) * h * (γ : GLV V)⁻¹, hN γ γ.2 h h.2⟩
      invFun := fun h => ⟨(γ : GLV V)⁻¹ * h * (γ : GLV V), by
        simpa using hN γ⁻¹ (Γ.inv_mem γ.2) h h.2⟩
      left_inv := fun h => Subtype.ext (by group)
      right_inv := fun h => Subtype.ext (by group)
      map_mul' := fun a b => Subtype.ext (by
        show (γ : GLV V) * ((a : GLV V) * b) * (γ : GLV V)⁻¹ =
          ((γ : GLV V) * a * (γ : GLV V)⁻¹) * ((γ : GLV V) * b * (γ : GLV V)⁻¹)
        group) }
  map_one' := MulEquiv.ext fun h => Subtype.ext (by
    show ((1 : ↥Γ) : GLV V) * h * ((1 : ↥Γ) : GLV V)⁻¹ = h
    simp)
  map_mul' a b := MulEquiv.ext fun h => Subtype.ext (by
    show ((a * b : ↥Γ) : GLV V) * h * ((a * b : ↥Γ) : GLV V)⁻¹ =
      (a : GLV V) * ((b : GLV V) * h * (b : GLV V)⁻¹) * (a : GLV V)⁻¹
    simp [mul_assoc])

theorem ker_conjAutHom {Γ H : Subgroup (GLV V)} (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) :
    (conjAutHom hN).ker = (Γ ⊓ Subgroup.centralizer (H : Set (GLV V))).subgroupOf Γ := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨γ.2, fun x hx => ?_⟩
    have := congrArg (fun f : MulAut ↥H => ((f ⟨x, hx⟩ : ↥H) : GLV V)) h
    simp only [MulAut.one_apply] at this
    change (γ : GLV V) * x * (γ : GLV V)⁻¹ = x at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · rintro ⟨-, h⟩
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show (γ : GLV V) * x * (γ : GLV V)⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact (h x x.2).symm

theorem natCard_le_mul_natCard_ker {G N : Type*} [Group G] [Group N] [Finite G] [Finite N]
    (f : G →* N) : Nat.card G ≤ Nat.card N * Nat.card f.ker := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (G ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card f.range ≤ Nat.card N :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [h1, h2]
  exact Nat.mul_le_mul_right _ h3

theorem natCard_le_aut_mul_centralizer [Finite V] {Γ H : Subgroup (GLV V)}
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) :
    Nat.card ↥Γ ≤ Nat.card (MulAut ↥H) *
      Nat.card ↥(Γ ⊓ Subgroup.centralizer (H : Set (GLV V))) := by
  have h1 := natCard_le_mul_natCard_ker (conjAutHom hN)
  rw [ker_conjAutHom hN] at h1
  have h2 : Nat.card ((Γ ⊓ Subgroup.centralizer (H : Set (GLV V))).subgroupOf Γ) =
      Nat.card ↥(Γ ⊓ Subgroup.centralizer (H : Set (GLV V))) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rwa [h2] at h1

end G117

end G11

end CFSG.Quasithin

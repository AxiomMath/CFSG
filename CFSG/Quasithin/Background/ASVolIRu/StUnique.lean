module

public import CFSG.Quasithin.Background.ASVolIRu.StUniqueDefs
public import CFSG.Quasithin.Background.ASVolIRu.StUniqueFlags

public section

namespace CFSG.Quasithin.RuType

namespace StUnique

open scoped MatrixGroups Matrix

section Generic

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
  (ρ : Representation (ZMod 2) SL(3, ZMod 2) M)

theorem rho_ne_zero (g : SL(3, ZMod 2)) {m : M} (hm : m ≠ 0) : ρ g m ≠ 0 := by
  intro h
  apply hm
  have e : ρ g⁻¹ (ρ g m) = m := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← e, h, map_zero]

theorem exists_fixed_vector [Finite M] (hcard : Nat.card M = 2 ^ 8) :
    ∃ m : M, m ≠ 0 ∧ ∀ u ∈ MulAction.stabilizer SL(3, ZMod 2) x₀, ρ u m = m := by
  have hP : IsPGroup 2 (MulAction.stabilizer SL(3, ZMod 2) x₀) :=
    IsPGroup.of_card (n := 3) (by rw [card_stabilizer]; norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction (MulAction.stabilizer SL(3, ZMod 2) x₀) M :=
    { smul := fun u m => ρ u m
      one_smul := fun m => by
        show ρ ((1 : MulAction.stabilizer SL(3, ZMod 2) x₀) : SL(3, ZMod 2)) m = m
        simp
      mul_smul := fun u v m => by
        show ρ ((u * v : MulAction.stabilizer SL(3, ZMod 2) x₀) : SL(3, ZMod 2)) m =
          ρ u (ρ v m)
        simp }
  obtain ⟨b, hb, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point M
    (by rw [hcard]; norm_num) (a := 0) (fun u => by
      show ρ u 0 = 0
      simp)
  exact ⟨b, fun h => hne h.symm, fun u hu => hb ⟨u, hu⟩⟩

theorem exists_equivariant_surjection [Finite M] (hcard : Nat.card M = 2 ^ 8)
    (hirr : ∀ N : Submodule (ZMod 2) M, (∀ g : SL(3, ZMod 2), ∀ m ∈ N, ρ g m ∈ N) →
      N = ⊥ ∨ N = ⊤) :
    ∃ φ : FlagMod →ₗ[ZMod 2] M, (∀ g f, φ (modAct g f) = ρ g (φ f)) ∧ Function.Surjective φ := by
  obtain ⟨m, hm0, hm⟩ := exists_fixed_vector ρ hcard
  choose rep hrep using flag_transitive
  have key : ∀ (g : SL(3, ZMod 2)) (y : Flag), ρ g (ρ (rep y) m) = ρ (rep (g • y)) m := by
    intro g y
    have hu : (rep (g • y))⁻¹ * (g * rep y) ∈ MulAction.stabilizer SL(3, ZMod 2) x₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hrep y, inv_smul_eq_iff]
      exact (hrep (g • y)).symm
    calc ρ g (ρ (rep y) m) = ρ (g * rep y) m := by rw [map_mul]; rfl
      _ = ρ (rep (g • y) * ((rep (g • y))⁻¹ * (g * rep y))) m := by rw [mul_inv_cancel_left]
      _ = ρ (rep (g • y)) (ρ ((rep (g • y))⁻¹ * (g * rep y)) m) := by rw [map_mul]; rfl
      _ = ρ (rep (g • y)) m := by rw [hm _ hu]
  have hφ : ∀ (g : SL(3, ZMod 2)) (f : FlagMod),
      Fintype.linearCombination (ZMod 2) (fun x => ρ (rep x) m) (modAct g f) =
        ρ g (Fintype.linearCombination (ZMod 2) (fun x => ρ (rep x) m) f) := by
    intro g f
    simp only [Fintype.linearCombination_apply, map_sum, map_smul]
    refine Fintype.sum_equiv (MulAction.toPerm g).symm _ _ fun x => ?_
    simp only [modAct_apply, MulAction.toPerm_symm_apply, key, smul_inv_smul]
  refine ⟨Fintype.linearCombination (ZMod 2) (fun x => ρ (rep x) m), hφ, ?_⟩
  set φ := Fintype.linearCombination (ZMod 2) (fun x => ρ (rep x) m) with hφdef
  have hrange : LinearMap.range φ = ⊤ := by
    rcases hirr (LinearMap.range φ) (by
      intro g y hy
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
      exact ⟨modAct g f, hφ g f⟩) with h | h
    · exfalso
      have h1 : φ (Pi.single x₀ 1) ∈ LinearMap.range φ := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot, hφdef, Fintype.linearCombination_apply_single, one_smul] at h1
      exact rho_ne_zero ρ (rep x₀) hm0 h1
    · exact h
  exact LinearMap.range_eq_top.mp hrange

theorem card_span_range_le {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    {ι : Type*} [Fintype ι] (v : ι → N) :
    Nat.card (Submodule.span (ZMod 2) (Set.range v)) ≤ 2 ^ Fintype.card ι := by
  rw [← Fintype.range_linearCombination]
  have h1 := Finite.card_range_le (⇑(Fintype.linearCombination (ZMod 2) v))
  rw [← LinearMap.coe_range] at h1
  refine h1.trans_eq ?_
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := ι)]

theorem eq_bot_of_small (hcard : Nat.card M = 2 ^ 8)
    (hirr : ∀ N : Submodule (ZMod 2) M, (∀ g : SL(3, ZMod 2), ∀ m ∈ N, ρ g m ∈ N) →
      N = ⊥ ∨ N = ⊤)
    {ι : Type} [Fintype ι] (hι : Fintype.card ι ≤ 7) (v : ι → M)
    (hinv : ∀ (g : SL(3, ZMod 2)) (m : M), m ∈ Submodule.span (ZMod 2) (Set.range v) →
      ρ g m ∈ Submodule.span (ZMod 2) (Set.range v)) :
    Submodule.span (ZMod 2) (Set.range v) = ⊥ := by
  rcases hirr _ hinv with h | h
  · exact h
  · exfalso
    have h1 := card_span_range_le v
    rw [h] at h1
    have h2 : Nat.card (⊤ : Submodule (ZMod 2) M) = Nat.card M :=
      Nat.card_congr Submodule.topEquiv.toEquiv
    have h3 : 2 ^ Fintype.card ι ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hι
    rw [h2, hcard] at h1
    omega

theorem map_eq_bot_of_invariant (hcard : Nat.card M = 2 ^ 8)
    (hirr : ∀ N : Submodule (ZMod 2) M, (∀ g : SL(3, ZMod 2), ∀ m ∈ N, ρ g m ∈ N) →
      N = ⊥ ∨ N = ⊤)
    {φ : FlagMod →ₗ[ZMod 2] M} (hφ : ∀ g f, φ (modAct g f) = ρ g (φ f))
    {E : Submodule (ZMod 2) FlagMod} {ι : Type} [Fintype ι] (hι : Fintype.card ι ≤ 7)
    (w : ι → FlagMod) (hE : E = Submodule.span (ZMod 2) (Set.range w))
    (hEinv : ∀ (g : SL(3, ZMod 2)) {f : FlagMod}, f ∈ E → modAct g f ∈ E) :
    Submodule.map φ E = ⊥ := by
  have hN : Submodule.map φ E = Submodule.span (ZMod 2) (Set.range (φ ∘ w)) := by
    rw [hE, Submodule.map_span, Set.range_comp]
  rw [hN]
  refine eq_bot_of_small ρ hcard hirr hι (φ ∘ w) ?_
  rw [← hN]
  rintro g _ ⟨f, hf, rfl⟩
  exact ⟨modAct g f, hEinv g hf, hφ g f⟩

theorem stUnique_core [Finite M] (hcard : Nat.card M = 2 ^ 8)
    (hirr : ∀ N : Submodule (ZMod 2) M, (∀ g : SL(3, ZMod 2), ∀ m ∈ N, ρ g m ∈ N) →
      N = ⊥ ∨ N = ⊤) :
    ∃ χ : M →+ Matrix (Fin 3) (Fin 3) (ZMod 2),
      Function.Injective χ ∧ (∀ m, IsTraceZero (χ m)) ∧
      (∀ A, IsTraceZero A → ∃ m, χ m = A) ∧
      ∀ (g : SL(3, ZMod 2)) (m : M), χ (ρ g m) = stAct g (χ m) := by
  obtain ⟨φ, hφ, hsurj⟩ := exists_equivariant_surjection ρ hcard hirr
  have hp : Submodule.map φ pointSpan = ⊥ :=
    map_eq_bot_of_invariant ρ hcard hirr hφ (ι := NZ) (by rw [card_NZ])
      (fun p => pointVec p.1) pointSpan_eq (fun g _ hf => modAct_mem_pointSpan g hf)
  have hl : Submodule.map φ lineSpan = ⊥ :=
    map_eq_bot_of_invariant ρ hcard hirr hφ (ι := NZ) (by rw [card_NZ])
      (fun l => lineVec l.1) lineSpan_eq (fun g _ hf => modAct_mem_lineSpan g hf)
  have hstmem : ∀ (g : SL(3, ZMod 2)) (x : slSub), stAct g x.1 ∈ slSub := fun g x =>
    stAct_mem_slSub g x.2
  let Ψ : slSub →ₗ[ZMod 2] M := (φ ∘ₗ betaMap).domRestrict slSub
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨f, rfl⟩ := hsurj y
    obtain ⟨A, hA, e₁, he₁, e₂, he₂, rfl⟩ := flagMod_decomp f
    refine ⟨⟨A, mem_slSub.mpr hA⟩, ?_⟩
    have h1 : φ e₁ = 0 := (Submodule.mem_bot _).mp (hp ▸ Submodule.mem_map_of_mem he₁)
    have h2 : φ e₂ = 0 := (Submodule.mem_bot _).mp (hl ▸ Submodule.mem_map_of_mem he₂)
    simp [Ψ, h1, h2]
  have hΨbij : Function.Bijective Ψ :=
    hΨsurj.bijective_of_nat_card_le (by rw [card_slSub, hcard])
  let e : slSub ≃ₗ[ZMod 2] M := LinearEquiv.ofBijective Ψ hΨbij
  have he : ∀ x, e x = Ψ x := fun x => rfl
  have hΨeq : ∀ (g : SL(3, ZMod 2)) (x : slSub), Ψ ⟨stAct g x.1, hstmem g x⟩ = ρ g (Ψ x) := by
    intro g x
    simp only [Ψ, LinearMap.domRestrict_apply, LinearMap.comp_apply, betaMap_stAct, hφ]
  refine ⟨{ toFun := fun m => (e.symm m).1
            map_zero' := by simp
            map_add' := fun m n => by simp }, ?_, ?_, ?_, ?_⟩
  · intro m n h
    exact e.symm.injective (Subtype.ext h)
  · intro m
    exact mem_slSub.mp (e.symm m).2
  · intro A hA
    refine ⟨e ⟨A, mem_slSub.mpr hA⟩, ?_⟩
    simp
  · intro g m
    have h1 : e ⟨stAct g (e.symm m).1, hstmem g _⟩ = ρ g m := by
      rw [he, hΨeq, ← he, e.apply_symm_apply]
    show (e.symm (ρ g m)).1 = stAct g (e.symm m).1
    rw [← h1, e.symm_apply_apply]

end Generic

end StUnique

theorem stUnique : StUniqueStatement := by
  intro M _ _ _ ρ hcard hirr
  exact StUnique.stUnique_core ρ hcard hirr

end CFSG.Quasithin.RuType

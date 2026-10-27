module

public import CFSG.Quasithin.Background.SmithB42LnL4Type
public import CFSG.Quasithin.Background.F918F1
public import CFSG.Quasithin.Background.JonesParshallNatural
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Sporadic.Schreier.J4SSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open Matrix CFSG.Quasithin.SmithCurtis CFSG.Quasithin.JonesParshall

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def natRep4 : Representation (ZMod 2) G4 (Fin 4 → ZMod 2) where
  toFun g := (g : 𝕄₄).mulVecLin
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp [mulVec_mulVec]

theorem natRep4_apply (g : G4) (v : Fin 4 → ZMod 2) : natRep4 g v = (g : 𝕄₄) *ᵥ v := rfl

@[expose] def wedgeRep4' : Representation (ZMod 2) G4 (Fin 6 → ZMod 2) where
  toFun g := (wedgeMat4 (g : 𝕄₄)).mulVecLin
  map_one' := LinearMap.ext fun v => by simp [wedgeMat4_one]
  map_mul' g h := LinearMap.ext fun v => by simp [wedgeMat4_mul, mulVec_mulVec]

theorem wedgeRep4'_apply (g : G4) (w : Fin 6 → ZMod 2) :
    wedgeRep4' g w = wedgeMat4 (g : 𝕄₄) *ᵥ w := rfl

noncomputable abbrev invT4 : G4 ≃* G4 := invTransposeSL 4 (ZMod 2)

noncomputable abbrev dualRep4 : Representation (ZMod 2) G4 (Fin 4 → ZMod 2) :=
  natRep4.comp invT4.toMonoidHom

theorem dualRep4_apply (g : G4) (v : Fin 4 → ZMod 2) :
    dualRep4 g v = ((g⁻¹ : G4) : 𝕄₄)ᵀ *ᵥ v := rfl

theorem fix_checks : ∀ c : Fin 64, up4 c *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
    (up4 c)ᵀ *ᵥ Pi.single 3 1 = Pi.single 3 1 ∧
    wedgeMat4 (up4 c) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  decide

theorem fixed_checks :
    (∀ x : Fin 4 → ZMod 2, (∀ s : Fin 3, xM4 s *ᵥ x = x) → x = 0 ∨ x = Pi.single 0 1) ∧
    (∀ x : Fin 4 → ZMod 2, (∀ s : Fin 3, (xM4 s)ᵀ *ᵥ x = x) → x = 0 ∨ x = Pi.single 3 1) ∧
    (∀ x : Fin 6 → ZMod 2, (∀ s : Fin 3, wedgeMat4 (xM4 s) *ᵥ x = x) →
      x = 0 ∨ x = Pi.single 0 1) := by
  decide

theorem gen_checks :
    (∀ i : Fin 4, pm (Equiv.swap 0 i) *ᵥ Pi.single 0 1 = Pi.single i 1) ∧
    (∀ i : Fin 4, (pm (Equiv.swap 3 i)⁻¹)ᵀ *ᵥ Pi.single 3 1 = Pi.single i 1) ∧
    (∀ k : Fin 6, wedgeMat4 (pm (Equiv.swap 0 (pr4 k).1 * Equiv.swap 1 (pr4 k).2)) *ᵥ
      Pi.single 0 1 = Pi.single k 1) := by
  decide

theorem type_checks : ∀ s : Fin 3,
    pm (sw s) *ᵥ Pi.single 0 1 + (xM4 s * pm (sw s)) *ᵥ Pi.single 0 1 =
      (![1, 0, 0] : Fin 3 → ZMod 2) s • Pi.single 0 1 ∧
    (pm (sw s))ᵀ *ᵥ Pi.single 3 1 + (pm (sw s) * xM4 s)ᵀ *ᵥ Pi.single 3 1 =
      (![0, 0, 1] : Fin 3 → ZMod 2) s • Pi.single 3 1 ∧
    wedgeMat4 (pm (sw s)) *ᵥ Pi.single 0 1 + wedgeMat4 (xM4 s * pm (sw s)) *ᵥ Pi.single 0 1 =
      (![0, 1, 0] : Fin 3 → ZMod 2) s • Pi.single 0 1 := by
  decide

theorem inv_eq_uOf {u : G4} (hu : u ∈ U4) : ((u⁻¹ : G4) : 𝕄₄) = up4 (code4 ((u⁻¹ : G4) : 𝕄₄)) :=
  (up4_code4 (U4.inv_mem hu)).symm

theorem e0_mem_fixU : (Pi.single 0 1 : Fin 4 → ZMod 2) ∈ datum4.fixU natRep4 := by
  intro u hu
  rw [natRep4_apply, ← up4_code4 hu]
  exact (fix_checks _).1

theorem e3_mem_fixU : (Pi.single 3 1 : Fin 4 → ZMod 2) ∈ datum4.fixU dualRep4 := by
  intro u hu
  rw [dualRep4_apply, inv_eq_uOf hu]
  exact (fix_checks _).2.1

theorem e01_mem_fixU : (Pi.single 0 1 : Fin 6 → ZMod 2) ∈ datum4.fixU wedgeRep4' := by
  intro u hu
  rw [wedgeRep4'_apply, ← up4_code4 hu]
  exact (fix_checks _).2.2

theorem fixU_nat {x : Fin 4 → ZMod 2} (hx : x ∈ datum4.fixU natRep4) :
    ∃ c : ZMod 2, x = c • Pi.single 0 1 := by
  rcases fixed_checks.1 x fun s => hx (x4 s) (x4_mem s) with h | h
  · exact ⟨0, by rw [h, zero_smul]⟩
  · exact ⟨1, by rw [h, one_smul]⟩

theorem fixU_dual {x : Fin 4 → ZMod 2} (hx : x ∈ datum4.fixU dualRep4) :
    ∃ c : ZMod 2, x = c • Pi.single 3 1 := by
  have h' : ∀ s : Fin 3, (xM4 s)ᵀ *ᵥ x = x := fun s => by
    have := hx (x4 s) (x4_mem s)
    rwa [dualRep4_apply, x4_inv, coe_x4] at this
  rcases fixed_checks.2.1 x h' with h | h
  · exact ⟨0, by rw [h, zero_smul]⟩
  · exact ⟨1, by rw [h, one_smul]⟩

theorem fixU_wedge {x : Fin 6 → ZMod 2} (hx : x ∈ datum4.fixU wedgeRep4') :
    ∃ c : ZMod 2, x = c • Pi.single 0 1 := by
  rcases fixed_checks.2.2 x fun s => hx (x4 s) (x4_mem s) with h | h
  · exact ⟨0, by rw [h, zero_smul]⟩
  · exact ⟨1, by rw [h, one_smul]⟩

theorem eq_top_of_single {m : ℕ} {S : Submodule (ZMod 2) (Fin m → ZMod 2)}
    (h : ∀ i, (Pi.single i 1 : Fin m → ZMod 2) ∈ S) : S = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin m)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact h i

theorem nat_gen : orbitSpan natRep4 (Pi.single 0 1 : Fin 4 → ZMod 2) = ⊤ :=
  eq_top_of_single fun i => Submodule.subset_span ⟨permHom (Equiv.swap 0 i), gen_checks.1 i⟩

theorem dual_gen : orbitSpan dualRep4 (Pi.single 3 1 : Fin 4 → ZMod 2) = ⊤ := by
  refine eq_top_of_single fun i => Submodule.subset_span ⟨permHom (Equiv.swap 3 i), ?_⟩
  show dualRep4 (permHom (Equiv.swap 3 i)) _ = _
  rw [dualRep4_apply, permHom_inv, coe_permHom]
  exact gen_checks.2.1 i

theorem wedge_gen : orbitSpan wedgeRep4' (Pi.single 0 1 : Fin 6 → ZMod 2) = ⊤ :=
  eq_top_of_single fun k => Submodule.subset_span
    ⟨permHom (Equiv.swap 0 (pr4 k).1 * Equiv.swap 1 (pr4 k).2), gen_checks.2.2 k⟩

theorem natRep4_simple : IsSimpleRep natRep4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact datum4.isSimpleRep_of_fixU natRep4 (fun x hx => fixU_nat hx) nat_gen

theorem dualRep4_simple : IsSimpleRep dualRep4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact datum4.isSimpleRep_of_fixU dualRep4 (fun x hx => fixU_dual hx) dual_gen

theorem wedgeRep4'_simple : IsSimpleRep wedgeRep4' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact datum4.isSimpleRep_of_fixU wedgeRep4' (fun x hx => fixU_wedge hx) wedge_gen

theorem triv4_simple : IsSimpleRep (Representation.trivial (ZMod 2) G4 (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine datum4.isSimpleRep_of_fixU _ (y := 1) (fun x _ => ⟨x, (mul_one x).symm⟩) ?_
  rw [eq_top_iff]
  intro x _
  have h := Submodule.smul_mem _ x (mem_orbitSpan_self
    (Representation.trivial (ZMod 2) G4 (ZMod 2)) (1 : ZMod 2))
  rwa [smul_eq_mul, mul_one] at h

theorem nat_type : IsType4 natRep4 (Pi.single 0 1) ![1, 0, 0] := by
  refine ⟨e0_mem_fixU, by decide, fun h hh => ?_, fun s => ?_⟩
  · rw [datum4_H, Subgroup.mem_bot] at hh
    rw [hh, map_one, one_smul]
    rfl
  · rw [heckeT4, natRep4_apply, natRep4_apply]
    exact (type_checks s).1

theorem dual_type : IsType4 dualRep4 (Pi.single 3 1) ![0, 0, 1] := by
  refine ⟨e3_mem_fixU, by decide, fun h hh => ?_, fun s => ?_⟩
  · rw [datum4_H, Subgroup.mem_bot] at hh
    rw [hh, map_one, one_smul]
    rfl
  · rw [heckeT4, dualRep4_apply, dualRep4_apply, _root_.mul_inv_rev, n4_inv, x4_inv]
    exact (type_checks s).2.1

theorem wedge_type : IsType4 wedgeRep4' (Pi.single 0 1) ![0, 1, 0] := by
  refine ⟨e01_mem_fixU, by decide, fun h hh => ?_, fun s => ?_⟩
  · rw [datum4_H, Subgroup.mem_bot] at hh
    rw [hh, map_one, one_smul]
    rfl
  · rw [heckeT4, wedgeRep4'_apply, wedgeRep4'_apply]
    exact (type_checks s).2.2

theorem triv_type : IsType4 (Representation.trivial (ZMod 2) G4 (ZMod 2)) 1 ![0, 0, 0] := by
  refine ⟨fun _ _ => rfl, one_ne_zero, fun h hh => ?_, fun s => ?_⟩
  · simp
  · rw [heckeT4]
    simp only [Representation.trivial_apply]
    revert s
    decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def L4Model (ρ : Representation (ZMod 2) G4 V) : Prop :=
  (∀ g w, ρ g w = w) ∨
    (∃ κ : G4 ≃* G4, ∃ β : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2), ∀ g w, β (ρ g w) = natRep4 (κ g) (β w)) ∨
    (∃ β : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2), ∀ g w, β (ρ g w) = wedgeRep4' g (β w))

theorem mu_cases (μ : Fin 3 → ZMod 2) (h01 : ∀ s, μ s = 0 ∨ μ s = 1)
    (hu : ∀ a b : Fin 3, a ≠ b → μ a = 0 ∨ μ b = 0) :
    μ = ![0, 0, 0] ∨ μ = ![1, 0, 0] ∨ μ = ![0, 0, 1] ∨ μ = ![0, 1, 0] := by
  have key : ∀ a b c : ZMod 2, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) → (c = 0 ∨ c = 1) →
      (a = 0 ∨ b = 0) → (a = 0 ∨ c = 0) → (b = 0 ∨ c = 0) →
      ![a, b, c] = ![0, 0, 0] ∨ ![a, b, c] = ![1, 0, 0] ∨ ![a, b, c] = ![0, 0, 1] ∨
        ![a, b, c] = ![0, 1, 0] := by
    decide
  have hμ : μ = ![μ 0, μ 1, μ 2] := by
    funext s
    fin_cases s <;> rfl
  rw [hμ]
  exact key _ _ _ (h01 0) (h01 1) (h01 2) (hu 0 1 (by decide)) (hu 0 2 (by decide))
    (hu 1 2 (by decide))

theorem l4Model_of_type {ρ : Representation (ZMod 2) G4 V} (hρ : IsSimpleRep ρ) {y : V}
    {μ : Fin 3 → ZMod 2} (ht : IsType4 ρ y μ)
    (hu : ∀ a b : Fin 3, a ≠ b → μ a = 0 ∨ μ b = 0) : L4Model ρ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases mu_cases μ (mu_eq_zero_or_one ρ ht) hu with rfl | rfl | rfl | rfl
  · left
    obtain ⟨β, hβ⟩ := datum4.iso_of_isCurtisType hρ triv4_simple ht triv_type
    intro g w
    apply β.injective
    rw [hβ, Representation.trivial_apply]
  · right; left
    obtain ⟨β, hβ⟩ := datum4.iso_of_isCurtisType hρ natRep4_simple ht nat_type
    exact ⟨MulEquiv.refl _, β, hβ⟩
  · right; left
    obtain ⟨β, hβ⟩ := datum4.iso_of_isCurtisType hρ dualRep4_simple ht dual_type
    exact ⟨invT4, β, hβ⟩
  · right; right
    exact datum4.iso_of_isCurtisType hρ wedgeRep4'_simple ht wedge_type

theorem l4Model_of_finrank_lt [Finite V] {ρ : Representation (ZMod 2) G4 V} (hρ : IsSimpleRep ρ)
    (hdim : Module.finrank (ZMod 2) V < 12) : L4Model ρ := by
  obtain ⟨y, μ, ht⟩ := exists_isType4 hρ
  refine l4Model_of_type hρ ht fun a b hab => ?_
  by_contra h
  push Not at h
  have ha := (mu_eq_zero_or_one ρ ht a).resolve_left h.1
  have hb := (mu_eq_zero_or_one ρ ht b).resolve_left h.2
  have := twelve_le_finrank hρ ht hab ha hb
  omega

theorem third_cases : ∀ a b s t : Fin 3, s ≠ t → a ≠ b → a = s ∨ a = t ∨ b = s ∨ b = t := by
  decide

theorem l4Model_of_fixed [Finite V] {ρ : Representation (ZMod 2) G4 V} (hρ : IsSimpleRep ρ)
    {x : V} (hx0 : x ≠ 0) (hxU : x ∈ datum4.fixU ρ) {s t : Fin 3} (hst : s ≠ t)
    (hs : ρ (n4 s) x = x) (ht : ρ (n4 t) x = x) : L4Model ρ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, μ, hty⟩ := exists_isType4 hρ
  obtain ⟨c, hc⟩ := datum4.fixU_eq_smul hρ hty hxU
  have hc1 : c = 1 := by
    rcases zmod2_eq c with h | h
    · exact absurd (by rw [hc, h, zero_smul]) hx0
    · exact h
  rw [hc1, one_smul] at hc
  subst hc
  have hμs := mu_eq_zero_of_fixed ρ hty hs
  have hμt := mu_eq_zero_of_fixed ρ hty ht
  refine l4Model_of_type hρ hty fun a b hab => ?_
  rcases third_cases a b s t hst hab with h | h | h | h
  · exact Or.inl (h ▸ hμs)
  · exact Or.inl (h ▸ hμt)
  · exact Or.inr (h ▸ hμs)
  · exact Or.inr (h ▸ hμt)

end CFSG.Quasithin.B42Ln

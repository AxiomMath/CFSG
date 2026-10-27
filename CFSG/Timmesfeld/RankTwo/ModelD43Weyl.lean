module

public import CFSG.Timmesfeld.RankTwo.ModelD43Comm
public import CFSG.LieType.Steinberg.TwistedD4.Weyl
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

section Weyl

variable {K : Type} [Field K] [CharP K 2]

theorem reflection_eq_reflect (τ : Tag) (i : Fin τ.rank) (β : Fin τ.rank → ℤ) :
    CFSG.LieType.RootSystem.reflection τ.cartan i β = reflect τ i β := by
  rw [CFSG.LieType.RootSystem.reflection_apply]
  rfl

theorem weylElement_conj_xPar_charTwo {τ : Tag} (i : Fin τ.rank) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (c : K) :
    CFSG.LieType.Chevalley.weylElement τ K i * xPar (rootOperatorFamily τ) β c *
        (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ =
      xPar (rootOperatorFamily τ) (reflect τ i β) c := by
  obtain ⟨ε, hε, h⟩ := weylElement_xPar_conj (F := rootOperatorFamily τ) (K := K) i hβ
  have h1 := h 1 c
  rw [weylElement_xPar, torusElement_one_eq, one_mul] at h1
  rw [h1, reflection_eq_reflect]
  congr 1
  have hε1 : (ε : K) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · simp [CharTwo.neg_eq]
  simp [hε1]

local notation "𝕩" => xPar (rootOperatorFamily d4)

theorem nHatE_conj_xPar (i : Fin (Tag.rank .G2)) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β)
    (c : K) : nHatE K i * 𝕩 β c * (nHatE K i)⁻¹ = 𝕩 (twReflectHom i β) c := by
  match i with
  | ⟨0, _⟩ =>
    rw [nHatE_zero, weylElement_conj_xPar_charTwo _ hβ]
    rfl
  | ⟨1, _⟩ =>
    have e : nHatE K (ng 1) * 𝕩 β c * (nHatE K (ng 1))⁻¹ =
        CFSG.LieType.Chevalley.weylElement d4 K (nd 0) *
          (CFSG.LieType.Chevalley.weylElement d4 K (nd 1) *
            (CFSG.LieType.Chevalley.weylElement d4 K (nd 3) * 𝕩 β c *
              (CFSG.LieType.Chevalley.weylElement d4 K (nd 3))⁻¹) *
                (CFSG.LieType.Chevalley.weylElement d4 K (nd 1))⁻¹) *
                  (CFSG.LieType.Chevalley.weylElement d4 K (nd 0))⁻¹ := by
      rw [nHatE_one]
      group
    rw [e, weylElement_conj_xPar_charTwo _ hβ, weylElement_conj_xPar_charTwo _ (hβ.reflect _),
      weylElement_conj_xPar_charTwo _ ((hβ.reflect _).reflect _)]
    rfl

variable (σ : K →+* K)

theorem nHatE_conj_xOrbit (i : Fin (Tag.rank .G2)) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β)
    (c : K) : nHatE K i * xOrbit σ β c * (nHatE K i)⁻¹ = xOrbit σ (twReflectHom i β) c := by
  have h1 := isRoot_rho hβ
  have h2 := isRoot_rho h1
  rw [xOrbit_eq, xOrbit_eq, ← twReflect_rho, ← twReflect_rho,
    show nHatE K i * (𝕩 β c * 𝕩 (rho β) (σ c) * 𝕩 (rho (rho β)) (σ (σ c))) * (nHatE K i)⁻¹ =
      (nHatE K i * 𝕩 β c * (nHatE K i)⁻¹) * (nHatE K i * 𝕩 (rho β) (σ c) * (nHatE K i)⁻¹) *
        (nHatE K i * 𝕩 (rho (rho β)) (σ (σ c)) * (nHatE K i)⁻¹) by group,
    nHatE_conj_xPar i hβ, nHatE_conj_xPar i h1, nHatE_conj_xPar i h2]

end Weyl

@[expose] def d43LiftPos : List ℕ := [2, 0, 8, 19, 5, 4, 21, 22, 15, 11, 23, 20]

@[expose] def g2RootPos (γ : Fin (Tag.rank .G2) → ℤ) : ℕ :=
  ((List.range 12).find? fun k =>
    List.ofFn ((Tag.rootCertificate .G2).root k) == List.ofFn γ).getD 0

@[expose] def d43Lift (γ : Fin (Tag.rank .G2) → ℤ) : Fin d4.rank → ℤ :=
  d4Root (d43LiftPos.getD (g2RootPos γ) 0)

@[expose] def d43Long (γ : Fin (Tag.rank .G2) → ℤ) : Prop := 3 ∣ γ (ng 1)

instance (γ : Fin (Tag.rank .G2) → ℤ) : Decidable (d43Long γ) :=
  inferInstanceAs (Decidable (3 ∣ γ (ng 1)))

theorem d43Lift_spec {k : ℕ} (hk : k < 12) :
    d43LiftPos.getD k 0 < 24 ∧ d43Lift ((Tag.rootCertificate .G2).root k) =
      d4Root (d43LiftPos.getD k 0) := by
  interval_cases k <;> refine ⟨by decide, ?_⟩ <;> rw [d43Lift] <;> congr 2

theorem d43Lift_root {k : ℕ} (hk : k < 12) :
    d43Lift ((Tag.rootCertificate .G2).root k) = d4Root (d43LiftPos.getD k 0) :=
  (d43Lift_spec hk).2

theorem ofFn_injective' {n : ℕ} {v w : Fin n → ℤ} (h : List.ofFn v = List.ofFn w) : v = w :=
  List.ofFn_injective h

theorem isRoot_d43Lift {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) :
    IsRoot d4 (d43Lift γ) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  rw [d43Lift_root hk]
  exact isRoot_rootCertificate_root ((d43Lift_spec hk).1.trans_le (by decide))

theorem proj_d43Lift {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) : proj (d43Lift γ) = γ := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  rw [d43Lift_root hk']
  refine ofFn_injective' ?_
  interval_cases k <;> decide +kernel

theorem rho_d43Lift_of_long {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hl : d43Long γ) :
    rho (d43Lift γ) = d43Lift γ := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  rw [d43Lift_root hk']
  revert hl
  interval_cases k <;> intro hl <;> first
    | exact absurd hl (by decide +kernel)
    | exact ofFn_injective' (by decide +kernel)

theorem rho_d43Lift_ne {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hs : ¬d43Long γ) :
    rho (d43Lift γ) ≠ d43Lift γ := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  rw [d43Lift_root hk']
  revert hs
  interval_cases k <;> intro hs <;> first
    | exact absurd (by decide +kernel) hs
    | exact fun h => absurd (congrArg List.ofFn h) (by decide +kernel)

theorem exists_reflect_eq {k : ℕ} (hk : k < 12) (i : Fin (Tag.rank .G2)) :
    ∃ m < 12, reflect .G2 i ((Tag.rootCertificate .G2).root k) =
      (Tag.rootCertificate .G2).root m ∧ m = (Tag.rootCertificate .G2).image k i :=
  ⟨_, rootCertificate_image_lt hk i, (rootCertificate_root_image hk i).symm, rfl⟩

theorem twReflectHom_d43Lift (i : Fin (Tag.rank .G2)) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : IsRoot .G2 γ) : twReflectHom i (d43Lift γ) = d43Lift (reflect .G2 i γ) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  obtain ⟨m, hm, hme, rfl⟩ := exists_reflect_eq hk' i
  rw [hme, d43Lift_root hk', d43Lift_root hm]
  refine ofFn_injective' ?_
  fin_cases i <;> interval_cases k <;> decide +kernel

theorem d43Long_reflect (i : Fin (Tag.rank .G2)) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : IsRoot .G2 γ) : d43Long (reflect .G2 i γ) ↔ d43Long γ := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  obtain ⟨m, hm, hme, rfl⟩ := exists_reflect_eq hk' i
  rw [hme]
  fin_cases i <;> interval_cases k <;> decide +kernel

section Param

variable {K : Type} [Field K] (σ : K →+* K)

local notation "𝕩" => xPar (rootOperatorFamily d4)

@[expose] noncomputable def d43XSh (γ : Fin (Tag.rank .G2) → ℤ) (c : K) : adjointGroup d4 K :=
  xOrbit σ (d43Lift γ) c

@[expose] noncomputable def d43XLg (γ : Fin (Tag.rank .G2) → ℤ) (c : fixedField σ) :
    adjointGroup d4 K :=
  𝕩 (d43Lift γ) c

variable {σ}

theorem d43XSh_add {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hs : ¬d43Long γ)
    (c d : K) : d43XSh σ γ (c + d) = d43XSh σ γ c * d43XSh σ γ d :=
  xOrbit_add σ (isRoot_d43Lift hγ) (rho_d43Lift_ne hγ hs) c d

theorem d43XLg_add (γ : Fin (Tag.rank .G2) → ℤ) (c d : fixedField σ) :
    d43XLg σ γ (c + d) = d43XLg σ γ c * d43XLg σ γ d :=
  xPar_add _ (c : K) d

theorem d43XSh_injective {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hs : ¬d43Long γ) :
    Function.Injective (d43XSh σ γ) :=
  xOrbit_injective σ (isRoot_d43Lift hγ) (rho_d43Lift_ne hγ hs)

theorem d43XLg_injective {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) :
    Function.Injective (d43XLg σ γ) := fun _ _ h =>
  Subtype.ext (xPar_injective (isRoot_d43Lift hγ) h)

variable (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem mem_iff_d43XSh {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hs : ¬d43Long γ)
    (g : adjointGroup d4 K) : g ∈ twistedRootSubgroupD4 σ γ ↔ ∃ c, d43XSh σ γ c = g := by
  rw [mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_d43Lift hγ) (proj_d43Lift hγ)
    (rho_d43Lift_ne hγ hs)]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem mem_iff_d43XLg {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hl : d43Long γ)
    (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ γ ↔ ∃ c : fixedField σ, d43XLg σ γ c = g := by
  rw [mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d43Lift hγ) (proj_d43Lift hγ)
    (rho_d43Lift_of_long hγ hl)]
  exact ⟨fun ⟨c, hc, hg⟩ => ⟨⟨c, hc⟩, hg.symm⟩, fun ⟨c, hc⟩ => ⟨c, c.2, hc.symm⟩⟩

theorem d43XSh_mem {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hs : ¬d43Long γ) (c : K) :
    d43XSh σ γ c ∈ twistedRootSubgroupD4 σ γ :=
  (mem_iff_d43XSh hσ hγ hs _).2 ⟨c, rfl⟩

theorem d43XLg_mem {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hl : d43Long γ)
    (c : fixedField σ) : d43XLg σ γ c ∈ twistedRootSubgroupD4 σ γ :=
  (mem_iff_d43XLg hσ hγ hl _).2 ⟨c, rfl⟩

omit hσ

variable [CharP K 2]

theorem nHatE_conj_d43XSh (i : Fin (Tag.rank .G2)) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : IsRoot .G2 γ) (c : K) :
    nHatE K i * d43XSh σ γ c * (nHatE K i)⁻¹ = d43XSh σ (reflect .G2 i γ) c := by
  rw [d43XSh, d43XSh, nHatE_conj_xOrbit σ i (isRoot_d43Lift hγ), twReflectHom_d43Lift i hγ]

theorem nHatE_conj_d43XLg (i : Fin (Tag.rank .G2)) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : IsRoot .G2 γ) (c : fixedField σ) :
    nHatE K i * d43XLg σ γ c * (nHatE K i)⁻¹ = d43XLg σ (reflect .G2 i γ) c := by
  rw [d43XLg, d43XLg, nHatE_conj_xPar i (isRoot_d43Lift hγ), twReflectHom_d43Lift i hγ]

end Param

end CFSG.Timmesfeld.RankTwo

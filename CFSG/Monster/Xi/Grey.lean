module

public import CFSG.Monster.Spin.Pairing
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Monster.Xi

open CFSG.Monster.Code CFSG.Monster.Spin

@[expose] def greyC : (Fin 6 → ZMod 2) →ₗ[ZMod 2] C where
  toFun μ := ⟨∑ i, μ i • g i, C.sum_mem fun i _ => C.smul_mem _ (g_mem_C i)⟩
  map_add' μ ν := Subtype.ext <| by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add]
  map_smul' c μ := Subtype.ext <| by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Submodule.coe_smul,
      RingHom.id_apply]

theorem coe_greyC (μ : Fin 6 → ZMod 2) : (greyC μ : Fin 24 → ZMod 2) = ∑ i, μ i • g i := rfl

theorem greyC_mem_G (μ : Fin 6 → ZMod 2) : (greyC μ : Fin 24 → ZMod 2) ∈ G :=
  (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).2 ⟨μ, rfl⟩

theorem repr_greyC (μ : Fin 6 → ZMod 2) (j : Fin 6) : basisC.repr (greyC μ) (ι6 j) = μ j := by
  rw [repr_grey μ (greyC μ) rfl, greyCoords_ι6]

theorem greyC_injective : Function.Injective greyC := fun μ ν h =>
  funext fun j => by rw [← repr_greyC μ j, ← repr_greyC ν j, h]

theorem mem_G_iff (x : Fin 24 → ZMod 2) : x ∈ G ↔ ∃ μ, (greyC μ : Fin 24 → ZMod 2) = x :=
  Submodule.mem_span_range_iff_exists_fun (ZMod 2)

theorem mem_G_iff_existsUnique (x : Fin 24 → ZMod 2) :
    x ∈ G ↔ ∃! μ, (greyC μ : Fin 24 → ZMod 2) = x := by
  rw [mem_G_iff]
  refine ⟨fun ⟨μ, hμ⟩ => ⟨μ, hμ, fun ν hν => greyC_injective (Subtype.ext (hν.trans hμ.symm))⟩,
    fun h => h.exists⟩

@[simp] theorem greyC_single (i : Fin 6) : greyC (Pi.single i 1) = ⟨g i, g_mem_C i⟩ := by
  apply Subtype.ext
  rw [coe_greyC, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]

@[expose] noncomputable def greyEquiv : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] G :=
  LinearEquiv.ofBijective (LinearMap.codRestrict G (C.subtype ∘ₗ greyC) greyC_mem_G)
    ⟨fun μ ν h => greyC_injective (Subtype.ext (congrArg (fun x : G => (x : Fin 24 → ZMod 2)) h)),
      fun x => by
        obtain ⟨μ, hμ⟩ := (mem_G_iff x).1 x.2
        exact ⟨μ, Subtype.ext hμ⟩⟩

@[simp] theorem coe_greyEquiv (μ : Fin 6 → ZMod 2) :
    ((greyEquiv μ : G) : Fin 24 → ZMod 2) = greyC μ := rfl

@[expose] def gammaVec : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := greyGamma
  map_add' μ ν := by simp only [greyGamma, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c μ := by
    simp only [greyGamma, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

@[expose] def gammaD : (Fin 6 → ZMod 2) →ₗ[ZMod 2] Cocode := C.mkQ ∘ₗ gammaVec

theorem gammaD_apply (μ : Fin 6 → ZMod 2) :
    gammaD μ = Submodule.Quotient.mk (∑ i, μ i • γ i) := rfl

theorem mk_greyGamma (μ : Fin 6 → ZMod 2) :
    Submodule.Quotient.mk (p := C) (greyGamma μ) = gammaD μ := rfl

theorem gammaD_eq_sum (μ : Fin 6 → ZMod 2) :
    gammaD μ = ∑ i, μ i • Submodule.Quotient.mk (p := C) (γ i) := by
  rw [gammaD_apply, ← Submodule.mkQ_apply, map_sum]
  simp only [map_smul, Submodule.mkQ_apply]

@[simp] theorem gammaD_single (i : Fin 6) :
    gammaD (Pi.single i 1) = Submodule.Quotient.mk (γ i) := by
  rw [gammaD_apply, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]

@[expose] def qG (μ : Fin 6 → ZMod 2) : ZMod 2 := ((greyWeight μ).choose 2 : ℕ)

theorem qG_def (μ : Fin 6 → ZMod 2) : qG μ = (((∑ i, (μ i).val).choose 2 : ℕ) : ZMod 2) := rfl

private theorem ite_ne_add (p : Prop) [Decidable p] (a b : ZMod 2) :
    (if ¬p then a + b else 0) = (if ¬p then a else 0) + (if ¬p then b else 0) := by
  split_ifs <;> simp

private theorem ite_ne_mul (p : Prop) [Decidable p] (c a : ZMod 2) :
    (if ¬p then c * a else 0) = c * (if ¬p then a else 0) := by
  split_ifs <;> simp

@[expose] def bG : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) (fun μ ν => ∑ i, ∑ j, if i ≠ j then μ i * ν j else 0)
    (fun μ μ' ν => by
      simp only [Pi.add_apply, add_mul, ite_ne_add, Finset.sum_add_distrib])
    (fun c μ ν => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ite_ne_mul, ← Finset.mul_sum])
    (fun μ ν ν' => by
      simp only [Pi.add_apply, mul_add, ite_ne_add, Finset.sum_add_distrib])
    (fun c μ ν => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (μ _) c, ite_ne_mul,
        ← Finset.mul_sum])

theorem bG_apply (μ ν : Fin 6 → ZMod 2) :
    bG μ ν = ∑ i, ∑ j, if i ≠ j then μ i * ν j else 0 := rfl

@[expose] def Gstar : Submodule (ZMod 2) Cocode :=
  Submodule.span (ZMod 2) (Set.range fun j => Submodule.Quotient.mk (p := C) (γ j))

@[expose] def Hstar : Submodule (ZMod 2) Cocode where
  carrier := {δ | ∀ a : C, (a : Fin 24 → ZMod 2) ∈ G → pair a δ = 0}
  add_mem' hδ hε a ha := by rw [pair_add_right, hδ a ha, hε a ha, add_zero]
  zero_mem' a _ := pair_zero_right a
  smul_mem' c δ hδ a ha := by rw [map_smul, hδ a ha, smul_zero]

theorem mem_Hstar {δ : Cocode} :
    δ ∈ Hstar ↔ ∀ a : C, (a : Fin 24 → ZMod 2) ∈ G → pair a δ = 0 := Iff.rfl

theorem mem_Hstar_iff {δ : Cocode} : δ ∈ Hstar ↔ ∀ μ, pair (greyC μ) δ = 0 := by
  rw [mem_Hstar]
  refine ⟨fun h μ => h _ (greyC_mem_G μ), fun h a ha => ?_⟩
  obtain ⟨μ, hμ⟩ := (mem_G_iff _).1 ha
  rw [← h μ, show a = greyC μ from Subtype.ext hμ.symm]

theorem g_dotProduct_γ : ∀ i j : Fin 6, g i ⬝ᵥ γ j = if i = j then 0 else 1 := by
  decide +kernel

theorem pair_g_γ (i j : Fin 6) :
    pair ⟨g i, g_mem_C i⟩ (Submodule.Quotient.mk (γ j)) = if i = j then 0 else 1 :=
  g_dotProduct_γ i j

theorem pair_greyC_gammaD (μ ν : Fin 6 → ZMod 2) : pair (greyC μ) (gammaD ν) = bG μ ν := by
  rw [gammaD_apply, pair_mk, coe_greyC, bG_apply, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, dotProduct_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dotProduct_smul, g_dotProduct_γ, smul_eq_mul]
  split_ifs <;> simp_all

private theorem bG_single_aux : ∀ a b c d e f : ZMod 2,
    (∀ i : Fin 6, bG (Pi.single i 1) ![a, b, c, d, e, f] = 0) → ![a, b, c, d, e, f] = 0 := by
  decide +kernel

theorem bG_eq_zero_of_forall {ν : Fin 6 → ZMod 2} (h : ∀ μ, bG μ ν = 0) : ν = 0 := by
  have hν : ν = ![ν 0, ν 1, ν 2, ν 3, ν 4, ν 5] := by
    funext i; fin_cases i <;> rfl
  rw [hν]
  exact bG_single_aux _ _ _ _ _ _ fun i => by rw [← hν]; exact h _

theorem gammaD_injective : Function.Injective gammaD := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ν hν
  exact bG_eq_zero_of_forall fun μ => by rw [← pair_greyC_gammaD, hν, pair_zero_right]

theorem gammaD_mem_Gstar (μ : Fin 6 → ZMod 2) : gammaD μ ∈ Gstar := by
  rw [gammaD_eq_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem range_gammaD : LinearMap.range gammaD = Gstar := by
  refine le_antisymm (fun _ ⟨μ, hμ⟩ => hμ ▸ gammaD_mem_Gstar μ) ?_
  rw [Gstar, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact ⟨Pi.single j 1, gammaD_single j⟩

@[expose] noncomputable def gammaEquiv : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] Gstar :=
  (LinearEquiv.ofInjective gammaD gammaD_injective).trans (LinearEquiv.ofEq _ _ range_gammaD)

@[simp] theorem coe_gammaEquiv (μ : Fin 6 → ZMod 2) :
    ((gammaEquiv μ : Gstar) : Cocode) = gammaD μ := rfl

@[expose] noncomputable def gammaG : G ≃ₗ[ZMod 2] Gstar := greyEquiv.symm.trans gammaEquiv

@[simp] theorem gammaG_greyEquiv (μ : Fin 6 → ZMod 2) :
    ((gammaG (greyEquiv μ) : Gstar) : Cocode) = gammaD μ := by
  simp [gammaG]

@[expose] noncomputable def qGstar (δ : Gstar) : ZMod 2 := qG (gammaEquiv.symm δ)

@[simp] theorem qGstar_gammaEquiv (μ : Fin 6 → ZMod 2) : qGstar (gammaEquiv μ) = qG μ := by
  rw [qGstar, LinearEquiv.symm_apply_apply]

theorem grey_cocode_quadratic_data :
    (∀ x : Fin 24 → ZMod 2, x ∈ G ↔ ∃! μ : Fin 6 → ZMod 2, (greyC μ : Fin 24 → ZMod 2) = x) ∧
    (∀ μ : Fin 6 → ZMod 2, (greyC μ : Fin 24 → ZMod 2) = ∑ i, μ i • g i) ∧
    (∀ μ : Fin 6 → ZMod 2, gammaD μ = Submodule.Quotient.mk (∑ i, μ i • γ i)) ∧
    (∀ μ : Fin 6 → ZMod 2, qG μ = (((∑ i, (μ i).val).choose 2 : ℕ) : ZMod 2)) ∧
    (∀ μ ν : Fin 6 → ZMod 2, bG μ ν = ∑ i, ∑ j, if i ≠ j then μ i * ν j else 0) ∧
    (∀ (a : C) (x : Fin 24 → ZMod 2), pair a (Submodule.Quotient.mk x) =
      (a : Fin 24 → ZMod 2) ⬝ᵥ x) ∧
    (∀ i j : Fin 6, pair ⟨g i, g_mem_C i⟩ (Submodule.Quotient.mk (γ j)) =
      if i = j then 0 else 1) ∧
    Gstar = Submodule.span (ZMod 2) (Set.range fun j => Submodule.Quotient.mk (p := C) (γ j)) ∧
    Function.Injective gammaD ∧ LinearMap.range gammaD = Gstar ∧
    (∀ μ : Fin 6 → ZMod 2, ((gammaG (greyEquiv μ) : Gstar) : Cocode) = gammaD μ) ∧
    (∀ μ : Fin 6 → ZMod 2, qGstar (gammaEquiv μ) = qG μ) ∧
    (∀ δ : Cocode, δ ∈ Hstar ↔ ∀ a : C, (a : Fin 24 → ZMod 2) ∈ G → pair a δ = 0) :=
  ⟨mem_G_iff_existsUnique, coe_greyC, gammaD_apply, qG_def, bG_apply, pair_mk, pair_g_γ, rfl,
    gammaD_injective, range_gammaD, gammaG_greyEquiv, qGstar_gammaEquiv, fun _ => mem_Hstar⟩

end CFSG.Monster.Xi

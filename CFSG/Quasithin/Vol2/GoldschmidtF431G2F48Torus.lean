module

public import CFSG.GH74.GLS.Stage4.HexModelG2
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Gen

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.F48

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage4.Hex
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.BN

set_option linter.unusedSectionVars false


variable {F : Type} [Field F]

theorem coe_xPar_g2_eq_pinnedX {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) (c : F) :
    ((xPar (rootOperatorFamily Tag.G2) γ c : adjointGroup Tag.G2 F) : ModGL Tag.G2 F) =
      pinnedX Tag.G2 F γ ((((rootOperatorFamily Tag.G2).pinnedFamilySign γ : ℤ) : F) * c) := by
  have h2 : pinnedX Tag.G2 F γ ((((rootOperatorFamily Tag.G2).pinnedFamilySign γ : ℤ) : F) * c) =
      (rootOperatorFamily Tag.G2).eltUnit F ⟨γ, hγ⟩ c := by
    rw [(rootOperatorFamily Tag.G2).pinnedX_eq_eltUnit F hγ, ← mul_assoc,
      (rootOperatorFamily Tag.G2).pinnedFamilySign_mul_self, one_mul]
  rw [xPar_of_isRoot hγ]
  exact h2.symm

theorem rootDiagUnit_conj_xPar_g2 (a : Fin Tag.G2.rank → Fˣ) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot Tag.G2 γ) (c : F) :
    rootDiagUnit Tag.G2 a * ((xPar (rootOperatorFamily Tag.G2) γ c : adjointGroup Tag.G2 F) :
        ModGL Tag.G2 F) * (rootDiagUnit Tag.G2 a)⁻¹ =
      ((xPar (rootOperatorFamily Tag.G2) γ (((rootChar a γ : Fˣ) : F) * c) :
        adjointGroup Tag.G2 F) : ModGL Tag.G2 F) := by
  rw [coe_xPar_g2_eq_pinnedX hγ, coe_xPar_g2_eq_pinnedX hγ, rootDiagUnit_conj_pinnedX a hγ]
  congr 1
  ring

@[expose] def torG2 (u : Fˣ) : adjointGroup Tag.G2 F :=
  torusElement Tag.G2 F (0 : Fin 2) (u ^ 2) * torusElement Tag.G2 F (1 : Fin 2) u

theorem cartanChar_g2 (u : Fˣ) : cartanChar (τ := Tag.G2) ![u ^ 2, u] = ![u, 1] := by
  have key : ∀ l : Fin 2, ∏ j : Fin 2, (![u ^ 2, u] : Fin 2 → Fˣ) j ^ (Tag.G2.cartan j l) =
      (![u, 1] : Fin 2 → Fˣ) l := by
    intro l
    rw [Fin.prod_univ_two]
    fin_cases l
    · show (u ^ 2) ^ (2 : ℤ) * u ^ (-3 : ℤ) = u
      group
    · show (u ^ 2) ^ (-1 : ℤ) * u ^ (2 : ℤ) = 1
      group
  funext l
  exact key l

theorem rootChar_g2 (u : Fˣ) (γ : Fin Tag.G2.rank → ℤ) :
    rootChar (τ := Tag.G2) ![u, 1] γ = u ^ γ (0 : Fin 2) := by
  show ∏ i : Fin 2, (![u, 1] : Fin 2 → Fˣ) i ^ γ i = _
  rw [Fin.prod_univ_two]
  simp

theorem finRange_two_map {M : Type*} [Monoid M] (f : Fin 2 → M) :
    ((List.finRange 2).map f).prod = f 0 * f 1 := by
  rw [show List.finRange 2 = [0, 1] from rfl]
  simp

theorem torG2_coe (u : Fˣ) :
    ((torG2 u : adjointGroup Tag.G2 F) : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 ![u, 1] := by
  have h := list_prod_torusElt_eq_rootDiagUnit (K := F) (τ := Tag.G2) ![u ^ 2, u]
  rw [cartanChar_g2] at h
  have e : ((List.finRange Tag.G2.rank).map fun j => torusElt Tag.G2 F j (![u ^ 2, u] j)).prod =
      torusElt Tag.G2 F (0 : Fin 2) (u ^ 2) * torusElt Tag.G2 F (1 : Fin 2) u :=
    finRange_two_map (fun j => torusElt Tag.G2 F j (![u ^ 2, u] j))
  rw [e] at h
  exact h

theorem torG2_conj_xPar (u : Fˣ) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) (c : F) :
    torG2 u * xPar (rootOperatorFamily Tag.G2) γ c * (torG2 u)⁻¹ =
      xPar (rootOperatorFamily Tag.G2) γ (((u ^ γ (0 : Fin 2) : Fˣ) : F) * c) := by
  refine Subtype.ext ?_
  have h := rootDiagUnit_conj_xPar_g2 (F := F) ![u, 1] hγ c
  rw [rootChar_g2] at h
  rw [← torG2_coe] at h
  exact h

theorem eq_zero_of_fix_xPar (u : Fˣ) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ)
    (hu : u ^ γ (0 : Fin 2) ≠ 1) {c : F}
    (h : torG2 u * xPar (rootOperatorFamily Tag.G2) γ c * (torG2 u)⁻¹ =
      xPar (rootOperatorFamily Tag.G2) γ c) : c = 0 := by
  rw [torG2_conj_xPar u hγ] at h
  have h1 : ((u ^ γ (0 : Fin 2) : Fˣ) : F) * c = c := xPar_injective hγ h
  by_contra hc
  exact hu (Units.val_eq_one.1 (mul_right_cancel₀ hc (by rw [one_mul]; exact h1)))

theorem exists_unit_sq_ne_one [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ u : Fˣ, u ≠ 1 ∧ u ^ 2 ≠ 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra hcon
  push Not at hcon
  have hall : ∀ a : F, a ∈ ({0, 1, -1} : Finset F) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    · have h := hcon (Units.mk0 a ha)
      by_cases h1 : Units.mk0 a ha = 1
      · simp [Units.ext_iff] at h1
        simp [h1]
      · have h2 := h h1
        have h3 : a * a = 1 := by
          have := congrArg Units.val h2
          simpa [sq] using this
        rcases mul_self_eq_one_iff.1 h3 with h4 | h4 <;> simp [h4]
  have hle : Fintype.card F ≤ 3 := by
    calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
      _ ≤ ({0, 1, -1} : Finset F).card := Finset.card_le_card fun a _ => hall a
      _ ≤ 3 := Finset.card_le_three
  rw [Nat.card_eq_fintype_card] at h4
  omega

theorem hexPos_zero_of_rad {i : ℤ} (h2 : 2 ≤ i) (h6 : i ≤ 6) :
    hexPos i (0 : Fin 2) = 1 ∨ hexPos i (0 : Fin 2) = 2 := by
  interval_cases i <;> simp [hexPos]

theorem torG2_mem_torus (u : Fˣ) : torG2 u ∈ ⨆ i, torus (τ := Tag.G2) F i :=
  Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem (0 : Fin 2) ⟨u ^ 2, rfl⟩)
    (Subgroup.mem_iSup_of_mem (1 : Fin 2) ⟨u, rfl⟩)

theorem torG2_mem_cartan (hF : 3 ≤ Nat.card F) (u : Fˣ) :
    hexProj ↥(adjointGroup Tag.G2 F) (torG2 u) ∈
      (g2ModelSystem F hF).B ⊓ (g2ModelSystem F hF).N :=
  ⟨Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (torG2_mem_torus u)),
    (hexQuotRGD2 (g2Data F)).H_le_N (Subgroup.mem_map_of_mem _ (torG2_mem_torus u))⟩

theorem fix_of_fix_proj (u : Fˣ) {i : ℤ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) {x : adjointGroup Tag.G2 F}
    (hx : x ∈ hexGroup (g2Roots F) i)
    (h : hexProj ↥(adjointGroup Tag.G2 F) (torG2 u) * hexProj ↥(adjointGroup Tag.G2 F) x *
      (hexProj ↥(adjointGroup Tag.G2 F) (torG2 u))⁻¹ = hexProj ↥(adjointGroup Tag.G2 F) x) :
    torG2 u * x * (torG2 u)⁻¹ = x := by
  have hy : torG2 u * x * (torG2 u)⁻¹ ∈ hexGroup (g2Roots F) i :=
    (g2RGD2 F).invariant i (isRoot_of_pos_le hi1 hi6) _ (torG2_mem_torus u) x hx
  have hU : x⁻¹ * (torG2 u * x * (torG2 u)⁻¹) ∈ posUnipotent (g2Shape (g2Roots F)) :=
    mul_mem (inv_mem (hexGroup_le_posUnipotent hi1 hi6 hx))
      (hexGroup_le_posUnipotent hi1 hi6 hy)
  have hker : x⁻¹ * (torG2 u * x * (torG2 u)⁻¹) ∈ (hexProj ↥(adjointGroup Tag.G2 F)).ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [h, inv_mul_cancel]
  have h0 := posUnipotent_inf_ker_hexProj (g2Data F)
  have h1 : x⁻¹ * (torG2 u * x * (torG2 u)⁻¹) ∈ (⊥ : Subgroup (adjointGroup Tag.G2 F)) :=
    h0 ▸ ⟨hU, hker⟩
  exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 h1)).symm

theorem torus_fix_hexGroup (u : Fˣ) (hu : u ≠ 1) (hu2 : u ^ 2 ≠ 1) {i : ℤ} (hi2 : 2 ≤ i)
    (hi6 : i ≤ 6) {x : adjointGroup Tag.G2 F} (hx : x ∈ hexGroup (g2Roots F) i)
    (hfix : torG2 u * x * (torG2 u)⁻¹ = x) : x = 1 := by
  have hγ : IsRoot Tag.G2 (hexPos i) := isRoot_hexPos (by omega) (by omega)
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
  have hc : c = 0 := by
    refine eq_zero_of_fix_xPar u hγ ?_ hfix
    rcases hexPos_zero_of_rad hi2 hi6 with h | h
    · rw [h, zpow_one]
      exact hu
    · rw [h]
      simpa using hu2
  rw [hc]
  exact xPar_zero _

theorem g2Model_fix_root (hF : 3 ≤ Nat.card F) (u : Fˣ) (hu : u ≠ 1) (hu2 : u ^ 2 ≠ 1) {i : ℤ}
    (hi2 : 2 ≤ i) (hi6 : i ≤ 6) {x : AdjointQuotient Tag.G2 F}
    (hx : x ∈ (g2ModelSystem F hF).root i)
    (hfix : hexProj ↥(adjointGroup Tag.G2 F) (torG2 u) * x *
      (hexProj ↥(adjointGroup Tag.G2 F) (torG2 u))⁻¹ = x) : x = 1 := by
  obtain ⟨x', hx', rfl⟩ := hx
  have h1 := fix_of_fix_proj u (by omega) hi6 hx' hfix
  rw [torus_fix_hexGroup u hu hu2 hi2 hi6 hx' h1, map_one]

theorem g2Model_fix_Q [Finite F] (hF : 3 ≤ Nat.card F)
    (hU : IsSylowTwoOf (g2ModelSystem F hF).U ⊤) (u : Fˣ) (hu : u ≠ 1) (hu2 : u ^ 2 ≠ 1)
    {y : AdjointQuotient Tag.G2 F} (hy : y ∈ Q (g2ModelSystem F hF) true)
    (hc : hexProj ↥(adjointGroup Tag.G2 F) (torG2 u) * y *
      (hexProj ↥(adjointGroup Tag.G2 F) (torG2 u))⁻¹ = y) : y = 1 :=
  centralizer_Q_trivial (g2ModelSystem F hF) hU true (torG2_mem_cartan hF u)
    (fun k hk x hx hf => g2Model_fix_root hF u hu hu2 (mem_intList_iff.1 hk).1
      (by have := (mem_intList_iff.1 hk).2; omega) hx hf) hy hc

end CFSG.Quasithin.H13.F431.G2.F48

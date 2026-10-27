module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Certificates.A8Nbr476

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGForkA8TablePInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        (GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) ∨
          GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) →
        (∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
          GGHasLabel labJ (J ⧸ Subgroup.center J) →
          GGTablePAt 7 (J ⧸ Subgroup.center J) (K ⧸ Subgroup.center K)) ∧
        (∀ labJ labL : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labL →
          GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labL (L ⧸ Subgroup.center L) →
          GGTablePAt 7 (J ⧸ Subgroup.center J) (L ⧸ Subgroup.center L))

@[expose] def GGForkA8CoordInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 →
        (GGHasLabel ⟨.A, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
          GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
          GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L)) →
        ∃ (c : Case) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)), c ∈ allCases ∧
          (∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (gens c k)) ∧
          (c.1 = true → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3)

theorem GGForkA8TablePInput.toSecFive (h : GGForkA8TablePInput) : GGSecFiveA8TablePInput :=
  fun G _ _ p B Bs x L D J hR hp y K hK hlab => h G p B Bs x L D J hR.1 hR.2.2.1 hp y K hK hlab

theorem GGForkA8CoordInput.toSecFive (h : GGForkA8CoordInput) : GGA8NbrCoordInput :=
  fun G _ _ p B Bs x L D J hR hp y K hK hKm hL =>
    h G p B Bs x L D J hR.1 hR.2.2.1 hR.2.2.2.1 hp y K hK hKm hL

@[expose] def ggA8NbrScalarWord : List (Fin 6) := [0, 1, 0, 2, 5, 2, 5, 0, 1, 5, 0, 5]

theorem ggA8Nbr_scalar_word :
    ∀ c ∈ excCases, (ggA8NbrScalarWord.map (gens c)).prod = Matrix.diagonal fun _ => 2 := by
  decide +kernel

theorem ggA8Nbr_false_of_coord_exc {G : Type} [Group G] {Bs : Subgroup G} (L K : Subgroup G)
    (hSc : GGScalarsPmOne Bs) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) {c : Case}
    (hc : c ∈ excCases)
    (hgen : ∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
      ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (gens c k)) : False := by
  let S : Submonoid M4 :=
    { carrier := {g | ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
        ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) g}
      mul_mem' := by
        rintro g₁ g₂ ⟨φ₁, hφ₁, h₁⟩ ⟨φ₂, hφ₂, h₂⟩
        refine ⟨φ₂ * φ₁, Subgroup.mul_mem _ hφ₂ hφ₁, fun b => ?_⟩
        rw [MulAut.mul_apply, h₂, h₁, Matrix.vecMul_vecMul]
      one_mem' := ⟨1, Subgroup.one_mem _, fun b => by simp⟩ }
  have hmem : (ggA8NbrScalarWord.map (gens c)).prod ∈ S := by
    refine S.list_prod_mem fun g hg => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
    exact hgen k
  rw [ggA8Nbr_scalar_word c hc] at hmem
  obtain ⟨φ, hφA, hφ⟩ := hmem
  have hφ2 : ∀ b : ↥Bs, φ b = b ^ 2 := by
    intro b
    apply Additive.ofMul.injective
    apply ι.injective
    rw [hφ, ofMul_pow, map_nsmul]
    funext i
    rw [Matrix.vecMul_diagonal, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, mul_comm]
  have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have h1 : φ ^ 2 = 1 := hSc φ (mem_ggAutomizer_iff.mp (hle hφA)) ⟨2, hφ2⟩
  set b : ↥Bs := Additive.toMul (ι.symm (Pi.single 0 1)) with hb
  have hbb : φ (φ b) = b := by
    rw [← MulAut.mul_apply, ← pow_two, h1]
    rfl
  rw [hφ2, hφ2, ← pow_mul] at hbb
  have h4 := congrArg (fun z : ↥Bs => ι (Additive.ofMul z) 0) hbb
  simp only [ofMul_pow, map_nsmul, hb, ofMul_toMul, AddEquiv.apply_symm_apply, Pi.smul_apply,
    Pi.single_eq_same, nsmul_eq_mul, mul_one] at h4
  revert h4
  decide

theorem ggForkNbrSevenExcl_of_known (hRig : GGLabelRigidInput)
    (hTCJ : GGTCJKnown) (hTP : GGForkA8TablePInput) (hCoord : GGForkA8CoordInput) :
    GGForkNbrSevenExcl := by
  intro G _ _ B Bs x L D J hC _ hID hNT hSc y K hK hKA8
  obtain ⟨lab, labJ, hlab, hsplit, hhasL, hlabJ, hdvd, hhasJ⟩ := ggNbr_label_J_of_tcj hTCJ hC hK
  have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
  have hn1 : 1 ≤ lab.n := hlab.1
  obtain ⟨hTPJ, hTPL⟩ := hTP G 7 B Bs x L D J hC hID rfl y K hK (Or.inl hKA8)
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ := hTPJ labJ hlabJ hhasJ
  have hkA : klab = ⟨.A, 8, 1⟩ := eq_of_ggLabelIso_of_exc (Or.inl rfl)
    (hRig klab ⟨.A, 8, 1⟩ _ hkΛ largeEvenInLambda2_a8 hhasK1 hKA8)
  subst hkA
  obtain ⟨t, r, n⟩ := jlab
  have hLlab : GGHasLabel ⟨.A, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
      GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
      GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L) := by
    rcases ggTablePRow_a8_left hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hlabJ hjΛ hhasJ hhasJ1
        with rfl | ⟨h23, -⟩
      · have hdvd3 : lab.n ∣ 3 := hdvd
        have h33 := Nat.le_of_dvd (by norm_num) hdvd3
        have hL3 : lab.n = 3 := by omega
        obtain ⟨jlab2, llab2, hj2Λ, hl2Λ, hrow2, hhasJ2, hhasL2⟩ :=
          hTPL ⟨.A, 2, 3⟩ lab hlabJ hlab hhasJ hhasL
        rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hj2Λ hjΛ hhasJ2 hhasJ
          with rfl | ⟨h23, -⟩
        · obtain ⟨t2, r2, n2⟩ := llab2
          rcases ggTablePRow_a23_right hrow2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
              ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact Or.inl hhasL2
          · exact Or.inr (Or.inl hhasL2)
          · exact Or.inl (ggHasLabel_D3_iff_A3.1 hhasL2)
          · exact Or.inr (Or.inr hhasL2)
          · exfalso
            rcases ggLabelIso_typeA_cases hRig (r := 8) (f := 1) (by norm_num) hlab
                largeEvenInLambda2_a8 hhasL hhasL2 with rfl | ⟨h83, -⟩
            · have hL1 : (1 : ℕ) = 3 := hL3
              omega
            · omega
        · omega
      · omega
    · exfalso
      rcases ggLabelIso_typeA_cases hRig (r := 5) (f := 1) (by norm_num) hlabJ hjΛ hhasJ hhasJ1
        with rfl | ⟨h53, -⟩
      · have := Nat.le_of_dvd one_pos hdvd
        omega
      · omega
  have hKmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 :=
    statedClassicalModel_of_hasLabel_typeA (n := 8) (f := 1) largeEvenInLambda2_a8 hKA8
  obtain ⟨c, ι, hcall, hgen, -⟩ := hCoord G 7 B Bs x L D J hC hID hNT rfl y K hK hKmodel hLlab
  by_cases hc : c ∈ excCases
  · exact ggA8Nbr_false_of_coord_exc L K hSc ι hc hgen
  · exact ggA8Nbr_false_of_coord L K hNT ι hcall hc hgen

end CFSG.StandardType

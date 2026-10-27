module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.SmallFourLabels
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped MatrixGroups Matrix

theorem k14_2Small_two {I : Type} [CommGroup I] [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {X L : Subgroup (MulAut I)} (hLX : L ≤ X) (hLn : (L.subgroupOf X).Normal)
    (hirr : IsIrrOn L ⊤ ⊥) {e : ℕ} (he : e = 2 ∨ e = 4) (hS : IsSL3 ↥L e)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {U : Type} [AddCommGroup U]
    [Module (ZMod 2) U] [Finite U] (θ : I ≃* Multiplicative U) (φ : SL(3, F) →* ↥L)
    (ρ : Representation (ZMod 2) SL(3, F) U) (hF : Fintype.card F = 2 ^ e)
    (hφ : X7Sec.Cover φ) (hρ : ∀ g u, ρ g u = Layer.binPsi θ ((φ g : ↥L) : MulAut I) u)
    (hnat : IsTwistedNatural ρ) (hm : E3.mParam X ≤ 2) :
    IsSL3 ↥L 2 ∧ Subgroup.center ↥L ≠ ⊥ ∧ rk ↥(⊤ : Subgroup I) = 6 ∧ E3.mParam X = 2 ∧
      ∀ c : MulAut I, (∀ l ∈ L, c * l = l * c) → c ^ 3 = 1 := by
  classical
  obtain ⟨ψ, hψ, E, hE⟩ := hnat
  have hcardFNat : Nat.card F = 2 ^ e := by
    rw [Nat.card_eq_fintype_card, hF]
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hρx : ∀ u, ρ x u = u := by
      intro u
      rw [hρ x u, hx]
      simp
    have hψx : ψ x = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one]
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      obtain ⟨w, rfl⟩ := E.surjective v
      rw [← hE x w, hρx w, Matrix.one_mulVec]
    calc x = ψ (ψ x) := (hψ x).symm
      _ = ψ 1 := by rw [hψx]
      _ = 1 := map_one ψ
  let φ' : SL(3, F) ≃* ↥L := MulEquiv.ofBijective φ ⟨hφinj, hφ.surjective⟩
  let ψe : SL(3, F) ≃* SL(3, F) :=
    { ψ with invFun := ψ, left_inv := hψ, right_inv := hψ }
  let eSL : SL(3, F) ≃* ↥(StatedSL 3 F) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  let Θ : ↥L ≃* ↥(StatedSL 3 F) := φ'.symm.trans (ψe.trans eSL)
  have hΘ : ∀ x : SL(3, F), Θ (φ' x) = eSL (ψ x) := fun x => by
    simp [Θ, ψe]
  have hIsSLn : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn ↥L 3 e :=
    ⟨F, inferInstance, inferInstance, hcardFNat, ⟨Θ⟩⟩
  have hreal : (FFModel.nat (StatedSL 3 F)).Realizes L ⊤ ⊥ := by
    refine realizes_nat_of_equiv
      θ Θ E ?_
    intro l w
    obtain ⟨x, rfl⟩ := φ'.surjective l
    rw [show Layer.binPsi θ (((φ' x : ↥L) : MulAut I)) w = ρ x w from (hρ x w).symm,
      hE x w, hΘ x, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  have hBin : BinaryNaturalSL L ⊤ ⊥ 3 e :=
    ⟨F, inferInstance, inferInstance, hcardFNat, hreal⟩
  have hnatNat : IsNaturalClassicalModule L e :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hIsSLn, hBin⟩))))
  have hcardI : Nat.card I = Nat.card F ^ 3 := by
    calc Nat.card I = Nat.card (Multiplicative U) := Nat.card_congr θ.toEquiv
      _ = Nat.card U := Nat.card_congr Multiplicative.toAdd
      _ = Nat.card (Fin 3 → F) := Nat.card_congr E.toEquiv
      _ = Nat.card F ^ Nat.card (Fin 3) := Nat.card_fun
      _ = Nat.card F ^ 3 := by rw [Nat.card_fin]
  have hcardI2 : Nat.card I = 2 ^ (3 * e) := by
    rw [hcardI, Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm e 3]
  have hrkI : rk I = 3 * e := by
    show padicValNat 2 (Nat.card I) = 3 * e
    rw [hcardI2, padicValNat.prime_pow]
  have heven : Even (Nat.card ↥X) := by
    rcases Nat.even_or_odd (Nat.card ↥X) with h | h
    · exact h
    · exfalso
      have hne : ¬ Even (Nat.card ↥X) := by
        intro he'
        rcases h with ⟨a, ha⟩
        rcases he' with ⟨b, hb⟩
        omega
      have hm' : E3.mParam X = rk I := by
        rw [E3.mParam, if_neg hne]
      rw [hm', hrkI] at hm
      omega
  have hle : e ≤ E3.mParam X :=
    le_mParam_of_isNaturalClassicalModule
      hI hLX hLn hirr hnatNat heven
  have he2 : e = 2 := by omega
  have hSL3 : IsSL3 ↥L 2 := by simpa only [he2] using hS
  have hmParam : E3.mParam X = 2 := le_antisymm hm (by omega)
  have hrkTop : rk ↥(⊤ : Subgroup I) = 6 := by
    have htop : Nat.card ↥(⊤ : Subgroup I) = Nat.card I := by simp
    have h3 : rk ↥(⊤ : Subgroup I) = 3 * e := by
      show padicValNat 2 (Nat.card ↥(⊤ : Subgroup I)) = 3 * e
      rw [htop]
      exact hrkI
    rw [h3, he2]
  have hcardF4 : Fintype.card F = 4 := by
    rw [hF, he2]
    norm_num
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcardUnits : Fintype.card Fˣ = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_eq_fintype_card, hcardF4]
  obtain ⟨u, hu⟩ :=
    Fintype.exists_ne_of_one_lt_card (by rw [hcardUnits]; norm_num) (1 : Fˣ)
  have hu3 : (u : F) ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (u : F) (Units.ne_zero u)
    rw [hcardF4] at h
    simpa using h
  let z : SL(3, F) := ⟨Matrix.scalar (Fin 3) (u : F), by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    exact hu3⟩
  have hzmem : z ∈ LinearFlag.scalars 3 F := ⟨u, Units.ext hu3, rfl⟩
  have hz1 : z ≠ 1 := by
    intro hz
    apply hu
    apply Units.ext
    have hmat := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F)) hz
    have h00 := congrFun (congrFun hmat 0) 0
    simpa [z, Matrix.scalar_apply, Matrix.one_apply] using h00
  have hφz : φ z ≠ 1 := by
    intro h
    exact hz1 (hφinj (by simpa using h))
  have hcenter : Subgroup.center ↥L ≠ ⊥ := by
    intro hbot
    have hmem : φ z ∈ Subgroup.center ↥L := by
      rw [← hφ.map_scalars]
      exact Subgroup.mem_map_of_mem φ hzmem
    rw [hbot] at hmem
    exact hφz (Subgroup.mem_bot.mp hmem)
  refine ⟨hSL3, hcenter, hrkTop, hmParam, ?_⟩
  intro c hc
  set σ : U ≃ₗ[ZMod 2] U := Layer.binPsi θ c with hσ
  have hσρ : ∀ (x : SL(3, F)) (u : U), σ (ρ x u) = ρ x (σ u) := by
    intro x u
    have hφx : ∀ u : U, Layer.binPsi θ (((φ x : ↥L) : MulAut I)) u = ρ x u :=
      fun u => (hρ x u).symm
    calc σ (ρ x u) = Layer.binPsi θ c (Layer.binPsi θ (((φ x : ↥L) : MulAut I)) u) := by
          rw [hσ, ← hφx u]
      _ = Layer.binPsi θ (c * ((φ x : ↥L) : MulAut I)) u := by
          rw [map_mul, LinearEquiv.mul_apply]
      _ = Layer.binPsi θ (((φ x : ↥L) : MulAut I) * c) u := by rw [hc _ (φ x).2]
      _ = Layer.binPsi θ (((φ x : ↥L) : MulAut I)) (Layer.binPsi θ c u) := by
          rw [map_mul, LinearEquiv.mul_apply]
      _ = ρ x (σ u) := by rw [hφx (Layer.binPsi θ c u), hσ]
  let f : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => E (σ (E.symm v))
      map_zero' := by simp
      map_add' := by intro v w; simp [map_add] }
  have hfval : ∀ v, f v = E (σ (E.symm v)) := fun v => rfl
  have hfcomm : ∀ γ ∈ StatedSL 3 F, ∀ v,
      f ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ f v := by
    intro γ hγ v
    obtain ⟨g, hg⟩ := eSL.surjective ⟨γ, hγ⟩
    let x : SL(3, F) := ψ g
    have hx : ψ x = g := hψ g
    have hγmat : (γ : Matrix (Fin 3) (Fin 3) F) = ((ψ x : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) := by
      have hgl : (eSL g : GL (Fin 3) F) = γ := congrArg Subtype.val hg
      rw [← hgl, hx]
      exact CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F g
    rw [hfval, hγmat]
    have h2 : ((ψ x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        E (ρ x (E.symm v)) := by
      rw [hE x (E.symm v), AddEquiv.apply_symm_apply]
    rw [h2, AddEquiv.symm_apply_apply]
    have hσρx : σ (ρ x (E.symm v)) = ρ x (σ (E.symm v)) := hσρ x (E.symm v)
    rw [hσρx, hE x (σ (E.symm v)), hfval]
  obtain ⟨c₀, hc₀⟩ :=
    CFSG.Quasithin.H.hasScalarCommutant_statedSL (d := 3) (K := F) (by norm_num) f hfcomm
  have hsingle : (Pi.single (0 : Fin 3) (1 : F) : Fin 3 → F) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hfv0 : f (Pi.single (0 : Fin 3) (1 : F)) ≠ 0 := by
    intro h
    have h1 : σ (E.symm (Pi.single (0 : Fin 3) (1 : F))) = 0 := by
      have := congrArg E.symm h
      simpa [hfval] using this
    have h2 : E.symm (Pi.single (0 : Fin 3) (1 : F)) = 0 := by
      exact σ.injective (by rw [h1, map_zero])
    have h3 : (Pi.single (0 : Fin 3) (1 : F) : Fin 3 → F) = 0 := by
      have := congrArg E h2
      simpa using this
    exact hsingle h3
  have hc0 : c₀ ≠ 0 := by
    intro h0
    apply hfv0
    rw [hc₀]
    simp [h0]
  have hc03 : c₀ ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one c₀ hc0
    rw [hcardF4] at h
    simpa using h
  have hf3 : ∀ v, f (f (f v)) = v := by
    intro v
    calc f (f (f v)) = c₀ • (c₀ • (c₀ • v)) := by simp only [hc₀]
      _ = (c₀ * c₀ * c₀) • v := by rw [smul_smul, smul_smul]
      _ = v := by
            have hc : c₀ * c₀ * c₀ = 1 := by
              rw [show c₀ * c₀ * c₀ = c₀ ^ 3 by ring, hc03]
            rw [hc, one_smul]
  have hσ3 : σ ^ 3 = 1 := by
    apply LinearEquiv.ext
    intro u
    have hv := hf3 (E u)
    simp only [hfval, AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply] at hv
    have h3 : σ (σ (σ u)) = u := E.injective hv
    simpa [pow_succ, LinearEquiv.mul_apply] using h3
  apply (Layer.binPsi θ).injective
  rw [map_pow, map_one]
  rw [← hσ]
  exact hσ3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

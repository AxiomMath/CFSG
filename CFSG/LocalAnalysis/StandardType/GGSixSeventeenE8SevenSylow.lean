module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenE8Seven
public import CFSG.RankThree.PartOne.KE6.E8T3Frame
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderNine
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE.E8FiveArith
public import CFSG.RankThree.PartOne.KE.SLnDescended
public import CFSG.RankThree.PartOne.KE.SLnFamily
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KE6.E8T3A2
public import CFSG.RankThree.PartOne.KE6.E8T3Act
public import CFSG.RankThree.PartOne.KE6.E8T3Conj
public import CFSG.RankThree.PartOne.KE6.E8T3Supports
public import CFSG.RankThree.PartOne.KE6.E8T3Trans
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE6

@[expose] def GGSixSeventeenE8SevenCompInput : Prop :=
  ∀ b : ↥(adjointGroup .E8 (GaloisField 2 1)), orderOf b = 7 →
    ∃ L : Subgroup ↥(adjointGroup .E8 (GaloisField 2 1)),
      IsComponentOf L (Subgroup.centralizer {b}) ∧ 7 ^ 2 ∣ Nat.card L ∧
        ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 7 = 1 → z = 1

section Sylow

theorem card_le_of_isPGroup_seven_E8Two {Q : Subgroup ↥(adjointGroup .E8 (GaloisField 2 1))}
    (hQ : IsPGroup 7 Q) : Nat.card Q ≤ 7 ^ 4 := by
  classical
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  have : CharP (AlgebraicClosure (GaloisField 2 1)) 2 :=
    charP_of_injective_algebraMap (algebraMap (GaloisField 2 1)
      (AlgebraicClosure (GaloisField 2 1))).injective 2
  have : IsAlgClosed (AlgebraicClosure (GaloisField 2 1)) :=
    IsAlgClosure.isAlgClosed (GaloisField 2 1)
  have hcm := canonicalRep_mem_monomialSubgroup (AlgebraicClosure (GaloisField 2 1)) (e8T3We 1)
  have hπ : weylQuotientHom .E8 (AlgebraicClosure (GaloisField 2 1))
      ⟨canonicalRep (coxeterSystem .E8) (AlgebraicClosure (GaloisField 2 1)) (e8T3We 1), hcm⟩ =
        e8T3We 1 :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hpf : ((7 : ℕ) : ℤ) ∣ (Nat.card (GaloisField 2 1) : ℤ) ^ 2 +
      1 * (Nat.card (GaloisField 2 1) : ℤ) + 1 := by
    rw [hK]
    norm_num
  obtain ⟨g0, -, -, -, hconj⟩ := e8T3_frame (Or.inl rfl) (GaloisField 2 1) le_rfl hK
    (by norm_num) (by norm_num) hpf (AlgebraicClosure (GaloisField 2 1)) _ hcm hπ
  obtain ⟨c, hc⟩ := hconj Q hQ
  have hcard := natCard_e8T3Torus (Or.inl rfl) _ hcm hπ
    (Fr := iterateFrobenius (AlgebraicClosure (GaloisField 2 1)) 2 1) (q := 2)
    (fun x => by rw [iterateFrobenius_def, pow_one]) dvd_rfl
  have h7 : e8T3D 1 2 = 7 := by decide
  rw [h7] at hcard
  have : Finite (twistedTorusOf (canonicalRep (coxeterSystem .E8)
      (AlgebraicClosure (GaloisField 2 1)) (e8T3We 1))
      (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure (GaloisField 2 1)) 2 1)))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rw [← hcard]
  refine Nat.card_le_card_of_injective
    (fun y : Q => (⟨g0⁻¹ * adjEmb .E8 (GaloisField 2 1) (AlgebraicClosure (GaloisField 2 1))
      (c * y * c⁻¹) * g0, (mem_subtorusImage_iff _ _ _ _).1 (hc y y.2)⟩ : twistedTorusOf _ _))
    fun y y' hyy => Subtype.ext ?_
  have h1 := congrArg Subtype.val hyy
  simp only [mul_left_inj, mul_right_inj] at h1
  have h2 := adjEmb_injective h1
  simpa using h2

theorem ggSixSeventeenE8SevenCentInput_of_comp (h : GGSixSeventeenE8SevenCompInput) :
    GGSixSeventeenE8SevenCentInput := by
  classical
  intro b hb
  obtain ⟨L, hL, hdvd, hZ⟩ := h b hb
  refine ⟨L, hL, fun A _ hAL hA => ?_⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime 7 hdvd
  have hEL : E₀.map L.subtype ≤ L := Subgroup.map_subtype_le E₀
  have hEcard : Nat.card (E₀.map L.subtype) = 7 ^ 2 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hE₀]
  have hcomm : ∀ (a : A) (e : E₀.map L.subtype),
      Commute (A.subtype a) ((E₀.map L.subtype).subtype e) := fun a e =>
    (Subgroup.mem_centralizer_iff.mp (hAL a.2) e (hEL e.2)).symm
  have hφinj : Function.Injective (MonoidHom.noncommCoprod _ _ hcomm) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, e⟩ hae
    rw [MonoidHom.noncommCoprod_apply] at hae
    have hae' : (a : ↥(adjointGroup .E8 (GaloisField 2 1))) = (e : _)⁻¹ :=
      eq_inv_of_mul_eq_one_left hae
    have haL : (a : ↥(adjointGroup .E8 (GaloisField 2 1))) ∈ L :=
      hEL (hae' ▸ (E₀.map L.subtype).inv_mem e.2)
    have ha1 : (a : ↥(adjointGroup .E8 (GaloisField 2 1))) = 1 :=
      hZ _ haL (fun l hl => (Subgroup.mem_centralizer_iff.mp (hAL a.2) l hl).symm) (hA.2 _ a.2)
    have he1 : (e : ↥(adjointGroup .E8 (GaloisField 2 1))) = 1 := by
      rw [ha1, eq_comm, Subgroup.coe_inv, inv_eq_one] at hae'
      exact hae'
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext he1)
  obtain ⟨k, hk⟩ := (TableB.isPGroup_of_isElemAbelian hA).exists_card_eq
  have hcardR : Nat.card (MonoidHom.noncommCoprod _ _ hcomm).range =
      Nat.card (A × (E₀.map L.subtype)) :=
    Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm
  have hR : IsPGroup 7 (MonoidHom.noncommCoprod _ _ hcomm).range :=
    IsPGroup.of_card (n := k + 2) (by rw [hcardR, Nat.card_prod, hk, hEcard, pow_add])
  have hle := card_le_of_isPGroup_seven_E8Two hR
  rw [hcardR, Nat.card_prod, hEcard] at hle
  exact Nat.le_of_mul_le_mul_right (by norm_num at hle ⊢; omega) (by norm_num : 0 < 7 ^ 2)

end Sylow

end CFSG.StandardType

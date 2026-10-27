module

public import CFSG.RankThree.PartOne.SEITZ7.D4Tor
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxSL2
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.SEITZ7.D4Elim
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3
open scoped commutatorElement

theorem commute_map_of_closure {G H₁ H₂ : Type*} [Group G] [Group H₁] [Group H₂]
    (f : H₁ →* G) (g : H₂ →* G) {P₁ : Set H₁} {P₂ : Set H₂}
    (h₁ : Subgroup.closure P₁ = ⊤) (h₂ : Subgroup.closure P₂ = ⊤)
    (h : ∀ x ∈ P₁, ∀ y ∈ P₂, Commute (f x) (g y)) (M : H₁) (N : H₂) :
    Commute (f M) (g N) := by
  have hM : M ∈ Subgroup.closure P₁ := h₁ ▸ Subgroup.mem_top M
  induction hM using Subgroup.closure_induction generalizing N with
  | mem x hx =>
    have hN : N ∈ Subgroup.closure P₂ := h₂ ▸ Subgroup.mem_top N
    induction hN using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => simp
    | mul y z _ _ hy hz => rw [map_mul]; exact hy.mul_right hz
    | inv y _ hy => rw [map_inv]; exact hy.inv_right
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact (hx N).mul_left (hy N)
  | inv x _ hx => rw [map_inv]; exact (hx N).inv_left

variable {K : Type} [Field K] (σ : K →+* K)

theorem commute_22_4 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 4 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_6 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 6 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_10 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 10 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_23_0 [CharP K 2] (x y : K) : Commute (xd 23 x) (xd 0 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_23_1 [CharP K 2] (x y : K) : Commute (xd 23 x) (xd 1 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_23_3 [CharP K 2] (x y : K) : Commute (xd 23 x) (xd 3 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_23_4 [CharP K 2] (x y : K) : Commute (xd 23 x) (xd 4 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_23_6 [CharP K 2] (x y : K) : Commute (xd 23 x) (xd 6 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_23_10 [CharP K 2] (x y : K) : Commute (xd 23 x) (xd 10 y) :=
  commute_gen (by decide +kernel) x y

@[expose] noncomputable def xAm (a : K) : adjointGroup d4 K :=
  xd 4 a * xd 6 (σ a) * xd 10 (σ (σ a))

theorem commute_xA_x23 [CharP K 2] (a c : K) : xA σ a * xd 23 c = xd 23 c * xA σ a :=
  (((commute_23_0 c a).mul_right (commute_23_1 c (σ a))).mul_right
    (commute_23_3 c (σ (σ a)))).symm.eq

theorem commute_xAm_x22 [CharP K 2] (a c : K) : xAm σ a * xd 22 c = xd 22 c * xAm σ a :=
  (((commute_22_4 c a).mul_right (commute_22_6 c (σ a))).mul_right
    (commute_22_10 c (σ (σ a)))).symm.eq

theorem commute_xAm_x23 [CharP K 2] (a c : K) : xAm σ a * xd 23 c = xd 23 c * xAm σ a :=
  (((commute_23_4 c a).mul_right (commute_23_6 c (σ a))).mul_right
    (commute_23_10 c (σ (σ a)))).symm.eq

theorem d4Root_dict : d4Root 2 = Pi.single (nd 2) 1 ∧ d4Root 8 = -Pi.single (nd 2) 1 ∧
    d4Root 0 = (1 : ℤ) • Pi.single (nd 0) 1 ∧ d4Root 1 = (1 : ℤ) • Pi.single (nd 1) 1 ∧
    d4Root 3 = (1 : ℤ) • Pi.single (nd 3) 1 ∧ d4Root 4 = (-1 : ℤ) • Pi.single (nd 0) 1 ∧
    d4Root 6 = (-1 : ℤ) • Pi.single (nd 1) 1 ∧ d4Root 10 = (-1 : ℤ) • Pi.single (nd 3) 1 := by
  decide +kernel

@[expose] noncomputable def Wg (σ : K →+* K) : twistedGroup σ := nHat σ (ng 0) * nHat σ (ng 1)

theorem Wg_val : ((Wg σ : twistedGroup σ) : adjointGroup d4 K) = Wt := rfl

@[expose] noncomputable def psiB (hσ : ∀ c, σ (σ (σ c)) = c) :
    Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* twistedGroup σ :=
  (MulAut.conj (Wg σ)).toMonoidHom.comp (slLong σ hσ)

theorem psiB_injective (hσ : ∀ c, σ (σ (σ c)) = c) : Function.Injective (psiB σ hσ) :=
  (MulAut.conj (Wg σ)).injective.comp (slLong_injective hσ)

theorem psiB_upper [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : fixedField σ) :
    ((psiB σ hσ (sl2Upper c) : twistedGroup σ) : adjointGroup d4 K) = xH (c : K) := by
  have h := Wt_xB (K := K) (c : K)
  have e : xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (c : K) = xd 2 (c : K) := by
    simp only [xd, d4Root_dict.1]
  simp only [psiB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, Wg_val, slLong_val, slLongE_upper]
  rw [e]
  exact h

theorem psiB_lower [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : fixedField σ) :
    ((psiB σ hσ (sl2Lower c) : twistedGroup σ) : adjointGroup d4 K) = xd 23 (c : K) := by
  have h := Wt_xBneg (K := K) (c : K)
  have e : xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) (c : K) = xd 8 (c : K) := by
    simp only [xd, d4Root_dict.2.1]
  simp only [psiB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, Wg_val, slLong_val, slLongE_lower]
  rw [e]
  exact h

theorem slShort_upper_xA [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : K) :
    ((slShort σ hσ (sl2Upper c) : twistedGroup σ) : adjointGroup d4 K) = xA σ c := by
  rw [slShort_upper]
  simp only [xOuter, xA, ← d4Root_dict.2.2.1, ← d4Root_dict.2.2.2.1, ← d4Root_dict.2.2.2.2.1]

theorem slShort_lower_xAm [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : K) :
    ((slShort σ hσ (sl2Lower c) : twistedGroup σ) : adjointGroup d4 K) = xAm σ c := by
  rw [slShort_lower]
  simp only [xOuter, xAm, ← d4Root_dict.2.2.2.2.2.1, ← d4Root_dict.2.2.2.2.2.2.1,
    ← d4Root_dict.2.2.2.2.2.2.2]

@[expose] def dSL {k : Type*} [Field k] (t : kˣ) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![(t : k), 0; 0, ((t⁻¹ : kˣ) : k)], by simp [Matrix.det_fin_two_of]⟩

theorem slShort_dSL (hσ : ∀ c, σ (σ (σ c)) = c) (t : Kˣ) :
    ((slShort σ hσ (dSL t) : twistedGroup σ) : adjointGroup d4 K) = hShortHom σ t := by
  have h : (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm (dSL t) =
      ⟨torusElement d4 K (nd 0) t, torusElement_mem_rankOne (nd 0) t⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext
      (restrictHom_torusElement cartan_zero_two t (torusElement_mem_rankOne (nd 0) t)).symm
  simp only [slShort, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, phiShortTw_val]
  exact phiShort_torusElement σ t

theorem slLongE_dSL (r : (fixedField σ)ˣ) :
    slLongE σ (dSL r) =
      torusElement d4 K (nd 2) (Units.map (fixedField σ).subtype.toMonoidHom r) := by
  have e : Matrix.SpecialLinearGroup.map (fixedField σ).subtype (dSL r) =
      dSL (Units.map (fixedField σ).subtype.toMonoidHom r) :=
    Subtype.ext (by
      ext p q
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply]
      fin_cases p <;> fin_cases q <;> simp [dSL, Units.val_inv_eq_inv_val])
  have h : (restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm
      (dSL (Units.map (fixedField σ).subtype.toMonoidHom r)) =
      ⟨torusElement d4 K (nd 2) (Units.map (fixedField σ).subtype.toMonoidHom r),
        torusElement_mem_rankOne (nd 2) _⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext
      (restrictHom_torusElement cartan_two_zero _ (torusElement_mem_rankOne (nd 2) _)).symm
  simp only [slLongE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, h,
    Subgroup.coe_subtype]

@[expose] noncomputable def Asub (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) :
    Subgroup (twistedGroup σ) := (slShort σ hσ).range

@[expose] noncomputable def Bsub (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) :
    Subgroup (twistedGroup σ) := (psiB σ hσ).range

@[expose] noncomputable def Lsub (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) :
    Subgroup (twistedGroup σ) := Asub σ hσ ⊔ Bsub σ hσ

theorem Asub_le_Lsub (hσ : ∀ c, σ (σ (σ c)) = c) : Asub σ hσ ≤ Lsub σ hσ := le_sup_left

theorem Bsub_le_Lsub (hσ : ∀ c, σ (σ (σ c)) = c) : Bsub σ hσ ≤ Lsub σ hσ := le_sup_right

theorem hHat_one_le_Asub (hσ : ∀ c, σ (σ (σ c)) = c) : hHat σ (ng 1) ≤ Asub σ hσ := by
  intro g hg
  obtain ⟨t, ht⟩ : (g : adjointGroup d4 K) ∈ (hShortHom σ).range := hg
  refine ⟨dSL t, Subtype.ext ?_⟩
  rw [slShort_dSL, ht]

theorem hB_mem_Lsub [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {g : twistedGroup σ}
    {s : Kˣ} (hs : σ (s : K) = (s : K))
    (hg : (g : adjointGroup d4 K) = torusElement d4 K (nd 2) s) : g ∈ Lsub σ hσ := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (s : K)
  have hr0 : r ≠ 0 := fun h => s.ne_zero (by rw [hr, h, mul_zero])
  have hrfix : σ r = r := by
    have h1 : σ r * σ r = r * r := by rw [← map_mul, ← hr]; exact hs
    have h2 : (σ r + r) ^ 2 = 0 := by
      rw [CharTwo.add_sq, sq, sq, h1, CharTwo.add_self_eq_zero]
    exact CharTwo.add_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).mp h2)
  set r' : Kˣ := Units.mk0 r hr0 with hr'
  have hsr : s = r' ^ 2 := Units.ext (by simp [hr', hr, sq])
  have hσr' : Units.map σ.toMonoidHom r' = r' := Units.ext hrfix
  let ρ : (fixedField σ)ˣ := Units.mk0 ⟨r, hrfix⟩ (fun h => hr0 (congrArg Subtype.val h))
  have hρ : Units.map (fixedField σ).subtype.toMonoidHom ρ = r' := Units.ext rfl
  have hB : ((psiB σ hσ (dSL ρ) : twistedGroup σ) : adjointGroup d4 K) =
      torusElement d4 K (nd 2) s * hShortHom σ r' := by
    simp only [psiB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, Wg_val, slLong_val, slLongE_dSL, hρ]
    rw [Wt_hB, hsr, hShortHom_apply]
    simp only [hσr']
  have hA : ((slShort σ hσ (dSL r') : twistedGroup σ) : adjointGroup d4 K) = hShortHom σ r' :=
    slShort_dSL σ hσ r'
  have hmem : g = psiB σ hσ (dSL ρ) * (slShort σ hσ (dSL r'))⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hB, hA, hg]
    group
  rw [hmem]
  exact Subgroup.mul_mem _ (Bsub_le_Lsub σ hσ ⟨dSL ρ, rfl⟩)
    (Subgroup.inv_mem _ (Asub_le_Lsub σ hσ ⟨dSL r', rfl⟩))

theorem hHat_le_Lsub [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) (i : Fin (Tag.rank .G2)) :
    hHat σ i ≤ Lsub σ hσ := by
  fin_cases i
  · intro g hg
    obtain ⟨s, hs⟩ : (g : adjointGroup d4 K) ∈ (hLongHom σ).range := hg
    exact hB_mem_Lsub σ hσ (s := (s : Kˣ)) ((mem_fixedUnits σ).1 s.2) hs.symm
  · exact (hHat_one_le_Asub σ hσ).trans (Asub_le_Lsub σ hσ)

local notation "uU" => CFSG.LocalAnalysis.ComponentInitial.sl2Upper
local notation "uL" => CFSG.LocalAnalysis.ComponentInitial.sl2Lower

theorem commute_of_val' {σ : K →+* K} {a b : twistedGroup σ}
    (h : (a : adjointGroup d4 K) * b = b * a) : Commute a b :=
  Subtype.ext (by simpa using h)

theorem slShort_commute_psi [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)
    (M : Matrix.SpecialLinearGroup (Fin 2) K)
    (N : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    Commute (slShort σ hσ M) (psiB σ hσ N) := by
  refine commute_map_of_closure (slShort σ hσ) (psiB σ hσ)
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K))
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixedField σ)) ?_ M N
  intro x hx y hy
  rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;> rcases hy with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have h1 : ((slShort σ hσ (uU K c) : twistedGroup σ) : adjointGroup d4 K) = xA σ c :=
      slShort_upper_xA σ hσ c
    have h2 : ((psiB σ hσ (uU (fixedField σ) d) : twistedGroup σ) : adjointGroup d4 K) =
        xH (d : K) :=
      psiB_upper σ hσ d
    refine commute_of_val' ?_
    rw [h1, h2]
    exact (commute_xH_xA σ (d : K) c).symm
  · have h1 : ((slShort σ hσ (uU K c) : twistedGroup σ) : adjointGroup d4 K) = xA σ c :=
      slShort_upper_xA σ hσ c
    have h2 : ((psiB σ hσ (uL (fixedField σ) d) : twistedGroup σ) : adjointGroup d4 K) =
        xd 23 (d : K) :=
      psiB_lower σ hσ d
    refine commute_of_val' ?_
    rw [h1, h2]
    exact commute_xA_x23 σ c (d : K)
  · have h1 : ((slShort σ hσ (uL K c) : twistedGroup σ) : adjointGroup d4 K) = xAm σ c :=
      slShort_lower_xAm σ hσ c
    have h2 : ((psiB σ hσ (uU (fixedField σ) d) : twistedGroup σ) : adjointGroup d4 K) =
        xH (d : K) :=
      psiB_upper σ hσ d
    refine commute_of_val' ?_
    rw [h1, h2]
    exact commute_xAm_x22 σ c (d : K)
  · have h1 : ((slShort σ hσ (uL K c) : twistedGroup σ) : adjointGroup d4 K) = xAm σ c :=
      slShort_lower_xAm σ hσ c
    have h2 : ((psiB σ hσ (uL (fixedField σ) d) : twistedGroup σ) : adjointGroup d4 K) =
        xd 23 (d : K) :=
      psiB_lower σ hσ d
    refine commute_of_val' ?_
    rw [h1, h2]
    exact commute_xAm_x23 σ c (d : K)

theorem Asub_Bsub_commute [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    ∀ a ∈ Asub σ hσ, ∀ b ∈ Bsub σ hσ, a * b = b * a := by
  rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
  exact slShort_commute_psi σ hσ M N

theorem Asub_inf_Bsub [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) : Asub σ hσ ⊓ Bsub σ hσ = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨M, rfl⟩, ⟨N, hN⟩⟩
  have hc : ∀ M' : Matrix.SpecialLinearGroup (Fin 2) K,
      M' * M = M * M' := by
    intro M'
    apply slShort_injective hσ
    rw [map_mul, map_mul, ← hN]
    exact (slShort_commute_psi σ hσ M' N).eq
  have hM : M ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Subgroup.mem_center_iff.2 fun M' => (hc M')
  rw [CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot, Subgroup.mem_bot] at hM
  rw [hM, map_one]
  exact Subgroup.one_mem _

end CFSG.RankThree.PartOne.SEITZ7

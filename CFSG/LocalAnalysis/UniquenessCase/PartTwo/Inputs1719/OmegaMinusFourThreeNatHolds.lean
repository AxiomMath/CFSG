module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaMinusThreeNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.Milestones.ASVolI.A3Spor.Out
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaMinusFourCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

abbrev O4Idx : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {B C : K}

def o4e1 : O4Idx → K := Pi.single (Sum.inl 0) 1

def o4e2 : O4Idx → K := Pi.single (Sum.inr (Sum.inl 0)) 1

def o4e3 : O4Idx → K := Pi.single (Sum.inr (Sum.inr 0)) 1

def o4e4 : O4Idx → K := Pi.single (Sum.inr (Sum.inr 1)) 1

def o4param (a b : K) : O4Idx → K := a • o4e3 + b • o4e4

noncomputable abbrev o4Q : QuadraticForm K (O4Idx → K) := quadMinus 2 K B C

theorem o4Q_apply (v : O4Idx → K) :
    o4Q (B := B) (C := C) v =
      v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
        B * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
        C * v (Sum.inr (Sum.inr 1)) ^ 2 := by
  rw [o4Q, quadMinus_apply, Fin.sum_univ_one]

theorem o4Q_e1 : o4Q (B := B) (C := C) o4e1 = 0 := by
  rw [o4Q_apply]
  simp [o4e1]

def o4c1 (x : O4Idx → K) : K := x (Sum.inl 0)

def o4c2 (x : O4Idx → K) : K := x (Sum.inr (Sum.inl 0))

def o4c3 (x : O4Idx → K) : K := x (Sum.inr (Sum.inr 0))

def o4c4 (x : O4Idx → K) : K := x (Sum.inr (Sum.inr 1))

omit [Finite K] [CharP K 2] in
theorem o4_eq_of_c1_eq {x y : O4Idx → K}
    (hx : o4c2 x = 0 ∧ o4c3 x = 0 ∧ o4c4 x = 0) (hy : o4c2 y = 0 ∧ o4c3 y = 0 ∧ o4c4 y = 0)
    (h1 : o4c1 x = o4c1 y) : x = y := by
  funext i
  rcases i with i | i | i
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h1
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact hx.1.trans hy.1.symm
  · fin_cases i
    · exact hx.2.1.trans hy.2.1.symm
    · exact hx.2.2.trans hy.2.2.symm

theorem polar_o4Q_apply (x y : O4Idx → K) :
    polar (⇑(o4Q (B := B) (C := C))) x y =
      o4c1 x * o4c2 y + o4c2 x * o4c1 y +
        B * (o4c3 x * o4c4 y + o4c4 x * o4c3 y) := by
  rw [o4Q, polar_quadMinus, Fin.sum_univ_one]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [o4c1, o4c2, o4c3, o4c4, h2]
  ring

theorem polar_e1_param (a b : K) :
    polar (⇑(o4Q (B := B) (C := C))) o4e1 (o4param a b) = 0 := by
  rw [polar_o4Q_apply]
  simp [o4e1, o4c1, o4c2, o4c3, o4c4, o4param, o4e3, o4e4]

theorem o4param_add (a b a' b' : K) :
    o4param a b + o4param a' b' = o4param (a + a') (b + b') := by
  simp only [o4param, add_smul]
  abel

noncomputable def o4sylowLin (a b : K) : (O4Idx → K) ≃ₗ[K] (O4Idx → K) :=
  eichler (o4Q (B := B) (C := C)) o4e1 (o4param a b)

theorem o4sylowLin_mul (a b a' b' : K) :
    o4sylowLin (B := B) (C := C) a b * o4sylowLin (B := B) (C := C) a' b' =
      o4sylowLin (B := B) (C := C) (a + a') (b + b') := by
  rw [o4sylowLin, o4sylowLin, o4sylowLin,
    eichler_mul (polar_e1_param a b) (polar_e1_param a' b'), o4param_add]

theorem o4sylowLin_one :
    o4sylowLin (B := B) (C := C) 0 0 = 1 := by
  rw [o4sylowLin, o4param]
  simp only [zero_smul, add_zero, eichler_zero_right]

theorem o4sylowLin_apply (a b : K) (x : O4Idx → K) :
    o4sylowLin (B := B) (C := C) a b x =
      x + o4c2 x • o4param a b -
        (B * (a * o4c4 x + b * o4c3 x) +
          o4Q (B := B) (C := C) (o4param a b) * o4c2 x) • o4e1 := by
  rw [o4sylowLin, eichler_apply (o4Q_e1 (B := B) (C := C)) (polar_e1_param a b)]
  simp [polar_o4Q_apply, o4e1, o4c1, o4c2, o4c3, o4c4, o4param, o4e3, o4e4]
  ring

theorem o4sylowLin_apply_e2 (a b : K) :
    o4sylowLin (B := B) (C := C) a b o4e2 =
      o4e2 + o4param a b - (o4Q (B := B) (C := C) (o4param a b)) • o4e1 := by
  rw [o4sylowLin_apply]
  simp [o4e2, o4c1, o4c2, o4c3, o4c4]

theorem o4sylowLin_injective : Function.Injective
    (fun p : K × K => o4sylowLin (B := B) (C := C) p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h2 := congrArg (fun e : (O4Idx → K) ≃ₗ[K] (O4Idx → K) => e o4e2) h
  simp only [o4sylowLin_apply_e2] at h2
  have h3 := congrFun h2 (Sum.inr (Sum.inr 0))
  have h4 := congrFun h2 (Sum.inr (Sum.inr 1))
  simp [o4e2, o4e1, o4c1, o4c2, o4c3, o4c4, o4param, o4e3, o4e4] at h3 h4
  exact Prod.ext h3 h4

theorem B_ne_zero (hirr : ∀ s : K, s ^ 2 + B * s + C ≠ 0) : B ≠ 0 := by
  intro hB
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (R := K) C
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  exact hirr s (by
    rw [hB, zero_mul, hs, add_zero]
    calc s ^ 2 + s * s = s * s + s * s := by rw [pow_two]
      _ = (2 : K) * (s * s) := (two_mul (s * s)).symm
      _ = 0 := by rw [h2, zero_mul])

theorem o4sylowLin_fixed_iff (hirr : ∀ s : K, s ^ 2 + B * s + C ≠ 0) (x : O4Idx → K) :
    (∀ a b : K, o4sylowLin (B := B) (C := C) a b x = x) ↔
      o4c2 x = 0 ∧ o4c3 x = 0 ∧ o4c4 x = 0 := by
  have hB : B ≠ 0 := B_ne_zero hirr
  constructor
  · intro h
    have h10 := h 1 0
    have h01 := h 0 1
    rw [o4sylowLin_apply] at h10 h01
    have h2 := congrFun h10 (Sum.inr (Sum.inr 0))
    have h4 := congrFun h10 (Sum.inl 0)
    have h3 := congrFun h01 (Sum.inl 0)
    simp [o4param, o4e1, o4e3, o4e4, o4c1, o4c2, o4c3, o4c4, o4Q_apply] at h2 h3 h4
    rw [h2] at h3 h4
    simp at h3 h4
    exact ⟨h2, h3.resolve_left hB, h4.resolve_left hB⟩
  · rintro ⟨h2, h3, h4⟩ a b
    rw [o4sylowLin_apply]
    simp only [h2, h3, h4, mul_zero, add_zero, zero_mul, zero_smul, sub_zero]

noncomputable def o4sylowMat (a b : K) : GL O4Idx K :=
  (toLinEquiv O4Idx K).symm (o4sylowLin (B := B) (C := C) a b)

theorem toLinEquiv_o4sylowMat (a b : K) :
    toLinEquiv O4Idx K (o4sylowMat (B := B) (C := C) a b) =
      o4sylowLin (B := B) (C := C) a b := by
  rw [o4sylowMat, MulEquiv.apply_symm_apply]

theorem o4sylowMat_mem (hirr : ∀ s : K, s ^ 2 + B * s + C ≠ 0) (a b : K) :
    o4sylowMat (B := B) (C := C) a b ∈ StatedOmega (StatedQuadMinus 2 K B C) := by
  rw [mem_statedOmega_iff_mem_elementaryGroup (coe_quadMinus 2 K B C)
    (commutator_orthogonalGroup_quadMinus_small (Or.inl rfl) hirr)]
  show toLinEquiv O4Idx K (o4sylowMat (B := B) (C := C) a b) ∈
    elementaryGroup (quadMinus 2 K B C)
  rw [o4sylowMat, MulEquiv.apply_symm_apply]
  exact eichler_mem_elementaryGroup _ _ _

noncomputable def o4sylowHom (hirr : ∀ s : K, s ^ 2 + B * s + C ≠ 0) :
    Multiplicative (K × K) →* StatedOmega (StatedQuadMinus 2 K B C) where
  toFun p := ⟨o4sylowMat (B := B) (C := C) p.toAdd.1 p.toAdd.2,
    o4sylowMat_mem hirr p.toAdd.1 p.toAdd.2⟩
  map_one' := by
    ext i j
    simp [o4sylowMat, o4sylowLin_one]
  map_mul' p q := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    apply (toLinEquiv O4Idx K).injective
    rw [map_mul (toLinEquiv O4Idx K), toLinEquiv_o4sylowMat, toLinEquiv_o4sylowMat,
      toLinEquiv_o4sylowMat, o4sylowLin_mul]
    rfl

theorem o4sylowHom_fixed_iff (hirr : ∀ s : K, s ^ 2 + B * s + C ≠ 0) (x : O4Idx → K) :
    (∀ s ∈ (o4sylowHom (B := B) (C := C) hirr).range,
      toLinEquiv O4Idx K s x = x) ↔
      o4c2 x = 0 ∧ o4c3 x = 0 ∧ o4c4 x = 0 := by
  rw [← o4sylowLin_fixed_iff hirr x]
  constructor
  · rintro h a b
    have h1 := h _ ⟨Multiplicative.ofAdd (a, b), rfl⟩
    simpa only [o4sylowHom, MonoidHom.coe_mk, OneHom.coe_mk, toLinEquiv_o4sylowMat,
      toAdd_ofAdd] using h1
  · rintro h s ⟨p, rfl⟩
    simpa only [o4sylowHom, MonoidHom.coe_mk, OneHom.coe_mk, toLinEquiv_o4sylowMat]
      using h (p.toAdd).1 (p.toAdd).2

theorem o4sylowHom_injective (hirr : ∀ s : K, s ^ 2 + B * s + C ≠ 0) :
    Function.Injective (o4sylowHom (B := B) (C := C) hirr) := by
  intro p q hpq
  have h := congrArg (fun g : StatedOmega (StatedQuadMinus 2 K B C) =>
    toLinEquiv O4Idx K g) hpq
  simp only [o4sylowHom, MonoidHom.coe_mk, OneHom.coe_mk, toLinEquiv_o4sylowMat] at h
  exact o4sylowLin_injective h

theorem card_o4sylowHom_range (hirr : ∀ s : K, s ^ 2 + B * s + C ≠ 0)
    (hK : Nat.card K = 4) :
    Nat.card ↥(o4sylowHom (B := B) (C := C) hirr).range = 16 := by
  have hinj := o4sylowHom_injective (B := B) (C := C) hirr
  calc Nat.card ↥(o4sylowHom (B := B) (C := C) hirr).range
      = Nat.card (Multiplicative (K × K)) :=
        (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card (K × K) := rfl
    _ = 16 := by rw [Nat.card_prod, hK]

end Model

section Outer

open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_outer_l2_four {X : Type} [Group X] [Finite X]
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 X 4) :
    Nat.card (Outer X) = 4 := by
  obtain ⟨-, F, hF, hFfin, hFcard, hchar, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_isL2_psl h
  letI : Field F := hF
  have : Finite F := hFfin
  have h1 : Nat.card F = 16 := by simpa using hFcard
  have h2 : Nat.card (Outer (CFSG.GorensteinWalter.PSL2 F)) = 4 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F))).toEquiv]
    exact CFSG.RankThree.PartOne.KCRootAxis.natCard_out_sl2 (K := F) (by norm_num) h1
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact h2

variable {W : Type} [CommGroup W] [Finite W]

theorem seventeen_inner {X Y : Subgroup (MulAut W)} (hXY : X ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hL2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 ↥X 4)
    {h : ↥Y} {k : ℕ} (hh : h ^ (17 ^ k) = 1) :
    ∃ l ∈ X.subgroupOf Y,
      (l : ↥Y)⁻¹ * h ∈ Subgroup.centralizer (X.subgroupOf Y : Set ↥Y) := by
  classical
  let L := X.subgroupOf Y
  have hnorm : L.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr hYN
  let eL : ↥L ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXY
  have hOut : Nat.card (Outer ↥L) = 4 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eL).toEquiv]
    exact card_outer_l2_four hL2
  have hdvd : Nat.card (Outer ↥L) ∣ 2 ^ 2 := by rw [hOut]; norm_num
  let α : MulAut ↥L := MulAut.conjNormal (H := L) h
  have hα : α ^ (17 ^ k) = 1 := by
    rw [show α = MulAut.conjNormal (H := L) h from rfl, ← map_pow, hh, map_one]
  have hαodd : Odd (orderOf α) := by
    have hd : orderOf α ∣ 17 ^ k := orderOf_dvd_of_pow_eq_one hα
    exact Odd.of_dvd_nat (Odd.pow (by norm_num : Odd 17) : Odd (17 ^ k)) hd
  obtain ⟨l, hl⟩ := CFSG.ASVolI.burnsideA315s_exists_conj_of_card_outer_dvd hdvd α hαodd
  refine ⟨l.1, l.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hconj : h * x * h⁻¹ = l.1 * x * l.1⁻¹ := by
    have h1 := congrArg (fun β : MulAut ↥L => (((β ⟨x, hx⟩ : ↥L) : ↥Y))) hl
    simpa [α, MulAut.conjNormal_apply, MulAut.conj_apply] using h1
  calc x * (l.1⁻¹ * h)
      = l.1⁻¹ * (l.1 * x * l.1⁻¹) * h := by group
    _ = l.1⁻¹ * (h * x * h⁻¹) * h := by rw [← hconj]
    _ = (l.1⁻¹ * h) * x := by group

end Outer

section KFact

theorem natOmegaMinus_four_exists_fix {W : Type} [CommGroup W]
    {X : Subgroup (MulAut W)} {I : Subgroup W} (h : NatOmegaMinus X I ⊥ 4 2) :
    ∃ T : Subgroup ↥X, IsPGroup 2 ↥T ∧
      Nat.card ↥(I ⊓ CFSG.Quasithin.fixV (T.map X.subtype)) ≤ 4 := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKc, hirr, π, hπ⟩ := h
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 2) hKc
  let Γ : Subgroup (GL O4Idx K) := StatedOmega (StatedQuadMinus 2 K b c)
  let πΓ : ↥Γ →* ↥X := π
  have hπΓ : (FFModel.nat Γ).RealizesVia X I ⊥ πΓ := hπ
  have hinj : Function.Injective πΓ :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful Γ) hπΓ
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.SL3Pair.exists_mulEquiv_of_realizesVia_sub Γ hπΓ
  let S : Subgroup ↥Γ := (o4sylowHom (B := b) (C := c) hirr).range
  refine ⟨S.map πΓ, ?_, ?_⟩
  · have hcard : Nat.card ↥(S.map πΓ) = 2 ^ 4 := by
      rw [Subgroup.card_map_of_injective hinj]
      exact card_o4sylowHom_range hirr hKc
    exact IsPGroup.of_card hcard
  · have hfix : ∀ w : ↥(I ⊓ CFSG.Quasithin.fixV ((S.map πΓ).map X.subtype)),
        o4c2 (Multiplicative.toAdd (e ⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩)) = 0 ∧
        o4c3 (Multiplicative.toAdd (e ⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩)) = 0 ∧
        o4c4 (Multiplicative.toAdd (e ⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩)) = 0 := by
      intro w
      rw [← o4sylowHom_fixed_iff hirr]
      intro s hs
      have hwI : (w : W) ∈ I := (Subgroup.mem_inf.1 w.2).1
      have hsw : ((πΓ s : ↥X) : MulAut W) (w : W) = w :=
        (Subgroup.mem_inf.1 w.2).2 _ ⟨πΓ s, ⟨s, hs, rfl⟩, rfl⟩
      have hu : ((πΓ s : ↥X) : MulAut W) (w : W) ∈ I := hsw.symm ▸ hwI
      have h1 := he s ⟨w, hwI⟩ hu
      have h2 : (⟨((πΓ s : ↥X) : MulAut W) (w : W), hu⟩ : ↥I) = ⟨w, hwI⟩ := Subtype.ext hsw
      rw [h2] at h1
      exact (congrArg Multiplicative.toAdd h1).symm
    let f : ↥(I ⊓ CFSG.Quasithin.fixV ((S.map πΓ).map X.subtype)) → K := fun w =>
      o4c1 (Multiplicative.toAdd (e ⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩))
    have hf : Function.Injective f := by
      intro w w' hww'
      have h1 := o4_eq_of_c1_eq (hfix w) (hfix w') hww'
      have h2 := e.injective (Multiplicative.toAdd.injective h1)
      have h3 : (w : W) = (w' : W) := congrArg (fun u : ↥I => (u : W)) h2
      exact Subtype.ext h3
    calc Nat.card ↥(I ⊓ CFSG.Quasithin.fixV ((S.map πΓ).map X.subtype))
        ≤ Nat.card K := Nat.card_le_card_of_injective f hf
      _ = 4 := hKc

theorem natOmegaMinus_four_card_fixV_sylow_le {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {I : Subgroup W} (h : NatOmegaMinus X I ⊥ 4 2) (P : Sylow 2 ↥X) :
    Nat.card ↥(I ⊓ CFSG.Quasithin.fixV ((P : Subgroup ↥X).map X.subtype)) ≤ 4 := by
  obtain ⟨T, hT, hTfix⟩ := natOmegaMinus_four_exists_fix h
  have hI : ∀ x ∈ X, ∀ w ∈ I, x w ∈ I := by
    obtain ⟨-, K, hKf, hKfin, b, c, hKc, hirr, π, hπ⟩ := h
    exact fun x hx w hw => hπ.2.2.2.1 ⟨x, hx⟩ w hw
  exact (card_inf_fixV_sylow_le_of_isPGroup hI hT P).trans hTfix

theorem sumOfNat_omegaMinus_four_cent_seventeen {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 2) X ⊤ ⊥ 3)
    {c : MulAut W} (hcX : ∀ x ∈ X, x * c = c * x) {k : ℕ} (hc : c ^ (17 ^ k) = 1) : c = 1 := by
  classical
  obtain ⟨I, -, hind, hsup, hNat⟩ := hsum
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥X))
  let R : Subgroup (MulAut W) := (P : Subgroup ↥X).map X.subtype
  have hR2 : IsPGroup 2 ↥R := P.isPGroup'.map X.subtype
  have hRX : ∀ r ∈ R, r ∈ X := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hRI : ∀ r ∈ R, ∀ i, ∀ w ∈ I i, r w ∈ I i := by
    intro r hr i w hw
    obtain ⟨-, K, hKf, hKfin, b, c', hKc, hirr, π, hπ⟩ := hNat i
    exact hπ.2.2.2.1 ⟨r, hRX r hr⟩ w hw
  have hcard : Nat.card ↥(CFSG.Quasithin.fixV R) < 2 ^ 8 := by
    have h2 : ∀ i, Nat.card ↥(I i ⊓ CFSG.Quasithin.fixV R) ≤ 4 :=
      fun i => natOmegaMinus_four_card_fixV_sylow_le (hNat i) P
    have h3 : ∏ i, Nat.card ↥(I i ⊓ CFSG.Quasithin.fixV R) ≤ 4 * 4 * 4 := by
      rw [Fin.prod_univ_three]
      exact Nat.mul_le_mul (Nat.mul_le_mul (h2 0) (h2 1)) (h2 2)
    calc Nat.card ↥(CFSG.Quasithin.fixV R)
        ≤ ∏ i, Nat.card ↥(I i ⊓ CFSG.Quasithin.fixV R) :=
          card_fixV_le_prod_inf_fixV hind hsup hRI
      _ ≤ 4 * 4 * 4 := h3
      _ < 2 ^ 8 := by norm_num
  have hcR : ∀ w ∈ CFSG.Quasithin.fixV R, c w ∈ CFSG.Quasithin.fixV R := by
    intro w hw r hr
    rw [← MulAut.mul_apply, hcX r (hRX r hr), MulAut.mul_apply, hw r hr]
  exact eq_one_of_commute_of_fixV_le hsq hc hR2 (fun r hr => hcX r (hRX r hr))
    (apply_eq_of_pow_seventeen_of_card_lt hsq hc hcR hcard)

theorem k_O4m4_ThreeNat_holds : K_O4m4_ThreeNat := by
  intro W _ _ hsq X Y hXY hYN hX hsum
  classical
  have hL2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 ↥X 4 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.isL2_of_isOmegaMinus_four (by norm_num) hX
  let L : Subgroup ↥Y := X.subgroupOf Y
  have hLn : L.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr hYN
  have hLL2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 ↥L 4 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXY).symm hL2
  have hLC : L ⊓ Subgroup.centralizer (L : Set ↥Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxC⟩
    have hz : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC (g : ↥Y) g.2)
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_center_bot hLL2, Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)
  have hrank : ∀ E : Subgroup ↥L, CFSG.IsElementaryAbelian 17 ↥E → Nat.card E ≤ 17 := by
    intro E hE
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_rank (by norm_num) (by norm_num) hLL2 E
  have hC : ∀ c ∈ Subgroup.centralizer (L : Set ↥Y), (∃ k : ℕ, c ^ (17 ^ k) = 1) → c = 1 := by
    rintro c hc ⟨k, hk⟩
    have hcX : ∀ x ∈ X, x * (c : MulAut W) = (c : MulAut W) * x := by
      intro x hx
      have hxL : (⟨x, hXY hx⟩ : ↥Y) ∈ L := Subgroup.mem_subgroupOf.2 hx
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc _ hxL)
    have hk' : (c : MulAut W) ^ (17 ^ k) = 1 := by
      rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
    exact Subtype.ext (sumOfNat_omegaMinus_four_cent_seventeen hsq hsum hcX hk')
  have hinn : ∀ h : ↥Y, (∃ k : ℕ, h ^ (17 ^ k) = 1) →
      ∃ l ∈ L, l⁻¹ * h ∈ Subgroup.centralizer (L : Set ↥Y) := by
    rintro h ⟨k, hk⟩
    exact seventeen_inner hXY hYN hL2 hk
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro r ⟨E, -, hEab, hEr⟩
  have := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hEab
  have h1 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_card_le L hLC hrank hC hinn E
  rw [hEr] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 17)).1 (by simpa using h1)

end KFact

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end

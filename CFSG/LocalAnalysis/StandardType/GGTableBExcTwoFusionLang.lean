module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionCount
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviDescent
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBExcTwoFusion

open TableBExc TableBExcTwo

section Field

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem natCard_ext (hK : Nat.card K = 2) : Nat.card (FiniteField.Extension K 2 2) = 4 := by
  rw [FiniteField.natCard_extension, hK]
  norm_num

theorem three_dvd_natCard_ext_sub_one (hK : Nat.card K = 2) :
    3 ∣ Nat.card (FiniteField.Extension K 2 2) - 1 := by
  rw [natCard_ext hK]

theorem frob_eq_sq (hK : Nat.card K = 2) (z : FiniteField.Extension K 2 2) :
    FiniteField.Extension.frob K 2 2 z = z ^ 2 := by
  rw [FiniteField.Extension.frob_apply, hK]

theorem units_pow_three (hK : Nat.card K = 2) (t : (FiniteField.Extension K 2 2)ˣ) : t ^ 3 = 1 := by
  have h : Nat.card (FiniteField.Extension K 2 2)ˣ = 3 := by
    rw [Nat.card_units, natCard_ext hK]
  rw [← h]
  exact pow_card_eq_one'

theorem units_map_frob (hK : Nat.card K = 2) (t : (FiniteField.Extension K 2 2)ˣ) :
    Units.map (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom.toMonoidHom t = t⁻¹ := by
  refine Units.ext ?_
  rw [Units.coe_map]
  change FiniteField.Extension.frob K 2 2 (t : FiniteField.Extension K 2 2) = _
  rw [frob_eq_sq hK, ← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left (a := t ^ 2) (by
    rw [← pow_succ, units_pow_three hK])]

end Field

section SL2

variable {L : Type} [Field L] {x : L}

theorem sq_add_self_add_one_eq_zero {ω : Lˣ} (hω : orderOf ω = 3) :
    (ω : L) ^ 2 + ω + 1 = 0 := by
  have h3 : (ω : L) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have h1 : (ω : L) ≠ 1 := by
    intro h
    have : ω = 1 := Units.ext h
    rw [this, orderOf_one] at hω
    exact absurd hω (by norm_num)
  have hm : ((ω : L) - 1) * ((ω : L) ^ 2 + ω + 1) = 0 := by
    linear_combination h3
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h1)

theorem pow_three_of_sq_add (hx : x ^ 2 + x + 1 = 0) : x ^ 3 = 1 := by
  linear_combination (x - 1) * hx

theorem coe_nSL_one : ((nSL 1 : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; -1, 0] := by
  simp [nSL]

theorem map_nSL_one (σ : L →+* L) : Matrix.SpecialLinearGroup.map σ (nSL 1) = nSL 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_nSL_one]
  fin_cases i <;> fin_cases j <;> simp

theorem map_uSL_mul_vSL {K : Type} [Field K] (f : K →+* L) :
    Matrix.SpecialLinearGroup.map f (uSL 1 * vSL 1) = uSL 1 * vSL 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

variable [CharP L 2]

theorem det_langMat (hx : x ^ 2 + x + 1 = 0) :
    (!![1, 1; x, x ^ 2] : Matrix (Fin 2) (Fin 2) L).det = 1 := by
  rw [Matrix.det_fin_two_of]
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  linear_combination hx - (x + 1) * h2

@[expose] noncomputable def langP (hx : x ^ 2 + x + 1 = 0) : SL2 L :=
  ⟨!![1, 1; x, x ^ 2], det_langMat hx⟩

theorem coe_langP (hx : x ^ 2 + x + 1 = 0) :
    ((langP hx : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![1, 1; x, x ^ 2] :=
  rfl

theorem map_langP (hx : x ^ 2 + x + 1 = 0) (σ : L →+* L) (hσ : σ x = x ^ 2) :
    Matrix.SpecialLinearGroup.map σ (langP hx) = langP hx * nSL 1 := by
  have h3 := pow_three_of_sq_add hx
  have h4 : σ (x ^ 2) = x := by
    rw [map_pow, hσ, ← pow_mul]
    linear_combination x * h3
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_mul, coe_langP,
    coe_nSL_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hσ, h4, CharTwo.neg_eq]

theorem langP_mul_HSL {ω : Lˣ} (hx : (ω : L) ^ 2 + ω + 1 = 0) :
    langP hx * HSL ω = (uSL 1 * vSL 1) * langP hx := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have h3 := pow_three_of_sq_add hx
  have hinv : ((ω⁻¹ : Lˣ) : L) = (ω : L) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ']
    exact h3
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_langP]
  fin_cases i <;> fin_cases j <;>
    simp [HSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, hinv] <;>
    first
    | linear_combination h2
    | linear_combination hx - ((ω : L) + 1) * h2
    | linear_combination (ω : L) * h3 - hx + (ω : L) * h2

end SL2

theorem list_prod_ofFn_mul_of_ne {G : Type*} [Group G] :
    ∀ {n : ℕ} (f g : Fin n → G), (∀ i j, i ≠ j → Commute (f i) (g j)) →
      (List.ofFn fun i => f i * g i).prod = (List.ofFn f).prod * (List.ofFn g).prod
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, list_prod_ofFn_mul_of_ne (fun i => f i.succ) (fun i => g i.succ)
        (fun i j hij => h i.succ j.succ fun e => hij (Fin.succ_injective _ e))]
    have hc : Commute (g 0) (List.ofFn fun i => f i.succ).prod :=
      Commute.list_prod_right _ _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact (h i.succ 0 (Fin.succ_ne_zero i)).symm
    rw [mul_assoc, ← mul_assoc (g 0), hc.eq]
    simp only [mul_assoc]

section Frame

variable
  {τ : Tag} {d : ℕ}

variable (L : Type) [Field L] in
@[expose] noncomputable def frameProd (F : OrthFrame τ d) (A : SL2 L) : adjointGroup τ L :=
  (List.ofFn fun i : Fin (d + 1) => rho L F i A).prod

variable {L : Type} [Field L]

theorem frameProd_mul (F : OrthFrame τ d) (A B : SL2 L) :
    frameProd L F (A * B) = frameProd L F A * frameProd L F B := by
  rw [frameProd, frameProd, frameProd, ← list_prod_ofFn_mul_of_ne]
  · simp only [map_mul]
  · intro i j hij
    exact commute_rho F hij A B

theorem frameProd_eq (F : OrthFrame τ d) (A : SL2 L) :
    frameProd L F A = rho L F 0 A * (List.ofFn fun i : Fin d => rho L F i.succ A).prod := by
  rw [frameProd, List.ofFn_succ, List.prod_cons]

theorem frameProd_conj_rho_zero (F : OrthFrame τ d) (A B : SL2 L) :
    frameProd L F A * rho L F 0 B * (frameProd L F A)⁻¹ = rho L F 0 (A * B * A⁻¹) := by
  have hc : Commute (List.ofFn fun i : Fin d => rho L F i.succ A).prod (rho L F 0 B) :=
    Commute.list_prod_left _ _ fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact commute_rho F (Fin.succ_ne_zero i) A B
  rw [frameProd_eq, map_mul, map_mul, map_inv, mul_inv_rev, mul_assoc (rho L F 0 A),
    hc.eq]
  group

variable [CharP L 2]

theorem adjointMap_rho {L' : Type} [Field L'] (f : L →+* L') (F : OrthFrame τ d)
    (i : Fin (d + 1)) (A : SL2 L) :
    adjointMap τ f (rho L F i A) = rho L' F i (Matrix.SpecialLinearGroup.map f A) :=
  Subtype.ext (by
    rw [coe_adjointMap, coe_rho, coe_rho]
    exact CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo f (F.isRoot i) A)

theorem adjointMap_frameProd {L' : Type} [Field L'] (f : L →+* L') (F : OrthFrame τ d)
    (A : SL2 L) :
    adjointMap τ f (frameProd L F A) = frameProd L' F (Matrix.SpecialLinearGroup.map f A) := by
  rw [frameProd, frameProd, map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => adjointMap_rho f F i A))

theorem exists_rho_nSL_mem_monomial (F : OrthFrame τ d) (i : Fin (d + 1)) :
    ∃ h : ((rho L F i (nSL 1) : adjointGroup τ L) : ModGL τ L) ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨_, h⟩ = rootReflection (F.root i) :=
  ((CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ L (F.isRoot i)).2.2.2.2.1
    1).2.2

theorem exists_frameProd_nSL_mem_monomial (F : OrthFrame τ d) :
    ∃ h : ((frameProd L F (nSL 1) : adjointGroup τ L) : ModGL τ L) ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨_, h⟩ = (List.ofFn fun i => rootReflection (F.root i)).prod := by
  choose hm hw using exists_rho_nSL_mem_monomial (L := L) F
  set m : Fin (d + 1) → monomialSubgroup τ L := fun i => ⟨_, hm i⟩ with hmdef
  have hcoe : ((frameProd L F (nSL 1) : adjointGroup τ L) : ModGL τ L) =
      (((List.ofFn m).prod : monomialSubgroup τ L) : ModGL τ L) := by
    rw [frameProd, SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod, List.map_ofFn,
      List.map_ofFn]
    rfl
  refine ⟨hcoe ▸ ((List.ofFn m).prod).2, ?_⟩
  have he : (⟨_, hcoe ▸ ((List.ofFn m).prod).2⟩ : monomialSubgroup τ L) = (List.ofFn m).prod :=
    Subtype.ext hcoe
  rw [he, map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => hw i))

end Frame

section Frob

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def frobHom :
    FiniteField.Extension K 2 2 →+* FiniteField.Extension K 2 2 :=
  (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom

theorem frobHom_apply (z : FiniteField.Extension K 2 2) :
    frobHom K z = FiniteField.Extension.frob K 2 2 z :=
  rfl

theorem units_map_frobHom (hK : Nat.card K = 2) (t : (FiniteField.Extension K 2 2)ˣ) :
    Units.map (frobHom K : FiniteField.Extension K 2 2 →* FiniteField.Extension K 2 2) t = t⁻¹ :=
  units_map_frob hK t

theorem frobHom_comp_algebraMap :
    (frobHom K).comp (algebraMap K (FiniteField.Extension K 2 2)) =
      algebraMap K (FiniteField.Extension K 2 2) :=
  RingHom.ext fun a => (FiniteField.Extension.frob K 2 2).commutes a

variable
  {τ : Tag}

theorem baseChangeGL_frob_of_mem_torusGroup (hK : Nat.card K = 2)
    {h : ModGL τ (FiniteField.Extension K 2 2)} (hh : h ∈ torusGroup τ (FiniteField.Extension K 2 2)) :
    baseChangeGL (frobHom K) h = h⁻¹ ∧ h ^ 3 = 1 := by
  set L := FiniteField.Extension K 2 2 with hL
  obtain ⟨t, ht⟩ := torusCoordHom_surjective (⟨h, hh⟩ : torusGroup τ L)
  have hh' : h = ((torusCoordHom τ L t : torusGroup τ L) : (Module.End L (RootModule τ L))ˣ) := by
    rw [ht]
  rw [hh']
  constructor
  · have e : ((torusCoordHom τ L t : torusGroup τ L) : (Module.End L (RootModule τ L))ˣ)⁻¹ =
        ((torusCoordHom τ L t⁻¹ : torusGroup τ L) : (Module.End L (RootModule τ L))ˣ) := by
      rw [map_inv, Subgroup.coe_inv]
    rw [e, coe_torusCoordHom, coe_torusCoordHom, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    change baseChangeGL (frobHom K) (torusElt τ L i (t i)) = torusElt τ L i (t⁻¹ i)
    rw [baseChangeGL_torusElt, Pi.inv_apply, ← units_map_frobHom hK]
    rfl
  · have e3 : t ^ 3 = 1 := funext fun i => by rw [Pi.pow_apply, units_pow_three hK, Pi.one_apply]
    rw [← Subgroup.coe_pow, ← map_pow, e3, map_one, OneMemClass.coe_one]


theorem eq_one_of_monomial_of_frob (hK : Nat.card K = 2) {m : ModGL τ (FiniteField.Extension K 2 2)}
    (hm : m ∈ monomialSubgroup τ (FiniteField.Extension K 2 2))
    (hρ : weylQuotientHom τ (FiniteField.Extension K 2 2) ⟨m, hm⟩ = 1)
    (hφ : baseChangeGL (frobHom K) m = m) : m = 1 := by
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := FiniteField.Extension K 2 2)
  have hT : m ∈ torusGroup τ (FiniteField.Extension K 2 2) := by
    have h1 : (⟨m, hm⟩ : monomialSubgroup τ _) ∈ (weylQuotientHom τ _).ker := hρ
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨h1, h3⟩ := baseChangeGL_frob_of_mem_torusGroup hK hT
  rw [hφ] at h1
  have h2 : m ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel m
  calc m = m ^ 3 * (m ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

end Frob

theorem commute_of_smul_eq_neg {τ : Tag} {w₀ : WeylGroup τ}
    (hw : ∀ v : Fin τ.rank → ℤ, w₀ • v = -v)
    (w : WeylGroup τ) : w₀ * w = w * w₀ := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, hw, hw, smul_neg]

section Descent

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_adjointMap_eq_of_frob (hτ : τ = .E7 ∨ τ = .E8)
    {g : adjointGroup τ (FiniteField.Extension K 2 2)} (hg : adjointMap τ (frobHom K) g = g) :
    ∃ g₀ : adjointGroup τ K, adjointMap τ (algebraMap K (FiniteField.Extension K 2 2)) g₀ = g := by
  set φ : FiniteField.Extension K 2 2 ≃+* FiniteField.Extension K 2 2 :=
    (FiniteField.Extension.frob K 2 2).toRingEquiv with hφ
  have hσg : baseChangeGL (frobHom K) (g : ModGL τ _) = g := congrArg Subtype.val hg
  have h1 : (g : ModGL τ _) ∈ entrywiseFixedGroup τ φ :=
    mem_entrywiseFixedGroup.2 ⟨g.2, by
      rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self]; exact hσg⟩
  rw [entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (Or.inr (Or.inr (Or.inr hτ)))
    (ringChar.eq _ 2) φ, fixedFieldImage,
    map_adjointGroup_baseChangeGL_eq_of_range_eq (fixSubfield φ).subtype
      (algebraMap K (FiniteField.Extension K 2 2)) ?_] at h1
  · obtain ⟨g₀, hg₀, hg₀g⟩ := h1
    exact ⟨⟨g₀, hg₀⟩, Subtype.ext hg₀g⟩
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (CFSG.SeitzReduction.F4Pilot.frob_eq_self_iff (w : FiniteField.Extension K 2 2)).1 w.2
    · intro hz
      exact ⟨⟨z, (CFSG.SeitzReduction.F4Pilot.frob_eq_self_iff z).2 hz⟩, rfl⟩

omit
  [Finite K] [CharP K 2] in
theorem adjointMap_nWord {L : Type} [Field L] (f : L →+* L) (ω : List (Fin τ.rank)) :
    adjointMap τ f (nWord τ L ω) = nWord τ L ω := by
  apply Subtype.ext
  rw [coe_adjointMap, coe_nWord, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => baseChangeGL_weylElt_one f i)

theorem adjointMap_frob_frameProd_nSL (F : OrthFrame τ d) :
    adjointMap τ (frobHom K) (frameProd (FiniteField.Extension K 2 2) F (nSL 1)) =
      frameProd (FiniteField.Extension K 2 2) F (nSL 1) := by
  rw [adjointMap_frameProd, map_nSL_one]

theorem commute_frameProd_nSL_nWord (hK : Nat.card K = 2) (F : OrthFrame τ d)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    (ω : List (Fin τ.rank)) :
    frameProd (FiniteField.Extension K 2 2) F (nSL 1) * nWord τ _ ω =
      nWord τ _ ω * frameProd (FiniteField.Extension K 2 2) F (nSL 1) := by
  set L := FiniteField.Extension K 2 2 with hL
  set n := frameProd L F (nSL 1) with hn
  obtain ⟨hnm, hnw⟩ := exists_frameProd_nSL_mem_monomial (L := L) F
  have hm := coe_nWord_mem_monomialSubgroup (K := L) ω
  set c := n * nWord τ L ω * n⁻¹ * (nWord τ L ω)⁻¹ with hc
  have hcm : (c : ModGL τ L) ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (mul_mem hnm hm) (inv_mem hnm)) (inv_mem hm)
  have hce : (⟨c, hcm⟩ : monomialSubgroup τ L) =
      ⟨_, hnm⟩ * ⟨_, hm⟩ * (⟨_, hnm⟩ : monomialSubgroup τ L)⁻¹ * (⟨_, hm⟩ : monomialSubgroup τ L)⁻¹ :=
    rfl
  have hc1 : c = 1 := by
    refine Subtype.ext (eq_one_of_monomial_of_frob hK hcm ?_ ?_)
    · rw [hce, map_mul, map_mul, map_mul, map_inv, map_inv, hnw, weylQuotientHom_nWord,
        commute_of_smul_eq_neg hw]
      group
    · have h1 := adjointMap_frob_frameProd_nSL (K := K) F
      have h2 := adjointMap_nWord (frobHom K) (τ := τ) ω
      have h3 : adjointMap τ (frobHom K) c = c := by
        rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, h1, h2]
      exact congrArg Subtype.val h3
  have : n * nWord τ L ω * n⁻¹ = nWord τ L ω := by
    rw [← mul_inv_eq_one]
    exact hc1
  calc n * nWord τ L ω = (n * nWord τ L ω * n⁻¹) * n := by group
    _ = nWord τ L ω * n := by rw [this]

theorem frameProd_nSL_eq_nWord (hK : Nat.card K = 2) (F : OrthFrame τ d)
    {ω₀ : List (Fin τ.rank)}
    (hω₀ : (coxeterSystem τ).wordProd ω₀ = (List.ofFn fun i => rootReflection (F.root i)).prod) :
    frameProd (FiniteField.Extension K 2 2) F (nSL 1) = nWord τ _ ω₀ := by
  set L := FiniteField.Extension K 2 2 with hL
  set n := frameProd L F (nSL 1) with hn
  obtain ⟨hnm, hnw⟩ := exists_frameProd_nSL_mem_monomial (L := L) F
  have hm := coe_nWord_mem_monomialSubgroup (K := L) ω₀
  set c := n * (nWord τ L ω₀)⁻¹ with hc
  have hcm : (c : ModGL τ L) ∈ monomialSubgroup τ L := mul_mem hnm (inv_mem hm)
  have hce : (⟨c, hcm⟩ : monomialSubgroup τ L) =
      ⟨_, hnm⟩ * (⟨_, hm⟩ : monomialSubgroup τ L)⁻¹ := rfl
  have hc1 : c = 1 := by
    refine Subtype.ext (eq_one_of_monomial_of_frob hK hcm ?_ ?_)
    · rw [hce, map_mul, map_inv, hnw, weylQuotientHom_nWord, hω₀, mul_inv_cancel]
    · have h1 := adjointMap_frob_frameProd_nSL (K := K) F
      have h2 := adjointMap_nWord (frobHom K) (τ := τ) ω₀
      have h3 : adjointMap τ (frobHom K) c = c := by
        rw [hc, map_mul, map_inv, h1, h2]
      exact congrArg Subtype.val h3
  exact mul_inv_eq_one.mp hc1

theorem frameProd_nSL_conj_chevTorus (hK : Nat.card K = 2) (F : OrthFrame τ d)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) {ζ : (FiniteField.Extension K 2 2)ˣ}
    (hζ : ζ ^ 3 = 1) (a : Fin τ.rank → ZMod 3) :
    frameProd (FiniteField.Extension K 2 2) F (nSL 1) * chevTorus τ ζ hζ (.ofAdd a) *
        (frameProd (FiniteField.Extension K 2 2) F (nSL 1))⁻¹ =
      chevTorus τ ζ hζ (.ofAdd (-a)) := by
  obtain ⟨ω₀, hω₀⟩ :=
    (coxeterSystem τ).wordProd_surjective (List.ofFn fun i => rootReflection (F.root i)).prod
  rw [frameProd_nSL_eq_nWord hK F hω₀, nWord_conj_chevTorus hζ ω₀ a, torusWord_eq_torusAct hsymm,
    hω₀]
  congr 2
  rw [torusAct, hw]
  funext i
  simp only [redMod, liftMod, Pi.neg_apply, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl

end Descent

theorem pow_val_intCast_eq_zpow {G : Type*} [Group G] {ζ : G} (hζo : orderOf ζ = 3) (k : ℤ) :
    ζ ^ ((k : ZMod 3).val) = ζ ^ k := by
  rw [← zpow_natCast]
  refine zpow_eq_zpow_iff_modEq.mpr ?_
  rw [hζo, ZMod.val_intCast]
  exact Int.mod_modEq k 3

section HighRoot

variable
  {τ : Tag}

theorem coe_chevTorus_redMod_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    [CharP L 2] {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    ((chevTorus τ ζ hζ (.ofAdd (redMod τ 3 (CFSG.SeitzReduction.highRoot τ))) :
        adjointGroup τ L) : ModGL τ L) =
      rootSL2 τ L (CFSG.SeitzReduction.highRoot τ) (HSL ζ) := by
  rw [coe_chevTorus, CFSG.SeitzReduction.E6Pilot.rootSL2_highRoot_HSL hτ, List.ofFn_eq_map,
    list_prod_torusElt_eq_rootDiagUnit]
  congr 1
  funext l
  have h1 : ∀ j, zmodPowHom ζ hζ (.ofAdd (Multiplicative.toAdd (Multiplicative.ofAdd
      (redMod τ 3 (CFSG.SeitzReduction.highRoot τ))) j)) ^ τ.cartan j l =
        ζ ^ (CFSG.SeitzReduction.highRoot τ j * τ.cartan j l) := fun j => by
    rw [toAdd_ofAdd, zmodPowHom_apply, redMod, pow_val_intCast_eq_zpow hζo, ← zpow_mul]
  rw [cartanChar, Finset.prod_congr rfl fun j _ => h1 j, prod_zpow_eq_zpow_sum,
    CFSG.SeitzReduction.EPilot.sum_highRoot_mul_cartan hτ l, CFSG.SeitzReduction.EPilot.highDiag]
  by_cases hl : l = CFSG.SeitzReduction.highNode τ
  · subst hl
    simp
  · simp [hl]

end HighRoot

section RootMod

variable {τ : Tag}

theorem redMod_ne_zero_of_isRoot (hsym : ∀ i, τ.symmetrizer i i = 1) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) : redMod τ 3 β ≠ 0 := by
  intro h0
  have hd : ∀ i, (3 : ℤ) ∣ β i := fun i => by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (β i) 3).mp (congrFun h0 i)
    exact_mod_cast h
  have hβ3 : β = (3 : ℤ) • fun i => β i / 3 := funext fun i => by
    rw [Pi.smul_apply, smul_eq_mul, Int.mul_ediv_cancel' (hd i)]
  have h2 := TableBExcTwo.iform_self_eq_two_of_isRoot hsym hβ
  rw [hβ3, CFSG.LieType.Steinberg.Adjoint.iform_smul_left,
    CFSG.LieType.Steinberg.Adjoint.iform_smul_right] at h2
  omega

end RootMod

section Lang

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def langElt (F : OrthFrame τ d) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) : adjointGroup τ (FiniteField.Extension K 2 2) :=
  frameProd _ F (langP (sq_add_self_add_one_eq_zero hω))

theorem adjointMap_frob_langElt (hK : Nat.card K = 2) (F : OrthFrame τ d)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    adjointMap τ (frobHom K) (langElt F hω) = langElt F hω * frameProd _ F (nSL 1) := by
  rw [langElt, adjointMap_frameProd, map_langP _ (frobHom K) (by rw [frobHom_apply, frob_eq_sq hK]),
    frameProd_mul]

theorem adjointMap_frob_conj_langElt (hK : Nat.card K = 2) (F : OrthFrame τ d)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3))
    (hV : Nat.card (torusPow τ (FiniteField.Extension K 2 2) 3) = 3 ^ τ.rank)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3)
    {m : adjointGroup τ (FiniteField.Extension K 2 2)}
    (hm : (m : ModGL τ (FiniteField.Extension K 2 2)) ∈
      monomialSubgroup τ (FiniteField.Extension K 2 2)) :
    adjointMap τ (frobHom K) (langElt F hω * m * (langElt F hω)⁻¹) =
      langElt F hω * m * (langElt F hω)⁻¹ := by
  set L := FiniteField.Extension K 2 2 with hL
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := L)
  obtain ⟨ω', hω'⟩ := (coxeterSystem τ).wordProd_surjective (weylQuotientHom τ L ⟨_, hm⟩)
  set nW := nWord τ L ω' with hnW
  have hnWm := coe_nWord_mem_monomialSubgroup (K := L) ω'
  set h := m * nW⁻¹ with hh
  have hhT : (h : ModGL τ L) ∈ torusGroup τ L := by
    have h1 : (⟨_, hm⟩ * (⟨_, hnWm⟩ : monomialSubgroup τ L)⁻¹ : monomialSubgroup τ L) ∈
        (weylQuotientHom τ L).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, weylQuotientHom_nWord, ← hω', mul_inv_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨hφh, hh3⟩ := baseChangeGL_frob_of_mem_torusGroup hK hhT
  obtain ⟨a, ha⟩ : h ∈ (chevTorus τ ω hω3).range := by
    rw [range_chevTorus_eq_torusPow hω hω3 hdet hV]
    exact ⟨hhT, Subtype.ext (by rw [Subgroup.coe_pow]; exact hh3)⟩
  set nF := frameProd L F (nSL 1) with hnF
  have e0 : nF * h * nF⁻¹ = h⁻¹ := by
    have := frameProd_nSL_conj_chevTorus hK F hw hsymm hω3 (Multiplicative.toAdd a)
    rw [ofAdd_toAdd, ofAdd_neg, ofAdd_toAdd, ha] at this
    rw [this, ← ha]
    exact map_inv _ a
  have e1 : nF * h⁻¹ * nF⁻¹ = h := by
    have : nF * h⁻¹ * nF⁻¹ = (nF * h * nF⁻¹)⁻¹ := by group
    rw [this, e0, inv_inv]
  have e2 : nF * nW * nF⁻¹ = nW := by
    rw [commute_frameProd_nSL_nWord hK F hw ω', mul_inv_cancel_right]
  have hφm : adjointMap τ (frobHom K) m = h⁻¹ * nW := by
    have hm' : m = h * nW := by rw [hh, inv_mul_cancel_right]
    rw [hm', map_mul, adjointMap_nWord]
    congr 1
    exact Subtype.ext (by rw [coe_adjointMap, Subgroup.coe_inv]; exact hφh)
  calc adjointMap τ (frobHom K) (langElt F hω * m * (langElt F hω)⁻¹)
      = (langElt F hω * nF) * (h⁻¹ * nW) * (langElt F hω * nF)⁻¹ := by
        rw [map_mul, map_mul, map_inv, adjointMap_frob_langElt hK F hω, hφm]
    _ = langElt F hω * ((nF * h⁻¹ * nF⁻¹) * (nF * nW * nF⁻¹)) * (langElt F hω)⁻¹ := by group
    _ = langElt F hω * m * (langElt F hω)⁻¹ := by rw [e1, e2, hh, inv_mul_cancel_right]

theorem langElt_conj_chevTorus_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (F : OrthFrame τ d)
    (hF0 : F.root 0 = CFSG.SeitzReduction.highRoot τ) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) (hω3 : ω ^ 3 = 1) :
    langElt F hω * chevTorus τ ω hω3 (.ofAdd (redMod τ 3 (CFSG.SeitzReduction.highRoot τ))) *
        (langElt F hω)⁻¹ =
      adjointMap τ (algebraMap K (FiniteField.Extension K 2 2)) (rho K F 0 (uSL 1 * vSL 1)) := by
  have hc : chevTorus τ ω hω3 (.ofAdd (redMod τ 3 (CFSG.SeitzReduction.highRoot τ))) =
      rho _ F 0 (HSL ω) := by
    apply Subtype.ext
    rw [coe_rho, hF0]
    exact coe_chevTorus_redMod_highRoot hτ hω hω3
  have hP : langP (sq_add_self_add_one_eq_zero hω) * HSL ω *
      (langP (sq_add_self_add_one_eq_zero hω))⁻¹ = uSL 1 * vSL 1 := by
    rw [langP_mul_HSL, mul_inv_cancel_right]
  rw [hc, langElt, frameProd_conj_rho_zero, hP, adjointMap_rho, map_uSL_mul_vSL]

end Lang

theorem index_comap_dvd {C₁ C₂ : Type*} [Group C₁] [Group C₂] [Finite C₂] {j : C₁ →* C₂}
    (hj : Function.Injective j) {X : Subgroup C₂} (g : C₂)
    (hX : X.map (MulAut.conj g).toMonoidHom ≤ j.range) :
    ((X.map (MulAut.conj g).toMonoidHom).comap j).index ∣ X.index := by
  have : Finite C₁ := Finite.of_injective j hj
  set X' := X.map (MulAut.conj g).toMonoidHom with hX'
  set Y := X'.comap j with hY
  have hYX : Nat.card Y = Nat.card X := by
    have h1 : Y.map j = X' := Subgroup.map_comap_eq_self hX
    rw [← Subgroup.card_map_of_injective hj, h1, hX',
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h1 := Y.card_mul_index
  have h2 := X.card_mul_index
  have h3 := j.range.card_mul_index
  have h4 : Nat.card j.range = Nat.card C₁ :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  rw [h4, ← h1, hYX, mul_assoc] at h3
  rw [← h3] at h2
  have hpos : 0 < Nat.card X := Nat.card_pos
  exact ⟨j.range.index, Nat.eq_of_mul_eq_mul_left hpos h2⟩

section Fusion

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_mem_highRootSL2_of_weylX (hτ : τ = .E7 ∨ τ = .E8) (F : OrthFrame τ d)
    (hF0 : F.root 0 = CFSG.SeitzReduction.highRoot τ)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3))
    (hV : Nat.card (torusPow τ (FiniteField.Extension K 2 2) 3) = 3 ^ τ.rank)
    {S : Subgroup (WeylGroup τ)} (hidx : ¬ 3 ∣ (weylX τ (FiniteField.Extension K 2 2) S).index)
    {T : ℕ}
    (hS : ∀ (ζ : (FiniteField.Extension K 2 2)ˣ), orderOf ζ = 3 → ∀ (hζ : ζ ^ 3 = 1)
      (E : Subgroup (adjointGroup τ (FiniteField.Extension K 2 2))), IsElemAbelian 3 E →
      E ≤ weylX τ _ S → T ≤ Nat.card E →
      ∃ β, IsRoot τ β ∧ chevTorus τ ζ hζ (.ofAdd (redMod τ 3 β)) ∈ E)
    (hK : Nat.card K = 2) {A : Subgroup (adjointGroup τ K)} (hA : IsElemAbelian 3 A)
    (hT : T ≤ Nat.card A) :
    ∃ t ∈ A, t ≠ 1 ∧ ∃ g : adjointGroup τ K,
      g * t * g⁻¹ ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 τ K).subgroupOf (adjointGroup τ K) := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  have := Fact.mk Nat.prime_three
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3)
    (three_dvd_natCard_ext_sub_one hK)
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  set g := langElt F hωo with hg
  set j := adjointMap τ (algebraMap K L) with hj
  have hjinj : Function.Injective j := adjointMap_injective _
  have : Finite (adjointGroup τ L) := generated_group_finite τ L
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hdesc : ∀ m : adjointGroup τ L, (m : ModGL τ L) ∈ monomialSubgroup τ L →
      ∃ m₀ : adjointGroup τ K, j m₀ = g * m * g⁻¹ := fun m hm =>
    exists_adjointMap_eq_of_frob hτ (adjointMap_frob_conj_langElt hK F hw hsymm hdet hV hωo hm)
  set X := weylX τ L S with hX
  have hXj : X.map (MulAut.conj g).toMonoidHom ≤ j.range := by
    rintro _ ⟨m, hmX, rfl⟩
    obtain ⟨m₀, hm₀⟩ := hdesc m (mem_weylX.mp hmX).1
    exact ⟨m₀, hm₀⟩
  set Y := (X.map (MulAut.conj g).toMonoidHom).comap j with hY
  have hYidx : ¬ 3 ∣ Y.index := fun h => hidx (h.trans (index_comap_dvd hjinj g hXj))
  obtain ⟨x, hx⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hYidx
    (TableB.isPGroup_of_isElemAbelian hA)
  set E' := ((A.map (MulAut.conj x).toMonoidHom).map j).map (MulAut.conj g⁻¹).toMonoidHom with
    hE'def
  have hE'X : E' ≤ X := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    obtain ⟨m, hmX, hm⟩ := hx hb
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hm, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
    rw [e]
    exact hmX
  have hE' : IsElemAbelian 3 E' :=
    TableB.isElemAbelian_map (TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _) _
  have hcard : Nat.card E' = Nat.card A := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective hjinj,
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  obtain ⟨β, hβ, hβE⟩ := hS ω hωo hω3 E' hE' hE'X (hcard ▸ hT)
  obtain ⟨_, ⟨_, ⟨a, haA, rfl⟩, rfl⟩, hya⟩ := hβE
  set y := chevTorus τ ω hω3 (.ofAdd (redMod τ 3 β)) with hy
  have hjxa : j (x * a * x⁻¹) = g * y * g⁻¹ := by
    rw [← hya]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine ⟨a, haA, fun ha1 => ?_, ?_⟩
  ·
    have hy1 : y = 1 := by
      rw [← hya, ha1]
      simp
    have h0 := chevTorus_injective hωo hω3 hdet (hy1.trans (map_one _).symm)
    exact redMod_ne_zero_of_isRoot F.symm_one hβ (Multiplicative.ofAdd.injective h0)
  ·
    obtain ⟨w, hwβ⟩ := CFSG.SeitzReduction.EPilot.exists_smul_eq_highRoot hτ' hβ
    obtain ⟨ω', hω'⟩ := (coxeterSystem τ).wordProd_surjective w
    set n := nWord τ L ω' with hn
    have hny : n * y * n⁻¹ =
        chevTorus τ ω hω3 (.ofAdd (redMod τ 3 (CFSG.SeitzReduction.highRoot τ))) := by
      rw [hy, hn, nWord_conj_chevTorus hω3 ω', torusWord_eq_torusAct hsymm, hω', torusAct,
        redMod_smul_eq w (redMod_liftMod (redMod τ 3 β)), hwβ]
    obtain ⟨z, hz⟩ := hdesc n (coe_nWord_mem_monomialSubgroup ω')
    have hroot := langElt_conj_chevTorus_highRoot hτ' F hF0 hωo hω3
    refine ⟨z * x, ?_⟩
    have key : j (z * x * a * (z * x)⁻¹) = j (rho K F 0 (uSL 1 * vSL 1)) := by
      calc j (z * x * a * (z * x)⁻¹) = j z * j (x * a * x⁻¹) * (j z)⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = (g * n * g⁻¹) * (g * y * g⁻¹) * (g * n * g⁻¹)⁻¹ := by rw [hz, hjxa]
        _ = g * (n * y * n⁻¹) * g⁻¹ := by group
        _ = j (rho K F 0 (uSL 1 * vSL 1)) := by rw [hny, ← hroot]
    rw [Subgroup.mem_subgroupOf, hjinj key, coe_rho, hF0,
      ← CFSG.SeitzReduction.E6Pilot.range_rootSL2_highRoot]
    exact ⟨_, rfl⟩

end Fusion

end TableBExcTwoFusion

end CFSG.StandardType

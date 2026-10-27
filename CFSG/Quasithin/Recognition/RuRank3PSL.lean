module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Certificates.NativeSchreierEnum
public meta import CFSG.Sporadic.Schreier.RuChainSpec
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Certificates.NativeSchreierEnum
public meta import Certificates.Data.CFSGNative.Schreier.Enum3
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Quasithin.Recognition.RuRank3PSLInputs
public import Certificates.Certificate7044

public section

namespace CFSG.Quasithin.RuRank3

open scoped MatrixGroups Matrix LinearAlgebra.Projectivization
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.RuSchreier

theorem fact_prime_five' : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five'

theorem fact_two_not_square_five : Fact (∀ r : ZMod 5, r ^ 2 ≠ 2 + 0 * r) := ⟨by decide +kernel⟩

attribute [local instance] fact_two_not_square_five

theorem fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

attribute [local instance] fact_prime_thirteen

@[expose] def F25 : Type := QuadraticAlgebra (ZMod 5) 2 0

instance : Field F25 := inferInstanceAs (Field (QuadraticAlgebra (ZMod 5) 2 0))

instance : DecidableEq F25 := fun x y =>
  decidable_of_iff (QuadraticAlgebra.re (x : QuadraticAlgebra (ZMod 5) 2 0) =
      QuadraticAlgebra.re (y : QuadraticAlgebra (ZMod 5) 2 0) ∧
    QuadraticAlgebra.im (x : QuadraticAlgebra (ZMod 5) 2 0) =
      QuadraticAlgebra.im (y : QuadraticAlgebra (ZMod 5) 2 0)) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact QuadraticAlgebra.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

instance : Fintype F25 :=
  Fintype.ofEquiv _ (QuadraticAlgebra.equivProd (2 : ZMod 5) 0).symm

instance : Algebra (ZMod 5) F25 :=
  inferInstanceAs (Algebra (ZMod 5) (QuadraticAlgebra (ZMod 5) 2 0))

@[expose] def mkF (a b : ZMod 5) : F25 := (⟨a, b⟩ : QuadraticAlgebra (ZMod 5) 2 0)

theorem card_F25 : Fintype.card F25 = 5 ^ 2 := by decide +kernel

noncomputable def f25EquivGalois : F25 ≃+* GaloisField 5 2 :=
  (GaloisField.algEquivGaloisFieldOfFintype 5 2 card_F25).toRingEquiv

noncomputable def pslF25EquivGalois : PSL(2, F25) ≃* PSL(2, GaloisField 5 2) :=
  CFSG.GorensteinWalter.FieldTransport.projectiveSpecialLinearGroupMulEquiv f25EquivGalois

theorem mk_eq_mk_of_cross {K : Type*} [Field K] (u v : Fin 2 → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : u 0 * v 1 = u 1 * v 0) : Projectivization.mk K u hu = Projectivization.mk K v hv := by
  rw [Projectivization.mk_eq_mk_iff']
  by_cases h1 : u 1 = 0
  · have h0 : u 0 ≠ 0 := by
      intro h0
      apply hu
      funext i
      fin_cases i <;> simp [h0, h1]
    have hv1 : v 1 = 0 := by
      rw [h1, zero_mul] at h
      exact (mul_eq_zero.1 h).resolve_left h0
    have hv0 : v 0 ≠ 0 := by
      intro h0'
      apply hv
      funext i
      fin_cases i <;> simp [h0', hv1]
    refine ⟨u 0 / v 0, ?_⟩
    funext i
    fin_cases i
    · simp [hv0]
    · simp [h1, hv1]
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      rw [hv1, mul_zero] at h
      have hv0 : v 0 = 0 := (mul_eq_zero.1 h.symm).resolve_left h1
      apply hv
      funext i
      fin_cases i <;> simp [hv0, hv1]
    refine ⟨u 1 / v 1, ?_⟩
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h.symm
    · simp [hv1]

theorem cross_of_mk_eq_mk {K : Type*} [Field K] (u v : Fin 2 → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : Projectivization.mk K u hu = Projectivization.mk K v hv) : u 0 * v 1 = u 1 * v 0 := by
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, rfl⟩ := h
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

@[expose] def ptVec (i : Fin 26) : Fin 2 → F25 :=
  if i.val < 25 then ![mkF (i.val % 5 : ℕ) (i.val / 5 : ℕ), 1] else ![1, 0]

theorem ptVec_ne_zero : ∀ i, ptVec i ≠ 0 := by decide +kernel

@[expose] noncomputable def ptP (i : Fin 26) : ℙ F25 (Fin 2 → F25) :=
  Projectivization.mk F25 (ptVec i) (ptVec_ne_zero i)

theorem ptVec_cross_injective :
    ∀ i j : Fin 26, ptVec i 0 * ptVec j 1 = ptVec i 1 * ptVec j 0 → i = j := by
  decide +kernel

theorem ptP_injective : Function.Injective ptP := fun i j h =>
  ptVec_cross_injective i j (cross_of_mk_eq_mk _ _ _ _ h)

theorem card_projF25 : Nat.card (ℙ F25 (Fin 2 → F25)) = 26 := by
  rw [Projectivization.card_of_finrank_two _ _ (Module.finrank_fin_fun F25),
    Nat.card_eq_fintype_card, card_F25]
  norm_num

theorem ptP_bijective : Function.Bijective ptP := by
  have : Fintype (ℙ F25 (Fin 2 → F25)) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card ptP).2 ⟨ptP_injective, ?_⟩
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_projF25]

noncomputable def ptEquiv : Fin 26 ≃ ℙ F25 (Fin 2 → F25) := Equiv.ofBijective ptP ptP_bijective

noncomputable def sigma26 : PSL(2, F25) →* Equiv.Perm (Fin 26) :=
  (Equiv.permCongrHom ptEquiv.symm).toMonoidHom.comp Projectivization.PSLAction.toPermHom

theorem sigma26_injective : Function.Injective sigma26 :=
  (Equiv.permCongrHom ptEquiv.symm).injective.comp
    Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective

@[expose] def mv2 (A : Matrix (Fin 2) (Fin 2) F25) (v : Fin 2 → F25) : Fin 2 → F25 :=
  ![A 0 0 * v 0 + A 0 1 * v 1, A 1 0 * v 0 + A 1 1 * v 1]

theorem mulVec_eq_mv2 (A : Matrix (Fin 2) (Fin 2) F25) (v : Fin 2 → F25) : A *ᵥ v = mv2 A v := by
  funext i
  fin_cases i <;> simp [mv2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sigma26_apply_of_cross (A : SL(2, F25)) (τ : Fin 26 → Fin 26)
    (h : ∀ i, mv2 A (ptVec i) 0 * ptVec (τ i) 1 = mv2 A (ptVec i) 1 * ptVec (τ i) 0)
    (i : Fin 26) : sigma26 (A : PSL(2, F25)) i = τ i := by
  have hne : (A : Matrix (Fin 2) (Fin 2) F25) *ᵥ ptVec i ≠ 0 := by
    intro h0
    have hinj := Matrix.mulVec_injective_of_isUnit (A := (A : Matrix (Fin 2) (Fin 2) F25))
      (by rw [Matrix.isUnit_iff_isUnit_det, A.2]; exact isUnit_one)
    exact ptVec_ne_zero i (hinj (h0.trans (Matrix.mulVec_zero _).symm))
  have key : (A : PSL(2, F25)) • ptP i = ptP (τ i) := by
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, ptP, Projectivization.smul_mk]
    refine mk_eq_mk_of_cross _ _ _ _ ?_
    have := h i
    rw [← mulVec_eq_mv2] at this
    exact this
  show ptEquiv.symm (Projectivization.PSLAction.toPermHom (A : PSL(2, F25)) (ptEquiv i)) = τ i
  rw [Equiv.symm_apply_eq]
  exact key

@[expose] def matX : SL(2, F25) :=
  ⟨!![mkF 0 0, mkF 1 0; mkF 4 0, mkF 1 1], by decide +kernel⟩

@[expose] def matS : SL(2, F25) :=
  ⟨!![mkF 0 0, mkF 2 0; mkF 2 0, mkF 0 0], by decide +kernel⟩

@[expose] def matT : SL(2, F25) :=
  ⟨!![mkF 0 0, mkF 1 0; mkF 4 0, mkF 0 0], by decide +kernel⟩

@[expose] def tab26 (a : Array ℕ) (i : Fin 26) : Fin 26 :=
  ⟨a[(i : ℕ)]! % 26, Nat.mod_lt _ (by norm_num)⟩

theorem matX_cross : ∀ i, mv2 matX (ptVec i) 0 * ptVec (tab26 psl26X i) 1 =
    mv2 matX (ptVec i) 1 * ptVec (tab26 psl26X i) 0 := by decide +kernel

theorem matS_cross : ∀ i, mv2 matS (ptVec i) 0 * ptVec (tab26 psl26S i) 1 =
    mv2 matS (ptVec i) 1 * ptVec (tab26 psl26S i) 0 := by decide +kernel

theorem matT_cross : ∀ i, mv2 matT (ptVec i) 0 * ptVec (tab26 psl26T i) 1 =
    mv2 matT (ptVec i) 1 * ptVec (tab26 psl26T i) 0 := by decide +kernel

theorem rep_of_tab {a : Array ℕ} {g : Equiv.Perm (Fin 26)} (ha : ∀ i : Fin 26, a[(i : ℕ)]! < 26)
    (h : ∀ i, g i = tab26 a i) : Rep 26 a g := fun i => by
  rw [h i]
  simp [tab26, Nat.mod_eq_of_lt (ha i)]

theorem psl26X_lt : ∀ i : Fin 26, psl26X[(i : ℕ)]! < 26 := by decide +kernel
theorem psl26S_lt : ∀ i : Fin 26, psl26S[(i : ℕ)]! < 26 := by decide +kernel
theorem psl26T_lt : ∀ i : Fin 26, psl26T[(i : ℕ)]! < 26 := by decide +kernel

theorem rep_sigma26X' : Rep 26 psl26X (sigma26 (matX : PSL(2, F25))) :=
  rep_of_tab psl26X_lt (sigma26_apply_of_cross matX _ matX_cross)

theorem rep_sigma26S' : Rep 26 psl26S (sigma26 (matS : PSL(2, F25))) :=
  rep_of_tab psl26S_lt (sigma26_apply_of_cross matS _ matS_cross)

theorem rep_sigma26T' : Rep 26 psl26T (sigma26 (matT : PSL(2, F25))) :=
  rep_of_tab psl26T_lt (sigma26_apply_of_cross matT _ matT_cross)

theorem rep_powArr {n : ℕ} {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hg : Rep n g G) :
    ∀ k, Rep n (powArr n g k) (G ^ k)
  | 0 => by simpa [powArr] using (rep_idA (n := n))
  | k + 1 => by
    rw [pow_succ']
    exact rep_compA hg (rep_powArr hg k)

theorem psl26_check :
    ruChainOK 26 psl26Strong 3 9 [0, 1, 2] psl26Words = true ∧
    rawOrbitSizes 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) = [26, 25, 12] ∧
    eqA 26 psl26Strong[0]! psl26X = true ∧ eqA 26 psl26Strong[1]! psl26S = true ∧
    eqA 26 psl26Strong[2]! psl26T = true ∧ psl26OrdersOK psl26Levels = true ∧
    psl26D.size = 26 ∧ eqA 26 psl26D[0]! (idA 26) = true ∧ psl26DClosed psl26X = true ∧
    psl26DClosed psl26S = true ∧ psl26DClosed (invCand 26 psl26X) = true ∧
    psl26DClosed (invCand 26 psl26S) = true ∧ (psl26D.all fun e => !eqA 26 e psl26T) = true ∧
    psl26RelOK = true ∧
    (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 0).pts.size = 26 ∧
    (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 1).pts.size = 25 ∧
    (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 2).pts.size = 12 :=
  Certificates.certificate7044

theorem psl26_chainOK :
    ruChainOK 26 psl26Strong 3 9 [0, 1, 2] psl26Words = true :=
  psl26_check.1

theorem psl26_orbitSizes :
    rawOrbitSizes 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) = [26, 25, 12] :=
  psl26_check.2.1

theorem psl26_gens :
    eqA 26 psl26Strong[0]! psl26X = true ∧ eqA 26 psl26Strong[1]! psl26S = true ∧
    eqA 26 psl26Strong[2]! psl26T = true :=
  ⟨psl26_check.2.2.1, psl26_check.2.2.2.1, psl26_check.2.2.2.2.1⟩

theorem psl26_orders :
    psl26OrdersOK psl26Levels = true := psl26_check.2.2.2.2.2.1

theorem psl26_D :
    psl26D.size = 26 ∧ eqA 26 psl26D[0]! (idA 26) = true ∧
    psl26DClosed psl26X = true ∧ psl26DClosed psl26S = true ∧
    psl26DClosed (invCand 26 psl26X) = true ∧ psl26DClosed (invCand 26 psl26S) = true ∧
    (psl26D.all fun e => !eqA 26 e psl26T) = true := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4, h5, h6, h7, -⟩ := psl26_check
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem psl26_rel : psl26RelOK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := psl26_check
  exact h

theorem psl26_levels :
    (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 0).pts.size = 26 ∧
    (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 1).pts.size = 25 ∧
    (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 2).pts.size = 12 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := psl26_check
  exact h

@[expose] noncomputable def pslX : PSL(2, F25) := ((matX : SL(2, F25)) : PSL(2, F25))

@[expose] noncomputable def pslS : PSL(2, F25) := ((matS : SL(2, F25)) : PSL(2, F25))

@[expose] noncomputable def pslT : PSL(2, F25) := ((matT : SL(2, F25)) : PSL(2, F25))

theorem rep_sigma26X : Rep 26 psl26X (sigma26 pslX) := rep_sigma26X'

theorem rep_sigma26S : Rep 26 psl26S (sigma26 pslS) := rep_sigma26S'

theorem rep_sigma26T : Rep 26 psl26T (sigma26 pslT) := rep_sigma26T'

noncomputable def psl26Chain : RawSchreierDatum 26 :=
  RawSchreierDatum.ofArrays 26 (by norm_num) psl26Strong 3 (by decide)
    (ruFinList 26 (by norm_num) [0, 1, 2]) (by decide) (ruWordsArr 3 9 psl26Words)

theorem psl26Chain_original :
    psl26Chain.original.toList = [sigma26 pslX, sigma26 pslS, sigma26 pslT] := by
  have h := psl26_chainOK
  rw [show psl26Chain.original.toList = (List.range 3).map fun i => permOfArr 26
    psl26Strong[i]! from ofArrays_original_toList, show List.range 3 = [0, 1, 2] from rfl,
    List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    eq_of_eqA (rep_permOfArr (ruChain_strong_inv h (by decide))).1 rep_sigma26X
      psl26_gens.1,
    eq_of_eqA (rep_permOfArr (ruChain_strong_inv h (by decide))).1 rep_sigma26S
      psl26_gens.2.1,
    eq_of_eqA (rep_permOfArr (ruChain_strong_inv h (by decide))).1 rep_sigma26T
      psl26_gens.2.2]

theorem psl26Chain_sub : psl26Chain.originalSubgroup =
    Subgroup.closure {sigma26 pslX, sigma26 pslS, sigma26 pslT} := by
  rw [RawSchreierDatum.originalSubgroup, psl26Chain_original]
  congr 1
  ext g
  simp

theorem card_closure26 :
    Nat.card (Subgroup.closure {sigma26 pslX, sigma26 pslS, sigma26 pslT}) = 7800 := by
  have h := ruChain_card (n := 26) (hn := by norm_num) (hpos := by norm_num) (k := 3) (s := 9)
    (hk := by decide) (b := [0, 1, 2]) (hb := by decide) psl26_chainOK
  rw [psl26_orbitSizes] at h
  rw [← psl26Chain_sub]
  exact h

theorem card_psl2F25 : Nat.card PSL(2, F25) = 7800 := by
  rw [Nat.card_congr pslF25EquivGalois.toEquiv,
    CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (by norm_num) (by norm_num)]
  norm_num

theorem map_sigma26_closure :
    (Subgroup.closure {pslX, pslS, pslT}).map sigma26 =
      Subgroup.closure {sigma26 pslX, sigma26 pslS, sigma26 pslT} := by
  rw [MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton]

theorem closure_pslXST :
    Subgroup.closure {pslX, pslS, pslT} = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [card_psl2F25, ← card_closure26, ← map_sigma26_closure]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ sigma26_injective).toEquiv

theorem range_sigma26 :
    sigma26.range = Subgroup.closure {sigma26 pslX, sigma26 pslS, sigma26 pslT} := by
  rw [MonoidHom.range_eq_map, ← closure_pslXST, map_sigma26_closure]

theorem psl2F25_pow (g : PSL(2, F25)) :
    g ^ 12 = 1 ∨ g ^ 13 = 1 ∨ g ^ 5 = 1 := by
  have h := psl26_chainOK
  have hA := ruChain_arrays (n := 26) (hn := by norm_num) (hpos := by norm_num) (k := 3)
    (s := 9) (hk := by decide) (b := [0, 1, 2]) (hb := by decide) h
  have hF := chainCheckFacts (n := 26) (chunks := 4) h
  have hg : sigma26 g ∈ psl26Chain.originalSubgroup := by
    rw [psl26Chain_sub, ← range_sigma26]
    exact ⟨g, rfl⟩
  have hbc : psl26Chain.baseCount = 3 := rfl
  have h3 : 3 ≤ psl26Chain.baseCount := hbc.ge
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := ChainArrays.exists_prod3 hA (by norm_num) h h3
    (fun i hi3 hi => by
      have : i < 3 := hi
      omega) hg
  have hsz := psl26_levels
  have ha' : a < 26 := hsz.1 ▸ ha
  have hb' : b < 25 := hsz.2.1 ▸ hb
  have hc' : c < 12 := hsz.2.2 ▸ hc
  have hcheck := allLt_spec (allLt_spec (allLt_spec psl26_orders ha') hb') hc'
  have hrep : Rep 26 (Array.ofFn (n := 26) fun p => tr3 psl26Levels a b c p.val)
      (sigma26 g) := by
    intro p
    rw [getElem!_ofFn_nat _ p.2, ← habc]
    exact (ChainArrays.prod3_apply hA hF h3 ha hb hc p).symm
  have key : sigma26 g ^ 12 = 1 ∨ sigma26 g ^ 13 = 1 ∨ sigma26 g ^ 5 = 1 := by
    simp only [Bool.or_eq_true] at hcheck
    rcases hcheck with (h12 | h13) | h5
    · exact Or.inl (eq_of_eqA (rep_powArr hrep 12) rep_idA h12)
    · exact Or.inr (Or.inl (eq_of_eqA (rep_powArr hrep 13) rep_idA h13))
    · exact Or.inr (Or.inr (eq_of_eqA (rep_powArr hrep 5) rep_idA h5))
  rcases key with hk | hk | hk
  · exact Or.inl (sigma26_injective (by rw [map_pow, hk, map_one]))
  · exact Or.inr (Or.inl (sigma26_injective (by rw [map_pow, hk, map_one])))
  · exact Or.inr (Or.inr (sigma26_injective (by rw [map_pow, hk, map_one])))

theorem rep_of_eqA {n : ℕ} {f t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : eqA n f t = true)
    (ht : Rep n t g) : Rep n f g := fun x => by
  have := allLt_spec h x.2
  rw [beq_iff_eq] at this
  rw [this, ht x]

theorem mem_closure_xs_psl26D {g : Equiv.Perm (Fin 26)}
    (hg : g ∈ Subgroup.closure {sigma26 pslX, sigma26 pslS}) :
    ∃ i < 26, Rep 26 psl26D[i]! g := by
  obtain ⟨hsz, h0, hclX, hclS, hclXi, hclSi, -⟩ := psl26_D
  have hR := psl26_rel
  simp only [psl26RelOK, Bool.and_eq_true] at hR
  obtain ⟨⟨-, hXi⟩, hSi⟩ := hR
  have rX : Rep 26 psl26X (sigma26 pslX) := rep_sigma26X
  have rS : Rep 26 psl26S (sigma26 pslS) := rep_sigma26S
  have rXi := rep_inv_of_isInvA rX hXi
  have rSi := rep_inv_of_isInvA rS hSi
  have step : ∀ (a : Array ℕ) (A : Equiv.Perm (Fin 26)), Rep 26 a A →
      psl26DClosed a = true →
      ∀ y, (∃ i < 26, Rep 26 psl26D[i]! y) → ∃ i < 26, Rep 26 psl26D[i]! (A * y) := by
    rintro a A ha hall y ⟨i, hi, hy⟩
    obtain ⟨j, hj, hje⟩ := Array.any_eq_true.1 (allLt_spec hall hi)
    refine ⟨j, hsz ▸ hj, ?_⟩
    rw [show psl26D[j]! = psl26D[j] from getElem!_pos psl26D j hj]
    exact rep_of_eqA hje (rep_compA ha hy)
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, by norm_num, rep_of_eqA h0 rep_idA⟩
  | mul_left x hx y hy ih =>
    rcases hx with rfl | rfl
    · exact step _ _ rX hclX y ih
    · exact step _ _ rS hclS y ih
  | inv_mul_cancel x hx y hy ih =>
    rcases hx with rfl | rfl
    · exact step _ _ rXi hclXi y ih
    · exact step _ _ rSi hclSi y ih

theorem psl225_witnesses {K : Type*} [Group K]
    (e : K ≃* PSL(2, GaloisField 5 2)) :
    Nat.card K = 7800 ∧ ∃ x s t : K, orderOf x = 13 ∧ orderOf s = 2 ∧ s * x * s⁻¹ = x⁻¹ ∧
      orderOf t = 2 ∧ t * s = s * t ∧ t ∉ Subgroup.closure {x, s} ∧
      Subgroup.closure {x, s, t} = ⊤ ∧ ∀ k : K, k ^ 12 = 1 ∨ k ^ 13 = 1 ∨ k ^ 5 = 1 := by
  let φ : K ≃* PSL(2, F25) := e.trans pslF25EquivGalois.symm
  let ψ : K →* Equiv.Perm (Fin 26) := sigma26.comp φ.toMonoidHom
  have hψ : Function.Injective ψ := sigma26_injective.comp φ.injective
  have hR := psl26_rel
  simp only [psl26RelOK, Bool.and_eq_true, Bool.not_eq_true'] at hR
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hX13, hX1⟩, hS2⟩, hS1⟩, hT2⟩, hT1⟩, hSXSX⟩, hTS⟩, -⟩, -⟩ := hR
  have rX : Rep 26 psl26X (ψ (φ.symm pslX)) := by
    have e : ψ (φ.symm pslX) = sigma26 pslX := by simp [ψ]
    rw [e]
    exact rep_sigma26X
  have rS : Rep 26 psl26S (ψ (φ.symm pslS)) := by
    have e : ψ (φ.symm pslS) = sigma26 pslS := by simp [ψ]
    rw [e]
    exact rep_sigma26S
  have rT : Rep 26 psl26T (ψ (φ.symm pslT)) := by
    have e : ψ (φ.symm pslT) = sigma26 pslT := by simp [ψ]
    rw [e]
    exact rep_sigma26T
  have hinj : ∀ a b : K, ψ a = ψ b → a = b := fun a b h => hψ h
  have ne1 : ∀ (a : Array ℕ) (k : K), Rep 26 a (ψ k) → eqA 26 a (idA 26) = false → k ≠ 1 := by
    intro a k ha h hk
    rw [hk, map_one] at ha
    rw [(eqA_iff ha rep_idA).2 rfl] at h
    exact Bool.false_ne_true h.symm
  have powk : ∀ (a : Array ℕ) (k : K) (m : ℕ), Rep 26 a (ψ k) →
      eqA 26 (powArr 26 a m) (idA 26) = true → k ^ m = 1 := by
    intro a k m ha h
    apply hψ
    rw [map_pow, map_one]
    exact eq_of_eqA (rep_powArr ha m) rep_idA h
  refine ⟨?_, φ.symm pslX, φ.symm pslS, φ.symm pslT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr φ.toEquiv, card_psl2F25]
  · exact orderOf_eq_prime (powk _ _ 13 rX hX13) (ne1 _ _ rX hX1)
  · exact orderOf_eq_prime (powk _ _ 2 rS hS2) (ne1 _ _ rS hS1)
  · have hs2 : (φ.symm pslS) ^ 2 = 1 := powk _ _ 2 rS hS2
    have hsinv : (φ.symm pslS)⁻¹ = φ.symm pslS := by
      rw [inv_eq_iff_mul_eq_one, ← sq, hs2]
    rw [hsinv]
    have h4 : ψ (φ.symm pslS * φ.symm pslX * φ.symm pslS * φ.symm pslX) = 1 := by
      rw [map_mul, map_mul, map_mul]
      exact eq_of_eqA (rep_compA (rep_compA (rep_compA rS rX) rS) rX) rep_idA hSXSX
    have : φ.symm pslS * φ.symm pslX * φ.symm pslS * φ.symm pslX = 1 := by
      apply hψ
      rw [h4, map_one]
    exact eq_inv_of_mul_eq_one_left this
  · exact orderOf_eq_prime (powk _ _ 2 rT hT2) (ne1 _ _ rT hT1)
  · apply hψ
    rw [map_mul, map_mul]
    exact eq_of_eqA (rep_compA rT rS) (rep_compA rS rT) hTS
  · intro hmem
    have hm : ψ (φ.symm pslT) ∈ Subgroup.closure {sigma26 pslX, sigma26 pslS} := by
      have := Subgroup.mem_map_of_mem ψ hmem
      rw [MonoidHom.map_closure] at this
      simpa [ψ, Set.image_insert_eq, Set.image_singleton] using this
    obtain ⟨i, hi, hrep⟩ := mem_closure_xs_psl26D hm
    obtain ⟨hsz, -, -, -, -, -, hall⟩ := psl26_D
    have hi' : i < psl26D.size := hsz ▸ hi
    have hnot := Array.all_eq_true.1 hall i hi'
    rw [show psl26D[i] = psl26D[i]! from (getElem!_pos psl26D i hi').symm] at hnot
    rw [(eqA_iff hrep rT).2 rfl] at hnot
    exact Bool.false_ne_true hnot
  · have h := closure_pslXST
    apply_fun Subgroup.map φ.symm.toMonoidHom at h
    rw [MonoidHom.map_closure] at h
    rw [Subgroup.map_top_of_surjective _ φ.symm.surjective] at h
    simpa [Set.image_insert_eq, Set.image_singleton] using h
  · intro k
    rcases psl2F25_pow (φ k) with h | h | h
    · exact Or.inl (φ.injective (by rw [map_pow, h, map_one]))
    · exact Or.inr (Or.inl (φ.injective (by rw [map_pow, h, map_one])))
    · exact Or.inr (Or.inr (φ.injective (by rw [map_pow, h, map_one])))

end CFSG.Quasithin.RuRank3

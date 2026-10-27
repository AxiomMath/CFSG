module

public import CFSG.Quasithin.Background.SmithB45SzRep
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiModule
public import CFSG.Quasithin.Background.SmithB42Sp4Desc

public section

namespace CFSG.Quasithin

namespace B45Sz

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.X7 CFSG.Blueprint
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.LieType.Ree
open Representation Matrix

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]

section Sylow

theorem szIncl_suzukiSElt (hK : Nat.card K = 2 ^ (2 * a + 1))
    (u v : K) :
    szIncl hK (suzukiSElt a K u v) = lowUSp u v (u ^ 2 ^ (a + 1)) (suzukiN a u v) := by
  refine Subtype.ext (Units.ext ?_)
  change suzukiS a u v = lowU u v (u ^ 2 ^ (a + 1)) (suzukiN a u v)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiS, lowU, pow_succ]
  ring

theorem szIncl_mem_lowerUniSp (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ↥(suzukiGroup a K)} (hg : g ∈ suzukiU a K) : szIncl hK g ∈ lowerUniSp K := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).mp hg
  rw [szIncl_suzukiSElt]
  exact ⟨_, _, _, _, rfl⟩

theorem szIncl_suzukiWElt (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    szIncl hK (suzukiWElt a K) = Jsp := by
  refine Subtype.ext (Units.ext ?_)
  change suzukiW K = minorJ K
  ext i j
  rw [minorJ_apply]
  rfl

variable (a K) in
@[expose] noncomputable def szUp : Subgroup ↥(suzukiGroup a K) :=
  (suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom

theorem szIncl_mem_upperUniSp (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ↥(suzukiGroup a K)} (hg : g ∈ szUp a K) : szIncl hK g ∈ upperUniSp K := by
  obtain ⟨u, hu, rfl⟩ := hg
  refine ⟨szIncl hK u, szIncl_mem_lowerUniSp hK hu, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    szIncl_suzukiWElt hK]

omit [CharP K 2] in
theorem isPGroup_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsPGroup 2 ↥(suzukiU a K) := by
  have h := (CFSG.QuasithinUnique.Setup.Family.suzukiSylow (a := a) hK).isPGroup'
  rwa [CFSG.QuasithinUnique.Setup.Family.coe_suzukiSylow hK] at h

omit [CharP K 2] in
theorem isPGroup_szUp (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsPGroup 2 ↥(szUp a K) :=
  (isPGroup_suzukiU hK).map _

noncomputable instance instFintypeSuzukiU :
    Fintype ↥(suzukiU a K) := Fintype.ofFinite _

omit [CharP K 2] in
theorem card_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Fintype.card ↥(suzukiU a K) = 4 ^ (2 * a + 1) := by
  rw [← Nat.card_eq_fintype_card, (suzuki_unipotent_structure hK).2.1, ← pow_mul,
    show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring_nf

@[expose] noncomputable def suzukiUEquiv
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : K × K ≃ ↥(suzukiU a K) :=
  Equiv.ofBijective (fun p => ⟨suzukiSElt a K p.1 p.2, (mem_suzukiU_iff hK).mpr ⟨_, _, rfl⟩⟩)
    ⟨fun p p' h => by
      have h1 := suzukiSElt_inj.mp (congrArg Subtype.val h)
      exact Prod.ext h1.1 h1.2,
     fun g => by
      obtain ⟨u, v, hg⟩ := (mem_suzukiU_iff hK).mp g.2
      exact ⟨(u, v), Subtype.ext hg⟩⟩

omit [CharP K 2] in
theorem coe_suzukiUEquiv (hK : Nat.card K = 2 ^ (2 * a + 1))
    (p : K × K) : (suzukiUEquiv hK p : ↥(suzukiGroup a K)) = suzukiSElt a K p.1 p.2 := rfl

end Sylow

section Norm

variable (k : Type) [Field k] [Algebra K k]

theorem natRepS_two_mul_three_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : ℕ) (u v : K) :
    natRepS k (2 * c) (szIncl hK (suzukiSElt a K u v)) 3 0 =
      algebraMap K k (suzukiN a u v) ^ 2 ^ c := by
  have h := B42Sp4.natRepS_add_two_mul_pow (F := K) k 0 c (szIncl hK (suzukiSElt a K u v))
  rw [zero_add] at h
  rw [h, Matrix.map_apply, natRepS_apply, pow_zero, MulAut.one_apply, Matrix.map_apply]
  rfl

theorem szT_coeff (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    ((szT k hK (szOmega a) (suzukiSElt a K u v)).mulVec (hwS k (szOmega a))) (fun _ => 3) =
      algebraMap K k (suzukiN a u v ^ (2 ^ (2 * a + 1) - 1)) := by
  rw [szT_apply, tensorRepS_mulVec_hwS]
  rw [Finset.prod_coe_sort (szOmega a)
    (fun i => natRepS k i (szIncl hK (suzukiSElt a K u v)) 3 0)]
  rw [szOmega, Finset.prod_image (fun x _ y _ h => by simpa using h)]
  simp_rw [natRepS_two_mul_three_zero k hK]
  rw [prod_pow_two_pow, map_pow]

theorem sum_suzukiN_pow (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∑ p : K × K, suzukiN a p.1 p.2 ^ (2 ^ (2 * a + 1) - 1) = 1 := by
  classical
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have hq1 : 2 ^ (2 * a + 1) - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hterm : ∀ p : K × K, suzukiN a p.1 p.2 ^ (2 ^ (2 * a + 1) - 1) =
      if p = 0 then 0 else 1 := by
    intro p
    by_cases hp : p = 0
    · subst hp
      have : suzukiN a (0 : K) 0 = 0 :=
        (suzuki_norm_nonzero a K hK 0 0).mpr ⟨rfl, rfl⟩
      simp [this, zero_pow hq1]
    · have hN : suzukiN a p.1 p.2 ≠ 0 := fun h => hp (Prod.ext
        ((suzuki_norm_nonzero a K hK p.1 p.2).mp h).1 ((suzuki_norm_nonzero a K hK p.1 p.2).mp h).2)
      rw [show (if p = 0 then (0 : K) else 1) = 1 from by simp [hp], ← hcard]
      exact FiniteField.pow_card_sub_one_eq_one _ hN
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_ne' Finset.univ (0 : K × K), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_prod, hcard]
  set M : ℕ := 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) with hM
  have hpos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hM0 : ((M : ℕ) : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K 2, hM]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have h3 : ((M - 1 : ℕ) : K) + 1 = ((M : ℕ) : K) := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hpos]
  rw [hM0] at h3
  have h1 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  linear_combination h3 - h1

theorem szT_norm_coeff (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∑ g : ↥(suzukiU a K), ((szT k hK (szOmega a) (g : ↥(suzukiGroup a K))).mulVec
      (hwS k (szOmega a))) (fun _ => 3) = 1 := by
  rw [← (suzukiUEquiv hK).sum_comp]
  simp_rw [coe_suzukiUEquiv, szT_coeff k hK]
  rw [← map_sum, sum_suzukiN_pow hK, map_one]

theorem szOrbit_basis [CharP k 2]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ b : Module.Basis ↥(suzukiU a K) k ((↥(szOmega a) → Fin 4) → k),
      ∀ u : ↥(suzukiU a K), b u = (szT k hK (szOmega a) (u : ↥(suzukiGroup a K))).mulVec
        (hwS k (szOmega a)) := by
  classical
  let ρ : ↥(suzukiU a K) →* (((↥(szOmega a) → Fin 4) → k) →ₗ[k] ((↥(szOmega a) → Fin 4) → k)) :=
    (matRep (szT k hK (szOmega a))).comp (suzukiU a K).subtype
  have hv : ∑ g : ↥(suzukiU a K), ρ g (hwS k (szOmega a)) ≠ 0 := by
    intro h
    have h2 := szT_norm_coeff k hK
    have h3 : ∑ g : ↥(suzukiU a K), ((szT k hK (szOmega a) (g : ↥(suzukiGroup a K))).mulVec
        (hwS k (szOmega a))) (fun _ => 3) = 0 := by
      have := congrFun h (fun _ => 3)
      rw [Finset.sum_apply] at this
      exact this
    exact zero_ne_one (h3.symm.trans h2)
  have hdim : Module.finrank k ((↥(szOmega a) → Fin 4) → k) = Fintype.card ↥(suzukiU a K) := by
    rw [finrank_tensorRepS, card_szOmega, card_suzukiU hK]
  obtain ⟨b, hb, -, -⟩ := orbit_regular_of_norm_ne_zero k Nat.prime_two (isPGroup_suzukiU hK) ρ
    (hwS k (szOmega a)) hv hdim
  exact ⟨b, fun u => by rw [hb]; rfl⟩

theorem szCoords_li [CharP k 2]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    LinearIndependent k (fun x : (↥(szOmega a) → Fin 4) => fun u : ↥(suzukiU a K) =>
      ((szT k hK (szOmega a) (u : ↥(suzukiGroup a K))).mulVec (hwS k (szOmega a))) x) := by
  obtain ⟨b, hb⟩ := szOrbit_basis k hK
  refine coords_linearIndependent_of_span (szT k hK (szOmega a)) (suzukiU a K)
    (hwS k (szOmega a)) ?_
  have : (fun u : ↥(suzukiU a K) => matRep (szT k hK (szOmega a)) (u : ↥(suzukiGroup a K))
      (hwS k (szOmega a))) = ⇑b := funext fun u => (hb u).symm
  rw [this]
  exact b.span_eq

theorem szMixed_span [CharP k 2]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {A : Finset ℕ} (hA : A ⊆ szOmega a) :
    Submodule.span k (Set.range fun u : ↥(suzukiU a K) =>
      matRep (szT k hK A) (u : ↥(suzukiGroup a K)) (hwS k A)) = ⊤ := by
  refine span_orbit_eq_top_of_coords _ _ _ ?_
  have h := (szCoords_li k hK).comp (embIdx A (szOmega a)) (embIdx_injective hA)
  convert h using 1
  funext x u
  exact coord_eq_emb k hA x ⟨szIncl hK u, szIncl_mem_lowerUniSp hK u.2⟩

end Norm

section Irred

variable (k : Type) [Field k] [Algebra K k] [CharP k 2]

theorem szT_fixed_irreducible (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A : Finset ℕ} (hA : A ⊆ szOmega a) :
    fixedSub (matRep (szT k hK A)) (szUp a K) = Submodule.span k {hwS k A} ∧
      (matRep (szT k hK A)).IsIrreducible := by
  have hspan := szMixed_span k hK hA
  have : Finite ↥(szUp a K) := inferInstance
  refine fixedSub_eq_span_and_irreducible k Nat.prime_two (matRep (szT k hK A))
    (suzukiU a K) (szUp a K) (isPGroup_szUp hK) (suzukiWElt a K) (fun u hu => ⟨u, hu, rfl⟩)
    (hwS k A) (hwS_ne_zero k A) ?_ hspan ?_
  · intro h hh
    exact tensorRepS_upper_fixed k A (szIncl_mem_upperUniSp hK hh)
  · refine hline_of_selfdual (szT k hK A) (suzukiU a K) (JtS K k A) (JtS_mul_self k A)
      (fun g => ?_) (hwS k A) hspan
    rw [szT_apply, szT_apply, map_inv]
    exact tensorRepS_inv_transpose k A (szIncl hK g)

end Irred

section Torus

variable (k : Type) [Field k] [Algebra K k] [CharP k 2]

theorem szIncl_suzukiDElt (hK : Nat.card K = 2 ^ (2 * a + 1))
    (l : Kˣ) :
    szIncl hK (suzukiDElt a K l) = dSp (l ^ (1 + (2 ^ a : ℤ))) (l ^ (2 ^ a : ℤ)) := by
  refine Subtype.ext (Units.ext ?_)
  change suzukiD a l = dmat ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ((l ^ (2 ^ a : ℤ) : Kˣ) : K)
  rw [suzukiD, dmat]
  congr 1
  ext i
  fin_cases i
  · rfl
  · rfl
  · show ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K) = ((l ^ (2 ^ a : ℤ) : Kˣ) : K)⁻¹
    rw [← Units.val_inv_eq_inv_val, ← _root_.zpow_neg]
  · show ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) = ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K)⁻¹
    rw [← Units.val_inv_eq_inv_val, ← _root_.zpow_neg]
    congr 2
    ring

theorem nIdx_eq_zero {A : Finset ℕ} (hA : A ⊆ szOmega a) : nIdx (2 * a + 1) A = 0 := by
  unfold nIdx
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [ite_eq_right_iff]
  intro h
  exfalso
  obtain ⟨c, -, hc⟩ := mem_szOmega.mp (hA h)
  omega

omit [CharP k 2] in
theorem szT_suzukiDElt_hwS (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A : Finset ℕ} (hA : A ⊆ szOmega a) (l : Kˣ) :
    (szT k hK A (suzukiDElt a K l)).mulVec (hwS k A) =
      (algebraMap K k ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ^ mIdx (2 * a + 1) A) • hwS k A := by
  rw [szT_apply, szIncl_suzukiDElt hK, tensorRepS_dSp_hwS,
    prod_dChar k (hA.trans szOmega_subset), nIdx_eq_zero hA]
  simp

theorem szIso_torus_char (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A B : Finset ℕ} (hA : A ⊆ szOmega a) (hB : B ⊆ szOmega a)
    {P : Matrix (B → Fin 4) (A → Fin 4) k} {Q : Matrix (A → Fin 4) (B → Fin 4) k}
    (h : MatIso (szT k hK A) (szT k hK B) P Q) (l : Kˣ) :
    algebraMap K k ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ^ mIdx (2 * a + 1) A =
      algebraMap K k ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ^ mIdx (2 * a + 1) B := by
  obtain ⟨hfixA, -⟩ := szT_fixed_irreducible k hK hA
  obtain ⟨hfixB, -⟩ := szT_fixed_irreducible k hK hB
  have hmem : hwS k A ∈ fixedSub (matRep (szT k hK A)) (szUp a K) := by
    rw [hfixA]
    exact Submodule.mem_span_singleton_self _
  have hmem' : P.mulVec (hwS k A) ∈ fixedSub (matRep (szT k hK B)) (szUp a K) := by
    refine mem_fixedSub.mpr fun u hu => ?_
    have h1 := mem_fixedSub.mp hmem u hu
    simp only [matRep_apply] at h1 ⊢
    rw [Matrix.mulVec_mulVec, ← h.comm, ← Matrix.mulVec_mulVec, h1]
  rw [hfixB] at hmem'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem'
  have hne : P.mulVec (hwS k A) ≠ 0 := by
    intro h0
    have h2 : hwS k A = 0 := by
      have := congrArg Q.mulVec h0
      rwa [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact hwS_ne_zero k A h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hc, zero_smul])
  have e1 : (szT k hK B (suzukiDElt a K l)).mulVec (P.mulVec (hwS k A)) =
      P.mulVec ((szT k hK A (suzukiDElt a K l)).mulVec (hwS k A)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h.comm]
  rw [szT_suzukiDElt_hwS k hK hA, Matrix.mulVec_smul, ← hc, Matrix.mulVec_smul,
    szT_suzukiDElt_hwS k hK hB, smul_smul, smul_smul] at e1
  have e2 := smul_left_injective k (hwS_ne_zero k B) e1
  have e3 : c * _ = c * _ := e2.trans (mul_comm _ _)
  exact (mul_left_cancel₀ hc0 e3).symm

theorem eq_of_evenBits {A B : Finset ℕ} (hA : A ⊆ szOmega a) (hB : B ⊆ szOmega a)
    (h : evenBits (2 * a + 1) A = evenBits (2 * a + 1) B) : A = B := by
  refine eq_of_bits (hA.trans szOmega_subset) (hB.trans szOmega_subset) h ?_
  funext j
  have hA' : 2 * (j : ℕ) + 1 ∉ A := fun hj => by
    obtain ⟨c, -, hc⟩ := mem_szOmega.mp (hA hj)
    omega
  have hB' : 2 * (j : ℕ) + 1 ∉ B := fun hj => by
    obtain ⟨c, -, hc⟩ := mem_szOmega.mp (hB hj)
    omega
  simp [oddBits, hA', hB']

theorem eq_szOmega_of_evenBits {A : Finset ℕ} (hA : A ⊆ szOmega a)
    (h : evenBits (2 * a + 1) A = CFSG.QuasithinUnique.Setup.X7a.ones (2 * a + 1)) :
    A = szOmega a := by
  refine eq_of_evenBits hA le_rfl (h.trans ?_)
  funext j
  have hj := j.2
  simp [evenBits, CFSG.QuasithinUnique.Setup.X7a.ones, mem_szOmega]
  omega

theorem szT_eq_of_equiv (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A B : Finset ℕ} (hA : A ⊆ szOmega a) (hB : B ⊆ szOmega a)
    (e : Nonempty ((matRep (szT k hK A)).Equiv (matRep (szT k hK B)))) : A = B := by
  obtain ⟨e⟩ := e
  obtain ⟨P, Q, h⟩ := MatIso.exists_of_equiv e
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hbij⟩ := suzuki_frobenius_exponents a K hK
  have hM : ∀ z : Kˣ, z ^ mIdx (2 * a + 1) A = z ^ mIdx (2 * a + 1) B := by
    intro z
    obtain ⟨l, rfl⟩ := hbij.2 z
    have h1 := szIso_torus_char k hK hA hB h l
    apply Units.ext
    apply (algebraMap K k).injective
    simpa [map_pow] using h1
  simp only [mIdx_eq_mBits] at hM
  have hdim : A.card = B.card := by
    have h1 := h.card_eq
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] at h1
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h1
  rcases CFSG.QuasithinUnique.Setup.X7a.torus_weight_eq hcard
    (CFSG.QuasithinUnique.Setup.X7a.mBits_lt _) (CFSG.QuasithinUnique.Setup.X7a.mBits_lt _) hM
    with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact eq_of_evenBits hA hB (CFSG.QuasithinUnique.Setup.X7a.mBits_injective h1)
  · exfalso
    have hA0 : A = ∅ := by
      have := CFSG.QuasithinUnique.Setup.X7a.mBits_eq_zero h1
      refine eq_of_evenBits hA (Finset.empty_subset _) (this.trans ?_)
      funext j
      simp [evenBits, CFSG.QuasithinUnique.Setup.X7a.zeros]
    have hBΩ := eq_szOmega_of_evenBits hB (CFSG.QuasithinUnique.Setup.X7a.eq_ones_of_mBits h2)
    rw [hA0, hBΩ, card_szOmega, Finset.card_empty] at hdim
    omega
  · exfalso
    have hB0 : B = ∅ := by
      have := CFSG.QuasithinUnique.Setup.X7a.mBits_eq_zero h1
      refine eq_of_evenBits hB (Finset.empty_subset _) (this.trans ?_)
      funext j
      simp [evenBits, CFSG.QuasithinUnique.Setup.X7a.zeros]
    have hAΩ := eq_szOmega_of_evenBits hA (CFSG.QuasithinUnique.Setup.X7a.eq_ones_of_mBits h2)
    rw [hB0, hAΩ, card_szOmega, Finset.card_empty] at hdim
    omega

end Torus

end B45Sz

end CFSG.Quasithin

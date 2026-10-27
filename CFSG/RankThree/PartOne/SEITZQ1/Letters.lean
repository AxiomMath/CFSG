module

public import Certificates.Certificate14947
public import CFSG.LieType.Ree.LargeReeInvolutionFusionWord
public import CFSG.RankThree.PartOne.SEITZQ1.Conj

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR
open scoped MatrixGroups

section Words

variable {L : Type} [Field L]

@[expose] def q1Tv (ω : L) (x : Fin 3 × Fin 3 × Fin 4) : SL(3, L) :=
  if h : x.1 ≠ x.2.1 then Matrix.SpecialLinearGroup.transvection h (f4Ev ω x.2.2) else 1

@[expose] def q1TvProd (ω : L) (l : List (Fin 3 × Fin 3 × Fin 4)) : SL(3, L) :=
  (l.map (q1Tv ω)).prod

theorem q1TvProd_cons (ω : L) (x : Fin 3 × Fin 3 × Fin 4) (l : List (Fin 3 × Fin 3 × Fin 4)) :
    q1TvProd ω (x :: l) = q1Tv ω x * q1TvProd ω l := by
  rw [q1TvProd, List.map_cons, List.prod_cons, ← q1TvProd]

theorem coe_q1TvProd [CharP L 2] {ω : L} (hω : ω ^ 2 + ω + 1 = 0)
    (l : List (Fin 3 × Fin 3 × Fin 4)) (hl : ∀ x ∈ l, x.1 ≠ x.2.1) :
    ((q1TvProd ω l : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = f4MEv ω (f4MProd l) := by
  induction l with
  | nil =>
    rw [f4MProd, List.foldr_nil, f4MEv_one]
    rfl
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    rw [q1TvProd_cons, Matrix.SpecialLinearGroup.coe_mul,
      ih fun y hy => hl y (List.mem_cons_of_mem _ hy),
      show f4MProd (x :: l) = f4MMul (f4MTv x.1 x.2.1 x.2.2) (f4MProd l) from rfl,
      f4MEv_mul hω, f4MEv_tv hx]
    simp only [q1Tv, ne_eq, hx, not_false_eq_true, ↓reduceDIte, CFSG.LinearGroups.coe_transvection]

theorem f4Ev_eq_coef [CharP L 2] {ω : L} (hω : ω ^ 2 + ω + 1 = 0) (t : Fin 4) :
    f4Ev ω t = (q1Coef t : L) * ω ^ q1Pow t := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  fin_cases t <;> simp [f4Ev, q1Coef, q1Pow]
  linear_combination (-1 : L) * hω + (ω + 1) * h2

theorem f4Ev_pow_two_pow [CharP L 2] {ω : L} (hω : ω ^ 2 + ω + 1 = 0) (a : ℕ) (t : Fin 4) :
    f4Ev ω t ^ 2 ^ a = f4Ev ω (q1Frob (a % 2 == 1) t) := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadd : (ω + 1) ^ 2 ^ a = ω ^ 2 ^ a + 1 := by
    rw [add_pow_char_pow, one_pow]
  rcases Nat.even_or_odd a with ha | ha
  · have hb : (a % 2 == 1) = false := by simp [Nat.even_iff.1 ha]
    have hω' := (omega_pow_two_pow hω a).1 ha
    rw [hb]
    fin_cases t <;> simp [f4Ev, q1Frob, hadd, hω']
  · have hb : (a % 2 == 1) = true := by simp [Nat.odd_iff.1 ha]
    have hω' := (omega_pow_two_pow hω a).2 ha
    rw [hb]
    fin_cases t <;> simp [f4Ev, q1Frob, f4Mul, hadd, hω']
    linear_combination h2

end Words

section Roots


theorem root_q1SigPos (side : Bool) {i j : Fin 3} (hij : i ≠ j) :
    ReeTag.F4.tag.rootCertificate.root (q1SigPos side i j) =
      if side then q1V • q1Sig i j else q1Sig i j := by
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [q1Sig_eq]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | (funext k; fin_cases k <;> decide +kernel)
  · simp only [↓reduceIte]
    rw [q1V_smul, q1Sig_eq]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | (funext k; fin_cases k <;> decide +kernel)

theorem root_q1TauPos_false (side : Bool) {i j : Fin 3} (hij : i ≠ j) :
    ReeTag.F4.tag.rootCertificate.root (q1TauPos false side i j) =
      if side then q1V • q1Tau 0 i j else q1Tau 0 i j := by
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [q1Tau, q1W_smul, q1Sig_eq]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | (funext k; fin_cases k <;> decide +kernel)
  · simp only [↓reduceIte]
    rw [q1V_smul, q1Tau, q1W_smul, q1Sig_eq]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | (funext k; fin_cases k <;> decide +kernel)

theorem root_q1TauPos_true (side : Bool) {i j : Fin 3} (hij : i ≠ j) :
    ReeTag.F4.tag.rootCertificate.root (q1TauPos true side i j) =
      if side then q1V • q1Tau 3 i j else q1Tau 3 i j := by
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [q1Tau, q1W_smul, q1Sig_eq]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | (funext k; fin_cases k <;> decide +kernel)
  · simp only [↓reduceIte]
    rw [q1V_smul, q1Tau, q1W_smul, q1Sig_eq]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | (funext k; fin_cases k <;> decide +kernel)

theorem root_q1TauPos (odd side : Bool) {i j : Fin 3} (hij : i ≠ j) :
    ReeTag.F4.tag.rootCertificate.root (q1TauPos odd side i j) =
      if side then q1V • q1Tau (if odd then 3 else 0) i j
      else q1Tau (if odd then 3 else 0) i j := by
  cases odd
  · exact root_q1TauPos_false side hij
  · exact root_q1TauPos_true side hij

end Roots

section Psi

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

variable (L) in
@[expose] def q1SideAut (side : Bool) : MulAut (ModGL ReeTag.F4.tag L) :=
  if side then MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V) else 1

omit [CharP L 2] in
theorem q1SideAut_false (g : ModGL ReeTag.F4.tag L) : q1SideAut L false g = g :=
  rfl

omit [CharP L 2] in
theorem q1SideAut_true (g : ModGL ReeTag.F4.tag L) :
    q1SideAut L true g = canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * g *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V)⁻¹ :=
  rfl

theorem q1SideAut_pinnedX (side : Bool) {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : IsRoot ReeTag.F4.tag γ) (t : L) :
    q1SideAut L side (pinnedX ReeTag.F4.tag L γ t) =
      pinnedX ReeTag.F4.tag L (if side then q1V • γ else γ) t := by
  cases side
  · rfl
  · exact canonicalRep_conj_pinnedX q1V hγ t

theorem q1SideAut_q1Rho (side : Bool) {ω : L} (hω : ω ^ 2 + ω + 1 = 0)
    (l : List (Fin 3 × Fin 3 × Fin 4)) (hl : ∀ x ∈ l, x.1 ≠ x.2.1) :
    q1SideAut L side (q1Rho L (q1TvProd ω l)) = omegaPinned ReeTag.F4.tag L
      (l.map fun x => (q1SigPos side x.1 x.2.1, q1Coef x.2.2, q1Pow x.2.2)) ω := by
  induction l with
  | nil => rw [List.map_nil, omegaPinned_nil, q1TvProd, List.map_nil, List.prod_nil, map_one, map_one]
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    rw [q1TvProd_cons, map_mul, map_mul, ih fun y hy => hl y (List.mem_cons_of_mem _ hy),
      List.map_cons, omegaPinned_cons]
    congr 1
    simp only [q1Tv, ne_eq, hx, not_false_eq_true, ↓reduceDIte]
    rw [q1Rho_transvection _ _ hx, q1SideAut_pinnedX side (isRoot_q1Sig hx),
      root_q1SigPos side hx, f4Ev_eq_coef hω]

theorem q1SideAut_q1PsiRho (hF : IsReeFrob a F) (odd : Bool)
    (hpar : q1Par a = if odd then 3 else 0) (side : Bool) {ω : L} (hω : ω ^ 2 + ω + 1 = 0)
    (hfr : ∀ t : Fin 4, f4Ev ω t ^ 2 ^ a = f4Ev ω (q1Frob odd t))
    (l : List (Fin 3 × Fin 3 × Fin 4)) (hl : ∀ x ∈ l, x.1 ≠ x.2.1) :
    q1SideAut L side (q1PsiRho F a (q1TvProd ω l)) = omegaPinned ReeTag.F4.tag L
      (l.map fun x => (q1TauPos odd side x.1 x.2.1, q1Coef (q1Frob odd x.2.2),
        q1Pow (q1Frob odd x.2.2))) ω := by
  induction l with
  | nil => rw [List.map_nil, omegaPinned_nil, q1TvProd, List.map_nil, List.prod_nil, map_one, map_one]
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    rw [q1TvProd_cons, map_mul, map_mul, ih fun y hy => hl y (List.mem_cons_of_mem _ hy),
      List.map_cons, omegaPinned_cons]
    congr 1
    simp only [q1Tv, ne_eq, hx, not_false_eq_true, ↓reduceDIte]
    rw [q1PsiRho_transvection hF hx, q1SideAut_pinnedX side (isRoot_q1Tau hx), hpar,
      root_q1TauPos odd side hx, hfr, f4Ev_eq_coef hω]

theorem q1SideAut_q1Psi0 (hF : IsReeFrob a F) (odd : Bool)
    (hpar : q1Par a = if odd then 3 else 0) (side : Bool) {ω : L} (hω : ω ^ 2 + ω + 1 = 0)
    (hfr : ∀ t : Fin 4, f4Ev ω t ^ 2 ^ a = f4Ev ω (q1Frob odd t))
    (l : List (Fin 3 × Fin 3 × Fin 4)) (hl : ∀ x ∈ l, x.1 ≠ x.2.1) :
    q1SideAut L side (q1Psi0 hF (q1TvProd ω l)) =
      omegaPinned ReeTag.F4.tag L (q1DecWord odd side l) ω := by
  rw [q1Psi0_apply, map_mul, q1SideAut_q1Rho side hω l hl,
    q1SideAut_q1PsiRho hF odd hpar side hω hfr l hl, q1DecWord, omegaPinned_append]

end Psi

section CWord

theorem omegaPinned_reverse {τ : Tag}
    {R : Type*} [CommRing R] [CharP R 2] (l : List (ℕ × ℤ × ℕ)) (s : R) :
    omegaPinned τ R l.reverse s = (omegaPinned τ R l s)⁻¹ := by
  induction l with
  | nil => rw [List.reverse_nil, omegaPinned_nil, inv_one]
  | cons x l ih =>
    rw [List.reverse_cons, omegaPinned_append, ih, omegaPinned_cons R x l s, _root_.mul_inv_rev,
      omegaPinned_cons R x [] s, omegaPinned_nil, mul_one, pinnedX_neg, CharTwo.neg_eq]

theorem omegaPinned_flatMap {τ : Tag}
    {R : Type*} [CommRing R] {β : Type*} (l : List β) (f : β → List (ℕ × ℤ × ℕ)) (s : R) :
    omegaPinned τ R (l.flatMap f) s = (l.map fun x => omegaPinned τ R (f x) s).prod := by
  induction l with
  | nil => rw [List.flatMap_nil, omegaPinned_nil, List.map_nil, List.prod_nil]
  | cons x l ih => rw [List.flatMap_cons, omegaPinned_append, ih, List.map_cons, List.prod_cons]

theorem q1_prod_map_conj {G : Type*} [Group G] {β : Type*} (l : List β) (f : β → G) (c : G) :
    (l.map fun x => c * f x * c⁻¹).prod = c * (l.map f).prod * c⁻¹ := by
  have h := map_list_prod (MulAut.conj c).toMonoidHom (l.map f)
  rw [List.map_map] at h
  exact h.symm

variable {L : Type} [Field L] [CharP L 2]

theorem omegaPinned_q1CWord (ω : L) : omegaPinned ReeTag.F4.tag L q1CWord ω = q1C ω := by
  have r4 : ReeTag.F4.tag.rootCertificate.root 4 = -Pi.single 0 1 := by
    funext k; fin_cases k <;> decide +kernel
  have r0 : ReeTag.F4.tag.rootCertificate.root 0 = Pi.single 0 1 := by
    funext k; fin_cases k <;> decide +kernel
  have r11 : ReeTag.F4.tag.rootCertificate.root 11 = -Pi.single 3 1 := by
    funext k; fin_cases k <;> decide +kernel
  have r3 : ReeTag.F4.tag.rootCertificate.root 3 = Pi.single 3 1 := by
    funext k; fin_cases k <;> decide +kernel
  have r38 : ReeTag.F4.tag.rootCertificate.root 38 = q1V • -Pi.single 0 1 := by
    rw [q1V_smul]; funext k; fin_cases k <;> decide +kernel
  have r35 : ReeTag.F4.tag.rootCertificate.root 35 = q1V • Pi.single 0 1 := by
    rw [q1V_smul]; funext k; fin_cases k <;> decide +kernel
  have r41 : ReeTag.F4.tag.rootCertificate.root 41 = q1V • -Pi.single 3 1 := by
    rw [q1V_smul]; funext k; fin_cases k <;> decide +kernel
  have r36 : ReeTag.F4.tag.rootCertificate.root 36 = q1V • Pi.single 3 1 := by
    rw [q1V_smul]; funext k; fin_cases k <;> decide +kernel
  simp only [q1CWord, omegaPinned_cons, omegaPinned_nil, r4, r0, r11, r3, r38, r35, r41, r36,
    Int.cast_one, one_mul, pow_zero, pow_one, mul_one]
  rw [q1C, q1CA, q1CL_eq, q1A, q1A]
  simp only [mul_assoc]

end CWord

section Gamma

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2]

theorem q1_theta_letters (D : ReeFrameData K L a) {ω : L}
    (hω : ω ^ 2 + ω + 1 = 0) (odd : Bool) (hpar : q1Par a = if odd then 3 else 0)
    (hfr : ∀ t : Fin 4, f4Ev ω t ^ 2 ^ a = f4Ev ω (q1Frob odd t)) {G₀ : Type*} [Group G₀]
    (Ψ : G₀ →* ReeTag.F4.reeGamma K a) (j : G₀ →* SL(3, L))
    (hΨ : ∀ x, thetaGamma L a (Ψ x) = q1C ω * q1Psi0 D.isFrob (j x) * (q1C ω)⁻¹)
    (u : Fin 9 → G₀) (hu : ∀ k, j (u k) = q1TvProd ω (q1LetterDec k))
    (g : ReeTag.F4.reeGamma K a)
    (hg : thetaGamma L a g =
      q1C ω * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1C ω)⁻¹)
    (tgt : Bool) :
    thetaGamma L a ((q1Letters tgt).map fun x =>
        if x.1 then g * Ψ (u x.2) * g⁻¹ else Ψ (u x.2)).prod =
      omegaPinned ReeTag.F4.tag L (q1Target tgt) ω := by
  have hfac : ∀ x : Bool × Fin 9,
      thetaGamma L a (if x.1 then g * Ψ (u x.2) * g⁻¹ else Ψ (u x.2)) =
        q1C ω * omegaPinned ReeTag.F4.tag L (q1LetterWord odd x.1 x.2) ω * (q1C ω)⁻¹ := by
    rintro ⟨side, k⟩
    have hk := q1SideAut_q1Psi0 D.isFrob odd hpar side hω hfr (q1LetterDec k)
      (q1Letter_checks k).2.2.2
    rw [← hu k] at hk
    rw [q1LetterWord, ← hk]
    cases side
    · simp only [Bool.false_eq_true, ↓reduceIte, q1SideAut_false, hΨ]
    · simp only [↓reduceIte, q1SideAut_true, map_mul, map_inv, hΨ, hg]
      group
  have hcheck : omegaCheck ReeTag.F4.tag (q1Full odd tgt) (q1Target tgt) = true := by
    obtain ⟨h1, h2, h3, h4⟩ := (Certificates.certificate14947 :
      omegaCheck Tag.F4 (q1Full false false) (q1Target false) = true ∧ _)
    cases odd <;> cases tgt
    exacts [h1, h3, h2, h4]
  rw [map_list_prod, List.map_map,
    List.map_congr_left fun x _ => (show (thetaGamma L a ∘ fun x : Bool × Fin 9 =>
      if x.1 then g * Ψ (u x.2) * g⁻¹ else Ψ (u x.2)) x = _ from hfac x),
    q1_prod_map_conj, ← omegaPinned_flatMap, ← omegaPinned_q1CWord, ← omegaPinned_reverse,
    ← omegaPinned_append, ← omegaPinned_append]
  exact omegaPinned_eq_of_omegaCheck hcheck L CharTwo.two_eq_zero ω hω

omit [Finite K] [CharP L 2] in
theorem baseChangeGL_weylTwo (ω : L) :
    baseChangeGL (algebraMap K L) (LargeReeInvolution.weylTwo K) =
      omegaPinned ReeTag.F4.tag L (q1Target false) ω := by
  have : CharP K 2 := (inferInstance : CharP K ReeTag.F4.prime)
  have r1 : ReeTag.F4.tag.rootCertificate.root 1 = Pi.single 1 1 := by
    funext k; fin_cases k <;> decide +kernel
  have r6 : ReeTag.F4.tag.rootCertificate.root 6 = -Pi.single 1 1 := by
    funext k; fin_cases k <;> decide +kernel
  have r2 : ReeTag.F4.tag.rootCertificate.root 2 = Pi.single 2 1 := by
    funext k; fin_cases k <;> decide +kernel
  have r9 : ReeTag.F4.tag.rootCertificate.root 9 = -Pi.single 2 1 := by
    funext k; fin_cases k <;> decide +kernel
  have hw : ReeTag.F4.fixedOrbitElement ⟨1, by decide⟩ =
      (coxeterSystem ReeTag.F4.tag).simple 1 * ((coxeterSystem ReeTag.F4.tag).simple 2 *
        ((coxeterSystem ReeTag.F4.tag).simple 1 * (coxeterSystem ReeTag.F4.tag).simple 2)) := by
    rw [ReeTag.fixedOrbitElement, show ReeTag.F4.fixedOrbitWord ⟨1, by decide⟩ = [1, 2, 1, 2] from
      rfl, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton]
  rw [LargeReeInvolution.weylTwo, hw, CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo, canonicalRep_simple_eq_pinnedX,
    canonicalRep_simple_eq_pinnedX]
  simp only [q1Target, omegaPinned_cons, omegaPinned_nil, r1, r6, r2, r9, Int.cast_one, pow_zero,
    mul_one, map_mul, baseChangeGL_pinnedX, map_one, mul_assoc]

omit [Finite K] [CharP K ReeTag.F4.prime] [CharP L 2] in
theorem baseChangeGL_sylowB_one_zero (ω : L) :
    baseChangeGL (algebraMap K L) (LargeReeInvolution.sylowB a K 1 0) =
      omegaPinned ReeTag.F4.tag L (q1Target true) ω := by
  have r2 : ReeTag.F4.tag.rootCertificate.root 2 =
      CFSG.LieType.Chevalley.RootOps.orbitCertRoot ReeTag.F4.tag 25 := by
    funext k; fin_cases k <;> decide +kernel
  have r1 : ReeTag.F4.tag.rootCertificate.root 1 =
      CFSG.LieType.Chevalley.RootOps.orbitCertRoot ReeTag.F4.tag 27 := by
    funext k; fin_cases k <;> decide +kernel
  have r7 : ReeTag.F4.tag.rootCertificate.root 7 =
      CFSG.LieType.Chevalley.RootOps.orbitCertRoot ReeTag.F4.tag 30 := by
    funext k; fin_cases k <;> decide +kernel
  have hσ1 : ReeTag.largeReeSigma a (1 : K) = 1 := one_pow _
  have hσ0 : ReeTag.largeReeSigma a (0 : K) = 0 := zero_pow (by positivity)
  simp only [LargeReeInvolution.sylowB, LargeReeInvolution.sylowX, hσ1, hσ0, one_pow,
    zero_add, pinnedX_zero, mul_one, map_mul, baseChangeGL_pinnedX, map_one, q1Target,
    omegaPinned_cons, omegaPinned_nil, r2, r1, r7, Int.cast_one, pow_zero, mul_assoc]

theorem q1_letters_eq (D : ReeFrameData K L a) {ω : L}
    (hω : ω ^ 2 + ω + 1 = 0) (odd : Bool) (hpar : q1Par a = if odd then 3 else 0)
    (hfr : ∀ t : Fin 4, f4Ev ω t ^ 2 ^ a = f4Ev ω (q1Frob odd t)) {G₀ : Type*} [Group G₀]
    (Ψ : G₀ →* ReeTag.F4.reeGamma K a) (j : G₀ →* SL(3, L))
    (hΨ : ∀ x, thetaGamma L a (Ψ x) = q1C ω * q1Psi0 D.isFrob (j x) * (q1C ω)⁻¹)
    (u : Fin 9 → G₀) (hu : ∀ k, j (u k) = q1TvProd ω (q1LetterDec k))
    (g : ReeTag.F4.reeGamma K a)
    (hg : thetaGamma L a g =
      q1C ω * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1C ω)⁻¹)
    (tgt : Bool) :
    ((((q1Letters tgt).map fun x => if x.1 then g * Ψ (u x.2) * g⁻¹ else Ψ (u x.2)).prod :
        ReeTag.F4.reeGamma K a) : ModGL ReeTag.F4.tag K) =
      if tgt then LargeReeInvolution.sylowB a K 1 0 else LargeReeInvolution.weylTwo K := by
  apply baseChangeGL_injective (algebraMap K L)
  rw [← thetaGamma_apply, q1_theta_letters D hω odd hpar hfr Ψ j hΨ u hu g hg tgt]
  cases tgt
  · exact (baseChangeGL_weylTwo ω).symm
  · exact (baseChangeGL_sylowB_one_zero ω).symm

end Gamma

end CFSG.RankThree.PartOne.SEITZQ1

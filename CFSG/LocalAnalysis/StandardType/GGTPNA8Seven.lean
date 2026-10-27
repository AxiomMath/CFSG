module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.StarFour.Shape
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.UnitaryWeightGram
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private noncomputable def tpa8_slGL :
    Matrix.SpecialLinearGroup (Fin 9) (ZMod 2) ≃* Matrix.GeneralLinearGroup (Fin 9) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    (toGL_nine_bijective_of_card_two (K := ZMod 2) (Nat.card_zmod 2))

private noncomputable def tpa8_psi :=
  (Matrix.SpecialLinearGroup.toLin'_equiv (R := ZMod 2) (n := Fin 9)).symm.trans tpa8_slGL

private theorem tpa8_centralizer_zpowers {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer (↑(Subgroup.zpowers x) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem tpa8_hasLabel_of_sl {E : Type} [Field E] [Finite E] {m f : ℕ}
    (hm : 3 ≤ m) (hf : 1 ≤ f) (hE : Nat.card E = 2 ^ f)
    {G : Type} [Group G] {J : Subgroup G}
    (e : Matrix.SpecialLinearGroup (Fin m) E ≃* J) :
    GGHasLabel ⟨.A, m - 1, f⟩ (J ⧸ Subgroup.center J) := by
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin m) E ≃* (J ⧸ Subgroup.center J) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hmodel : CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) .PSL m 2 f := by
    refine ⟨⟨Nat.prime_two, hf, by omega, ?_, ?_⟩, E, inferInstance, inferInstance, hE, ⟨?_⟩⟩
    · intro h
      have h1 : m = 2 := (Prod.mk.inj h).1
      omega
    · intro h
      have h1 : m = 2 := (Prod.mk.inj h).1
      omega
    · exact e'.symm.trans (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)
  have h1 : m - 1 + 1 = m := by omega
  exact ggHasLabel_typeA (n := m - 1) (f := f) (by rw [h1]; exact hmodel)

private theorem tpa8_seven_dvd_card_sl {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 2 ≤ n) (hn9 : n ≤ 9) (hq : Fintype.card K = 2 ∨ Fintype.card K = 8)
    (hgood : 3 ≤ n ∨ Fintype.card K = 8) :
    7 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) K) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [Matrix.card_SL_field n]
  rcases hq with hq | hq
  · rw [hq, show (2 - 1) = 1 by norm_num, Nat.div_one]
    have hn3 : 3 ≤ n := by
      rcases hgood with h | h
      · exact h
      · rw [hq] at h; norm_num at h
    interval_cases n <;> decide
  · rw [hq]
    interval_cases n <;> decide

private theorem tpa8_block_finrank_general {P : Type} [CommGroup P] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : P →* (V ≃ₗ[ZMod 2] V)}
    (fr : StarFour.SemiFrame (ZMod 2) ρ) (hρ7 : ∀ p : P, ρ p ^ 7 = 1)
    (j : Fin fr.r) (hm : fr.m j ≠ 0) :
    Module.finrank (ZMod 2) (fr.E j) = 1 ∨ Module.finrank (ZMod 2) (fr.E j) = 3 := by
  let E := fr.E j
  haveI : Finite E := fr.instFinite j
  letI : Fintype E := Fintype.ofFinite E
  haveI : CharP E 2 := charP_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective (ZMod 2) E) 2
  obtain ⟨a⟩ : Nonempty (Fin (fr.m j)) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hm)
  let b : Fin (fr.m j) → E := fun _ => 1
  let v : V := fr.Φ.symm (Pi.single j b)
  have hv : fr.Φ v j ≠ 0 := by
    have h1 : fr.Φ v j = b := by
      simp only [v, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
    rw [h1]
    intro h
    exact one_ne_zero (congrFun h a)
  have hva : (fr.Φ v j) a = 1 := by
    have h1 : fr.Φ v j = b := by
      simp only [v, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
    exact congrFun h1 a
  have hχ7 : ∀ p : P, (fr.χ j p : E) ^ 7 = 1 := by
    intro p
    have hρ : ρ (p ^ 7) = 1 := by rw [map_pow, hρ7 p]
    have hact := fr.act (p ^ 7) v j
    rw [hρ] at hact
    have hact' : fr.Φ v j = (fr.χ j (p ^ 7) : E) • fr.Φ v j := by
      simpa using hact
    have hval : (fr.Φ v j) a = (fr.χ j (p ^ 7) : E) • (fr.Φ v j) a := by
      have := congrFun hact' a
      simpa only [Pi.smul_apply] using this
    rw [hva, smul_eq_mul, mul_one] at hval
    have h1 : (fr.χ j (p ^ 7) : E) = 1 := hval.symm
    rw [map_pow, Units.val_pow_eq_pow_val] at h1
    exact h1
  have h8 : ∀ x : E, x ^ 8 = x := by
    intro x
    have hx : x ∈ Algebra.adjoin (ZMod 2) (Set.range (fun p : P => (fr.χ j p : E))) := by
      rw [fr.gen j]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem s hs =>
        obtain ⟨p, rfl⟩ := hs
        have hs7 : (fr.χ j p : E) ^ 7 = 1 := hχ7 p
        rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, hs7, one_mul, pow_one]
    | algebraMap r =>
        rw [← map_pow]
        congr 1
        revert r
        decide
    | add x y hx hy ihx ihy =>
        have h2 : (x + y) ^ 8 = x ^ 8 + y ^ 8 := by
          rw [show (8 : ℕ) = 2 ^ 3 by norm_num, add_pow_char_pow]
        rw [h2, ihx, ihy]
    | mul x y hx hy ihx ihy =>
        rw [mul_pow, ihx, ihy]
  let σ : E ≃+* E := RingEquiv.ofBijective (frobenius E 2)
    ⟨(frobenius E 2).injective,
      (Finite.injective_iff_surjective.mp (frobenius E 2).injective)⟩
  have hσ : ∀ x, σ x = x ^ 2 := fun x => by
    change frobenius E 2 x = x ^ 2
    rw [frobenius_def]
  have hσpow : ∀ n : ℕ, ∀ x : E, (σ ^ n) x = x ^ 2 ^ n := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ, show (σ ^ n * σ) x = (σ ^ n) (σ x) from rfl, ih, hσ, ← pow_mul]
        congr 1
        rw [mul_comm, ← pow_succ]
  have hσ3 : σ ^ 3 = 1 := by
    ext x
    rw [hσpow 3 x, show (2 : ℕ) ^ 3 = 8 by norm_num, h8 x]
    rfl
  have hσd : σ ^ (Module.finrank (ZMod 2) E) = 1 := by
    ext x
    change (σ ^ Module.finrank (ZMod 2) E) x = x
    rw [hσpow (Module.finrank (ZMod 2) E) x]
    haveI : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    have hcard : Nat.card E = 2 ^ Module.finrank (ZMod 2) E := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod]
    letI : Fintype E := Fintype.ofFinite E
    have hpow : x ^ Nat.card E = x := by
      simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card x
    rw [← hcard]
    exact hpow
  have hσm : σ ^ (Nat.gcd 3 (Module.finrank (ZMod 2) E)) = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd ?_ ?_)
    · exact orderOf_dvd_iff_pow_eq_one.mpr hσ3
    · exact orderOf_dvd_iff_pow_eq_one.mpr hσd
  have h8m : ∀ x : E, x ^ 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E) = x := by
    intro x
    rw [← hσpow (Nat.gcd 3 (Module.finrank (ZMod 2) E)) x, hσm]
    rfl
  have hcardm : Nat.card E ≤ 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E) := by
    let p : Polynomial E :=
      Polynomial.X ^ (2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E)) - Polynomial.X
    have hne1 : 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E) ≠ 1 := by
      have h1 : 1 ≤ Nat.gcd 3 (Module.finrank (ZMod 2) E) :=
        Nat.gcd_pos_of_pos_right 3 (Module.finrank_pos (R := ZMod 2) (M := E))
      have h2 : 2 ≤ 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E) :=
              Nat.pow_le_pow_right (by norm_num) h1
      omega
    have hp : p ≠ 0 := by
      intro h
      have hc := congrArg
        (fun q : Polynomial E => q.coeff (2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E))) h
      simp only [p, Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_X,
        if_neg (show ¬ (1 = 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E)) by omega),
        Polynomial.coeff_zero] at hc
      norm_num at hc
    have hsub : (Finset.univ : Finset E).val ⊆ p.roots := by
      intro x _
      rw [Polynomial.mem_roots hp]
      simp only [Polynomial.IsRoot, p, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [h8m x, sub_self]
    have h1 : 1 ≤ Nat.gcd 3 (Module.finrank (ZMod 2) E) :=
      Nat.gcd_pos_of_pos_right 3 (Module.finrank_pos (R := ZMod 2) (M := E))
    have hpdeg : (Polynomial.X ^ (2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E)) -
        Polynomial.X : Polynomial E).natDegree ≤ 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E) := by
      calc _ ≤ max (Polynomial.X ^ (2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E))).natDegree
              Polynomial.X.natDegree := Polynomial.natDegree_sub_le _ _
        _ = 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E) := by
              rw [Polynomial.natDegree_X_pow (R := E), Polynomial.natDegree_X (R := E),
                max_eq_left (by
                  calc (1 : ℕ) = 2 ^ 0 := by norm_num
                    _ ≤ 2 ^ Nat.gcd 3 (Module.finrank (ZMod 2) E) :=
                        Nat.pow_le_pow_right (by norm_num) (by omega))]
    have h := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h
    exact h.trans hpdeg
  have hdle : Module.finrank (ZMod 2) E ≤ Nat.gcd 3 (Module.finrank (ZMod 2) E) := by
    haveI : Finite E := fr.instFinite j
    have hcard : Nat.card E = 2 ^ Module.finrank (ZMod 2) E := by
      haveI : Module.Finite (ZMod 2) E := Module.Finite.of_finite
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod]
    rw [hcard] at hcardm
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcardm
  have hdvd : Module.finrank (ZMod 2) E ∣ 3 := by
    haveI : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    have hpos : 0 < Module.finrank (ZMod 2) E := Module.finrank_pos
    have h2 : Nat.gcd 3 (Module.finrank (ZMod 2) E) = Module.finrank (ZMod 2) E :=
      le_antisymm (Nat.gcd_le_right 3 hpos) hdle
    rw [← h2]
    exact Nat.gcd_dvd_left 3 _
  rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd _ hdvd with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem tpa8_dim_sum_general {F : Type} [Field F] [Finite F] {P : Type} [CommGroup P]
    {V : Type} [AddCommGroup V] [Module F V] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : StarFour.SemiFrame F ρ) (hV : Nat.card V = Nat.card F ^ 9) :
    ∑ j : Fin fr.r, fr.m j * Module.finrank F (fr.E j) = 9 := by
  have h2 : Nat.card F ^ 9 = Nat.card F ^ (∑ j : Fin fr.r,
      fr.m j * Module.finrank F (fr.E j)) := by
    calc Nat.card F ^ 9
        = Nat.card V := hV.symm
      _ = Nat.card (∀ j : Fin fr.r, Fin (fr.m j) → fr.E j) :=
            Nat.card_congr fr.Φ.toEquiv
      _ = ∏ j : Fin fr.r, Nat.card (Fin (fr.m j) → fr.E j) := Nat.card_pi
      _ = ∏ j : Fin fr.r,
            Nat.card F ^ (fr.m j * Module.finrank F (fr.E j)) := by
            apply Finset.prod_congr rfl
            intro j _
            haveI : Module.Finite F (fr.E j) := Module.Finite.of_finite
            rw [Nat.card_fun, Module.natCard_eq_pow_finrank (K := F) (V := fr.E j), ← pow_mul]
            congr 1
            rw [Nat.card_fin, mul_comm]
      _ = Nat.card F ^ (∑ j : Fin fr.r,
            fr.m j * Module.finrank F (fr.E j)) := by
            rw [Finset.prod_pow_eq_pow_sum]
  exact (Nat.pow_right_injective (Nat.succ_le_of_lt (Finite.one_lt_card (α := F))) h2).symm

private theorem tpa8_slOnBlock_normal {F : Type} [Field F] {P : Type} [CommGroup P]
    {V : Type} [AddCommGroup V] [Module F V] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : StarFour.SemiFrame F ρ) (j : Fin fr.r) :
    ((fr.slOnBlock j).subgroupOf (StarFour.repCentSL ρ)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 : StarFour.SemiFrame.blockPiGL fr n ∈
      CFSG.RankThree.PartOne.KCLinComm.blockSL fr.E fr.m j :=
    (StarFour.SemiFrame.mem_slOnBlock_iff_mem_comap fr n j).mp hn
  have h2 : StarFour.SemiFrame.blockPiGL fr g * StarFour.SemiFrame.blockPiGL fr n *
      (StarFour.SemiFrame.blockPiGL fr g)⁻¹ ∈
      CFSG.RankThree.PartOne.KCLinComm.blockSL fr.E fr.m j :=
    CFSG.RankThree.PartOne.KCLinComm.conj_mem_blockSL j
      (StarFour.SemiFrame.blockPiGL fr g) h1
  refine (StarFour.SemiFrame.mem_slOnBlock_iff_mem_comap fr (g * n * g⁻¹) j).mpr ?_
  have h2' : StarFour.SemiFrame.blockPiGL fr (g * n * g⁻¹) =
      StarFour.SemiFrame.blockPiGL fr g * StarFour.SemiFrame.blockPiGL fr n *
        (StarFour.SemiFrame.blockPiGL fr g)⁻¹ := by
    simp only [map_mul, map_inv]
  rw [h2']
  exact h2

private theorem tpa8_slOnBlock_isComponentOf {F : Type} [Field F] [Finite F]
    {P : Type} [CommGroup P] {V : Type} [AddCommGroup V] [Module F V]
    {ρ : P →* (V ≃ₗ[F] V)} (fr : StarFour.SemiFrame F ρ) {j : Fin fr.r}
    (hj : fr.GoodAtBlock j) :
    IsComponentOf (fr.slOnBlock j) (StarFour.repCentSL ρ) :=
  ⟨StarFour.SemiFrame.slOnBlock_le_repCentSL fr j,
    ggIsSubnormal_of_normal (StarFour.SemiFrame.slOnBlock_le_repCentSL fr j)
      (tpa8_slOnBlock_normal fr j),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (StarFour.SemiFrame.isQuasisimple_slOnBlock fr hj)⟩

private theorem tpa8_slOnBlock_disjoint {F : Type} [Field F] {P : Type} [CommGroup P]
    {V : Type} [AddCommGroup V] [Module F V] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : StarFour.SemiFrame F ρ) {i j : Fin fr.r} (hji : j ≠ i)
    {g : SpecialLinearGroup F V} (hgj : g ∈ fr.slOnBlock j) (hgi : g ∈ fr.slOnBlock i) :
    g = 1 := by
  obtain ⟨B, hB⟩ := hgj
  obtain ⟨B', hB'⟩ := hgi
  have hBw : ∀ w, B w = w := by
    intro w
    obtain ⟨v, hv⟩ := StarFour.SemiFrame.exists_phi_eq fr j w
    have h1 : fr.Φ (g v) j = B w := by rw [hB v, Function.update_self, hv]
    have h2 : fr.Φ (g v) j = w := by
      rw [hB' v, Function.update_of_ne hji]
      exact hv
    rw [← h1, h2]
  have hB'w : ∀ w, B' w = w := by
    intro w
    obtain ⟨v, hv⟩ := StarFour.SemiFrame.exists_phi_eq fr i w
    have h1 : fr.Φ (g v) i = B' w := by rw [hB' v, Function.update_self, hv]
    have h2 : fr.Φ (g v) i = w := by
      rw [hB v, Function.update_of_ne (Ne.symm hji)]
      exact hv
    rw [← h1, h2]
  refine Subtype.ext (LinearEquiv.ext (fun v => ?_))
  apply fr.Φ.injective
  funext k
  by_cases hk : k = j
  · subst hk
    rw [hB v, Function.update_self, hBw]
    rfl
  · by_cases hk' : k = i
    · subst hk'
      rw [hB' v, Function.update_self, hB'w]
      rfl
    · rw [hB v, Function.update_of_ne hk]
      rfl

private theorem tpa8_frame_all_one {P : Type} [CommGroup P] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : P →* (V ≃ₗ[ZMod 2] V)}
    (fr : StarFour.SemiFrame (ZMod 2) ρ)
    (h1 : ∀ j, fr.m j ≠ 0 → Module.finrank (ZMod 2) (fr.E j) = 1) :
    ∀ p, ρ p = 1 := by
  intro p
  ext v
  apply fr.Φ.injective
  funext j
  rw [fr.act p v j]
  by_cases hj : fr.m j = 0
  · haveI : IsEmpty (Fin (fr.m j)) := by rw [hj]; infer_instance
    exact Subsingleton.elim _ _
  · haveI : Module.Finite (ZMod 2) (fr.E j) := Module.Finite.of_finite
    have hcard : Nat.card (fr.E j) = 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fr.E j), h1 j hj, Nat.card_zmod]
      norm_num
    have hunits : Nat.card (fr.E j)ˣ = 1 := by
      simp [Nat.card_units, hcard]
    haveI : Subsingleton (fr.E j)ˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
    have hχ : fr.χ j p = 1 := Subsingleton.elim _ _
    rw [hχ]
    simp

private theorem tpa8_hcase_arith {m f : ℕ} {E : Type} [Field E] [Fintype E]
    (hm2 : 2 ≤ m) (hmle : m ≤ 6) (hmf : m * f ≤ 9) (hf : f = 1 ∨ f = 3)
    (hE : Fintype.card E = 2 ^ f)
    (hdiv : 7 ^ 2 * (Fintype.card E - 1) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin m) E)) :
    (m = 6 ∧ f = 1) ∨ (m = 3 ∧ f = 3) := by
  rw [Matrix.card_GL_field] at hdiv
  rw [hE] at hdiv
  rcases hf with rfl | rfl
  · interval_cases m
    all_goals simp [Fin.prod_univ_succ] at hdiv ⊢
    all_goals norm_num at hdiv ⊢
  · have hm3 : m ≤ 3 := by omega
    interval_cases m
    all_goals simp [Fin.prod_univ_succ] at hdiv ⊢
    all_goals norm_num at hdiv ⊢

private theorem tpa8_center_block_mem_centralizer {F : Type} [Field F] {P : Type} [CommGroup P]
    {V : Type} [AddCommGroup V] [Module F V] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : StarFour.SemiFrame F ρ) (i : Fin fr.r)
    {h : StarFour.repCentSL ρ}
    (hc : StarFour.SemiFrame.blockPiGL fr h i ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i))) :
    h.1 ∈ Subgroup.centralizer (fr.slOnBlock i : Set (SpecialLinearGroup F V)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hgle := StarFour.SemiFrame.slOnBlock_le_repCentSL fr i hg
  obtain ⟨B, hB⟩ := hg
  have hBlin_eq : StarFour.SemiFrame.blockEquiv fr ⟨g, hgle⟩ i =
      SpecialLinearGroup.toLinearEquiv B := by
    apply LinearEquiv.ext
    intro x
    change StarFour.SemiFrame.blockLin fr ⟨g, hgle⟩ i x =
      (SpecialLinearGroup.toLinearEquiv B) x
    obtain ⟨v, rfl⟩ := StarFour.SemiFrame.exists_phi_eq fr i x
    rw [← StarFour.SemiFrame.blockLin_spec fr ⟨g, hgle⟩ i v]
    exact (congrFun (hB v) i).trans (Function.update_self _ _ _)
  have hcomm : StarFour.SemiFrame.blockEquiv fr h i *
        StarFour.SemiFrame.blockEquiv fr ⟨g, hgle⟩ i =
      StarFour.SemiFrame.blockEquiv fr ⟨g, hgle⟩ i *
        StarFour.SemiFrame.blockEquiv fr h i := by
    have hcenter := Subgroup.mem_center_iff.mp hc
      (StarFour.SemiFrame.blockPiGL fr ⟨g, hgle⟩ i)
    rw [show StarFour.SemiFrame.blockPiGL fr h i =
        StarFour.SemiFrame.linEquivToGL (StarFour.SemiFrame.blockEquiv fr h i) from rfl,
      show StarFour.SemiFrame.blockPiGL fr ⟨g, hgle⟩ i =
        StarFour.SemiFrame.linEquivToGL (StarFour.SemiFrame.blockEquiv fr ⟨g, hgle⟩ i)
        from rfl] at hcenter
    rw [← map_mul, ← map_mul] at hcenter
    exact ((StarFour.SemiFrame.linEquivToGL (E := fr.E i) (n := fr.m i)).injective hcenter).symm
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply fr.Φ.injective
  funext k
  have h1 : ((h.1 * g : SpecialLinearGroup F V) : V ≃ₗ[F] V) v = h.1 (g v) := by
    rw [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
  have h2 : ((g * h.1 : SpecialLinearGroup F V) : V ≃ₗ[F] V) v = g (h.1 v) := by
    rw [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
  rw [h1, h2]
  by_cases hk : k = i
  · subst hk
    rw [StarFour.SemiFrame.blockLin_spec fr h k (g v), hB v, Function.update_self,
      hB (h.1 v), Function.update_self, StarFour.SemiFrame.blockLin_spec fr h k v]
    have hc' := congrFun (congrArg (fun (u : (Fin (fr.m k) → fr.E k) ≃ₗ[fr.E k]
      (Fin (fr.m k) → fr.E k)) => u (fr.Φ v k)) hcomm)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hc'
    rw [hBlin_eq] at hc'
    exact funext (fun a => (hc' a).symm)
  · rw [hB (h.1 v), Function.update_of_ne hk, StarFour.SemiFrame.blockLin_spec fr h k v,
      StarFour.SemiFrame.blockLin_spec fr h k (g v), hB v, Function.update_of_ne hk]

private theorem tpa8_blockLin_eta {F : Type} [Field F] {P : Type} [CommGroup P]
    {V : Type} [AddCommGroup V] [Module F V] {η : P →* SpecialLinearGroup F V}
    (fr : StarFour.SemiFrame F (StarFour.groupRep η)) (p : P) (i : Fin fr.r)
    (h : η p ∈ StarFour.repCentSL (StarFour.groupRep η)) :
    StarFour.SemiFrame.blockLin fr ⟨η p, h⟩ i = (fr.χ i p : fr.E i) • 1 := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, hv⟩ := StarFour.SemiFrame.exists_phi_eq fr i x
  rw [← hv, ← StarFour.SemiFrame.blockLin_spec fr ⟨η p, h⟩ i v]
  change fr.Φ (StarFour.groupRep η p v) i = (fr.χ i p : fr.E i) • fr.Φ v i
  rw [fr.act p v i]

theorem ggTablePA8SevenKnown_holds : GGTablePA8SevenKnown := by
  intro x E J hxord hxE hEab hEcard hJcomp hEnorm hEinter hT8
  let ψh := tpa8_psi.toMonoidHom
  let D : Subgroup (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)) := Subgroup.zpowers x
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    show a * b = b * a
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have hDodd : (Nat.card D : ZMod 2) ≠ 0 := by
    show (Nat.card (Subgroup.zpowers x) : ZMod 2) ≠ 0
    rw [Nat.card_zpowers, hxord]
    decide
  have hJ' : IsComponentOf J (ψh.range ⊓ Subgroup.centralizer (D :
      Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) := by
    have hrange : ψh.range = ⊤ := MonoidHom.range_eq_top.mpr tpa8_psi.surjective
    rw [hrange, top_inf_eq]
    show IsComponentOf J (Subgroup.centralizer
      (↑(Subgroup.zpowers x) : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))))
    rw [tpa8_centralizer_zpowers]
    exact hJcomp
  obtain ⟨P, instP, η, fr, i, hη, hgood, hJψ⟩ :=
    StarFour.exists_frame_of_component ψh tpa8_psi.injective ⊤ D J
      (tpa8_psi.symm.toMonoidHom.comp (⊤ : Subgroup
        (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))).subtype)
      (by
        intro b u
        show (b : Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)) * tpa8_psi u *
            (b : Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))⁻¹ =
          tpa8_psi (tpa8_psi.symm b * u * (tpa8_psi.symm b)⁻¹)
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply])
      le_top hDab hDodd hJ'
  letI : CommGroup P := instP
  have hx7 : x ^ 7 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxord] at this
  have hsymm7 : (tpa8_psi.symm x) ^ 7 = 1 := by
    rw [← map_pow, hx7, map_one]
  have hrange : η.range = Subgroup.zpowers (tpa8_psi.symm x) := by
    rw [hη]
    ext q
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : (b : (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))).1 ∈
          Subgroup.zpowers x := hb
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb'
      show tpa8_psi.symm (b : (⊤ : Subgroup
        (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))).1 ∈
          Subgroup.zpowers (tpa8_psi.symm x)
      rw [← hn, map_zpow]
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
    · intro hq
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hq
      refine Subgroup.mem_map.mpr ⟨⟨x ^ n, Subgroup.mem_top _⟩, ?_, ?_⟩
      · exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
      · show tpa8_psi.symm (x ^ n) = q
        rw [map_zpow, hn]
  have hηexp : ∀ q ∈ η.range, q ^ 7 = 1 := by
    intro q hq
    rw [hrange] at hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [zpow_natCast, hsymm7]
  have hρ7 : ∀ p : P, StarFour.groupRep η p ^ 7 = 1 := by
    intro p
    have hp : (η p) ^ 7 = 1 := hηexp (η p) (MonoidHom.mem_range.mpr ⟨p, rfl⟩)
    change (SpecialLinearGroup.toLinearEquiv (η p)) ^ 7 = 1
    rw [← map_pow, hp, map_one]
  have hfield : ∀ j : Fin fr.r, fr.m j ≠ 0 →
      (Module.finrank (ZMod 2) (fr.E j) = 1 ∨
        Module.finrank (ZMod 2) (fr.E j) = 3) :=
    fun j hm => tpa8_block_finrank_general fr hρ7 j hm
  have hdim : ∑ j : Fin fr.r, fr.m j * Module.finrank (ZMod 2) (fr.E j) = 9 :=
    tpa8_dim_sum_general fr (by rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod])
  have hgood7 : ∀ j : Fin fr.r, fr.GoodAtBlock j → 7 ∣ Nat.card (fr.slOnBlock j) := by
    intro j hj
    have hm : fr.m j ≠ 0 := by have := hj.1; omega
    have hf := hfield j hm
    haveI : Fintype (fr.E j) := Fintype.ofFinite (fr.E j)
    have hcardE : Nat.card (fr.E j) = 2 ^ Module.finrank (ZMod 2) (fr.E j) := by
      haveI : Module.Finite (ZMod 2) (fr.E j) := Module.Finite.of_finite
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fr.E j), Nat.card_zmod]
    have hq : Fintype.card (fr.E j) = 2 ∨ Fintype.card (fr.E j) = 8 := by
      rw [← Nat.card_eq_fintype_card, hcardE]
      rcases hf with hf | hf <;> rw [hf] <;> norm_num
    have hgood' : 3 ≤ fr.m j ∨ Fintype.card (fr.E j) = 8 := by
      rw [← Nat.card_eq_fintype_card]
      rcases hj.2 with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        rw [hcardE] at h ⊢
        rcases hf with hf | hf
        · rw [hf] at h ⊢
          norm_num at h
        · rw [hf] at h ⊢
          norm_num
    have hm9 : fr.m j ≤ 9 := by
      have h1 : fr.m j * Module.finrank (ZMod 2) (fr.E j) ≤
          ∑ k : Fin fr.r, fr.m k * Module.finrank (ZMod 2) (fr.E k) :=
        Finset.single_le_sum (f := fun k => fr.m k * Module.finrank (ZMod 2) (fr.E k))
          (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [hdim] at h1
      have h2 : 1 ≤ Module.finrank (ZMod 2) (fr.E j) := by
        haveI : Module.Finite (ZMod 2) (fr.E j) := Module.Finite.of_finite
        exact Module.finrank_pos
      have : fr.m j * 1 ≤ fr.m j * Module.finrank (ZMod 2) (fr.E j) :=
        Nat.mul_le_mul_left _ h2
      omega
    have hcard : Nat.card (fr.slOnBlock j) =
        Nat.card (Matrix.SpecialLinearGroup (Fin (fr.m j)) (fr.E j)) := by
      rw [← Nat.card_congr (StarFour.SemiFrame.blockMulEquiv fr j).toEquiv,
        ← Nat.card_congr (Matrix.SpecialLinearGroup.toLin'_equiv (R := fr.E j)
          (n := Fin (fr.m j))).toEquiv]
    rw [hcard]
    exact tpa8_seven_dvd_card_sl (fr.m j) hj.1 hm9 hq hgood'
  have huniq : ∀ j : Fin fr.r, fr.GoodAtBlock j → j = i := by
    intro j hj
    by_contra hji
    have hcomp := tpa8_slOnBlock_isComponentOf fr hj
    have hset : Set.image (fun b : Matrix.GeneralLinearGroup (Fin 9) (ZMod 2) =>
          tpa8_psi.symm b) (D : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) =
        η.range := by
      rw [hη]
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, Subgroup.mem_top b⟩, hb, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b, hb, rfl⟩
    have hinf := StarFour.inf_centralizer_eq_map_centralizer ψh tpa8_psi.injective
      (D : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))
      (fun b => tpa8_psi.symm b)
      (by
        intro b hb u
        show b * tpa8_psi u * b⁻¹ =
          tpa8_psi (tpa8_psi.symm b * u * (tpa8_psi.symm b)⁻¹)
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply])
    rw [hset] at hinf
    rw [← StarFour.repCentSL_groupRep η] at hinf
    have hcompψ := CFSG.StandardType.isComponentOf_map_of_injective
      ψh tpa8_psi.injective hcomp
    rw [← hinf] at hcompψ
    rw [MonoidHom.range_eq_top.mpr tpa8_psi.surjective, top_inf_eq] at hcompψ
    rw [tpa8_centralizer_zpowers] at hcompψ
    have h7 : 7 ∣ Nat.card (Subgroup.map ψh (fr.slOnBlock j)) := by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective (fr.slOnBlock j) ψh
        tpa8_psi.injective).toEquiv]
      exact hgood7 j hj
    have hJj : Subgroup.map ψh (fr.slOnBlock j) = J := hT8 _ hcompψ h7
    have heq : fr.slOnBlock j = fr.slOnBlock i := by
      refine le_antisymm ?_ ?_
      · exact (Subgroup.map_le_map_iff_of_injective tpa8_psi.injective).mp
          (le_of_eq (hJj.trans hJψ))
      · exact (Subgroup.map_le_map_iff_of_injective tpa8_psi.injective).mp
          (le_of_eq (hJj.trans hJψ).symm)
    haveI : Nontrivial ↥(fr.slOnBlock j) :=
      CFSG.LocalCores.isQuasisimple_nontrivial (StarFour.SemiFrame.isQuasisimple_slOnBlock fr hj)
    obtain ⟨g, hg1⟩ := exists_ne (1 : ↥(fr.slOnBlock j))
    have hgj : g.1 ∈ fr.slOnBlock j := g.2
    have hgi : g.1 ∈ fr.slOnBlock i := by rw [← heq]; exact g.2
    have hgone : g.1 = 1 := tpa8_slOnBlock_disjoint fr hji g.2 hgi
    exact hg1 (Subtype.ext hgone)
  have hsome3 : ∃ j, fr.m j ≠ 0 ∧ Module.finrank (ZMod 2) (fr.E j) = 3 := by
    by_contra h
    push Not at h
    have hall : ∀ j, fr.m j ≠ 0 → Module.finrank (ZMod 2) (fr.E j) = 1 := by
      intro j hj
      rcases hfield j hj with h' | h'
      · exact h'
      · exact absurd h' (h j hj)
    have htriv : ∀ p, StarFour.groupRep η p = 1 :=
      tpa8_frame_all_one (ρ := StarFour.groupRep η) fr hall
    have hmem : tpa8_psi.symm x ∈ η.range := by
      rw [hrange]; exact Subgroup.mem_zpowers _
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hmem
    have h1 : StarFour.groupRep η p = 1 := htriv p
    rw [StarFour.groupRep, MonoidHom.comp_apply] at h1
    have h2 : η p = 1 := Subtype.ext h1
    have hx1 : x = 1 := by
      have h3 : tpa8_psi.symm x = 1 := by rw [← hp]; exact h2
      have := congrArg tpa8_psi h3
      simpa using this
    rw [hx1] at hxord
    simp at hxord
  have hmf : fr.m i * Module.finrank (ZMod 2) (fr.E i) ≤ 9 := by
    calc fr.m i * Module.finrank (ZMod 2) (fr.E i)
        ≤ ∑ k, fr.m k * Module.finrank (ZMod 2) (fr.E k) :=
          Finset.single_le_sum (f := fun k => fr.m k * Module.finrank (ZMod 2) (fr.E k))
            (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = 9 := hdim
  have hmle : fr.m i ≤ 6 := by
    rcases hfield i (by
        exact Nat.pos_iff_ne_zero.mp
          (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hgood.1)) with hfi | hfi
    · obtain ⟨j, hj0, hj3⟩ := hsome3
      have hji : j ≠ i := by
        rintro rfl; rw [hfi] at hj3; omega
      have hpair : fr.m i + fr.m j * 3 ≤ 9 := by
        calc fr.m i + fr.m j * 3
            = fr.m i * Module.finrank (ZMod 2) (fr.E i)
                + fr.m j * Module.finrank (ZMod 2) (fr.E j) := by simp [hfi, hj3]
          _ ≤ ∑ k, fr.m k * Module.finrank (ZMod 2) (fr.E k) := by
              have hsub : ({i, j} : Finset (Fin fr.r)) ⊆ Finset.univ := Finset.subset_univ _
              have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun k _ _ => Nat.zero_le (fr.m k * Module.finrank (ZMod 2) (fr.E k)))
              simpa [Finset.sum_pair (Ne.symm hji)] using h
          _ = 9 := hdim
      have hj1 : 1 ≤ fr.m j := Nat.one_le_iff_ne_zero.mpr hj0
      omega
    · have hmf' := hmf
      rw [hfi] at hmf'
      omega
  have hcardEi : Nat.card (fr.E i) = 2 ^ Module.finrank (ZMod 2) (fr.E i) := by
    haveI : Module.Finite (ZMod 2) (fr.E i) := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fr.E i), Nat.card_zmod]
  have hdiv : 7 ^ 2 * (Nat.card (fr.E i) - 1) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i)) := by
    have hset : Set.image (fun b : Matrix.GeneralLinearGroup (Fin 9) (ZMod 2) =>
          tpa8_psi.symm b) (D : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) =
        η.range := by
      rw [hη]
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, Subgroup.mem_top b⟩, hb, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b, hb, rfl⟩
    have hinf := StarFour.inf_centralizer_eq_map_centralizer ψh tpa8_psi.injective
      (D : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))
      (fun b => tpa8_psi.symm b)
      (by
        intro b hb u
        show b * tpa8_psi u * b⁻¹ =
          tpa8_psi (tpa8_psi.symm b * u * (tpa8_psi.symm b)⁻¹)
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply])
    rw [hset] at hinf
    rw [← StarFour.repCentSL_groupRep η] at hinf
    have hEx : E ≤ Subgroup.centralizer
        ({x} : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (congrArg Subtype.val (hEab.1.is_comm.comm ⟨e, he⟩ ⟨x, hxE⟩)).symm
    have hEcard7 : Nat.card E = 7 ^ 3 := by
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hEp : IsPGroup 7 ↥E := by
        rw [isPGroup_iff_orderOf_dvd_pow]
        intro e
        refine ⟨1, ?_⟩
        rw [pow_one]
        exact orderOf_dvd_of_pow_eq_one
          (Subtype.ext (hEab.2 (e : Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)) e.2))
      obtain ⟨n, hEn⟩ := (IsPGroup.iff_card (p := 7) (G := ↥E)).mp hEp
      have hcardGL : Nat.card (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)) =
          Nat.card (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := Nat.card_congr ggSL9GLEquiv.toEquiv
      have hn_le : n ≤ 3 := by
        by_contra h
        push Not at h
        have hdvd : 7 ^ 4 ∣ Nat.card (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := by
          rw [← hcardGL]
          exact dvd_trans (Nat.pow_dvd_pow 7 (Nat.succ_le_of_lt h))
            (by rw [← hEn]; exact Subgroup.card_subgroup_dvd_card E)
        exact not_seven_pow_four_dvd_card_ggSL9 hdvd
      exact le_antisymm (by rw [hEn]; exact Nat.pow_le_pow_right (by norm_num) hn_le) hEcard
    let E' := E.comap ψh
    have hE'le : E' ≤ StarFour.repCentSL (StarFour.groupRep η) := by
      intro e he
      have h1 : ψh e ∈ ψh.range ⊓
          Subgroup.centralizer (D : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) := by
        refine ⟨MonoidHom.mem_range.mpr ⟨e, rfl⟩, ?_⟩
        rw [tpa8_centralizer_zpowers]
        exact hEx he
      rw [hinf] at h1
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp h1
      have hye' : y = e := tpa8_psi.injective hye
      exact hye' ▸ hy
    have hE'map : E'.map ψh = E := by
      rw [Subgroup.map_comap_eq_self]
      rw [MonoidHom.range_eq_top.mpr tpa8_psi.surjective]
      exact le_top
    have hE'card : Nat.card E' = 7 ^ 3 := by
      rw [← hEcard7, ← hE'map]
      exact Nat.card_congr (Subgroup.equivMapOfInjective E' ψh tpa8_psi.injective).toEquiv
    have hx'E' : tpa8_psi.symm x ∈ E' := by
      change ψh (tpa8_psi.symm x) ∈ E
      rw [show ψh (tpa8_psi.symm x) = x from by
        change tpa8_psi (tpa8_psi.symm x) = x
        exact MulEquiv.apply_symm_apply tpa8_psi x]
      exact hxE
    have hx'mem : tpa8_psi.symm x ∈ η.range := by
      rw [hrange]; exact Subgroup.mem_zpowers _
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hx'mem
    have hx'E'' : η p ∈ E' := by rw [hp]; exact hx'E'
    have hηprep : η p ∈ StarFour.repCentSL (StarFour.groupRep η) := hE'le hx'E''
    let Z : Subgroup (Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i)) :=
      Subgroup.center (Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i))
    let φ : E' →* Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i) :=
      (Pi.evalMonoidHom (fun j => Matrix.GeneralLinearGroup (Fin (fr.m j)) (fr.E j)) i).comp
        ((StarFour.SemiFrame.blockPiGL fr).comp (Subgroup.inclusion hE'le))
    let ψ' : E' →* Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i) ⧸ Z :=
      (QuotientGroup.mk' Z).comp φ
    have hinc : (Subgroup.inclusion hE'le ⟨tpa8_psi.symm x, hx'E'⟩ :
        StarFour.repCentSL (StarFour.groupRep η)) = ⟨η p, hηprep⟩ := by
      apply Subtype.ext
      exact hp.symm
    have hblock : StarFour.SemiFrame.blockLin fr ⟨η p, hηprep⟩ i =
        (fr.χ i p : fr.E i) • (1 : (Fin (fr.m i) → fr.E i) →ₗ[fr.E i]
          (Fin (fr.m i) → fr.E i)) :=
      tpa8_blockLin_eta fr p i hηprep
    have hphiZ : φ ⟨tpa8_psi.symm x, hx'E'⟩ ∈ Z := by
      change StarFour.SemiFrame.blockPiGL fr
        (Subgroup.inclusion hE'le ⟨tpa8_psi.symm x, hx'E'⟩) i ∈ Z
      rw [hinc]
      change StarFour.SemiFrame.linEquivToGL
        (StarFour.SemiFrame.blockEquiv fr ⟨η p, hηprep⟩ i) ∈ Z
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, rfl⟩ :=
        (StarFour.SemiFrame.linEquivToGL (E := fr.E i) (n := fr.m i)).surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply LinearEquiv.ext
      intro y
      change u (StarFour.SemiFrame.blockLin fr ⟨η p, hηprep⟩ i y) =
        StarFour.SemiFrame.blockLin fr ⟨η p, hηprep⟩ i (u y)
      rw [hblock]
      change u ((fr.χ i p : fr.E i) • y) = (fr.χ i p : fr.E i) • u y
      exact u.map_smul (fr.χ i p : fr.E i) y
    have hx'ker : (⟨tpa8_psi.symm x, hx'E'⟩ : E') ∈ ψ'.ker := by
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' Z) (φ (⟨tpa8_psi.symm x, hx'E'⟩ : E')) = 1
      exact (QuotientGroup.eq_one_iff _).mpr hphiZ
    have hker_le : ψ'.ker.map E'.subtype ≤ (E ⊓ Subgroup.centralizer (J : Set
        (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))).comap ψh := by
      intro e he
      rw [Subgroup.mem_map] at he
      obtain ⟨e', he'ker, rfl⟩ := he
      rw [MonoidHom.mem_ker] at he'ker
      rw [Subgroup.mem_comap]
      refine ⟨e'.2, ?_⟩
      have heZ : φ e' ∈ Z := by
        have h1 : (QuotientGroup.mk' Z) (φ e') = 1 := he'ker
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hmem : (Subgroup.inclusion hE'le e' : StarFour.repCentSL
          (StarFour.groupRep η)).1 ∈
          Subgroup.centralizer (fr.slOnBlock i : Set _) := by
        apply tpa8_center_block_mem_centralizer
        change StarFour.SemiFrame.blockPiGL fr (Subgroup.inclusion hE'le e') i ∈ Z
        exact heZ
      rw [hJψ]
      change ψh (E'.subtype e') ∈ Subgroup.centralizer ((fr.slOnBlock i).map ψh : Set _)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      change ψh z * ψh ((Subgroup.inclusion hE'le e').1) =
        ψh ((Subgroup.inclusion hE'le e').1) * ψh z
      simpa only [map_mul] using
        congrArg ψh ((Subgroup.mem_centralizer_iff.mp hmem) z hz)
    haveI : Finite ↥E' := Finite.of_injective (fun e : E' => (⟨ψh e, e.2⟩ : E))
      (by intro a b h; exact Subtype.ext (tpa8_psi.injective (Subtype.ext_iff.mp h)))
    haveI : Finite (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)) := inferInstance
    haveI : Finite ↥(E ⊓ Subgroup.centralizer (J : Set
        (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) := Subtype.finite
    have hle' : Subgroup.comap ψh (E ⊓ Subgroup.centralizer (J : Set
        (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) ≤ E' := by
      intro e he
      exact (Subgroup.mem_comap.mp he).1
    haveI : Finite ↥(Subgroup.comap ψh (E ⊓ Subgroup.centralizer (J : Set
        (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))))) :=
      Finite.of_injective (Subgroup.inclusion hle') (Subgroup.inclusion_injective hle')
    have hker_card_le : Nat.card ψ'.ker ≤ 7 := by
      have h1 : Nat.card ψ'.ker = Nat.card (ψ'.ker.map E'.subtype) :=
        Nat.card_congr (Subgroup.equivMapOfInjective ψ'.ker E'.subtype
          E'.subtype_injective).toEquiv
      rw [h1]
      have h2 := Nat.card_le_card_of_injective (f := Subgroup.inclusion hker_le)
          (Subgroup.inclusion_injective hker_le)
      have h3 : Nat.card ↥(E ⊓ Subgroup.centralizer (J : Set
          (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) = 7 := by
        rw [hEinter]
        exact (Nat.card_zpowers x).trans hxord
      have h4 : Nat.card ↥(Subgroup.comap ψh (E ⊓ Subgroup.centralizer (J : Set
          (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))))) = 7 := by
        rw [← h3]
        rw [Nat.card_congr (Subgroup.equivMapOfInjective _ ψh
          tpa8_psi.injective).toEquiv]
        congr 1
        rw [Subgroup.map_comap_eq_self]
        rw [MonoidHom.range_eq_top.mpr tpa8_psi.surjective]
        exact le_top
      omega
    have hker_card : Nat.card ψ'.ker = 7 := by
      have hzp : Subgroup.zpowers (⟨tpa8_psi.symm x, hx'E'⟩ : E') ≤ ψ'.ker :=
        Subgroup.zpowers_le.mpr hx'ker
      have h1 := Nat.card_le_card_of_injective (f := Subgroup.inclusion hzp)
          (Subgroup.inclusion_injective hzp)
      have hx'ne : tpa8_psi.symm x ≠ 1 := by
        intro h
        have hx1 : x = 1 := by
          have := congrArg tpa8_psi h
          simpa using this
        rw [hx1] at hxord
        simp at hxord
      have h2 : Nat.card (Subgroup.zpowers (⟨tpa8_psi.symm x, hx'E'⟩ : E')) = 7 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (Subtype.ext hsymm7)
          (by intro h; exact hx'ne (congrArg Subtype.val h))
      omega
    have h49 : 49 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i) ⧸ Z) := by
      have hmul : Nat.card E' = Nat.card (E' ⧸ ψ'.ker) * Nat.card ψ'.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup ψ'.ker
      have hiso : Nat.card (E' ⧸ ψ'.ker) = Nat.card ψ'.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ').toEquiv
      rw [hiso, hker_card, hE'card] at hmul
      have hrange_card : Nat.card ψ'.range = 49 := by omega
      rw [← hrange_card]
      exact Subgroup.card_subgroup_dvd_card ψ'.range
    have hZcard : Nat.card Z = Nat.card (fr.E i) - 1 := by
      change Nat.card (Subgroup.center (Matrix.GeneralLinearGroup (Fin (fr.m i))
        (fr.E i))) = Nat.card (fr.E i) - 1
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      change Nat.card (Set.range (Matrix.GeneralLinearGroup.scalar (Fin (fr.m i))
        (R := fr.E i))) = Nat.card (fr.E i) - 1
      rw [Nat.card_range_of_injective]
      · exact Nat.card_units _
      · intro u v huv
        have h1 : (Matrix.GeneralLinearGroup.scalar (Fin (fr.m i)) u :
            Matrix (Fin (fr.m i)) (Fin (fr.m i)) (fr.E i)) =
            Matrix.GeneralLinearGroup.scalar (Fin (fr.m i)) v := by rw [huv]
        have hm0 : 0 < fr.m i := by have := hgood.1; omega
        have h2 := congrFun (congrFun h1 ⟨0, hm0⟩) ⟨0, hm0⟩
        exact Units.ext (by simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] using h2)
    obtain ⟨k, hk⟩ := h49
    have hmul : Nat.card (Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i)) =
        Nat.card (Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i) ⧸ Z) * Nat.card Z :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    refine ⟨k, ?_⟩
    rw [hmul, hk, hZcard]
    ring
  have hcase : (fr.m i = 6 ∧ Module.finrank (ZMod 2) (fr.E i) = 1) ∨
      (fr.m i = 3 ∧ Module.finrank (ZMod 2) (fr.E i) = 3) := by
    letI : Fintype (fr.E i) := Fintype.ofFinite _
    have hEcard : Fintype.card (fr.E i) = 2 ^ Module.finrank (ZMod 2) (fr.E i) := by
      rw [← Nat.card_eq_fintype_card]; exact hcardEi
    have hdiv' : 7 ^ 2 * (Fintype.card (fr.E i) - 1) ∣
        Nat.card (Matrix.GeneralLinearGroup (Fin (fr.m i)) (fr.E i)) := by
      rwa [Nat.card_eq_fintype_card] at hdiv
    exact tpa8_hcase_arith (m := fr.m i) (f := Module.finrank (ZMod 2) (fr.E i))
      (E := fr.E i) hgood.1 hmle hmf
      (hfield i (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hgood.1)))
      hEcard hdiv'
  have he : Matrix.SpecialLinearGroup (Fin (fr.m i)) (fr.E i) ≃* J :=
    ((Matrix.SpecialLinearGroup.toLin'_equiv (R := fr.E i) (n := Fin (fr.m i))).trans
      (StarFour.SemiFrame.blockMulEquiv fr i)).trans
      ((Subgroup.equivMapOfInjective (fr.slOnBlock i) ψh tpa8_psi.injective).trans
        (MulEquiv.subgroupCongr hJψ.symm))
  have hlabel5 : fr.m i = 6 → Module.finrank (ZMod 2) (fr.E i) = 1 →
      GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J) := by
    intro hm hf
    have h := tpa8_hasLabel_of_sl (E := fr.E i) (m := fr.m i) (f := 1)
      (by simp [hm]) (by norm_num) (by rw [hcardEi, hf]) he
    simpa [hm] using h
  have hlabel2 : fr.m i = 3 → Module.finrank (ZMod 2) (fr.E i) = 3 →
      GGHasLabel ⟨.A, 2, 3⟩ (J ⧸ Subgroup.center J) := by
    intro hm hf
    have h := tpa8_hasLabel_of_sl (E := fr.E i) (m := fr.m i) (f := 3)
      (by simp [hm]) (by norm_num) (by rw [hcardEi, hf]) he
    simpa [hm] using h
  rcases hcase with ⟨hm, hf⟩ | ⟨hm, hf⟩
  · exact Or.inr (hlabel5 hm hf)
  · exact Or.inl (hlabel2 hm hf)

end CFSG.StandardType

end

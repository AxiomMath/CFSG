module

public import CFSG.LocalAnalysis.StandardType.GGF4N2KComponents
public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartDefs
import all CFSG.LocalAnalysis.StandardType.GGF4N2KComponents
import CFSG.LocalAnalysis.StandardType.GGF4N2JPositions
import CFSG.RankThree.PartOne.S15K.JointEigen
import CFSG.Quasithin.Vol2.Ch9Sec3FactsLieSL3
import TauCeti.LinearAlgebra.Dimension.DirectSum

public section

namespace CFSG.StandardType.N2ChartSupport

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.CALinearPrimary

section Eigen

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

theorem pow_apply_of_apply_eq_smul {Y : Module.End E W} {μ : E} {v : W} (hv : Y v = μ • v)
    (n : ℕ) : (Y ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]

theorem finrank_eigenspace_le_pow_four [FiniteDimensional E W] {Y G' : Module.End E W}
    (hYG' : Y * G' = G' * Y ^ 4) (hG' : Function.Injective G') (μ : E) :
    finrank E (Y.eigenspace μ) ≤ finrank E (Y.eigenspace (μ ^ 4)) := by
  have hmaps : ∀ v ∈ Y.eigenspace μ, G' v ∈ Y.eigenspace (μ ^ 4) := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h := congrArg (fun T : Module.End E W => T v) hYG'
    simp only [Module.End.mul_apply] at h
    rw [h, pow_apply_of_apply_eq_smul hv, map_smul]
  apply LinearMap.finrank_le_finrank_of_injective (f := G'.restrict hmaps)
  intro v w hvw
  apply Subtype.ext
  apply hG'
  simpa [LinearMap.restrict_apply] using congrArg Subtype.val hvw

theorem exists_finrank_eq_finrank_eigenspace_one_add_two_mul [FiniteDimensional E W] {ζ : E}
    (hζ : IsPrimitiveRoot ζ 5) {Y G G' : Module.End E W} (hY5 : Y ^ 5 = 1) (hGG' : G * G' = 1)
    (hG'G : G' * G = 1) (hconj : G * Y * G' = Y ^ 4) :
    ∃ m, finrank E W = finrank E (Y.eigenspace 1) + 2 * m := by
  classical
  have hYG' : Y * G' = G' * Y ^ 4 := by
    calc Y * G' = G' * G * Y * G' := by rw [hG'G, one_mul]
      _ = G' * (G * Y * G') := by simp only [mul_assoc]
      _ = G' * Y ^ 4 := by rw [hconj]
  have hG' : Function.Injective G' := by
    intro v w h
    have hv : G (G' v) = v := by rw [← Module.End.mul_apply G G' v, hGG', Module.End.one_apply]
    have hw : G (G' w) = w := by rw [← Module.End.mul_apply G G' w, hGG', Module.End.one_apply]
    rw [← hv, ← hw, h]
  have hle := finrank_eigenspace_le_pow_four hYG' hG'
  have hsym : ∀ i : ℕ, finrank E (Y.eigenspace (ζ ^ i)) =
      finrank E (Y.eigenspace ((ζ ^ i) ^ 4)) := by
    intro i
    refine le_antisymm (hle _) ?_
    have h16 : ((ζ ^ i) ^ 4) ^ 4 = ζ ^ i := by
      rw [← pow_mul, ← pow_mul, show i * (4 * 4) = 5 * (3 * i) + i by ring, pow_add, pow_mul,
        hζ.pow_eq_one, one_pow, one_mul]
    calc finrank E (Y.eigenspace ((ζ ^ i) ^ 4)) ≤
        finrank E (Y.eigenspace (((ζ ^ i) ^ 4) ^ 4)) := hle _
      _ = finrank E (Y.eigenspace (ζ ^ i)) := by rw [h16]
  have hinj : Function.Injective fun i : Fin 5 => ζ ^ (i : ℕ) :=
    fun i j h => Fin.ext (hζ.pow_inj i.2 j.2 h)
  have hind : iSupIndep fun i : Fin 5 => Y.eigenspace (ζ ^ (i : ℕ)) :=
    (Module.End.eigenspaces_iSupIndep Y).comp hinj
  have htop : (⨆ i : Fin 5, Y.eigenspace (ζ ^ (i : ℕ))) = ⊤ := by
    rw [eq_top_iff, ← CFSG.RankThree.PartOne.S15K.iSup_eigenspace_eq_top_of_pow_eq_one
      (by norm_num) hζ hY5]
    refine iSup₂_le fun μ hμ => ?_
    obtain ⟨i, hi, rfl⟩ :=
      hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset (by norm_num) (1 : E)).mp hμ)
    exact le_iSup (fun i : Fin 5 => Y.eigenspace (ζ ^ (i : ℕ))) ⟨i, hi⟩
  have hsum : finrank E W = ∑ i : Fin 5, finrank E (Y.eigenspace (ζ ^ (i : ℕ))) := by
    rw [← finrank_top E W, ← htop]
    exact TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hind
  rw [Fin.sum_univ_eq_sum_range (fun i => finrank E (Y.eigenspace (ζ ^ i))) 5] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
  have h0 : finrank E (Y.eigenspace (ζ ^ 0)) = finrank E (Y.eigenspace 1) := by rw [pow_zero]
  have h14 : finrank E (Y.eigenspace (ζ ^ 1)) = finrank E (Y.eigenspace (ζ ^ 4)) := by
    rw [hsym 1, ← pow_mul]
  have h23 : finrank E (Y.eigenspace (ζ ^ 2)) = finrank E (Y.eigenspace (ζ ^ 3)) := by
    rw [hsym 2, ← pow_mul, show 2 * 4 = 5 + 3 by norm_num, pow_add, hζ.pow_eq_one, one_mul]
  exact ⟨finrank E (Y.eigenspace (ζ ^ 1)) + finrank E (Y.eigenspace (ζ ^ 2)), by omega⟩

theorem finrank_range_sub_one_add_finrank_fixedSubmodule [FiniteDimensional E W]
    (x : Module.End E W) :
    finrank E (LinearMap.range (x - 1)) + finrank E x.fixedSubmodule = finrank E W := by
  have hker : LinearMap.ker (x - 1) = x.fixedSubmodule := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_fixedSubmodule_iff, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
  rw [← hker]
  exact LinearMap.finrank_range_add_finrank_ker (x - 1)

theorem isCompl_fixedSubmodule_range_sub_one [CharP E 2] {x : Module.End E W} (hx : x ^ 5 = 1) :
    IsCompl x.fixedSubmodule (LinearMap.range (x - 1)) := by
  have h2 : (2 : E[X]) = 0 := by
    rw [← map_ofNat (Polynomial.C (R := E)) 2, CharTwo.two_eq_zero, map_zero]
  have hN : aeval x (X - 1 : E[X]) = x - 1 := by simp
  obtain ⟨P, hP⟩ : ∃ P : Module.End E W, P = aeval x (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : E[X]) :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Module.End E W, R = aeval x (X ^ 3 + X : E[X]) := ⟨_, rfl⟩
  have hNP : (x - 1) * P = 0 := by
    rw [hP, ← hN, ← map_mul,
      show ((X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) : E[X]) = X ^ 5 - 1 by ring]
    simp [hx]
  have hPN : P * (x - 1) = 0 := by
    rw [hP, ← hN, ← map_mul,
      show ((X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1) : E[X]) = X ^ 5 - 1 by ring]
    simp [hx]
  have hbez : P - (x - 1) * R = 1 := by
    rw [hP, hR, ← hN, ← map_mul, ← map_sub,
      show ((X ^ 4 + X ^ 3 + X ^ 2 + X + 1) - (X - 1) * (X ^ 3 + X) : E[X]) =
        1 + 2 * (X ^ 3 + X) by ring, h2, zero_mul, add_zero, map_one]
  have hRN : R * (x - 1) = (x - 1) * R := by
    rw [hR, ← hN, ← map_mul, ← map_mul, mul_comm]
  have hdec : ∀ v, P v - (x - 1) (R v) = v := by
    intro v
    have h3 := LinearMap.congr_fun hbez v
    rwa [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply] at h3
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro v hv ⟨w, rfl⟩
    rw [LinearMap.mem_fixedSubmodule_iff] at hv
    have h1 : P ((x - 1) w) = 0 := by
      rw [← Module.End.mul_apply, hPN, LinearMap.zero_apply]
    have h0 : (x - 1) ((x - 1) w) = 0 := by
      rw [LinearMap.sub_apply ((x : Module.End E W)) 1 ((x - 1) w), hv, Module.End.one_apply,
        sub_self]
    have h1' : (x - 1) (R ((x - 1) w)) = 0 := by
      rw [← Module.End.mul_apply, ← hRN, Module.End.mul_apply, h0, map_zero]
    have h3 := hdec ((x - 1) w)
    rw [h1, h1', sub_zero] at h3
    exact h3.symm
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [← hdec v]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (LinearMap.mem_range.mpr ⟨R v, rfl⟩))
    rw [LinearMap.mem_fixedSubmodule_iff]
    have h := LinearMap.congr_fun hNP v
    rwa [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply,
      sub_eq_zero] at h

end Eigen

section SL6

variable {F : Type} [Field F]

theorem sl6End_one' : sl6End F (1 : Matrix.SpecialLinearGroup (Fin 6) F) = 1 := by
  simp [sl6End]

theorem sl6End_mul' (a b : Matrix.SpecialLinearGroup (Fin 6) F) :
    sl6End F (a * b) = sl6End F a * sl6End F b := by
  simp [sl6End, map_mul]

@[expose] noncomputable def sl6EndHom (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin 6) F →* Module.End F (Fin 6 → F) where
  toFun := sl6End F
  map_one' := sl6End_one'
  map_mul' := sl6End_mul'

@[simp] theorem sl6EndHom_apply (a : Matrix.SpecialLinearGroup (Fin 6) F) :
    sl6EndHom F a = sl6End F a := rfl

theorem sl6End_injective : Function.Injective (sl6End F) := by
  intro a b h
  apply slGL_injective (n := 6) (k := F)
  apply Units.ext
  simpa [sl6End] using h

@[expose] noncomputable def toCommutant (a : Matrix.SpecialLinearGroup (Fin 6) F) :
    Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F)) →*
      commutant (sl6End F a) where
  toFun c := ⟨sl6End F c, (mem_commutant _).mpr
    ((show Commute (c : Matrix.SpecialLinearGroup (Fin 6) F) a from
      Subgroup.mem_centralizer_singleton_iff.mp c.2).map (sl6EndHom F))⟩
  map_one' := Subtype.ext sl6End_one'
  map_mul' c d := Subtype.ext (sl6End_mul' (c : Matrix.SpecialLinearGroup (Fin 6) F) d)

end SL6

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem isPrimitiveRoot_root {q : F[X]} [Fact (Irreducible q)] (hdeg : q.natDegree = 2)
    (hdvd : q ∣ (X : F[X]) ^ 5 - 1) : IsPrimitiveRoot (AdjoinRoot.root q) 5 := by
  have hζ5 : AdjoinRoot.root q ^ 5 = 1 := by
    have h0 : AdjoinRoot.mk q ((X : F[X]) ^ 5 - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
    exact h0
  have hζ1 : AdjoinRoot.root q ≠ 1 := by
    intro h1
    have hroot : q.IsRoot 1 := by
      have h := AdjoinRoot.eval₂_root q
      rw [h1, Polynomial.eval₂_at_one] at h
      exact (AdjoinRoot.of q).injective (by rw [h, map_zero])
    have hd1 := Polynomial.natDegree_eq_of_degree_eq_some (n := 1)
      (by rw [Nat.cast_one]; exact Polynomial.degree_eq_one_of_irreducible_of_root Fact.out hroot)
    omega
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime hζ5 hζ1 ▸ IsPrimitiveRoot.orderOf _

theorem finrank_fixed_mod_four_of_irreducible {a b g : Matrix.SpecialLinearGroup (Fin 6) F}
    (ha : orderOf a = 5) (hb : orderOf b = 5) (hab : Commute a b)
    (hirr : Irreducible (minpoly F (sl6End F a))) (hdeg : (minpoly F (sl6End F a)).natDegree = 2)
    (hga : Commute g a) (hgb : g * b * g⁻¹ = b⁻¹) :
    finrank F (sl6End F b).fixedSubmodule % 4 = 2 := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, minpoly F (sl6End F a) = q := ⟨_, rfl⟩
  rw [hq] at hirr hdeg
  haveI : Fact (Irreducible q) := ⟨hirr⟩
  have hq0 : q ≠ 0 := hirr.ne_zero
  have htop : primaryComponent (sl6End F a) q = ⊤ := by
    refine eq_top_iff.mpr fun v _ => mem_primaryComponent.mpr ?_
    rw [← hq, minpoly.aeval]
    rfl
  have hdimE : finrank (AdjoinRoot q) (primaryComponent (sl6End F a) q) = 3 := by
    have h := finrank_primaryComponent (x := sl6End F a) (a := q)
    have h6 : finrank F (primaryComponent (sl6End F a) q) = 6 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    rw [h6, hdeg] at h
    omega
  have hζ : IsPrimitiveRoot (AdjoinRoot.root q) 5 :=
    isPrimitiveRoot_root hdeg (hq ▸ sl6End_minpoly_dvd ha)
  let φ : Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F)) →*
      Module.End (AdjoinRoot q) (primaryComponent (sl6End F a) q) :=
    (commutantRestrictHom (x := sl6End F a) q).toRingHom.toMonoidHom.comp (toCommutant a)
  have hb5 : b ^ 5 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  let b' : Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F)) :=
    ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hab.symm.eq⟩
  let g' : Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F)) :=
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hga.eq⟩
  have hb'5 : b' ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hb5)
  have hgb' : g' * b' * g'⁻¹ = b' ^ 4 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    change g * b * g⁻¹ = b ^ 4
    rw [hgb]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hb5))
  obtain ⟨m, hm⟩ := exists_finrank_eq_finrank_eigenspace_one_add_two_mul hζ
    (Y := φ b') (G := φ g') (G' := φ g'⁻¹)
    (by rw [← map_pow, hb'5, map_one]) (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_mul, inv_mul_cancel, map_one])
    (by rw [← map_mul, ← map_mul, hgb', map_pow])
  set S := (φ b').eigenspace 1 with hSdef
  let ι : S →ₗ[F] (Fin 6 → F) :=
    (primaryComponent (sl6End F a) q).subtype ∘ₗ (S.subtype.restrictScalars F)
  have hφb : ∀ w : primaryComponent (sl6End F a) q,
      ((φ b' w : primaryComponent (sl6End F a) q) : Fin 6 → F) = sl6End F b w := fun _ => rfl
  have hfix : (sl6End F b).fixedSubmodule = LinearMap.range ι := by
    ext v
    rw [LinearMap.mem_fixedSubmodule_iff, LinearMap.mem_range]
    constructor
    · intro hv
      have hvq : v ∈ primaryComponent (sl6End F a) q := by rw [htop]; trivial
      refine ⟨⟨⟨v, hvq⟩, ?_⟩, rfl⟩
      rw [hSdef, Module.End.mem_eigenspace_iff, one_smul]
      exact Subtype.ext ((hφb _).trans hv)
    · rintro ⟨w, rfl⟩
      have hw := Module.End.mem_eigenspace_iff.mp w.2
      rw [one_smul] at hw
      exact (hφb _).symm.trans (congrArg Subtype.val hw)
  have hι : Function.Injective ι := fun u v h => Subtype.ext (Subtype.ext h)
  have hFE : finrank F (AdjoinRoot q) = 2 := by
    rw [(AdjoinRoot.powerBasis hq0).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  haveI : Module.Free (AdjoinRoot q) S := Module.Free.of_divisionRing (AdjoinRoot q) S
  have hfinrank : finrank F (sl6End F b).fixedSubmodule = 2 * finrank (AdjoinRoot q) S := by
    rw [hfix, LinearMap.finrank_range_of_inj hι, ← Module.finrank_mul_finrank F (AdjoinRoot q) S,
      hFE]
  rw [hfinrank]
  omega

theorem sl6FixedMultiplicity_eq_four_of_inv_conj (hF : Nat.card F = 4)
    {a b g : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) (hb : orderOf b = 5)
    (hab : Commute a b)
    (h7a : 7 ∣ Nat.card (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))))
    (h7b : 7 ∣ Nat.card (Subgroup.centralizer ({b} : Set (Matrix.SpecialLinearGroup (Fin 6) F))))
    (hga : Commute g a) (hgb : g * b * g⁻¹ = b⁻¹) :
    sl6FixedMultiplicity F a = 4 := by
  rcases sl6_fixedMultiplicity_eq_four_or_irreducible_minpoly_of_seven_dvd hF ha h7a with
    h4 | ⟨-, hirr, hdeg⟩
  · exact h4
  · exfalso
    have hmod := finrank_fixed_mod_four_of_irreducible ha hb hab hirr hdeg hga hgb
    rw [← N2KCoordinate.sl6FixedMultiplicity_eq_finrank_fixedSubmodule hb] at hmod
    rcases sl6_fixedMultiplicity_eq_four_or_irreducible_minpoly_of_seven_dvd hF hb h7b with
      h4 | ⟨h0, -, -⟩
    · rw [h4] at hmod
      norm_num at hmod
    · rw [h0] at hmod
      norm_num at hmod

theorem finrank_fixedSubmodule_eq_four_of_inv_conj (hF : Nat.card F = 4)
    {a b g : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) (hb : orderOf b = 5)
    (hab : Commute a b)
    (h7a : 7 ∣ Nat.card (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))))
    (h7b : 7 ∣ Nat.card (Subgroup.centralizer ({b} : Set (Matrix.SpecialLinearGroup (Fin 6) F))))
    (hga : Commute g a) (hgb : g * b * g⁻¹ = b⁻¹) :
    finrank F (sl6End F a).fixedSubmodule = 4 := by
  rw [← N2KCoordinate.sl6FixedMultiplicity_eq_finrank_fixedSubmodule ha]
  exact sl6FixedMultiplicity_eq_four_of_inv_conj hF ha hb hab h7a h7b hga hgb

theorem range_le_fixedSubmodule_or_mem_zpowers (hF : Nat.card F = 4)
    {a b : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) (hb : orderOf b = 5)
    (hab : Commute a b) (hfa : finrank F (sl6End F a).fixedSubmodule = 4)
    (hfb : finrank F (sl6End F b).fixedSubmodule = 4) :
    LinearMap.range (sl6End F a - 1) ≤ (sl6End F b).fixedSubmodule ∨
      b ∈ Subgroup.zpowers a := by
  classical
  have hxy : Commute (sl6End F a) (sl6End F b) := hab.map (sl6EndHom F)
  have hcomplA := isCompl_fixedSubmodule_range_sub_one (sl6End_pow_five ha)
  have hA2 : finrank F (LinearMap.range (sl6End F a - 1)) = 2 := by
    have := finrank_range_sub_one_add_finrank_fixedSubmodule (sl6End F a)
    rw [hfa, Module.finrank_fin_fun] at this
    omega
  have hB2 : finrank F (LinearMap.range (sl6End F b - 1)) = 2 := by
    have := finrank_range_sub_one_add_finrank_fixedSubmodule (sl6End F b)
    rw [hfb, Module.finrank_fin_fun] at this
    omega
  have hsq := sl6End_squarefree ha
  obtain ⟨q, hq, hq1⟩ : ∃ q ∈ primaryFactors (sl6End F a), q ≠ X - 1 := by
    by_contra hcon
    push Not at hcon
    have hx1 : sl6End F a = LinearMap.id := ext_primaryComponent hsq fun q hq v hv => by
      have hv' := mem_primaryComponent.mp hv
      rw [hcon q hq] at hv'
      simpa [sub_eq_zero] using hv'
    have h1 : a = 1 := sl6End_injective (by rw [hx1, sl6End_one']; rfl)
    rw [h1, orderOf_one] at ha
    norm_num at ha
  obtain ⟨-, hdeg⟩ := (primaryFactor_degree_of_orderFive hF ha hq).resolve_left hq1
  haveI : Fact (Irreducible q) := ⟨irreducible_of_mem_primaryFactors hq⟩
  have hζ : IsPrimitiveRoot (AdjoinRoot.root q) 5 :=
    isPrimitiveRoot_root hdeg ((mem_primaryFactors.mp hq).2.2.trans (sl6End_minpoly_dvd ha))
  have hrootn : ∀ (n : ℕ) (w : primaryComponent (sl6End F a) q),
      (((AdjoinRoot.root q) ^ n • w : primaryComponent (sl6End F a) q) : Fin 6 → F) =
        (sl6End F a ^ n) w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', mul_smul, coe_root_smul_primaryComponent, ih, pow_succ',
        Module.End.mul_apply]
  have hlift : ∀ (c : AdjoinRoot q) (T : Module.End F (Fin 6 → F)), c ≠ 1 →
      (∀ w : primaryComponent (sl6End F a) q, T w = ((c • w : primaryComponent _ q) : Fin 6 → F)) →
      primaryComponent (sl6End F a) q ≤ LinearMap.range (T - 1) := by
    intro c T hc hT v hv
    have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr hc
    have hw : ∀ u : primaryComponent (sl6End F a) q, c • ((c - 1)⁻¹ • u) - (c - 1)⁻¹ • u = u :=
      fun u => by rw [smul_smul, ← sub_smul, ← sub_one_mul, mul_inv_cancel₀ hc1, one_smul]
    refine ⟨(((c - 1)⁻¹ • (⟨v, hv⟩ : primaryComponent (sl6End F a) q) :
      primaryComponent (sl6End F a) q) : Fin 6 → F), ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, hT, ← Submodule.coe_sub, hw]
  have hVqA : primaryComponent (sl6End F a) q ≤ LinearMap.range (sl6End F a - 1) :=
    hlift _ _ (hζ.ne_one (by norm_num)) fun w =>
      (coe_root_smul_primaryComponent (sl6End F a) q w).symm
  have hVqF : finrank F (primaryComponent (sl6End F a) q) =
      2 * primaryMultiplicity (sl6End F a) q := by
    rw [finrank_primaryComponent, hdeg]
  have hm1 : primaryMultiplicity (sl6End F a) q = 1 := by
    have hle := Submodule.finrank_mono hVqA
    rw [hVqF, hA2] at hle
    have := primaryMultiplicity_pos ha hq
    omega
  have hVqA' : primaryComponent (sl6End F a) q = LinearMap.range (sl6End F a - 1) :=
    Submodule.eq_of_le_of_finrank_eq hVqA (by rw [hVqF, hm1, hA2])
  let y' : commutant (sl6End F a) := ⟨sl6End F b, (mem_commutant _).mpr hxy.symm⟩
  obtain ⟨c, hc, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hm1 (commutantRestrictHom q y')
  have hyv : ∀ w : primaryComponent (sl6End F a) q,
      sl6End F b w = ((c • w : primaryComponent (sl6End F a) q) : Fin 6 → F) := by
    intro w
    have h := congrArg (fun T => ((T w : primaryComponent (sl6End F a) q) : Fin 6 → F)) hc
    simpa [y'] using h
  have hyvn : ∀ (n : ℕ) (w : primaryComponent (sl6End F a) q),
      (sl6End F b ^ n) w = ((c ^ n • w : primaryComponent (sl6End F a) q) : Fin 6 → F) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih, hyv, smul_smul, ← pow_succ']
  have hc5 : c ^ 5 = 1 := by
    obtain ⟨w, hw⟩ := (Submodule.ne_bot_iff _).mp (primaryComponent_ne_bot hsq hq)
    obtain ⟨hwq, hw0⟩ := hw
    have h := hyvn 5 ⟨w, hwq⟩
    rw [sl6End_pow_five hb, Module.End.one_apply] at h
    have h' : (c ^ 5 - 1) • (⟨w, hwq⟩ : primaryComponent (sl6End F a) q) = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]
      exact Subtype.ext h.symm
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd (congrArg Subtype.val h'') hw0
  obtain ⟨k, hk5, hck⟩ := hζ.eq_pow_of_pow_eq_one hc5
  by_cases hk0 : k = 0
  · left
    rw [← hVqA']
    intro v hv
    rw [LinearMap.mem_fixedSubmodule_iff, hyv ⟨v, hv⟩, ← hck, hk0, pow_zero, one_smul]
  · right
    have hc1 : c ≠ 1 := by
      rw [← hck]
      exact hζ.pow_ne_one_of_pos_of_lt hk0 hk5
    have hAB : LinearMap.range (sl6End F a - 1) = LinearMap.range (sl6End F b - 1) :=
      Submodule.eq_of_le_of_finrank_eq (hVqA' ▸ hlift c _ hc1 hyv) (by rw [hA2, hB2])
    have hyfix : ∀ v ∈ (sl6End F a).fixedSubmodule, sl6End F b v = v := by
      intro v hv
      have h1 : sl6End F b v - v ∈ LinearMap.range (sl6End F a - 1) := by
        rw [hAB]
        exact ⟨v, by rw [LinearMap.sub_apply, Module.End.one_apply]⟩
      have h2 : sl6End F b v - v ∈ (sl6End F a).fixedSubmodule := by
        rw [LinearMap.mem_fixedSubmodule_iff] at hv ⊢
        rw [map_sub, hv, ← Module.End.mul_apply, hxy.eq, Module.End.mul_apply, hv]
      exact sub_eq_zero.mp (Submodule.disjoint_def.mp hcomplA.disjoint _ h2 h1)
    have hyx : sl6End F b = sl6End F a ^ k := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ (sl6End F a).fixedSubmodule ⊔ LinearMap.range (sl6End F a - 1) := by
        rw [hcomplA.codisjoint.eq_top]
        trivial
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.mp hv
      have hx1 : sl6End F a v1 = (1 : F) • v1 := by
        rw [one_smul]
        exact LinearMap.mem_fixedSubmodule_iff.mp hv1
      rw [map_add, map_add, hyfix v1 hv1, pow_apply_of_apply_eq_smul hx1, one_pow, one_smul]
      rw [← hVqA'] at hv2
      rw [hyv ⟨v2, hv2⟩, ← hck, hrootn]
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply sl6End_injective
    rw [zpow_natCast, ← sl6EndHom_apply, map_pow, sl6EndHom_apply, hyx]

theorem support_decomposition (hF : Nat.card F = 4) {a b : Matrix.SpecialLinearGroup (Fin 6) F}
    (ha : orderOf a = 5) (hb : orderOf b = 5) (hab : Commute a b)
    (hind : b ∉ Subgroup.zpowers a) (hfa : finrank F (sl6End F a).fixedSubmodule = 4)
    (hfb : finrank F (sl6End F b).fixedSubmodule = 4) :
    finrank F (LinearMap.range (sl6End F a - 1)) = 2 ∧
      finrank F (LinearMap.range (sl6End F b - 1)) = 2 ∧
      finrank F ↥((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) = 2 ∧
      LinearMap.range (sl6End F a - 1) ≤ (sl6End F b).fixedSubmodule ∧
      LinearMap.range (sl6End F b - 1) ≤ (sl6End F a).fixedSubmodule ∧
      (sl6End F a).fixedSubmodule = LinearMap.range (sl6End F b - 1) ⊔
        ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ∧
      (sl6End F b).fixedSubmodule = LinearMap.range (sl6End F a - 1) ⊔
        ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ∧
      Disjoint (LinearMap.range (sl6End F b - 1))
        ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ∧
      Disjoint (LinearMap.range (sl6End F a - 1))
        ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ∧
      IsCompl (LinearMap.range (sl6End F a - 1)) (sl6End F a).fixedSubmodule := by
  have hind' : a ∉ Subgroup.zpowers b := by
    intro h
    apply hind
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr h
    have hcard : Nat.card (Subgroup.zpowers b) ≤ Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, ha, hb]
    rw [Subgroup.eq_of_le_of_card_ge hle hcard]
    exact Subgroup.mem_zpowers b
  have hcomplA := isCompl_fixedSubmodule_range_sub_one (sl6End_pow_five ha)
  have hcomplB := isCompl_fixedSubmodule_range_sub_one (sl6End_pow_five hb)
  have hA2 : finrank F (LinearMap.range (sl6End F a - 1)) = 2 := by
    have := finrank_range_sub_one_add_finrank_fixedSubmodule (sl6End F a)
    rw [hfa, Module.finrank_fin_fun] at this
    omega
  have hB2 : finrank F (LinearMap.range (sl6End F b - 1)) = 2 := by
    have := finrank_range_sub_one_add_finrank_fixedSubmodule (sl6End F b)
    rw [hfb, Module.finrank_fin_fun] at this
    omega
  have hAb := (range_le_fixedSubmodule_or_mem_zpowers hF ha hb hab hfa hfb).resolve_right hind
  have hBa := (range_le_fixedSubmodule_or_mem_zpowers hF hb ha hab.symm hfb hfa).resolve_right
    hind'
  have hBW : Disjoint (LinearMap.range (sl6End F b - 1))
      ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) :=
    hcomplB.disjoint.symm.mono_right inf_le_right
  have hAW : Disjoint (LinearMap.range (sl6End F a - 1))
      ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) :=
    hcomplA.disjoint.symm.mono_right inf_le_left
  have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq (sl6End F a).fixedSubmodule
    (sl6End F b).fixedSubmodule
  have hsup6 := Submodule.finrank_le ((sl6End F a).fixedSubmodule ⊔ (sl6End F b).fixedSubmodule)
  rw [Module.finrank_fin_fun] at hsup6
  have hBWsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (sl6End F b - 1))
    ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule)
  rw [hBW.eq_bot, finrank_bot] at hBWsup
  have hBWle : LinearMap.range (sl6End F b - 1) ⊔
      ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ≤
        (sl6End F a).fixedSubmodule := sup_le hBa inf_le_left
  have hBW4 := Submodule.finrank_mono hBWle
  rw [hfa] at hBW4
  have hW2 : finrank F ↥((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) = 2 := by
    omega
  have hAWsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (sl6End F a - 1))
    ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule)
  rw [hAW.eq_bot, finrank_bot] at hAWsup
  refine ⟨hA2, hB2, hW2, hAb, hBa, ?_, ?_, hBW, hAW, hcomplA.symm⟩
  · exact (Submodule.eq_of_le_of_finrank_eq hBWle (by omega)).symm
  · exact (Submodule.eq_of_le_of_finrank_eq (sup_le hAb inf_le_right) (by omega)).symm

theorem support_decomposition_of_inv_conj (hF : Nat.card F = 4)
    {a b ga gb : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) (hb : orderOf b = 5)
    (hab : Commute a b) (hind : b ∉ Subgroup.zpowers a)
    (h7a : 7 ∣ Nat.card (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))))
    (h7b : 7 ∣ Nat.card (Subgroup.centralizer ({b} : Set (Matrix.SpecialLinearGroup (Fin 6) F))))
    (hga : Commute ga a) (hgab : ga * b * ga⁻¹ = b⁻¹)
    (hgb : Commute gb b) (hgba : gb * a * gb⁻¹ = a⁻¹) :
    finrank F (LinearMap.range (sl6End F a - 1)) = 2 ∧
      finrank F (LinearMap.range (sl6End F b - 1)) = 2 ∧
      finrank F ↥((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) = 2 ∧
      LinearMap.range (sl6End F a - 1) ≤ (sl6End F b).fixedSubmodule ∧
      LinearMap.range (sl6End F b - 1) ≤ (sl6End F a).fixedSubmodule ∧
      (sl6End F a).fixedSubmodule = LinearMap.range (sl6End F b - 1) ⊔
        ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ∧
      (sl6End F b).fixedSubmodule = LinearMap.range (sl6End F a - 1) ⊔
        ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ∧
      Disjoint (LinearMap.range (sl6End F b - 1))
        ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ∧
      Disjoint (LinearMap.range (sl6End F a - 1))
        ((sl6End F a).fixedSubmodule ⊓ (sl6End F b).fixedSubmodule) ∧
      IsCompl (LinearMap.range (sl6End F a - 1)) (sl6End F a).fixedSubmodule :=
  support_decomposition hF ha hb hab hind
    (finrank_fixedSubmodule_eq_four_of_inv_conj hF ha hb hab h7a h7b hga hgab)
    (finrank_fixedSubmodule_eq_four_of_inv_conj hF hb ha hab.symm h7b h7a hgb hgba)

section SL3

open CFSG.Quasithin.H13.Ch9 CFSG.CharacterTheory.SteinbergBY

private def w0Mat : Matrix (Fin 3) (Fin 3) FieldFour := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private theorem w0Mat_det : w0Mat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

private def w0 : Matrix.SpecialLinearGroup (Fin 3) FieldFour := ⟨w0Mat, w0Mat_det⟩

private theorem w0_mul_h0_mul_w0_inv : w0 * SL3Four.h0 * w0⁻¹ = SL3Four.h0⁻¹ := by
  have hrel : SL3Four.h0 * w0 * SL3Four.h0 = w0 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    show SL3Four.h0Mat * w0Mat * SL3Four.h0Mat = w0Mat
    decide
  calc w0 * SL3Four.h0 * w0⁻¹ = SL3Four.h0⁻¹ * (SL3Four.h0 * w0 * SL3Four.h0) * w0⁻¹ := by group
    _ = SL3Four.h0⁻¹ := by rw [hrel]; group

theorem exists_conj_eq_inv_of_mulEquiv_sl3 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {H : Type*} [Group H] (e : H ≃* Matrix.SpecialLinearGroup (Fin 3) K) {t : H}
    (ht : orderOf t = 5) : ∃ w : H, w * t * w⁻¹ = t⁻¹ := by
  have := Fintype.ofFinite K
  let φ : K ≃+* FieldFour :=
    FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK, FieldFour.card_eq])
  let Φ : Matrix.SpecialLinearGroup (Fin 3) K ≃* Matrix.SpecialLinearGroup (Fin 3) FieldFour :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map φ.toRingHom)
      (Matrix.SpecialLinearGroup.map φ.symm.toRingHom)
      (by
        ext A : 1
        apply Subtype.ext
        refine Matrix.ext fun i j => ?_
        simp [Matrix.SpecialLinearGroup.map_apply_coe])
      (by
        ext A : 1
        apply Subtype.ext
        refine Matrix.ext fun i j => ?_
        simp [Matrix.SpecialLinearGroup.map_apply_coe])
  let ψ : H ≃* Matrix.SpecialLinearGroup (Fin 3) FieldFour := e.trans Φ
  obtain ⟨x, hx⟩ := SL3Four.exists_conj_mem_zpowers_h0 (ψ t) (by rw [MulEquiv.orderOf_eq, ht])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hw : w0 * SL3Four.h0 ^ k * w0⁻¹ = (SL3Four.h0 ^ k)⁻¹ := by
    have h := map_zpow (MulAut.conj w0) SL3Four.h0 k
    rw [MulAut.conj_apply, MulAut.conj_apply, w0_mul_h0_mul_w0_inv, inv_zpow] at h
    exact h
  have hst : ψ t = x⁻¹ * SL3Four.h0 ^ k * x := by
    rw [hk]
    group
  refine ⟨ψ.symm (x⁻¹ * w0 * x), ψ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hst]
  calc x⁻¹ * w0 * x * (x⁻¹ * SL3Four.h0 ^ k * x) * (x⁻¹ * w0 * x)⁻¹ =
      x⁻¹ * (w0 * SL3Four.h0 ^ k * w0⁻¹) * x := by group
    _ = (x⁻¹ * SL3Four.h0 ^ k * x)⁻¹ := by rw [hw]; group

end SL3

end CFSG.StandardType.N2ChartSupport

namespace CFSG.StandardType.N2Chart

open Module CFSG.StandardType.N2ChartSupport

theorem sl6End_eq_toLin' (g : SL6) :
    sl6End F4 g = Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) F4) := by
  simp [sl6End, CFSG.RankThree.CALinearPrimary.coe_slGL]

theorem suppSp_eq_range_sl6End (g : SL6) : suppSp g = LinearMap.range (sl6End F4 g - 1) := by
  rw [suppSp, sl6End_eq_toLin', Module.End.one_eq_id]

theorem fixSp_eq_fixedSubmodule (g : SL6) : fixSp g = (sl6End F4 g).fixedSubmodule := by
  ext v
  rw [fixSp, LinearMap.mem_ker, LinearMap.mem_fixedSubmodule_iff, sl6End_eq_toLin',
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem ggN2SL3InvConjInput_holds : ∀ t : Matrix.SpecialLinearGroup (Fin 3) F4, orderOf t = 5 → ∃ g, g * t * g⁻¹ = t⁻¹ :=
  fun _ ht =>
  exists_conj_eq_inv_of_mulEquiv_sl3 (GaloisField.card 2 2 (by norm_num)) (MulEquiv.refl _) ht

theorem ggN2SupportTwoInput_holds :
    ∀ u₁ u₂ : SL6, orderOf u₁ = 5 → orderOf u₂ = 5 → Commute u₁ u₂ →
      u₂ ∉ Subgroup.zpowers u₁ →
      7 ∣ Nat.card (Subgroup.centralizer ({u₁} : Set SL6)) →
      7 ∣ Nat.card (Subgroup.centralizer ({u₂} : Set SL6)) →
      (∃ g ∈ Subgroup.centralizer ({u₁} : Set SL6), g * u₂ * g⁻¹ = u₂⁻¹) →
      (∃ g ∈ Subgroup.centralizer ({u₂} : Set SL6), g * u₁ * g⁻¹ = u₁⁻¹) →
      Module.finrank F4 (suppSp u₁) = 2 ∧ Module.finrank F4 (suppSp u₂) = 2 ∧
        IsCompl (suppSp u₁) (fixSp u₁) ∧ IsCompl (suppSp u₂) (fixSp u₂) ∧
        suppSp u₁ ≤ fixSp u₂ ∧ suppSp u₂ ≤ fixSp u₁ := by
  intro u₁ u₂ ho₁ ho₂ hc hD h7₁ h7₂ ⟨g₁, hg₁, hg₁u⟩ ⟨g₂, hg₂, hg₂u⟩
  have hF : Nat.card F4 = 4 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨hA2, hB2, -, hAb, hBa, -, -, -, -, hAc⟩ :=
    support_decomposition_of_inv_conj hF ho₁ ho₂ hc hD h7₁ h7₂
      (Subgroup.mem_centralizer_singleton_iff.mp hg₁) hg₁u
      (Subgroup.mem_centralizer_singleton_iff.mp hg₂) hg₂u
  have hBc := (isCompl_fixedSubmodule_range_sub_one (sl6End_pow_five ho₂)).symm
  simp only [suppSp_eq_range_sl6End, fixSp_eq_fixedSubmodule]
  exact ⟨hA2, hB2, hAc, hBc, hAb, hBa⟩

end CFSG.StandardType.N2Chart

end

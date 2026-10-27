module

public import CFSG.RankThree.GF2n.Stroth80.SL2KDescent
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuterCore
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.RankThree.GF2n.Stroth80.SL2Descent
open CFSG.Quasithin.B45L2
open scoped MatrixGroups

theorem pow_two_pow_mod {F : Type*} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (x : F) (k : ℕ) : x ^ 2 ^ k = x ^ 2 ^ (k % n) := by
  conv_lhs => rw [← Nat.div_add_mod k n]
  rw [pow_add, pow_mul, pow_mul, ← pow_mul, mul_comm, pow_mul, ← hF, FiniteField.pow_card_pow]

section MinPeriod

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] {ρ : Representation (ZMod 2) SL(2, F) W} [Fact ρ.IsIrreducible]

theorem pow_shift_endRing {n : ℕ} (hF : Fintype.card F = 2 ^ n) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E] [CharP E 2] [Algebra F E]
    (ιD : EndRing ρ →+* E) {J : Finset ℕ} (hJn : ∀ i ∈ J, i < n)
    (Φ : (matRepE b ιD).Equiv (frobTensor F E J)) {e : ℕ}
    (he : J.image (fun i => (i + e) % n) = J) (c : EndRing ρ) : ιD c ^ 2 ^ e = ιD c := by
  classical
  have hmem : ∀ i : J, (i.1 + e) % n ∈ J := fun i => by
    have h := Finset.mem_image_of_mem (fun i => (i + e) % n) i.2
    rwa [he] at h
  let f : J → J := fun i => ⟨(i.1 + e) % n, hmem i⟩
  have hfinj : Function.Injective f := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    have h1 : (i + e) % n = (j + e) % n := congrArg Subtype.val h
    have h2 : i % n = j % n := Nat.ModEq.add_right_cancel' e h1
    rw [Nat.mod_eq_of_lt (hJn i hi), Nat.mod_eq_of_lt (hJn j hj)] at h2
    exact Subtype.ext h2
  let π : J ≃ J := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hπ : ∀ i : J, ((π i : J) : ℕ) = (i.1 + e) % n := fun i => rfl
  let fr : E →+* E := iterateFrobenius E 2 e
  have hfr : ∀ z : E, fr z = z ^ 2 ^ e := fun z => iterateFrobenius_def 2 e z
  let Θ : ((J → Fin 2) → E) → ((J → Fin 2) → E) := fun v x' => fr (v (fun i => x' (π i)))
  have hΘadd : ∀ u v, Θ (u + v) = Θ u + Θ v := fun u v => funext fun x' => map_add fr _ _
  have hΘsmul : ∀ (z : E) v, Θ (z • v) = fr z • Θ v := fun z v =>
    funext fun x' => map_mul fr _ _
  have hpowF : ∀ (a : F) (i : J), fr (algebraMap F E a ^ 2 ^ (i : ℕ)) =
      algebraMap F E a ^ 2 ^ ((π i : J) : ℕ) := by
    intro a i
    rw [hfr, ← pow_mul, ← pow_add, ← map_pow, ← map_pow, hπ, pow_two_pow_mod hF a (i + e)]
  have hΘT : ∀ (g : SL(2, F)) v, Θ (frobTensor F E J g v) = frobTensor F E J g (Θ v) := by
    intro g v
    funext x'
    show fr (frobTensor F E J g v (fun i => x' (π i))) = frobTensor F E J g (Θ v) x'
    rw [show frobTensor F E J g v (fun i => x' (π i)) =
        ∑ x, tmatE E (fun i : J => (i : ℕ)) g (fun i => x' (π i)) x * v x from
        tensorRep_apply _ g v _,
      show frobTensor F E J g (Θ v) x' =
        ∑ x, tmatE E (fun i : J => (i : ℕ)) g x' x * Θ v x from tensorRep_apply _ g _ x',
      map_sum]
    let σJ : (J → Fin 2) ≃ (J → Fin 2) := Equiv.arrowCongr π.symm (Equiv.refl (Fin 2))
    have hσJ : ∀ y, σJ y = fun i => y (π i) := fun y => by
      funext i
      simp [σJ, Equiv.arrowCongr_apply]
    rw [← σJ.sum_comp]
    refine Fintype.sum_congr _ _ fun y => ?_
    rw [hσJ y, map_mul]
    show fr (tmatE E (fun i : J => (i : ℕ)) g (fun i => x' (π i)) (fun i => y (π i))) *
        fr (v (fun i => y (π i))) =
      tmatE E (fun i : J => (i : ℕ)) g x' y * fr (v (fun i => y (π i)))
    congr 1
    simp only [tmatE, twistMat_apply, map_prod, hpowF]
    exact π.prod_comp (fun j => algebraMap F E (g (x' j) (y j)) ^ 2 ^ (j : ℕ))
  let P : Matrix (Fin m) (Fin m) (EndRing ρ) → Prop := fun Y => ∀ v,
    Θ (Φ ((Y.map ιD).mulVec (Φ.symm v))) = Φ ((Y.map ιD).mulVec (Φ.symm (Θ v)))
  have hadd : ∀ Y Y', P Y → P Y' → P (Y + Y') := by
    intro Y Y' hY hY' v
    rw [Matrix.map_add _ ιD.map_add, Matrix.add_mulVec, Matrix.add_mulVec, map_add, map_add,
      hΘadd, hY, hY']
  have hmul : ∀ Y Y', P Y → P Y' → P (Y * Y') := by
    intro Y Y' hY hY' v
    have h1 : ∀ w, Φ (((Y * Y').map ιD).mulVec (Φ.symm w)) =
        Φ ((Y.map ιD).mulVec (Φ.symm (Φ ((Y'.map ιD).mulVec (Φ.symm w))))) := by
      intro w
      rw [Representation.Equiv.symm_apply_apply, Matrix.map_mul, ← Matrix.mulVec_mulVec]
    rw [h1, h1, hY, hY']
  have hsc : ∀ c : ZMod 2, P (Matrix.diagonal fun _ => algebraMap (ZMod 2) (EndRing ρ) c) := by
    intro c v
    have hz : fr (ιD (algebraMap (ZMod 2) (EndRing ρ) c)) =
        ιD (algebraMap (ZMod 2) (EndRing ρ) c) :=
      DFunLike.congr_fun (RingHom.ext_zmod (fr.comp (ιD.comp (algebraMap (ZMod 2) (EndRing ρ))))
        (ιD.comp (algebraMap (ZMod 2) (EndRing ρ)))) c
    have hdiag : ∀ x : Fin m → E,
        ((Matrix.diagonal fun _ => algebraMap (ZMod 2) (EndRing ρ) c).map ιD).mulVec x =
          ιD (algebraMap (ZMod 2) (EndRing ρ) c) • x := by
      intro x
      rw [Matrix.diagonal_map ιD.map_zero]
      funext i
      simp [Matrix.mulVec_diagonal]
    rw [hdiag, hdiag, map_smul, map_smul, Representation.Equiv.apply_symm_apply,
      Representation.Equiv.apply_symm_apply, hΘsmul, hz]
  have hgen : ∀ g, P (matRep b g) := by
    intro g v
    have h1 : ∀ w, Φ (((matRep b g).map ιD).mulVec (Φ.symm w)) = frobTensor F E J g w := by
      intro w
      rw [← matRepE_apply, equiv_apply Φ g, Representation.Equiv.apply_symm_apply]
    rw [h1, h1, hΘT]
  have key := density_closure b P hadd hmul hsc hgen (Matrix.diagonal fun _ => c)
  have hdiag : ∀ x : Fin m → E, ((Matrix.diagonal fun _ => c).map ιD).mulVec x = ιD c • x := by
    intro x
    rw [Matrix.diagonal_map ιD.map_zero]
    funext i
    simp [Matrix.mulVec_diagonal]
  let x0 : J → Fin 2 := fun _ => 0
  have h5 := key (Pi.single x0 1)
  rw [hdiag, hdiag, map_smul, map_smul, Representation.Equiv.apply_symm_apply,
    Representation.Equiv.apply_symm_apply, hΘsmul] at h5
  have h6 := congrFun h5 (fun i => x0 (π.symm i))
  have h7 : Θ (Pi.single x0 1) (fun i => x0 (π.symm i)) = 1 := by
    show fr ((Pi.single x0 (1 : E) : (J → Fin 2) → E) (fun i => x0 (π.symm (π i)))) = 1
    simp
  simp only [Pi.smul_apply, smul_eq_mul, h7, mul_one] at h6
  rw [← hfr]
  exact h6

theorem card_endRing_le_of_shift {n : ℕ} (hF : Fintype.card F = 2 ^ n) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E] [CharP E 2] [Algebra F E]
    (ιD : EndRing ρ →+* E) {J : Finset ℕ} (hJn : ∀ i ∈ J, i < n)
    (Φ : (matRepE b ιD).Equiv (frobTensor F E J)) {e : ℕ} (he1 : 1 ≤ e)
    (he : J.image (fun i => (i + e) % n) = J) : Nat.card (EndRing ρ) ≤ 2 ^ e := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Fintype (EndRing ρ) := Fintype.ofFinite _
  have hroot : ∀ c : EndRing ρ, c ^ 2 ^ e = c := fun c =>
    ιD.injective (by rw [map_pow]; exact pow_shift_endRing hF b ιD hJn Φ he c)
  have h2e : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
  set p : Polynomial (EndRing ρ) := Polynomial.X ^ 2 ^ e - Polynomial.X
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (EndRing ρ) h2e
  have hsub : (Finset.univ : Finset (EndRing ρ)) ⊆ p.roots.toFinset := by
    intro c _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    simp [p, hroot c]
  calc Nat.card (EndRing ρ) = (Finset.univ : Finset (EndRing ρ)).card := by
        rw [Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ = 2 ^ e := FiniteField.X_pow_card_sub_X_natDegree_eq (EndRing ρ) h2e

end MinPeriod

section Numerics

theorem two_mul_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  have h1 : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem num_outer_lin {n s d m w c : ℕ} (hns : n = 2 * s) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hds : d ≤ s) (horb : n ≤ 2 * m * d) (hw : w = d * 2 ^ (2 * m))
    (hc : c = d * (2 ^ m * (2 ^ m + 1) / 2)) :
    (m = 1 ∧ d = s ∧ w - c = s ∧ w = 4 * s) ∨ 3 * s ≤ w - c := by
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ m = 2 * (r + 1) :=
    ⟨2 ^ (m - 1) - 1, by
      have h1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h2 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
      omega⟩
  have hmr : m ≤ r + 1 := by
    have h1 : m - 1 < 2 ^ (m - 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hpow : 2 ^ (2 * m) = 4 * (r + 1) * (r + 1) := by
    rw [pow_mul', hr]
    ring
  have hhalf : 2 ^ m * (2 ^ m + 1) / 2 = (r + 1) * (2 * r + 3) := by
    rw [hr, show 2 * (r + 1) * (2 * (r + 1) + 1) = 2 * ((r + 1) * (2 * r + 3)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hpow] at hw
  rw [hhalf] at hc
  have hwc : w = c + d * (r + 1) * (2 * r + 1) := by
    rw [hw, hc]
    ring
  have hsub : w - c = d * (r + 1) * (2 * r + 1) := by omega
  rw [hsub]
  rcases Nat.lt_or_ge r 1 with hr0 | hr1
  · have hr0' : r = 0 := by omega
    subst hr0'
    have hm1 : m = 1 := by omega
    subst hm1
    left
    refine ⟨rfl, by omega, by omega, ?_⟩
    rw [hw]
    omega
  · right
    have hs : s ≤ m * d := by
      rw [hns] at horb
      nlinarith
    have h1 : m * d ≤ (r + 1) * d := Nat.mul_le_mul_right d hmr
    have h2 : 3 * ((r + 1) * d) ≤ d * (r + 1) * (2 * r + 1) := by nlinarith
    omega

end Numerics

section Dims

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem natCard_eq_two_pow : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
  have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  rwa [Nat.card_zmod] at this

theorem finrank_eq_of_natCard {k : ℕ} (h : Nat.card W = 2 ^ k) : Module.finrank (ZMod 2) W = k :=
  Nat.pow_right_injective le_rfl (natCard_eq_two_pow.symm.trans h)

theorem natCard_fixed_eq (a : Module.End (ZMod 2) W) :
    Nat.card {w : W // a w = w} = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) := by
  rw [← natCard_eq_two_pow]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero])

end Dims

section Factor

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W]

theorem two_mul_le_finrank {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) (hirr : ρ.IsIrreducible) (hnt : ∃ g, ρ g ≠ 1) :
    2 * n ≤ Module.finrank (ZMod 2) W := by
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  obtain ⟨d, hd1, hDcard, hdesc⟩ := binary_SL2_irreducible_Frobenius_descent hn hF ρ hnt
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨_, _, _, _, ιF, ιD, J, hJne, hJn, -, hshift, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  have hw : Module.finrank (ZMod 2) W = d * 2 ^ J.card := by
    apply finrank_eq_of_natCard
    rw [natCard_eq_pow_finrank (ρ := ρ), hdim, hDcard, ← pow_mul]
  have horb := n_le_card_mul (by omega) (by omega) hJn hJne hshift
  have hJ := two_mul_le_two_pow (Finset.card_pos.mpr hJne)
  rw [hw]
  calc 2 * n ≤ 2 * J.card * d := by rw [mul_assoc]; omega
    _ ≤ 2 ^ J.card * d := Nat.mul_le_mul_right d hJ
    _ = d * 2 ^ J.card := mul_comm _ _

theorem eq_one_or_eq_of_mem_zpowers {M : Type*} [Group M] {g x : M} (hg : g * g = 1)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [zpow_eq_zpow_emod k (n := 2) (by rw [zpow_two, hg])]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem finrank_le_or_orth_or {n : ℕ} (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (a : Module.End (ZMod 2) W) (ha2 : a * a = 1) (τ : SL(2, F) → SL(2, F))
    (hτ : ∀ g, a * ρ g = ρ (τ g) * a) (hτ1 : ∃ g, τ g ≠ g) :
    Module.finrank (ZMod 2) W ≤
        2 * (Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) (LinearMap.ker (a - 1))) ∨
      (∃ s, n = 2 * s ∧
        Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) = s ∧
        Module.finrank (ZMod 2) W = 4 * s ∧
        ∃ hs : Fintype.card F = 2 ^ (2 * s), CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hs ρ) ∨
      (∃ s, n = 2 * s ∧
        3 * s ≤ Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) (LinearMap.ker (a - 1))) := by
  classical
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρU := ρ.toHomUnits with hρU_def
  have hρU_val : ∀ g, (ρU g).val = ρ g := fun g => by rw [hρU_def]; rfl
  have hρUinj : Function.Injective ρU := fun g h e =>
    hρ (by simpa [hρU_val] using congrArg Units.val e)
  have hne : (uElt (1 : F) : SL(2, F)) ≠ 1 := fun h =>
    one_ne_zero (uElt_injective (h.trans uElt_zero.symm))
  have hnt : ∃ g, ρ g ≠ 1 := ⟨uElt 1, fun h => hne (hρ (h.trans (map_one ρ).symm))⟩
  have haa : ∀ w, a (a w) = w := fun w => by
    rw [← Module.End.mul_apply, ha2, Module.End.one_apply]
  have hττ : ∀ g, τ (τ g) = g := fun g => hρ (by
    calc ρ (τ (τ g)) = ρ (τ (τ g)) * (a * a) := by rw [ha2, mul_one]
      _ = (a * ρ (τ g)) * a := by rw [hτ (τ g), mul_assoc]
      _ = a * (a * ρ g) := by rw [mul_assoc, ← hτ g]
      _ = ρ g := by rw [← mul_assoc, ha2, one_mul])
  let aU : (Module.End (ZMod 2) W)ˣ := ⟨a, a, ha2, ha2⟩
  have haU : aU.val = a := rfl
  have haU2 : aU * aU = 1 := Units.ext ha2
  have haUinv : aU⁻¹ = aU := inv_eq_of_mul_eq_one_right haU2
  have hconjU : ∀ g, aU * ρU g * aU⁻¹ = ρU (τ g) := by
    intro g
    apply Units.ext
    rw [haUinv, Units.val_mul, Units.val_mul, haU, hρU_val, hρU_val, hτ g, mul_assoc, ha2,
      mul_one]
  set w := Module.finrank (ZMod 2) W with hw_def
  set c := Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) with hc_def
  have hCcard : Nat.card {x : W // a x = x} = 2 ^ c := natCard_fixed_eq a
  have hWcard : Nat.card W = 2 ^ w := natCard_eq_two_pow
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := n) (by omega) hF ρ hnt
  have hDfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  set b := Module.finBasis (EndRing ρ) W
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  let _ : Algebra F E := ιF.toAlgebra
  have hwJ : w = d * 2 ^ J.card := by
    apply finrank_eq_of_natCard
    rw [natCard_eq_pow_finrank (ρ := ρ), hdim, hDcard, ← pow_mul]
  by_cases hin : aU ∈ ρU.range
  ·
    left
    obtain ⟨x, hx⟩ := hin
    have hxa : ρ x = a := by rw [← hρU_val, hx]
    have hx2 : x * x = 1 := hρ (by rw [map_mul, hxa, ha2, map_one])
    have hx1 : x ≠ 1 := by
      rintro rfl
      obtain ⟨g, hg⟩ := hτ1
      apply hg
      apply hρ
      have h := hτ g
      rw [← hxa, map_one, one_mul, mul_one] at h
      exact h.symm
    have hCg := natCard_fixW_involution ρ b ιF ιD J hJne Φ x hx1 hx2
    rw [hDcard, ← pow_mul] at hCg
    have hc : c = d * 2 ^ (J.card - 1) := by
      have h : 2 ^ c = 2 ^ (d * 2 ^ (J.card - 1)) := by
        rw [← hCcard, ← hCg]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by rw [hxa])
      exact Nat.pow_right_injective le_rfl h
    have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
    have h2 : 2 ^ J.card = 2 * 2 ^ (J.card - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : w = 2 * c := by
      rw [hwJ, hc, h2]
      ring
    omega
  by_cases hlin : ∀ δ : EndRing ρ, a * epsHom ρ δ = epsHom ρ δ * a
  ·
    right
    haveI hE : CFSG.IsElementaryAbelian 2 (Subgroup.zpowers aU) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two, haU2])
    have hAN : Subgroup.zpowers aU ≤
        Subgroup.normalizer (ρU.range : Set (Module.End (ZMod 2) W)ˣ) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨τ g, (hconjU g).symm⟩
      · rintro ⟨g, hg⟩
        refine ⟨τ g, ?_⟩
        rw [← hconjU g, hg, haUinv]
        calc aU * (aU * h * aU) * aU = (aU * aU) * h * (aU * aU) := by group
          _ = h := by rw [haU2, one_mul, mul_one]
    have hAL : ¬ Subgroup.zpowers aU ≤ ρU.range := fun h => hin (h (Subgroup.mem_zpowers aU))
    obtain ⟨s, hs1, hns, -, -, a', ha'A, ha'L, x, hxconj⟩ :=
      outer_data (n := n) (by omega) ((Nat.card_eq_fintype_card (α := F)).trans hF) ρ hirr
        hρUinj (Subgroup.zpowers aU) hAN hAL
    have ha' : a' = aU := by
      rcases eq_one_or_eq_of_mem_zpowers haU2 ha'A with h | h
      · exact absurd (h ▸ Subgroup.one_mem _) ha'L
      · exact h
    rw [ha'] at hxconj
    have hF2 : Fintype.card F = 2 ^ (2 * s) := by rw [← hns]; exact hF
    have hJ2 : ∀ i ∈ J, i < 2 * s := fun i hi => hns ▸ hJn i hi
    set a'' := (ρU x)⁻¹ * aU * ρU x with ha''
    have ha''2 : a'' * a'' = 1 := by
      calc a'' * a'' = (ρU x)⁻¹ * (aU * aU) * ρU x := by simp only [ha'']; group
        _ = 1 := by rw [haU2]; group
    have hcomm' : ∀ δ : EndRing ρ, a''.val * epsHom ρ δ = epsHom ρ δ * a''.val := by
      intro δ
      have h1 : ∀ g : SL(2, F), Commute (ρU g).val (epsHom ρ δ) := by
        intro g
        apply LinearMap.ext
        intro v
        rw [hρU_val]
        exact (epsHom_commutes ρ δ g v).symm
      have h3 : Commute (ρU x)⁻¹.val (epsHom ρ δ) := by
        rw [← map_inv ρU x]
        exact h1 x⁻¹
      have h2 : Commute aU.val (epsHom ρ δ) := hlin δ
      have h4 := (h3.mul_left h2).mul_left (h1 x)
      show ((ρU x)⁻¹ * aU * ρU x).val * _ = _ * ((ρU x)⁻¹ * aU * ρU x).val
      rw [Units.val_mul, Units.val_mul]
      exact h4
    let aD : Module.End (EndRing ρ) W := linD ρ a''.val hcomm'
    have haD2 : aD * aD = 1 := by
      apply LinearMap.ext
      intro v
      have h := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val v) ha''2
      simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply] at h
      exact h
    have hconjD : ∀ g, aD * repD ρ g = repD ρ (fieldAut F s g) * aD := by
      intro g
      apply LinearMap.ext
      intro v
      have h := hxconj g
      have h' : a'' * ρU g = ρU (fieldAut F s g) * a'' := by
        calc a'' * ρU g = (a'' * ρU g * a''⁻¹) * a'' := by group
          _ = ρU (fieldAut F s g) * a'' := by rw [h]
      have h2 := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val v) h'
      simp only [Units.val_mul, Module.End.mul_apply, hρU_val] at h2
      exact h2
    obtain ⟨hJs, m', hm', hCa'⟩ := outer_involution_count ρ b ιD J Φ hs1 hF2 hJ2 aD haD2 hconjD
    have hc : c = d * (2 ^ m' * (2 ^ m' + 1) / 2) := by
      have h : 2 ^ c = 2 ^ (d * (2 ^ m' * (2 ^ m' + 1) / 2)) := by
        rw [← hCcard, pow_mul, ← hDcard, ← hCa', ← natCard_fixed_conj_units aU (ρU x)]
        rfl
      exact Nat.pow_right_injective le_rfl h
    have hm1 : 1 ≤ m' := by
      have := Finset.card_pos.mpr hJne
      omega
    have hw' : w = d * 2 ^ (2 * m') := by rw [hwJ, hm']
    have hds : d ≤ s := by
      have hshs : J.image (fun i => (i + s) % n) = J := by
        rw [hns]
        exact hJs
      have h := card_endRing_le_of_shift hF b ιD hJn Φ hs1 hshs
      rw [hDcard] at h
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
    have horb : n ≤ 2 * m' * d := hm' ▸ n_le_card_mul (by omega) (by omega) hJn hJne hshift
    rcases num_outer_lin hns hd1 hm1 hds horb hw' hc with ⟨hm1', hds', hδ, h4⟩ | h3
    · left
      refine ⟨s, hns, hδ, h4, hF2, ?_⟩
      have hD : Nat.card (EndRing ρ) = 2 ^ s := by rw [hDcard, hds']
      have hdim4 : Module.finrank (EndRing ρ) W = 4 := by rw [hdim, hm', hm1']; rfl
      exact orth_iso hs1 hF2 ρ hnt hD hdim4
    · right
      exact ⟨s, hns, h3⟩
  ·
    left
    push Not at hlin
    obtain ⟨δ, hδ⟩ := hlin
    obtain ⟨δ', hδ'⟩ : ∃ δ' : EndRing ρ, epsHom ρ δ' = a * epsHom ρ δ * a := by
      refine (mem_endRing_iff ρ (a * epsHom ρ δ * a)).mpr ?_ |>.imp fun ψ hψ => ?_
      · intro g v
        simp only [Module.End.mul_apply]
        have e1 : a (ρ g v) = ρ (τ g) (a v) := by
          rw [← Module.End.mul_apply, hτ g, Module.End.mul_apply]
        have e2 : ∀ v', a (ρ (τ g) v') = ρ g (a v') := by
          intro v'
          rw [← Module.End.mul_apply, hτ (τ g), hττ g, Module.End.mul_apply]
        rw [e1, epsHom_commutes, e2]
      · exact LinearMap.ext fun w => congrFun hψ w
    have hδne : δ' ≠ δ := by
      intro h
      apply hδ
      apply LinearMap.ext
      intro v
      have h1 := congrArg (fun f : Module.End (ZMod 2) W => f (a v)) hδ'
      simp only [Module.End.mul_apply, h, haa] at h1
      exact h1.symm
    have h1 := card_fixed_sq_le ⊤ a.toAddMonoidHom (epsHom ρ δ).toAddMonoidHom
      (epsHom ρ δ').toAddMonoidHom (fun v => ?_) (fun z hz => ?_) (fun u _ => AddSubgroup.mem_top _)
    · have h2 : Nat.card {u : W // u ∈ (⊤ : AddSubgroup W) ∧ a.toAddMonoidHom u = u} =
          Nat.card {v : W // a v = v} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun v => by simp)
      rw [h2, Nat.card_congr (AddSubgroup.topEquiv (G := W)).toEquiv, hCcard, hWcard, ← pow_mul]
        at h1
      have h3 : c * 2 ≤ w := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
      omega
    · show a (epsHom ρ δ v) = epsHom ρ δ' (a v)
      rw [hδ']
      simp only [Module.End.mul_apply, haa]
    · have h1 : epsHom ρ (δ - δ') z = 0 := by
        rw [map_sub, LinearMap.sub_apply]
        exact sub_eq_zero.mpr hz
      have hunit : δ - δ' ≠ 0 := sub_ne_zero.mpr hδne.symm
      have h2 : epsHom ρ (δ - δ')⁻¹ (epsHom ρ (δ - δ') z) = z := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hunit, map_one,
          Module.End.one_apply]
      rw [← h2, h1, map_zero]

@[expose] def rootSub (F : Type) [Field F] : Subgroup SL(2, F) :=
  MonoidHom.range
    { toFun := fun t : Multiplicative F => uElt (Multiplicative.toAdd t)
      map_one' := uElt_zero
      map_mul' := fun s t => uElt_add _ _ }

omit [Fintype F] in
theorem mul_self_of_mem_rootSub {u : SL(2, F)} (hu : u ∈ rootSub F) : u * u = 1 := by
  obtain ⟨t, rfl⟩ := hu
  show uElt (Multiplicative.toAdd t) * uElt (Multiplicative.toAdd t) = 1
  rw [← uElt_add, CharTwo.add_self_eq_zero, uElt_zero]

theorem natCard_rootSub : Nat.card (rootSub F) = Fintype.card F := by
  rw [rootSub, ← Nat.card_eq_fintype_card]
  refine (Nat.card_congr (MonoidHom.ofInjective (f :=
    { toFun := fun t : Multiplicative F => uElt (Multiplicative.toAdd t)
      map_one' := uElt_zero
      map_mul' := fun s t => uElt_add _ _ }) ?_).toEquiv.symm).trans ?_
  · intro s t h
    exact Multiplicative.toAdd.injective (uElt_injective h)
  · exact Nat.card_congr Multiplicative.toAdd

theorem nat_or_orth_or_eight {n : ℕ} (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) (hirr : ρ.IsIrreducible) (hnt : ∃ g, ρ g ≠ 1)
    (hdim : Module.finrank (ZMod 2) W ≤ 2 * n + 2) :
    IsNaturalModule ρ ∨
      (∃ l, ∃ hl : Fintype.card F = 2 ^ (2 * l), n = 2 * l ∧
        CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hl ρ) ∨
      (n = 3 ∧ Module.finrank (ZMod 2) W = 8) := by
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hlt : Nat.card W < 2 ^ (4 * n) := by
    rw [natCard_eq_two_pow]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt (by omega)
      hF ρ hnt (rootSub F) (fun u hu => mul_self_of_mem_rootSub hu)
      (natCard_rootSub.trans hF) hlt with h | h | ⟨l, hl3, hlW, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right
    right
    have h8 : Module.finrank (ZMod 2) W = 8 * l := finrank_eq_of_natCard hlW
    omega

end Factor

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac

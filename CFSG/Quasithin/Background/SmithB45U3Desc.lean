module

public import CFSG.Quasithin.Background.SmithB45U3Class
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram

public section

namespace CFSG.Quasithin.B45U3

open CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso fixedSub)
open scoped MatrixGroups Matrix

@[expose] def letJ (s : ℕ) (a b : Fin s → Bool) : Finset ℕ :=
  bitSupp a ∪ (bitSupp b).image (· + s)

variable {s : ℕ}

theorem bitSupp_subset (a : Fin s → Bool) : bitSupp a ⊆ Finset.range s := by
  intro j hj
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr i.2

theorem letJ_subset (a b : Fin s → Bool) : letJ s a b ⊆ Finset.range (2 * s) := by
  intro j hj
  rcases Finset.mem_union.mp hj with h | h
  · have := Finset.mem_range.mp (bitSupp_subset a h)
    exact Finset.mem_range.mpr (by omega)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    have := Finset.mem_range.mp (bitSupp_subset b hi)
    exact Finset.mem_range.mpr (by omega)

theorem disjoint_letJ (a b : Fin s → Bool) :
    Disjoint (bitSupp a) ((bitSupp b).image (· + s)) := by
  rw [Finset.disjoint_left]
  intro j ha hb
  have h1 := Finset.mem_range.mp (bitSupp_subset a ha)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
  omega

theorem sum_letJ (a b : Fin s → Bool) : ∑ j ∈ letJ s a b, 2 ^ j = wtJ s a b := by
  rw [letJ, Finset.sum_union (disjoint_letJ a b), Finset.sum_image (fun i _ j _ h => by omega),
    wtJ, mBits_eq_sum_supp, mBits_eq_sum_supp, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, mul_comm]

theorem card_bitSupp (a : Fin s → Bool) :
    (bitSupp a).card = (Finset.univ.filter fun i => a i = true).card := by
  rw [bitSupp, Finset.card_image_of_injective _ Fin.val_injective]

theorem card_letJ (a b : Fin s → Bool) : (letJ s a b).card = cntS a b + 2 * cntH a b := by
  rw [letJ, Finset.card_union_of_disjoint (disjoint_letJ a b),
    Finset.card_image_of_injective _ (fun i j h => by simpa using h), card_bitSupp,
    card_bitSupp, cntS, cntH, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases a i <;> cases b i <;> simp

theorem letJ_nonempty {a b : Fin s → Bool} (h : wtJ s a b ≠ 0) : (letJ s a b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  apply h
  rw [← sum_letJ, he, Finset.sum_empty]

theorem eq_of_sum_two_pow_eq {C C' : Finset ℕ} (h : ∑ j ∈ C, 2 ^ j = ∑ j ∈ C', 2 ^ j) :
    C = C' := by
  have h1 := congrArg (fun n => n.bitIndices.toFinset) h
  simpa only [Finset.toFinset_bitIndices_sum_two_pow] using h1

theorem sum_two_pow_lt {n : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.range n)
    (hne : C ≠ Finset.range n) : ∑ j ∈ C, 2 ^ j < 2 ^ n - 1 := by
  obtain ⟨i, hi, hiC⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hC, hne⟩)
  have h1 : ∑ j ∈ C, 2 ^ j ≤ ∑ j ∈ (Finset.range n).erase i, 2 ^ j :=
    Finset.sum_le_sum_of_subset (fun j hj => Finset.mem_erase.mpr
      ⟨fun h => hiC (h ▸ hj), hC hj⟩)
  have h2 := Finset.sum_erase_add (Finset.range n) (fun j => 2 ^ j) hi
  have h3 : ∑ j ∈ Finset.range n, 2 ^ j = 2 ^ n - 1 := by
    rw [Nat.geomSum_eq (le_refl 2)]
    simp
  have h4 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  omega

theorem shiftSet_eq_of_modEq {n d : ℕ} (hn : 1 ≤ n) {C : Finset ℕ}
    (hC : C ⊆ Finset.range (2 * n)) (hfull : C ≠ Finset.range (2 * n))
    (hmod : 2 ^ d * ∑ j ∈ C, 2 ^ j ≡ ∑ j ∈ C, 2 ^ j [MOD 2 ^ (2 * n) - 1]) :
    CFSG.QuasithinUnique.Setup.X7b.shiftSet n d C = C := by
  set C' := CFSG.QuasithinUnique.Setup.X7b.shiftSet n d C with hC'
  have hinj : Set.InjOn (fun i => (i + d) % (2 * n)) C := by
    intro i hi j hj h
    have hi' := Finset.mem_range.mp (hC hi)
    have hj' := Finset.mem_range.mp (hC hj)
    have h' : (i + d) % (2 * n) = (j + d) % (2 * n) := h
    have := Nat.ModEq.add_right_cancel' d h'
    exact Nat.ModEq.eq_of_lt_of_lt this hi' hj'
  have hcard : C'.card = C.card := Finset.card_image_of_injOn hinj
  have hC'sub : C' ⊆ Finset.range (2 * n) :=
    CFSG.QuasithinUnique.Setup.X7b.shiftSet_subset hn d C
  have hval : ∑ j ∈ C', 2 ^ j ≡ 2 ^ d * ∑ j ∈ C, 2 ^ j [MOD 2 ^ (2 * n) - 1] := by
    rw [hC', CFSG.QuasithinUnique.Setup.X7b.shiftSet, Finset.sum_image hinj, Finset.mul_sum]
    refine Nat.ModEq.sum fun j _ => ?_
    have h1 : 2 ^ (2 * n) ≡ 1 [MOD 2 ^ (2 * n) - 1] := by
      have h2 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
      exact Nat.modEq_sub h2
    calc 2 ^ ((j + d) % (2 * n)) = 2 ^ ((j + d) % (2 * n)) * 1 ^ ((j + d) / (2 * n)) := by
          rw [one_pow, mul_one]
      _ ≡ 2 ^ ((j + d) % (2 * n)) * (2 ^ (2 * n)) ^ ((j + d) / (2 * n))
          [MOD 2 ^ (2 * n) - 1] := (Nat.ModEq.refl _).mul (h1.symm.pow _)
      _ = 2 ^ d * 2 ^ j := by
          rw [← pow_mul, ← pow_add, Nat.mod_add_div, pow_add, mul_comm]
  have hfull' : C' ≠ Finset.range (2 * n) := by
    intro h
    apply hfull
    refine Finset.eq_of_subset_of_card_le hC ?_
    rw [← hcard, h]
  have heq : ∑ j ∈ C', 2 ^ j = ∑ j ∈ C, 2 ^ j :=
    Nat.ModEq.eq_of_lt_of_lt (hval.trans hmod) (sum_two_pow_lt hC'sub hfull')
      (sum_two_pow_lt hC hfull)
  exact eq_of_sum_two_pow_eq heq

theorem two_mul_le_card_mul {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) {C : Finset ℕ}
    (hC : C ⊆ Finset.range (2 * n)) (hne : C.Nonempty)
    (hmod : 2 ^ d * ∑ j ∈ C, 2 ^ j ≡ ∑ j ∈ C, 2 ^ j [MOD 2 ^ (2 * n) - 1]) :
    2 * n ≤ C.card * d := by
  by_cases hfull : C = Finset.range (2 * n)
  · rw [hfull, Finset.card_range]
    exact Nat.le_mul_of_pos_right _ hd
  exact CFSG.QuasithinUnique.Setup.SL2Modules.n_le_card_mul (by omega) (by omega)
    (fun i hi => Finset.mem_range.mp (hC hi)) hne (shiftSet_eq_of_modEq hn hC hfull hmod)

theorem dvd_of_modEq_single {n d j : ℕ} (hn : 1 ≤ n) (hj : j < 2 * n)
    (hmod : 2 ^ d * 2 ^ j ≡ 2 ^ j [MOD 2 ^ (2 * n) - 1]) : 2 * n ∣ d := by
  have hsub : ({j} : Finset ℕ) ⊆ Finset.range (2 * n) :=
    Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hj)
  have hfull : ({j} : Finset ℕ) ≠ Finset.range (2 * n) := by
    intro h
    have := congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_range] at this
    omega
  have h := shiftSet_eq_of_modEq hn hsub hfull (by simpa using hmod)
  have h1 : (j + d) % (2 * n) ∈ ({j} : Finset ℕ) := by
    rw [← h]
    exact Finset.mem_image_of_mem _ (Finset.mem_singleton_self j)
  have h2 : (j + d) % (2 * n) = j % (2 * n) := by
    rw [Finset.mem_singleton.mp h1, Nat.mod_eq_of_lt hj]
  have h3 : j + d ≡ j + 0 [MOD 2 * n] := by rw [add_zero]; exact h2
  exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_left_cancel' j h3)

section Frob

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable (E : Type) [Field E] [Algebra K E] [CharP E 2]

omit [Finite K] [CharP K 2] [CharP E 2] in
theorem comp_hw (φ : E →+* E) (a b : Fin s → Bool) : φ ∘ hw E a b = hw E a b := by
  funext x
  simp only [Function.comp_apply, hw, hwVec]
  by_cases h : x = fun i => locDist (a i) (b i)
  · subst h
    simp
  · simp [h]

omit [Finite K] [CharP K 2] [CharP E 2] in
theorem map_mulVec_hw (φ : E →+* E) (a b : Fin s → Bool) (M : Matrix (TIdx s a b) (TIdx s a b) E) :
    (M.map φ).mulVec (hw E a b) = φ ∘ (M.mulVec (hw E a b)) := by
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec, comp_hw]

theorem fixed_frob_TJ [Finite E] (hK : Nat.card K = (2 ^ s) ^ 2) (φ : E →+* E)
    (a b : Fin s → Bool) {v : TIdx s a b → E}
    (hv : ∀ u ∈ UJ K s, ((TJ (K := K) E a b u).map φ).mulVec v = v) :
    ∃ c : E, v = c • hw E a b := by
  have hbij : Function.Bijective φ :=
    ⟨φ.injective, Finite.surjective_of_injective φ.injective⟩
  let ψ := RingEquiv.ofBijective φ hbij
  set w : TIdx s a b → E := fun x => ψ.symm (v x) with hwdef
  have hφw : φ ∘ w = v := funext fun x => ψ.apply_symm_apply (v x)
  have hwfix : w ∈ fixedSub (matRep (TJ (K := K) E a b)) (UJ K s) := by
    intro u hu
    rw [matRep_apply]
    funext i
    apply φ.injective
    rw [RingHom.map_mulVec, hφw, hv u hu, ← hφw]
    rfl
  rw [(TJ_fixed_irreducible E hK a b).1, Submodule.mem_span_singleton] at hwfix
  obtain ⟨c, hc⟩ := hwfix
  refine ⟨φ c, ?_⟩
  rw [← hφw, ← hc]
  funext x
  have := congrFun (comp_hw E φ a b) x
  simp only [Function.comp_apply] at this
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, this]

theorem wtJ_modEq_of_frob [Finite E] (hK : Nat.card K = (2 ^ s) ^ 2) {a b : Fin s → Bool}
    {κ : Type} [Fintype κ] [DecidableEq κ] (R : suJ K s →* Matrix κ κ E) (d : ℕ)
    (hR : ∀ g, (R g).map (iterateFrobenius E 2 d) = R g)
    (Φ : (matRep (TJ (K := K) E a b)).Equiv (matRep R)) :
    2 ^ d * wtJ s a b ≡ wtJ s a b [MOD (2 ^ s) ^ 2 - 1] := by
  classical
  set φ : E →+* E := iterateFrobenius E 2 d with hφ
  obtain ⟨P, Q, h⟩ := MatIso.exists_of_equiv Φ
  have h1 := h.map φ
  have hR' : matMap φ R = R := MonoidHom.ext fun g => hR g
  rw [hR'] at h1
  have h2 := h.trans h1.symm
  obtain ⟨A, hA⟩ : ∃ A, A = Q.map φ * P := ⟨_, rfl⟩
  rw [← hA] at h2
  have hfix : ∀ u ∈ UJ K s, ((TJ (K := K) E a b u).map φ).mulVec (A.mulVec (hw E a b)) =
      A.mulVec (hw E a b) := by
    intro u hu
    have hc := h2.comm u
    rw [matMap_apply] at hc
    rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec]
    obtain ⟨x, y, z, hxyz⟩ := mem_upperUni.mp (mem_UJ.mp hu)
    rw [TJ_apply, hxyz, tensorRep_up3_fixed]
  obtain ⟨c, hc⟩ := fixed_frob_TJ E hK φ a b hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    apply hw_ne_zero E a b
    have h3 := h2.inv_mul
    rw [← Matrix.one_mulVec (hw E a b), ← h3, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  have hchar : ∀ r : Kˣ, algebraMap K E (r : K) ^ wtJ s a b =
      algebraMap K E (r : K) ^ (2 ^ d * wtJ s a b) := by
    intro r
    have h3 := congrArg (fun M => M.mulVec (hw E a b)) (h2.comm (hJ hK r))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, TJ_hJ_hw E hK, Matrix.mulVec_smul, hc,
      Matrix.mulVec_smul, matMap_apply, map_mulVec_hw, TJ_hJ_hw E hK, smul_smul] at h3
    have h4 : (φ ∘ (algebraMap K E (r : K) ^ (mBits a + 2 ^ s * mBits b) • hw E a b)) =
        φ (algebraMap K E (r : K) ^ (mBits a + 2 ^ s * mBits b)) • hw E a b := by
      funext x
      have := congrFun (comp_hw E φ a b) x
      simp only [Function.comp_apply] at this
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, this]
    rw [h4, smul_smul] at h3
    have h5 := smul_left_injective E (hw_ne_zero E a b) h3
    have h6 : algebraMap K E (r : K) ^ (mBits a + 2 ^ s * mBits b) =
        φ (algebraMap K E (r : K) ^ (mBits a + 2 ^ s * mBits b)) :=
      mul_left_cancel₀ hc0 (by rw [mul_comm]; exact h5)
    rw [hφ, iterateFrobenius_def, ← pow_mul] at h6
    unfold wtJ
    rw [mul_comm (2 ^ d)]
    exact h6
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (2 ^ s) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hgpow : g ^ wtJ s a b = g ^ (2 ^ d * wtJ s a b) := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    apply (algebraMap K E).injective
    rw [map_pow, map_pow]
    exact hchar g)
  have := pow_eq_pow_iff_modEq.mp hgpow
  rw [hord] at this
  exact this.symm

end Frob

section Label

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) (suJ K s) W} [Fact ρ.IsIrreducible]

open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing matRepE matRepE_apply matRepE_isIrreducible
  repD finite_endRing)

@[expose] noncomputable def u3MatHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type} [Field E] (ι : EndRing ρ →+* E) : suJ K s →* Matrix (Fin m) (Fin m) E :=
  matMap ι (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b)

theorem u3MatHomE_apply {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) (g : suJ K s) :
    u3MatHomE b ι g = (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ι := rfl

theorem matRep_u3MatHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) : matRep (u3MatHomE b ι) = matRepE b ι := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  rw [matRep_apply, matRepE_apply, u3MatHomE_apply]

omit [Finite W] [Fact ρ.IsIrreducible] in
theorem TJ_zeros (k : Type) [Field k] [Algebra K k] [CharP k 2] (g : suJ K s) :
    TJ (K := K) k (zeros s) (zeros s) g = 1 := by
  rw [TJ_apply]
  show kron _ = 1
  have : (fun i : Fin s => locRep (F := K) k (zeros s i, zeros s i).1
      (zeros s i, zeros s i).2 (i : ℕ) (g : SL(3, K))) = fun _ => 1 := by
    funext i
    rfl
  rw [this]
  exact kron_one

theorem u3_exists_label (hK : Nat.card K = (2 ^ s) ^ 2) (hnt : ∃ g, ρ g ≠ 1) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [CharP E 2] (ιK : K →+* E)
    (ιD : EndRing ρ →+* E) :
    ∃ a b' : Fin s → Bool, wtJ s a b' ≠ 0 ∧
      (letI := ιK.toAlgebra
       Nonempty ((matRep (TJ (K := K) E a b')).Equiv (matRepE b ιD))) ∧
      m = Fintype.card (TIdx s a b') := by
  classical
  let _ : Algebra K E := ιK.toAlgebra
  have hirr := matRepE_isIrreducible b ιD
  obtain ⟨a, b', ⟨Φ⟩⟩ := exists_TJ_equiv E hK (matRepE b ιD) hirr
  have hdimE : m = Fintype.card (TIdx s a b') := by
    have h1 := Φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at h1
    exact h1.symm
  refine ⟨a, b', fun h0 => ?_, ⟨Φ⟩, hdimE⟩
  obtain ⟨rfl, rfl⟩ := eq_zeros_of_wtJ h0
  obtain ⟨g, hg⟩ := hnt
  apply hg
  have hid : ∀ x, matRepE b ιD g x = x := by
    intro x
    have h1 := repEquiv_apply E Φ g (Φ.symm x)
    rw [Representation.Equiv.apply_symm_apply] at h1
    rw [← h1, matRep_apply, TJ_zeros, Matrix.one_mulVec, Representation.Equiv.apply_symm_apply]
  have hmat : (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    have := hid x
    rw [matRepE_apply] at this
    simpa [Matrix.toLin'_apply] using this
  have hmat' : CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g = 1 := by
    have : (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD =
        (1 : Matrix (Fin _) (Fin _) (EndRing ρ)).map ιD := by
      rw [hmat, Matrix.map_one ιD (map_zero ιD) (map_one ιD)]
    exact Matrix.map_injective ιD.injective this
  have hrep : repD ρ g = 1 := by
    apply (LinearMap.toMatrix b b).injective
    rw [show LinearMap.toMatrix b b (repD ρ g) =
      CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g from rfl, hmat', LinearMap.toMatrix_one]
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun φ : Module.End (EndRing ρ) W => φ w) hrep
  have h2 : repD ρ g w = w := by simpa using h1
  exact h2

theorem u3_descent (hK : Nat.card K = (2 ^ s) ^ 2) (hnt : ∃ g, ρ g ≠ 1) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card (EndRing ρ) = 2 ^ d ∧
      ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W,
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (ιK : K →+* E)
        (ιD : EndRing ρ →+* E) (a b' : Fin s → Bool), wtJ s a b' ≠ 0 ∧
        (letI := ιK.toAlgebra
         Nonempty ((matRep (TJ (K := K) E a b')).Equiv (matRepE b ιD))) ∧
        2 ^ d * wtJ s a b' ≡ wtJ s a b' [MOD (2 ^ s) ^ 2 - 1] ∧
        Module.finrank (EndRing ρ) W = Fintype.card (TIdx s a b') := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (ZMod 2) (EndRing ρ) := Module.Finite.of_finite
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank (ZMod 2) (EndRing ρ) = d := ⟨_, rfl⟩
  have hDcard : Nat.card (EndRing ρ) = 2 ^ d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing ρ)
    rw [hd, Nat.card_zmod] at this
    exact this
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      have h1 : Nat.card (EndRing ρ) = 1 := by rw [hDcard]; rfl
      have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (EndRing ρ))
      omega
    · exact h
  refine ⟨d, hd1, hDcard, fun b => ?_⟩
  have : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have hs := one_le_s hK
  have hK' : Nat.card K = 2 ^ (2 * s) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨e, E, hEF, hEfin, hEchar, ιK, ιD, -, -, -, -, -, -, -, hfrobD, -⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.finite_fields_common_extension 2
      (by omega : 1 ≤ 2 * s) hd1 hK' hDcard
  let _ : Algebra K E := ιK.toAlgebra
  obtain ⟨a, b', hab, ⟨Φ⟩, hdimW⟩ := u3_exists_label hK hnt b ιK ιD
  have hmod : 2 ^ d * wtJ s a b' ≡ wtJ s a b' [MOD (2 ^ s) ^ 2 - 1] := by
    refine wtJ_modEq_of_frob E hK (u3MatHomE b ιD) d (fun g => ?_)
      (Φ.trans (Representation.Equiv.mk (LinearEquiv.refl E _) (fun g => ?_)))
    · ext i j
      rw [Matrix.map_apply, u3MatHomE_apply, Matrix.map_apply, iterateFrobenius_def]
      exact hfrobD _
    · rw [matRep_u3MatHomE]
      rfl
  exact ⟨E, hEF, hEfin, hEchar, ιK, ιD, a, b', hab, ⟨Φ⟩, hmod, hdimW⟩

end Label

end CFSG.Quasithin.B45U3

module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofL3

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

namespace Item228CensusProof

theorem mul_sub_algebraMap_eq {K R : Type*} [Field K] [CommRing R] [Algebra K R] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (x : R) :
    (x - algebraMap K R 1) * ((x - algebraMap K R ω) * (x - algebraMap K R (ω ^ 2))) =
      x ^ 3 - 1 := by
  have hw : algebraMap K R ω ^ 2 + algebraMap K R ω + 1 = 0 := by
    rw [← map_pow, ← map_one (algebraMap K R), ← map_add, ← map_add, hω, map_zero]
  rw [map_one, map_pow]
  linear_combination (-x ^ 2 + algebraMap K R ω * x - algebraMap K R ω + 1) * hw

theorem exists_smul_eq_of_isSimpleModule {K : Type*} [Field K] {A : Type*} [CommGroup A] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (S : Type*) [AddCommGroup S] [Module K S]
    [Module (MonoidAlgebra K A) S] [IsScalarTower K (MonoidAlgebra K A) S]
    [IsSimpleModule (MonoidAlgebra K A) S] {a : A} (ha : a ^ 3 = 1) :
    ∃ t : K, t ^ 3 = 1 ∧ ∀ v : S, MonoidAlgebra.of K A a • v = t • v := by
  have : Nontrivial S := IsSimpleModule.nontrivial (MonoidAlgebra K A) S
  set x : MonoidAlgebra K A := MonoidAlgebra.of K A a with hxdef
  have hx3 : x ^ 3 = 1 := by rw [hxdef, ← map_pow, ha, map_one]
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  let g : K → (S →ₗ[MonoidAlgebra K A] S) := fun t =>
    LinearMap.lsmul (MonoidAlgebra K A) S (x - algebraMap K (MonoidAlgebra K A) t)
  have hg : ∀ t v, g t v = (x - algebraMap K (MonoidAlgebra K A) t) • v := fun t v => rfl
  have hcomp : ∀ v : S, g 1 (g ω (g (ω ^ 2) v)) = 0 := by
    intro v
    rw [hg, hg, hg, smul_smul, smul_smul, mul_assoc, mul_sub_algebraMap_eq hω, hx3, sub_self,
      zero_smul]
  have key : ∃ t : K, t ^ 3 = 1 ∧ g t = 0 := by
    by_contra hne
    push Not at hne
    have h1 := ((g 1).bijective_or_eq_zero).resolve_right (hne 1 (one_pow 3))
    have h2 := ((g ω).bijective_or_eq_zero).resolve_right (hne ω hω3)
    have h3 := ((g (ω ^ 2)).bijective_or_eq_zero).resolve_right (hne (ω ^ 2)
      (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]))
    obtain ⟨v, hv⟩ := exists_ne (0 : S)
    apply hv
    apply h3.1
    apply h2.1
    apply h1.1
    rw [hcomp, map_zero, map_zero, map_zero]
  obtain ⟨t, ht3, ht⟩ := key
  refine ⟨t, ht3, fun v => ?_⟩
  have hv := LinearMap.congr_fun ht v
  rw [hg, LinearMap.zero_apply, sub_smul, algebraMap_smul, sub_eq_zero] at hv
  exact hv

theorem finrank_eq_one_of_forall_smul_eq {K : Type*} [Field K] {A : Type*} [Group A]
    (S : Type*) [AddCommGroup S] [Module K S] [Module (MonoidAlgebra K A) S]
    [IsScalarTower K (MonoidAlgebra K A) S] [IsSimpleModule (MonoidAlgebra K A) S]
    (h : ∀ a : A, ∃ t : K, ∀ v : S, MonoidAlgebra.of K A a • v = t • v) :
    Module.finrank K S = 1 := by
  have : Nontrivial S := IsSimpleModule.nontrivial (MonoidAlgebra K A) S
  obtain ⟨v, hv⟩ := exists_ne (0 : S)
  have hmem : ∀ r : MonoidAlgebra K A, r • v ∈ K ∙ v := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of a =>
      obtain ⟨t, ht⟩ := h a
      rw [ht]
      exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self v)
    | add r s hr hs =>
      rw [add_smul]
      exact Submodule.add_mem _ hr hs
    | smul k r hr =>
      rw [smul_assoc]
      exact Submodule.smul_mem _ k hr
  have hspan : Submodule.span (MonoidAlgebra K A) {v} = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (Submodule.span (MonoidAlgebra K A) {v}) with h0 | h0
    · exfalso
      apply hv
      rw [← Submodule.mem_bot (MonoidAlgebra K A), ← h0]
      exact Submodule.mem_span_singleton_self v
    · exact h0
  have htop : (K ∙ v) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Submodule.span (MonoidAlgebra K A) {v} := hspan ▸ Submodule.mem_top
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact hmem r
  rw [← finrank_top K S, ← htop, finrank_span_singleton hv]

theorem exists_eigenbasis_of_isElemAbelian {K : Type} [Field K] (h3 : (3 : K) ≠ 0) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {E : Subgroup (GL (Fin 3) K)} [Finite E]
    (hE : CFSG.Open.IsElemAbelian 3 E) :
    ∃ (b : Module.Basis (Fin 3) K (Fin 3 → K)) (c : Fin 3 → E → K), ∀ (a : E) (i : Fin 3),
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c i a • b i ∧ c i a ^ 3 = 1 := by
  classical
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hE.1.is_comm.comm }
  let ρ : E →* ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp E.subtype)
  have hρ : ∀ (a : E) (v : Fin 3 → K),
      ρ a v = ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v :=
    fun a v => rfl
  have hexp : ∀ a : E, a ^ 3 = 1 := fun a => Subtype.ext (hE.2 a a.2)
  let representation := CFSG.LargeEvenClassification.Helpers.linearActionRepresentation ρ
  have : FiniteDimensional K representation.asModule :=
    LinearEquiv.finiteDimensional representation.asModuleEquiv.symm
  obtain ⟨r, hr⟩ := Census.exists_card_eq_pow_of_exponent Nat.prime_three hexp
  have : NeZero (Nat.card E : K) := ⟨by rw [hr, Nat.cast_pow]; exact pow_ne_zero r h3⟩
  obtain ⟨count, S, e, hsimple, hdim⟩ :=
    Census.maschke_decomposition (K := K) (A := E) representation.asModule
  have : ∀ i, IsSimpleModule (MonoidAlgebra K E) (S i) := hsimple
  have hact : ∀ i (a : E), ∃ t : K, t ^ 3 = 1 ∧ ∀ v : S i, MonoidAlgebra.of K E a • v = t • v :=
    fun i a => exists_smul_eq_of_isSimpleModule hω (S i) (hexp a)
  have hone : ∀ i, Module.finrank K (S i) = 1 := fun i =>
    finrank_eq_one_of_forall_smul_eq (S i) fun a => (hact i a).imp fun _ ht => ht.2
  have hcount : count = 3 := by
    rw [representation.asModuleEquiv.finrank_eq, Module.finrank_fin_fun] at hdim
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at hdim
    exact hdim.symm
  subst hcount
  choose c hc3 hc using hact
  have : ∀ i, Nontrivial (S i) := fun i => IsSimpleModule.nontrivial (MonoidAlgebra K E) (S i)
  have hw : ∀ i, ∃ w : S i, w ≠ 0 := fun i => exists_ne 0
  choose w hw0 using hw
  let u : Fin 3 → representation.asModule := fun i => e.symm (DFinsupp.single i (w i))
  have hu : ∀ (a : E) i, MonoidAlgebra.of K E a • u i = c i a • u i := by
    intro a i
    simp only [u]
    rw [← map_smul, ← DFinsupp.single_smul, hc i a (w i), DFinsupp.single_smul,
      LinearMapClass.map_smul_of_tower]
  have hli : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h2 : e (∑ j, g j • u j) = ∑ j, g j • DFinsupp.single j (w j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMapClass.map_smul_of_tower, LinearEquiv.apply_symm_apply]
    have h1 := congrArg (fun y => e y i) hg
    simp only [map_zero, DFinsupp.zero_apply] at h1
    rw [h2, DFinsupp.finsetSum_apply, Finset.sum_eq_single i] at h1
    · rw [DFinsupp.smul_apply, DFinsupp.single_eq_same] at h1
      exact (smul_eq_zero.mp h1).resolve_right (hw0 i)
    · intro j _ hji
      rw [DFinsupp.smul_apply, DFinsupp.single_eq_of_ne (Ne.symm hji), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let b₀ := basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin, representation.asModuleEquiv.finrank_eq, Module.finrank_fin_fun])
  refine ⟨b₀.map representation.asModuleEquiv, c, fun a i => ⟨?_, hc3 i a⟩⟩
  rw [Module.Basis.map_apply, coe_basisOfLinearIndependentOfCardEqFinrank, ← hρ]
  have := congrArg representation.asModuleEquiv (hu a i)
  rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of, map_smul] at this
  exact this

theorem card_le_three_of_isElemAbelian_noScalar {K : Type} [Field K] (h3 : (3 : K) ≠ 0) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {E : Subgroup (GL (Fin 3) K)} [Finite E]
    (hE : CFSG.Open.IsElemAbelian 3 E)
    (hdet : ∀ g ∈ E, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hscalar : ∀ g ∈ E, ∀ t : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = t • 1 →
      g = 1) :
    Nat.card E ≤ 3 := by
  classical
  obtain ⟨b, c, hbc⟩ := exists_eigenbasis_of_isElemAbelian h3 hω hE
  have hb0 : ∀ i, b i ≠ 0 := fun i => b.ne_zero i
  have hne : ∀ i (a : E), c i a ≠ 0 := fun i a h => by
    have h1 := (hbc a i).2
    rw [h] at h1
    norm_num at h1
  have hmul : ∀ i (a a' : E), c i (a * a') = c i a * c i a' := by
    intro i a a'
    have h1 := (hbc (a * a') i).1
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, (hbc a' i).1,
      Matrix.mulVec_smul, (hbc a i).1, smul_smul] at h1
    have h2 : (c i (a * a') - c i a * c i a') • b i = 0 := by
      rw [sub_smul, ← h1, mul_comm, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (hb0 i))
  have hone : ∀ i, c i 1 = 1 := by
    intro i
    have h1 := (hbc 1 i).1
    rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec] at h1
    have h2 : (c i 1 - 1) • b i = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (hb0 i))
  have hdetc : ∀ a : E, c 0 a * c 1 a * c 2 a = 1 := by
    intro a
    have hmat : LinearMap.toMatrix b b
        (Matrix.toLin' ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
          Matrix.diagonal fun i => c i a := by
      ext i j
      rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, (hbc a j).1, map_smul, b.repr_self,
        Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Ne.symm hij]
    have h1 := hdet a a.2
    rw [← LinearMap.det_toLin', ← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal,
      Fin.prod_univ_three] at h1
    exact h1
  have hsc : ∀ (a : E) (t : K), (∀ i, c i a = t) → a = 1 := by
    intro a t ht
    have hlin : Matrix.toLin' ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        t • LinearMap.id := by
      refine b.ext fun i => ?_
      rw [Matrix.toLin'_apply, (hbc a i).1, ht i]
      rfl
    have hmat : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = t • 1 := by
      apply Matrix.toLin'.injective
      rw [hlin, map_smul, Matrix.toLin'_one]
    exact Subtype.ext (hscalar a a.2 t hmat)
  have hinv : ∀ i (a : E), c i a⁻¹ = (c i a)⁻¹ := fun i a => by
    have h1 := hmul i a⁻¹ a
    rw [inv_mul_cancel, hone] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  let φ : E → K := fun a => c 0 a / c 2 a
  have hφ : Function.Injective φ := by
    intro a a' h
    have key : c 0 a * c 2 a' = c 0 a' * c 2 a := by
      have h1 : c 0 a / c 2 a = c 0 a' / c 2 a' := h
      rwa [div_eq_div_iff (hne 2 a) (hne 2 a')] at h1
    set t := c 0 (a' * a⁻¹) with htdef
    have h02 : c 2 (a' * a⁻¹) = t := by
      rw [htdef, hmul, hmul, hinv, hinv, ← div_eq_mul_inv, ← div_eq_mul_inv,
        div_eq_div_iff (hne 2 a) (hne 0 a)]
      linear_combination key
    have h1 : c 1 (a' * a⁻¹) = t := by
      have hd := hdetc (a' * a⁻¹)
      rw [h02, ← htdef] at hd
      have ht3 : t ^ 3 = 1 := (hbc _ 0).2
      have h2 : c 1 (a' * a⁻¹) * t ^ 2 = t * t ^ 2 := by linear_combination hd - ht3
      exact mul_right_cancel₀ (pow_ne_zero 2 (hne 0 _)) h2
    have hg := hsc (a' * a⁻¹) t (fun i => by fin_cases i <;> simp [h1, h02, htdef])
    exact (mul_inv_eq_one.mp hg).symm
  have hrange : ∀ a, φ a ∈ ({1, ω, ω ^ 2} : Finset K) := by
    intro a
    have hx3 : φ a ^ 3 = 1 := by
      simp only [φ]
      rw [div_pow, (hbc a 0).2, (hbc a 2).2, div_one]
    have hfac : (φ a - 1) * ((φ a - ω) * (φ a - ω ^ 2)) = 0 := by
      have h1 := mul_sub_algebraMap_eq (R := K) hω (φ a)
      simp only [Algebra.algebraMap_self, RingHom.id_apply] at h1
      rw [h1, hx3, sub_self]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  calc Nat.card E ≤ Nat.card ({1, ω, ω ^ 2} : Finset K) :=
        Nat.card_le_card_of_injective (fun a => ⟨φ a, hrange a⟩)
          (fun a a' h => hφ (congrArg Subtype.val h))
    _ = ({1, ω, ω ^ 2} : Finset K).card := Nat.card_eq_finsetCard _
    _ ≤ 3 := Finset.card_le_three

theorem exists_unitaryFieldData {q : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) (hq : q % 3 = 1) : ∃ p f : ℕ, q = p ^ f ∧ UnitaryFieldData p f K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, hK] at hn
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hn]; ring⟩
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨ringChar K, f, rfl, hp, ?_, by rw [hK]; ring⟩
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · subst h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    norm_num at h1
  · exact h0

theorem eq_one_of_smul_one_mem_statedSU {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (h3 : ¬ 3 ∣ p ^ f + 1) {g : GL (Fin 3) K} (hg : g ∈ StatedSU 3 (p ^ f) K) {t : K}
    (ht : (g : Matrix (Fin 3) (Fin 3) K) = t • 1) : g = 1 := by
  obtain ⟨hdet, hunit⟩ := (mem_unitarySU_iff h).mp hg
  rw [ht] at hdet hunit
  have ht3 : t ^ 3 = 1 := by simpa [Matrix.det_smul] using hdet
  have htq : t ^ (p ^ f + 1) = 1 := by
    have h00 := congrFun (congrFun hunit 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, UnitaryFieldData.bar_apply] at h00
    rw [pow_succ]
    exact h00
  have hpow : ∀ k : ℕ, t ^ k = t ^ (k % 3) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, ht3, one_pow, one_mul]
  have ht1 : t = 1 := by
    rw [hpow] at htq
    have hmod : (p ^ f + 1) % 3 = 1 ∨ (p ^ f + 1) % 3 = 2 := by omega
    rcases hmod with hm | hm
    · rw [hm, pow_one] at htq
      exact htq
    · rw [hm] at htq
      have h32 : t ^ 3 = t ^ 2 * t := by ring
      rw [ht3, htq, one_mul] at h32
      exact h32.symm
  apply Units.ext
  rw [ht, ht1, one_smul, Units.val_one]

theorem pRank_three_statedSU_le_one {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) : CFSG.pRank 3 (StatedSU 3 (p ^ f) K) ≤ 1 := by
  have := h.finite
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hK3 : Nat.card K % 3 = 1 := by rw [hK, Nat.pow_mod, hq]
  have h3 : (3 : K) ≠ 0 := by
    intro h0
    have : Fintype K := Fintype.ofFinite K
    have hc := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, ← Nat.div_add_mod (Nat.card K) 3, hK3] at hc
    push_cast at hc
    rw [h0, zero_mul, zero_add] at hc
    exact one_ne_zero hc
  have h3' : ¬ 3 ∣ p ^ f + 1 := by omega
  have hω : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      have : 1 ≤ Nat.card K := Nat.card_pos
      omega
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    refine ⟨(x : K), ?_⟩
    have hx3 : (x : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one,
      Units.val_one]
    have hx1 : (x : K) ≠ 1 := by
      intro h1
      have : x = 1 := Units.ext h1
      rw [this, orderOf_one] at hx
      norm_num at hx
    have hfac : ((x : K) - 1) * ((x : K) ^ 2 + x + 1) = 0 := by linear_combination hx3
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hx1)
  obtain ⟨ω, hω⟩ := hω
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  have hE : CFSG.Open.IsElemAbelian 3 (B.map (StatedSU 3 (p ^ f) K).subtype) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨x', hx', hxe⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨y', hy', hye⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : GL (Fin 3) K) * y = y * x
      rw [← hxe, ← hye, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hB.toIsMulCommutative.is_comm.comm ⟨x', hx'⟩
        ⟨y', hy'⟩))
    · rintro _ ⟨x, hx, rfl⟩
      have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p ⟨x, hx⟩
      have h1' : x ^ 3 = 1 := by simpa using congrArg Subtype.val h1
      rw [← map_pow, h1', map_one]
  have hle := card_le_three_of_isElemAbelian_noScalar h3 hω hE
    (fun g hg => by
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hg
      exact ((mem_unitarySU_iff h).mp x.2).1)
    (fun g hg t ht => by
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hg
      exact eq_one_of_smul_one_mem_statedSU h h3' x.2 ht)
  rw [Subgroup.card_map_of_injective (StatedSU 3 (p ^ f) K).subtype_injective, hr] at hle
  by_contra hr1
  have : 3 ^ 2 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem center_statedSU_eq_bot {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) : Subgroup.center (StatedSU 3 (p ^ f) K) = ⊥ := by
  have hq2 : 2 < p ^ f := by
    have : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
    omega
  have hZ := KFacts.center_unitarySU_three (h := h) hq2
  have hcard := card_unitaryScalars h (n := 3) (by norm_num)
  have h3 : ¬ 3 ∣ p ^ f + 1 := by omega
  have hgcd : Nat.gcd 3 (p ^ f + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  change Subgroup.center (unitarySU p f K 3) = ⊥
  rw [hZ]
  exact Subgroup.eq_bot_of_card_eq _ (hcard.trans hgcd)

end Item228CensusProof

open Item228CensusProof

theorem census228U3Rank_holds : Census228U3Rank := by
  intro q K _ _ hK hq
  obtain ⟨p, f, rfl, h⟩ := exists_unitaryFieldData hK hq
  exact pRank_quot_center_le_of_center_eq_bot (center_statedSU_eq_bot h hq)
    (pRank_three_statedSU_le_one h hq)

theorem census228L3Rest_holds : Census228L3Rest :=
  census228L3Rest_of census228U3Rank_holds

end CFSG.RankThree.PartTwo.Sec21

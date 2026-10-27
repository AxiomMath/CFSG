module

public import CFSG.RankThree.PartOne.CTP.SeitzToral
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.RankThree.PartOne.K133.KillBasic
public import CFSG.RankThree.PartOne.K133.Quot

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.GorensteinWalter Matrix Module
open scoped MatrixGroups

theorem isCyclic_of_commuting_pow_eq_one_sl2 {K : Type*} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) [NeZero (p : K)] (E : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hpow : ∀ x ∈ E, x ^ p = 1) : IsCyclic E := by
  classical
  have : Finite E := Subtype.finite
  have : NeZero p := ⟨hp.ne_zero⟩
  let L := AlgebraicClosure K
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  let φ : Matrix (Fin 2) (Fin 2) K →+* Matrix (Fin 2) (Fin 2) L :=
    (algebraMap K L).mapMatrix
  have hφinj : Function.Injective φ := fun a b h =>
    Matrix.map_injective (algebraMap K L).injective (by simpa [φ, RingHom.mapMatrix_apply] using h)
  let f : E → Module.End L (Fin 2 → L) := fun x =>
    Matrix.toLinAlgEquiv' (φ (x : Matrix (Fin 2) (Fin 2) K))
  have hf_comm : ∀ x y, Commute (f x) (f y) := fun x y => by
    have h2 : (x : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K) =
        (y : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) := by
      simpa using congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
        (hcomm x x.2 y y.2)
    have h3 : φ (x : Matrix (Fin 2) (Fin 2) K) * φ (y : Matrix (Fin 2) (Fin 2) K) =
        φ (y : Matrix (Fin 2) (Fin 2) K) * φ (x : Matrix (Fin 2) (Fin 2) K) := by
      rw [← map_mul, ← map_mul, h2]
    show f x * f y = f y * f x
    simp only [f, ← map_mul, h3]
  have hf_pow : ∀ x, f x ^ p = 1 := fun x => by
    have h2 : (x : Matrix (Fin 2) (Fin 2) K) ^ p = 1 := by
      simpa using congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
        (hpow x x.2)
    simp only [f, ← map_pow, ← map_pow φ, h2, map_one]
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ f hf_comm hf_pow
  have hfr : finrank L (Fin 2 → L) = 2 := Module.finrank_fin_fun L
  let b' : Basis (Fin 2) L (Fin 2 → L) := b.reindex (finCongr hfr)
  let μ' : E → Fin 2 → L := fun x j => μ x ((finCongr hfr).symm j)
  have hb' : ∀ (x : E) (j : Fin 2), f x (b' j) = μ' x j • b' j := fun x j => by
    simp only [b', μ', Basis.reindex_apply]
    exact hb x _
  have hdet : ∀ x : E, μ' x 0 * μ' x 1 = 1 := fun x => by
    have h1 := LinearMap.det_toMatrix b' (f x)
    have h2 : LinearMap.toMatrix b' b' (f x) = Matrix.diagonal (μ' x) := by
      ext i j
      rw [LinearMap.toMatrix_apply, hb' x j, map_smul, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [h2, Matrix.det_diagonal, Fin.prod_univ_two] at h1
    rw [h1]
    have h3 : (f x).det = 1 := by
      have : (f x).det = (φ (x : Matrix (Fin 2) (Fin 2) K)).det := by
        simp only [f]
        exact LinearMap.det_toLin' _
      rw [this, ← RingHom.map_det]
      simp
    exact h3
  have hmul : ∀ x y : E, μ' (x * y) 0 = μ' x 0 * μ' y 0 := fun x y => by
    have hxy : f (x * y) = f x * f y := by
      have e1 : (((x * y : E) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          (x : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K) := rfl
      show Matrix.toLinAlgEquiv' (φ (((x * y : E) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = _
      rw [e1, map_mul, map_mul]
    have h1 : f (x * y) (b' 0) = (μ' x 0 * μ' y 0) • b' 0 := by
      rw [hxy, Module.End.mul_apply, hb' y 0, map_smul, hb' x 0, smul_smul, mul_comm]
    rw [hb' (x * y) 0] at h1
    exact smul_left_injective L (b'.ne_zero 0) h1
  have hone : μ' 1 0 = 1 := by
    have h1 : f 1 (b' 0) = b' 0 := by
      have h0 : f 1 = 1 := by
        simp only [f]
        rw [show (((1 : E) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl,
          map_one, map_one]
      rw [h0]
      rfl
    rw [hb' 1 0] at h1
    exact smul_left_injective L (b'.ne_zero 0)
      (show μ' 1 0 • b' 0 = (1 : L) • b' 0 by rw [h1, one_smul])
  let χ : E →* L :=
    { toFun := fun x => μ' x 0
      map_one' := hone
      map_mul' := hmul }
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx0 : μ' x 0 = 1 := hx
    have hx1 : μ' x 1 = 1 := by
      have := hdet x
      rwa [hx0, one_mul] at this
    have hfx : f x = 1 := by
      apply b'.ext
      intro j
      rw [hb' x j]
      fin_cases j
      · simp [hx0]
      · simp [hx1]
    have h1 : φ (x : Matrix (Fin 2) (Fin 2) K) = 1 := by
      have : Matrix.toLinAlgEquiv' (φ (x : Matrix (Fin 2) (Fin 2) K)) =
          Matrix.toLinAlgEquiv' (1 : Matrix (Fin 2) (Fin 2) L) := by
        rw [map_one]
        exact hfx
      exact Matrix.toLinAlgEquiv'.injective this
    have h2 : (x : Matrix (Fin 2) (Fin 2) K) = 1 := hφinj (by rw [h1, map_one])
    exact Subtype.ext (Subtype.ext (by simpa using h2))
  exact isCyclic_of_injective_ringHom χ hχinj

theorem psl2_elemAb_card_le {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [NeZero (p : K)] (A : Subgroup (PSL2 K)) (hA : IsElementaryAbelian p A) :
    Nat.card A ≤ p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let π : SpecialLinearGroup (Fin 2) K →* PSL2 K :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ¬ p ∣ Nat.card π.ker := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxc : (x : SpecialLinearGroup (Fin 2) K) ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
      have : (x : SpecialLinearGroup (Fin 2) K) ∈ π.ker := x.2
      simpa [π] using this
    obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hxc
    have hx2 : (x : SpecialLinearGroup (Fin 2) K) ^ 2 = 1 := by
      ext1
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, Matrix.SpecialLinearGroup.coe_one]
      rw [Fintype.card_fin] at hr
      rw [hr, map_one]
    have hxo : orderOf (x : SpecialLinearGroup (Fin 2) K) = p := by
      rw [Subgroup.orderOf_coe, hx]
    have : p ∣ 2 := hxo ▸ orderOf_dvd_of_pow_eq_one hx2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  obtain ⟨E', hE'map, hE'dis⟩ := CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hker A
    (IsElementaryAbelian.isPGroup p A)
  have hE'mem : ∀ x ∈ E', π x ∈ A := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' := E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
      (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have hcm : π a * π b = π b * π a :=
        congrArg Subtype.val (hA.is_comm.comm ⟨π a, hE'mem a ha⟩ ⟨π b, hE'mem b hb⟩)
      rw [hcm]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (π a) (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  have hcyc : IsCyclic E' := isCyclic_of_commuting_pow_eq_one_sl2 hp E' hE'comm hE'exp
  have hE'le : Nat.card E' ≤ p := by
    have hexp : Monoid.exponent ↥E' ∣ p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
      Subtype.ext (by simpa using hE'exp x x.2)
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd hp.pos hexp
  have hsurj : Function.Surjective (fun x : E' => (⟨π x, hE'mem x x.2⟩ : A)) := by
    intro a
    have : (a : PSL2 K) ∈ E'.map π := hE'map ▸ a.2
    obtain ⟨x, hx, hxa⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hE'le

theorem exists_elemAb_card_eq_of_le_inner {X : Type*} [Group X] {p : ℕ}
    (hZ : Subgroup.center X = ⊥) {E : Subgroup (MulAut X)} (hE : IsElementaryAbelian p E)
    (hle : E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner X) :
    ∃ A : Subgroup X, IsElementaryAbelian p A ∧ Nat.card A = Nat.card E := by
  set f : X →* MulAut X := MulAut.conj with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := DFunLike.congr_fun hg z
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * g = g * z * g⁻¹ * g * 1 := by rw [h1]; group
        _ = g * z := by group
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  refine ⟨E.comap f, ?_, ?_⟩
  · refine
      { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_ }
    · apply Subtype.ext
      apply hinj
      have := congrArg Subtype.val
        (hE.is_comm.comm ⟨f (x : X), x.2⟩ ⟨f (y : X), y.2⟩)
      simpa using this
    · apply Subtype.ext
      apply hinj
      have h1 : (⟨f (x : X), x.2⟩ : ↥E) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p E) _
      have h2 := congrArg Subtype.val h1
      simpa using h2
  · have hmap : (E.comap f).map f = E := Subgroup.map_comap_eq_self (by
      intro x hx
      exact hle hx)
    have h1 : Nat.card ((E.comap f).map f) = Nat.card (E.comap f) :=
      Subgroup.card_map_of_injective hinj
    rw [hmap] at h1
    exact h1.symm

theorem exists_inner_core_psl2 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut (PSL2 K))) (hE : IsElementaryAbelian p E) :
    ∃ E₀ : Subgroup (MulAut (PSL2 K)), E₀ ≤ E ∧
      E₀ ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K) ∧
      Nat.card E ≤ p * Nat.card E₀ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  let ψ : MulAut (PSL2 K) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K).symm.toMonoidHom
  let ψE : ↥E →* (K ≃+* K) := ψ.comp E.subtype
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hr, hcardK⟩ := FiniteField.card K (ringChar K)
  have hcyc : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hr K
      (by rw [← Nat.card_eq_fintype_card] at hcardK; exact hcardK)).2
  have hrange : Nat.card ψE.range ≤ p := by
    have hel : IsElementaryAbelian p ψE.range := isElementaryAbelian_range hE ψE
    have hexp : Monoid.exponent ↥ψE.range ∣ p := IsElementaryAbelian.exponent_dvd_p p _
    have : IsCyclic ↥ψE.range := Subgroup.isCyclic _
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd hp.pos hexp
  have hker : ∀ x : ↥E, x ∈ ψE.ker →
      (x : MulAut (PSL2 K)) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K) := by
    intro x hx
    have hψ : ψ (x : MulAut (PSL2 K)) = 1 := MonoidHom.mem_ker.1 hx
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hψ
    have hxp : (x : MulAut (PSL2 K)) ^ p = 1 := by
      have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (x : MulAut (PSL2 K)) x.2
      exact this
    have hgp : g ^ p = 1 :=
      CFSG.RankThree.PartTwo.KFacts.pglAction_injective (by rw [map_pow, hg, hxp, map_one])
    obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd hpodd hgp
    exact ⟨y, by rw [← hg, ← hy, CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL]⟩
  refine ⟨ψE.ker.map E.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hker x hx
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    have hmul := Subgroup.card_ker_mul_card_range ψE
    calc Nat.card E = Nat.card ψE.ker * Nat.card ψE.range := hmul.symm
      _ ≤ Nat.card ψE.ker * p := Nat.mul_le_mul_left _ hrange
      _ = p * Nat.card ψE.ker := mul_comm _ _

theorem noRankThree_psl2 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [NeZero (p : K)] : NoRankThree p (PSL2 K) := by
  classical
  rintro ⟨E, hE, hc⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, hE₀E, hE₀in, hE₀card⟩ := exists_inner_core_psl2 hp hp2 E hE
  have hE₀el : IsElementaryAbelian p E₀ := isElementaryAbelian_of_le hE hE₀E
  obtain ⟨A, hA, hAc⟩ := exists_elemAb_card_eq_of_le_inner
    (CFSG.GorensteinWalter.psl2_center_eq_bot K) hE₀el hE₀in
  have hle := psl2_elemAb_card_le hp hp2 A hA
  rw [hAc] at hle
  rw [hc] at hE₀card
  have hp0 : 0 < p := hp.pos
  have : p ^ 3 ≤ p * p := hE₀card.trans (Nat.mul_le_mul_left _ hle)
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  nlinarith

end CFSG.RankThree.PartOne.K133

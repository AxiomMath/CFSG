module

public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG

theorem card_le_three_mul_card_inf {X : Type*} [Group X] [Finite X] {B N C : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hC : IsCyclic C)
    (hCN : C ≤ Subgroup.normalizer (N : Set X))
    (hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c) :
    Nat.card B ≤ 3 * Nat.card (B ⊓ N : Subgroup X) := by
  set P := Subgroup.normalizer (N : Set X)
  have hNP : N ≤ P := Subgroup.le_normalizer
  have hBP : B ≤ P := by
    intro b hb
    obtain ⟨n, hn, c, hc, rfl⟩ := hBNC b hb
    exact P.mul_mem (hNP hn) (hCN hc)
  have : (N.subgroupOf P).Normal := Subgroup.normal_in_normalizer
  set π := QuotientGroup.mk' (N.subgroupOf P)
  set ψ : B →* P ⧸ N.subgroupOf P := π.comp (Subgroup.inclusion hBP)
  set Cbar : Subgroup (P ⧸ N.subgroupOf P) := (C.subgroupOf P).map π
  have hCbar : IsCyclic Cbar := by
    have : IsCyclic (C.subgroupOf P) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hCN).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hCN).symm.surjective
    have h := isCyclic_of_surjective (π.comp (C.subgroupOf P).subtype).rangeRestrict
      (π.comp (C.subgroupOf P).subtype).rangeRestrict_surjective
    have e : (π.comp (C.subgroupOf P).subtype).range = Cbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e] at h
    exact h
  have hrange : ψ.range ≤ Cbar := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨n, hn, c, hc, hbnc⟩ := hBNC b b.2
    refine ⟨⟨c, hCN hc⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
    change π ⟨c, hCN hc⟩ = π (Subgroup.inclusion hBP b)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have : ((⟨c, hCN hc⟩ : P)⁻¹ * Subgroup.inclusion hBP b : P) = c⁻¹ * n * c := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hbnc]
      group
    rw [this]
    have hcN : c⁻¹ ∈ P := P.inv_mem (hCN hc)
    have h := (Subgroup.mem_normalizer_iff.mp hcN n).mp hn
    rwa [inv_inv] at h
  have hcard3 : Nat.card ψ.range ≤ 3 := by
    have : IsCyclic (ψ.range.subgroupOf Cbar) := Subgroup.isCyclic _
    have e := Subgroup.subgroupOfEquivOfLe hrange
    have hcyc : IsCyclic ψ.range := isCyclic_of_surjective e.toMonoidHom e.surjective
    have hexp : Monoid.exponent ψ.range ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one
      fun y => by
        obtain ⟨b, hb⟩ := y.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hb, ← map_pow, Subgroup.coe_one]
        have : b ^ 3 = 1 := Subtype.ext (by simpa using hB.2 b b.2)
        rw [this, map_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  have hker : Nat.card ψ.ker = Nat.card (B ⊓ N : Subgroup X) := by
    have hk : ψ.ker = N.subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change π (Subgroup.inclusion hBP b) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [hk, inf_comm]
    exact ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm.trans
      (by rw [Subgroup.inf_subgroupOf_right])).symm
  have hfirst : Nat.card B = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hfirst, hker]
  exact Nat.mul_le_mul_right _ hcard3

theorem card_le_nine_of_pgl3 {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    (E : Subgroup (GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 9 := by
  set K' := AlgebraicClosure K
  set ι : K →+* K' := algebraMap K K'
  set Φ : GL (Fin 3) K →* GL (Fin 3) K' := Matrix.GeneralLinearGroup.map ι
  have hΦs : CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K ≤
      (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K').comap Φ := by
    rintro _ ⟨c, rfl⟩
    refine ⟨Units.map ι c, ?_⟩
    ext i j
    simp [Φ, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  set Φbar := QuotientGroup.map _ _ Φ hΦs
  have hinj : Function.Injective Φbar := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H A =>
      rw [MonoidHom.mem_ker, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hx
      obtain ⟨c', hc'⟩ := hx
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
      have hentry : ∀ i j, ι ((A : Matrix (Fin 3) (Fin 3) K) i j) =
          if i = j then (c' : K') else 0 := fun i j => by
        have := congrArg (fun M : GL (Fin 3) K' => (M : Matrix (Fin 3) (Fin 3) K') i j) hc'
        simp only [Φ, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map_apply] at this
        rw [← this]
        simp [Matrix.diagonal_apply]
      have hoff : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := fun i j hij =>
        ι.injective (by simp [hentry, hij])
      have hdiag : ∀ i, (A : Matrix (Fin 3) (Fin 3) K) i i = (A : Matrix (Fin 3) (Fin 3) K) 0 0 :=
        fun i => ι.injective (by simp [hentry])
      have hA0 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
        intro h0
        have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 0 := by
          rw [Matrix.det_fin_three]
          simp [hoff, hdiag, h0]
        exact (A.isUnit.map Matrix.detMonoidHom).ne_zero hdet
      refine ⟨Units.mk0 _ hA0, ?_⟩
      ext i j
      simp only [Matrix.GeneralLinearGroup.scalar]
      by_cases hij : i = j
      · subst hij
        simp [hdiag]
      · simp [hij, hoff i j hij]
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K').degree = 2 := by
    compute_degree!
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 :
    Polynomial K') (by rw [hdeg]; norm_num)
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at hτ
  have h3' : (3 : K') ≠ 0 := by
    intro h
    apply h3
    apply ι.injective
    rw [map_ofNat, h, map_zero]
  have hτ3 : τ ^ 3 = 1 := by linear_combination (τ - 1) * hτ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply h3'
    linear_combination hτ
  have hcomm' : ∀ x ∈ E.map Φbar, ∀ y ∈ E.map Φbar, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hexp' : ∀ x ∈ E.map Φbar, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have := card_le_nine_of_comm h3' hτ3 hτ1 (E.map Φbar) hcomm' hexp'
  rwa [Subgroup.card_map_of_injective hinj] at this

theorem three_ne_zero_of_card {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ f) : (3 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hF])
  intro h
  have h' : ((3 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')

theorem pRank_three_le_of_card_le {X : Type*} [Group X]
    (h : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 27) :
    CFSG.pRank 3 X ≤ 3 := by
  refine csSup_le' ?_
  rintro r ⟨B, hB, hcard⟩
  have hB' : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨hB.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian (A := B) x hx⟩
  have h27 := h B hB'
  rw [hcard, show (27 : ℕ) = 3 ^ 3 by norm_num] at h27
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h27

theorem card_le_of_mulEquiv_mulAut {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ B : Subgroup (MulAut Y), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 27)
    (B : Subgroup (MulAut X)) (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 27 := by
  have := h (B.map (MulAut.congr e).toMonoidHom) (isElemAbelian_map _ hB)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at this

end CFSG.RankThree.PartTwo.Sec4

module

public import CFSG.RankThree.PartTwo.KFacts.K71L28Model
public import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.KFacts.K71Item93b

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open Matrix
open scoped MatrixGroups

section Aut

theorem toPGL_surjective_psl28 :
    Function.Surjective (Matrix.ProjectiveSpecialLinearGroup.toPGL :
      PSL2 (GaloisField 2 3) →* PGL2 (GaloisField 2 3)) := by
  intro g
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have := Fintype.ofFinite (GaloisField 2 3)
  obtain ⟨d, hd⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (GaloisField 2 3) 2)
    (A.det : GaloisField 2 3)
  have hd_ne : d ≠ 0 := by
    intro hd0
    apply Units.ne_zero A.det
    rw [hd, hd0, mul_zero]
  set dU : (GaloisField 2 3)ˣ := Units.mk0 d hd_ne with hdU
  set B : GL (Fin 2) (GaloisField 2 3) := Matrix.GeneralLinearGroup.scalar (Fin 2) dU⁻¹ * A
    with hB
  have hBdet : Matrix.det (B : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det B = 1 := by
      rw [hB, map_mul, Matrix.GeneralLinearGroup.det_scalar]
      apply Units.ext
      change d⁻¹ ^ 2 * (A.det : GaloisField 2 3) = 1
      rw [hd]
      field_simp
    exact congrArg Units.val h1
  set Bs : SL(2, GaloisField 2 3) := ⟨(B : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)), hBdet⟩
  refine ⟨QuotientGroup.mk' (Subgroup.center _) Bs, ?_⟩
  change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL Bs) =
    Matrix.ProjGenLinGroup.mk A
  have htoGL : Matrix.SpecialLinearGroup.toGL Bs = B := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [htoGL, hB, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

theorem exists_conj_of_pow_eq_one_psl28 {ν : MulAut PSL(2, GaloisField 2 3)} {n : ℕ}
    (hn : ¬ 3 ∣ n) (hν : ν ^ n = 1) : ∃ y : PSL(2, GaloisField 2 3), ν = MulAut.conj y := by
  obtain ⟨g, δ, rfl⟩ := exists_pglAction_mul_psl2FieldAut ν
  have hδn : δ ^ n = 1 := by
    have h1 : semilinearAction (GaloisField 2 3)
        ((SemidirectProduct.inl g * SemidirectProduct.inr δ) ^ n) = 1 := by
      rw [map_pow, map_mul, semilinearAction_inl, semilinearAction_inr, hν]
    have h2 := semilinearAction_injective (GaloisField 2 3) (h1.trans (map_one _).symm)
    have h3 := congrArg SemidirectProduct.rightHom h2
    rw [map_pow, map_mul, SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr,
      one_mul, map_one] at h3
    exact h3
  have hδ3 : δ ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (x := δ)
    rwa [card_ringAut_galoisField_two_three] at h1
  have hδ : δ = 1 := by
    have h1 : δ ^ Nat.gcd n 3 = 1 := pow_gcd_eq_one.mpr ⟨hδn, hδ3⟩
    have h2 : Nat.gcd n 3 = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn)
    rwa [h2, pow_one] at h1
  subst hδ
  obtain ⟨y, rfl⟩ := toPGL_surjective_psl28 g
  exact ⟨y, by rw [map_one, mul_one, pglAction_toPGL]⟩

@[expose] noncomputable def sl2EquivPSL28 : SL(2, GaloisField 2 3) ≃* PSL(2, GaloisField 2 3) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center _))
    ⟨(injective_iff_map_eq_one _).mpr fun t ht => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ht
      have h1 := (Subgroup.ext_iff.mp CFSG.Walter.sl2_center_eq_bot_of_charTwo t).mp ht
      exact Subgroup.mem_bot.mp h1,
    QuotientGroup.mk'_surjective _⟩

theorem sl2EquivPSL28_symm_mk (t : SL(2, GaloisField 2 3)) :
    sl2EquivPSL28.symm (QuotientGroup.mk' (Subgroup.center _) t) = t :=
  sl2EquivPSL28.symm_apply_apply t

theorem eq_one_of_conj_eq_one_psl28 {y : PSL(2, GaloisField 2 3)} (hy : MulAut.conj y = 1) :
    y = 1 := by
  set φ := sl2EquivPSL28.symm
  have hc : φ y ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (GaloisField 2 3)) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨s', rfl⟩ := φ.surjective s
    have h1 := DFunLike.congr_fun hy s'
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    rw [← map_mul, ← map_mul]
    congr 1
    calc s' * y = y * s' * y⁻¹ * y := by rw [h1]
      _ = y * s' := by group
  have hc' := (Subgroup.ext_iff.mp CFSG.Walter.sl2_center_eq_bot_of_charTwo (φ y)).mp hc
  rw [Subgroup.mem_bot] at hc'
  exact (map_eq_one_iff φ φ.injective).1 hc'

theorem psl2MulEquivSL2_psl2FieldAut (σ : GaloisField 2 3 ≃+* GaloisField 2 3)
    (z : PSL(2, GaloisField 2 3)) :
    sl2EquivPSL28.symm (psl2FieldAut _ σ z) =
      SpecialLinearGroup.map σ.toRingHom (sl2EquivPSL28.symm z) := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ z
  rw [psl2FieldAut_apply, psl2RingEquiv_mk, sl2EquivPSL28_symm_mk, sl2EquivPSL28_symm_mk]

theorem eq_zero_or_eq_one_of_fixed {σ : GaloisField 2 3 ≃+* GaloisField 2 3}
    (hσ : orderOf σ = 3) {t : GaloisField 2 3} (ht : σ t = t) : t = 0 ∨ t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : Subgroup.zpowers σ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hσ, card_ringAut_galoisField_two_three]
  have hfrob : frobeniusEquiv (GaloisField 2 3) 2 ∈ Subgroup.zpowers σ := by
    rw [htop]
    exact Subgroup.mem_top _
  have hstab : σ ∈ MulAction.stabilizer (GaloisField 2 3 ≃+* GaloisField 2 3) t :=
    MulAction.mem_stabilizer_iff.mpr ht
  have hfix := (Subgroup.zpowers_le.mpr hstab) hfrob
  have h2 : t ^ 2 = t := by
    have h1 : (frobeniusEquiv (GaloisField 2 3) 2) t = t := MulAction.mem_stabilizer_iff.mp hfix
    rwa [frobeniusEquiv_apply, frobenius_def] at h1
  have h3 : t * (t - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h2, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem pow_card_eq_one_of_mem {M : Type*} [Group M] {N : Subgroup M} {ν : M} (hν : ν ∈ N) :
    ν ^ Nat.card N = 1 := by
  have h1 := pow_card_eq_one' (G := N) (x := ⟨ν, hν⟩)
  have h2 := congrArg Subtype.val h1
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2

end Aut

section Inner

theorem psl28_eq_bot_of_commute_conj {u : PSL(2, GaloisField 2 3)} (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) {N : Subgroup (MulAut PSL(2, GaloisField 2 3))}
    (hNc : ∀ ν ∈ N, ν * MulAut.conj u = MulAut.conj u * ν) (hN3 : ¬ 3 ∣ Nat.card N) :
    N = ⊥ := by
  rw [eq_bot_iff]
  intro ν hν
  rw [Subgroup.mem_bot]
  obtain ⟨y, rfl⟩ := exists_conj_of_pow_eq_one_psl28 hN3 (pow_card_eq_one_of_mem hν)
  have hyu : y * u = u * y := by
    have h1 := hNc _ hν
    rw [← map_mul, ← map_mul] at h1
    have h2 : MulAut.conj (y * u * (u * y)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact mul_inv_eq_one.mp (eq_one_of_conj_eq_one_psl28 h2)
  set φ := sl2EquivPSL28.symm with hφ
  have hU3 : (φ u).1 ^ 3 = 1 := by
    have h1 : φ u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
    exact congrArg Subtype.val h1
  have hU1 : (φ u).1 ≠ 1 := by
    intro h1
    apply hu1
    have h2 : φ u = 1 := Subtype.ext h1
    exact (map_eq_one_iff φ φ.injective).1 h2
  have hYU : (φ y).1 * (φ u).1 = (φ u).1 * (φ y).1 := by
    have h1 : φ y * φ u = φ u * φ y := by rw [← map_mul, ← map_mul, hyu]
    exact congrArg Subtype.val h1
  have h9 := mat2_pow_nine_eq_one_of_commute card_galoisField_two_three (φ u).2 hU3 hU1 (φ y).2
    hYU
  have hy9 : y ^ 9 = 1 := by
    have h1 : φ y ^ 9 = 1 := Subtype.ext h9
    rw [← map_pow] at h1
    exact (map_eq_one_iff φ φ.injective).1 h1
  refine eq_one_of_pow_three_pow_eq_one hN3 hν (k := 2) ?_
  rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← map_pow, hy9, map_one]

end Inner

section Field

@[expose] def sl2OrderThree : SL(2, GaloisField 2 3) :=
  ⟨!![0, 1; 1, 1], by
    have h2 : (2 : GaloisField 2 3) = 0 := CharTwo.two_eq_zero
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : GaloisField 2 3) * h2⟩

theorem sl2OrderThree_pow_three : sl2OrderThree ^ 3 = 1 := by
  have h2 : (2 : GaloisField 2 3) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  show (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem sl2OrderThree_ne_one : sl2OrderThree ≠ 1 := by
  intro h1
  have h2 := congrArg (fun s : SL(2, GaloisField 2 3) => s.1 0 0) h1
  simp [sl2OrderThree] at h2

theorem map_sl2OrderThree (σ : GaloisField 2 3 ≃+* GaloisField 2 3) :
    SpecialLinearGroup.map σ.toRingHom sl2OrderThree = sl2OrderThree := by
  apply Subtype.ext
  show (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)).map σ.toRingHom = !![0, 1; 1, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem psl28_eq_bot_of_commute_field {σ : GaloisField 2 3 ≃+* GaloisField 2 3}
    (hσ : orderOf σ = 3) {N : Subgroup (MulAut PSL(2, GaloisField 2 3))}
    (hNc : ∀ ν ∈ N, ν * psl2FieldAut _ σ = psl2FieldAut _ σ * ν) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ, psl2FieldAut _ σ ℓ = ℓ →
      ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) :
    N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := sl2EquivPSL28.symm with hφ
  set H : Subgroup PSL(2, GaloisField 2 3) :=
    (psl2FieldAut (GaloisField 2 3) σ : PSL(2, GaloisField 2 3) ≃* PSL(2, GaloisField 2 3)
      ).toMonoidHom.eqLocus (MonoidHom.id _) ⊓ N.comap MulAut.conj with hH
  have hH2 : ∀ z ∈ H, z ^ 2 = 1 := by
    intro z hz
    have hzσ : psl2FieldAut _ σ z = z := hz.1
    have hzN : MulAut.conj z ∈ N := hz.2
    have hz6 : z ^ 6 = 1 := by
      have hmap : SpecialLinearGroup.map σ.toRingHom (φ z) = φ z := by
        rw [← psl2MulEquivSL2_psl2FieldAut, hzσ]
      have hmap' : (φ z).1.map σ.toRingHom = (φ z).1 := congrArg Subtype.val hmap
      have htr : σ (φ z).1.trace = (φ z).1.trace := by
        conv_rhs => rw [← hmap']
        rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]
        rfl
      have h6 := mat2_pow_six_eq_one_of_trace (φ z).2 (eq_zero_or_eq_one_of_fixed hσ htr)
      have h1 : φ z ^ 6 = 1 := Subtype.ext h6
      rw [← map_pow] at h1
      exact (map_eq_one_iff φ φ.injective).1 h1
    have hzn : z ^ Nat.card N = 1 := by
      have h1 := pow_card_eq_one_of_mem hzN
      rw [← map_pow] at h1
      exact eq_one_of_conj_eq_one_psl28 h1
    have h1 : z ^ Nat.gcd (Nat.card N) 6 = 1 := pow_gcd_eq_one.mpr ⟨hzn, hz6⟩
    obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd (Nat.card N) 6 := ⟨_, rfl⟩
    have hd6 : g ∣ 6 := hg ▸ Nat.gcd_dvd_right _ 6
    have hdn : g ∣ Nat.card N := hg ▸ Nat.gcd_dvd_left _ 6
    rw [← hg] at h1
    have h2 : g ∣ 2 := by
      have hle : g ≤ 6 := Nat.le_of_dvd (by norm_num) hd6
      interval_cases g
      · norm_num at hd6
      · norm_num
      · norm_num
      · exact absurd hdn hN3
      · norm_num at hd6
      · norm_num at hd6
      · exact absurd (dvd_trans (by norm_num : 3 ∣ 6) hdn) hN3
    obtain ⟨k, hk⟩ := h2
    have h3 : z ^ (g * k) = 1 := by rw [pow_mul, h1, one_pow]
    rwa [← hk] at h3
  set u₀ := φ.symm sl2OrderThree with hu₀
  have hu₀3 : u₀ ^ 3 = 1 := by rw [hu₀, ← map_pow, sl2OrderThree_pow_three, map_one]
  have hu₀1 : u₀ ≠ 1 := fun h1 => sl2OrderThree_ne_one (by
    have h2 := congrArg φ h1
    rwa [hu₀, MulEquiv.apply_symm_apply, map_one] at h2)
  have hu₀σ : psl2FieldAut _ σ u₀ = u₀ := by
    apply φ.injective
    rw [psl2MulEquivSL2_psl2FieldAut, hu₀, MulEquiv.apply_symm_apply, map_sl2OrderThree]
  have hHp : IsPGroup 2 H := fun z => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hH2 _ z.2)⟩
  have hHu : ∀ z ∈ H, u₀ * z * u₀⁻¹ ∈ H := by
    intro z hz
    refine ⟨?_, ?_⟩
    · change psl2FieldAut _ σ (u₀ * z * u₀⁻¹) = u₀ * z * u₀⁻¹
      have hzσ : psl2FieldAut _ σ z = z := hz.1
      rw [map_mul, map_mul, map_inv, hu₀σ, hzσ]
    · change MulAut.conj (u₀ * z * u₀⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNn u₀ hu₀σ _ hz.2
  have hHbot := psl28_eq_bot_of_normalizes hu₀3 hu₀1 hHp hHu
  rw [eq_bot_iff]
  intro ν hν
  rw [Subgroup.mem_bot]
  obtain ⟨y, rfl⟩ := exists_conj_of_pow_eq_one_psl28 hN3 (pow_card_eq_one_of_mem hν)
  have hyσ : psl2FieldAut _ σ y = y := by
    have h1 := hNc _ hν
    have h2 : MulAut.conj y = MulAut.conj (psl2FieldAut _ σ y) := by
      rw [← mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    have h3 : MulAut.conj (psl2FieldAut _ σ y * y⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h2, mul_inv_cancel]
    exact (mul_inv_eq_one.mp (eq_one_of_conj_eq_one_psl28 h3))
  have hyH : y ∈ H := ⟨hyσ, hν⟩
  rw [hHbot, Subgroup.mem_bot] at hyH
  rw [hyH, map_one]

end Field

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem eq_bot_of_hyp91_psl28 {A : Subgroup G} {c a : G} {R : Subgroup G}
    (hyp : Sec9.Hyp91 G A c L a R)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {e : G} (heA : e ∈ A)
    (hec : e ∉ Subgroup.zpowers c) (he : e ∈ Subgroup.normalizer (L : Set G))
    (N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)))
    (hNc : ∀ ν ∈ N, ν * thetaQuotMulAut L (compAction L ⟨e, he⟩) =
      thetaQuotMulAut L (compAction L ⟨e, he⟩) * ν)
    (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ : L ⧸ aschbacherSolvableCore 3 L,
      thetaQuotMulAut L (compAction L ⟨e, he⟩) ℓ = ℓ →
        ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) :
    N = ⊥ := by
  obtain ⟨e', σ, x, b, hbA, hσ3, hx3, hx1, hσx, -, hA⟩ := exists_l28_model_of_hyp91 hyp hL hAL
  obtain ⟨i, j, hij⟩ := hA e heA
  have hσ3' : σ ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one σ
    rwa [hσ3] at h1
  have hσf3 : psl2FieldAut (GaloisField 2 3) σ ^ 3 = 1 := by rw [← map_pow, hσ3', map_one]
  have hx3' : MulAut.conj x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hxσ : Commute (MulAut.conj x) (psl2FieldAut (GaloisField 2 3) σ) := by
    have h1 := mul_conj_mul_inv (psl2FieldAut (GaloisField 2 3) σ) x
    rw [hσx] at h1
    change MulAut.conj x * psl2FieldAut _ σ = psl2FieldAut _ σ * MulAut.conj x
    calc MulAut.conj x * psl2FieldAut _ σ =
        psl2FieldAut _ σ * MulAut.conj x * (psl2FieldAut _ σ)⁻¹ * psl2FieldAut _ σ := by rw [h1]
      _ = psl2FieldAut _ σ * MulAut.conj x := by group
  have hε : MulAut.congr e' (thetaQuotMulAut L (compAction L ⟨e, he⟩)) =
      MulAut.conj (x ^ (i % 3)) * psl2FieldAut (GaloisField 2 3) σ ^ (j % 3) := by
    rw [← inducedAutHom_apply, show (⟨e, he⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, hAL heA⟩
      from rfl, hij, mulAut_pow_mod_three hx3' i, mulAut_pow_mod_three hσf3 j, map_pow]
  have hε1 : MulAut.conj (x ^ (i % 3)) * psl2FieldAut (GaloisField 2 3) σ ^ (j % 3) ≠ 1 := by
    intro h1
    apply hec
    refine mem_zpowers_of_thetaQuotMulAut_eq_one hyp.toHyp81 he heA ?_
    have h2 := hε.trans h1
    exact (MulAut.congr e').injective (h2.trans (map_one _).symm)
  refine eq_bot_of_congr e' (fun N₀ hc h3 hn => ?_) hNc hN3 hNn
  rw [hε] at hc hn
  have hmodj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_cases hj0 : j % 3 = 0
  ·
    rw [hj0, pow_zero, mul_one] at hc hn hε1
    have hu3 : (x ^ (i % 3)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
    have hu1 : x ^ (i % 3) ≠ 1 := fun h1 => hε1 (by rw [h1, map_one])
    exact psl28_eq_bot_of_commute_conj hu3 hu1 hc h3
  ·
    set ε' := MulAut.conj (x ^ (i % 3)) * psl2FieldAut (GaloisField 2 3) σ ^ (j % 3) with hε'
    have hε'3 : ε' ^ 3 = 1 := by
      have hc' : Commute (MulAut.conj (x ^ (i % 3)))
          (psl2FieldAut (GaloisField 2 3) σ ^ (j % 3)) := by
        rw [map_pow]
        exact (hxσ.pow_left _).pow_right _
      have e1 : MulAut.conj (x ^ (i % 3)) ^ 3 = 1 := by
        rw [← map_pow, ← pow_mul, mul_comm (i % 3) 3, pow_mul, hx3, one_pow, map_one]
      have e2 : (psl2FieldAut (GaloisField 2 3) σ ^ (j % 3)) ^ 3 = 1 := by
        rw [← pow_mul, mul_comm (j % 3) 3, pow_mul, hσf3, one_pow]
      rw [hε', hc'.mul_pow, e1, e2, one_mul]
    have hε'o : orderOf ε' = 3 := orderOf_eq_prime hε'3 hε1
    have hD : ε' ∉ (pglAction (GaloisField 2 3)).range := by
      rintro ⟨g, hg⟩
      apply hj0
      have h1 : pglAction (GaloisField 2 3)
          ((Matrix.ProjectiveSpecialLinearGroup.toPGL (x ^ (i % 3)))⁻¹ * g) =
          psl2FieldAut (GaloisField 2 3) (σ ^ (j % 3)) := by
        rw [map_mul, map_inv, pglAction_toPGL, hg, hε', map_pow (psl2FieldAut _),
          inv_mul_cancel_left]
      have h2 : semilinearAction (GaloisField 2 3) (SemidirectProduct.inl
          ((Matrix.ProjectiveSpecialLinearGroup.toPGL (x ^ (i % 3)))⁻¹ * g)) =
          semilinearAction (GaloisField 2 3) (SemidirectProduct.inr (σ ^ (j % 3))) := by
        rw [semilinearAction_inl, semilinearAction_inr, h1]
      have h3 := congrArg SemidirectProduct.rightHom
        (semilinearAction_injective (GaloisField 2 3) h2)
      rw [SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr] at h3
      have h4 := orderOf_dvd_of_pow_eq_one h3.symm
      rw [hσ3] at h4
      omega
    obtain ⟨σ', hσ', g, hg⟩ := linear_two_prime_order_field_descent Nat.prime_three ε' hε'o hD
    exact eq_bot_of_conj hg (fun N₁ hc₁ h₁ hn₁ => psl28_eq_bot_of_commute_field hσ' hc₁ h₁ hn₁)
      hc h3 hn

end Assembly

end CFSG.RankThree.PartTwo.KFacts

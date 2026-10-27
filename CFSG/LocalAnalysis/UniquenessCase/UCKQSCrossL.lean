module

public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSL
public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSDispatch

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

section PSL

open CFSG.Open CFSG.Open.StatedAPI CFSG.GroupTheory.WeirSylow PSLCross

theorem qsPSL_pca_proj {F : Type} [Field F] [Finite F] {n p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : PCentralAbelianAt (StatedProj (StatedSL n F)) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hp1 : Odd p := hp.odd_of_ne_two (by omega)
  have hpF' : ¬ p ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hGL : ∀ P : Sylow p (GL (Fin n) F), Nonempty (P ≃* sigmaModel p
      (orderOf (Fintype.card F : ZMod p))
      (padicValNat p (Fintype.card F ^ orderOf (Fintype.card F : ZMod p) - 1)) n) :=
    fun P => sylow_GL hp1 F hpF' n P
  by_cases hn4 : n ≤ 4
  · have hc := sylow_isMulCommutative_of_sigmaModel_of_lt hp
      (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega : n < p)) hGL
    exact PCentralAbelianAt.of_sylow_comm (sylow_comm_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (sylow_comm_of_subgroup (StatedSL n F) hc))
  · push Not at hn4
    by_cases hA : p ∣ Nat.card F - 1
    · obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
      by_cases hnp : 6 ≤ n ∨ ¬ p ∣ n
      · have hH : ∀ u : Fin n → Fˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) →
            (∀ i : Fin n, 5 ≤ i.val → u i = 1) → ∏ i, u i = 1 →
            diagGL n u ∈ StatedSL n F := by
          intro u _ _ hprod
          rw [mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod, Units.val_one]
        obtain ⟨E, hE, hEcard⟩ := exists_elemAbelian_four_projDiag hp hn4 hnp hζ (StatedSL n F) hH
        exact PCentralAbelianAt.of_elemAbelian hp hE hEcard le_rfl
      · push Not at hnp
        obtain rfl : n = 5 := by omega
        have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hnp.2
        subst hp5
        have hd : diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] ∈ StatedSL 5 F := by
          rw [mem_statedSL_iff, det_diagGL]
          simp [Fin.prod_univ_five]
        have hc : permGL 5 (finRotate 5) ∈ StatedSL 5 F := by
          rw [mem_statedSL_iff, det_permGL, sign_finRotate]
          simp
        exact qsCross_pca_projFive hζ (StatedSL 5 F) hd hc
    · have hGLpca : PCentralAbelianAt (GL (Fin n) F) p :=
        PCentralAbelianAt.of_sylow_sigmaModel hp h5 (one_le_padicValNat_card hp hpF') hGL
      have hSL : PCentralAbelianAt (StatedSL n F) p :=
        PCentralAbelianAt.of_normal_coprime_index (StatedSL n F)
          (fun hd => hA (hd.trans (index_statedSL_dvd n))) hGLpca
      refine PCentralAbelianAt.of_surjective_coprime_ker (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _) ?_ hSL
      rw [QuotientGroup.ker_mk']
      exact fun hd => hA (hd.trans (card_scalars_subgroupOf_dvd n))

theorem pcaLieCross_PSL : PCALieCrossAt .PSL := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, F, hF, hFin, hcard, ⟨e⟩⟩ := LieModel.statedClassicalModel hmodel (by simp [classicalTags])
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hcard]
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hadm.1).1 (hp.dvd_of_dvd_pow h))
  exact PCentralAbelianAt.of_mulEquiv e (qsPSL_pca_proj hp h5 hpF)

end PSL

section PSU

open CFSG.Open
open CFSG.Quasithin (StatedGU)
open scoped Matrix
open CFSG.GroupTheory.WeirSylow
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
  (mem_statedSU_of_mem_statedGU det_pow_card_add_one_of_mem_statedGU statedSU_le_statedGU)

variable {L : Type} [Field L] [Finite L] {ℓ f n p : ℕ}

theorem qsPSU_field (hL : Nat.card L = (ℓ ^ f) ^ 2) :
    ∃ f', ℓ ^ f = ringChar L ^ f' ∧ UnitaryFieldData (ringChar L) f' L := by
  haveI := Fintype.ofFinite L
  exact exists_unitaryFieldData L (by rw [Fintype.card_eq_nat_card]; exact hL)

theorem qsPSU_mem_statedSU_iff (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n)
    (A : GL (Fin n) L) :
    A ∈ StatedSU n (ℓ ^ f) L ↔ (A : Matrix (Fin n) (Fin n) L).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) L).map (· ^ ℓ ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) L) = 1 :=
  Set.ext_iff.1 (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).1 A

theorem qsPSU_exp_pos (hp : p.Prime) {q : ℕ} (hq2 : 2 ≤ q) (hpq : ¬ p ∣ q) :
    1 ≤ padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne0 : (-(q : ZMod p)) ≠ 0 :=
    neg_ne_zero.2 (fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h))
  have hdvd : (p : ℤ) ∣ (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hx : (-(q : ZMod p)) ^ orderOf (-(q : ZMod p)) = 1 := pow_orderOf_eq_one _
    push_cast
    exact sub_eq_zero.2 hx
  have hne : (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1 ≠ 0 := by
    intro h
    have h1 : (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) = 1 := sub_eq_zero.1 h
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_one] at h2
    have h3 : q = 1 := (Nat.pow_eq_one.1 h2).resolve_right (by
      have hepos : 0 < orderOf (-(q : ZMod p)) := by
        rw [orderOf_pos_iff]
        exact isOfFinOrder_iff_pow_eq_one.2
          ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hne0⟩
      omega)
    omega
  rcases (padicValInt_dvd_iff 1 ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1)).1
      (by simpa using hdvd) with h | h
  · exact absurd h hne
  · exact h

theorem qsPSU_two_le (hL : Nat.card L = (ℓ ^ f) ^ 2) : 2 ≤ ℓ ^ f := by
  have h1 : 1 < Nat.card L := Finite.one_lt_card
  rw [hL] at h1
  by_contra h
  have h2 : ℓ ^ f ≤ 1 := by omega
  have h3 : (ℓ ^ f) ^ 2 ≤ 1 := by
    calc (ℓ ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 1 := by norm_num
  omega

theorem qsPSU_pca_GU (hp : p.Prime) (h5 : 5 ≤ p) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq : ¬ p ∣ ℓ ^ f) (hn : 1 ≤ n) : PCentralAbelianAt ↥(StatedGU n (ℓ ^ f) L) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite L
  have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
  exact PCentralAbelianAt.of_sylow_sigmaModel hp h5 (qsPSU_exp_pos hp (qsPSU_two_le hL) hpq)
    (fun P => sylow_GU (hp.odd_of_ne_two (by omega)) L hLc hpq hn P)

@[expose] noncomputable def qsPSU_det (n q : ℕ) (L : Type) [Field L] : ↥(StatedGU n q L) →* Lˣ :=
  Matrix.GeneralLinearGroup.det.comp (StatedGU n q L).subtype

theorem qsPSU_det_val {q : ℕ} (g : ↥(StatedGU n q L)) :
    ((qsPSU_det n q L g : Lˣ) : L) = ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det := rfl

theorem qsPSU_subgroupOf_eq_ker (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    (StatedSU n (ℓ ^ f) L).subgroupOf (StatedGU n (ℓ ^ f) L) = (qsPSU_det n (ℓ ^ f) L).ker := by
  obtain ⟨f', hq, h⟩ := qsPSU_field hL
  ext g
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro hg
    exact Units.ext (by rw [qsPSU_det_val]; exact ((qsPSU_mem_statedSU_iff hℓ hL hn _).1 hg).1)
  · intro hg
    exact mem_statedSU_of_mem_statedGU h hq g.2 (by rw [← qsPSU_det_val, hg]; rfl)

theorem qsPSU_not_dvd_index (hp : p.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hpq1 : ¬ p ∣ ℓ ^ f + 1) :
    ¬ p ∣ (qsPSU_det n (ℓ ^ f) L).ker.index := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨f', hq, h⟩ := qsPSU_field hL
  intro hdvd
  rw [Subgroup.index_ker] at hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (qsPSU_det n (ℓ ^ f) L).range) p hdvd
  obtain ⟨g, hg⟩ := y.2
  have hpow : (y : Lˣ) ^ (ℓ ^ f + 1) = 1 := by
    rw [← hg]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, qsPSU_det_val, Units.val_one]
    exact det_pow_card_add_one_of_mem_statedGU h hq g.2
  have h1 : orderOf (y : Lˣ) ∣ ℓ ^ f + 1 := orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hy] at h1
  exact hpq1 h1

noncomputable def qsPSU_equivKer (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    ↥(StatedSU n (ℓ ^ f) L) ≃* ↥(qsPSU_det n (ℓ ^ f) L).ker :=
  (Subgroup.subgroupOfEquivOfLe statedSU_le_statedGU).symm.trans
    (MulEquiv.subgroupCongr (qsPSU_subgroupOf_eq_ker hℓ hL hn))

theorem qsPSU_not_dvd_ker (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n)
    (hpq1 : ¬ p ∣ ℓ ^ f + 1) :
    ¬ p ∣ Nat.card (QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf (StatedSU n (ℓ ^ f) L))).ker := by
  rw [QuotientGroup.ker_mk', (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).2.2]
  exact fun h => hpq1 (h.trans (Nat.gcd_dvd_right _ _))

theorem qsPSU_pca_of_not_dvd (hp : p.Prime) (h5 : 5 ≤ p) (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq : ¬ p ∣ ℓ ^ f) (hn : 1 ≤ n) (hpq1 : ¬ p ∣ ℓ ^ f + 1) :
    PCentralAbelianAt (StatedProj (StatedSU n (ℓ ^ f) L)) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSU : PCentralAbelianAt ↥(StatedSU n (ℓ ^ f) L) p :=
    PCentralAbelianAt.of_mulEquiv (qsPSU_equivKer hℓ hL hn)
      (PCentralAbelianAt.of_normal_coprime_index _ (qsPSU_not_dvd_index hp hL hpq1)
        (qsPSU_pca_GU hp h5 hL hpq hn))
  exact PCentralAbelianAt.of_surjective_coprime_ker (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (qsPSU_not_dvd_ker hℓ hL hn hpq1) hSU

theorem qsPSU_exists_zeta (hp : p.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hpq1 : p ∣ ℓ ^ f + 1) :
    ∃ ζ : Lˣ, orderOf ζ = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine exists_prime_orderOf_dvd_card' p ?_
  rw [Nat.card_units, hL]
  refine hpq1.trans ⟨ℓ ^ f - 1, ?_⟩
  have h2 := qsPSU_two_le hL
  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 1 := ⟨ℓ ^ f - 1, by omega⟩
  rw [hm]
  apply Nat.sub_eq_of_eq_add
  simp only [Nat.add_sub_cancel]
  ring

theorem qsPSU_zeta_pow (hpq1 : p ∣ ℓ ^ f + 1) {ζ : Lˣ} (hζ : orderOf ζ = p) :
    ∀ x ∈ Subgroup.zpowers ζ, x ^ (ℓ ^ f + 1) = 1 := fun x hx => by
  rw [← orderOf_dvd_iff_pow_eq_one]
  exact (orderOf_dvd_of_mem_zpowers hx).trans (by rw [hζ]; exact hpq1)

theorem qsPSU_diagGL_mem_statedSU {q : ℕ} (hq : q ≠ 0) (u : Fin n → Lˣ)
    (hu : ∀ i, (u i) ^ (q + 1) = 1) (hprod : ∏ i, u i = 1) : diagGL n u ∈ StatedSU n q L := by
  have hdet : ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = 1 := by
    rw [det_diagGL, ← Units.coe_prod, hprod, Units.val_one]
  have hunit : (((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ *
      ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [coe_diagGL, Matrix.diagonal_map (f := fun x : L => x ^ q) (zero_pow hq),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have := congrArg Units.val (hu i)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [← pow_succ]
    exact this
  unfold StatedSU
  exact Subgroup.subset_closure ⟨hdet, hunit⟩

theorem qsPSU_permGL_mem_statedSU {q : ℕ} (hq : q ≠ 0) (σ : Equiv.Perm (Fin n))
    (hσ : Equiv.Perm.sign σ = 1) : permGL n σ ∈ StatedSU n q L := by
  have hdet : ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = 1 := by
    rw [det_permGL, hσ]; simp
  have hmap : ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q) =
      ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [coe_permGL]
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    split_ifs <;> simp [hq]
  have hunit : (((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ *
      ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [hmap, coe_permGL, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one]
  unfold StatedSU
  exact Subgroup.subset_closure ⟨hdet, hunit⟩

theorem qsPSU_pca_of_dvd (hp : p.Prime) (h5 : 5 ≤ p) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq : ¬ p ∣ ℓ ^ f) (hn : 1 ≤ n) (hpq1 : p ∣ ℓ ^ f + 1) :
    PCentralAbelianAt (StatedProj (StatedSU n (ℓ ^ f) L)) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : ℓ ^ f ≠ 0 := by have := qsPSU_two_le hL; omega
  by_cases hnp5 : n < 5
  · have hnp : n < p := by omega
    have he : orderOf (-((ℓ ^ f : ℕ) : ZMod p)) = 1 := by
      have h0 : (((ℓ ^ f + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq1
      have h1 : ((ℓ ^ f : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_add, Nat.cast_one] at h0
        exact eq_neg_of_add_eq_zero_left h0
      have h2 : -((ℓ ^ f : ℕ) : ZMod p) = 1 := neg_eq_iff_eq_neg.2 h1
      rw [h2, orderOf_one]
    haveI := Fintype.ofFinite L
    have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
    have hGU : ∀ P : Sylow p ↥(StatedGU n (ℓ ^ f) L),
        IsMulCommutative (P : Subgroup ↥(StatedGU n (ℓ ^ f) L)) :=
      sylow_isMulCommutative_of_sigmaModel_of_lt hp
        (e := orderOf (-((ℓ ^ f : ℕ) : ZMod p))) (by rw [he, Nat.div_one]; exact hnp)
        (fun P => sylow_GU (hp.odd_of_ne_two (by omega)) L hLc hpq hn P)
    have hSub := sylow_comm_of_subgroup ((StatedSU n (ℓ ^ f) L).subgroupOf (StatedGU n (ℓ ^ f) L)) hGU
    have hSU := sylow_comm_of_surjective
      (Subgroup.subgroupOfEquivOfLe (statedSU_le_statedGU (L := L) (q := ℓ ^ f) (n := n))).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (statedSU_le_statedGU (L := L) (q := ℓ ^ f) (n := n))).surjective
      hSub
    exact PCentralAbelianAt.of_sylow_comm
      (sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hSU)
  · push Not at hnp5
    obtain ⟨ζ, hζ⟩ := qsPSU_exists_zeta hp hL hpq1
    have hzp := qsPSU_zeta_pow hpq1 hζ
    have hdiag : ∀ u : Fin n → Lˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) → ∏ i, u i = 1 →
        diagGL n u ∈ StatedSU n (ℓ ^ f) L := fun u hu hprod =>
      qsPSU_diagGL_mem_statedSU hq0 u (fun i => hzp _ (hu i)) hprod
    by_cases hnp : 6 ≤ n ∨ ¬ p ∣ n
    · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_four_projDiag hp hnp5 hnp hζ
        (StatedSU n (ℓ ^ f) L) (fun u hu _ hprod => hdiag u hu hprod)
      exact PCentralAbelianAt.of_elemAbelian hp hE hEc le_rfl
    · push Not at hnp
      obtain ⟨hn6, hpn⟩ := hnp
      have hn5 : n = 5 := by omega
      subst hn5
      have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn
      subst hp5
      have hd : diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] ∈ StatedSU 5 (ℓ ^ f) L := by
        apply hdiag
        · intro i
          fin_cases i
          · exact Subgroup.mem_zpowers ζ
          · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
          · exact Subgroup.one_mem _
          · exact Subgroup.one_mem _
          · exact Subgroup.one_mem _
        · simp [Fin.prod_univ_five]
      have hc : permGL 5 (finRotate 5) ∈ StatedSU 5 (ℓ ^ f) L :=
        qsPSU_permGL_mem_statedSU hq0 _ (by rw [sign_finRotate]; decide)
      exact qsCross_pca_projFive hζ (StatedSU 5 (ℓ ^ f) L) hd hc

end PSU

theorem pcaLieCross_PSU : PCALieCrossAt .PSU := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hℓ, hf, hn3, -⟩ := hadm
  obtain ⟨-, L, _, _, hL, ⟨e⟩⟩ := hmodel.statedClassicalModel_of_ne_zero (by omega)
  have hpq : ¬ p ∣ ℓ ^ f := fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  refine PCentralAbelianAt.of_mulEquiv e ?_
  by_cases hpq1 : p ∣ ℓ ^ f + 1
  · exact qsPSU_pca_of_dvd hp h5 hL hpq (by omega) hpq1
  · exact qsPSU_pca_of_not_dvd hp h5 hℓ hL hpq (by omega) hpq1

section PSp

theorem qsPSp_one_le_padicValNat {p q : ℕ} [hp : Fact p.Prime] (hq : 1 < q) (hpq : ¬ p ∣ q) :
    1 ≤ padicValNat p (q ^ orderOf (q : ZMod p) - 1) := by
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hepos : 0 < orderOf (q : ZMod p) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨p - 1, Nat.sub_pos_of_lt hp.out.one_lt, ZMod.pow_card_sub_one_eq_one hq0⟩
  have h1 : 1 < q ^ orderOf (q : ZMod p) := Nat.one_lt_pow hepos.ne' hq
  refine one_le_padicValNat_of_dvd (by omega) ?_
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1.le, Nat.cast_pow, pow_orderOf_eq_one, Nat.cast_one,
    sub_self]

theorem qsPSp_not_dvd_card_ker {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {n : ℕ} (hn : 1 ≤ n) {F : Type}
    [Field F] [Finite F] :
    ¬ p ∣ Nat.card (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F))).ker := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have hmem := (QuotientGroup.ker_mk' _).le x.2
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hmem
    have hc2 : c ^ 2 = 1 :=
      (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn c).1 (by rw [hc]; exact (x : StatedSp n F).2)
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, ← hc, ← map_pow, hc2, map_one]
    rfl
  have h2 := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem pcaLieCross_PSp : PCALieCrossAt .PSp := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, F, _, _, hF, ⟨e⟩⟩ := hmodel.statedClassicalModel (by simp [classicalTags])
  have hℓ : ℓ.Prime := hadm.1
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  have hn : 1 ≤ n := by have := hadm.2.2.1; omega
  haveI := Fintype.ofFinite F
  have hpF' : ¬ p ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hSp : PCentralAbelianAt (StatedSp n F) p :=
    PCentralAbelianAt.of_sylow_sigmaModel hp h5 (qsPSp_one_le_padicValNat Fintype.one_lt_card hpF')
      (fun P => CFSG.GroupTheory.WeirSylow.sylow_Sp (hp.odd_of_ne_two (by omega)) F hpF' n P)
  exact PCentralAbelianAt.of_mulEquiv e (PCentralAbelianAt.of_surjective_coprime_ker (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (qsPSp_not_dvd_card_ker hp h5 hn) hSp)

end PSp

end CFSG.LocalAnalysis.UniquenessCase.UCK

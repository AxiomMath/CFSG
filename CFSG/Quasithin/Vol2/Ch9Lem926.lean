module

public import CFSG.Quasithin.Vol2.Ch9Lem925
public import CFSG.Quasithin.Vol2.Ch10SecC9S3a
public import CFSG.Quasithin.Vol2.Ch10SecQ3CQ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBorel

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.H
open Matrix

section Model

variable {K : Type} [Field K]

@[expose] def utFst (K : Type) [Field K] :
    Subgroup (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) where
  carrier := {γ | ((γ.1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two] at ha hb ⊢
    rw [ha, hb, zero_mul, mul_zero, add_zero]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] at ha ⊢
    simp [ha]

theorem mul_eq_one_of_ut {g : SpecialLinearGroup (Fin 2) K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at h
  exact h

@[expose] noncomputable def chiFst (K : Type) [Field K] : ↥(utFst K) →* Kˣ where
  toFun γ := Units.mk0 ((((γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K).1 :
    SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0)
      (left_ne_zero_of_mul_eq_one (mul_eq_one_of_ut γ.2))
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    have hb : (((b : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K).1 :
      SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := b.2
    simp only [Subgroup.coe_mul, Prod.fst_mul, Matrix.SpecialLinearGroup.coe_mul,
      Units.val_mk0, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hb, mul_zero,
      add_zero])

theorem coe_chiFst (γ : ↥(utFst K)) :
    ((chiFst K γ : Kˣ) : K) =
      (((γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K).1 :
      SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 := rfl

theorem conj_mem_uni {g u : SpecialLinearGroup (Fin 2) K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hu : u ∈ uni K) : g * u * g⁻¹ ∈ uni K := by
  obtain ⟨c, hc⟩ := mem_uni_iff.mp hu
  have hdet := mul_eq_one_of_ut hg
  refine mem_uni_iff.mpr ⟨(g : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * c, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hg]
  all_goals first | exact hdet | linear_combination hdet | ring

theorem toAdd_apply_upper {A B : GL (Fin 2) K} (hA : Om4.IsUT A) (hB : Om4.IsUT B)
    (τ : K ≃+* K) {Z : Matrix (Fin 2) (Fin 2) K} (hZ10 : Z 1 0 = 0) (hZ11 : Z 1 1 = 0) :
    (Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd Z)) :
        Matrix (Fin 2) (Fin 2) K) 0 1 =
      (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 * τ (Z 0 1) ∧
    (Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd Z)) :
        Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
    (Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd Z)) :
        Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
  unfold Om4.IsUT at hA hB
  rw [MulAut.mul_apply, Om4.toAdd_lr, Om4.toAdd_frM, toAdd_ofAdd]
  refine ⟨?_, ?_, ?_⟩ <;> rw [Om4.mul_mul_transpose_entry] <;>
    simp [Matrix.map_apply, hA, hB, hZ10, hZ11]
  ring

end Model

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)

include S in
theorem mem_L0_of_orderOf_dvd (h122 : Vol2Native.Lemma122A)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) {x : G}
    (hx : x ∈ fsuM T L) (hxo : orderOf x ∣ 2 ^ n - 1) : x ∈ fsuL0 T L := by
  have := S.hyp.fsu.simple
  have hf := S.hyp.fsu.faithful
  obtain ⟨K, _, _, hK, ⟨eL⟩⟩ := S.exists_quot_equiv_sl2 h37c h38c
  have hcardL : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr eL.toEquiv, Vol2.Ch10.SecA.card_SL_two_pow hK]
  refine Vol2.Ch10.SecC.mem_of_forall_primePow (N := 2 ^ n - 1) (fun p hp hpN y hy k hyk => ?_)
    x hx hxo
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, by have := S.two_le; omega⟩) odd_one
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr hpN)
  have hpL : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [hcardL]
    refine Dvd.dvd.mul_left (hpN.trans ?_) _
    have : 4 ^ n - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      zify [h1, Nat.one_le_pow _ _ (show 0 < 2 ^ n by positivity)]
      ring
    rw [this]
    exact Dvd.intro _ rfl
  have h := h122 G S.hyp.fsu.simple S.hyp.fsu.nonabelian
    (qtkeCore_of_cat S.hyp.fsu.nonabelian S.hyp.fsu.qtke) (fsuM T L) L
    (Vol2.Ch10.SecA.pCoreOf_fsuM_ne_bot hf) (Vol2.Ch10.SecA.mem_cComp_fsuM hf.1) p hp hp2
    (Vol2.Ch10.SecA.ncard_conjSubgroupsBy_fsuM h37c h38c S.hyp.fsu.simple S.hyp.fsu.nonabelian
      S.hyp.fsu.qtke hf S.not_le_normalizer_L) hpL
  rw [Vol2.Ch10.SecA.conjClosure_fsuM] at h
  rw [← h]
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hyk)
  exact Subgroup.subset_closure ⟨hy, j, hj⟩

omit [Finite G] in
theorem mem_oTwoUpper_inf {H : Subgroup G} {x : G} (hx : x ∈ H ⊓ fsuM T L)
    (hodd : Odd (orderOf x)) : x ∈ oTwoUpper H ⊓ fsuM T L :=
  ⟨mem_oTwoUpper_of_odd hx.1 hodd, hx.2⟩

include S in
theorem hall_abelian (h4414 : Stmt4_4_14) (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1 : zQ T I = fsuV T I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) :
    ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨P, hP, hPN⟩, -⟩ := S.hall_faithful h4414 h37 h38 h39 h1 hH hn1
  have hInM : InM T (fsuM T L) := ⟨S.uniq.1.1, le_sup_right.trans S.uniq.1.2⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ fsuM T L :=
    ((h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke S.hyp.fsu.sylow).2 L
      S.hyp.fsu.maximal S.hyp.fsu.quasisimple).2.2.2.1
  obtain ⟨B₀, hB₀, hB₀c, -⟩ := Vol2.Ch11.SecB.derivedHallBorel_ofC hE22
    Vol2.Ch11.SecB.factBorelComm_holds G T (fsuM T L) H S.hyp.fsu.simple S.hyp.fsu.nonabelian
    S.hyp.fsu.qtke S.hyp.fsu.sylow hInM hNT hH hn1
  set N := oTwoUpper H ⊓ fsuM T L with hN
  have hNX : N ≤ H ⊓ fsuM T L := inf_le_inf_right _ (oTwoUpper_le H)
  have hBN : ∀ (X : Subgroup G), QuasithinUnique.Lin2.IsHallTwoPrimeOf X (H ⊓ fsuM T L) →
      X ≤ N := fun X hX x hx => mem_oTwoUpper_inf (hX.1 hx)
        (hX.2.1.of_dvd_nat (X.orderOf_dvd_natCard hx))
  have hB₀N : QuasithinUnique.Lin2.IsHallTwoPrimeOf B₀ N := by
    refine ⟨hBN B₀ hB₀, hB₀.2.1, ?_⟩
    obtain ⟨k, hk⟩ := hB₀.2.2
    have h1 := Subgroup.relIndex_mul_relIndex B₀ N (H ⊓ fsuM T L) (hBN B₀ hB₀) hNX
    rw [hk] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ h1)
    exact ⟨j, hj⟩
  obtain ⟨-, -, hdec⟩ := QuasithinUnique.Lin2.hall_sylow_decomp hP hPN hB₀N
  have hPn : (P.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP.1).mpr hPN
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ P := by
    intro x hx y hy
    obtain ⟨p₁, hp₁, d₁, hd₁, rfl⟩ := hdec x hx
    obtain ⟨p₂, hp₂, d₂, hd₂, rfl⟩ := hdec y hy
    let π := QuotientGroup.mk' (P.subgroupOf N)
    have hd₁N : d₁ ∈ N := hB₀N.1 hd₁
    have hd₂N : d₂ ∈ N := hB₀N.1 hd₂
    have hp₁N : p₁ ∈ N := hP.1 hp₁
    have hp₂N : p₂ ∈ N := hP.1 hp₂
    have hπ1 : π ⟨p₁, hp₁N⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hp₁)
    have hπ2 : π ⟨p₂, hp₂N⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hp₂)
    have hdd : (⟨d₁, hd₁N⟩ : ↥N) * ⟨d₂, hd₂N⟩ = ⟨d₂, hd₂N⟩ * ⟨d₁, hd₁N⟩ :=
      Subtype.ext (hB₀c d₁ hd₁ d₂ hd₂)
    have key : π (⟨p₁, hp₁N⟩ * ⟨d₁, hd₁N⟩ * (⟨p₂, hp₂N⟩ * ⟨d₂, hd₂N⟩) *
        (⟨p₁, hp₁N⟩ * ⟨d₁, hd₁N⟩)⁻¹ * (⟨p₂, hp₂N⟩ * ⟨d₂, hd₂N⟩)⁻¹) = 1 := by
      simp only [map_mul, map_inv, hπ1, hπ2, one_mul]
      rw [← map_mul, hdd, map_mul]
      group
    have := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp key)
    simpa using this
  intro x hx y hy
  have hc := hcomm x (hBN B hB hx) y (hBN B hB hy)
  have hcB : x * y * x⁻¹ * y⁻¹ ∈ B :=
    B.mul_mem (B.mul_mem (B.mul_mem hx hy) (B.inv_mem hx)) (B.inv_mem hy)
  have hPB : P ⊓ B = ⊥ := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP.2.1
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [ha]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hB.2.1)
  have h0 : x * y * x⁻¹ * y⁻¹ = 1 := by
    have : x * y * x⁻¹ * y⁻¹ ∈ P ⊓ B := ⟨hc, hcB⟩
    rw [hPB] at this
    exact this
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h0, one_mul]

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem ut_of_mem_centralizer (h1 : zQ T I = fsuV T I) (k : ↥(fsuL0 T L))
    (hk : (k : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ψ k ∈ utFst K ∧
      (((ψ k).2 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (((ψ k).1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
        (((ψ k).2 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
  obtain ⟨z, hzV, hzZ, c, hc0, hze⟩ := hc.exists_z h1
  have hfix : bar e (Subgroup.inclusion S.L0_le_normalizer_V k) (e ⟨z, hzV⟩) = e ⟨z, hzV⟩ := by
    rw [bar_apply]
    congr 1
    refine Subtype.ext ?_
    show (k : G) * z * (k : G)⁻¹ = z
    rw [← Subgroup.mem_centralizer_iff.mp hk z hzZ, mul_inv_cancel_right]
  rw [hc.bar_L0, hze] at hfix
  have h2 := congrArg Multiplicative.toAdd hfix
  rw [toAdd_rho, toAdd_ofAdd, Matrix.mul_smul, Matrix.smul_mul] at h2
  have h3 : (((Matrix.SpecialLinearGroup.toGL (ψ k).1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      !![(1 : K), 0; 0, 0] *
      ((Matrix.SpecialLinearGroup.toGL (ψ k).2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ) =
      (1 : K) • !![(1 : K), 0; 0, 0] := by
    rw [one_smul]
    have := congrArg (fun X => c⁻¹ • X) h2
    simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    exact this
  obtain ⟨hA, hB⟩ := Om4.isUT_of_mul_e11 h3
  refine ⟨hA, hB, ?_⟩
  have h5 := congrFun (congrFun h3 0) 0
  rw [Om4.mul_mul_transpose_entry] at h5
  simp at h5
  exact h5

theorem sq_mem_centralizer (h1 : zQ T I = fsuV T I) (k : ↥(fsuL0 T L))
    (hk : (k : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hk1 : (((ψ k).1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1) :
    (k : G) ^ 2 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨hg, hh, hgh⟩ := hc.ut_of_mem_centralizer h1 k hk
  rw [hk1, one_mul] at hgh
  have hg11 := mul_eq_one_of_ut hg
  rw [hk1, one_mul] at hg11
  have hh11 := mul_eq_one_of_ut hh
  rw [hgh, one_mul] at hh11
  have hgsq : (Matrix.SpecialLinearGroup.toGL (ψ k).1) ^ 2 = 1 :=
    Om4.IsUT.sq_eq_one hg hk1 hg11
  have hhsq : (Matrix.SpecialLinearGroup.toGL (ψ k).2) ^ 2 = 1 :=
    Om4.IsUT.sq_eq_one hh hgh hh11
  have hbar : bar e (Subgroup.inclusion S.L0_le_normalizer_V (k ^ 2)) = 1 := by
    rw [hc.bar_L0, map_pow, Om4.rho_apply]
    rw [show Om4.lr (Matrix.SpecialLinearGroup.toGL ((ψ k) ^ 2).1)
        (Matrix.SpecialLinearGroup.toGL ((ψ k) ^ 2).2) =
        Om4.lr ((Matrix.SpecialLinearGroup.toGL (ψ k).1) ^ 2)
          ((Matrix.SpecialLinearGroup.toGL (ψ k).2) ^ 2) by
      rw [Prod.pow_fst, Prod.pow_snd, map_pow, map_pow]]
    rw [hgsq, hhsq, Om4.lr_one]
  have := mem_centralizer_of_bar e _ hbar
  simpa using this

theorem map_L (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) :
    (L.subgroupOf (fsuL0 T L)).map ψ =
        (MonoidHom.snd (SpecialLinearGroup (Fin 2) K) (SpecialLinearGroup (Fin 2) K)).ker ∨
      (L.subgroupOf (fsuL0 T L)).map ψ =
        (MonoidHom.fst (SpecialLinearGroup (Fin 2) K) (SpecialLinearGroup (Fin 2) K)).ker := by
  have hK4 := hc.four_le
  have := Om4.sl2_isSimple hK4
  have hcen := center_eq_bot_of_commutator_eq_top (Om4.sl2_commutator_eq_top hK4)
  set N := (L.subgroupOf (fsuL0 T L)).map ψ with hNdef
  have hloc := S.hyp.fsu.maximal.1
  have hnorm : N.Normal := by
    refine ⟨fun x hx γ => ?_⟩
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := hc.surj γ
    have hl' : (l : G) ∈ L := hl
    refine ⟨k * l * k⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show ((k * l * k⁻¹ : ↥(fsuL0 T L)) : G) ∈ L
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (Vol2.Ch10.SecA.fsuL0_le_normalizer hloc k.2) l).mp hl'
  let ψL : ↥L →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K :=
    ψ.comp (Subgroup.inclusion S.L_le_L0)
  have hrange : ψL.range = N := by
    ext γ
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion S.L_le_L0 l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
  have hker : ψL.ker = CFSG.pCore 2 ↥L := by
    rw [← Vol2.Ch10.SecA.subgroupOf_pCoreOf]
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hb : bar e (Subgroup.inclusion S.L0_le_normalizer_V (Subgroup.inclusion S.L_le_L0 l)) =
          1 := by
        rw [hc.bar_L0]
        show Om4.rho (ψL l) = 1
        rw [h, map_one]
      exact S.inf_centralizer_L_le h37c h38c ⟨l.2, mem_centralizer_of_bar e _ hb⟩
    · intro h
      apply Om4.rho_injective
      rw [map_one]
      show Om4.rho (ψ (Subgroup.inclusion S.L_le_L0 l)) = 1
      rw [← hc.bar_L0]
      refine MulEquiv.ext fun X => ?_
      obtain ⟨v, rfl⟩ := e.surjective X
      rw [bar_apply, MulAut.one_apply]
      congr 1
      refine Subtype.ext ?_
      show (l : G) * v * (l : G)⁻¹ = v
      rw [← Subgroup.mem_centralizer_iff.mp (S.pCoreOf_L_le_centralizer h) v v.2,
        mul_inv_cancel_right]
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Vol2.Ch10.SecA.isSimpleGroup_of_not_normal h37c h38c S.hyp.fsu.simple S.hyp.fsu.nonabelian
      S.hyp.fsu.qtke S.hyp.fsu.faithful S.not_le_normalizer_L
  let e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥N :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange ψL)).trans (MulEquiv.subgroupCongr hrange)
  have : IsSimpleGroup ↥N := e1.symm.isSimpleGroup
  exact eq_ker_of_normal_of_isSimpleGroup hcen hcen hnorm

theorem eq_one_of_chi (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h1 : zQ T I = fsuV T I) (k : ↥(fsuL0 T L))
    (hk : (k : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hodd : Odd (orderOf (k : G)))
    (hk1 : (((ψ k).1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1) :
    (k : G) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq := hc.sq_mem_centralizer h1 k hk hk1
  have hP : (k : G) ^ 2 ∈ pCoreOf 2 (fsuL0 T L) :=
    S.inf_centralizer_L0_le h37c h38c ⟨(fsuL0 T L).pow_mem k.2 2, hsq⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 (fsuL0 T L))) ⟨_, hP⟩
  rw [Subgroup.orderOf_mk] at hj
  have h2 : Odd (orderOf ((k : G) ^ 2)) := hodd.of_dvd_nat (orderOf_pow_dvd 2)
  rw [hj] at h2
  have hj0 : j = 0 := by
    by_contra h0
    exact (Nat.not_even_iff_odd.mpr h2) (Nat.even_pow.mpr ⟨even_two, h0⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  have h3 : orderOf (k : G) ∣ 2 := orderOf_dvd_of_pow_eq_one hj
  have h4 : orderOf (k : G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h4

theorem mem_centralizer_V1 (h1 : zQ T I = fsuV T I) (k : ↥(fsuL0 T L))
    (hk : (k : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    (k : G) ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hg, hh, hgh⟩ := hc.ut_of_mem_centralizer h1 k hk
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  have hev := hc.toAdd_e_eq hv
  set c := (Multiplicative.toAdd (e ⟨v, hv.1⟩) : Matrix (Fin 2) (Fin 2) K) 0 0 with hcdef
  have hev' : e ⟨v, hv.1⟩ = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact hev
  have hfix : bar e (Subgroup.inclusion S.L0_le_normalizer_V k) (e ⟨v, hv.1⟩) =
      e ⟨v, hv.1⟩ := by
    rw [hc.bar_L0, Om4.rho_apply, hev']
    have h2 := Om4.apply_smul_e11 (A := Matrix.SpecialLinearGroup.toGL (ψ k).1)
      (B := Matrix.SpecialLinearGroup.toGL (ψ k).2) hg hh 1 c
    rw [Om4.frM_one, mul_one] at h2
    rw [h2]
    congr 2
    change (((ψ k).1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (((ψ k).2 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * c = c
    rw [hgh, one_mul]
  rw [bar_apply] at hfix
  have h3 : (k : G) * v * (k : G)⁻¹ = v := congrArg Subtype.val (e.injective hfix)
  calc v * (k : G) = ((k : G) * v * (k : G)⁻¹) * k := by rw [h3]
    _ = k * v := by group

theorem mem_T_of_mem_uni (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (k : ↥(fsuL0 T L)) (hk : ψ k ∈ (uni K).prod (uni K)) :
    (k : G) ∈ T := by
  rw [← hc.sylow] at hk
  obtain ⟨t, ht, htk⟩ := hk
  have hker : bar e (Subgroup.inclusion S.L0_le_normalizer_V (t⁻¹ * k)) = 1 := by
    rw [hc.bar_L0, map_mul, map_inv, htk, inv_mul_cancel, map_one]
  have hV := mem_centralizer_of_bar e _ hker
  have hP : ((t⁻¹ * k : ↥(fsuL0 T L)) : G) ∈ T :=
    (S.pCoreOf_L0_le_Q (S.inf_centralizer_L0_le h37c h38c ⟨(t⁻¹ * k).2, hV⟩)).1
  have htT : (t : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht).1
  have := T.mul_mem htT hP
  simpa using this

end IsCoord

include S in
theorem hall_eq_cartan
    (hE22 : E2.E22StatementC) (h4414 : Stmt4_4_14) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h331 : Stmt3_3_1) (h122 : Vol2Native.Lemma122A) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3)
    (hH11 : Ch9InH11Plus) (h1 : zQ T I = fsuV T I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) :
    B ≤ fsuL0 T L ∧ IsCyclic B ∧ Nat.card B = 2 ^ n - 1 ∧ B ⊓ L = ⊥ ∧
      ∃ D : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf D
          (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) ∧
        B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
          ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, e, ψ, hc⟩ := S.exists_isCoord
  obtain ⟨-, hcart⟩ := S.exists_orderOf_eq hE22 h4414 hC58 h317 h331 h37c h38c h37 h38 h39
    h3228 hE610 h63 hH11 h1 hH hn1
  obtain ⟨b, hb, hbo⟩ := hcart B hB
  have hBZ := S.le_centralizer_of_hall h37c h38c hC58 h317 h1 hH hB
  have hkill : ∀ x ∈ B, x ∈ Subgroup.centralizer (fsuV T I : Set G) → x = 1 := fun x hx hxV =>
    S.eq_one_of_hall h4414 h37c h38c h37 h38 h39 h1 hH hn1 hB hx hxV
  have hBodd : ∀ x ∈ B, Odd (orderOf x) := fun x hx =>
    hB.2.1.of_dvd_nat (B.orderOf_dvd_natCard hx)
  have hab := S.hall_abelian h4414 hE22 h331 h37 h38 h39 h1 hH hn1 hB
  have hq : Fintype.card K - 1 = 2 ^ n - 1 := by rw [hc.card]
  have hbL : b ∈ fsuL0 T L := S.mem_L0_of_orderOf_dvd h122 h37c h38c (hB.1 hb).2 (by rw [hbo])
  set kb : ↥(fsuL0 T L) := ⟨b, hbL⟩ with hkb
  obtain ⟨hgb, hhb, hghb⟩ := hc.ut_of_mem_centralizer h1 kb (hBZ hb)
  set α := (((ψ kb).1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 with hα
  have hα0 : α ≠ 0 := left_ne_zero_of_mul_eq_one hghb
  set u : Kˣ := Units.mk0 α hα0 with hu
  have hpowα : ∀ j : ℕ, (((ψ (kb ^ j)).1 : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0 = α ^ j := by
    intro j
    have h3 := Om4.IsUT.pow_apply_zero_zero (A := Matrix.SpecialLinearGroup.toGL (ψ kb).1) hgb j
    rw [map_pow, Prod.pow_fst]
    rw [← map_pow] at h3
    exact h3
  have hαo : orderOf u = 2 ^ n - 1 := by
    refine le_antisymm ?_ ?_
    · have h2 := orderOf_dvd_natCard u
      rw [Nat.card_units, Nat.card_eq_fintype_card, hc.card] at h2
      have h3 : 0 < 2 ^ n - 1 := by
        have h4 : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := S.two_le; omega)
        omega
      exact Nat.le_of_dvd h3 h2
    · have h2 : α ^ orderOf u = 1 := by
        have h := congrArg Units.val (pow_orderOf_eq_one u)
        rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
      have hk1 := hpowα (orderOf u)
      rw [h2] at hk1
      have h3 := hc.eq_one_of_chi h37c h38c h1 (kb ^ orderOf u) (by
        show b ^ orderOf u ∈ _
        exact Subgroup.pow_mem _ (hBZ hb) _) (by
        show Odd (orderOf (b ^ orderOf u))
        exact (hBodd b hb).of_dvd_nat (orderOf_pow_dvd _)) hk1
      have h4 : b ^ orderOf u = 1 := h3
      rw [← hbo]
      exact Nat.le_of_dvd (orderOf_pos u) (orderOf_dvd_of_pow_eq_one h4)
  have hgen : ∀ c : K, c ≠ 0 → ∃ j : ℕ, c = α ^ j := by
    classical
    intro c hc0
    have htop : Subgroup.zpowers u = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hαo, Nat.card_units, Nat.card_eq_fintype_card, hc.card]
    have hmem : Units.mk0 c hc0 ∈ Subgroup.zpowers u := by rw [htop]; exact Subgroup.mem_top _
    rw [(isOfFinOrder_of_finite u).mem_zpowers_iff_mem_range_orderOf] at hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    refine ⟨j, ?_⟩
    have := congrArg Units.val hj
    simpa [hu] using this.symm
  have hxL : ∀ x ∈ B, x ∈ fsuL0 T L := by
    intro x hx
    have hxM := (hB.1 hx).2
    obtain ⟨A, B', τ, hA, hB', hform⟩ :=
      hc.isUT_of_mem_centralizer h1 hxM (hBodd x hx) (hBZ hx)
    have hbar : bar e ⟨x, S.hMN hxM⟩ * bar e (Subgroup.inclusion S.L0_le_normalizer_V kb) =
        bar e (Subgroup.inclusion S.L0_le_normalizer_V kb) * bar e ⟨x, S.hMN hxM⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hab x hx b hb)
    rw [hform, hc.bar_L0, Om4.rho_apply] at hbar
    have hg' : Om4.lr (Matrix.SpecialLinearGroup.toGL (ψ kb).1)
        (Matrix.SpecialLinearGroup.toGL (ψ kb).2) =
        Om4.lr (Matrix.SpecialLinearGroup.toGL (ψ kb).1)
          (Matrix.SpecialLinearGroup.toGL (ψ kb).2) * Om4.frM 1 := by
      rw [Om4.frM_one, mul_one]
    rw [hg'] at hbar
    have hcomm : ∀ X : Om4.VM K, (Om4.lr A B' * Om4.frM τ : MulAut (Om4.VM K)) ((Om4.lr
        (Matrix.SpecialLinearGroup.toGL (ψ kb).1) (Matrix.SpecialLinearGroup.toGL (ψ kb).2) *
          Om4.frM 1 : MulAut (Om4.VM K)) X) = (Om4.lr (Matrix.SpecialLinearGroup.toGL (ψ kb).1)
          (Matrix.SpecialLinearGroup.toGL (ψ kb).2) * Om4.frM 1 : MulAut (Om4.VM K))
            ((Om4.lr A B' * Om4.frM τ : MulAut (Om4.VM K)) X) :=
      fun X => congrArg (fun f : MulAut (Om4.VM K) => f X) hbar
    have hE := congrArg (fun Y : Om4.VM K => (Multiplicative.toAdd Y : Matrix (Fin 2) (Fin 2) K)
      0 1) (hcomm (Multiplicative.ofAdd !![(0 : K), 1; 0, 0]))
    have hb1 := toAdd_apply_upper (A := Matrix.SpecialLinearGroup.toGL (ψ kb).1)
      (B := Matrix.SpecialLinearGroup.toGL (ψ kb).2) hgb hhb 1 (Z := !![(0 : K), 1; 0, 0])
      (by simp) (by simp)
    have hx1 := toAdd_apply_upper hA hB' τ (Z := !![(0 : K), 1; 0, 0]) (by simp) (by simp)
    have hL1 := toAdd_apply_upper hA hB' τ (Z := Multiplicative.toAdd ((Om4.lr
      (Matrix.SpecialLinearGroup.toGL (ψ kb).1) (Matrix.SpecialLinearGroup.toGL (ψ kb).2) *
        Om4.frM 1 : MulAut (Om4.VM K)) (Multiplicative.ofAdd !![(0 : K), 1; 0, 0])))
      hb1.2.1 hb1.2.2
    have hR1 := toAdd_apply_upper (A := Matrix.SpecialLinearGroup.toGL (ψ kb).1)
      (B := Matrix.SpecialLinearGroup.toGL (ψ kb).2) hgb hhb 1
      (Z := Multiplicative.toAdd ((Om4.lr A B' * Om4.frM τ : MulAut (Om4.VM K))
        (Multiplicative.ofAdd !![(0 : K), 1; 0, 0]))) hx1.2.1 hx1.2.2
    rw [ofAdd_toAdd] at hL1 hR1
    rw [hL1.1, hR1.1, hb1.1, hx1.1] at hE
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_one, mul_one, RingAut.one_apply] at hE
    have hh11 : (((ψ kb).2 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = α := by
      have h2 := mul_eq_one_of_ut (g := (ψ kb).2) hhb
      have h3 : (((ψ kb).2 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
          α⁻¹ := eq_inv_of_mul_eq_one_right hghb
      rw [h3] at h2
      field_simp at h2
      exact h2
    obtain ⟨hA0, -⟩ := hA.apply_ne_zero
    obtain ⟨-, hB1⟩ := hB'.apply_ne_zero
    change (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B' : Matrix (Fin 2) (Fin 2) K) 1 1 *
      τ (((Matrix.SpecialLinearGroup.toGL (ψ kb).1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
        ((Matrix.SpecialLinearGroup.toGL (ψ kb).2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) =
      ((Matrix.SpecialLinearGroup.toGL (ψ kb).1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
        ((Matrix.SpecialLinearGroup.toGL (ψ kb).2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 *
          ((A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B' : Matrix (Fin 2) (Fin 2) K) 1 1) at hE
    have hτα2 : τ (α * α) = α * α := by
      have h2 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B' : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 :=
        mul_ne_zero hA0 hB1
      have h3 : ((Matrix.SpecialLinearGroup.toGL (ψ kb).1 : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 0 0 = α := rfl
      have h4 : ((Matrix.SpecialLinearGroup.toGL (ψ kb).2 : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 1 1 = α := hh11
      rw [h3, h4] at hE
      exact mul_left_cancel₀ h2 (by rw [hE]; ring)
    have hτα : τ α = α := by
      rw [map_mul] at hτα2
      have h2 : (τ α - α) ^ 2 = 0 := by
        have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination hτα2 + (α * α - τ α * α) * h22
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
    have hτ1 : τ = 1 := by
      refine RingEquiv.ext fun c => ?_
      by_cases hc0 : c = 0
      · rw [hc0, map_zero]; rfl
      · obtain ⟨j, rfl⟩ := hgen c hc0
        rw [map_pow, hτα]
        rfl
    have hpow := Om4.pow_eq_one_of_isUT hA hB' (τ := τ) (k := 1) (by rw [pow_one, hτ1])
    rw [hc.card, one_mul, ← hform] at hpow
    set y : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨x, S.hMN hxM⟩ with hy
    have hyodd : Odd (orderOf (bar e y)) := by
      have := orderOf_map_dvd (bar e) y
      rw [hy, Subgroup.orderOf_mk] at this
      exact (hBodd x hx).of_dvd_nat this
    have hdvd : orderOf (bar e y) ∣ 2 ^ n - 1 :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_right.mpr hyodd)
        (orderOf_dvd_of_pow_eq_one hpow)
    have hy1 : bar e (y ^ (2 ^ n - 1)) = 1 := by
      rw [map_pow]
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hxV : x ^ (2 ^ n - 1) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
      have := mem_centralizer_of_bar e _ hy1
      simpa [hy] using this
    have hx1 := hkill _ (B.pow_mem hx _) hxV
    exact S.mem_L0_of_orderOf_dvd h122 h37c h38c hxM (orderOf_dvd_of_pow_eq_one hx1)
  have hBL : B ≤ fsuL0 T L := fun x hx => hxL x hx
  have hut : ∀ x : ↥B, ψ (Subgroup.inclusion hBL x) ∈ utFst K := fun x =>
    (hc.ut_of_mem_centralizer h1 _ (hBZ x.2)).1
  let χB : ↥B →* Kˣ := (chiFst K).comp ((ψ.comp (Subgroup.inclusion hBL)).codRestrict _ hut)
  have hχ : Function.Injective χB := by
    rw [injective_iff_map_eq_one]
    intro x hx1
    have h2 : (((ψ (Subgroup.inclusion hBL x)).1 : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
      have := congrArg Units.val hx1
      simpa [χB, coe_chiFst] using this
    have h3 := hc.eq_one_of_chi h37c h38c h1 (Subgroup.inclusion hBL x) (hBZ x.2)
      (by simpa using hBodd x x.2) h2
    exact Subtype.ext h3
  have hcardB : Nat.card B = 2 ^ n - 1 := by
    refine le_antisymm ?_ ?_
    · have h2 := Nat.card_le_card_of_injective χB hχ
      rwa [Nat.card_units, hc.natCard] at h2
    · rw [← hbo]
      exact Nat.le_of_dvd Nat.card_pos (B.orderOf_dvd_natCard hb)
  have hcyc : IsCyclic B := by
    have : IsCyclic ↥χB.range := Subgroup.isCyclic _
    exact isCyclic_of_surjective (MonoidHom.ofInjective hχ).symm.toMonoidHom
      (MonoidHom.ofInjective hχ).symm.surjective
  have hBLbot : B ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxL'⟩
    have hmem : ψ (Subgroup.inclusion hBL ⟨x, hxB⟩) ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
      ⟨Subgroup.inclusion hBL ⟨x, hxB⟩, Subgroup.mem_subgroupOf.mpr hxL', rfl⟩
    obtain ⟨-, -, hgh⟩ := hc.ut_of_mem_centralizer h1 (Subgroup.inclusion hBL ⟨x, hxB⟩)
      (hBZ hxB)
    have h2 : (((ψ (Subgroup.inclusion hBL ⟨x, hxB⟩)).1 : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
      rcases hc.map_L h37c h38c with h | h <;> rw [h] at hmem
      · have h3 : (ψ (Subgroup.inclusion hBL ⟨x, hxB⟩)).2 = 1 := hmem
        rw [h3, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, mul_one] at hgh
        exact hgh
      · have h3 : (ψ (Subgroup.inclusion hBL ⟨x, hxB⟩)).1 = 1 := hmem
        rw [h3, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
    have h3 := hc.eq_one_of_chi h37c h38c h1 (Subgroup.inclusion hBL ⟨x, hxB⟩) (hBZ hxB)
      (by simpa using hBodd x hxB) h2
    exact h3
  set P₀ := T ⊓ fsuL0 T L with hP₀
  set N₀ := fsuL0 T L ⊓ Subgroup.normalizer (P₀ : Set G) with hN₀
  have hP₀N₀ : P₀ ≤ N₀ := fun x hx => ⟨hx.2, Subgroup.le_normalizer hx⟩
  have hP₀2 : IsPGroup 2 P₀ := S.hyp.fsu.sylow.1.to_le inf_le_left
  have hP₀i : ¬ 2 ∣ P₀.relIndex N₀ := by
    intro h2
    have hS := S.isSylowTwoOf_T_inf_L0
    apply hS.2.2
    show 2 ∣ P₀.relIndex (fsuL0 T L)
    have h3 := Subgroup.relIndex_mul_relIndex P₀ N₀ (fsuL0 T L) hP₀N₀ inf_le_left
    rw [← h3]
    exact h2.mul_right _
  have hBP₀ : ∀ x ∈ B, ∀ p ∈ P₀, x * p * x⁻¹ ∈ P₀ := by
    intro x hx p hp
    have hxL0 := hxL x hx
    have hxpL : x * p * x⁻¹ ∈ fsuL0 T L :=
      (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hxL0 hp.2) ((fsuL0 T L).inv_mem hxL0)
    refine ⟨?_, hxpL⟩
    obtain ⟨hg, hh, -⟩ := hc.ut_of_mem_centralizer h1 ⟨x, hxL0⟩ (hBZ hx)
    have hpu : ψ ⟨p, hp.2⟩ ∈ (uni K).prod (uni K) := by
      rw [← hc.sylow]
      exact ⟨⟨p, hp.2⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
    have h2 : ψ ⟨x * p * x⁻¹, hxpL⟩ ∈ (uni K).prod (uni K) := by
      have h3 : (⟨x * p * x⁻¹, hxpL⟩ : ↥(fsuL0 T L)) = ⟨x, hxL0⟩ * ⟨p, hp.2⟩ * ⟨x, hxL0⟩⁻¹ := rfl
      rw [h3, map_mul, map_mul, map_inv]
      exact ⟨conj_mem_uni hg hpu.1, conj_mem_uni hh hpu.2⟩
    exact hc.mem_T_of_mem_uni h37c h38c _ h2
  have hBN : B ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.mpr fun p => ⟨fun hp => hBP₀ x hx p hp, fun hp => ?_⟩
    have := hBP₀ x⁻¹ (B.inv_mem hx) _ hp
    simpa [mul_assoc] using this
  have hBN₀ : B ≤ N₀ := fun x hx => ⟨hxL x hx, hBN hx⟩
  obtain ⟨D, hD, n', hn', hBD⟩ := Vol2.Ch10.SecB.C11AmS.exists_hall_le_normalizer hP₀N₀ hP₀2
    hP₀i inf_le_right hBN (hBN₀.trans Subgroup.le_normalizer) hB.2.1
  set B' := B.map (MulAut.conj n'⁻¹).toMonoidHom with hB'
  have hcardB' : Nat.card B' = Nat.card B :=
    (Nat.card_congr (B.equivMapOfInjective _ (MulAut.conj n'⁻¹).injective).toEquiv).symm
  have hn'N : n' ∈ N₀ := hP₀N₀ hn'
  have hB'N : B' ≤ N₀ := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using
      N₀.mul_mem (N₀.mul_mem (N₀.inv_mem hn'N) (hBN₀ hx)) hn'N
  have hB'D : B' ≤ D := by
    have h2 := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hBD
    have hXodd : Odd (Nat.card ↥(B' ⊔ D)) := by
      have h3 : Odd (Nat.card ↥B' * Nat.card ↥D) := (hcardB' ▸ hB.2.1).mul hD.2.1
      exact h3.of_dvd_nat (Dvd.intro _ h2)
    have hXN : B' ⊔ D ≤ N₀ := sup_le hB'N hD.1
    obtain ⟨k, hk⟩ := hD.2.2
    have h4 := Subgroup.relIndex_mul_relIndex D (B' ⊔ D) N₀ le_sup_right hXN
    rw [hk] at h4
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ h4)
    have h5 : D.relIndex (B' ⊔ D) ∣ Nat.card ↥(B' ⊔ D) := Subgroup.relIndex_dvd_card _ _
    rw [hj] at h5
    have hj0 : j = 0 := by
      by_contra h0
      exact (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr
        ((dvd_pow_self 2 h0).trans h5))
    rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
    exact le_sup_left.trans hj
  set D' := D.map (MulAut.conj n').toMonoidHom with hD'
  have hBD' : B ≤ D' := by
    intro x hx
    refine ⟨n'⁻¹ * x * n', hB'D ⟨x, hx, by simp⟩, ?_⟩
    simp [mul_assoc]
  have hD'h : QuasithinUnique.Lin2.IsHallTwoPrimeOf D' N₀ := by
    obtain ⟨hDN, hodd, k, hk⟩ := hD
    have hle : D' ≤ N₀ := by
      rintro _ ⟨d, hd, rfl⟩
      simpa [MulAut.conj_apply] using N₀.mul_mem (N₀.mul_mem hn'N (hDN hd)) (N₀.inv_mem hn'N)
    have hcard : Nat.card D' = Nat.card D :=
      (Nat.card_congr (D.equivMapOfInjective _ (MulAut.conj n').injective).toEquiv).symm
    refine ⟨hle, hcard ▸ hodd, k, ?_⟩
    have h1' := Subgroup.relIndex_mul_card D' N₀
    have h2' := Subgroup.relIndex_mul_card D N₀
    rw [inf_of_le_left hle, hcard] at h1'
    rw [inf_of_le_left hDN] at h2'
    rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1'.trans h2'.symm), hk]
  refine ⟨hBL, hcyc, hcardB, hBLbot, D', hD'h, le_antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨hBD' hx, hc.mem_centralizer_V1 h1 ⟨x, hxL x hx⟩ (hBZ hx)⟩
  ·
    set X := D' ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) with hX
    have hXL : X ≤ fsuL0 T L := fun x hx => (hD'h.1 hx.1).1
    have hXZ : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
      Subgroup.centralizer_le (S.omegaOneCenter_T_le h1) hx.2
    have hXodd : ∀ x ∈ X, Odd (orderOf x) := fun x hx =>
      hD'h.2.1.of_dvd_nat (D'.orderOf_dvd_natCard hx.1)
    have hutX : ∀ x : ↥X, ψ (Subgroup.inclusion hXL x) ∈ utFst K := fun x =>
      (hc.ut_of_mem_centralizer h1 _ (hXZ x.2)).1
    let χX : ↥X →* Kˣ := (chiFst K).comp ((ψ.comp (Subgroup.inclusion hXL)).codRestrict _ hutX)
    have hχX : Function.Injective χX := by
      rw [injective_iff_map_eq_one]
      intro x hx1
      have h2 : (((ψ (Subgroup.inclusion hXL x)).1 : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
        have := congrArg Units.val hx1
        simpa [χX, coe_chiFst] using this
      exact Subtype.ext (hc.eq_one_of_chi h37c h38c h1 (Subgroup.inclusion hXL x) (hXZ x.2)
        (by simpa using hXodd x x.2) h2)
    have hcardX : Nat.card X ≤ Nat.card B := by
      have h2 := Nat.card_le_card_of_injective χX hχX
      rwa [Nat.card_units, hc.natCard, ← hcardB] at h2
    have hBX : B ≤ X := fun x hx => ⟨hBD' hx, hc.mem_centralizer_V1 h1 ⟨x, hxL x hx⟩ (hBZ hx)⟩
    exact (Subgroup.eq_of_le_of_card_ge hBX hcardX).ge

end Setup

end CFSG.Quasithin.H13.Ch9

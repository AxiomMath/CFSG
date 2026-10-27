module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Transport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

private lemma coe_det_map {R S : Type*} [Field R] [Field S] (e : R ≃+* S)
    (A : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map e.toRingHom A) : Sˣ) : S) = e (A.det : R) := by
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

private lemma map_mk_mem_pslRange_iff {R S : Type*} [Field R] [Field S] (e : R ≃+* S)
    (A : GL (Fin 2) R) :
    (Matrix.ProjGenLinGroup.map e.toRingHom (Matrix.ProjGenLinGroup.mk A) : PGL2 S) ∈
        pslRange S ↔ (Matrix.ProjGenLinGroup.mk A : PGL2 R) ∈ pslRange R := by
  rw [Matrix.ProjGenLinGroup.map_mk, pgl2_mk_mem_psl2_range_iff_det_isSquare,
    pgl2_mk_mem_psl2_range_iff_det_isSquare]
  constructor
  · rintro ⟨c, hc⟩
    have hc' : e (A.det : R) = c * c := by
      rw [← hc]
      exact (coe_det_map e A).symm
    obtain ⟨d, rfl⟩ := e.surjective c
    refine ⟨d, ?_⟩
    apply e.injective
    rw [map_mul, hc']
  · rintro ⟨c, hc⟩
    refine ⟨e c, ?_⟩
    rw [coe_det_map, hc, map_mul]

private lemma map_pslRange_eq {R S : Type*} [Field R] [Field S] (e : R ≃+* S) :
    (pslRange R).map (Matrix.ProjGenLinGroup.map (n := Fin 2) e.toRingHom) = pslRange S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
    exact (map_mk_mem_pslRange_iff e A).mpr hy
  · intro x hx
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    let A' : GL (Fin 2) R := Matrix.GeneralLinearGroup.map (n := Fin 2) e.symm.toRingHom A
    have hcomp : (↑e : R →+* S).comp (↑e.symm : S →+* R) = RingHom.id S := by
      ext y
      simp
    have hA' : Matrix.GeneralLinearGroup.map (n := Fin 2) e.toRingHom A' = A := by
      dsimp [A']
      rw [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp, hcomp,
        Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply]
    have hmem : (Matrix.ProjGenLinGroup.mk A' : PGL2 R) ∈ pslRange R :=
      (map_mk_mem_pslRange_iff e A').mp (by
        rw [Matrix.ProjGenLinGroup.map_mk, hA']
        exact hx)
    refine Subgroup.mem_map.mpr ⟨Matrix.ProjGenLinGroup.mk A', hmem, ?_⟩
    rw [Matrix.ProjGenLinGroup.map_mk, hA']

private lemma projGenLinGroup_map_injective {R S : Type*} [Field R] [Field S]
    (e : R ≃+* S) :
    Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2) e.toRingHom) := by
  have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext x
    simp
  refine Function.LeftInverse.injective
    (g := Matrix.ProjGenLinGroup.map (n := Fin 2) e.symm.toRingHom) ?_
  intro x
  rw [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp, hcomp,
    Matrix.ProjGenLinGroup.map_id, MonoidHom.id_apply]

private lemma mk_eq_mk_of_mul_scalar {K : Type*} [Field K]
    {A B : GL (Fin 2) K} {c : K} (hc : c ≠ 0)
    (h : (A : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) c =
      (B : Matrix (Fin 2) (Fin 2) K)) :
    (Matrix.ProjGenLinGroup.mk A : PGL2 K) = Matrix.ProjGenLinGroup.mk B := by
  refine (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr ⟨Units.mk0 c hc, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simpa [Matrix.GeneralLinearGroup.coe_scalar] using congrFun (congrFun h i) j

private lemma mk_pow_eq_one_of_val_pow_eq_smul {K : Type*} [Field K]
    {X : GL (Fin 2) K} (n : ℕ) {c : K}
    (h : (↑(X ^ n) : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hc : c ≠ 0) :
    (Matrix.ProjGenLinGroup.mk X : PGL2 K) ^ n = 1 := by
  rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨c, ?_⟩
  rw [Matrix.scalar_apply, h]
  ext i j
  simp [Matrix.diagonal, Matrix.one_apply]

private lemma mk_pow_ne_one_of_val_pow_eq_matrix {K : Type*} [Field K]
    {X : GL (Fin 2) K} (n : ℕ) {M : Matrix (Fin 2) (Fin 2) K}
    (h : (↑(X ^ n) : Matrix (Fin 2) (Fin 2) K) = M)
    (hM : M 0 1 ≠ 0 ∨ M 1 0 ≠ 0) :
    (Matrix.ProjGenLinGroup.mk X : PGL2 K) ^ n ≠ 1 := by
  rw [← map_pow]
  intro hx
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hx
  obtain ⟨c, hc⟩ := hx
  rw [h] at hc
  rcases hM with h | h
  · apply h
    have h01 := congrFun (congrFun hc 0) 1
    simpa [Matrix.scalar_apply, Matrix.diagonal] using h01.symm
  · apply h
    have h10 := congrFun (congrFun hc 1) 0
    simpa [Matrix.scalar_apply, Matrix.diagonal] using h10.symm

private lemma eq_of_dvd_card_of_simple {G : Type*} [Group G] [Finite G]
    {M J : Subgroup G} (hMJ : M ≤ J) (hsimple : IsSimpleGroup ↥J)
    {D N : ℕ} (hN : N = 2 * D) (hD : 1 < D)
    (hdvd : D ∣ Nat.card M) (hJcard : Nat.card J = N) :
    M = J := by
  have hcardMdvd : Nat.card M ∣ Nat.card J := Subgroup.card_dvd_of_le hMJ
  have hle : Nat.card M ≤ N := by
    rw [← hJcard]
    exact Nat.le_of_dvd Nat.card_pos hcardMdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk_le : k ≤ 2 := by
    have h1 : D * k ≤ D * 2 := by
      rw [hk] at hle
      rw [hN] at hle
      simpa [mul_comm] using hle
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      have hMpos : 0 < Nat.card M := Nat.card_pos
      rw [h0, mul_zero] at hk
      rw [hk] at hMpos
      omega
    · exact hpos
  have hk_cases : k = 1 ∨ k = 2 := by omega
  have hsubcard : Nat.card (M.subgroupOf J) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMJ).toEquiv
  rcases hk_cases with rfl | rfl
  · have hcardM : Nat.card M = D := by simpa using hk
    have hindex : (M.subgroupOf J).index = 2 := by
      have h := (M.subgroupOf J).card_mul_index
      rw [hsubcard, hcardM, hJcard, hN] at h
      have h' : D * (M.subgroupOf J).index = D * 2 := by
        rw [h]
        ring
      exact Nat.mul_left_cancel (by omega) h'
    have hnormal : (M.subgroupOf J).Normal := Subgroup.normal_of_index_eq_two hindex
    have hsimple' := hsimple
    rw [Subgroup.isSimpleGroup_iff] at hsimple'
    obtain ⟨-, hdich⟩ := hsimple'
    rcases hdich M hMJ hnormal with hbot | htop
    · exfalso
      rw [hbot, Subgroup.card_bot, mul_one] at hk
      omega
    · exact htop
  · refine Subgroup.eq_of_le_of_card_ge hMJ ?_
    rw [hk, hJcard, hN]
    omega

private lemma eq_of_orderOf_eq_two_of_isCyclic {P : Type*} [Group P] [Finite P]
    [IsCyclic P] {a b : P} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  have hcard : Nat.card (Subgroup.zpowers a) = Nat.card (Subgroup.zpowers b) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, ha, hb]
  have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  have ha_mem : a ∈ Subgroup.zpowers b := by
    rw [← heq]
    exact Subgroup.mem_zpowers a
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha_mem
  have hb2 : b ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← hb]
    exact pow_orderOf_eq_one b
  rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
  · have h1 : a = 1 := by
      rw [← Int.mul_ediv_add_emod n 2, hn0, add_zero, zpow_mul, hb2, one_zpow] at hn
      exact hn.symm
    rw [h1, orderOf_one] at ha
    omega
  · rw [← Int.mul_ediv_add_emod n 2, hn1, zpow_add, zpow_mul, hb2, one_zpow, one_mul,
      zpow_one] at hn
    exact hn.symm

private lemma odd_orderOf_of_mem_torus {K : Type*} [Field K] [Finite K]
    {U : Subgroup (PGL2 K)} {s x : PGL2 K} (hUc : IsCyclic U) (hsU : s ∈ U)
    (hsJ : s ∉ pslRange K) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hxU : x ∈ U)
    (hxJ : x ∈ pslRange K) : Odd (orderOf x) := by
  letI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨m, hm⟩ := hodd
  have hxpos : 0 < orderOf x := orderOf_pos x
  have hmpos : 0 < m := by omega
  let z : PGL2 K := x ^ m
  have hzU : z ∈ U := U.pow_mem hxU m
  have hzJ : z ∈ pslRange K := (pslRange K).pow_mem hxJ m
  have hzord : orderOf z = 2 := by
    simp only [z]
    rw [orderOf_pow, hm]
    have hgcd : Nat.gcd (m + m) m = m :=
      Nat.gcd_eq_right (dvd_add (dvd_refl m) (dvd_refl m))
    rw [hgcd, show m + m = 2 * m by ring]
    exact Nat.mul_div_cancel 2 hmpos
  have hsord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hzU' : orderOf (⟨z, hzU⟩ : U) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hzord
  have hsU' : orderOf (⟨s, hsU⟩ : U) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hsord
  have heq : (⟨z, hzU⟩ : U) = ⟨s, hsU⟩ :=
    eq_of_orderOf_eq_two_of_isCyclic (P := ↥U) (a := ⟨z, hzU⟩) (b := ⟨s, hsU⟩) hzU' hsU'
  have hzs : z = s := congrArg Subtype.val heq
  exact hsJ (hzs ▸ hzJ)

private structure StandardData (L : Type*) [Field L] where
  t0 : PGL2 L
  b0 : PGL2 L
  ht0J : t0 ∈ pslRange L
  hb0J : b0 ∉ pslRange L
  ht0 : t0 * t0 = 1
  ht01 : t0 ≠ 1
  hb0 : b0 * b0 = 1
  hcomm : t0 * b0 = b0 * t0
  hgen : ParrottGen (pslRange L) t0 b0

private noncomputable def StandardData.map {R S : Type*} [Field R] [Field S] (d : StandardData R)
    (e : R ≃+* S) : StandardData S := by
  let f : PGL2 R →* PGL2 S := Matrix.ProjGenLinGroup.map (n := Fin 2) e.toRingHom
  have hf : Function.Injective f := projGenLinGroup_map_injective e
  have hJ : (pslRange R).map f = pslRange S := map_pslRange_eq e
  refine ⟨f d.t0, f d.b0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hJ]
    exact Subgroup.mem_map_of_mem f d.ht0J
  · intro h
    rw [← hJ] at h
    obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp h
    exact d.hb0J (hf hyf ▸ hy)
  · rw [← map_mul, d.ht0, map_one]
  · intro h
    apply d.ht01
    apply hf
    rw [h, map_one]
  · rw [← map_mul, d.hb0, map_one]
  · rw [← map_mul, ← map_mul, d.hcomm]
  · simpa [hJ] using ParrottGen.map hf d.hgen

private theorem parrottGen_reduce {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {t0 b0 : PGL2 K} (ht0J : t0 ∈ pslRange K) (hb0J : b0 ∉ pslRange K)
    (ht0 : t0 * t0 = 1) (ht01 : t0 ≠ 1) (hb0 : b0 * b0 = 1)
    (hcomm0 : t0 * b0 = b0 * t0) (h0 : ParrottGen (pslRange K) t0 b0) :
    ∀ {t β : PGL2 K}, t ∈ pslRange K → β ∉ pslRange K → t * t = 1 → t ≠ 1 →
      β * β = 1 → t * β = β * t → ParrottGen (pslRange K) t β := by
  intro t β htJ hβJ ht ht1 hβ hcomm
  letI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  haveI hJnorm : (pslRange K).Normal := pslRange_normal hK hcard
  have hcommJ : commutator (PGL2 K) = pslRange K :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  have hb01 : b0 ≠ 1 := fun h => hb0J (h ▸ (pslRange K).one_mem)
  have hβ1 : β ≠ 1 := fun h => hβJ (h ▸ (pslRange K).one_mem)
  obtain ⟨c, hc⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate K hK hcard
    (a := b0) (b := β) ⟨hb01, by rw [pow_two]; exact hb0⟩
    ⟨hβ1, by rw [pow_two]; exact hβ⟩
    (by rw [hcommJ]; exact hb0J) (by rw [hcommJ]; exact hβJ))
  let t' : PGL2 K := c⁻¹ * t * c
  have ht'J : t' ∈ pslRange K := by
    simpa [t'] using Subgroup.Normal.conj_mem (inferInstance : (pslRange K).Normal) t htJ c⁻¹
  have ht'sq : t' * t' = 1 := by
    simp only [t']
    calc (c⁻¹ * t * c) * (c⁻¹ * t * c) = c⁻¹ * (t * t) * c := by group
      _ = 1 := by rw [ht]; group
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
      _ = 1 := by rw [show c⁻¹ * t * c = 1 by simpa [t'] using h]; group
  have hc1 : c * b0 = β * c := by rw [← hc]; group
  have hc2 : b0 * c⁻¹ = c⁻¹ * β := by rw [← hc]; group
  have ht'C : t' * b0 = b0 * t' := by
    simp only [t']
    calc c⁻¹ * t * c * b0 = c⁻¹ * t * (c * b0) := by group
      _ = c⁻¹ * t * (β * c) := by rw [hc1]
      _ = c⁻¹ * (t * β) * c := by group
      _ = c⁻¹ * (β * t) * c := by rw [hcomm]
      _ = (c⁻¹ * β) * (t * c) := by group
      _ = (b0 * c⁻¹) * (t * c) := by rw [← hc2]
      _ = b0 * (c⁻¹ * t * c) := by group
  obtain ⟨U, w, hUc, -, hb0U, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard (by rw [pow_two]; exact hb0) hb0J
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hwN : w ∈ Subgroup.normalizer (U : Set (PGL2 K)) :=
    zpowers_le_normalizer_of_inverting hww hwinv (Subgroup.mem_zpowers w)
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have ht'C' : t' ∈ Subgroup.centralizer ({b0} : Set (PGL2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr ht'C
  rw [hC] at ht'C'
  have ht'U : t' ∉ U := by
    intro h
    have hodd := odd_orderOf_of_mem_torus (U := U) hUc hb0U hb0J hb0 hb01 h ht'J
    have h2 : orderOf t' = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht'sq) ht'1
    rw [h2] at hodd
    exact absurd hodd (by decide)
  have ht'rep := ht'C'
  rw [sup_comm, mem_zpowers_sup_iff hwN (by rw [pow_two]; exact hww)] at ht'rep
  obtain ⟨a0, ha0U, ht'eq | ht'eq⟩ := ht'rep
  · exfalso
    exact ht'U (ht'eq ▸ ha0U)
  have ha0 : t' = a0⁻¹ * w := by
    rw [ht'eq]
    calc w * a0 = (w * a0 * w⁻¹) * w := by group
      _ = a0⁻¹ * w := by rw [hwinv a0 ha0U]
  let a : PGL2 K := a0⁻¹
  have haU : a ∈ U := U.inv_mem ha0U
  have ht'a : t' = a * w := ha0
  have ht0C : t0 ∈ Subgroup.centralizer ({b0} : Set (PGL2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm0
  rw [hC] at ht0C
  have ht0U : t0 ∉ U := by
    intro h
    have hodd := odd_orderOf_of_mem_torus (U := U) hUc hb0U hb0J hb0 hb01 h ht0J
    have h2 : orderOf t0 = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht0) ht01
    rw [h2] at hodd
    exact absurd hodd (by decide)
  have ht0rep := ht0C
  rw [sup_comm, mem_zpowers_sup_iff hwN (by rw [pow_two]; exact hww)] at ht0rep
  obtain ⟨b0c, hb0cU, ht0eq | ht0eq⟩ := ht0rep
  · exfalso
    exact ht0U (ht0eq ▸ hb0cU)
  have hb0' : t0 = b0c⁻¹ * w := by
    rw [ht0eq]
    calc w * b0c = (w * b0c * w⁻¹) * w := by group
      _ = b0c⁻¹ * w := by rw [hwinv b0c hb0cU]
  let b : PGL2 K := b0c⁻¹
  have hbU : b ∈ U := U.inv_mem hb0cU
  have ht0b : t0 = b * w := hb0'
  have hw_mul : ∀ u ∈ U, w * u = u⁻¹ * w := by
    intro u hu
    calc w * u = (w * u * w⁻¹) * w := by group
      _ = u⁻¹ * w := by rw [hwinv u hu]
  have hdJ : b⁻¹ * a ∈ pslRange K := by
    have h : t'⁻¹ * t0 = b⁻¹ * a := by
      rw [ht'a, ht0b]
      calc
        (a * w)⁻¹ * (b * w) = w * a⁻¹ * b * w := by
          rw [mul_inv_rev, hw']
          group
        _ = w * (a⁻¹ * b) * w := by group
        _ = (a⁻¹ * b)⁻¹ := by
          have h := hwinv (a⁻¹ * b) (U.mul_mem (U.inv_mem haU) hbU)
          rwa [hw'] at h
        _ = b⁻¹ * a := by group
    rw [← h]
    exact (pslRange K).mul_mem ((pslRange K).inv_mem ht'J) ht0J
  have hdU : b⁻¹ * a ∈ U := U.mul_mem (U.inv_mem hbU) haU
  have hodd : Odd (orderOf (b⁻¹ * a)) :=
    odd_orderOf_of_mem_torus (U := U) hUc hb0U hb0J hb0 hb01 hdU hdJ
  obtain ⟨m, hm⟩ := hodd
  let y : PGL2 K := (b⁻¹ * a) ^ (m + 1)
  have hyU : y ∈ U := U.pow_mem hdU (m + 1)
  have hy2 : y * y = b⁻¹ * a := by
    simp only [y]
    rw [← pow_two, ← pow_mul, show (m + 1) * 2 = orderOf (b⁻¹ * a) + 1 by omega,
      pow_succ, pow_orderOf_eq_one, one_mul]
  have hwy : w * y * w = y⁻¹ := by
    have h := hwinv y hyU
    rwa [hw'] at h
  have hyw : y * w * y⁻¹ = w * (y * y)⁻¹ := by
    have h2 : y * w = w * y⁻¹ := by
      have h := congrArg (fun z => w * z) hwy
      calc y * w = (w * w) * y * w := by rw [hww]; group
        _ = w * (w * y * w) := by group
        _ = w * y⁻¹ := h
    calc y * w * y⁻¹ = (w * y⁻¹) * y⁻¹ := by rw [h2]
      _ = w * (y * y)⁻¹ := by rw [mul_inv_rev]; group
  have hy_conj : y * t0 * y⁻¹ = t' := by
    rw [ht0b, ht'a]
    calc y * (b * w) * y⁻¹ = (y * b) * (w * y⁻¹) := by group
      _ = (b * y) * (w * y⁻¹) := by rw [hUcomm y hyU b hbU]
      _ = b * (y * w * y⁻¹) := by group
      _ = b * (w * (y * y)⁻¹) := by rw [hyw]
      _ = b * ((y * y) * w) := by
        have h := hw_mul (y * y)⁻¹ (U.inv_mem (U.mul_mem hyU hyU))
        rw [h, inv_inv]
      _ = (b * (b⁻¹ * a)) * w := by
        rw [hy2]
        group
      _ = a * w := by group
  have hyb0 : y * b0 * y⁻¹ = b0 := by
    rw [hUcomm y hyU b0 hb0U]
    group
  have hmap := ParrottGen.map (f := (MulAut.conj y).toMonoidHom)
    (MulAut.conj y).injective h0
  have hJmap : (pslRange K).map (MulAut.conj y).toMonoidHom = pslRange K := by
    change (pslRange K).map (↑(MulAut.conj y)) = pslRange K
    exact Subgroup.Normal.map_conj_eq (pslRange K) y
  have hy_conj' : (MulAut.conj y).toMonoidHom t0 = t' := by
    simpa [MulAut.conj_apply] using hy_conj
  have hyb0' : (MulAut.conj y).toMonoidHom b0 = b0 := by
    simpa [MulAut.conj_apply] using hyb0
  rw [hJmap, hyb0', hy_conj'] at hmap
  have hmap2 := ParrottGen.map (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).injective hmap
  have hJmap2 : (pslRange K).map (MulAut.conj c).toMonoidHom = pslRange K := by
    change (pslRange K).map (↑(MulAut.conj c)) = pslRange K
    exact Subgroup.Normal.map_conj_eq (pslRange K) c
  have hct : (MulAut.conj c).toMonoidHom t' = t := by
    simp [MulAut.conj_apply, t']
    group
  have hcb : (MulAut.conj c).toMonoidHom b0 = β := by
    simpa [MulAut.conj_apply] using hc
  rw [hJmap2, hct, hcb] at hmap2
  exact hmap2

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private def T0_7 : GL (Fin 2) (ZMod 7) where
  val := !![0, -1; 1, 0]
  inv := !![0, 1; -1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> decide
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> decide

private def B0_7 : GL (Fin 2) (ZMod 7) where
  val := !![-1, 0; 0, 1]
  inv := !![-1, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> decide
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> decide

private def Tau_7 : GL (Fin 2) (ZMod 7) where
  val := !![4, 6; 6, 6]
  inv := !![3, 4; 4, 2]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> decide
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> decide

private def C_7 : GL (Fin 2) (ZMod 7) := B0_7 * Tau_7 * B0_7
private def M_7 : GL (Fin 2) (ZMod 7) := Tau_7 * C_7
private def N_7 : GL (Fin 2) (ZMod 7) := T0_7 * Tau_7 * C_7

private lemma seven_T0_sq : (↑(T0_7 ^ 2) : Matrix (Fin 2) (Fin 2) (ZMod 7)) =
    (-1 : ZMod 7) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 7)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, T0_7, Matrix.one_apply] <;> decide

private lemma seven_B0_sq : (↑(B0_7 ^ 2) : Matrix (Fin 2) (Fin 2) (ZMod 7)) =
    (1 : ZMod 7) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 7)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, B0_7, Matrix.one_apply] <;> decide

private lemma seven_Tau_cube : (↑(Tau_7 ^ 3) : Matrix (Fin 2) (Fin 2) (ZMod 7)) =
    (1 : ZMod 7) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 7)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two, Tau_7, Matrix.one_apply] <;> decide

private lemma seven_M_sq : (↑(M_7 ^ 2) : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![4, 5; 2, 3] := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, M_7, C_7, B0_7, Tau_7] <;> decide

private lemma seven_M_four : (↑(M_7 ^ 4) : Matrix (Fin 2) (Fin 2) (ZMod 7)) =
    (5 : ZMod 7) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 7)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two, M_7, C_7, B0_7, Tau_7, Matrix.one_apply] <;> decide

private lemma seven_N_seven : (↑(N_7 ^ 7) : Matrix (Fin 2) (Fin 2) (ZMod 7)) =
    (5 : ZMod 7) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 7)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [show (7 : ℕ) = 6 + 1 by norm_num, pow_succ, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two, N_7, C_7, B0_7, T0_7, Tau_7, Matrix.one_apply] <;> decide

private lemma seven_N_mat : (↑N_7 : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![5, 0; 1, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [N_7, C_7, B0_7, T0_7, Tau_7] <;> decide

private lemma seven_Tau_mat : (↑Tau_7 : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![4, 6; 6, 6] := rfl

private lemma seven_T0_mat : (↑T0_7 : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![0, -1; 1, 0] := rfl

private noncomputable def standard_seven : StandardData (ZMod 7) := by
  have ht0J : (Matrix.ProjGenLinGroup.mk T0_7 : PGL2 (ZMod 7)) ∈ pslRange (ZMod 7) := by
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
    have hdet : ((T0_7.det : (ZMod 7)ˣ) : ZMod 7) = 1 := by
      change (T0_7 : Matrix (Fin 2) (Fin 2) (ZMod 7)).det = 1
      decide
    rw [hdet]
    exact ⟨1, by ring⟩
  have hb0J : (Matrix.ProjGenLinGroup.mk B0_7 : PGL2 (ZMod 7)) ∉ pslRange (ZMod 7) := by
    intro h
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare] at h
    have hdet : ((B0_7.det : (ZMod 7)ˣ) : ZMod 7) = -1 := by
      change (B0_7 : Matrix (Fin 2) (Fin 2) (ZMod 7)).det = -1
      decide
    rw [hdet] at h
    exact (by decide : ¬ IsSquare (-1 : ZMod 7)) h
  have ht0sq : (Matrix.ProjGenLinGroup.mk T0_7 : PGL2 (ZMod 7)) *
      Matrix.ProjGenLinGroup.mk T0_7 = 1 := by
    have h := mk_pow_eq_one_of_val_pow_eq_smul 2 seven_T0_sq (by decide)
    simpa [pow_two] using h
  have ht01 : (Matrix.ProjGenLinGroup.mk T0_7 : PGL2 (ZMod 7)) ≠ 1 := by
    simpa using (mk_pow_ne_one_of_val_pow_eq_matrix (X := T0_7) 1
      (by simpa using seven_T0_mat) (Or.inl (by decide)))
  have hb0sq : (Matrix.ProjGenLinGroup.mk B0_7 : PGL2 (ZMod 7)) *
      Matrix.ProjGenLinGroup.mk B0_7 = 1 := by
    have h := mk_pow_eq_one_of_val_pow_eq_smul 2 seven_B0_sq (by decide)
    simpa [pow_two] using h
  have hcomm : (Matrix.ProjGenLinGroup.mk T0_7 : PGL2 (ZMod 7)) *
      Matrix.ProjGenLinGroup.mk B0_7 = Matrix.ProjGenLinGroup.mk B0_7 *
      Matrix.ProjGenLinGroup.mk T0_7 := by
    rw [← map_mul, ← map_mul]
    apply mk_eq_mk_of_mul_scalar (c := -1) (by decide)
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp [T0_7, B0_7, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] <;> decide
  have hgen : ParrottGen (pslRange (ZMod 7))
      (Matrix.ProjGenLinGroup.mk T0_7) (Matrix.ProjGenLinGroup.mk B0_7) := by
    let t0 : PGL2 (ZMod 7) := Matrix.ProjGenLinGroup.mk T0_7
    let b0 : PGL2 (ZMod 7) := Matrix.ProjGenLinGroup.mk B0_7
    let tau : PGL2 (ZMod 7) := Matrix.ProjGenLinGroup.mk Tau_7
    let c : PGL2 (ZMod 7) := b0 * tau * b0
    let Mcl : Subgroup (PGL2 (ZMod 7)) := closure {t0, tau, c}
    have hK : IsOddPrimePower (Nat.card (ZMod 7)) := by
      rw [Nat.card_zmod]
      exact ⟨7, 1, by norm_num, by norm_num, le_rfl, by rw [pow_one]⟩
    have hcard3 : 3 < Nat.card (ZMod 7) := by rw [Nat.card_zmod]; norm_num
    have hJnorm : (pslRange (ZMod 7)).Normal := pslRange_normal hK hcard3
    have ht0J : t0 ∈ pslRange (ZMod 7) := by
      rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
      have hdet : ((T0_7.det : (ZMod 7)ˣ) : ZMod 7) = 1 := by
        change (T0_7 : Matrix (Fin 2) (Fin 2) (ZMod 7)).det = 1
        decide
      rw [hdet]
      exact ⟨1, by ring⟩
    have htauJ : tau ∈ pslRange (ZMod 7) := by
      rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
      have hdet : ((Tau_7.det : (ZMod 7)ˣ) : ZMod 7) = 2 := by
        change (Tau_7 : Matrix (Fin 2) (Fin 2) (ZMod 7)).det = 2
        decide
      rw [hdet]
      exact ⟨3, by decide⟩
    have hb0sq : b0 * b0 = 1 := by
      simpa [b0, pow_two] using mk_pow_eq_one_of_val_pow_eq_smul 2 seven_B0_sq (by decide)
    have hcJ : c ∈ pslRange (ZMod 7) := by
      have h := hJnorm.conj_mem tau htauJ b0
      rwa [inv_eq_of_mul_eq_one_right hb0sq] at h
    have ht0_mem : t0 ∈ ({t0, tau, c} : Set (PGL2 (ZMod 7))) := by simp
    have htau_mem : tau ∈ ({t0, tau, c} : Set (PGL2 (ZMod 7))) := by simp
    have hc_mem : c ∈ ({t0, tau, c} : Set (PGL2 (ZMod 7))) := by simp
    have ht0M : t0 ∈ Mcl := by
      change t0 ∈ Subgroup.closure ({t0, tau, c} : Set (PGL2 (ZMod 7)))
      exact Subgroup.subset_closure ht0_mem
    have htauM : tau ∈ Mcl := by
      change tau ∈ Subgroup.closure ({t0, tau, c} : Set (PGL2 (ZMod 7)))
      exact Subgroup.subset_closure htau_mem
    have hcM : c ∈ Mcl := by
      change c ∈ Subgroup.closure ({t0, tau, c} : Set (PGL2 (ZMod 7)))
      exact Subgroup.subset_closure hc_mem
    have hMJ : Mcl ≤ pslRange (ZMod 7) := by
      refine (Subgroup.closure_le (pslRange (ZMod 7))).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ht0J
      · exact htauJ
      · exact hcJ
    have htau3 : tau ^ 3 = 1 :=
      mk_pow_eq_one_of_val_pow_eq_smul 3 seven_Tau_cube (by decide)
    have htau1 : tau ≠ 1 := by
      simpa [tau] using (mk_pow_ne_one_of_val_pow_eq_matrix (X := Tau_7) 1
        (by simpa using seven_Tau_mat) (Or.inl (by decide)))
    have htauOrd : orderOf tau = 3 := orderOf_eq_prime htau3 htau1
    have hM4 : (Matrix.ProjGenLinGroup.mk M_7 : PGL2 (ZMod 7)) ^ 4 = 1 :=
      mk_pow_eq_one_of_val_pow_eq_smul 4 seven_M_four (by decide)
    have hM2 : (Matrix.ProjGenLinGroup.mk M_7 : PGL2 (ZMod 7)) ^ 2 ≠ 1 :=
      mk_pow_ne_one_of_val_pow_eq_matrix 2 seven_M_sq (Or.inl (by decide))
    have hMOrd : orderOf (Matrix.ProjGenLinGroup.mk M_7 : PGL2 (ZMod 7)) = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1)
        (x := (Matrix.ProjGenLinGroup.mk M_7 : PGL2 (ZMod 7)))
        (by simpa using hM2) (by simpa using hM4)
      simpa using h
    have hN7 : (Matrix.ProjGenLinGroup.mk N_7 : PGL2 (ZMod 7)) ^ 7 = 1 :=
      mk_pow_eq_one_of_val_pow_eq_smul 7 seven_N_seven (by decide)
    have hN1 : (Matrix.ProjGenLinGroup.mk N_7 : PGL2 (ZMod 7)) ≠ 1 := by
      simpa using (mk_pow_ne_one_of_val_pow_eq_matrix 1 (by simpa using seven_N_mat)
        (Or.inr (by decide)))
    have hNOrd : orderOf (Matrix.ProjGenLinGroup.mk N_7 : PGL2 (ZMod 7)) = 7 :=
      orderOf_eq_prime hN7 hN1
    have hMc : tau * c = Matrix.ProjGenLinGroup.mk M_7 := rfl
    have hNc : t0 * tau * c = Matrix.ProjGenLinGroup.mk N_7 := rfl
    have h3dvd : 3 ∣ Nat.card Mcl := by
      have h := Subgroup.orderOf_dvd_natCard Mcl htauM
      rwa [htauOrd] at h
    have h4dvd : 4 ∣ Nat.card Mcl := by
      have hmem : tau * c ∈ Mcl := Subgroup.mul_mem Mcl htauM hcM
      have h := Subgroup.orderOf_dvd_natCard Mcl hmem
      rwa [hMc, hMOrd] at h
    have h7dvd : 7 ∣ Nat.card Mcl := by
      have hmem : t0 * tau * c ∈ Mcl :=
        Subgroup.mul_mem Mcl (Subgroup.mul_mem Mcl ht0M htauM) hcM
      have h := Subgroup.orderOf_dvd_natCard Mcl hmem
      rwa [hNc, hNOrd] at h
    have h12 : 12 ∣ Nat.card Mcl :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 4) h3dvd h4dvd
    have h84 : 84 ∣ Nat.card Mcl :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 7) h12 h7dvd
    have hJcard : Nat.card (pslRange (ZMod 7)) = 168 := by
      have h := psl2_card_formula (ZMod 7) hK
      rw [Nat.card_zmod] at h
      norm_num at h
      change Nat.card ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := ZMod 7)).range = 168
      have hcard : Nat.card ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := ZMod 7)).range = Nat.card (PSL2 (ZMod 7)) :=
        (Nat.card_congr (Equiv.ofInjective _
          (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := ZMod 7)))).symm
      rw [hcard]
      simpa using h
    have hsimple : IsSimpleGroup ↥(pslRange (ZMod 7)) := by
      haveI : IsSimpleGroup (PSL2 (ZMod 7)) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
      exact (MonoidHom.ofInjective
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
          (n := Fin 2) (R := ZMod 7))).symm.isSimpleGroup
    haveI : Finite (PGL2 (ZMod 7)) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    have hEq : Mcl = pslRange (ZMod 7) :=
      eq_of_dvd_card_of_simple hMJ hsimple (D := 84) (N := 168) rfl (by norm_num) h84 hJcard
    refine ⟨tau, htauJ, ?_, ?_, ?_⟩
    · rw [htauOrd]
      decide
    · rw [← map_inv, ← map_mul, ← map_mul]
      apply mk_eq_mk_of_mul_scalar (c := 4) (by decide)
      ext i j
      fin_cases i <;> fin_cases j <;>
      simp [T0_7, Tau_7, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] <;> decide
    · rw [← hEq]
      refine (Subgroup.closure_le
        (Subgroup.closure ({t0, b0, tau} : Set (PGL2 (ZMod 7))))).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.subset_closure (k := ({t0, b0, tau} : Set (PGL2 (ZMod 7))))
          (by show t0 ∈ ({t0, b0, tau} : Set (PGL2 (ZMod 7))); simp)
      · exact Subgroup.subset_closure (k := ({t0, b0, tau} : Set (PGL2 (ZMod 7))))
          (by show tau ∈ ({t0, b0, tau} : Set (PGL2 (ZMod 7))); simp)
      · have ht0' : t0 ∈ Subgroup.closure ({t0, b0, tau} : Set (PGL2 (ZMod 7))) :=
          Subgroup.subset_closure (by simp)
        have hb0' : b0 ∈ Subgroup.closure ({t0, b0, tau} : Set (PGL2 (ZMod 7))) :=
          Subgroup.subset_closure (by simp)
        have htau' : tau ∈ Subgroup.closure ({t0, b0, tau} : Set (PGL2 (ZMod 7))) :=
          Subgroup.subset_closure (by simp)
        have : c = b0 * tau * b0 := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb0' htau') hb0'
  exact ⟨Matrix.ProjGenLinGroup.mk T0_7, Matrix.ProjGenLinGroup.mk B0_7,
    ht0J, hb0J, ht0sq, ht01, hb0sq, hcomm, hgen⟩

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private def T0_11 : GL (Fin 2) (ZMod 11) where
  val := !![0, -1; 1, 0]
  inv := !![0, 1; -1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> decide
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> decide

private def B0_11 : GL (Fin 2) (ZMod 11) where
  val := !![-1, 0; 0, 1]
  inv := !![-1, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> decide
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> decide

private def Tau_11 : GL (Fin 2) (ZMod 11) where
  val := !![9, 2; 2, 7]
  inv := !![10, 5; 5, 5]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> decide
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> decide

private def C_11 : GL (Fin 2) (ZMod 11) := B0_11 * Tau_11 * B0_11

private def Ci_11 : GL (Fin 2) (ZMod 11) where
  val := !![10, 6; 6, 5]
  inv := !![9, 9; 9, 7]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> decide
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> decide

private def X_11 : GL (Fin 2) (ZMod 11) := Tau_11 * Ci_11 * Tau_11 * Ci_11
private def N_11 : GL (Fin 2) (ZMod 11) := T0_11 * Tau_11 * C_11

private lemma eleven_T0_sq : (↑(T0_11 ^ 2) : Matrix (Fin 2) (Fin 2) (ZMod 11)) =
    (-1 : ZMod 11) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, T0_11, Matrix.one_apply] <;> decide

private lemma eleven_B0_sq : (↑(B0_11 ^ 2) : Matrix (Fin 2) (Fin 2) (ZMod 11)) =
    (1 : ZMod 11) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, B0_11, Matrix.one_apply] <;> decide

private lemma eleven_Tau_five : (↑(Tau_11 ^ 5) : Matrix (Fin 2) (Fin 2) (ZMod 11)) =
    (1 : ZMod 11) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [show (5 : ℕ) = 4 + 1 by norm_num, pow_succ, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two, Tau_11, Matrix.one_apply] <;> decide

private lemma eleven_X_cube : (↑(X_11 ^ 3) : Matrix (Fin 2) (Fin 2) (ZMod 11)) =
    (10 : ZMod 11) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two, X_11, Ci_11, B0_11, Tau_11, Matrix.one_apply] <;> decide

private lemma eleven_N_eleven : (↑(N_11 ^ 11) : Matrix (Fin 2) (Fin 2) (ZMod 11)) =
    (7 : ZMod 11) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) := by
  rw [Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [show (11 : ℕ) = 10 + 1 by norm_num, pow_succ, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two, N_11, C_11, B0_11, T0_11, Tau_11, Matrix.one_apply] <;> decide

private lemma eleven_X_mat : (↑X_11 : Matrix (Fin 2) (Fin 2) (ZMod 11)) = !![6, 10; 9, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [X_11, Ci_11, B0_11, Tau_11] <;> decide

private lemma eleven_N_mat : (↑N_11 : Matrix (Fin 2) (Fin 2) (ZMod 11)) = !![7, 10; 0, 7] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [N_11, C_11, B0_11, T0_11, Tau_11] <;> decide

private lemma eleven_Tau_mat : (↑Tau_11 : Matrix (Fin 2) (Fin 2) (ZMod 11)) = !![9, 2; 2, 7] := rfl

private lemma eleven_T0_mat : (↑T0_11 : Matrix (Fin 2) (Fin 2) (ZMod 11)) = !![0, -1; 1, 0] := rfl

private lemma eleven_Ci_mul_C : Ci_11 * C_11 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [Ci_11, C_11, B0_11, Tau_11, Matrix.mul_apply, Fin.sum_univ_two] <;> decide

private noncomputable def standard_eleven : StandardData (ZMod 11) := by
  have ht0J : (Matrix.ProjGenLinGroup.mk T0_11 : PGL2 (ZMod 11)) ∈ pslRange (ZMod 11) := by
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
    have hdet : ((T0_11.det : (ZMod 11)ˣ) : ZMod 11) = 1 := by
      change (T0_11 : Matrix (Fin 2) (Fin 2) (ZMod 11)).det = 1
      decide
    rw [hdet]
    exact ⟨1, by ring⟩
  have hb0J : (Matrix.ProjGenLinGroup.mk B0_11 : PGL2 (ZMod 11)) ∉ pslRange (ZMod 11) := by
    intro h
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare] at h
    have hdet : ((B0_11.det : (ZMod 11)ˣ) : ZMod 11) = -1 := by
      change (B0_11 : Matrix (Fin 2) (Fin 2) (ZMod 11)).det = -1
      decide
    rw [hdet] at h
    exact (by decide : ¬ IsSquare (-1 : ZMod 11)) h
  have ht0sq : (Matrix.ProjGenLinGroup.mk T0_11 : PGL2 (ZMod 11)) *
      Matrix.ProjGenLinGroup.mk T0_11 = 1 := by
    have h := mk_pow_eq_one_of_val_pow_eq_smul 2 eleven_T0_sq (by decide)
    simpa [pow_two] using h
  have ht01 : (Matrix.ProjGenLinGroup.mk T0_11 : PGL2 (ZMod 11)) ≠ 1 := by
    simpa using (mk_pow_ne_one_of_val_pow_eq_matrix (X := T0_11) 1
      (by simpa using eleven_T0_mat) (Or.inl (by decide)))
  have hb0sq : (Matrix.ProjGenLinGroup.mk B0_11 : PGL2 (ZMod 11)) *
      Matrix.ProjGenLinGroup.mk B0_11 = 1 := by
    have h := mk_pow_eq_one_of_val_pow_eq_smul 2 eleven_B0_sq (by decide)
    simpa [pow_two] using h
  have hcomm : (Matrix.ProjGenLinGroup.mk T0_11 : PGL2 (ZMod 11)) *
      Matrix.ProjGenLinGroup.mk B0_11 = Matrix.ProjGenLinGroup.mk B0_11 *
      Matrix.ProjGenLinGroup.mk T0_11 := by
    rw [← map_mul, ← map_mul]
    apply mk_eq_mk_of_mul_scalar (c := -1) (by decide)
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp [T0_11, B0_11, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] <;> decide
  have hgen : ParrottGen (pslRange (ZMod 11))
      (Matrix.ProjGenLinGroup.mk T0_11) (Matrix.ProjGenLinGroup.mk B0_11) := by
    let t0 : PGL2 (ZMod 11) := Matrix.ProjGenLinGroup.mk T0_11
    let b0 : PGL2 (ZMod 11) := Matrix.ProjGenLinGroup.mk B0_11
    let tau : PGL2 (ZMod 11) := Matrix.ProjGenLinGroup.mk Tau_11
    let c : PGL2 (ZMod 11) := b0 * tau * b0
    let Mcl : Subgroup (PGL2 (ZMod 11)) := closure {t0, tau, c}
    have hK : IsOddPrimePower (Nat.card (ZMod 11)) := by
      rw [Nat.card_zmod]
      exact ⟨11, 1, by norm_num, by norm_num, le_rfl, by rw [pow_one]⟩
    have hcard3 : 3 < Nat.card (ZMod 11) := by rw [Nat.card_zmod]; norm_num
    have hJnorm : (pslRange (ZMod 11)).Normal := pslRange_normal hK hcard3
    have ht0J : t0 ∈ pslRange (ZMod 11) := by
      rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
      have hdet : ((T0_11.det : (ZMod 11)ˣ) : ZMod 11) = 1 := by
        change (T0_11 : Matrix (Fin 2) (Fin 2) (ZMod 11)).det = 1
        decide
      rw [hdet]
      exact ⟨1, by ring⟩
    have htauJ : tau ∈ pslRange (ZMod 11) := by
      rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
      have hdet : ((Tau_11.det : (ZMod 11)ˣ) : ZMod 11) = 4 := by
        change (Tau_11 : Matrix (Fin 2) (Fin 2) (ZMod 11)).det = 4
        decide
      rw [hdet]
      exact ⟨2, by decide⟩
    have hb0sq : b0 * b0 = 1 := by
      simpa [b0, pow_two] using mk_pow_eq_one_of_val_pow_eq_smul 2 eleven_B0_sq (by decide)
    have hcJ : c ∈ pslRange (ZMod 11) := by
      have h := hJnorm.conj_mem tau htauJ b0
      rwa [inv_eq_of_mul_eq_one_right hb0sq] at h
    have ht0_mem : t0 ∈ ({t0, tau, c} : Set (PGL2 (ZMod 11))) := by simp
    have htau_mem : tau ∈ ({t0, tau, c} : Set (PGL2 (ZMod 11))) := by simp
    have hc_mem : c ∈ ({t0, tau, c} : Set (PGL2 (ZMod 11))) := by simp
    have ht0M : t0 ∈ Mcl := by
      change t0 ∈ Subgroup.closure ({t0, tau, c} : Set (PGL2 (ZMod 11)))
      exact Subgroup.subset_closure ht0_mem
    have htauM : tau ∈ Mcl := by
      change tau ∈ Subgroup.closure ({t0, tau, c} : Set (PGL2 (ZMod 11)))
      exact Subgroup.subset_closure htau_mem
    have hcM : c ∈ Mcl := by
      change c ∈ Subgroup.closure ({t0, tau, c} : Set (PGL2 (ZMod 11)))
      exact Subgroup.subset_closure hc_mem
    have hcInvM : c⁻¹ ∈ Mcl := Subgroup.inv_mem _ hcM
    have hMJ : Mcl ≤ pslRange (ZMod 11) := by
      refine (Subgroup.closure_le (pslRange (ZMod 11))).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ht0J
      · exact htauJ
      · exact hcJ
    have htau5 : tau ^ 5 = 1 :=
      mk_pow_eq_one_of_val_pow_eq_smul 5 eleven_Tau_five (by decide)
    have htau1 : tau ≠ 1 := by
      simpa [tau] using (mk_pow_ne_one_of_val_pow_eq_matrix (X := Tau_11) 1
        (by simpa using eleven_Tau_mat) (Or.inl (by decide)))
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have htauOrd : orderOf tau = 5 := orderOf_eq_prime htau5 htau1
    have ht0sq : t0 * t0 = 1 := by
      have h := mk_pow_eq_one_of_val_pow_eq_smul 2 eleven_T0_sq (by decide)
      simpa [t0, pow_two] using h
    have ht01 : t0 ≠ 1 := by
      simpa [t0] using (mk_pow_ne_one_of_val_pow_eq_matrix (X := T0_11) 1
        (by simpa using eleven_T0_mat) (Or.inl (by decide)))
    have ht0Ord : orderOf t0 = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht0sq) ht01
    have hCiP : (Matrix.ProjGenLinGroup.mk Ci_11 : PGL2 (ZMod 11)) = c⁻¹ := by
      have hCeq : (Matrix.ProjGenLinGroup.mk C_11 : PGL2 (ZMod 11)) = c := rfl
      rw [← hCeq]
      exact eq_inv_of_mul_eq_one_left (by
        rw [← map_mul, eleven_Ci_mul_C, map_one])
    have hXc : tau * c⁻¹ * tau * c⁻¹ = (Matrix.ProjGenLinGroup.mk X_11 : PGL2 (ZMod 11)) := by
      simp only [tau, c, b0, X_11, map_mul]
      rw [hCiP]
    have hX3 : (Matrix.ProjGenLinGroup.mk X_11 : PGL2 (ZMod 11)) ^ 3 = 1 :=
      mk_pow_eq_one_of_val_pow_eq_smul 3 eleven_X_cube (by decide)
    have hX1 : (Matrix.ProjGenLinGroup.mk X_11 : PGL2 (ZMod 11)) ≠ 1 := by
      simpa using (mk_pow_ne_one_of_val_pow_eq_matrix (X := X_11) 1 (by simpa using eleven_X_mat)
        (Or.inr (by decide)))
    have hXOrd : orderOf (Matrix.ProjGenLinGroup.mk X_11 : PGL2 (ZMod 11)) = 3 :=
      orderOf_eq_prime hX3 hX1
    have hN11 : (Matrix.ProjGenLinGroup.mk N_11 : PGL2 (ZMod 11)) ^ 11 = 1 :=
      mk_pow_eq_one_of_val_pow_eq_smul 11 eleven_N_eleven (by decide)
    have hN1 : (Matrix.ProjGenLinGroup.mk N_11 : PGL2 (ZMod 11)) ≠ 1 := by
      simpa using (mk_pow_ne_one_of_val_pow_eq_matrix (X := N_11) 1 (by simpa using eleven_N_mat)
        (Or.inl (by decide)))
    have hNOrd : orderOf (Matrix.ProjGenLinGroup.mk N_11 : PGL2 (ZMod 11)) = 11 :=
      orderOf_eq_prime hN11 hN1
    have hNc : t0 * tau * c = Matrix.ProjGenLinGroup.mk N_11 := rfl
    have h2dvd : 2 ∣ Nat.card Mcl := by
      have h := Subgroup.orderOf_dvd_natCard Mcl ht0M
      rwa [ht0Ord] at h
    have h3dvd : 3 ∣ Nat.card Mcl := by
      have hXmem : (Matrix.ProjGenLinGroup.mk X_11 : PGL2 (ZMod 11)) ∈ Mcl := by
        rw [← hXc]
        exact Subgroup.mul_mem Mcl
          (Subgroup.mul_mem Mcl (Subgroup.mul_mem Mcl htauM hcInvM) htauM) hcInvM
      have h := Subgroup.orderOf_dvd_natCard Mcl hXmem
      rwa [hXOrd] at h
    have h5dvd : 5 ∣ Nat.card Mcl := by
      have h := Subgroup.orderOf_dvd_natCard Mcl htauM
      rwa [htauOrd] at h
    have h11dvd : 11 ∣ Nat.card Mcl := by
      have hmem : t0 * tau * c ∈ Mcl :=
        Subgroup.mul_mem Mcl (Subgroup.mul_mem Mcl ht0M htauM) hcM
      have h := Subgroup.orderOf_dvd_natCard Mcl hmem
      rwa [hNc, hNOrd] at h
    have h6 : 6 ∣ Nat.card Mcl :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2dvd h3dvd
    have h30 : 30 ∣ Nat.card Mcl :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 6 5) h6 h5dvd
    have h330 : 330 ∣ Nat.card Mcl :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 30 11) h30 h11dvd
    have hJcard : Nat.card (pslRange (ZMod 11)) = 660 := by
      have h := psl2_card_formula (ZMod 11) hK
      rw [Nat.card_zmod] at h
      norm_num at h
      change Nat.card ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := ZMod 11)).range = 660
      have hcard : Nat.card ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := ZMod 11)).range = Nat.card (PSL2 (ZMod 11)) :=
        (Nat.card_congr (Equiv.ofInjective _
          (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := ZMod 11)))).symm
      rw [hcard]
      simpa using h
    have hsimple : IsSimpleGroup ↥(pslRange (ZMod 11)) := by
      haveI : IsSimpleGroup (PSL2 (ZMod 11)) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
      exact (MonoidHom.ofInjective
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
          (n := Fin 2) (R := ZMod 11))).symm.isSimpleGroup
    haveI : Finite (PGL2 (ZMod 11)) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    have hEq : Mcl = pslRange (ZMod 11) :=
      eq_of_dvd_card_of_simple hMJ hsimple (D := 330) (N := 660) rfl (by norm_num) h330 hJcard
    refine ⟨tau, htauJ, ?_, ?_, ?_⟩
    · rw [htauOrd]
      decide
    · rw [← map_inv, ← map_mul, ← map_mul]
      apply mk_eq_mk_of_mul_scalar (c := 3) (by decide)
      ext i j
      fin_cases i <;> fin_cases j <;>
      simp [T0_11, Tau_11, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] <;> decide
    · rw [← hEq]
      refine (Subgroup.closure_le
        (Subgroup.closure ({t0, b0, tau} : Set (PGL2 (ZMod 11))))).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.subset_closure (k := ({t0, b0, tau} : Set (PGL2 (ZMod 11))))
          (by show t0 ∈ ({t0, b0, tau} : Set (PGL2 (ZMod 11))); simp)
      · exact Subgroup.subset_closure (k := ({t0, b0, tau} : Set (PGL2 (ZMod 11))))
          (by show tau ∈ ({t0, b0, tau} : Set (PGL2 (ZMod 11))); simp)
      · have hb0' : b0 ∈ Subgroup.closure ({t0, b0, tau} : Set (PGL2 (ZMod 11))) :=
          Subgroup.subset_closure (by show b0 ∈ ({t0, b0, tau} : Set (PGL2 (ZMod 11))); simp)
        have htau' : tau ∈ Subgroup.closure ({t0, b0, tau} : Set (PGL2 (ZMod 11))) :=
          Subgroup.subset_closure (by show tau ∈ ({t0, b0, tau} : Set (PGL2 (ZMod 11))); simp)
        have : c = b0 * tau * b0 := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb0' htau') hb0'
  exact ⟨Matrix.ProjGenLinGroup.mk T0_11, Matrix.ProjGenLinGroup.mk B0_11,
    ht0J, hb0J, ht0sq, ht01, hb0sq, hcomm, hgen⟩

theorem parrottGen_pgl2_small {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 7 ∨ Nat.card K = 11) {t β : PGL2 K} (htJ : t ∈ pslRange K)
    (hβJ : β ∉ pslRange K) (ht : t * t = 1) (ht1 : t ≠ 1) (hβ : β * β = 1)
    (hcomm : t * β = β * t) : ParrottGen (pslRange K) t β := by
  have hoddK : IsOddPrimePower (Nat.card K) := by
    rcases hK with h | h
    · rw [h]
      exact ⟨7, 1, by norm_num, by norm_num, le_rfl, by rw [pow_one]⟩
    · rw [h]
      exact ⟨11, 1, by norm_num, by norm_num, le_rfl, by rw [pow_one]⟩
  have hcard : 3 < Nat.card K := by
    rcases hK with h | h <;> rw [h] <;> norm_num
  letI : Fintype K := Fintype.ofFinite K
  rcases hK with hK7 | hK11
  · have hF : Fintype.card K = 7 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK7
    let e : ZMod 7 ≃+* K := ZMod.ringEquivOfPrime K (by norm_num) hF
    let d : StandardData K := StandardData.map standard_seven e
    exact parrottGen_reduce hoddK hcard d.ht0J d.hb0J d.ht0 d.ht01 d.hb0 d.hcomm d.hgen
      htJ hβJ ht ht1 hβ hcomm
  · have hF : Fintype.card K = 11 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK11
    let e : ZMod 11 ≃+* K := ZMod.ringEquivOfPrime K (by norm_num) hF
    let d : StandardData K := StandardData.map standard_eleven e
    exact parrottGen_reduce hoddK hcard d.ht0J d.hb0J d.ht0 d.ht01 d.hb0 d.hcomm d.hgen
      htJ hβJ ht ht1 hβ hcomm

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end

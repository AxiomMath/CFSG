module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddTools
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddSL3
import CFSG.RankThree.Classical.SteinbergCFProjectiveTwoAutomorphisms
import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCore
import CFSG.Walter.W67.Section5.P56AbAut

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open CFSG Subgroup
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] noncomputable def restrictAut {G : Type*} [Group G] (α : MulAut G) (H : Subgroup G)
    (h : H.map α.toMonoidHom = H) : MulAut H :=
  (α.subgroupMap H).trans (MulEquiv.subgroupCongr h)

theorem restrictAut_pow_apply {G : Type*} [Group G] (α : MulAut G) (H : Subgroup G)
    (h : H.map α.toMonoidHom = H) (n : ℕ) (g : H) :
    (((restrictAut α H h) ^ n) g : G) = (α ^ n) g := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
    rfl

theorem fix_of_pow_fix {Q : Type*} [Group Q] {p : ℕ} (hp : p.Prime) {α : MulAut Q}
    (hα : α ^ p = 1) {m : ℕ} (hm : ¬ p ∣ m) {t : Q} (ht : (α ^ m) t = t) : α t = t := by
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm))) hp.one_lt
  have hpow : ∀ n : ℕ, ((α ^ m) ^ n) t = t := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, ht, ih]
  have hαeq : α ^ (m * a) = α := by
    rw [← Nat.div_add_mod (m * a) p, pow_add, pow_mul, hα, one_pow, one_mul, ha, pow_one]
  rw [← hαeq, pow_mul]
  exact hpow a

theorem fix_of_pow_apply_eq {Q : Type*} [Group Q] {p : ℕ} (hp : p.Prime) {α : MulAut Q}
    (hα : α ^ p = 1) {i j : ℕ} (hij : i < j) (hjp : j < p) {t : Q}
    (h : (α ^ i) t = (α ^ j) t) : α t = t := by
  have h1 : (α ^ (j - i)) ((α ^ i) t) = (α ^ i) t := by
    rw [← MulAut.mul_apply, pow_sub_mul_pow α hij.le]
    exact h.symm
  have h2 : α ((α ^ i) t) = (α ^ i) t := by
    refine fix_of_pow_fix hp hα (m := j - i) ?_ h1
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have h3 : (α ^ i) (α t) = (α ^ i) t := by
    rw [← MulAut.mul_apply, ← pow_succ, pow_succ', MulAut.mul_apply, h2]
  exact (α ^ i).injective h3

theorem fix_of_card_lt {Q : Type*} [Group Q] {p : ℕ} (hp : p.Prime) {α : MulAut Q}
    (hα : α ^ p = 1) (s : Set Q) [Finite s] (hs : ∀ t ∈ s, α t ∈ s) (hcard : Nat.card s < p) :
    ∀ t ∈ s, α t = t := by
  intro t ht
  have hmem : ∀ n : ℕ, (α ^ n) t ∈ s := by
    intro n
    induction n with
    | zero => exact ht
    | succ n ih => rw [pow_succ', MulAut.mul_apply]; exact hs _ ih
  haveI := Fintype.ofFinite s
  let f : Fin p → s := fun i => ⟨(α ^ (i : ℕ)) t, hmem i⟩
  obtain ⟨i, j, hne, hij⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact hcard)
  have hij' : (α ^ (i : ℕ)) t = (α ^ (j : ℕ)) t := congrArg Subtype.val hij
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact fix_of_pow_apply_eq hp hα hlt j.2 hij'
  · exact fix_of_pow_apply_eq hp hα hlt i.2 hij'.symm

theorem noTwoAut_pgl2 (k : Type) [Field k] [Finite k] (hk : ringChar k ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : NoTwoAut p PGL(2, k) := by
  haveI : Finite PGL(2, k) := Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  intro Q hQ α hα
  have hP : IsPGroup p (Subgroup.zpowers α) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hα, one_zpow]
    rfl
  exact (CFSG.RankThree.Classical.odd_projective_linear_two_subgroup_automorphisms_no_large_primes
    k hk Q hQ).2 p hp (by omega) (Subgroup.zpowers α) hP (Subgroup.zpowers α).subtype
    ⟨α, Subgroup.mem_zpowers α⟩

theorem mem_center_of_mem_center_of_noncomm {K : Type*} [Field K]
    {T : Subgroup (GL (Fin 2) K)} {a b : T} (hab : a * b ≠ b * a) {z : T}
    (hz : z ∈ Subgroup.center T) : (z : GL (Fin 2) K) ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  by_contra hns
  apply hab
  have hza : ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (a : GL (Fin 2) K) =
      ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (z : GL (Fin 2) K) := by
    have := congrArg (fun g : T => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      (Subgroup.mem_center_iff.1 hz a)
    simpa using this.symm
  have hzb : ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (b : GL (Fin 2) K) =
      ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (z : GL (Fin 2) K) := by
    have := congrArg (fun g : T => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      (Subgroup.mem_center_iff.1 hz b)
    simpa using this.symm
  have hnot : ¬ ∃ c : K, ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
    rintro ⟨c, hc⟩
    exact hns ⟨c, by rw [hc, Matrix.smul_one_eq_diagonal]; rfl⟩
  have hcomm := CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hnot hza hzb
  apply Subtype.ext
  apply Units.ext
  simpa using hcomm

theorem noTwoAut_gl2 (K : Type) [Field K] [Finite K] (hK : ringChar K ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : NoTwoAut p (GL (Fin 2) K) := by
  intro T hT α hα
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hab : ∀ a b : T, a * b = b * a
  ·
    refine CFSG.Walter.W67.P56Ab.eq_one_of_forall_pow_eq_one hT hab α ?_ ?_
    · exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hα)
        (Nat.coprime_two_right.2 hodd)
    · let Ω : Subgroup T :=
        { carrier := {t | t ^ 2 = 1}
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq] at *
            rw [Commute.mul_pow (hab a b) 2, ha, hb, one_mul]
          one_mem' := by simp
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at *
            rw [inv_pow, ha, inv_one] }
      have hΩ : Nat.card Ω ≤ 4 := by
        rw [← Subgroup.card_map_of_injective (f := T.subtype) T.subtype_injective]
        refine CFSG.RankThree.PartTwo.Sec4.L34Odd.card_le_four_of_exp_two_gl2 h2 _ ?_
        rintro _ ⟨t, ht, rfl⟩
        have ht' : t ^ 2 = 1 := ht
        simpa using congrArg Subtype.val ht'
      intro t ht
      refine fix_of_card_lt hp hα (Ω : Set T) ?_ ?_ t ht
      · intro y hy
        have hy' : y ^ 2 = 1 := hy
        show α y ^ 2 = 1
        rw [← map_pow, hy', map_one]
      · exact lt_of_le_of_lt hΩ (by omega)
  ·
    push Not at hab
    obtain ⟨a, b, hab⟩ := hab
    have hZ : ∀ z ∈ Subgroup.center T,
        (z : GL (Fin 2) K) ∈ Subgroup.center (GL (Fin 2) K) := fun z hz =>
      mem_center_of_mem_center_of_noncomm hab hz
    set N : Subgroup T := Subgroup.center T with hN
    have hN2 : IsPGroup 2 N := hT.to_subgroup N
    have hNcyc : IsCyclic N := by
      let g : N →* Subgroup.center (GL (Fin 2) K) :=
        (T.subtype.comp N.subtype).codRestrict _ (fun z => hZ z z.2)
      have hg : Function.Injective g := by
        intro z w hzw
        have h1 := congrArg Subtype.val hzw
        exact Subtype.ext (Subtype.ext h1)
      have hcen : IsCyclic (Subgroup.center (GL (Fin 2) K)) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact isCyclic_of_surjective _
          (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).rangeRestrict_surjective
      exact isCyclic_of_surjective _ (MonoidHom.ofInjective hg).symm.surjective
    have hαN : N.map α.toMonoidHom = N :=
      (Subgroup.characteristic_iff_map_eq.1 inferInstance) α
    have hαNp : (restrictAut α N hαN) ^ p = 1 := by
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [restrictAut_pow_apply, hα]
      rfl
    have hαN1 := CFSG.LocalAnalysis.GorensteinLyons.mulAut_eq_one_of_odd hN2 hodd hαNp
    have hfix : ∀ c ∈ N, α c = c := by
      intro c hc
      have := restrictAut_pow_apply α N hαN 1 ⟨c, hc⟩
      rw [pow_one, pow_one, hαN1] at this
      exact this.symm
    let π : T →* PGL(2, K) := Matrix.ProjGenLinGroup.mk.comp T.subtype
    have hker : π.ker = N := by
      ext t
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Matrix.ProjGenLinGroup.mk_eq_one]
      constructor
      · intro ht
        exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 ht y)
      · exact hZ t
    have hQ : IsPGroup 2 π.range := hT.of_surjective π.rangeRestrict π.rangeRestrict_surjective
    have hfree : TwoAutFree p (T ⧸ N) :=
      TwoAutFree.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange π)) (noTwoAut_pgl2 K hK hp hp5 π.range hQ)
    let γ : MulAut (T ⧸ N) := QuotientGroup.congr N N α hαN
    have hγ : ∀ (n : ℕ) (t : T), (γ ^ n) (t : T ⧸ N) = (((α ^ n) t : T) : T ⧸ N) := by
      intro n
      induction n with
      | zero => intro t; rfl
      | succ n ih =>
        intro t
        rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ← ih]
        rfl
    have hγp : γ ^ p = 1 := by
      apply MulEquiv.ext
      intro q
      induction q using QuotientGroup.induction_on with
      | H t => rw [hγ, hα]; rfl
    have hγ1 := hfree γ hγp
    have hmod : ∀ t : T, t⁻¹ * α t ∈ N := by
      intro t
      have := hγ 1 t
      rw [pow_one, pow_one, hγ1] at this
      exact QuotientGroup.eq.1 this
    exact CFSG.LocalAnalysis.GorensteinLyons.mulAut_eq_one_of_odd_of_inv_mul_mem hN2 hodd hα
      hfix hmod

theorem projSL_eq_range_toPGL3 (n : ℕ) (K : Type*) [Field K] :
    projSL n K = (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjGenLinGroup (Fin n) K).range := by
  rw [projSL, CFSG.PGLModel.projImage, Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

theorem projSL_le_range_toPGL3 (n : ℕ) (K : Type*) [Field K] :
    projSL n K ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjGenLinGroup (Fin n) K).range :=
  (projSL_eq_range_toPGL3 n K).le

theorem projSU_le_range_toPGL3 (r e : ℕ) [Fact r.Prime] :
    CFSG.Assembly.RankThreeEven.projSU 3 r e ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField r (2 * e)) →*
        Matrix.ProjGenLinGroup (Fin 3) (GaloisField r (2 * e))).range := by
  rintro _ ⟨g, hg, rfl⟩
  have hdet : g ∈ (Matrix.GeneralLinearGroup.det :
      GL (Fin 3) (GaloisField r (2 * e)) →* (GaloisField r (2 * e))ˣ).ker := by
    refine (Subgroup.closure_le _).2 ?_ hg
    intro A hA
    exact hA.1
  rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hdet
  obtain ⟨s, rfl⟩ := hdet
  exact ⟨s, rfl⟩

theorem noTwoAut_of_le_range_toPGL3 (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (G : Subgroup PGL(3, K))
    (hG : G ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* PGL(3, K)).range) : NoTwoAut p G := by
  have hK2 : ringChar K ≠ 2 := by
    intro h
    haveI : Fintype K := Fintype.ofFinite K
    have h1 := (FiniteField.even_card_iff_char_two).1 h
    rw [← Nat.card_eq_fintype_card] at h1
    exact (Nat.not_even_iff_odd.2 hK) (Nat.even_iff.2 h1)
  intro Q hQ
  set Q' : Subgroup PGL(3, K) := Q.map G.subtype with hQ'def
  have hQ' : IsPGroup 2 Q' := hQ.map _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hTQ⟩ := CFSG.RankThree.PartTwo.Sec4.L34Odd.exists_isPGroup_map_eq 2
    (Matrix.SpecialLinearGroup.toPGL : Matrix.SpecialLinearGroup (Fin 3) K →* PGL(3, K)) Q' hQ'
    ((Subgroup.map_subtype_le Q).trans hG)
  have hinjT : Function.Injective
      ((Matrix.SpecialLinearGroup.toPGL :
        Matrix.SpecialLinearGroup (Fin 3) K →* PGL(3, K)).comp T.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Matrix.SpecialLinearGroup.toPGL_ker, Matrix.SpecialLinearGroup.mem_center_iff] at ht
    obtain ⟨r, hr, hrt⟩ := ht
    have hrt' : (Matrix.scalar (Fin 3) r) =
        ((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := hrt
    rw [Fintype.card_fin] at hr
    have h3 : (t : Matrix.SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrt', ← map_pow, hr, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have h3' : t ^ 3 = 1 := Subtype.ext (by simpa using h3)
    obtain ⟨k, hk⟩ := hT t
    have hdvd : orderOf t ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3') (orderOf_dvd_of_pow_eq_one hk)
    have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
      Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact hdvd ▸ Subgroup.one_mem _
  have hrange : ((Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* PGL(3, K)).comp T.subtype).range = Q' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hTQ]
  obtain ⟨σ, hσ⟩ := CFSG.RankThree.PartTwo.Sec4.L34Odd.exists_injective_gl2 hK hT T.subtype
    T.subtype_injective
  have hσP : IsPGroup 2 σ.range := hT.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
  refine TwoAutFree.of_mulEquiv ?_ (noTwoAut_gl2 K hK2 hp hp5 σ.range hσP)
  exact (Q.equivMapOfInjective G.subtype G.subtype_injective).trans
    (((MonoidHom.ofInjective hinjT).trans (MulEquiv.subgroupCongr hrange)).symm.trans
      (MonoidHom.ofInjective hσ))

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

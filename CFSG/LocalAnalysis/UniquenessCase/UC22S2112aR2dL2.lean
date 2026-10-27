module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.Open.LocalVocabulary
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Order
import CFSG.LocalAnalysis.UniquenessCase.UC6AutL2
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.RankThree.PartTwo.KFacts.K71bOutAbelian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

theorem uc22s2112r2d_sylow {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (e : X ≃* CFSG.GorensteinWalter.PSL2 (GaloisField p 3)) (S : Subgroup X) (hSp : IsPGroup p S)
    (hSi : ¬ p ∣ S.index) : IsElemAbelian p S ∧ Nat.card S = p ^ 3 := by
  have hF : Nat.card (GaloisField p 3) = p ^ 3 := GaloisField.card p 3 (by norm_num)
  let f : X →* CFSG.GorensteinWalter.PSL2 (GaloisField p 3) := e
  have hf : Function.Injective f := e.injective
  let T : Subgroup (CFSG.GorensteinWalter.PSL2 (GaloisField p 3)) := S.map f
  have hTp : IsPGroup p T := hSp.map f
  have hTi : ¬ p ∣ T.index := by
    rw [show T.index = S.index from Subgroup.index_map_equiv S e]
    exact hSi
  obtain ⟨hel, hcard⟩ := UC6.isElemAbelian_card_sylow_psl2 hp2 hF (by norm_num) (hTp.toSylow hTi)
  have hdisj : Disjoint S f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hf]
    exact disjoint_bot_right
  refine ⟨UC6S846.isElemAbelian_of_disjoint_ker f S hdisj hel, ?_⟩
  rw [← Subgroup.card_map_of_injective hf]
  exact hcard

theorem uc22s2112r2d_fix_sylow {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (e : X ≃* CFSG.GorensteinWalter.PSL2 (GaloisField p 3)) (S : Subgroup X)
    (hSp : IsPGroup p S) (hSi : ¬ p ∣ S.index) (α : MulAut X) (hα : ∃ k : ℕ, α ^ (p ^ k) = 1)
    (hαS : ∀ s ∈ S, α s ∈ S) : ∀ s ∈ S, α s = s := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := hα
  have h6 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ 3 * 2 :=
    ((CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp (GaloisField p 3)
      (GaloisField.card p 3 (by norm_num))).2 X ⟨e⟩).trans
      (Nat.mul_dvd_mul_left 3 (Nat.gcd_dvd_left 2 _))
  have hpOut : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).1 (hd.trans h6) with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    Nat.finite_of_card_ne_zero (fun h => by rw [h] at h6; norm_num at h6)
  have hinn := CFSG.AGLEmbedding.mem_inner_of_pow_prime_pow_eq_one hp hpOut hk
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1
    (show α ∈ (MulAut.conj : X →* MulAut X).range from hinn)
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_eq_bot_of_equiv_psl2 e
  have hxk : x ^ (p ^ k) = 1 :=
    UC6.conj_injective_of_center_eq_bot hZ (by rw [map_pow, hk, map_one])
  have hxN : x ∈ Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
    rintro _ ⟨s, hs, rfl⟩
    exact hαS s hs
  have hxS : x ∈ S := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hxk)
    have hZp : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hsup : IsPGroup p (S ⊔ Subgroup.zpowers x : Subgroup X) :=
      hSp.to_sup_of_normal_left' hZp (Subgroup.zpowers_le.2 hxN)
    have h := (hSp.toSylow hSi).is_maximal' hsup le_sup_left
    have hx : x ∈ S ⊔ Subgroup.zpowers x := le_sup_right (a := S) (Subgroup.mem_zpowers x)
    rw [h] at hx
    exact hx
  have hab := (uc22s2112r2d_sylow (by omega) e S hSp hSi).1
  intro s hs
  have hc : x * s = s * x :=
    congrArg Subtype.val (hab.1.is_comm.comm (⟨x, hxS⟩ : S) ⟨s, hs⟩)
  rw [MulAut.conj_apply, hc, mul_inv_cancel_right]

theorem uc22s2112r2d_mem_of_closure {Γ : Type*} [Group Γ] (I : Subgroup Γ) [I.Normal]
    (hcomm : ∀ σ τ : Γ, σ * τ * σ⁻¹ * τ⁻¹ ∈ I) {q : ℕ} (hq : q.Prime) (H : Subgroup Γ)
    (hgen : Subgroup.closure {x | x ∈ H ∧ ¬ q ∣ orderOf x} = H) {h : Γ} (hh : h ∈ H)
    (hk : h ^ q = 1) : h ∈ I := by
  classical
  let π : Γ →* Γ ⧸ I := QuotientGroup.mk' I
  have hc : ∀ a b : Γ ⧸ I, Commute a b := by
    intro a b
    induction a using QuotientGroup.induction_on with | H σ => ?_
    induction b using QuotientGroup.induction_on with | H τ => ?_
    have h1 : π (σ * τ * σ⁻¹ * τ⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 (hcomm σ τ)
    simp only [map_mul, map_inv] at h1
    show π σ * π τ = π τ * π σ
    calc π σ * π τ = (π σ * π τ * (π σ)⁻¹ * (π τ)⁻¹) * (π τ * π σ) := by group
      _ = π τ * π σ := by rw [h1, one_mul]
  let K : Subgroup (Γ ⧸ I) :=
    { carrier := {y | ¬ q ∣ orderOf y}
      mul_mem' := by
        intro a b ha hb hd
        exact (hq.dvd_mul.1 (hd.trans (hc a b).orderOf_mul_dvd_mul_orderOf)).elim ha hb
      one_mem' := by
        show ¬ q ∣ orderOf (1 : Γ ⧸ I)
        rw [orderOf_one]
        exact hq.not_dvd_one
      inv_mem' := by
        intro a ha
        show ¬ q ∣ orderOf a⁻¹
        rw [orderOf_inv]
        exact ha }
  have hHK : H.map π ≤ K := by
    rw [← hgen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨_, hx⟩, rfl⟩ hd
    exact hx (hd.trans (orderOf_map_dvd π x))
  have hπh : ¬ q ∣ orderOf (π h) := hHK ⟨h, hh, rfl⟩
  have h1 : orderOf (π h) ∣ q := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  rcases (Nat.dvd_prime hq).1 h1 with h2 | h2
  · exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h2)
  · exact absurd (h2 ▸ dvd_refl q) hπh

theorem uc22s2112r2d_inner {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (e : X ≃* CFSG.GorensteinWalter.PSL2 (GaloisField p 3)) {q : ℕ} (hq : q.Prime)
    (H : Subgroup (MulAut X)) (hgen : Subgroup.closure {x | x ∈ H ∧ ¬ q ∣ orderOf x} = H)
    {h : MulAut X} (hh : h ∈ H) (hk : h ^ q = 1) :
    h ∈ (MulAut.conj : X →* MulAut X).range := by
  have : (MulAut.conj : X →* MulAut X).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal X
  exact uc22s2112r2d_mem_of_closure _ (fun σ τ =>
    CFSG.RankThree.PartTwo.KFacts.isInnerAut_commutator_of_mulEquiv_psl2_all e σ τ)
    hq H hgen hh hk

theorem uc22s2112r2d_card_le {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (e : X ≃* CFSG.GorensteinWalter.PSL2 (GaloisField p 3)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p) (R : Subgroup (MulAut X)) (hR : IsElemAbelian r R)
    (hRi : R ≤ (MulAut.conj : X →* MulAut X).range) : Nat.card R ≤ r := by
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    UC6.conj_injective_of_center_eq_bot
      (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_eq_bot_of_equiv_psl2 e)
  let A : Subgroup X := R.comap MulAut.conj
  have hAR : A.map MulAut.conj = R := Subgroup.map_comap_eq_self hRi
  have hdisj : Disjoint A (MulAut.conj : X →* MulAut X).ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact disjoint_bot_right
  have hAel : IsElemAbelian r A :=
    UC6S846.isElemAbelian_of_disjoint_ker MulAut.conj A hdisj (by rw [hAR]; exact hR)
  let f : X →* CFSG.GorensteinWalter.PSL2 (GaloisField p 3) := e
  have hf : Function.Injective f := e.injective
  have hBel : IsElemAbelian r (A.map f) := hAel.map f
  have : NeZero (r : GaloisField p 3) := ⟨by
    intro h
    have h1 := (CharP.cast_eq_zero_iff (GaloisField p 3) p r).1 h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 h1).symm⟩
  have hB := CFSG.RankThree.PartOne.K133.psl2_elemAb_card_le hr hr2 (A.map f)
    hBel.isElementaryAbelian
  rw [← hAR, Subgroup.card_map_of_injective hinj, ← Subgroup.card_map_of_injective hf]
  exact hB

end CFSG.LocalAnalysis.UniquenessCase.UC22

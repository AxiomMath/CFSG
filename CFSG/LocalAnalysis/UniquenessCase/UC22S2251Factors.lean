module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wg
import all CFSG.Quasithin.Background.A1bKrullSchmidt
import CFSG.RankThree.PartOne.S11c.Simple168
import CFSG.RankThree.PartOne.S12.Sec1212Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigRank
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.S2251

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem normalizes_factors_of_pGroup {X : Type} [Group X] [Finite X] {m : ℕ}
    {H : Subgroup X} {Nb : Fin m → Subgroup X} (hd : Ext.IsInternalDirect H Nb)
    (hs : ∀ j, FactorShape22 ↥(Nb j)) {p : ℕ} (hp : p.Prime) (hmp : m < p)
    {g : X} (hgp : IsPGroup p (zpowers g)) (hgH : g ∈ normalizer (H : Set X)) :
    ∀ j, g ∈ normalizer (Nb j : Set X) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨τ, hτ⟩ := P22y.exists_perm hd
    (fun j => P22w.isIndecomposable_of_factorShape22 (hs j))
    (fun j => P22w.center_eq_bot_of_factorShape22 (hs j)) hgH
  have hmapOne : ∀ N : Subgroup X, N.map (MulAut.conj (1 : X)).toMonoidHom = N := by
    intro N
    have h : (MulAut.conj (1 : X)).toMonoidHom = MonoidHom.id X := by
      ext x
      simp
    rw [h, Subgroup.map_id]
  have hNb : Function.Injective Nb := by
    intro j k hjk
    by_contra hne
    have hle : Nb j ≤ ⨆ k, ⨆ (_ : k ≠ j), Nb k := by
      rw [hjk]
      exact le_iSup_of_le k (le_iSup_of_le (Ne.symm hne) le_rfl)
    have hbot : Nb j = ⊥ := by
      have h := hd.2.2 j
      change Nb j ⊓ (⨆ k, ⨆ (_ : k ≠ j), Nb k) = ⊥ at h
      rw [inf_of_le_left hle] at h
      exact h
    have hnt : Nontrivial ↥(Nb j) := by
      have h := P22w.isIndecomposable_of_factorShape22 (hs j)
      unfold CFSG.Quasithin.IsIndecomposableGroup at h
      exact h.1
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hbot
  obtain ⟨e, he⟩ := hgp ⟨g, mem_zpowers g⟩
  have hgpow : g ^ p ^ e = 1 := by simpa using congrArg Subtype.val he
  have hpow : ∀ n j, (Nb j).map (MulAut.conj (g ^ n)).toMonoidHom = Nb ((τ ^ n) j) := by
    intro n
    induction n with
    | zero =>
        intro j
        simpa only [pow_zero, Equiv.Perm.one_apply] using hmapOne (Nb j)
    | succ n ih =>
        intro j
        have h1 := (ih ((τ j)))
        rw [← hτ j, Subgroup.map_map] at h1
        have hconj : (MulAut.conj (g ^ n)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
            (MulAut.conj (g ^ (n + 1))).toMonoidHom := by
          ext x
          simp [pow_succ, mul_assoc]
        rw [hconj] at h1
        simpa only [pow_succ, Equiv.Perm.mul_apply] using h1
  have hτpow : τ ^ p ^ e = 1 := by
    apply Equiv.ext
    intro j
    apply hNb
    have h := hpow (p ^ e) j
    simpa only [hgpow, hmapOne, Equiv.Perm.one_apply] using h.symm
  have hτp : IsPGroup p (zpowers τ) := P2251f.isPGroup_zpowers_of_pow hτpow
  have hτ1 : τ = 1 := by
    by_contra hne
    have hpd : p ∣ orderOf τ := by
      have h := hτp.dvd_orderOf (g := ⟨τ, mem_zpowers τ⟩)
        (fun h => hne (congrArg Subtype.val h))
      simpa only [Subgroup.orderOf_mk] using h
    have hcard : orderOf τ ∣ m.factorial := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        using orderOf_dvd_natCard τ
    exact (Nat.not_le.2 hmp) ((hp.dvd_factorial).1 (hpd.trans hcard))
  intro j
  apply CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem
  intro x hx
  have h := hτ j
  rw [hτ1, Equiv.Perm.one_apply] at h
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem s3_factor_count_le (D : Data G) {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) (i : Fin m)
    (hS3 : ∀ j, j ≠ i → IsL2Ev ↥(Nb j) 1) (hRank : CFSG.pRank 3 D.M ≤ 3) : m ≤ 4 := by
  classical
  cases m with
  | zero => exact i.elim0
  | succ r =>
    let π : D.M →* MBar D.M D.U := QuotientGroup.mk' (kerAct D.M D.U).normalCore
    let Lc : Fin r → Subgroup (MBar D.M D.U) := fun j => Nb (i.succAbove j)
    have hiso : ∀ j, Nonempty (↥(Lc j) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
      intro j
      obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := P22y.exists_equiv_sl2 (hS3 _ (Fin.succAbove_ne i j))
      let : Fintype F := Fintype.ofFinite F
      have hcard : Fintype.card F = Fintype.card (ZMod 2) := by
        rw [← Nat.card_eq_fintype_card, hF]
        norm_num
      exact ⟨e.trans (P22s.slMapEquiv (FiniteField.ringEquivOfCardEq hcard))⟩
    have hcomm : ∀ j k, j ≠ k → ∀ x ∈ Lc j, ∀ y ∈ Lc k, x * y = y * x := by
      intro j k hjk x hx y hy
      exact hNb.1.2.1 _ _ (fun h => hjk ((Fin.succAbove_inj).1 h)) x hx y hy
    have hind : ∀ j, Lc j ⊓ (⨆ k, ⨆ (_ : k ≠ j), Lc k) = ⊥ := by
      intro j
      refine eq_bot_iff.2 ((inf_le_inf_left _ (iSup_le fun k => iSup_le fun hkj => ?_)).trans
        (hNb.1.2.2 (i.succAbove j)).le)
      exact le_iSup_of_le (i.succAbove k) (le_iSup_of_le
        (fun h => hkj ((Fin.succAbove_inj).1 h)) le_rfl)
    have hrange : ∀ j, Lc j ≤ π.range := by
      intro j
      rw [MonoidHom.range_eq_top_of_surjective π (QuotientGroup.mk'_surjective _)]
      exact le_top
    obtain ⟨Y₀, f, hf⟩ := CFSG.QuasithinUnique.Setup.Lift.exists_section_symThree_pow π Lc
      hrange hiso hcomm hind
    have hr := CFSG.QuasithinUnique.Setup.Lift.sym_three_pow_section_forces_three_rank r Y₀ f hf
    omega

theorem centralizes_s3_of_pGroup {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hA : IsL2Ev ↥A 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {g : X}
    (hgp : IsPGroup p (zpowers g)) (hgA : g ∈ normalizer (A : Set X)) :
    g ∈ centralizer (A : Set X) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := P22y.exists_equiv_sl2 hA
  let : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 1) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 1 (by norm_num)]
  let eA : ↥A ≃* Equiv.Perm (Fin 3) :=
    (e.trans (P22s.slMapEquiv (FiniteField.ringEquivOfCardEq hcard))).trans
      CFSG.Quasithin.slTwoEquivPermThree
  let gn : normalizer (A : Set X) := ⟨g, hgA⟩
  let σ : MulAut (Equiv.Perm (Fin 3)) := MulAut.congr eA (A.normalizerMonoidHom gn)
  obtain ⟨k, hk⟩ := hgp ⟨g, mem_zpowers g⟩
  have hgnpow : gn ^ p ^ k = 1 := Subtype.ext (by
    simpa only [gn, Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hk)
  have hpow : σ ^ p ^ k = 1 := by
    change (MulAut.congr eA (A.normalizerMonoidHom gn)) ^ p ^ k = 1
    rw [← map_pow, ← map_pow, hgnpow, map_one, map_one]
  have hσ : σ = 1 := by
    by_contra hne
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hpow)
    have hj0 : j ≠ 0 := by
      intro h
      exact hne (orderOf_eq_one_iff.1 (by rw [hj, h, pow_zero]))
    have hord : orderOf (σ ^ (orderOf σ / p)) = p := orderOf_pow_orderOf_div
      (by rw [hj]; exact pow_ne_zero _ hp.ne_zero) (by rw [hj]; exact dvd_pow_self p hj0)
    have hσpow : (σ ^ (orderOf σ / p)) ^ p = 1 := by
      simpa only [hord] using pow_orderOf_eq_one (σ ^ (orderOf σ / p))
    have htr := CFSG.RankThree.PartOne.Sec1212Aut.mulAut_perm_three hp hp5
      (σ ^ (orderOf σ / p)) hσpow
    rw [htr, orderOf_one] at hord
    exact hp.one_lt.ne' hord.symm
  have hact : A.normalizerMonoidHom gn = 1 := by
    apply (MulAut.congr eA).injective
    exact hσ.trans (map_one _).symm
  rw [mem_centralizer_iff]
  intro a ha
  have h := congrArg (fun s : MulAut A => (s ⟨a, ha⟩ : X)) hact
  change g * a * g⁻¹ = a at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem not_sq_dvd_card_mulAut_bad {X : Type} [Group X] [Finite X]
    (hX : IsL2Ev X 2 ∨ IsL3 X 1 ∨ IsS5 X) {p : ℕ} (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card (MulAut X) := by
  rcases hX with h | h | h
  · exact BadShape22.not_sq_dvd_card_mulAut (Or.inl h) hp5
  · exact BadShape22.not_sq_dvd_card_mulAut (Or.inr h) hp5
  · obtain ⟨e⟩ : Nonempty (X ≃* Equiv.Perm (Fin 5)) := h
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      ← Nat.card_congr (MulEquiv.ofBijective (MulAut.conj : Equiv.Perm (Fin 5) →*
        MulAut (Equiv.Perm (Fin 5))) CFSG.Monster.B.TwoA.sym5_conj_bijective).toEquiv]
    have hcard : Nat.card (Equiv.Perm (Fin 5)) = 120 := P2251f.card_perm_fin_five
    rw [hcard]
    intro h
    have hp10 : p ≤ 10 := by
      have hle := Nat.le_of_dvd (by norm_num : 0 < 120) h
      nlinarith
    interval_cases p <;> norm_num at h

theorem centralizer_relIndex_le_prime {X : Type} [Group X] [Finite X] {m : ℕ}
    {H : Subgroup X} {Nb : Fin m → Subgroup X} (hd : Ext.IsInternalDirect H Nb)
    (hs : ∀ j, FactorShape22 ↥(Nb j)) (i : Fin m)
    (hbad : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i))
    (hS3 : ∀ j, j ≠ i → IsL2Ev ↥(Nb j) 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmp : m < p) {P : Subgroup X} (hP : IsPGroup p P)
    (hPH : P ≤ normalizer (H : Set X)) :
    (centralizer (H : Set X)).relIndex P ≤ p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn : ∀ j, P ≤ normalizer (Nb j : Set X) := fun j g hg =>
    normalizes_factors_of_pGroup hd hs hp hmp (hP.to_le (zpowers_le.2 hg)) (hPH hg) j
  let φ : P →* MulAut ↥(Nb i) :=
    (Nb i).normalizerMonoidHom.comp (Subgroup.inclusion (hn i))
  have hker : φ.ker = (centralizer (H : Set X)).subgroupOf P := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro hg h hh
      have hci : (g : X) ∈ centralizer (Nb i : Set X) := by
        rw [mem_centralizer_iff]
        intro x hx
        have h := congrArg (fun a : MulAut ↥(Nb i) => (a ⟨x, hx⟩ : X)) hg
        change (g : X) * x * (g : X)⁻¹ = x at h
        exact (mul_inv_eq_iff_eq_mul.1 h).symm
      have hcall : ∀ j, (g : X) ∈ centralizer (Nb j : Set X) := by
        intro j
        by_cases hji : j = i
        · simpa only [hji] using hci
        · exact centralizes_s3_of_pGroup (hS3 j hji) hp hp5
            (hP.to_le (zpowers_le.2 g.2)) (hn j g.2)
      have hHC : H ≤ centralizer ({(g : X)} : Set X) := by
        rw [← hd.1]
        refine iSup_le fun j => ?_
        intro x hx
        exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hcall j) x hx)
      exact mem_centralizer_singleton_iff.1 (hHC hh)
    · intro hg
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change (g : X) * (x : X) * (g : X)⁻¹ = (x : X)
      exact mul_inv_eq_iff_eq_mul.2 (hg _ ((hd.1.symm ▸ le_iSup Nb i) x.2)).symm
  have hφp : IsPGroup p φ.range := hP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hφp
  have hk1 : k ≤ 1 := by
    by_contra h
    exact not_sq_dvd_card_mulAut_bad hbad hp5
      ((pow_dvd_pow p (show 2 ≤ k by omega)).trans
        (hk.symm.dvd.trans (Subgroup.card_subgroup_dvd_card φ.range)))
  have hcard : Nat.card φ.range ≤ p := by
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one _
  change ((centralizer (H : Set X)).subgroupOf P).index ≤ p
  rw [← hker, Subgroup.index_ker]
  exact hcard

end CFSG.LocalAnalysis.UniquenessCase.UC22.S2251

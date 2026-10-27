module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.Classical.EvenSurvivingScalarRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Assembly.RankThreeEven

theorem exponent_eq_of_forall_pow_eq_one {G : Type*} [Group G] [Nontrivial G] {p : ℕ}
    (hp : p.Prime) (h : ∀ x : G, x ^ p = 1) : Monoid.exponent G = p := by
  rcases (Nat.dvd_prime hp).1 (Monoid.exponent_dvd_of_forall_pow_eq_one h) with h1 | h1
  · rw [Monoid.exp_eq_one_iff] at h1
    exact absurd h1 (not_subsingleton G)
  · exact h1

theorem range_frattiniAction_conj_ne_bot {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y]
    [Group.IsPerfect Y] {P : Subgroup Y} [P.Normal] [Finite P] (D : Subgroup P)
    [D.Characteristic] (hker : IsPGroup p (frattiniAction D).ker)
    (hYP : ⁅(⊤ : Subgroup Y), P⁆ ≠ ⊥) :
    ((frattiniAction D).comp (MulAut.conjNormal (H := P))).range ≠ ⊥ := by
  intro hbot
  apply hYP
  set c : Y →* MulAut P := MulAut.conjNormal with hc
  have hle : c.range ≤ (frattiniAction D).ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    have : (frattiniAction D).comp c y ∈ ((frattiniAction D).comp c).range := ⟨y, rfl⟩
    rw [hbot, mem_bot] at this
    exact this
  have : Finite (MulAut P) := inferInstance
  have hpg : IsPGroup p c.range := hker.to_le hle
  have : Group.IsPerfect c.range := Group.IsPerfect.range c
  have hc1 : c.range = ⊥ := by
    by_contra hne
    have : Nontrivial c.range := (nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent c.range hpg.isNilpotent
  rw [eq_bot_iff, commutator_le]
  intro y _ x hx
  have hy : c y = 1 := by
    have : c y ∈ c.range := ⟨y, rfl⟩
    rw [hc1, mem_bot] at this
    exact this
  have h2 := congrArg (fun σ : MulAut P => ((σ ⟨x, hx⟩ : P) : Y)) hy
  simp only [hc, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  rw [mem_bot, commutatorElement_def, h2, mul_inv_cancel]

theorem det_eq_one_of_mem_range {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Group.IsPerfect Y]
    {W : Type*} [Group W] (α : Y →* MulAut W) {n : ℕ} (e : W ≃* Multiplicative (Fin n → ZMod p))
    {r : MulAut W} (hr : r ∈ α.range) : Matrix.GeneralLinearGroup.det (elemAutEquivGL e r) = 1 := by
  have : Group.IsPerfect α.range := Group.IsPerfect.range α
  have h := perfect_hom_eq_one_of_range_comm
    ((Matrix.GeneralLinearGroup.det.comp (elemAutEquivGL e).toMonoidHom).comp α.range.subtype)
    (fun a _ b _ => mul_comm a b)
  exact DFunLike.congr_fun h ⟨r, hr⟩

theorem map_comap_centralizer {Y : Type*} [Group Y] {P : Subgroup Y} (D : Subgroup P) (t : Y) :
    ((centralizer {t}).comap (P.subtype.comp D.subtype)).map (P.subtype.comp D.subtype) =
      D.map P.subtype ⊓ centralizer {t} := by
  rw [map_comap_eq, MonoidHom.range_comp, range_subtype]

theorem card_fixed_frattini_quotient_le {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {Y : Type*}
    [Group Y] [Finite Y] {P : Subgroup Y} [P.Normal] (hP : IsPGroup p P) (D : Subgroup P)
    [D.Characteristic] (hDexp : ∀ x ∈ D, x ^ p = 1) {t : Y} (ht : orderOf t = 2)
    (hrank : CFSG.Open.pRank p (D.map P.subtype ⊓ centralizer {t}) ≤ 2) :
    Nat.card {w : D ⧸ frattini D //
      (frattiniAction D).comp (MulAut.conjNormal (H := P)) t w = w} ≤ p ^ 2 := by
  classical
  set α : Y →* MulAut (D ⧸ frattini D) := (frattiniAction D).comp (MulAut.conjNormal (H := P))
    with hα
  set g : D →* Y := P.subtype.comp D.subtype with hg
  have hginj : Function.Injective g := P.subtype_injective.comp D.subtype_injective
  set C' : Subgroup D := (centralizer {t}).comap g with hC'
  have hDp : IsPGroup p D := hP.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hC'rank : CFSG.Open.pRank p (⊤ : Subgroup C') ≤ 2 := by
    rw [pRank_top_eq_of_mulEquiv hp.out.one_lt ((C'.equivMapOfInjective g hginj).trans
      (MulEquiv.subgroupCongr (map_comap_centralizer D t))), ← pRank_eq_pRank_top_subgroup]
    exact hrank
  have hC'p : IsPGroup p C' := hDp.to_subgroup C'
  have hC'exp : ∀ x : C', x ^ p = 1 := fun x =>
    Subtype.ext (Subtype.ext (by simpa using hDexp _ x.1.2))
  obtain ⟨-, hΦ⟩ := rank_two_exponent_prime_order_bound hC'p hC'exp hC'rank
  set f : C' →* D ⧸ frattini D := (QuotientGroup.mk' (frattini D)).comp C'.subtype with hf
  have hfΦ : frattini C' ≤ f.ker := frattini_le_ker_of_elementary f hWcomm hWpow
  set A := zpowers t with hA
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  set β : A →* MulAut D := (MulAut.characteristic D).comp
    ((MulAut.conjNormal (H := P)).comp A.subtype) with hβ
  have hΦinv : ∀ a : A, ∀ n ∈ frattini D, β a n ∈ frattini D := fun a n hn =>
    characteristic_iff_le_comap.mp inferInstance (β a) hn
  have hcop : ¬ 2 ∣ Nat.card (frattini D) := by
    obtain ⟨k, hk⟩ := (hDp.to_subgroup (frattini D)).exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hA2 β (frattini D)
    hΦinv hcop
  have hqa : ∀ a : A, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction β
      (frattini D) hΦinv a = α a := fun a => rfl
  have hset : ∀ w : D ⧸ frattini D, α t w = w ↔ w ∈ f.range := by
    intro w
    constructor
    · intro hw
      have hstab : A ≤ (MulAction.stabilizer (MulAut (D ⧸ frattini D)) w).comap α := by
        rw [hA, zpowers_le, mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hw
      have hmem : w ∈ {q : D ⧸ frattini D | ∀ a : A,
          CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction β (frattini D) hΦinv a q
            = q} := by
        intro a
        rw [hqa]
        have := hstab a.2
        rwa [mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
      rw [hlift] at hmem
      obtain ⟨c, hc, rfl⟩ := hmem
      refine ⟨⟨c, ?_⟩, rfl⟩
      have h1 := congrArg (fun x : D => ((x : P) : Y)) (hc ⟨t, mem_zpowers t⟩)
      simp only [hβ, MonoidHom.comp_apply, MulAut.characteristic_apply_apply_coe,
        coe_subtype, MulAut.conjNormal_apply] at h1
      rw [hC', mem_comap, mem_centralizer_singleton_iff]
      change ((c : P) : Y) * t = t * ((c : P) : Y)
      calc ((c : P) : Y) * t = t * ((c : P) : Y) * t⁻¹ * t := by rw [h1]
        _ = t * ((c : P) : Y) := by group
    · rintro ⟨c, rfl⟩
      have hc : g c * t = t * g c := mem_centralizer_singleton_iff.1 c.2
      change frattiniAction D (MulAut.conjNormal t) ((c : D) : D ⧸ frattini D) =
        ((c : D) : D ⧸ frattini D)
      rw [frattiniAction_mk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      change t * ((c : D) : P) * t⁻¹ = (((c : D) : P) : Y)
      change ((c : D) : P) * t = t * ((c : D) : P) at hc
      rw [← hc, mul_inv_cancel_right]
  have hcard : Nat.card {w : D ⧸ frattini D // α t w = w} = Nat.card f.range :=
    Nat.card_congr (Equiv.subtypeEquivRight hset)
  rw [hcard, ← Subgroup.index_ker]
  calc f.ker.index ≤ (frattini C').index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
          (Subgroup.index_dvd_of_le hfΦ)
    _ = Nat.card (C' ⧸ frattini C') := rfl
    _ ≤ p ^ 2 := hΦ

theorem odd_prime_kernel_critical_involution_fixed_spaces {p : ℕ} [hp : Fact p.Prime]
    (hp3 : 3 < p) {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y) [P.Normal]
    (hP : IsPGroup p P) (hP1 : P ≠ ⊥) (hYP : ⁅(⊤ : Subgroup Y), P⁆ ≠ ⊥)
    (hloc : localRank p Y ≤ 2) :
    ∃ D : Subgroup P, ∃ _ : D.Characteristic, D ≠ ⊥ ∧ Monoid.exponent D = p ∧
      ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P) ∧
      IsPGroup p (frattiniAction D).ker ∧ D.lowerCentralSeries 2 = ⊥ ∧
      ((frattiniAction D).comp (MulAut.conjNormal (H := P))).range ≠ ⊥ ∧
      Group.IsPerfect ((frattiniAction D).comp (MulAut.conjNormal (H := P))).range ∧
      (∀ (n : ℕ) (e : D ⧸ frattini D ≃* Multiplicative (Fin n → ZMod p)),
        ∀ r ∈ ((frattiniAction D).comp (MulAut.conjNormal (H := P))).range,
          Matrix.GeneralLinearGroup.det (elemAutEquivGL e r) = 1) ∧
      ∀ t : Y, orderOf t = 2 →
        pRank p (D.map P.subtype ⊓ centralizer {t} : Subgroup Y) ≤ 2 ∧
          Nat.card {w : D ⧸ frattini D //
            (frattiniAction D).comp (MulAut.conjNormal (H := P)) t w = w} ≤ p ^ 2 := by
  have hp2 : p ≠ 2 := by omega
  have : Nontrivial P := (nontrivial_iff_ne_bot P).2 hP1
  obtain ⟨D, hDc, hD1, hDexp, hDZ, -, hker⟩ := supercritical_witness hp2 hP
  have : Nontrivial D := (nontrivial_iff_ne_bot D).2 hD1
  have hexp : Monoid.exponent D = p := exponent_eq_of_forall_pow_eq_one hp.out fun x =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, hDexp x x.2, OneMemClass.coe_one])
  have hclass : D.lowerCentralSeries 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero, commutator_eq_bot_iff_le_centralizer]
    exact (commutator_mono le_rfl le_top).trans (hDZ.trans inf_le_right)
  refine ⟨D, hDc, hD1, hexp, hDZ, hker, hclass, range_frattiniAction_conj_ne_bot D hker hYP,
    Group.IsPerfect.range _, fun n e r hr => det_eq_one_of_mem_range _ e hr, ?_⟩
  intro t ht
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hA2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hAne : zpowers t ≠ ⊥ := fun h => ht1 (by
    have : t ∈ zpowers t := mem_zpowers t
    rwa [h, mem_bot] at this)
  have hloc' : CFSG.Assembly.IsTwoLocal (normalizer (zpowers t : Set Y)) :=
    ⟨_, hAne, hA2, rfl⟩
  have hCN : D.map P.subtype ⊓ centralizer {t} ≤ normalizer (zpowers t : Set Y) := by
    refine inf_le_right.trans ?_
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact centralizer_le_normalizer _
  have hCrank : CFSG.Open.pRank p (D.map P.subtype ⊓ centralizer {t}) ≤ 2 :=
    ((pRank_mono hp.out.one_lt hCN).trans
      (CFSG.RankThree.Classical.pRank_le_localRank hp.out.one_lt hloc')).trans hloc
  refine ⟨?_, card_fixed_frattini_quotient_le hp2 hP D hDexp ht hCrank⟩
  rw [pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup]
  exact hCrank

end CFSG.RankThree.OddKernel

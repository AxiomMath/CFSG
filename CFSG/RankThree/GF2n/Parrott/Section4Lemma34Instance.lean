module

public import CFSG.RankThree.GF2n.Parrott.Section3Lemma34
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma34Local
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma34Model
public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality

import CFSG.RankThree.GF2n.Parrott.SpinFixedCardMore
import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveStructure
import CFSG.RankThree.GF2n.Parrott.SpinTFacts

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem lemma34_dvd_card_orbit {Q : Type} [Group Q] [Finite Q]
    {D : Subgroup Q} (hDn : ∀ g : Q, ∀ d ∈ D, g * d * g⁻¹ ∈ D) {a : Q} (ha : a ∈ D) (ha1 : a ≠ 1)
    {σ : Q} {p : ℕ} [Fact p.Prime] (hσ : orderOf σ = p)
    (hf : ∀ d ∈ D, σ * d * σ⁻¹ = d → d = 1) :
    p ∣ Nat.card (MulAction.orbit (ConjAct Q) a) := by
  set Z : Subgroup (ConjAct Q) := Subgroup.zpowers (ConjAct.toConjAct σ) with hZ
  have hZcard : Nat.card Z = p ^ 1 := by
    rw [pow_one, hZ, Nat.card_zpowers, MulEquiv.orderOf_eq ConjAct.toConjAct σ, hσ]
  have hZp : IsPGroup p Z := IsPGroup.of_card hZcard
  have h1 := hZp.card_modEq_card_fixedPoints (MulAction.orbit (ConjAct Q) a)
  have h2 : Nat.card (MulAction.fixedPoints Z (MulAction.orbit (ConjAct Q) a)) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨⟨x, hx⟩, hxfix⟩
    obtain ⟨g, hg⟩ := hx
    have hg' : g • a = x := hg
    have hxD : x ∈ D := by
      rw [← hg', ConjAct.smul_def]
      exact hDn _ a ha
    have h' : (ConjAct.toConjAct σ) • x = x :=
      congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hxfix)
        ⟨ConjAct.toConjAct σ, Subgroup.mem_zpowers _⟩)
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h'
    have hx1 := hf x hxD h'
    apply ha1
    rw [← hg', ConjAct.smul_def] at hx1
    have : a = (ConjAct.ofConjAct g)⁻¹ * ((ConjAct.ofConjAct g) * a * (ConjAct.ofConjAct g)⁻¹) *
      ConjAct.ofConjAct g := by group
    rw [this, hx1]
    group
  rw [h2] at h1
  exact (Nat.modEq_zero_iff_dvd).mp (by simpa using h1)


private theorem lemma34_transitive_of_fixedPointFree {Q : Type} [Group Q] [Finite Q]
    {D : Subgroup Q} (hD : Nat.card D = 16) (hDn : ∀ g : Q, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    {σ₃ σ₅ : Q} (h3 : orderOf σ₃ = 3) (h5 : orderOf σ₅ = 5)
    (f3 : ∀ d ∈ D, σ₃ * d * σ₃⁻¹ = d → d = 1) (f5 : ∀ d ∈ D, σ₅ * d * σ₅⁻¹ = d → d = 1) :
    ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g : Q, g * a * g⁻¹ = b := by
  intro a ha b hb ha1 hb1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have d3 := lemma34_dvd_card_orbit hDn ha ha1 h3 f3
  have d5 := lemma34_dvd_card_orbit hDn ha ha1 h5 f5
  have d15 : 15 ∣ Nat.card (MulAction.orbit (ConjAct Q) a) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) d3 d5
  have hOsub : (MulAction.orbit (ConjAct Q) a : Set Q) ⊆ (D : Set Q) \ {1} := by
    rintro x ⟨g, rfl⟩
    have hgD : g • a ∈ D := by
      rw [ConjAct.smul_def]
      exact hDn _ a ha
    refine ⟨hgD, fun hx1 => ha1 ?_⟩
    have hx1' : g • a = 1 := hx1
    rw [ConjAct.smul_def] at hx1'
    have : a = (ConjAct.ofConjAct g)⁻¹ * ((ConjAct.ofConjAct g) * a * (ConjAct.ofConjAct g)⁻¹) *
      ConjAct.ofConjAct g := by group
    rw [this, hx1']
    group
  have h1D : (1 : Q) ∈ (D : Set Q) := D.one_mem
  have hDcard : ((D : Set Q) \ {1}).ncard = 15 := by
    rw [Set.ncard_diff_singleton_of_mem h1D, ← Nat.card_coe_set_eq]
    show Nat.card D - 1 = 15
    rw [hD]
  have hOpos : 0 < Nat.card (MulAction.orbit (ConjAct Q) a) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨a, MulAction.mem_orbit_self a⟩⟩, inferInstance⟩
  have hOle : (MulAction.orbit (ConjAct Q) a : Set Q).ncard ≤ 15 := by
    rw [← hDcard]
    exact Set.ncard_le_ncard hOsub (Set.toFinite _)
  have hOcard : (MulAction.orbit (ConjAct Q) a : Set Q).ncard = 15 := by
    have h1 : 15 ≤ Nat.card (MulAction.orbit (ConjAct Q) a) := Nat.le_of_dvd hOpos d15
    have h2 : Nat.card (MulAction.orbit (ConjAct Q) a) =
        (MulAction.orbit (ConjAct Q) a : Set Q).ncard := Nat.card_coe_set_eq _
    omega
  have hEq : (MulAction.orbit (ConjAct Q) a : Set Q) = (D : Set Q) \ {1} :=
    Set.eq_of_subset_of_ncard_le hOsub (by rw [hDcard, hOcard]) (Set.toFinite _)
  have hbO : b ∈ (MulAction.orbit (ConjAct Q) a : Set Q) := by
    rw [hEq]
    exact ⟨hb, hb1⟩
  obtain ⟨g, hg⟩ := hbO
  exact ⟨ConjAct.ofConjAct g, by simpa [ConjAct.smul_def] using hg⟩


private theorem lemma34_mem_of_mulAut_fixedPointFree {V : Type*} [CommGroup V] (T : MulAut V)
    (W : Subgroup V) {p : ℕ} (hp : Odd p) (hT : T ^ p = 1) (hTW : ∀ w ∈ W, T w ∈ W)
    (hsq : ∀ v : V, v ^ 2 = 1) (hfix : ∀ v : V, T v = v → v = 1) {v : V}
    (hv : T v * v⁻¹ ∈ W) : v ∈ W := by
  have hi : ∀ i : ℕ, (T ^ i) v * v⁻¹ ∈ W := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : (T ^ (i + 1)) v * v⁻¹ = T ((T ^ i) v * v⁻¹) * (T v * v⁻¹) := by
        rw [pow_succ', MulAut.mul_apply, map_mul, map_inv]
        group
      rw [e]
      exact W.mul_mem (hTW _ ih) hv
  have hTu : T (∏ i ∈ Finset.range p, (T ^ i) v) = ∏ i ∈ Finset.range p, (T ^ i) v := by
    have h1 : T (∏ i ∈ Finset.range p, (T ^ i) v) = ∏ i ∈ Finset.range p, (T ^ (i + 1)) v := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [pow_succ', MulAut.mul_apply]
    rw [h1]
    have a1 := Finset.prod_range_succ (fun i => (T ^ i) v) p
    have a2 := Finset.prod_range_succ' (fun i => (T ^ i) v) p
    simp only [hT, pow_zero, MulAut.one_apply] at a1 a2
    exact mul_right_cancel (a2.symm.trans a1)
  have hu1 := hfix _ hTu
  have hu : ∏ i ∈ Finset.range p, (T ^ i) v =
      (∏ i ∈ Finset.range p, ((T ^ i) v * v⁻¹)) * v ^ p := by
    have h1 : v ^ p = ∏ _i ∈ Finset.range p, v := by
      rw [Finset.prod_const, Finset.card_range]
    rw [h1, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    group
  have hvp : v ^ p = v := by
    obtain ⟨k, hk⟩ := hp
    rw [hk, pow_succ, pow_mul, hsq v, one_pow, one_mul]
  rw [hu, hvp] at hu1
  have hw : (∏ i ∈ Finset.range p, ((T ^ i) v * v⁻¹)) ∈ W :=
    Subgroup.prod_mem W fun i _ => hi i
  have : v = (∏ i ∈ Finset.range p, ((T ^ i) v * v⁻¹))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, mul_comm]
    exact hu1
  rw [this]
  exact W.inv_mem hw

private theorem lemma34_mem_of_commutator_mem (h : Tim79a.ParrottHyp z)
    {E : Subgroup G} (hE : IsParrottE z E) {σ : ↥(H z)}
    (hσN : (σ : G) ∈ Subgroup.normalizer (E : Set G)) {p : ℕ} (hp : Odd p) (hσp : σ ^ p = 1)
    (hfix : fixDimV h σ = 0) :
    ∀ r ∈ J z ⊔ E, (σ : G) * r * (σ : G)⁻¹ * r⁻¹ ∈ E → r ∈ E := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  have hJN := J_le_normalizer_of_isParrottE h hE
  have hEJ : E ⊓ J z ≤ J z := inf_le_right
  have hconjE : ∀ j ∈ J z, ∀ e ∈ E, j * e * j⁻¹ ∈ E := fun j hj e he =>
    (Subgroup.mem_normalizer_iff.mp (hJN hj) e).mp he
  have hσE : ∀ e ∈ E, (σ : G) * e * (σ : G)⁻¹ ∈ E := fun e he =>
    (Subgroup.mem_normalizer_iff.mp hσN e).mp he
  have hσJ : ∀ j ∈ J z, (σ : G) * j * (σ : G)⁻¹ ∈ J z := fun j hj =>
    lemma34_conj_mem_J σ.2 hj
  set T : MulAut (QuotientV.V z) := conjV h σ with hT
  set W : Subgroup (QuotientV.V z) := imageInV hEJ with hW
  have hTW : ∀ w ∈ W, T w ∈ W := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := (mem_imageInV_iff hEJ w).mp hw
    refine (mem_imageInV_iff hEJ _).mpr ⟨(σ : G) * b * (σ : G)⁻¹, ⟨hσE b hb.1, hσJ b hb.2⟩, ?_⟩
    rw [hT, conjV_mk]
    rfl
  have hTp : T ^ p = 1 := by
    rw [hT, ← map_pow, hσp, map_one]
  have hfixT : ∀ v : QuotientV.V z, T v = v → v = 1 := by
    have hcard : Nat.card (autFixedSubgroup (conjV h σ)) = 1 := by
      rw [card_fix h σ, hfix, pow_zero]
    have hbot := Subgroup.eq_bot_of_card_eq _ hcard
    intro v hv
    have : v ∈ autFixedSubgroup (conjV h σ) := mem_autFixedSubgroup.mpr hv
    rw [hbot] at this
    exact (Subgroup.mem_bot).mp this
  intro r hr hcomm
  obtain ⟨j, hj, e, he, rfl⟩ := lemma34_exists_mul_of_mem_sup hJN hr
  have hσjE : (σ : G) * j * (σ : G)⁻¹ * j⁻¹ ∈ E := by
    have h1 : (σ : G) * (j * e) * (σ : G)⁻¹ * (j * e)⁻¹ =
        ((σ : G) * j * (σ : G)⁻¹ * j⁻¹) * (j * ((σ : G) * e * (σ : G)⁻¹ * e⁻¹) * j⁻¹) := by
      group
    have h2 : (j * ((σ : G) * e * (σ : G)⁻¹ * e⁻¹) * j⁻¹) ∈ E :=
      hconjE j hj _ (E.mul_mem (hσE e he) (E.inv_mem he))
    rw [h1] at hcomm
    have h3 := E.mul_mem hcomm (E.inv_mem h2)
    rwa [mul_inv_cancel_right] at h3
  have hσjJ : (σ : G) * j * (σ : G)⁻¹ * j⁻¹ ∈ J z :=
    (J z).mul_mem (hσJ j hj) ((J z).inv_mem hj)
  have hv : T (QuotientV.pi z ⟨j, hj⟩) * (QuotientV.pi z ⟨j, hj⟩)⁻¹ ∈ W := by
    refine (mem_imageInV_iff hEJ _).mpr ⟨(σ : G) * j * (σ : G)⁻¹ * j⁻¹, ⟨hσjE, hσjJ⟩, ?_⟩
    rw [hT, conjV_mk, ← map_inv, ← map_mul]
    rfl
  have hmem := lemma34_mem_of_mulAut_fixedPointFree T W hp hTp hTW (QuotientV.pow_two_eq_one_V h)
    hfixT hv
  obtain ⟨b, hb, hbj⟩ := (mem_imageInV_iff hEJ _).mp hmem
  have hb' : b⁻¹ * j ∈ centerIn (J z) := by
    have h1 : QuotientV.pi z (⟨b, hEJ hb⟩⁻¹ * ⟨j, hj⟩) = 1 := by
      rw [map_mul, map_inv, hbj, inv_mul_cancel]
    have h2 : (⟨b, hEJ hb⟩⁻¹ * ⟨j, hj⟩ : ↥(J z)) ∈ (QuotientV.pi z).ker := h1
    rw [QuotientV.pi_ker] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hjE : j ∈ E := by
    have h1 : j = b * (b⁻¹ * j) := by group
    rw [h1]
    exact E.mul_mem hb.1 (hE.2.2.1 hb')
  exact E.mul_mem hjE he

private theorem lemma34_fixCard_eq_fixedCount (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    fixCard M = CFSG.LinearAlgebra.F2Cube.fixedCount M := by
  unfold fixCard CFSG.LinearAlgebra.F2Cube.fixedCount
  exact Fintype.card_congr (Equiv.refl _)

section Quotient

variable {N E : Subgroup G} {Y : Type} [Group Y] {q : ↥N →* Y}

omit [Finite G] in
private theorem lemma34_qmod_mk_eq_iff (hqE : ∀ n : ↥N, q n = 1 ↔ (n : G) ∈ E) (a b : ↥N) :
    q a = q b ↔ (a : G)⁻¹ * b ∈ E := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, hqE]
  rfl

omit [Finite G] in
private theorem lemma34_qmod_mem_push_iff (hqE : ∀ n : ↥N, q n = 1 ↔ (n : G) ∈ E) {S : Subgroup G}
    (hES : E ≤ S) (n : ↥N) : q n ∈ (S.subgroupOf N).map q ↔ (n : G) ∈ S := by
  constructor
  · rintro ⟨m, hm, hmn⟩
    have h1 := (lemma34_qmod_mk_eq_iff hqE m n).mp hmn
    have h2 : (n : G) = (m : G) * ((m : G)⁻¹ * n) := by group
    rw [h2]
    exact S.mul_mem hm (hES h1)
  · intro hn
    exact ⟨n, hn, rfl⟩

omit [Finite G] in
private theorem lemma34_qmod_card_push (hqE : ∀ n : ↥N, q n = 1 ↔ (n : G) ∈ E) {R : Subgroup G}
    (hRN : R ≤ N) : Nat.card ((R.subgroupOf N).map q) = E.relIndex R := by
  let φ : ↥R →* Y := q.comp (Subgroup.inclusion hRN)
  have hrange : φ.range = (R.subgroupOf N).map q := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = E.subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hqE (Subgroup.inclusion hRN r)
  rw [← hrange, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv.symm, hker]
  rfl

end Quotient

private theorem lemma34_transitive_of_fixedPointFree_elements (h : Tim79a.ParrottHyp z)
    {E : Subgroup G} (hE : IsParrottE z E)
    {σ₃ σ₅ : ↥(Subgroup.normalizer (E : Set G) ⊓ H z)} (h3 : orderOf σ₃ = 3)
    (h5 : orderOf σ₅ = 5)
    (f3 : ∀ r ∈ J z ⊔ E, (σ₃ : G) * r * (σ₃ : G)⁻¹ * r⁻¹ ∈ E → r ∈ E)
    (f5 : ∀ r ∈ J z ⊔ E, (σ₅ : G) * r * (σ₅ : G)⁻¹ * r⁻¹ ∈ E → r ∈ E) :
    ∀ r ∈ J z ⊔ E, ∀ s ∈ J z ⊔ E, r ∉ E → s ∉ E →
      ∃ g ∈ Subgroup.normalizer (E : Set G) ⊓ H z, g * r * g⁻¹ * s⁻¹ ∈ E := by
  have hJN := J_le_normalizer_of_isParrottE h hE
  have hRM : J z ⊔ E ≤ Subgroup.normalizer (E : Set G) ⊓ H z :=
    sup_le (le_inf hJN J_le_H) (le_inf Subgroup.le_normalizer hE.1)
  have hEM : E ≤ Subgroup.normalizer (E : Set G) ⊓ H z := le_sup_right.trans hRM
  have hMR : ∀ m ∈ Subgroup.normalizer (E : Set G) ⊓ H z, ∀ r ∈ J z ⊔ E,
      m * r * m⁻¹ ∈ J z ⊔ E := by
    have hJn : H z ≤ Subgroup.normalizer (J z : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer J_le_H).mp (J_subgroupOf_normal z)
    intro m hm r hr
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inf_normalizer_le_normalizer_sup (J z) E ⟨hJn hm.2, hm.1⟩) r).mp hr
  have hEnorm : (E.subgroupOf (Subgroup.normalizer (E : Set G) ⊓ H z)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEM).mpr inf_le_left
  obtain ⟨Q, instQ, instQf, q, hq, hqE⟩ : ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
      (q : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) →* Q), Function.Surjective q ∧
        ∀ n : ↥(Subgroup.normalizer (E : Set G) ⊓ H z), q n = 1 ↔ (n : G) ∈ E :=
    ⟨_, inferInstance, inferInstance, QuotientGroup.mk' (E.subgroupOf _),
      QuotientGroup.mk'_surjective _, fun n => by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        rfl⟩
  have hD'card : Nat.card (((J z ⊔ E).subgroupOf (Subgroup.normalizer (E : Set G) ⊓ H z)).map q) =
      16 := by
    rw [lemma34_qmod_card_push hqE hRM]
    exact relIndex_sup_J_of_isParrottE h hE
  have hDn : ∀ g : Q, ∀ d ∈ ((J z ⊔ E).subgroupOf (Subgroup.normalizer (E : Set G) ⊓ H z)).map q,
      g * d * g⁻¹ ∈ ((J z ⊔ E).subgroupOf (Subgroup.normalizer (E : Set G) ⊓ H z)).map q := by
    intro g d hd
    obtain ⟨m', rfl⟩ := hq g
    obtain ⟨m, hm, rfl⟩ := hd
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (lemma34_qmod_mem_push_iff hqE le_sup_right _).mpr (hMR _ m'.2 _ hm)
  have hfree : ∀ σ : ↥(Subgroup.normalizer (E : Set G) ⊓ H z),
      (∀ r ∈ J z ⊔ E, (σ : G) * r * (σ : G)⁻¹ * r⁻¹ ∈ E → r ∈ E) →
      ∀ d ∈ ((J z ⊔ E).subgroupOf (Subgroup.normalizer (E : Set G) ⊓ H z)).map q,
        q σ * d * (q σ)⁻¹ = d → d = 1 := by
    intro σ hσ d hd hfix
    obtain ⟨m, hm, rfl⟩ := hd
    have h1 : q (σ * m * σ⁻¹ * m⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hfix, mul_inv_cancel]
    have h2 : (σ : G) * m * (σ : G)⁻¹ * (m : G)⁻¹ ∈ E := (hqE _).mp h1
    exact (hqE m).mpr (hσ _ hm h2)
  have hord : ∀ (σ : ↥(Subgroup.normalizer (E : Set G) ⊓ H z)) (p : ℕ), p.Prime →
      Nat.Coprime p (2 ^ 10) → orderOf σ = p → orderOf (q σ) = p := by
    intro σ p hp hpc hσ
    have : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
    · intro h1
      have h2 : (σ : G) ∈ E := (hqE σ).mp h1
      have h3 : (σ : G) ^ p = 1 := by
        have := congrArg (fun x : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) => (x : G))
          (hσ ▸ pow_orderOf_eq_one σ : σ ^ p = 1)
        simpa using this
      have h4 := lemma34_eq_one_of_mem_of_card hE.2.2.2.2.1 h2 hpc h3
      have h5 : σ = 1 := Subtype.ext h4
      rw [h5, orderOf_one] at hσ
      exact absurd hσ.symm hp.one_lt.ne'
  have hT := lemma34_transitive_of_fixedPointFree hD'card hDn
    (hord σ₃ 3 Nat.prime_three (by norm_num) h3) (hord σ₅ 5 Nat.prime_five (by norm_num) h5)
    (hfree σ₃ f3) (hfree σ₅ f5)
  intro r hr s hs hrE hsE
  let r' : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) := ⟨r, hRM hr⟩
  let s' : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) := ⟨s, hRM hs⟩
  have hr1 : q r' ≠ 1 := fun h1 => hrE ((hqE r').mp h1)
  have hs1 : q s' ≠ 1 := fun h1 => hsE ((hqE s').mp h1)
  obtain ⟨g', hg'⟩ := hT (q r') ((lemma34_qmod_mem_push_iff hqE le_sup_right r').mpr hr) (q s')
    ((lemma34_qmod_mem_push_iff hqE le_sup_right s').mpr hs) hr1 hs1
  obtain ⟨m', rfl⟩ := hq g'
  refine ⟨(m' : G), m'.2, ?_⟩
  have h1 : q (m' * r' * m'⁻¹ * s'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg', mul_inv_cancel]
  exact (hqE _).mp h1


section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

include D

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

private theorem lemma34_exists_conj_rhoA (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    ∃ P : GL8, ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹ := by
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  exact ⟨P, fun a => by simpa [rhoA, toQAct] using hP a⟩

private theorem lemma34_exists_fixedPointFree_five (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {E : Subgroup G}
    (hE : IsParrottE z E) :
    ∃ σ : ↥(Subgroup.normalizer (E : Set G) ⊓ H z), orderOf σ = 5 ∧
      ∀ r ∈ J z ⊔ E, (σ : G) * r * (σ : G)⁻¹ * r⁻¹ ∈ E → r ∈ E := by
  obtain ⟨P, hP'⟩ := lemma34_exists_conj_rhoA D h hIII
  have hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0 :=
    fixDimV_eq_of_conj_rep D h rhoA P hP' (fun a => orderOf a = 5) 0
      (fun a ha => by simpa using spinFixedCard_five a ha)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ∣ Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓ H z) := by
    rw [lemma34_card_normalizer_inf_H hE]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer (E : Set G) ⊓ H z))
    5 h5
  refine ⟨σ, hσ, ?_⟩
  have hσ5 : σ ^ 5 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hσH5 : (⟨(σ : G), σ.2.2⟩ : ↥(H z)) ^ 5 = 1 := by
    apply Subtype.ext
    have := congrArg (fun x : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) => (x : G)) hσ5
    simpa using this
  have hq5 : orderOf (qH D ⟨(σ : G), σ.2.2⟩) = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hσH5, map_one]
    · intro h1
      have hJ1 : (σ : G) ∈ J z := Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
      have h2 : (σ : G) ^ 5 = 1 := by
        have := congrArg (fun x : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) => (x : G)) hσ5
        simpa using this
      have h3 := lemma34_eq_one_of_mem_of_card (card_J h) hJ1 (by norm_num) h2
      have h4 : σ = 1 := Subtype.ext h3
      rw [h4, orderOf_one] at hσ
      exact absurd hσ (by norm_num)
  exact lemma34_mem_of_commutator_mem h hE σ.2.1 (by decide) hσH5 (hV5 _ hq5)

private theorem lemma34_exists_fixedPointFree_three (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {E : Subgroup G}
    (hE : IsParrottE z E)
    (hweak : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
      ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) :
    ∃ σ : ↥(Subgroup.normalizer (E : Set G) ⊓ H z), orderOf σ = 3 ∧
      ∀ r ∈ J z ⊔ E, (σ : G) * r * (σ : G)⁻¹ * r⁻¹ ∈ E → r ∈ E := by
  obtain ⟨P, hP'⟩ := lemma34_exists_conj_rhoA D h hIII
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c, hS⟩ := lemma34_exists_conj_sQA45 D hE
  have hR0N : spinR0 ∈ Subgroup.normalizer (sQA45 : Set A45) := by
    have h3 : spinR0 ^ 3 = 1 := spinOddFact.1
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨spinNormFact k, fun hk => ?_⟩
    have h2 := spinNormFact _ (spinNormFact _ hk)
    have h3' : spinR0 * spinR0 * spinR0 = 1 := by rw [← pow_three']; exact h3
    have e : spinR0 * (spinR0 * (spinR0 * k * spinR0⁻¹) * spinR0⁻¹) * spinR0⁻¹ = k := by
      calc _ = (spinR0 * spinR0 * spinR0) * k * (spinR0 * spinR0 * spinR0)⁻¹ := by group
        _ = k := by rw [h3']; group
    rwa [e] at h2
  have ha : c⁻¹ * spinR0 * c ∈ Subgroup.normalizer (imageQA45 D hE.1 : Set A45) := by
    refine (lemma34_mem_normalizer_conj_iff hS).mpr ?_
    have : c * (c⁻¹ * spinR0 * c) * c⁻¹ = spinR0 := by group
    rwa [this]
  obtain ⟨m, hm⟩ := lemma34_exists_qH_eq_of_mem_normalizer D h hE hweak ha
  set mH : ↥(H z) := ⟨(m : G), m.2.2⟩ with hmH
  have ha3 : (c⁻¹ * spinR0 * c) ^ 3 = 1 := by
    have : (c⁻¹ * spinR0 * c) ^ 3 = c⁻¹ * spinR0 ^ 3 * c := by
      rw [pow_three, pow_three]
      group
    rw [this, spinOddFact.1]
    group
  have ha1 : c⁻¹ * spinR0 * c ≠ 1 := by
    intro h1
    apply spinOddFact.2.1
    have : spinR0 = c * (c⁻¹ * spinR0 * c) * c⁻¹ := by group
    rw [this, h1]
    group
  have hm3J : ((mH ^ 3 : ↥(H z)) : G) ∈ J z := by
    have : qH D (mH ^ 3) = 1 := by rw [map_pow]; exact hm ▸ ha3
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr this)
  have hσ3 : (mH ^ 2 ^ 10 : ↥(H z)) ^ 3 = 1 := by
    have h1 : (⟨((mH ^ 3 : ↥(H z)) : G), hm3J⟩ : ↥(J z)) ^ 2 ^ 10 = 1 := by
      rw [← card_J h]
      exact pow_card_eq_one'
    have h2 := congrArg (fun x : ↥(J z) => (x : G)) h1
    apply Subtype.ext
    simpa [← pow_mul, mul_comm] using h2
  have hqσ : qH D (mH ^ 2 ^ 10) = c⁻¹ * spinR0 * c := by
    rw [map_pow, hm]
    have : (2 : ℕ) ^ 10 = 3 * 341 + 1 := by norm_num
    rw [this, pow_succ, pow_mul, ha3, one_pow, one_mul]
  have hσ1 : (mH ^ 2 ^ 10 : ↥(H z)) ≠ 1 := fun h1 => ha1 (by rw [← hqσ, h1, map_one])
  have hord : orderOf (mH ^ 2 ^ 10 : ↥(H z)) = 3 := orderOf_eq_prime hσ3 hσ1
  have hfixdim : fixDimV h (mH ^ 2 ^ 10) = 0 := by
    have h1 := two_pow_fixDimV_eq_of_conj_rep D h rhoA P hP' (mH ^ 2 ^ 10)
    rw [hqσ, map_mul, map_mul, map_inv] at h1
    have h2 : fixCard (((rhoA c)⁻¹ * rhoA spinR0 * rhoA c : GL8) : Mat8) = 1 := by
      have := fixCard_conj (rhoA c)⁻¹ (rhoA spinR0)
      rw [inv_inv] at this
      rw [this, lemma34_fixCard_eq_fixedCount]
      exact spinOddFact.2.2.2
    rw [h2] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.trans (pow_zero 2).symm)
  have hmem : ((m ^ 2 ^ 10 : ↥(Subgroup.normalizer (E : Set G) ⊓ H z)) : G) ∈
      Subgroup.normalizer (E : Set G) := (m ^ 2 ^ 10).2.1
  refine ⟨m ^ 2 ^ 10, ?_, ?_⟩
  · have hσ3M : (m ^ 2 ^ 10 : ↥(Subgroup.normalizer (E : Set G) ⊓ H z)) ^ 3 = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hσ3
      simpa using this
    have hσ1M : (m ^ 2 ^ 10 : ↥(Subgroup.normalizer (E : Set G) ⊓ H z)) ≠ 1 := by
      intro h1
      apply hσ1
      apply Subtype.ext
      have := congrArg Subtype.val h1
      simpa using this
    exact orderOf_eq_prime hσ3M hσ1M
  · exact lemma34_mem_of_commutator_mem h hE (σ := mH ^ 2 ^ 10) hmem (by decide)
      hσ3 hfixdim

theorem transitive_on_J_sup_of_isParrottE (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {E : Subgroup G}
    (hE : IsParrottE z E)
    (hweak : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
      ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) :
    ∀ r ∈ J z ⊔ E, ∀ s ∈ J z ⊔ E, r ∉ E → s ∉ E →
      ∃ g ∈ Subgroup.normalizer (E : Set G) ⊓ H z, g * r * g⁻¹ * s⁻¹ ∈ E := by
  obtain ⟨σ₅, h5, f5⟩ := lemma34_exists_fixedPointFree_five D h hIII hE
  obtain ⟨σ₃, h3, f3⟩ := lemma34_exists_fixedPointFree_three D h hIII hE hweak
  exact lemma34_transitive_of_fixedPointFree_elements h hE h3 h5 f3 f5

theorem hB6_of_lemma34 (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    ∀ E : Subgroup G, IsParrottE z E →
      (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
        ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) →
      (∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j) →
      (∃ e ∈ E, e ≠ z ∧ ∃ n ∈ Subgroup.normalizer (E : Set G), n * z * n⁻¹ = e) →
      ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (Subgroup.normalizer (E : Set G)) = 2 ∧
        ¬ (Subgroup.normalizer (E : Set G) ⊓ H z ≤ K) ∧
        (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
          ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2 := by
  intro E hE hweak hJ hfus
  have hJN : J z ≤ Subgroup.normalizer (E : Set G) := J_le_normalizer_of_isParrottE h hE
  obtain ⟨K, hEK, hKi, hKM, hKq, -, -⟩ := lemma34_generic z E (J z ⊔ E)
    (Subgroup.normalizer (E : Set G) ⊓ H z) rfl hE.2.2.2.1 le_sup_right
    (sup_le (le_inf hJN J_le_H) (le_inf Subgroup.le_normalizer hE.1))
    (relIndex_sup_J_of_isParrottE h hE)
    (fun r hr s hs => commutator_mem_of_mem_J_sup h hE hr hs)
    (fun r hr => mul_self_mem_of_mem_J_sup h hE hr)
    (exists_perm_five_of_isParrottE D h hE hweak)
    (transitive_on_J_sup_of_isParrottE D h hIII hE hweak)
    (fun r hr hrE => exists_commutator_eq_z h hE hr hrE)
    (fun r hr e he hc => commutator_eq_z_of_isConj h hE hJ hr he hc)
    (odd_relIndex_of_isParrottE D h hZ hE) hfus
  exact ⟨K, hEK, hKi, hKM, hKq⟩

omit D

end Certified

end CFSG.RankThree.GF2n.Parrott

module

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Sec21.PairExistence

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open (GLBStronglyEmbedded GLBConj)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

theorem mem_map_conj_iff {X : Subgroup G} {g x : G} :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem lt_inf_normalizer_of_lt [Finite G] {p : ℕ} [Fact p.Prime] {X R : Subgroup G}
    (hR : IsPGroup p R) (hXR : X < R) : X < R ⊓ Subgroup.normalizer (X : Set G) := by
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hlt : X.subgroupOf R < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    apply (lt_iff_le_not_ge.mp hXR).2
    intro r hr
    have : (⟨r, hr⟩ : R) ∈ X.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨r, hrN, hrX⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine lt_of_le_of_ne (le_inf hXR.le Subgroup.le_normalizer) fun heq => hrX ?_
  have hrG : (r : G) ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 : (⟨y, hXR.le hy⟩ : R) ∈ X.subgroupOf R := Subgroup.mem_subgroupOf.mpr hy
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hrN _).mp h1)
    · intro hy
      have hyR : y ∈ R := by
        have h1 : (r : G)⁻¹ * ((r : G) * y * (r : G)⁻¹) * (r : G) = y := by group
        rw [← h1]
        exact R.mul_mem (R.mul_mem (R.inv_mem r.2) (hXR.le hy)) r.2
      have h1 : r * (⟨y, hyR⟩ : R) * r⁻¹ ∈ X.subgroupOf R := Subgroup.mem_subgroupOf.mpr hy
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hrN _).mpr h1)
  have : (r : G) ∈ X := by
    rw [heq]
    exact ⟨r.2, hrG⟩
  exact Subgroup.mem_subgroupOf.mpr this

theorem mem_of_map_conj_le [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (h : ∀ X : Subgroup G, X ≤ M → IsPGroup p X → X ≠ ⊥ →
      Subgroup.normalizer (X : Set G) ≤ M) {X : Subgroup G} (hXM : X ≤ M) (hX : IsPGroup p X)
    (hX1 : X ≠ ⊥) {g : G} (hg : X.map (MulAut.conj g).toMonoidHom ≤ M) : g ∈ M := by
  induction hn : Nat.card M - Nat.card X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  by_cases hmax : ∃ R : Subgroup G, R ≤ M ∧ IsPGroup p R ∧ X < R
  · obtain ⟨R, hRM, hR, hXR⟩ := hmax
    have hXY := lt_inf_normalizer_of_lt hR hXR
    set Y := R ⊓ Subgroup.normalizer (X : Set G)
    have hYM : Y ≤ M := inf_le_left.trans hRM
    have hY : IsPGroup p Y := hR.to_le inf_le_left
    have hY1 : Y ≠ ⊥ := fun h' => hX1 (eq_bot_iff.mpr (h' ▸ hXY.le))
    have hgY : Y.map (MulAut.conj g).toMonoidHom ≤ M := by
      have h1 : Y.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
        rw [← Subgroup.map_equiv_normalizer_eq X (MulAut.conj g)]
        exact Subgroup.map_mono inf_le_right
      refine h1.trans (h _ hg (hX.map _) ?_)
      intro hb
      exact hX1 ((Subgroup.map_eq_bot_iff_of_injective X (MulAut.conj g).injective).mp hb)
    have hcard : Nat.card X < Nat.card Y := Subgroup.card_lt_of_lt hXY
    have hcardY : Nat.card Y ≤ Nat.card M := Subgroup.card_le_of_le hYM
    exact ih _ (by omega) hYM hY hY1 hgY rfl
  · push Not at hmax
    have hmaxM : ∀ {Q : Subgroup M}, IsPGroup p Q → X.subgroupOf M ≤ Q →
        Q = X.subgroupOf M := by
      intro Q hQ hXQ
      have hXQ' : X ≤ Q.map M.subtype := by
        intro x hx
        exact ⟨⟨x, hXM hx⟩, hXQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
      have heq : X = Q.map M.subtype := by
        by_contra hne
        exact hmax _ (Subgroup.map_subtype_le Q) (hQ.map M.subtype) (lt_of_le_of_ne hXQ' hne)
      ext y
      rw [Subgroup.mem_subgroupOf, heq]
      simp
    let S1 : Sylow p M := ⟨X.subgroupOf M, hX.comap_subtype, hmaxM⟩
    have hcard1 : Nat.card (X.subgroupOf M) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
    set Xg := X.map (MulAut.conj g).toMonoidHom
    have hcard2 : Nat.card (Xg.subgroupOf M) = Nat.card X := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv]
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hS1card := S1.card_eq_multiplicity
    let S2 : Sylow p M := Sylow.ofCard (Xg.subgroupOf M) (by
      rw [hcard2, ← hcard1]; exact hS1card)
    obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M S1 S2
    have key : ∀ x ∈ X, (m : G)⁻¹ * g * x * ((m : G)⁻¹ * g)⁻¹ ∈ X := by
      intro x hx
      have hxg : g * x * g⁻¹ ∈ Xg := mem_map_conj_iff.mpr (by simpa [mul_assoc] using hx)
      have h2 : (⟨g * x * g⁻¹, hg hxg⟩ : M) ∈ (S2 : Subgroup M) := by
        show _ ∈ Xg.subgroupOf M
        exact Subgroup.mem_subgroupOf.mpr hxg
      rw [← hm, Sylow.smul_def, Sylow.pointwise_smul_def,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
      have h3 := Subgroup.mem_subgroupOf.mp h2
      simpa [MulAut.conj_apply, mul_assoc] using h3
    have hnorm : (m : G)⁻¹ * g ∈ Subgroup.normalizer (X : Set G) := by
      set k := (m : G)⁻¹ * g
      have hle : X.map (MulAut.conj k).toMonoidHom ≤ X := by
        rintro _ ⟨x, hx, rfl⟩
        simpa [MulAut.conj_apply] using key x hx
      exact mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj k).injective).symm))
    have := M.mul_mem m.2 (h X hXM hX hX1 hnorm)
    simpa using this

theorem glbStronglyEmbedded_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} (hM : M ≠ ⊤) (hpM : p ∣ Nat.card M)
    (h : ∀ X : Subgroup G, X ≤ M → IsPGroup p X → X ≠ ⊥ →
      Subgroup.normalizer (X : Set G) ≤ M) : GLBStronglyEmbedded p M := by
  refine ⟨hM, hpM, fun g hg hdvd => hg ?_⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (M ⊓ GLBConj g M : Subgroup G)) p hdvd
  set X := Subgroup.zpowers (x : G)
  have hxM : (x : G) ∈ M := x.2.1
  have hxg : g * x * g⁻¹ ∈ M := mem_glbConj_iff.mp x.2.2
  have hXM : X ≤ M := (Subgroup.zpowers_le).mpr hxM
  have hord : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hX : IsPGroup p X := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro hb
    rw [Subgroup.zpowers_eq_bot.mp hb, orderOf_one] at hord
    exact (Fact.out : p.Prime).one_lt.ne hord
  apply mem_of_map_conj_le h hXM hX hX1
  rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
  simpa [MulAut.conj_apply] using hxg

@[expose] def omegaOneCenterOf (p : ℕ) (X : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ X ∧ z ∈ Subgroup.centralizer (X : Set G) ∧ z ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haX, haC, hap⟩ ⟨hbX, hbC, hbp⟩
    refine ⟨X.mul_mem haX hbX, Subgroup.mul_mem _ haC hbC, ?_⟩
    have hcomm : Commute a b := (Subgroup.mem_centralizer_iff.mp hbC) a haX
    rw [hcomm.mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haX, haC, hap⟩
    exact ⟨X.inv_mem haX, Subgroup.inv_mem _ haC, by rw [inv_pow, hap, inv_one]⟩

theorem omegaOneCenterOf_le (p : ℕ) (X : Subgroup G) : omegaOneCenterOf p X ≤ X :=
  fun _ h => h.1

theorem isElemAbelian_omegaOneCenterOf (p : ℕ) (X : Subgroup G) :
    IsElemAbelian p (omegaOneCenterOf p X) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2.2⟩
  exact Subgroup.mem_centralizer_iff.mp b.2.2.1 a a.2.1

theorem omegaOneCenterOf_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) : omegaOneCenterOf p X ≠ ⊥ := by
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hZ : Nontrivial (Subgroup.center X) := hX.center_nontrivial
  have hdvd : p ∣ Nat.card (Subgroup.center X) := by
    obtain ⟨k, hk⟩ := (hX.to_subgroup (Subgroup.center X)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center X) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h1
      exact lt_irrefl 1 h1
    exact dvd_pow_self p hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) p hdvd
  intro h
  have hmem : (((z : Subgroup.center X) : X) : G) ∈ omegaOneCenterOf p X := by
    refine ⟨(z : X).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
    · have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      have h2 := congrArg (fun w : Subgroup.center X => ((w : X) : G)) h1
      simpa using h2
  rw [h, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact (Fact.out : p.Prime).one_lt.ne hz

theorem normalizer_le_normalizer_omegaOneCenterOf (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (omegaOneCenterOf p X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ z ∈ omegaOneCenterOf p X,
      g * z * g⁻¹ ∈ omegaOneCenterOf p X := by
    rintro g hg z ⟨hzX, hzC, hzp⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzX, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hzC ⊢
      intro y hy
      have hy' : g⁻¹ * y * g ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
        simpa using this
      have := hzC _ hy'
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = g * z * g⁻¹ * y := by group
    · rw [conj_pow, hzp, mul_one, mul_inv_cancel]
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key h hh z, fun hz => ?_⟩
  have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hz
  simpa [mul_assoc] using this

theorem glbStronglyEmbedded_of_elemAbelian [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ≠ ⊤) (hpM : p ∣ Nat.card M) (S : Sylow p M)
    (h : ∀ B : Subgroup G, B ≤ (S : Subgroup M).map M.subtype → IsElemAbelian p B → B ≠ ⊥ →
      Subgroup.normalizer (B : Set G) ≤ M) : GLBStronglyEmbedded p M := by
  refine glbStronglyEmbedded_of_normalizer_le hM hpM fun X hXM hX hX1 => ?_
  obtain ⟨S', hS'⟩ := (hX.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M S' S
  set X' := X.map (MulAut.conj (m : G)).toMonoidHom
  have hX'S : X' ≤ (S : Subgroup M).map M.subtype := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (⟨x, hXM hx⟩ : M) ∈ (S' : Subgroup M) := hS' (Subgroup.mem_subgroupOf.mpr hx)
    have h2 : m * ⟨x, hXM hx⟩ * m⁻¹ ∈ (S : Subgroup M) := by
      rw [← hm, Sylow.smul_def, Sylow.pointwise_smul_def,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [mul_assoc] using h1
    exact ⟨_, h2, by simp [MulAut.conj_apply]⟩
  have hX'1 : X' ≠ ⊥ := fun hb =>
    hX1 ((Subgroup.map_eq_bot_iff_of_injective X (MulAut.conj (m : G)).injective).mp hb)
  have hX'p : IsPGroup p X' := hX.map _
  set B := omegaOneCenterOf p X'
  have hBN : Subgroup.normalizer (X' : Set G) ≤ M :=
    (normalizer_le_normalizer_omegaOneCenterOf p X').trans
      (h B ((omegaOneCenterOf_le p X').trans hX'S) (isElemAbelian_omegaOneCenterOf p X')
        (omegaOneCenterOf_ne_bot hX'p hX'1))
  intro y hy
  have hy' : (m : G) * y * (m : G)⁻¹ ∈ Subgroup.normalizer (X' : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq X (MulAut.conj (m : G))]
    exact ⟨y, hy, rfl⟩
  have := M.mul_mem (M.mul_mem (M.inv_mem m.2) (hBN hy')) m.2
  simpa [mul_assoc] using this

theorem isElemAbelian_map {H : Type*} [Group H] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (f : G →* H) : IsElemAbelian p (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    (K : Subgroup G) : IsElemAbelian p (E.subgroupOf K) := CFSG.Open.IsElemAbelian.subgroupOf hE K

theorem isElementaryAbelian_of_isElemAbelian {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) :
    CFSG.IsElementaryAbelian p E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h

theorem isPGroup_of_isElementaryAbelian {p : ℕ} {E : Subgroup G}
    (hE : CFSG.IsElementaryAbelian p E) : IsPGroup p E := fun x =>
  ⟨1, by rw [pow_one]; exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p x⟩

theorem pRank_set_bddAbove [Finite G] (p : ℕ) (hp : 1 < p) :
    BddAbove {r : ℕ | ∃ A : Subgroup G, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ r} := by
  refine ⟨Nat.card G, ?_⟩
  rintro r ⟨A, -, hA⟩
  have h1 : r < p ^ r := Nat.lt_pow_self hp
  have h2 : Nat.card A ≤ Nat.card G := Subgroup.card_le_card_group A
  omega

theorem pRank_mem [Finite G] (p : ℕ) [hp : Fact p.Prime] :
    CFSG.pRank p G ∈
      {r : ℕ | ∃ A : Subgroup G, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ r} := by
  apply Nat.sSup_mem _ (pRank_set_bddAbove p hp.out.one_lt)
  refine ⟨0, ⊥, ?_, by simp⟩
  exact { toIsMulCommutative := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subsingleton.elim _ _ }

theorem card_le_pow_pRank [Finite G] {p : ℕ} [hp : Fact p.Prime] {E : Subgroup G}
    (hE : CFSG.IsElementaryAbelian p E) : Nat.card E ≤ p ^ CFSG.pRank p G := by
  obtain ⟨s, hs⟩ := (isPGroup_of_isElementaryAbelian hE).exists_card_eq
  have hs' : s ≤ CFSG.pRank p G := le_csSup (pRank_set_bddAbove p hp.out.one_lt) ⟨E, hE, hs⟩
  rw [hs]
  exact Nat.pow_le_pow_right hp.out.pos hs'

theorem isElementaryAbelian_map {X Y : Type*} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    {E : Subgroup X} (h : CFSG.IsElementaryAbelian p E) :
    CFSG.IsElementaryAbelian p (E.map f) := CFSG.IsElementaryAbelian.subgroup_map h _

theorem pRank_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y) :
    CFSG.pRank p X = CFSG.pRank p Y := CFSG.pRank_congr_of_mulEquiv e p

theorem elemThompson_map_mulEquiv {X Y : Type*} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y) :
    (CFSG.elemThompson X p).map e.toMonoidHom = CFSG.elemThompson Y p := by
  unfold CFSG.elemThompson
  rw [(Subgroup.gc_map_comap e.toMonoidHom).l_sSup]
  apply le_antisymm
  · refine iSup₂_le fun A hA => le_sSup ?_
    refine ⟨isElementaryAbelian_map _ hA.1, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective, hA.2, pRank_eq_of_mulEquiv e]
  · refine sSup_le fun B hB => ?_
    have hB' : B.map e.symm.toMonoidHom ∈ CFSG.elemThompsonFamily X p := by
      refine ⟨isElementaryAbelian_map _ hB.1, ?_⟩
      rw [Subgroup.card_map_of_injective e.symm.injective, hB.2, pRank_eq_of_mulEquiv e]
    have : B = (B.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map]
      conv_lhs => rw [← Subgroup.map_id B]
      congr 1
      ext x
      simp
    rw [this]
    exact le_iSup₂_of_le
      (f := fun A (_ : A ∈ CFSG.elemThompsonFamily X p) => A.map e.toMonoidHom) _ hB' le_rfl

theorem map_elemThompson_map_subtype {I : Subgroup G} (Q : Subgroup I) (p : ℕ) :
    (CFSG.elemThompson (Q.map I.subtype) p).map (Q.map I.subtype).subtype =
      ((CFSG.elemThompson Q p).map Q.subtype).map I.subtype := by
  rw [← elemThompson_map_mulEquiv (Q.equivMapOfInjective I.subtype I.subtype_injective),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem eq_elemThompson_of_card_le [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hJ : CFSG.IsElementaryAbelian p (CFSG.elemThompson G p)) {E : Subgroup G}
    (hE : CFSG.IsElementaryAbelian p E) (hcard : Nat.card (CFSG.elemThompson G p) ≤ Nat.card E) :
    E = CFSG.elemThompson G p := by
  obtain ⟨E0, hE0, hE0c⟩ := pRank_mem (G := G) p
  have hE0J : E0 ≤ CFSG.elemThompson G p := le_sSup ⟨hE0, hE0c⟩
  have hJc : Nat.card (CFSG.elemThompson G p) = p ^ CFSG.pRank p G :=
    le_antisymm (card_le_pow_pRank hJ) (hE0c ▸ Subgroup.card_le_of_le hE0J)
  have hEc : Nat.card E = p ^ CFSG.pRank p G :=
    le_antisymm (card_le_pow_pRank hE) (hJc ▸ hcard)
  have hEJ : E ≤ CFSG.elemThompson G p := le_sSup ⟨hE, hEc⟩
  exact Subgroup.eq_of_le_of_card_ge hEJ (hJc ▸ hEc ▸ le_rfl)

theorem unique_of_elemThompson_eq [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    {A : Subgroup G} (hAe : IsElemAbelian p A)
    (hJ : (CFSG.elemThompson (P : Subgroup G) p).map (P : Subgroup G).subtype = A) :
    ∀ (S : Sylow p G) (B : Subgroup G), A ≤ S → B ≤ S → IsElemAbelian p B →
      Nat.card A ≤ Nat.card B → B = A := by
  intro S B hAS hBS hBe hcard
  set P' := (P : Subgroup G)
  have hJcard : Nat.card (CFSG.elemThompson P' p) = Nat.card A := by
    rw [← hJ]; exact (Subgroup.card_map_of_injective P'.subtype_injective).symm
  have hJe : CFSG.IsElementaryAbelian p (CFSG.elemThompson P' p) := by
    have hJe' : IsElemAbelian p ((CFSG.elemThompson P' p).map P'.subtype) := hJ ▸ hAe
    refine isElementaryAbelian_of_isElemAbelian ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩,
      fun x hx => Subtype.ext ?_⟩
    · have := congrArg Subtype.val (hJe'.1.is_comm.comm ⟨((a : P') : G), a, a.2, rfl⟩
        ⟨((b : P') : G), b, b.2, rfl⟩)
      simpa using this
    · simpa using hJe'.2 _ ⟨x, hx, rfl⟩
  have key : ∀ C : Subgroup G, C ≤ P' → IsElemAbelian p C → Nat.card A ≤ Nat.card C →
      C = A := by
    intro C hCP hCe hCc
    have hCcard : Nat.card (C.subgroupOf P') = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv
    have h1 := eq_elemThompson_of_card_le hJe
      (isElementaryAbelian_of_isElemAbelian (isElemAbelian_subgroupOf hCe P'))
      (by rw [hJcard, hCcard]; exact hCc)
    rw [← hJ, ← h1, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCP]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hSP : ∀ x ∈ (S : Subgroup G), g * x * g⁻¹ ∈ P' := by
    intro x hx
    have : g * x * g⁻¹ ∈ ((g • S : Sylow p G) : Subgroup G) := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [mul_assoc] using hx
    rwa [hg] at this
  have hmapS : ∀ C : Subgroup G, C ≤ S → C.map (MulAut.conj g).toMonoidHom ≤ P' := by
    rintro C hC _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hSP x (hC hx)
  have hcardmap : ∀ C : Subgroup G,
      Nat.card (C.map (MulAut.conj g).toMonoidHom) = Nat.card C :=
    fun C => Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hA' := key _ (hmapS A hAS) (isElemAbelian_map hAe _) (by rw [hcardmap])
  have hB' := key _ (hmapS B hBS) (isElemAbelian_map hBe _) (by rw [hcardmap]; exact hcard)
  exact Subgroup.map_injective (MulAut.conj g).injective (hB'.trans hA'.symm)

theorem exists_mem_mul_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAe : IsElemAbelian p A)
    (huniq : ∀ (S : Sylow p G) (B : Subgroup G), A ≤ S → B ≤ S → IsElemAbelian p B →
      Nat.card A ≤ Nat.card B → B = A)
    {H K : Subgroup G} (hAK : A ≤ K) (hK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) {h : G}
    (hh : h ∈ H) : ∃ k ∈ K, k⁻¹ * h ∈ Subgroup.normalizer (A : Set G) := by
  have hAp : IsPGroup p A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  set A' := A.map (MulAut.conj h).toMonoidHom
  have hA'K : A' ≤ K := by
    rintro _ ⟨a, ha, rfl⟩
    exact hK h hh a (hAK ha)
  obtain ⟨Q, hQ⟩ := (hAp.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨Q', hQ'⟩ :=
    ((hAp.map (MulAut.conj h).toMonoidHom).comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨k, k.2, ?_⟩
  obtain ⟨S, hS⟩ := (Q.isPGroup'.map K.subtype).exists_le_sylow
  have hAS : A ≤ S := fun a ha =>
    hS ⟨⟨a, hAK ha⟩, hQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  set c := (k : G)⁻¹ * h
  set B := A.map (MulAut.conj c).toMonoidHom
  have hBS : B ≤ S := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : h * a * h⁻¹ ∈ A' := ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have h2 : (⟨h * a * h⁻¹, hA'K h1⟩ : K) ∈ (Q' : Subgroup K) :=
      hQ' (Subgroup.mem_subgroupOf.mpr h1)
    rw [← hk, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
    refine hS ⟨_, h2, ?_⟩
    simp [MulAut.conj_apply, c, mul_assoc]
  have hcard : Nat.card A ≤ Nat.card B :=
    le_of_eq (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm
  exact mem_normalizer_of_map_conj_eq (huniq S B hAS hBS (isElemAbelian_map hAe _) hcard)

theorem normalizer_le_of_centralizer_le [Finite G] {p : ℕ} [Fact p.Prime] {A B M : Subgroup G}
    (hAe : IsElemAbelian p A)
    (huniq : ∀ (S : Sylow p G) (C : Subgroup G), A ≤ S → C ≤ S → IsElemAbelian p C →
      Nat.card A ≤ Nat.card C → C = A)
    (hBA : B ≤ A) (hC : Subgroup.centralizer (B : Set G) ≤ M)
    (hW : Subgroup.normalizer (A : Set G) ≤ M) : Subgroup.normalizer (B : Set G) ≤ M := by
  have hAC : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨b, hBA hb⟩ ⟨a, ha⟩)
  have hK : ∀ h ∈ Subgroup.normalizer (B : Set G), ∀ k ∈ Subgroup.centralizer (B : Set G),
      h * k * h⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
    intro h hh k hk
    rw [Subgroup.mem_centralizer_iff] at hk ⊢
    intro b hb
    have hb' : h⁻¹ * b * h ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) b).mp hb
      simpa using this
    have := hk _ hb'
    calc b * (h * k * h⁻¹) = h * ((h⁻¹ * b * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * b * h)) * h⁻¹ := by rw [this]
      _ = h * k * h⁻¹ * b := by group
  intro h hh
  obtain ⟨k, hk, hkn⟩ := exists_mem_mul_normalizer hAe huniq hAC hK hh
  have := M.mul_mem (hC hk) (hW hkn)
  simpa using this

end CFSG.RankThree.PartTwo.Sec21

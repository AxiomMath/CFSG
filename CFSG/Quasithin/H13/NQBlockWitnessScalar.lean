module

public import CFSG.Quasithin.H13.NQBlockRadicalWitnessProduct
public import CFSG.Quasithin.H13.NQTermCharNormalizerResidual
public import CFSG.Quasithin.H13.NQRigidCoreQuot
public import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniFoundations

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj normalizerCoreQuotConj)

section Abstract

theorem scalar_of_commute_noncomm {p : ℕ} [Fact p.Prime] {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1) (hcard : Nat.card W = p ^ 2)
    {J : Set (MulAut W)} (hJ : ∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a) {γ : MulAut W}
    (hγ : ∀ j ∈ J, γ * j = j * γ) :
    (∃ c : ZMod p, ∀ w, γ w = w ^ c.val) ∧ (γ ^ 2 = 1 → γ = 1 ∨ ∀ w, γ w = w⁻¹) := by
  classical
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hcard
  set φ := CFSG.SectionRank.Ccomm.elemAutEquivGL e with hφ
  have hsc : ∃ c : ZMod p,
      ((φ γ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = c • 1 := by
    by_contra hns
    obtain ⟨a, ha, b, hb, hab⟩ := hJ
    apply hab
    have h1 : ((φ γ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        ((φ a : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        ((φ a : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          ((φ γ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [← Units.val_mul, ← map_mul, hγ a ha, map_mul, Units.val_mul]
    have h2 : ((φ γ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        ((φ b : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        ((φ b : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          ((φ γ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [← Units.val_mul, ← map_mul, hγ b hb, map_mul, Units.val_mul]
    have h3 := CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hns h1 h2
    apply φ.injective
    rw [map_mul, map_mul]
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h3)
  obtain ⟨c, hc⟩ := hsc
  have happ : ∀ w, Multiplicative.toAdd (e (γ w)) = c • Multiplicative.toAdd (e w) := by
    intro w
    rw [← CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e γ w, ← hφ, hc,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨⟨c, fun w => ?_⟩, fun h2 => ?_⟩
  · apply e.injective
    apply Multiplicative.toAdd.injective
    rw [happ, map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  · have hcc : c ^ 2 = 1 := by
      have h1 := congrArg (fun g => ((φ g : GL (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) h2
      simp only [pow_two, map_mul, Units.val_mul, map_one, Units.val_one, hc] at h1
      have h00 := congrFun (congrFun h1 0) 0
      simp [Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply] at h00
      rw [pow_two]
      exact h00
    rcases CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq hcc with h1 | h1
    · left
      ext w
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [happ, h1, one_smul]
      rfl
    · right
      intro w
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [happ, h1, map_inv, toAdd_inv]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      exact neg_one_mul _

theorem commute_of_conj_central {Γ : Type*} [Group Γ] {J : Subgroup Γ} [Group.IsPerfect J]
    {γ : Γ} (hγJ : ∀ j ∈ J, γ * j * γ⁻¹ ∈ J)
    (hc : ∀ j ∈ J, ∀ k ∈ J, (j⁻¹ * (γ * j * γ⁻¹)) * k = k * (j⁻¹ * (γ * j * γ⁻¹))) :
    ∀ j ∈ J, γ * j = j * γ := by
  let f : ↥J →* ↥J :=
    ((MulAut.conj γ).toMonoidHom.comp J.subtype).codRestrict J (fun j => hγJ j j.2)
  have hf := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement f
    (fun j => by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact (hc j j.2 k k.2).symm)
  intro j hj
  have h1 := congrArg (fun φ : ↥J →* ↥J => ((φ ⟨j, hj⟩ : ↥J) : Γ)) hf
  change γ * j * γ⁻¹ = j at h1
  calc γ * j = γ * j * γ⁻¹ * γ := by group
    _ = j * γ := by rw [h1]

theorem exists_noncomm_of_perfect {Q : Type*} [Group Q] [Group.IsPerfect Q] [Nontrivial Q] :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  have h1 : commutator Q = ⊥ := by
    rw [commutator_eq_closure, eq_bot_iff, closure_le]
    rintro _ ⟨a, b, rfl⟩
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc a b)
  rw [Group.IsPerfect.commutator_eq_top] at h1
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  exact hx (by simpa using (h1 ▸ mem_top x : x ∈ (⊥ : Subgroup Q)))

theorem subsingleton_of_perfect_solvable {Q : Type*} [Group Q] [Group.IsPerfect Q]
    [Group.IsSolvable Q] : Subsingleton Q := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def Q).mp inferInstance
  have h : ∀ k, derivedSeries Q k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, Group.IsPerfect.commutator_eq_top]
  rw [h n] at hn
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Subgroup Q) := hn ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup Q) := hn ▸ mem_top b
  rw [mem_bot] at ha hb
  rw [ha, hb]

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem frattini_pow_prime {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X))
    (w : (↥X ⧸ CFSG.pCore 2 ↥X) ⧸ frattini (↥X ⧸ CFSG.pCore 2 ↥X)) : w ^ p = 1 := by
  have : Fact (IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X)) := ⟨hXA⟩
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective _ w
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact CFSG.pth_power_mem_frattini_of_isPGroup r

theorem frattini_comm {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X))
    (a b : (↥X ⧸ CFSG.pCore 2 ↥X) ⧸ frattini (↥X ⧸ CFSG.pCore 2 ↥X)) : a * b = b * a := by
  have := CFSG.RankThreeEvenClassification.Helpers.pGroup_frattini_quotient_commutative p hp hXA
  exact mul_comm' a b

theorem witness_R_scalar {T L M : Subgroup G} (h : QTNQ T L M)
    {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {X : Subgroup G} (hXN : X ≤ (CFSG.solvableRadical ↥L).map L.subtype)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X))
    (hW : Nat.card ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ frattini (↥X ⧸ CFSG.pCore 2 ↥X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (r : normalizer (X : Set G)) (hr : (r : G) ∈ R) :
    (∃ c : ZMod p, ∀ w, normalizerFrattiniConj X r w = w ^ c.val) ∧
      (normalizerFrattiniConj X r ^ 2 = 1 →
        normalizerFrattiniConj X r = 1 ∨ ∀ w, normalizerFrattiniConj X r w = w⁻¹) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hMX := (radical_witness_product h hR hp hp5 hXN hXc hXA).1
  have hLX : L ≤ normalizer (X : Set G) := h.l_le.trans hMX
  set β := normalizerFrattiniConj X with hβdef
  set βL := β.comp (Subgroup.inclusion hLX) with hβLdef
  set J := βL.range with hJdef
  have hLp : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.maximal_local.1.2.1.2.1
  have hJp : Group.IsPerfect ↥J := Group.IsPerfect.range βL
  have hJ1 : J ≠ ⊥ := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro h0
    apply hl1
    have h1 : βL ⟨l, hlL⟩ ∈ J := ⟨_, rfl⟩
    rw [h0, mem_bot] at h1
    exact h1
  have hcommW := frattini_comm hp hXA
  have hpowW := frattini_pow_prime hXA
  have hJq : CFSG.IsQuasisimple ↥J :=
    NQTerm.isQuasisimple_of_le_mulAut_plane (by omega) hcommW hpowW hW J hJ1
  have hJnt : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  obtain ⟨-, hNs, -, -⟩ := CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization ↥L
  have hNn : (CFSG.solvableRadical ↥L).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  set NJ : Subgroup ↥J := (CFSG.solvableRadical ↥L).map βL.rangeRestrict with hNJdef
  have hNJn : NJ.Normal := Subgroup.Normal.map hNn _ βL.rangeRestrict_surjective
  have hNJc : NJ ≤ center ↥J := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hJq hNJn with h1 | h1
    · exfalso
      have hJs : Group.IsSolvable ↥J := by
        have : Group.IsSolvable ↥NJ := by
          have := hNs
          exact Group.isSolvable_of_surjective (f := βL.rangeRestrict.subgroupMap _)
            (MonoidHom.subgroupMap_surjective _ _)
        have hJN : Function.Surjective (NJ.subtype) := by
          intro j
          have hj : j ∈ NJ := by rw [h1]; exact mem_top j
          exact ⟨⟨j, hj⟩, rfl⟩
        exact Group.isSolvable_of_surjective hJN
      have := subsingleton_of_perfect_solvable (Q := ↥J)
      exact not_subsingleton ↥J this
    · exact h1
  have hr' : (r : G) ∈ nqOriginalCentralizer T L := by
    rw [← hR]
    exact hr
  have hrM : (r : G) ∈ M := h.t_le hr'.1
  have hrL : (r : G) ∈ normalizer (L : Set G) := h.eq_normalizer ▸ hrM
  have hγJ : ∀ j ∈ J, β r * j * (β r)⁻¹ ∈ J := by
    rintro _ ⟨l, rfl⟩
    refine ⟨⟨r * l * (r : G)⁻¹, (mem_normalizer_iff.mp hrL l).mp l.2⟩, ?_⟩
    have e : Subgroup.inclusion hLX ⟨r * l * (r : G)⁻¹, (mem_normalizer_iff.mp hrL l).mp l.2⟩ =
        r * Subgroup.inclusion hLX l * r⁻¹ := Subtype.ext rfl
    rw [hβLdef, MonoidHom.comp_apply, e, map_mul, map_mul, map_inv]
    rfl
  have hc : ∀ j ∈ J, ∀ k ∈ J,
      (j⁻¹ * (β r * j * (β r)⁻¹)) * k = k * (j⁻¹ * (β r * j * (β r)⁻¹)) := by
    rintro _ ⟨l, rfl⟩ k hk
    have hn : (l : G)⁻¹ * r * l * (r : G)⁻¹ ∈ (CFSG.solvableRadical ↥L).map L.subtype := by
      have h1 := hr'.2 (l : G)⁻¹ (L.inv_mem l.2)
      have e : (l : G)⁻¹ * r * l * (r : G)⁻¹ = (r * (l : G)⁻¹ * (r : G)⁻¹ * (l : G)⁻¹⁻¹)⁻¹ := by
        group
      rw [e]
      exact inv_mem h1
    obtain ⟨n, hnN, hn'⟩ := hn
    have hmem : βL.rangeRestrict n ∈ NJ := ⟨n, hnN, rfl⟩
    have hz := hNJc hmem
    have heq : ((βL.rangeRestrict n : ↥J) : MulAut _) = (βL l)⁻¹ * (β r * βL l * (β r)⁻¹) := by
      have e : Subgroup.inclusion hLX n =
          (Subgroup.inclusion hLX l)⁻¹ * r * Subgroup.inclusion hLX l * r⁻¹ :=
        Subtype.ext (by
          change (n : G) = (l : G)⁻¹ * r * l * (r : G)⁻¹
          exact hn')
      change β (Subgroup.inclusion hLX n) = _
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      change (β (Subgroup.inclusion hLX l))⁻¹ * β r * β (Subgroup.inclusion hLX l) * (β r)⁻¹ =
        (β (Subgroup.inclusion hLX l))⁻¹ * (β r * β (Subgroup.inclusion hLX l) * (β r)⁻¹)
      group
    have h2 := congrArg Subtype.val ((mem_center_iff.mp hz) ⟨k, hk⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, heq] at h2
    exact h2.symm
  have hcomm := commute_of_conj_central hγJ hc
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_perfect (Q := ↥J)
  exact scalar_of_commute_noncomm hcommW hpowW hW (J := (J : Set (MulAut _)))
    ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩ hcomm

theorem witness_R_kernel {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXN : X ≤ (CFSG.solvableRadical ↥L).map L.subtype)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X))
    (r : normalizer (X : Set G)) (hr : (r : G) ∈ R) :
    normalizerFrattiniConj X r = 1 ↔ (r : G) ∈ pCoreOf 2 (X ⊔ R) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMX, -, hR2, hQXM, hMR, -, -, -, -, -, -, -⟩ :=
    radical_witness_product h hR hp hp5 hXN hXc hXA
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hRX : R ≤ normalizer (X : Set G) := (hRT.trans h.t_le).trans hMX
  set Q := pCoreOf 2 X with hQdef
  have hQR : Q ≤ R := hQXM.trans hMR
  have hXQ : X ≤ normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hRQ : R ≤ normalizer (Q : Set G) :=
    hRX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hconj : ∀ g ∈ normalizer (Q : Set G), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
    fun g hg q hq => (mem_normalizer_iff.mp hg q).mp hq
  let C : Subgroup G :=
    { carrier := {c | c ∈ R ∧ ∀ x ∈ X, (c * x * c⁻¹)⁻¹ * x ∈ Q}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun x hx => by
        have hy : b * x * b⁻¹ ∈ X := (mem_normalizer_iff.mp (hRX hb.1) x).mp hx
        have e : (a * b * x * (a * b)⁻¹)⁻¹ * x =
            ((a * (b * x * b⁻¹) * a⁻¹)⁻¹ * (b * x * b⁻¹)) * ((b * x * b⁻¹)⁻¹ * x) := by group
        rw [e]
        exact mul_mem (ha.2 _ hy) (hb.2 x hx)⟩
      one_mem' := ⟨one_mem _, fun x _ => by
        rw [one_mul, inv_one, mul_one, inv_mul_cancel]
        exact one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun x hx => by
        have e : (a⁻¹ * x * a⁻¹⁻¹)⁻¹ * x = a⁻¹ * ((a * x * a⁻¹)⁻¹ * x)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hconj _ (hRQ (inv_mem ha.1)) _ (inv_mem (ha.2 x hx))⟩ }
  have hmemC : ∀ c, c ∈ C ↔ c ∈ R ∧ ∀ x ∈ X, (c * x * c⁻¹)⁻¹ * x ∈ Q := fun _ => Iff.rfl
  have hRC : R ≤ normalizer (C : Set G) := by
    have hfwd : ∀ s ∈ R, ∀ c ∈ C, s * c * s⁻¹ ∈ C := by
      intro s hs c hc
      rw [hmemC] at hc ⊢
      refine ⟨mul_mem (mul_mem hs hc.1) (inv_mem hs), fun x hx => ?_⟩
      have hx' : s⁻¹ * x * s⁻¹⁻¹ ∈ X := (mem_normalizer_iff.mp (hRX (inv_mem hs)) x).mp hx
      have e : (s * c * s⁻¹ * x * (s * c * s⁻¹)⁻¹)⁻¹ * x =
          s * ((c * (s⁻¹ * x * s⁻¹⁻¹) * c⁻¹)⁻¹ * (s⁻¹ * x * s⁻¹⁻¹)) * s⁻¹ := by group
      rw [e]
      exact hconj _ (hRQ hs) _ (hc.2 _ hx')
    intro s hs
    refine mem_normalizer_of_conj_mem (hfwd s hs) fun c hc => ?_
    have := hfwd s⁻¹ (inv_mem hs) c hc
    rwa [inv_inv] at this
  have hXC : X ≤ normalizer (C : Set G) := by
    have hfwd : ∀ y ∈ X, ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
      intro y hy c hc
      rw [hmemC] at hc ⊢
      have hc' : c⁻¹ ∈ C := inv_mem ((hmemC c).mpr hc)
      rw [hmemC] at hc'
      refine ⟨?_, fun x hx => ?_⟩
      · have e : y * c * y⁻¹ = c * ((c⁻¹ * y⁻¹ * c⁻¹⁻¹)⁻¹ * y⁻¹) := by group
        rw [e]
        exact mul_mem hc.1 (hQR (hc'.2 _ (inv_mem hy)))
      · have hx' : y⁻¹ * x * y⁻¹⁻¹ ∈ X := mul_mem (mul_mem (inv_mem hy) hx) (inv_mem (inv_mem hy))
        have e : (y * c * y⁻¹ * x * (y * c * y⁻¹)⁻¹)⁻¹ * x =
            y * ((c * (y⁻¹ * x * y⁻¹⁻¹) * c⁻¹)⁻¹ * (y⁻¹ * x * y⁻¹⁻¹)) * y⁻¹ := by group
        rw [e]
        exact hconj _ (hXQ hy) _ (hc.2 _ hx')
    intro y hy
    refine mem_normalizer_of_conj_mem (hfwd y hy) fun c hc => ?_
    have := hfwd y⁻¹ (inv_mem hy) c hc
    rwa [inv_inv] at this
  have hCV : C ≤ pCoreOf 2 (X ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun c hc => mem_sup_right hc.1)
      (sup_le hXC hRC) (hR2.to_le fun c hc => hc.1)
  constructor
  · intro h1
    set α := normalizerCoreQuotConj X r with hαdef
    have hαker : α ∈ (CFSG.SectionRank.Ccomm.autQuotient
        (frattini (↥X ⧸ CFSG.pCore 2 ↥X))).ker := h1
    obtain ⟨k, hk⟩ := CFSG.SectionRank.Ccomm.isPGroup_ker_autQuotient_frattini hXA ⟨α, hαker⟩
    obtain ⟨m, hm⟩ := hR2 ⟨r, hr⟩
    have hrm : r ^ 2 ^ m = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hm
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact this
    have hα2 : α ^ 2 ^ m = 1 := by rw [hαdef, ← map_pow, hrm, map_one]
    have hαp : α ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hcop : Nat.Coprime (p ^ k) (2 ^ m) := by
      apply Nat.Coprime.pow
      rw [Nat.coprime_primes hp Nat.prime_two]
      omega
    have h3 : orderOf α ∣ Nat.gcd (p ^ k) (2 ^ m) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hαp) (orderOf_dvd_of_pow_eq_one hα2)
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    have hα1 : α = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    refine hCV ⟨hr, fun x hx => ?_⟩
    have h2 := congrArg (fun f : MulAut (↥X ⧸ CFSG.pCore 2 ↥X) =>
      f (QuotientGroup.mk (⟨x, hx⟩ : ↥X))) hα1
    change (QuotientGroup.mk (X.normalizerMonoidHom r ⟨x, hx⟩) : ↥X ⧸ CFSG.pCore 2 ↥X) =
      QuotientGroup.mk ⟨x, hx⟩ at h2
    rw [QuotientGroup.eq, mem_pCore_iff_mem_pCoreOf] at h2
    exact h2
  · intro h1
    ext w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [NQRigid.normalizerFrattiniConj_mk_mk]
    change _ = (((x : ↥X ⧸ CFSG.pCore 2 ↥X) :
      (↥X ⧸ CFSG.pCore 2 ↥X) ⧸ frattini (↥X ⧸ CFSG.pCore 2 ↥X)))
    congr 1
    rw [QuotientGroup.eq, mem_pCore_iff_mem_pCoreOf]
    change (r * (x : G) * (r : G)⁻¹)⁻¹ * x ∈ Q
    have hXO : X ⊓ pCoreOf 2 (X ⊔ R) ≤ Q :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => mem_normalizer_inf (le_normalizer hg)
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ R) (mem_sup_left hg)))
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ R)).to_le inf_le_right)
    refine hXO (mem_inf.mpr ⟨?_, ?_⟩)
    · exact mul_mem (inv_mem ((mem_normalizer_iff.mp r.2 x).mp x.2)) x.2
    · have e : (r * (x : G) * (r : G)⁻¹)⁻¹ * x = r * ((x : G)⁻¹ * (r : G)⁻¹ * (x : G)⁻¹⁻¹) := by
        group
      rw [e]
      refine mul_mem h1 ?_
      exact (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ R)
        (mem_sup_left (inv_mem x.2))) _).mp (inv_mem h1)

theorem witness_inversion_generation {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X)) (a₀ : normalizer (X : Set G))
    (hinv : ∀ w, normalizerFrattiniConj X a₀ w = w⁻¹) :
    X ≤ closure {g | ∃ x ∈ X, g = x * a₀ * x⁻¹ * (a₀ : G)⁻¹} ⊔ pCoreOf 2 X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set D := closure {g | ∃ x ∈ X, g = x * a₀ * x⁻¹ * (a₀ : G)⁻¹} with hDdef
  have hxX : ∀ x ∈ X, x * a₀ * x⁻¹ * (a₀ : G)⁻¹ ∈ X := by
    intro x hx
    have e : x * a₀ * x⁻¹ * (a₀ : G)⁻¹ = x * (a₀ * x⁻¹ * (a₀ : G)⁻¹) := by group
    rw [e]
    exact mul_mem hx ((mem_normalizer_iff.mp a₀.2 _).mp (inv_mem hx))
  set S' : Set ↥X := {d | ∃ x ∈ X, (d : G) = x * a₀ * x⁻¹ * (a₀ : G)⁻¹} with hS'def
  set mkP := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hmkPdef
  set mkW := QuotientGroup.mk' (frattini (↥X ⧸ CFSG.pCore 2 ↥X)) with hmkWdef
  have hpowW := frattini_pow_prime hXA
  have hsq : ∀ y : ↥X, mkW (mkP ⟨y * a₀ * (y : G)⁻¹ * (a₀ : G)⁻¹, hxX y y.2⟩) =
      (mkW (mkP y)) ^ 2 := by
    intro y
    have e : (⟨y * a₀ * (y : G)⁻¹ * (a₀ : G)⁻¹, hxX y y.2⟩ : ↥X) =
        y * X.normalizerMonoidHom a₀ y⁻¹ := Subtype.ext (by
      change (y : G) * a₀ * (y : G)⁻¹ * (a₀ : G)⁻¹ = (y : G) * (a₀ * (y : G)⁻¹ * (a₀ : G)⁻¹)
      group)
    rw [e, map_mul, map_mul]
    have h1 : mkW (mkP (X.normalizerMonoidHom a₀ y⁻¹)) =
        normalizerFrattiniConj X a₀ (mkW (mkP y⁻¹)) :=
      (NQRigid.normalizerFrattiniConj_mk_mk a₀ y⁻¹).symm
    rw [h1, hinv, map_inv, map_inv, inv_inv, pow_two]
  have hWtop : closure (mkW '' (mkP '' S')) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ u
    refine subset_closure ⟨mkP ⟨x ^ ((p + 1) / 2) * a₀ * ((x : G) ^ ((p + 1) / 2))⁻¹ *
      (a₀ : G)⁻¹, hxX _ (x ^ ((p + 1) / 2)).2⟩,
      ⟨_, ⟨x ^ ((p + 1) / 2), (x ^ ((p + 1) / 2)).2, rfl⟩, rfl⟩, ?_⟩
    have h1 := hsq (x ^ ((p + 1) / 2))
    simp only [Subgroup.coe_pow] at h1
    rw [h1, map_pow, map_pow, ← pow_mul]
    have hp2 : (p + 1) / 2 * 2 = p + 1 := by
      have : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
      omega
    rw [hp2, pow_succ, hpowW, one_mul]
  have hPtop : closure (mkP '' S') = ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.frattini_generator_lifting (mkP '' S') hWtop
  have hS'D : (closure S').map X.subtype ≤ D := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨d, ⟨x, hx, hd⟩, rfl⟩
    change (d : G) ∈ D
    rw [hd]
    exact subset_closure ⟨x, hx, rfl⟩
  intro x hx
  have h1 : mkP ⟨x, hx⟩ ∈ (closure S').map mkP := by
    rw [MonoidHom.map_closure, hPtop]
    exact mem_top _
  obtain ⟨d, hd, hdx⟩ := h1
  rw [hmkPdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    mem_pCore_iff_mem_pCoreOf] at hdx
  have e : x = (d : G) * ((d⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
    change x = (d : G) * ((d : G)⁻¹ * x)
    group
  rw [e]
  exact mul_mem (mem_sup_left (hS'D ⟨d, hd, rfl⟩)) (mem_sup_right hdx)

theorem witness_elementary {T L M : Subgroup G} (h : QTNQ T L M)
    {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {X : Subgroup G} (hXN : X ≤ (CFSG.solvableRadical ↥L).map L.subtype)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X))
    (hW : Nat.card ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ frattini (↥X ⧸ CFSG.pCore 2 ↥X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {A : Subgroup G} (hAR : A ≤ R) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAQ : ¬ A ≤ pCoreOf 2 (X ⊔ R)) :
    (A ⊓ pCoreOf 2 (X ⊔ R)).relIndex A = 2 ∧
      X ≤ closure {g | ∃ v ∈ X ⊔ R, ∃ a ∈ A, g = v * a * v⁻¹} ⊔ R := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hMX, -, -, hQXM, hMR, -, -, -, -, -, -, -⟩ :=
    radical_witness_product h hR hp hp5 hXN hXc hXA
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hRX : R ≤ normalizer (X : Set G) := (hRT.trans h.t_le).trans hMX
  have hAX : A ≤ normalizer (X : Set G) := hAR.trans hRX
  set β := normalizerFrattiniConj X with hβdef
  set f : ↥A →* MulAut ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ frattini (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    β.comp (Subgroup.inclusion hAX) with hfdef
  have hfa : ∀ a : ↥A, f a = 1 ∨ ∀ w, f a w = w⁻¹ := by
    intro a
    refine (witness_R_scalar h hR hp hp5 hXN hXc hXA hW hLW (Subgroup.inclusion hAX a)
      (hAR a.2)).2 ?_
    have h1 : Subgroup.inclusion hAX a ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA2 _ a.2)
    rw [← map_pow, h1, map_one]
  have hfker : ∀ a : ↥A, f a = 1 ↔ (a : G) ∈ pCoreOf 2 (X ⊔ R) := fun a =>
    witness_R_kernel h hR hp hp5 hXN hXc hXA (Subgroup.inclusion hAX a) (hAR a.2)
  obtain ⟨a₀, ha₀A, ha₀Q⟩ := Set.not_subset.mp hAQ
  have hfa₀ : ∀ w, f ⟨a₀, ha₀A⟩ w = w⁻¹ :=
    (hfa _).resolve_left fun h1 => ha₀Q ((hfker _).mp h1)
  have hker : f.ker = (A ⊓ pCoreOf 2 (X ⊔ R)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, hfker, Subgroup.mem_subgroupOf, mem_inf]
    exact ⟨fun h1 => ⟨a.2, h1⟩, fun h1 => h1.2⟩
  have hrange : Nat.card f.range = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨f ⟨a₀, ha₀A⟩, ⟨_, rfl⟩⟩, fun h1 => ?_, ?_⟩
    · exact ha₀Q ((hfker _).mp (congrArg Subtype.val h1).symm)
    · ext ⟨g, a, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases hfa a with h1 | h1
      · left
        exact Subtype.ext h1
      · right
        apply Subtype.ext
        ext w
        change f a w = f ⟨a₀, ha₀A⟩ w
        rw [h1, hfa₀]
  refine ⟨by rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange], ?_⟩
  have hgen0 := witness_inversion_generation hp (by omega) hXA ⟨a₀, hAX ha₀A⟩ hfa₀
  refine hgen0.trans (sup_le ?_ ((hQXM.trans hMR).trans le_sup_right))
  rw [closure_le]
  rintro _ ⟨x, hx, rfl⟩
  refine mem_sup_left (mul_mem (subset_closure ⟨x, mem_sup_left hx, a₀, ha₀A, rfl⟩) (inv_mem ?_))
  exact subset_closure ⟨1, one_mem _, a₀, ha₀A, by group⟩

end CFSG.Quasithin.H13.NQBlock

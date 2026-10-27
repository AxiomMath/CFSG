module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.RankThree.PartTwo.KFacts.BlackburnScalar
import CFSG.RankThree.PartTwo.Sec16.Kcd166.FixRank
import CFSG.GroupTheory.ChiefFactorScalar

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG
open CFSG.ABGLocalTools
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

structure IsChiefRep {r : ℕ} (Y F₁ F₂ : Subgroup G) {V : Type} [AddCommGroup V]
    [Module (ZMod r) V] (ρ : Representation (ZMod r) ↥Y V) (q : G → V) : Prop where
  surj : ∀ v : V, ∃ m ∈ F₁, q m = v
  add : ∀ m ∈ F₁, ∀ m' ∈ F₁, q (m * m') = q m + q m'
  ker : ∀ m ∈ F₁, q m = 0 ↔ m ∈ F₂
  equivariant : ∀ y : ↥Y, ∀ m ∈ F₁, ρ y (q m) = q ((y : G) * m * (y : G)⁻¹)

theorem exists_chiefRep_of_isChiefFactorUnder [Finite G] {r : ℕ} [Fact r.Prime]
    {Y F₁ F₂ : Subgroup G} (h : CFSG.ABGLocalTools.IsChiefFactorUnder r Y F₁ F₂) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod r) V) (_ : Module.Finite (ZMod r) V)
      (ρ : Representation (ZMod r) ↥Y V) (q : G → V),
      ρ.IsIrreducible ∧ IsChiefRep Y F₁ F₂ ρ q := by
  classical
  haveI hnormal : (F₂.subgroupOf F₁).Normal := h.normal
  haveI hEA : IsElementaryAbelian r (F₁ ⧸ F₂.subgroupOf F₁) := h.isElementaryAbelian
  let V := Additive (F₁ ⧸ F₂.subgroupOf F₁)
  haveI hFin : Finite V := inferInstance
  haveI hModFin : Module.Finite (ZMod r) V := Module.Finite.of_finite
  haveI hnt : Nontrivial V := by
    obtain ⟨m, hmF₁, hmF₂⟩ := IsConcreteLE.exists_of_lt h.1
    refine ⟨0, Additive.ofMul ((⟨m, hmF₁⟩ : F₁) : F₁ ⧸ F₂.subgroupOf F₁), ?_⟩
    intro hzero
    have hzero' : Additive.ofMul ((⟨m, hmF₁⟩ : F₁) : F₁ ⧸ F₂.subgroupOf F₁) = 0 :=
      hzero.symm
    rw [ofMul_eq_zero] at hzero'
    exact hmF₂ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hzero'))
  let ρ : Representation (ZMod r) ↥Y V :=
    (Units.coeHom (Module.End (ZMod r) V)).comp (chiefRep (p := r) h.2.1 h.2.2.1)
  let q : G → V := fun y =>
    if hy : y ∈ F₁ then Additive.ofMul ((⟨y, hy⟩ : F₁) : F₁ ⧸ F₂.subgroupOf F₁) else 0
  have hq_mem : ∀ (y : G) (hy : y ∈ F₁),
      q y = Additive.ofMul ((⟨y, hy⟩ : F₁) : F₁ ⧸ F₂.subgroupOf F₁) := by
    intro y hy
    dsimp only [q]
    rw [dif_pos hy]
  have hρapply : ∀ (y : ↥Y) (w : F₁),
      ρ y (Additive.ofMul ((w : F₁) : F₁ ⧸ F₂.subgroupOf F₁)) =
        Additive.ofMul ((⟨(y : G) * (w : G) * (y : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (h.2.1 y.2) (w : G)).mp w.2⟩ : F₁) :
          F₁ ⧸ F₂.subgroupOf F₁) := by
    intro y w
    change ((chiefRep (p := r) h.2.1 h.2.2.1 y : LinearMap.GeneralLinearGroup (ZMod r) V) :
        Additive (F₁ ⧸ F₂.subgroupOf F₁) →ₗ[ZMod r] Additive (F₁ ⧸ F₂.subgroupOf F₁))
      (Additive.ofMul ((w : F₁) : F₁ ⧸ F₂.subgroupOf F₁)) = _
    rw [chiefRep_apply_mk]
    congr 1
  have hirr : ρ.IsIrreducible := by
    refine { eq_bot_or_eq_top := fun U => ?_ }
    have hU : ∀ n : ↥Y, ∀ v ∈ U.toSubmodule,
        ((chiefRep (p := r) h.2.1 h.2.2.1 n :
          LinearMap.GeneralLinearGroup (ZMod r) V) : V →ₗ[ZMod r] V) v ∈ U.toSubmodule := by
      intro n v hv
      exact U.apply_mem_toSubmodule n hv
    rcases chiefRep_irreducible h U.toSubmodule hU with hbot | htop
    · exact Or.inl (Subrepresentation.toSubmodule_injective hbot)
    · exact Or.inr (Subrepresentation.toSubmodule_injective htop)
  refine ⟨V, inferInstance, inferInstance, hModFin, ρ, q, hirr, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul f)
    exact ⟨w, w.2, by rw [hq_mem w w.2]; simpa using congrArg Additive.ofMul hw⟩
  · intro m hm m' hm'
    rw [hq_mem (m * m') (F₁.mul_mem hm hm'), hq_mem m hm, hq_mem m' hm']
    rfl
  · intro m hm
    rw [hq_mem m hm, ofMul_eq_zero, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  · intro y m hm
    rw [hq_mem m hm, hq_mem ((y : G) * m * (y : G)⁻¹)
      ((Subgroup.mem_normalizer_iff.mp (h.2.1 y.2) m).mp hm)]
    exact hρapply y ⟨m, hm⟩

private lemma IsChiefRep.q_one {r : ℕ} {Y F₁ F₂ : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod r) V] {ρ : Representation (ZMod r) ↥Y V} {q : G → V}
    (hq : IsChiefRep Y F₁ F₂ ρ q) : q 1 = 0 := by
  have h := hq.add 1 F₁.one_mem 1 F₁.one_mem
  rw [mul_one] at h
  have h1 : q 1 + q 1 = 0 + q 1 := by rw [zero_add]; exact h.symm
  exact add_right_cancel h1

private lemma IsChiefRep.q_inv {r : ℕ} {Y F₁ F₂ : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod r) V] {ρ : Representation (ZMod r) ↥Y V} {q : G → V}
    (hq : IsChiefRep Y F₁ F₂ ρ q) {m : G} (hm : m ∈ F₁) : q m⁻¹ = -q m := by
  have h := hq.add m hm m⁻¹ (F₁.inv_mem hm)
  rw [mul_inv_cancel, hq.q_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private lemma isPGroup_zpowers_subtype {Y : Subgroup G} {t : ↥Y}
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) :
    IsPGroup 2 (Subgroup.zpowers (t : G)) := by
  have h := ht2.map Y.subtype
  rwa [MonoidHom.map_zpowers] at h

private lemma rho_apply_eq_iff_of_isChiefRep {r : ℕ} {Y F₁ F₂ : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod r) V] {ρ : Representation (ZMod r) ↥Y V} {q : G → V}
    (hq : IsChiefRep Y F₁ F₂ ρ q) (hY : Y ≤ Subgroup.normalizer (F₁ : Set G))
    {m : G} (hm : m ∈ F₁) (y : ↥Y) :
    ρ y (q m) = q m ↔ ⁅m, (y : G)⁆ ∈ F₂ := by
  have hqinv : ∀ m ∈ F₁, q m⁻¹ = -q m := fun _ hm => hq.q_inv hm
  constructor
  · intro h
    have hu : (y : G) * m * (y : G)⁻¹ ∈ F₁ :=
      (Subgroup.mem_normalizer_iff.mp (hY y.2) m).mp hm
    have h1 : q ((y : G) * m * (y : G)⁻¹) = q m := by
      rw [← hq.equivariant y m hm]; exact h
    have h2 : q ((y : G) * m * (y : G)⁻¹ * m⁻¹) =
        q ((y : G) * m * (y : G)⁻¹) + q m⁻¹ :=
      hq.add ((y : G) * m * (y : G)⁻¹) hu m⁻¹ (F₁.inv_mem hm)
    rw [h1, hqinv m hm, add_neg_cancel] at h2
    have h3 : (y : G) * m * (y : G)⁻¹ * m⁻¹ ∈ F₂ :=
      (hq.ker ((y : G) * m * (y : G)⁻¹ * m⁻¹)
        (F₁.mul_mem hu (F₁.inv_mem hm))).mp h2
    have h4 := F₂.inv_mem h3
    rwa [show ((y : G) * m * (y : G)⁻¹ * m⁻¹)⁻¹ = ⁅m, (y : G)⁆ by
      rw [commutatorElement_def]; group] at h4
  · intro h
    have hu : (y : G) * m * (y : G)⁻¹ ∈ F₁ :=
      (Subgroup.mem_normalizer_iff.mp (hY y.2) m).mp hm
    have h1 : (y : G) * m * (y : G)⁻¹ * m⁻¹ ∈ F₂ := by
      have h' := F₂.inv_mem h
      rwa [show (⁅m, (y : G)⁆)⁻¹ = (y : G) * m * (y : G)⁻¹ * m⁻¹ by
        rw [commutatorElement_def]; group] at h'
    have h2 : q ((y : G) * m * (y : G)⁻¹ * m⁻¹) = 0 :=
      (hq.ker ((y : G) * m * (y : G)⁻¹ * m⁻¹)
        (F₁.mul_mem hu (F₁.inv_mem hm))).mpr h1
    have h3 := hq.add ((y : G) * m * (y : G)⁻¹) hu m⁻¹ (F₁.inv_mem hm)
    rw [h2, hqinv m hm] at h3
    have h4 : q ((y : G) * m * (y : G)⁻¹) = q m := by
      have h5 : q ((y : G) * m * (y : G)⁻¹) + (-q m) = q m + (-q m) := by
        rw [h3.symm, add_neg_cancel]
      exact add_right_cancel h5
    rw [hq.equivariant y m hm, h4]

theorem IsChiefRep.rho_eq_one_iff {r : ℕ} {Y F₁ F₂ : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod r) V] {ρ : Representation (ZMod r) ↥Y V} {q : G → V}
    (hq : IsChiefRep Y F₁ F₂ ρ q) (hch : CFSG.ABGLocalTools.IsChiefFactorUnder r Y F₁ F₂)
    (y : ↥Y) : ρ y = 1 ↔ ∀ m ∈ F₁, ⁅m, (y : G)⁆ ∈ F₂ := by
  constructor
  · intro h m hm
    exact (rho_apply_eq_iff_of_isChiefRep hq hch.2.1 hm y).mp (by rw [h]; rfl)
  · intro h
    ext v
    obtain ⟨m, hm, rfl⟩ := hq.surj v
    exact (rho_apply_eq_iff_of_isChiefRep hq hch.2.1 hm y).mpr (h m hm)

private lemma exists_fixedSubgroup {r : ℕ} {Y F₁ F₂ : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod r) V] {ρ : Representation (ZMod r) ↥Y V} {q : G → V}
    (hq : IsChiefRep Y F₁ F₂ ρ q) (hch : CFSG.ABGLocalTools.IsChiefFactorUnder r Y F₁ F₂)
    (t : ↥Y) :
    ∃ F : Subgroup G, F₂ ≤ F ∧ F ≤ F₁ ∧
      (∀ m : G, m ∈ F ↔ m ∈ F₁ ∧ ρ t (q m) = q m) ∧
      (∀ f ∈ F, (t : G) * f * (t : G)⁻¹ * f⁻¹ ∈ F₂) := by
  classical
  have hqinv : ∀ m ∈ F₁, q m⁻¹ = -q m := fun _ hm => hq.q_inv hm
  let F : Subgroup G :=
    { carrier := {m | m ∈ F₁ ∧ ρ t (q m) = q m}
      one_mem' := ⟨F₁.one_mem, by rw [hq.q_one]; simp⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨F₁.mul_mem ha1 hb1, ?_⟩
        rw [hq.add a ha1 b hb1, map_add, ha2, hb2]
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨F₁.inv_mem ha1, ?_⟩
        rw [hqinv a ha1, map_neg, ha2] }
  have hFmem : ∀ m : G, m ∈ F ↔ m ∈ F₁ ∧ ρ t (q m) = q m := fun m => Iff.rfl
  refine ⟨F, ?_, ?_, hFmem, ?_⟩
  · intro x hx
    refine (hFmem x).mpr ⟨hch.1.le hx, ?_⟩
    rw [(hq.ker x (hch.1.le hx)).mpr hx]
    simp
  · exact fun x hx => ((hFmem x).mp hx).1
  · intro f hf
    have hf1 : f ∈ F₁ := ((hFmem f).mp hf).1
    have hfix : ρ t (q f) = q f := ((hFmem f).mp hf).2
    have hcomm : ⁅f, (t : G)⁆ ∈ F₂ :=
      (rho_apply_eq_iff_of_isChiefRep hq hch.2.1 hf1 t).mp hfix
    have hinv := F₂.inv_mem hcomm
    rwa [show (⁅f, (t : G)⁆)⁻¹ = (t : G) * f * (t : G)⁻¹ * f⁻¹ by
      rw [commutatorElement_def]; group] at hinv

private lemma natCard_ker_eq_relIndex {r : ℕ} {Y F₁ F₂ F : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod r) V] {ρ : Representation (ZMod r) ↥Y V} {q : G → V}
    (hq : IsChiefRep Y F₁ F₂ ρ q) (t : ↥Y)
    (hF : ∀ m : G, m ∈ F ↔ m ∈ F₁ ∧ ρ t (q m) = q m) :
    F₂.relIndex F = Nat.card (LinearMap.ker (ρ t - 1)) := by
  classical
  let K : AddSubgroup V := (LinearMap.ker (ρ t - 1)).toAddSubgroup
  let qF : F →* Multiplicative V :=
    { toFun := fun a => Multiplicative.ofAdd (q a)
      map_one' := by
        have h1 : q (1 : G) = 0 := hq.q_one
        simp [h1]
      map_mul' := fun a b => by
        have ha : (a : G) ∈ F₁ := ((hF a).mp a.2).1
        have hb : (b : G) ∈ F₁ := ((hF b).mp b.2).1
        change Multiplicative.ofAdd (q ((a : G) * (b : G))) =
          Multiplicative.ofAdd (q (a : G)) * Multiplicative.ofAdd (q (b : G))
        rw [hq.add (a : G) ha (b : G) hb]
        rfl }
  have hqFker : qF.ker = F₂.subgroupOf F := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change Multiplicative.ofAdd (q (a : G)) = 1 ↔ (a : G) ∈ F₂
    rw [ofAdd_eq_one]
    exact hq.ker (a : G) ((hF a).mp a.2).1
  have hqFrange : qF.range = K.toSubgroup := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [Multiplicative.mem_toSubgroup]
      change (ρ t - 1) (q (a : G)) = 0
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact ((hF a).mp a.2).2
    · intro hv
      rw [Multiplicative.mem_toSubgroup] at hv
      change (ρ t - 1) (Multiplicative.toAdd v) = 0 at hv
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      obtain ⟨m, hm, hqm⟩ := hq.surj (Multiplicative.toAdd v)
      refine ⟨⟨m, (hF m).mpr ⟨hm, ?_⟩⟩, ?_⟩
      · rw [hqm]; exact hv
      · change Multiplicative.ofAdd (q m) = v
        rw [hqm]; simp
  have hfirst : Nat.card (F ⧸ F₂.subgroupOf F) = Nat.card qF.range := by
    rw [← hqFker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange qF).toEquiv
  have hsecond : Nat.card qF.range = Nat.card (LinearMap.ker (ρ t - 1)) := by
    rw [hqFrange]
    refine Nat.card_congr ?_
    refine
      { toFun := fun a => ⟨Multiplicative.toAdd a.val,
          (Multiplicative.mem_toSubgroup K a.val).mp a.2⟩
        invFun := fun a => ⟨Multiplicative.ofAdd a.val,
          (Multiplicative.mem_toSubgroup K (Multiplicative.ofAdd a.val)).mpr a.2⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
  rw [Subgroup.relIndex, Subgroup.index_eq_card, hfirst, hsecond]

theorem IsChiefRep.finrank_ker_le_three [Finite G] {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ r = 1) → Nat.card E ≤ r ^ 2)
    {Y F₁ F₂ : Subgroup G} (hch : CFSG.ABGLocalTools.IsChiefFactorUnder r Y F₁ F₂)
    (hF₁ : IsPGroup r F₁) {V : Type} [AddCommGroup V] [Module (ZMod r) V]
    [Module.Finite (ZMod r) V] {ρ : Representation (ZMod r) ↥Y V} {q : G → V}
    (hq : IsChiefRep Y F₁ F₂ ρ q) {t : ↥Y} (ht2 : IsPGroup 2 (Subgroup.zpowers t))
    (ht1 : t ≠ 1) : Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) ≤ 3 := by
  obtain ⟨F, hNF, hFM, hFmem, hFt⟩ := exists_fixedSubgroup hq hch t
  have ht2' : IsPGroup 2 (Subgroup.zpowers (t : G)) := isPGroup_zpowers_subtype ht2
  have htnM : (t : G) ∉ F₁ := by
    intro htF
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdisj : Disjoint (Subgroup.zpowers (t : G)) F₁ :=
      IsPGroup.disjoint_of_ne 2 r (by omega) _ _ ht2' hF₁
    rw [disjoint_iff] at hdisj
    have hmem : (t : G) ∈ Subgroup.zpowers (t : G) ⊓ F₁ :=
      ⟨Subgroup.mem_zpowers _, htF⟩
    rw [hdisj] at hmem
    exact ht1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have hrel : F₂.relIndex F ≤ r ^ 3 :=
    CFSG.RankThree.PartTwo.Sec16.Kcd166.relIndex_le_pow_three_of_not_mem (p := r) hr5 hloc
      hch.1.le hch.normal hch.2.2.2.2.1 hch.2.2.2.2.2.1 ht2' (hch.2.1 t.2) (hch.2.2.1 t.2) htnM
      hNF hFM hFt
  have hcardker : Nat.card (LinearMap.ker (ρ t - 1)) =
      r ^ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod]
  have hpow : r ^ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) ≤ r ^ 3 := by
    rw [← hcardker, ← natCard_ker_eq_relIndex hq t hFmem]
    exact hrel
  exact (Nat.pow_le_pow_iff_right (Fact.out : r.Prime).one_lt).mp hpow

theorem IsChiefRep.finrank_ker_le_two [Finite G]
    (hK1 : CFSG.RankThree.PartTwo.KFacts.BlackburnScalarAut) {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ r = 1) → Nat.card E ≤ r ^ 2)
    {Y F₁ F₂ : Subgroup G} (hch : CFSG.ABGLocalTools.IsChiefFactorUnder r Y F₁ F₂)
    (hF₁ : IsPGroup r F₁) {V : Type} [AddCommGroup V] [Module (ZMod r) V]
    [Module.Finite (ZMod r) V] {ρ : Representation (ZMod r) ↥Y V} {q : G → V}
    (hq : IsChiefRep Y F₁ F₂ ρ q) {σ : ↥Y} (hσc : σ ∈ Subgroup.center ↥Y) (hσ3 : σ ^ 3 = 1)
    (hσ1 : ρ σ ≠ 1) {t : ↥Y} (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (ht1 : t ≠ 1) :
    Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) ≤ 2 := by
  obtain ⟨F, hNF, hFM, hFmem, hFt⟩ := exists_fixedSubgroup hq hch t
  have ht2' : IsPGroup 2 (Subgroup.zpowers (t : G)) := isPGroup_zpowers_subtype ht2
  have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hσ3' : (σ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hσ3
  have hσtY : σ * t = t * σ := (Subgroup.mem_center_iff.mp hσc t).symm
  have hσt : (σ : G) * (t : G) = (t : G) * (σ : G) := by
    simpa using congrArg Subtype.val hσtY
  have hcY : Y ≤ Subgroup.centralizer ({(σ : G)} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hσc ⟨y, hy⟩))
  have hfpf : ∀ m ∈ F₁, (σ : G) * m * (σ : G)⁻¹ * m⁻¹ ∈ F₂ → m ∈ F₂ := by
    rcases CFSG.GroupTheory.trivial_or_fixedPointFree_of_isChiefFactorUnder hch hcY
      (hch.2.1 σ.2) (hch.2.2.1 σ.2) with htr | hfpf
    · exfalso
      apply hσ1
      rw [IsChiefRep.rho_eq_one_iff hq hch σ]
      intro m hm
      have h := F₂.inv_mem (htr m hm)
      rwa [show ((σ : G) * m * (σ : G)⁻¹ * m⁻¹)⁻¹ = ⁅m, (σ : G)⁆ by
        rw [commutatorElement_def]; group] at h
    · exact hfpf
  have hsc : r % 3 = 1 → ∃ w : ℕ, ∀ m ∈ F₁, (σ : G) * m * (σ : G)⁻¹ * (m ^ w)⁻¹ ∈ F₂ :=
    fun hr => CFSG.GroupTheory.exists_pow_of_isChiefFactorUnder hr hch hσ3' hcY
      (hch.2.1 σ.2) (hch.2.2.1 σ.2)
  have hσF : (σ : G) ∈ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm
      have hm1 : m ∈ F₁ := ((hFmem m).mp hm).1
      have hfix : ρ t (q m) = q m := ((hFmem m).mp hm).2
      have hconj1 : (σ : G) * m * (σ : G)⁻¹ ∈ F₁ :=
        (Subgroup.mem_normalizer_iff.mp (hch.2.1 σ.2) m).mp hm1
      refine (hFmem _).mpr ⟨hconj1, ?_⟩
      rw [← hq.equivariant σ m hm1]
      have hcommρ : ρ σ * ρ t = ρ t * ρ σ := by
        rw [← map_mul, ← map_mul, hσtY]
      calc ρ t (ρ σ (q m)) = (ρ t * ρ σ) (q m) := rfl
        _ = (ρ σ * ρ t) (q m) := by rw [← hcommρ]
        _ = ρ σ (ρ t (q m)) := rfl
        _ = ρ σ (q m) := by rw [hfix]
    · intro hm
      have hm1 : (σ : G) * m * (σ : G)⁻¹ ∈ F₁ := ((hFmem _).mp hm).1
      have hfix : ρ t (q ((σ : G) * m * (σ : G)⁻¹)) = q ((σ : G) * m * (σ : G)⁻¹) :=
        ((hFmem _).mp hm).2
      have hm1' : m ∈ F₁ := by
        have h := (Subgroup.mem_normalizer_iff.mp (hch.2.1 (Subgroup.inv_mem Y σ.2))
          ((σ : G) * m * (σ : G)⁻¹)).mp hm1
        rwa [show (↑σ)⁻¹ * ((↑σ) * m * (↑σ)⁻¹) * (↑σ)⁻¹⁻¹ = m by group] at h
      refine (hFmem m).mpr ⟨hm1', ?_⟩
      have heq : ρ σ⁻¹ (q ((σ : G) * m * (σ : G)⁻¹)) = q m := by
        rw [hq.equivariant σ⁻¹ ((σ : G) * m * (σ : G)⁻¹) hm1]
        congr 1
        simp only [Subgroup.coe_inv]
        group
      rw [← heq]
      have hσinv_c : σ⁻¹ ∈ Subgroup.center ↥Y := Subgroup.inv_mem _ hσc
      have hcommρ : ρ σ⁻¹ * ρ t = ρ t * ρ σ⁻¹ := by
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hσinv_c t).symm]
      calc ρ t (ρ σ⁻¹ (q ((σ : G) * m * (σ : G)⁻¹)))
          = (ρ t * ρ σ⁻¹) (q ((σ : G) * m * (σ : G)⁻¹)) := rfl
        _ = (ρ σ⁻¹ * ρ t) (q ((σ : G) * m * (σ : G)⁻¹)) := by rw [← hcommρ]
        _ = ρ σ⁻¹ (ρ t (q ((σ : G) * m * (σ : G)⁻¹))) := rfl
        _ = ρ σ⁻¹ (q ((σ : G) * m * (σ : G)⁻¹)) := by rw [hfix]
  have hrel : F₂.relIndex F ≤ r ^ 2 :=
    CFSG.RankThree.PartTwo.Sec16.Kcd166.relIndex_le_sq_of_order_three hK1 hr5 hloc hF₁
      hch.1.le hch.normal hch.2.2.2.2.1 hch.2.2.2.2.2.1 ht2' ht1' (hch.2.2.1 t.2) hσ3' hσt
      (hch.2.2.1 σ.2) hfpf hsc hNF hFM hσF hFt
  have hcardker : Nat.card (LinearMap.ker (ρ t - 1)) =
      r ^ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod]
  have hpow : r ^ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) ≤ r ^ 2 := by
    rw [← hcardker, ← natCard_ker_eq_relIndex hq t hFmem]
    exact hrel
  exact (Nat.pow_le_pow_iff_right (Fact.out : r.Prime).one_lt).mp hpow

end CFSG.RankThree.PartTwo.J2Residue

module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUInner
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsRank
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsCfg
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgForward

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Action

variable {S : Type} [Group S] {A : Subgroup (MulAut S)} {K : Subgroup S}

theorem map_eq_of_mapsTo (hmap : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut S) k ∈ K) {a : MulAut S}
    (ha : a ∈ A) : K.map (a : S →* S) = K := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    exact hmap a ha k hk
  · intro k hk
    exact ⟨a⁻¹ k, hmap a⁻¹ (inv_mem ha) k hk, MulAut.apply_inv_self S a k⟩

@[expose] noncomputable def restrK (hmap : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut S) k ∈ K) (a : A) :
    MulAut K :=
  ((a : MulAut S).subgroupMap K).trans (MulEquiv.subgroupCongr (map_eq_of_mapsTo hmap a.2))

@[expose] noncomputable def actQ (hmap : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut S) k ∈ K) :
    A →* MulAut (K ⧸ CFSG.pCore 2 K) where
  toFun a := quotPCoreTwoCongr (restrK hmap a)
  map_one' := by
    ext x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    change ((restrK hmap 1 k : K) : K ⧸ CFSG.pCore 2 K) = (k : K ⧸ CFSG.pCore 2 K)
    congr 1
  map_mul' a b := by
    ext x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    change ((restrK hmap (a * b) k : K) : K ⧸ CFSG.pCore 2 K) =
      ((restrK hmap a (restrK hmap b k) : K) : K ⧸ CFSG.pCore 2 K)
    congr 1

theorem actQ_mk (hmap : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut S) k ∈ K) (a : A) (k : K) :
    actQ hmap a (k : K ⧸ CFSG.pCore 2 K) = ((restrK hmap a k : K) : K ⧸ CFSG.pCore 2 K) :=
  rfl

theorem mem_pCoreOf_of_actQ_eq_one (hmap : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut S) k ∈ K) {a : A}
    (ha : actQ hmap a = 1) : ∀ k ∈ K, (a : MulAut S) k * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  intro k hk
  have h := congrArg (fun α : MulAut (K ⧸ CFSG.pCore 2 K) => α ((⟨k, hk⟩ : K) :
    K ⧸ CFSG.pCore 2 K)) ha
  simp only [actQ_mk, MulAut.one_apply] at h
  have h' : (((restrK hmap a ⟨k, hk⟩) * (⟨k, hk⟩ : K)⁻¹ : K) : K ⧸ CFSG.pCore 2 K) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, mul_inv_cancel]
  rw [QuotientGroup.eq_one_iff] at h'
  exact ⟨_, h', rfl⟩

variable [Finite S]

theorem nine_le_card_range_actQ {σ : MulAut S} (hc : CfgSEps S A σ K) :
    9 ≤ Nat.card (actQ hc.map_mem).range := by
  set ρ := actQ hc.map_mem with hρ
  have hker : ρ.ker ≤ (Subgroup.zpowers σ).subgroupOf A := by
    intro a ha
    rw [Subgroup.mem_subgroupOf]
    exact hc.faithful a a.2 (mem_pCoreOf_of_actQ_eq_one hc.map_mem ha)
  have hσ3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  have hz : Nat.card (Subgroup.zpowers σ) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hσ3)
  have hk3 : Nat.card ρ.ker ≤ 3 := by
    have hle : ρ.ker.map A.subtype ≤ Subgroup.zpowers σ := by
      rintro _ ⟨a, ha, rfl⟩
      exact hker ha
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective A)] at h1
    omega
  have hA : Nat.card A = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  rw [hc.isE27.2] at hA
  by_contra hlt
  push Not at hlt
  have : Nat.card ρ.range * Nat.card ρ.ker ≤ 8 * 3 := Nat.mul_le_mul (by omega) hk3
  omega

theorem pow_three_of_mem_range_actQ {σ : MulAut S} (hc : CfgSEps S A σ K) {α : MulAut
    (K ⧸ CFSG.pCore 2 K)} (hα : α ∈ (actQ hc.map_mem).range) : α ^ 3 = 1 := by
  obtain ⟨a, rfl⟩ := hα
  rw [← map_pow]
  have : a ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hc.isE27.1.2 _ a.2)
  rw [this, map_one]

end Action

section Cyclic

theorem card_le_three_of_isCyclic_sylow {X : Type*} [Group X] [Finite X]
    (hcyc : ∀ Q : Sylow 3 X, IsCyclic Q) {E : Subgroup X} (hE3 : ∀ a ∈ E, a ^ 3 = 1) :
    Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 _ x.2)⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  haveI := hcyc Q
  haveI : IsCyclic (E.subgroupOf (Q : Subgroup X)) := Subgroup.isCyclic _
  have heq : E.subgroupOf (Q : Subgroup X) ≃* E := Subgroup.subgroupOfEquivOfLe hQ
  haveI : IsCyclic E := isCyclic_of_surjective heq.toMonoidHom heq.surjective
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.card_le_three_of_isCyclic
    fun w => Subtype.ext (by simpa using hE3 _ w.2)

theorem card_le_three_of_le_inn {X : Type} [Group X] [Finite X]
    (hcyc : ∀ Q : Sylow 3 X, IsCyclic Q) (hZ : Subgroup.center X = ⊥) {E : Subgroup (MulAut X)}
    (hE : E ≤ (MulAut.conj : X →* MulAut X).range) (hE3 : ∀ a ∈ E, a ^ 3 = 1) :
    Nat.card E ≤ 3 := by
  have hinj := conj_injective_of_center_eq_bot hZ
  set E' := E.comap (MulAut.conj : X →* MulAut X) with hE'
  have hmap : E'.map (MulAut.conj : X →* MulAut X) = E := by
    rw [hE', Subgroup.map_comap_eq, inf_eq_right.mpr hE]
  have hcard : Nat.card E' = Nat.card E := by
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  rw [← hcard]
  refine card_le_three_of_isCyclic_sylow hcyc fun a ha => hinj ?_
  rw [map_pow, map_one]
  exact hE3 _ ha

end Cyclic

section Inner

theorem mem_range_conj_of_mem_linearAutGroup {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F % 3 = 2) {α : MulAut (projectiveSL 3 F)} (hα : α ∈ linearAutGroup 3 F) :
    α ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
  rw [linearAutGroup_eq_range] at hα
  obtain ⟨g, rfl⟩ := hα
  set q := Nat.card F with hq
  set d : Fˣ := GeneralLinearGroup.det g with hd
  have hq1 : 2 ≤ q := by omega
  have hdq : d ^ (q - 1) = 1 := by
    classical
    have := Fintype.ofFinite F
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hq, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ d.ne_zero
  set u : Fˣ := d ^ ((2 * q - 1) / 3) with hu
  have hu3 : u ^ 3 = d := by
    rw [hu, ← pow_mul, show (2 * q - 1) / 3 * 3 = 2 * (q - 1) + 1 by omega, pow_succ, pow_mul',
      hdq, one_pow, one_mul]
  set g' : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g with hg'
  have hdet' : GeneralLinearGroup.det g' = 1 := by
    rw [hg', map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hd, inv_pow, hu3,
      inv_mul_cancel]
  set s : SpecialLinearGroup (Fin 3) F :=
    ⟨(g' : Matrix (Fin 3) (Fin 3) F), by
      rw [← GeneralLinearGroup.val_det_apply, hdet', Units.val_one]⟩ with hs
  have hgs : SpecialLinearGroup.toGL s = g' := Units.ext rfl
  have hconj : conjAut 3 F g = conjAut 3 F g' := by
    rw [hg', map_mul, conjAut_scalar, one_mul]
  refine ⟨proj 3 F s, ?_⟩
  rw [conj_proj_eq_conjAut, hgs, hconj]

theorem mem_range_conj_of_mem_psuConj_range {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : p ^ f % 3 = 1) {β : MulAut (unitaryPSU h 3)}
    (hβ : β ∈ (psuConj h).range) :
    β ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  obtain ⟨A, rfl⟩ := hβ
  set d : Kˣ := GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hN : h.norm (d : K) = 1 := by
    rw [hd, GeneralLinearGroup.val_det_apply]
    exact norm_det_of_mem_unitaryIsom3 A.2
  have hdq : d ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, mul_comm]
    exact hN
  set u : Kˣ := d ^ ((p ^ f + 2) / 3) with hu
  have hu3 : u ^ 3 = d := by
    rw [hu, ← pow_mul, show (p ^ f + 2) / 3 * 3 = (p ^ f + 1) + 1 by omega, pow_succ, hdq,
      one_mul]
  have huN : h.norm (u : K) = 1 := by
    have hpow : (u : K) * h.bar (u : K) = ((d : K) * h.bar (d : K)) ^ ((p ^ f + 2) / 3) := by
      rw [hu, Units.val_pow_eq_pow_val, mul_pow, map_pow]
    rw [UnitaryFieldData.norm, hpow, ← UnitaryFieldData.norm, hN, one_pow]
  exact psuConj_mem_range_conj_of_det_eq_pow huN (by rw [← hd]; exact hu3.symm)

end Inner

section Field

theorem three_dvd_of_elemAbelian_linear {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 2) {E : Subgroup (MulAut (projectiveSL 3 (GaloisField p f)))}
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE9 : 9 ≤ Nat.card E) : 3 ∣ f := by
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  by_contra h3f
  have hlin : E ≤ (MulAut.conj : projectiveSL 3 (GaloisField p f) →*
      MulAut (projectiveSL 3 (GaloisField p f))).range := by
    intro α hα
    by_cases hD : α ∈ linearAutGroup 3 (GaloisField p f)
    · exact mem_range_conj_of_mem_linearAutGroup (by rw [hFcard]; exact hq) hD
    · exfalso
      obtain ⟨σ, hσ, -⟩ := linear_order_three_field_descent le_rfl α (hE3 α hα) hD
      exact h3f (eq_frobenius_pow_of_orderOf_eq_three (Fact.out : p.Prime) hf hFcard hσ).1
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p f)
  have hcyc : ∀ Q : Sylow 3 (projectiveSL 3 (GaloisField p f)), IsCyclic Q :=
    isCyclic_sylow_three_of_mulEquiv_projSL (by rw [hFcard]; exact hq) φ.symm
  have := card_le_three_of_le_inn hcyc
    (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot le_rfl) hlin hE3
  omega

theorem three_dvd_of_elemAbelian_unitary {p f : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData p f (GaloisField p (2 * f))) (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE9 : 9 ≤ Nat.card E) :
    3 ∣ f := by
  have hKcard : Nat.card (GaloisField p (2 * f)) = p ^ (2 * f) := h.card
  by_contra h3f
  have hinn : E ≤ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
    intro β hβ
    by_cases hD : β ∈ (psuConj h).range
    · exact mem_range_conj_of_mem_psuConj_range hq hD
    · exfalso
      obtain ⟨σ, hσ, -⟩ := unitary_order_three_field_descent hq2 β (hE3 β hβ) hD
      have h3 := (eq_frobenius_pow_of_orderOf_eq_three (Fact.out : p.Prime) (by omega) hKcard
        hσ).1
      exact h3f (by omega)
  obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  have hcyc : ∀ Q : Sylow 3 (unitaryPSU h 3), IsCyclic Q :=
    isCyclic_sylow_three_of_mulEquiv_projSU (by omega) hq φ
  have := card_le_three_of_le_inn hcyc (center_unitaryPSU_three_eq_bot h hq2) hinn hE3
  omega

theorem card_map_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (E : Subgroup (MulAut X)) :
    Nat.card (E.map (MulAut.congr e).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.congr e).injective

end Field

@[expose] def IsTypeEpsCube (X : Type) [Group X] : Prop :=
  ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧ 3 ∣ f ∧
    ((p ^ f % 3 = 2 ∧ Nonempty (X ≃* projSL 3 (GaloisField p f))) ∨
      (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧ Nonempty (X ≃* projSU 3 p f)))

theorem isTypeEpsCube_of_cfgSEps {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    {σ : MulAut S} {K : Subgroup S} (hc : CfgSEps S A σ K) :
    IsTypeEpsCube (K ⧸ CFSG.pCore 2 K) := by
  set ρ := actQ hc.map_mem with hρ
  have h9 := nine_le_card_range_actQ hc
  have h3 : ∀ α ∈ ρ.range, α ^ 3 = 1 := fun α hα => pow_three_of_mem_range_actQ hc hα
  obtain ⟨p, f, hp, hp3, hf, ⟨hq, ⟨ψ⟩⟩ | ⟨hq, hq2, ⟨ψ⟩⟩⟩ := hc.isType
  · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p f)
    set e := ψ.trans φ with he
    have h3f : 3 ∣ f := by
      refine three_dvd_of_elemAbelian_linear hf hq (E := ρ.range.map (MulAut.congr e).toMonoidHom)
        ?_ (by rw [card_map_congr]; exact h9)
      rintro _ ⟨α, hα, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, h3 α hα, map_one]
    exact ⟨p, f, hp, hp3, hf, h3f, Or.inl ⟨hq, ⟨ψ⟩⟩⟩
  · have hK : UnitaryFieldData p f (GaloisField p (2 * f)) :=
      ⟨hp.out, hf, GaloisField.card p (2 * f) (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU hK
    set e := ψ.trans φ.symm with he
    have h3f : 3 ∣ f := by
      refine three_dvd_of_elemAbelian_unitary hK hq hq2
        (E := ρ.range.map (MulAut.congr e).toMonoidHom) ?_ (by rw [card_map_congr]; exact h9)
      rintro _ ⟨α, hα, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, h3 α hα, map_one]
    exact ⟨p, f, hp, hp3, hf, h3f, Or.inr ⟨hq, hq2, ⟨ψ⟩⟩⟩

end CFSG.RankThree.PartTwo.Sec4.RonanEps

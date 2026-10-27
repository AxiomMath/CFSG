module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelCoords

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace UnitModel

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F]

theorem frameActs_inv {φ : ↥(unitarySU 2 f F n) →* G} {b : G} {τ : Fin n → Fˣ}
    (hb : SURep.GGFrameActs φ b τ) : SURep.GGFrameActs φ b⁻¹ τ⁻¹ := by
  refine ⟨SURep.norm_inv_eq_one hb.1, fun s s' hs' => ?_⟩
  have h1 := hb.2 s' s (by rw [hs', map_inv]; group)
  calc b⁻¹ * φ s * b⁻¹⁻¹ = b⁻¹ * (b * φ s' * b⁻¹) * b := by rw [h1, inv_inv]
    _ = φ s' := by group

theorem frameActs_of_scalar {φ : ↥(unitarySU 2 f F n) →* G} {g : G} {τ : Fin n → Fˣ} {c : Fˣ}
    (hg : SURep.GGFrameActs φ g (fun i => c * τ i)) (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) :
    SURep.GGFrameActs φ g τ := by
  refine ⟨hτ, fun s s' hs' => hg.2 s s' ?_⟩
  rw [hs']
  have h1 : diagHom n (fun i => c * τ i) =
      GeneralLinearGroup.scalar (Fin n) c * diagHom n τ := by
    apply Units.ext
    rw [coe_diagHom, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagHom, scalar_apply,
      diagonal_mul_diagonal]
    simp
  have hc : ∀ X : GL (Fin n) F, GeneralLinearGroup.scalar (Fin n) c * X =
      X * GeneralLinearGroup.scalar (Fin n) c := fun X => (TypeA.PGLTor.commute_scalar c X).eq
  rw [h1, _root_.mul_inv_rev,
    show GeneralLinearGroup.scalar (Fin n) c * diagHom n τ * (s : GL (Fin n) F) *
        ((diagHom n τ)⁻¹ * (GeneralLinearGroup.scalar (Fin n) c)⁻¹) =
      GeneralLinearGroup.scalar (Fin n) c * (diagHom n τ * (s : GL (Fin n) F) * (diagHom n τ)⁻¹) *
        (GeneralLinearGroup.scalar (Fin n) c)⁻¹ by group, hc, mul_inv_cancel_right]

variable (p : ℕ) (h : UnitaryFieldData 2 f F) (φ : ↥(unitarySU 2 f F n) →* G) in
@[expose] def frameTorus : Subgroup G where
  carrier := {g | ∃ τ : Fin n → Fˣ, (∀ i, τ i ^ p = 1) ∧ SURep.GGFrameActs φ g τ}
  one_mem' := ⟨1, fun _ => one_pow _, SURep.frameActs_one φ⟩
  mul_mem' := by
    rintro a b ⟨τ, hτ, ha⟩ ⟨τ', hτ', hb⟩
    exact ⟨τ * τ', fun i => by rw [Pi.mul_apply, mul_pow, hτ, hτ', one_mul], ha.mul h hb⟩
  inv_mem' := by
    rintro a ⟨τ, hτ, ha⟩
    exact ⟨τ⁻¹, fun i => by rw [Pi.inv_apply, inv_pow, hτ, inv_one], frameActs_inv ha⟩

theorem eq_one_of_frameActs_one {φ : ↥(unitarySU 2 f F n) →* G}
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {g : G}
    (hg : SURep.GGFrameActs φ g 1) : g = 1 := by
  apply SURep.eq_of_act_eqU hcent
  intro s
  rw [hg.2 s s (by rw [map_one, one_mul, inv_one, mul_one]), one_mul, inv_one, mul_one]

theorem frameTorus_le {p : ℕ} (h : UnitaryFieldData 2 f F) {φ : ↥(unitarySU 2 f F n) →* G}
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBs : ∀ b ∈ Bs, SURep.GGFrameDiagU φ b)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    frameTorus p h φ ≤ Bs := by
  rintro g ⟨τ, hτ, hg⟩
  apply hom g
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨τ', hb'⟩ := hBs b hb
    exact (SURep.commute_of_frameActs h hcent hg hb').symm
  · have h1 := hg.pow h p
    rw [show τ ^ p = 1 from funext hτ] at h1
    exact eq_one_of_frameActs_one hcent h1

theorem card_le_card_frameTorus [Finite G] {m p : ℕ} [NeZero p] (h : UnitaryFieldData 2 f F)
    (hn : 3 ≤ m + 1) {φ : ↥(unitarySU 2 f F (m + 1)) →* G} (hker : SURep.GGFrameKer φ)
    {ω : Fˣ} (hω : IsPrimitiveRoot ω p)
    (hreal : ∀ a : Fin (m + 1) → ZMod p, ∃ g : G,
      SURep.GGFrameActs φ g (fun i => ω ^ (a i).val)) :
    p ^ m ≤ Nat.card (frameTorus p h φ) := by
  choose g hg using hreal
  have hmem : ∀ a, g a ∈ frameTorus p h φ := fun a =>
    ⟨_, fun i => by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], hg a⟩
  have hinj : Function.Injective (fun x : Fin m → ZMod p =>
      (⟨g (Fin.cons 0 x), hmem _⟩ : frameTorus p h φ)) := by
    intro x y hxy
    have hgxy : g (Fin.cons 0 x) = g (Fin.cons 0 y) := congrArg Subtype.val hxy
    have h1 := hg (Fin.cons 0 y)
    rw [← hgxy] at h1
    funext k
    have h2 := SURep.ratio_eq_of_frameActs hker h hn (hg (Fin.cons 0 x)) h1 k.succ 0
    simp only [Fin.cons_succ, Fin.cons_zero, ZMod.val_zero, pow_zero, mul_one, one_mul] at h2
    exact LinModel.pow_val_injective hω h2
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_fun] using this

theorem exists_frameActs_of_pow_eq {p : ℕ} (h : UnitaryFieldData 2 f F) (hnp : n = p)
    (φ : ↥(unitarySU 2 f F n) →* G) {ω ζ' : Fˣ} (hζ' : ζ' ^ p = ω)
    (hζ'N : (ζ' : F) ^ (2 ^ f + 1) = 1) (a : Fin n → ZMod p) :
    ∃ g : G, SURep.GGFrameActs φ g (fun i => ω ^ (a i).val) := by
  have hpow : ∀ u : Fˣ, u ^ n = u ^ p := fun u => by rw [hnp]
  have hωN : (ω : F) ^ (2 ^ f + 1) = 1 := by
    rw [← hζ', Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hζ'N, one_pow]
  set c : Fˣ := ζ' ^ (∑ i, (a i).val) with hc
  have hcN : (c : F) ^ (2 ^ f + 1) = 1 := by
    rw [hc, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hζ'N, one_pow]
  set δ : Fin n → Fˣ := fun i => c⁻¹ * ω ^ (a i).val with hδ
  have hτN : ∀ i, ((ω ^ (a i).val : Fˣ) : F) ^ (2 ^ f + 1) = 1 := fun i => by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hωN, one_pow]
  have hδN : ∀ i, (δ i : F) ^ (2 ^ f + 1) = 1 := fun i => by
    rw [hδ, Units.val_mul, mul_pow, hτN i, Units.val_inv_eq_inv_val, inv_pow, hcN, inv_one,
      one_mul]
  have hδprod : ∏ i, δ i = 1 := by
    rw [hδ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hpow,
      Finset.prod_pow_eq_pow_sum, hc, inv_pow, ← pow_mul, mul_comm (∑ i, (a i).val) p, pow_mul,
      hζ', inv_mul_cancel]
  refine ⟨φ ⟨diagHom n δ, SURep.diagHom_mem_unitarySU' h hδN hδprod⟩,
    frameActs_of_scalar (c := c⁻¹) (SURep.frameActs_map φ rfl hδN) hτN⟩

theorem mem_suPairs_coe (φ : ↥(unitarySU 2 f F n) →* G) (s : ↥(unitarySU 2 f F n)) :
    (φ s, (s : GL (Fin n) F)) ∈ SUTorus.suPairs φ := by
  refine ⟨Subgroup.le_normalizer s.2, fun u v hv => ?_⟩
  have : v = s * u * s⁻¹ := Subtype.ext (by rw [hv]; rfl)
  rw [this, map_mul, map_mul, map_inv]

theorem det_pow_eq_one_of_mem (h : UnitaryFieldData 2 f F) {B : GL (Fin n) F}
    (hB : B ∈ primeFormUnitary h (idGram F n)) :
    GeneralLinearGroup.det B ^ (2 ^ f + 1) = 1 := by
  apply Units.ext
  have h1 := mem_primeFormUnitary.mp hB
  rw [idGram, Units.val_one, Matrix.mul_one] at h1
  have h2 := congrArg Matrix.det h1
  have h3 : ((B : Matrix (Fin n) (Fin n) F).map h.bar).det = h.bar (B : Matrix (Fin n) (Fin n) F).det :=
    (RingHom.map_det h.bar _).symm
  rw [Matrix.det_mul, Matrix.det_transpose, h3, Matrix.det_one, h.bar_apply] at h2
  rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one, pow_succ]
  exact h2

theorem exists_frameActs_of_det [Finite F] {p : ℕ} (h : UnitaryFieldData 2 f F) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hnp : n = p) {φ : ↥(unitarySU 2 f F n) →* G}
    {g₀ : G} {A₀ : GL (Fin n) F} (hA₀U : A₀ ∈ primeFormUnitary h (idGram F n))
    (h₀ : (g₀, A₀) ∈ SUTorus.suPairs φ) (hdet : ¬ ∃ c : Fˣ, c ^ p = GeneralLinearGroup.det A₀)
    {τ : Fin n → Fˣ} (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) :
    ∃ g : G, SURep.GGFrameActs φ g τ := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpow : ∀ u : Fˣ, u ^ n = u ^ p := fun u => by rw [hnp]
  set x : TypeA.PGLTor.PowQuot F p := QuotientGroup.mk (GeneralLinearGroup.det A₀) with hx
  have hx1 : x ≠ 1 := fun h' => hdet (TypeA.PGLTor.powQuot_mk_eq_one_iff.mp h')
  have hxp : x ^ p = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨_, rfl⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have htop : Subgroup.zpowers x = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, hord]
    exact TypeA.PGLTor.card_powQuot_le
  have hmem : (QuotientGroup.mk (GeneralLinearGroup.det (diagHom n τ)) :
      TypeA.PGLTor.PowQuot F p) ∈ Subgroup.zpowers x := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [hx, ← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
  obtain ⟨c, hc⟩ := hk
  have hc' : c ^ p = (GeneralLinearGroup.det A₀ ^ k)⁻¹ * GeneralLinearGroup.det (diagHom n τ) :=
    hc
  have hdA : GeneralLinearGroup.det A₀ ^ (2 ^ f + 1) = 1 := det_pow_eq_one_of_mem h hA₀U
  have hdD : GeneralLinearGroup.det (diagHom n τ) ^ (2 ^ f + 1) = 1 := by
    have hτu : ∀ i, τ i ^ (2 ^ f + 1) = 1 := fun i =>
      Units.ext (by rw [Units.val_pow_eq_pow_val, hτ i, Units.val_one])
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, det_diagHom,
      ← Finset.prod_pow, Units.val_one]
    exact Finset.prod_eq_one fun i _ => hτ i
  have hcN : c ^ (2 ^ f + 1) = 1 := SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hc' (by
    rw [mul_pow, inv_pow, hdD, mul_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm k,
      _root_.zpow_mul, zpow_natCast, hdA, _root_.one_zpow, inv_one])
  set S := GeneralLinearGroup.scalar (Fin n) c⁻¹ * diagHom n τ * A₀ ^ (-k) with hS
  have hSU : S ∈ primeFormUnitary h (idGram F n) := by
    have hne : NeZero n := ⟨by rw [hnp]; exact hp.ne_zero⟩
    refine (primeFormUnitary h _).mul_mem ((primeFormUnitary h _).mul_mem ?_ ?_)
      ((primeFormUnitary h _).zpow_mem hA₀U _)
    · rw [SUTorus.scalar_mem_primeFormUnitary_iff, h.bar_apply]
      have h1 : ((c⁻¹ : Fˣ) : F) ^ (2 ^ f + 1) = 1 := by
        rw [← Units.val_pow_eq_pow_val, inv_pow, hcN, inv_one, Units.val_one]
      rwa [pow_succ] at h1
    · rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
      exact CFSG.RankThree.Classical2.diagHom_unitary h hτ
  have hdetsc : ∀ u : Fˣ, GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) u) = u ^ n :=
    fun u => by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Units.val_pow_eq_pow_val]
  have hdD' : GeneralLinearGroup.det (diagHom n τ) = GeneralLinearGroup.det A₀ ^ k * c ^ p := by
    rw [hc']
    group
  have hSdet : GeneralLinearGroup.det S = 1 := by
    rw [hS, map_mul, map_mul, map_zpow, hdetsc, hpow, hdD',
      mul_comm (GeneralLinearGroup.det A₀ ^ k) (c ^ p)]
    group
  have hSSU : S ∈ unitarySU 2 f F n := by
    rw [mem_unitarySU_iff h]
    refine ⟨by rw [← GeneralLinearGroup.val_det_apply, hSdet, Units.val_one], ?_⟩
    have h1 := mem_primeFormUnitary.mp hSU
    rwa [idGram, Units.val_one, Matrix.mul_one] at h1
  have hg := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem
    (SUTorus.one_scalar_mem_suPairs φ c) (mem_suPairs_coe φ ⟨S, hSSU⟩))
    ((SUTorus.suPairs φ).zpow_mem h₀ k)
  rw [Prod.pow_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul] at hg
  have hD : GeneralLinearGroup.scalar (Fin n) c * S * A₀ ^ k = diagHom n τ := by
    rw [hS, ← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul, mul_assoc,
      ← _root_.zpow_add, neg_add_cancel, _root_.zpow_zero, mul_one]
  rw [hD] at hg
  exact ⟨_, hτ, fun s s' hs' => hg.2 s s' hs'⟩

end UnitModel

end CFSG.StandardType

module

public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndex
public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesAlt
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Cyclic

variable {Q : Type*} [Group Q]

theorem mem_zpowers_of_pow_three_eq_one [IsCyclic Q] {x y : Q} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy3 : y ^ 3 = 1) : y ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hfx : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hx3⟩
  have hfy : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hy3⟩
  have : Finite (Subgroup.zpowers x) := hfx.finite_zpowers
  have : Finite (Subgroup.zpowers y) := hfy.finite_zpowers
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoy])
  rw [← heq]
  exact Subgroup.mem_zpowers y

theorem exists_lt_three_pow_mul_eq_one {x y : Q} (hx3 : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : ∃ k < 3, x ^ k * y = 1 := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨w, hw⟩ : ∃ w : ℤ, (((-z) % 3).toNat : ℤ) + z = 3 * w := ⟨-((-z) / 3), by omega⟩
  refine ⟨((-z) % 3).toNat, by omega, ?_⟩
  rw [← zpow_natCast, ← zpow_add, hw, zpow_mul, zpow_ofNat, hx3, one_zpow]

end Cyclic

section OutThree

variable {M N : Type*} [Group M] [Group N]

@[expose] def OutThreeCyclic (M : Type*) [Group M] : Prop :=
  ∀ α β : MulAut M, Commute α β → α ^ 3 = 1 → β ^ 3 = 1 → ¬ IsInnerAut α →
    ∃ k < 3, IsInnerAut (α ^ k * β)

theorem OutThreeCyclic.of_hom (hN : OutThreeCyclic N) (D : MulAut M →* MulAut N)
    (hD : ∀ τ, IsInnerAut (D τ) ↔ IsInnerAut τ) : OutThreeCyclic M := by
  intro α β hαβ hα hβ hαin
  obtain ⟨k, hk, h⟩ := hN (D α) (D β) (hαβ.map D) (by rw [← map_pow, hα, map_one])
    (by rw [← map_pow, hβ, map_one]) (fun h => hαin ((hD α).mp h))
  exact ⟨k, hk, (hD _).mp (by rwa [map_mul, map_pow])⟩

theorem OutThreeCyclic.of_mulEquiv (hN : OutThreeCyclic N) (e : M ≃* N) : OutThreeCyclic M :=
  hN.of_hom (MulAut.congr e).toMonoidHom fun τ => isInnerAut_congr e τ

theorem outThreeCyclic_of_isCyclic (h : IsCyclic (Outer M)) : OutThreeCyclic M := by
  intro α β _ hα hβ hαin
  have hα1 : (QuotientGroup.mk α : Outer M) ≠ 1 := fun h1 =>
    hαin ((QuotientGroup.eq_one_iff (N := inner M) α).mp h1)
  have hα3 : (QuotientGroup.mk α : Outer M) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hβ3 : (QuotientGroup.mk β : Outer M) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  obtain ⟨k, hk, h1⟩ := exists_lt_three_pow_mul_eq_one hα3
    (mem_zpowers_of_pow_three_eq_one hα3 hα1 hβ3)
  refine ⟨k, hk, ?_⟩
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul] at h1
  exact (QuotientGroup.eq_one_iff (N := inner M) _).mp h1

theorem isCyclic_outer_of_normalForm {Γ : Type*} [Group Γ] [IsCyclic Γ] (ψ : Γ →* MulAut M)
    (h : ∀ α : MulAut M, ∃ (m : M) (γ : Γ), α = MulAut.conj m * ψ γ) :
    IsCyclic (Outer M) := by
  refine isCyclic_of_surjective ((QuotientGroup.mk' (inner M)).comp ψ) fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H α =>
    obtain ⟨m, γ, rfl⟩ := h α
    refine ⟨γ, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (N := inner M) _).mpr ⟨m, rfl⟩, one_mul]

theorem isCyclic_range {Γ G : Type*} [Group Γ] [Group G] [IsCyclic Γ] (ψ : Γ →* G) :
    IsCyclic ψ.range :=
  isCyclic_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective

end OutThree

theorem exists_pow_mul_mem_range_pow_three {G : Type*} [CommGroup G] [IsCyclic G] {u : G}
    (hu : u ∉ (powMonoidHom 3 : G →* G).range) (v : G) :
    ∃ k < 3, u ^ k * v ∈ (powMonoidHom 3 : G →* G).range := by
  set C := (powMonoidHom 3 : G →* G).range
  have h3 : ∀ x : G, (QuotientGroup.mk x : G ⧸ C) ^ 3 = 1 := fun x => by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  have hu1 : (QuotientGroup.mk u : G ⧸ C) ≠ 1 := fun h => hu ((QuotientGroup.eq_one_iff u).mp h)
  have : IsCyclic (G ⧸ C) :=
    isCyclic_of_surjective (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
  obtain ⟨k, hk, h1⟩ := exists_lt_three_pow_mul_eq_one (h3 u)
    (mem_zpowers_of_pow_three_eq_one (h3 u) hu1 (h3 v))
  refine ⟨k, hk, ?_⟩
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem mod_three_eq_one_of_pow_three {r : ℕ} (hr : r ^ 3 % 3 = 1) : r % 3 = 1 := by
  rw [Nat.pow_mod] at hr
  rcases (by omega : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2) with h | h | h <;> simp [h] at hr ⊢

theorem exists_pow_three_mul_add_one_of_orderOf_eq_three {K : Type*} [Field K] [Finite K]
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (h3 : 3 ∣ Nat.card Kˣ) :
    ∃ s : ℕ, ∀ x : K, σ x = x ^ (3 * s + 1) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hf3, hσr⟩ := eq_frobenius_pow_of_orderOf_eq_three hp f.pos hK hσ
  have hq : p ^ (f : ℕ) % 3 = 1 := by
    rw [Nat.card_units, hK] at h3
    have : 1 ≤ p ^ (f : ℕ) := Nat.one_le_pow _ _ hp.pos
    omega
  rcases hσr with hσr | hσr
  · have hr : p ^ ((f : ℕ) / 3) % 3 = 1 := mod_three_eq_one_of_pow_three (by
      rw [← pow_mul, Nat.div_mul_cancel hf3, hq])
    exact ⟨p ^ ((f : ℕ) / 3) / 3, fun x => by rw [hσr x]; congr 1; omega⟩
  · have hr : p ^ (2 * (f : ℕ) / 3) % 3 = 1 := mod_three_eq_one_of_pow_three (by
      rw [← pow_mul, show 2 * (f : ℕ) / 3 * 3 = (f : ℕ) * 2 by omega, pow_mul, Nat.pow_mod, hq])
    exact ⟨p ^ (2 * (f : ℕ) / 3) / 3, fun x => by rw [hσr x]; congr 1; omega⟩

theorem mul_inv_pow_three_mul_add_one {G : Type*} [Group G] (x : G) (s : ℕ) :
    x * x⁻¹ ^ (3 * s + 1) = (x ^ s)⁻¹ ^ 3 := by
  group

section Pinned

variable {M : Type*} [Group M] (P : PinnedAut M)

theorem pow_three_eq_one_of_conj {d φ : MulAut M} (h : (d * φ * d⁻¹) ^ 3 = 1) : φ ^ 3 = 1 := by
  rw [conj_pow] at h
  calc φ ^ 3 = d⁻¹ * (d * φ ^ 3 * d⁻¹) * d := by group
    _ = 1 := by rw [h]; group

theorem outThreeCyclic_of_pinned (hnorm : P.inndiag.Normal)
    (hkind : ∀ τ : MulAut M, τ ^ 3 = 1 → τ ∉ P.inndiag → P.IsField τ)
    (hcyc : IsCyclic P.field)
    (hdiag : ∀ δ₁ ∈ P.inndiag, ∀ δ₂ ∈ P.inndiag, δ₁ ^ 3 = 1 → δ₂ ^ 3 = 1 → ¬ IsInnerAut δ₁ →
      ∃ k < 3, IsInnerAut (δ₁ ^ k * δ₂))
    (hcent : ∀ φ ∈ P.field, φ ≠ 1 → φ ^ 3 = 1 → ∀ δ ∈ P.inndiag, δ ^ 3 = 1 → Commute δ φ →
      IsInnerAut δ) :
    OutThreeCyclic M := by
  have key : ∀ γ δ : MulAut M, P.IsField γ → γ ^ 3 = 1 → δ ∈ P.inndiag → δ ^ 3 = 1 →
      Commute δ γ → IsInnerAut δ := by
    rintro γ δ ⟨φ, hφ, hφ1, d, hd, rfl⟩ hγ3 hδ hδ3 hcomm
    have hφ3 : φ ^ 3 = 1 := pow_three_eq_one_of_conj hγ3
    have h1 : d⁻¹ * δ * d ∈ P.inndiag := mul_mem (mul_mem (inv_mem hd) hδ) hd
    have h2 : (d⁻¹ * δ * d) ^ 3 = 1 := by
      have h := conj_pow (a := d⁻¹) (b := δ) (i := 3)
      rw [inv_inv] at h
      rw [h, hδ3]
      group
    have h3 : Commute (d⁻¹ * δ * d) φ := by
      have hc := hcomm.eq
      change d⁻¹ * δ * d * φ = φ * (d⁻¹ * δ * d)
      calc d⁻¹ * δ * d * φ = d⁻¹ * (δ * (d * φ * d⁻¹)) * d := by group
        _ = d⁻¹ * ((d * φ * d⁻¹) * δ) * d := by rw [hc]
        _ = φ * (d⁻¹ * δ * d) := by group
    have h5 := (isInnerAut_conj_iff d (d⁻¹ * δ * d)).mpr (hcent φ hφ hφ1 hφ3 _ h1 h2 h3)
    rwa [show d * (d⁻¹ * δ * d) * d⁻¹ = δ by group] at h5
  intro α β hαβ hα3 hβ3 hαin
  by_contra hcon
  push Not at hcon
  have hpow3 : ∀ k : ℕ, (α ^ k * β) ^ 3 = 1 := fun k => by
    rw [(hαβ.pow_left k).mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hα3, one_pow, one_mul, hβ3]
  by_cases hαD : α ∈ P.inndiag
  · by_cases hβD : β ∈ P.inndiag
    · obtain ⟨k, hk, h⟩ := hdiag α hαD β hβD hα3 hβ3 hαin
      exact hcon k hk h
    · exact hαin (key β α (hkind β hβ3 hβD) hβ3 hαD hα3 hαβ)
  · have hαF := hkind α hα3 hαD
    by_cases hex : ∃ k < 3, α ^ k * β ∈ P.inndiag
    · obtain ⟨k, hk, hD⟩ := hex
      exact hcon k hk (key α _ hαF hα3 hD (hpow3 k)
        (((Commute.refl α).pow_left k).mul_left hαβ.symm))
    · push Not at hex
      have hβD : β ∉ P.inndiag := by simpa using hex 0 (by norm_num)
      obtain ⟨φ, hφ, hφ1, d, hd, hαeq⟩ := hαF
      obtain ⟨φ', hφ', -, d', hd', hβeq⟩ := hkind β hβ3 hβD
      have hφ3 : φ ^ 3 = 1 := pow_three_eq_one_of_conj (hαeq ▸ hα3)
      have hφ'3 : φ' ^ 3 = 1 := pow_three_eq_one_of_conj (hβeq ▸ hβ3)
      have hmem : (⟨φ', hφ'⟩ : P.field) ∈ Subgroup.zpowers (⟨φ, hφ⟩ : P.field) :=
        mem_zpowers_of_pow_three_eq_one (Subtype.ext (by simpa using hφ3))
          (fun h => hφ1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hφ'3))
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hφz : φ ^ z = φ' := by
        have := congrArg Subtype.val hz
        simpa using this
      have := hnorm
      set π := QuotientGroup.mk' P.inndiag with hπ
      have hconj : ∀ e ψ : MulAut M, e ∈ P.inndiag → π (e * ψ * e⁻¹) = π ψ := by
        intro e ψ he
        have he1 : π e = 1 := (QuotientGroup.eq_one_iff (N := P.inndiag) e).mpr he
        rw [map_mul, map_mul, map_inv, he1, one_mul, inv_one, mul_one]
      have hπα : π α = π φ := by rw [hαeq, hconj d φ hd]
      have hπβ : π β = π α ^ z := by rw [hβeq, hconj d' φ' hd', hπα, ← map_zpow, hφz]
      have hπα3 : π α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
      obtain ⟨k, hk, h1⟩ := exists_lt_three_pow_mul_eq_one hπα3 (Subgroup.mem_zpowers_iff.mpr
        ⟨z, hπβ.symm⟩)
      rw [← map_pow, ← map_mul] at h1
      exact hex k hk ((QuotientGroup.eq_one_iff (N := P.inndiag) _).mp h1)

theorem outThreeCyclic_of_pinned_cube (hnorm : P.inndiag.Normal)
    (hkind : ∀ τ : MulAut M, τ ^ 3 = 1 → τ ∉ P.inndiag → P.IsField τ)
    (hcyc : IsCyclic P.field) (hcube : ∀ δ ∈ P.inndiag, δ ^ 3 = 1 → IsInnerAut δ) :
    OutThreeCyclic M :=
  outThreeCyclic_of_pinned P hnorm hkind hcyc
    (fun _ _ δ₂ hδ₂ _ h₂ _ => ⟨0, by norm_num, by rw [pow_zero, one_mul]; exact hcube δ₂ hδ₂ h₂⟩)
    (fun _ _ _ _ δ hδ hδ3 _ => hcube δ hδ hδ3)

end Pinned

section Models

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem isCyclic_ringEquiv_of_finite (K : Type) [Field K] [Finite K] : IsCyclic (K ≃+* K) :=
  ringAut_isCyclic

theorem outThreeCyclic_psl2 (K : Type) [Field K] [Finite K] : OutThreeCyclic (PSL2 K) := by
  have := isCyclic_ringEquiv_of_finite K
  refine outThreeCyclic_of_pinned_cube (stdPinnedPSL2 K) stdPinnedPSL2_stable.normal
    (fun τ hτ3 hτD => ?_) (isCyclic_range _) psl2_inndiag_cube
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isField_psl2_of_orderOf_prime Nat.prime_three (orderOf_eq_prime hτ3 ?_) hτD
  rintro rfl
  exact hτD (one_mem _)

theorem outThreeCyclic_psp4Even (F : Type) [Field F] [Finite F] [CharP F 2] :
    OutThreeCyclic (StatedProj (StatedSp 2 F)) := by
  have := isCyclic_ringEquiv_of_finite F
  exact outThreeCyclic_of_pinned_cube (stdPinnedPSp4Even F) range_conjAut_normal_of_charTwo
    (fun τ hτ3 hτD => isField_psp4Even_of_pow_three_eq_one hτ3 hτD) (isCyclic_range _)
    psp4Even_inndiag_cube

theorem outThreeCyclic_g2
    (K : Type) [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) : OutThreeCyclic (adjointGroup Tag.G2 K) := by
  have := isCyclic_ringEquiv_of_finite K
  exact outThreeCyclic_of_isCyclic
    (isCyclic_outer_of_normalForm (g2FieldHom K) (g2_automorphism_normal_form hK3 hK4).1)

theorem outThreeCyclic_sz {a : ℕ} {K : Type} [Field K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) : OutThreeCyclic (suzukiGroup a K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := isCyclic_ringEquiv_of_finite K
  exact outThreeCyclic_of_isCyclic
    (isCyclic_outer_of_normalForm _ (exists_conj_mul_szFieldAut ha hK))

theorem outThreeCyclic_largeRee
    {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    OutThreeCyclic (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := by
  have := isCyclic_ringEquiv_of_finite K
  exact outThreeCyclic_of_isCyclic
    (isCyclic_outer_of_normalForm (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAutHom K a)
      (largeRee_automorphism_normal_form ha hK).1)

theorem outThreeCyclic_triality
    {f : ℕ} {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    OutThreeCyclic (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have := isCyclic_ringEquiv_of_finite K
  exact outThreeCyclic_of_isCyclic
    (isCyclic_outer_of_normalForm (fieldActorHom (t := TwistTag.D4) σ)
      (exists_conj_mul_fieldActor hf hK hσ))

end Models

section PSL3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {K : Type} [Field K]

theorem isInnerAut_conjAut_of_det_mem_range {A : GL (Fin 3) K}
    (hA : GeneralLinearGroup.det A ∈ (powMonoidHom 3 : Kˣ →* Kˣ).range) :
    IsInnerAut (conjAut 3 K A) := by
  obtain ⟨μ, hμ⟩ := hA
  have hdet : ((A * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, GeneralLinearGroup.det_scalar,
      Fintype.card_fin, ← hμ, powMonoidHom_apply, inv_pow, mul_inv_cancel, Units.val_one]
  have h := isInnerAut_conjAut_of_det _ hdet
  rwa [map_mul, conjAut_scalar, mul_one] at h

theorem psl3_inndiag_pair [Finite K] :
    ∀ δ₁ ∈ (stdPinnedPSL 3 K).inndiag, ∀ δ₂ ∈ (stdPinnedPSL 3 K).inndiag, δ₁ ^ 3 = 1 →
      δ₂ ^ 3 = 1 → ¬ IsInnerAut δ₁ → ∃ k < 3, IsInnerAut (δ₁ ^ k * δ₂) := by
  intro δ₁ h₁ δ₂ h₂ _ _ hin
  rw [stdPinnedPSL_inndiag, mem_linearAutGroup_iff] at h₁ h₂
  obtain ⟨A₁, rfl⟩ := h₁
  obtain ⟨A₂, rfl⟩ := h₂
  obtain ⟨k, hk, hmem⟩ := exists_pow_mul_mem_range_pow_three
    (fun h => hin (isInnerAut_conjAut_of_det_mem_range h)) (GeneralLinearGroup.det A₂)
  refine ⟨k, hk, ?_⟩
  rw [← map_pow, ← map_mul]
  exact isInnerAut_conjAut_of_det_mem_range (by rwa [map_mul, map_pow])

theorem psl3_inndiag_comm_field [Finite K] :
    ∀ φ ∈ (stdPinnedPSL 3 K).field, φ ≠ 1 → φ ^ 3 = 1 → ∀ δ ∈ (stdPinnedPSL 3 K).inndiag,
      δ ^ 3 = 1 → Commute δ φ → IsInnerAut δ := by
  rintro _ ⟨σ, rfl⟩ hφ1 hφ3 δ hδ hδ3 hcomm
  by_cases h3 : 3 ∣ Nat.card Kˣ
  swap
  · exact psl_inndiag_cube (Or.inr h3) δ hδ hδ3
  rw [stdPinnedPSL_inndiag, mem_linearAutGroup_iff] at hδ
  obtain ⟨A, rfl⟩ := hδ
  have hα3 : (conjAut 3 K A * fieldAut 3 K σ) ^ 3 = 1 := by
    rw [hcomm.mul_pow, hδ3, hφ3, one_mul]
  have hαD : conjAut 3 K A * fieldAut 3 K σ ∉ linearAutGroup 3 K := by
    intro hmem
    have h' : fieldAut 3 K σ ∈ linearAutGroup 3 K := by
      have := mul_mem (inv_mem (conjAut_mem_linearAutGroup A)) hmem
      rwa [inv_mul_cancel_left] at this
    rw [fieldAut_mem_linearAutGroup_iff (le_refl 3)] at h'
    exact hφ1 (by rw [h', map_one])
  obtain ⟨τ, hτ3, H, hH⟩ := linear_order_three_field_descent (le_refl 3) _ hα3 hαD
  set B : GL (Fin 3) K := H * GeneralLinearGroup.map (τ : K →+* K) H⁻¹ with hBdef
  have hB : conjAut 3 K A * fieldAut 3 K σ = conjAut 3 K B * fieldAut 3 K τ := by
    rw [hH, hBdef, map_mul, ← map_inv (conjAut 3 K) H, mul_assoc (conjAut 3 K H),
      fieldAut_mul_conjAut, mul_assoc]
  have h2 : conjAut 3 K (B⁻¹ * A) * fieldAut 3 K (σ * τ⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv]
    calc (conjAut 3 K B)⁻¹ * conjAut 3 K A * (fieldAut 3 K σ * (fieldAut 3 K τ)⁻¹) =
        (conjAut 3 K B)⁻¹ * (conjAut 3 K A * fieldAut 3 K σ) * (fieldAut 3 K τ)⁻¹ := by group
      _ = 1 := by rw [hB]; group
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h2
  have hA : A = B * GeneralLinearGroup.scalar (Fin 3) c := by rw [hc]; group
  obtain ⟨s, hs⟩ := exists_pow_three_mul_add_one_of_orderOf_eq_three hτ3 h3
  have hτu : ∀ v : Kˣ, Units.map ((τ : K →+* K) : K →* K) v = v ^ (3 * s + 1) := fun v =>
    Units.ext (by simp [hs])
  apply isInnerAut_conjAut_of_det_mem_range
  refine ⟨(GeneralLinearGroup.det H ^ s)⁻¹ * c, ?_⟩
  rw [powMonoidHom_apply, mul_pow, hA, hBdef, map_mul, map_mul, GeneralLinearGroup.map_det,
    hτu, map_inv, GeneralLinearGroup.det_scalar, Fintype.card_fin, mul_inv_pow_three_mul_add_one]

theorem outThreeCyclic_psl3 (K : Type) [Field K] [Finite K] :
    OutThreeCyclic (projectiveSL 3 K) := by
  have := isCyclic_ringEquiv_of_finite K
  exact outThreeCyclic_of_pinned (stdPinnedPSL 3 K) (stdPinnedPSL_stable (le_refl 3)).normal
    (fun τ hτ3 hτD => isField_of_pow_three_eq_one (le_refl 3) hτ3 hτD) (isCyclic_range _)
    psl3_inndiag_pair psl3_inndiag_comm_field

theorem outThreeCyclic_sl3 (K : Type) [Field K] [Finite K] :
    OutThreeCyclic (SpecialLinearGroup (Fin 3) K) :=
  (outThreeCyclic_psl3 K).of_hom (descendAut 3 K) fun _ => isInnerAut_descendAut_iff (le_refl 3)

end PSL3

section PSU3

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem det_pow_succ_eq_one_of_mem {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) :
    GeneralLinearGroup.det A ^ (p ^ f + 1) = 1 :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_pow_succ_eq_one hA)

theorem scalar_mem_unitaryIsom3_of_pow {v : Kˣ} (hv : v ^ (p ^ f + 1) = 1) :
    GeneralLinearGroup.scalar (Fin 3) v ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  have hv' : h.bar (v : K) * v = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hv, Units.val_one]
  simp only [hv']
  exact Matrix.diagonal_one

theorem isInnerAut_psuConj_of_det_eq_pow_three (A : unitaryIsom3 h) {u : Kˣ}
    (hu3 : u ^ 3 = GeneralLinearGroup.det (A : GL (Fin 3) K)) (hun : u ^ (p ^ f + 1) = 1) :
    IsInnerAut (psuConj h A) := by
  have hsu : GeneralLinearGroup.scalar (Fin 3) u⁻¹ ∈ unitaryIsom3 h :=
    scalar_mem_unitaryIsom3_of_pow h (by rw [inv_pow, hun, inv_one])
  set B : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A with hB
  have hBI : B ∈ unitaryIsom3 h := mul_mem hsu A.2
  have hdet : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hu3, inv_pow,
      inv_mul_cancel]
  have hBSU : B ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨?_, hBI⟩
    rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  have hAB : psuConj h A = psuConj h ⟨B, hBI⟩ := by
    have : (⟨B, hBI⟩ : unitaryIsom3 h) = ⟨_, hsu⟩ * A := rfl
    rw [this, map_mul, psuConj_scalar, one_mul]
  rw [hAB, show (⟨B, hBI⟩ : unitaryIsom3 h) = ⟨(⟨B, hBSU⟩ : unitarySU p f K 3),
    unitarySU_le_unitaryIsom3 hBSU⟩ from rfl, ← conj_mk_eq_psuConj]
  exact isInnerAut_conj _

theorem psu3_inndiag_pair :
    ∀ δ₁ ∈ (stdPinnedPSU3 h).inndiag, ∀ δ₂ ∈ (stdPinnedPSU3 h).inndiag, δ₁ ^ 3 = 1 →
      δ₂ ^ 3 = 1 → ¬ IsInnerAut δ₁ → ∃ k < 3, IsInnerAut (δ₁ ^ k * δ₂) := by
  rintro _ ⟨A₁, rfl⟩ _ ⟨A₂, rfl⟩ _ _ hin
  have : IsCyclic (rootsOfUnity (p ^ f + 1) K) := rootsOfUnity.isCyclic K (p ^ f + 1)
  have hU : ∀ A : unitaryIsom3 h,
      GeneralLinearGroup.det (A : GL (Fin 3) K) ∈ rootsOfUnity (p ^ f + 1) K := fun A =>
    (mem_rootsOfUnity _ _).mpr (det_pow_succ_eq_one_of_mem h A.2)
  have key : ∀ (A : unitaryIsom3 h) (w : rootsOfUnity (p ^ f + 1) K),
      (w : Kˣ) = GeneralLinearGroup.det (A : GL (Fin 3) K) →
      w ∈ (powMonoidHom 3 : rootsOfUnity (p ^ f + 1) K →* _).range →
      IsInnerAut (psuConj h A) := by
    rintro A w hw ⟨v, rfl⟩
    refine isInnerAut_psuConj_of_det_eq_pow_three h A (u := v) ?_ ((mem_rootsOfUnity _ _).mp v.2)
    rw [← hw, powMonoidHom_apply, SubgroupClass.coe_pow]
  obtain ⟨k, hk, hmem⟩ := exists_pow_mul_mem_range_pow_three
    (u := ⟨_, hU A₁⟩) (fun hc => hin (key A₁ _ rfl hc)) ⟨_, hU A₂⟩
  refine ⟨k, hk, ?_⟩
  rw [← map_pow, ← map_mul]
  refine key _ _ ?_ hmem
  simp [map_mul, map_pow]

theorem psu3_inndiag_comm_field (hq : 2 < p ^ f) :
    ∀ φ ∈ (stdPinnedPSU3 h).field, φ ≠ 1 → φ ^ 3 = 1 → ∀ δ ∈ (stdPinnedPSU3 h).inndiag,
      δ ^ 3 = 1 → Commute δ φ → IsInnerAut δ := by
  have := h.finite
  rintro _ ⟨σ, rfl⟩ hφ1 hφ3 δ hδ hδ3 hcomm
  by_cases h3 : 3 ∣ p ^ f + 1
  swap
  · exact psu3_inndiag_cube h3 δ hδ hδ3
  obtain ⟨A, rfl⟩ := hδ
  have hα3 : (psuConj h A * psuField h σ) ^ 3 = 1 := by rw [hcomm.mul_pow, hδ3, hφ3, one_mul]
  have hαD : psuConj h A * psuField h σ ∉ (psuConj h).range := by
    intro hmem
    have h' : psuField h σ ∈ (psuConj h).range := by
      have := mul_mem (inv_mem (⟨A, rfl⟩ : psuConj h A ∈ (psuConj h).range)) hmem
      rwa [inv_mul_cancel_left] at this
    rw [psuField_mem_range_psuConj_iff] at h'
    exact hφ1 (by rw [h', map_one])
  obtain ⟨τ, hτ3, H, hH⟩ := unitary_order_three_field_descent hq _ hα3 hαD
  set Hτ : unitaryIsom3 h :=
    ⟨glAut τ ((H⁻¹ : unitaryIsom3 h) : GL (Fin 3) K), glAut_mem_unitaryIsom3 τ (H⁻¹).2⟩ with hHτ
  have hB : psuConj h A * psuField h σ = psuConj h (H * Hτ) * psuField h τ := by
    have h1 := psuField_mul_psuConj_mul_inv τ H⁻¹
    rw [hH, map_mul]
    calc psuConj h H * psuField h τ * (psuConj h H)⁻¹ =
        psuConj h H * (psuField h τ * psuConj h H⁻¹ * (psuField h τ)⁻¹) * psuField h τ := by
          rw [map_inv]; group
      _ = psuConj h H * psuConj h Hτ * psuField h τ := by rw [h1]
  have h2 : psuConj h ((H * Hτ)⁻¹ * A) * psuField h (σ * τ⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv]
    calc (psuConj h (H * Hτ))⁻¹ * psuConj h A * (psuField h σ * (psuField h τ)⁻¹) =
        (psuConj h (H * Hτ))⁻¹ * (psuConj h A * psuField h σ) * (psuField h τ)⁻¹ := by group
      _ = 1 := by rw [hB]; group
  obtain ⟨-, c, hcn, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h2
  have hA : (A : GL (Fin 3) K) =
      (H : GL (Fin 3) K) * (Hτ : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
    group
  have hc1 : c ^ (p ^ f + 1) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, ← h.norm_eq_pow, hcn, Units.val_one])
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, mul_comm, pow_mul]
    have hx : p ^ f % 3 = 2 := by omega
    have hx2 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hx]
    omega
  obtain ⟨s, hs⟩ := exists_pow_three_mul_add_one_of_orderOf_eq_three hτ3 h3K
  set u := GeneralLinearGroup.det (H : GL (Fin 3) K) with hu
  have hu1 : u ^ (p ^ f + 1) = 1 := det_pow_succ_eq_one_of_mem h H.2
  have hdetτ : GeneralLinearGroup.det (Hτ : GL (Fin 3) K) = u⁻¹ ^ (3 * s + 1) := by
    refine Units.ext ?_
    rw [hHτ, GeneralLinearGroup.val_det_apply, coe_glAut, Units.val_pow_eq_pow_val, hu,
      ← map_inv, GeneralLinearGroup.val_det_apply, ← hs]
    rw [show ((H⁻¹ : unitaryIsom3 h) : GL (Fin 3) K) = (H : GL (Fin 3) K)⁻¹ from rfl]
    exact (RingHom.map_det (τ : K →+* K) _).symm
  refine isInnerAut_psuConj_of_det_eq_pow_three h A (u := (u ^ s)⁻¹ * c) ?_ ?_
  · rw [mul_pow, hA, map_mul, map_mul, hdetτ, mul_inv_pow_three_mul_add_one,
      GeneralLinearGroup.det_scalar, Fintype.card_fin]
  · rw [mul_pow, inv_pow, ← pow_mul, mul_comm s, pow_mul, hu1, one_pow, inv_one, one_mul, hc1]

theorem outThreeCyclic_psu3 (hq : 2 < p ^ f) : OutThreeCyclic (unitaryPSU h 3) := by
  have := h.finite
  have := isCyclic_ringEquiv_of_finite K
  exact outThreeCyclic_of_pinned (stdPinnedPSU3 h) (stdPinnedPSU3_stable hq).normal
    (fun τ hτ3 hτD => isField_psu3_of_pow_three_eq_one hq hτ3 hτD) (isCyclic_range _)
    (psu3_inndiag_pair h) (psu3_inndiag_comm_field h hq)

include h in
theorem outThreeCyclic_su3 (hq : 2 < p ^ f) : OutThreeCyclic (unitarySU p f K 3) :=
  (outThreeCyclic_psu3 h hq).of_hom
    ((MulAut.congr (suCenterEquiv h hq)).toMonoidHom.comp (centerDescend _))
    fun _ => isInnerAut_congr_centerDescend_iff h hq

end PSU3

section List47

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {X : Type} [Group X]

theorem eq_two_and_eq_one_of_pow_le_two {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (h : p ^ e ≤ 2) : p = 2 ∧ e = 1 := by
  have hp2 := hp.two_le
  have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  have hp' : p = 2 := by omega
  subst hp'
  refine ⟨rfl, ?_⟩
  by_contra hne
  have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem outThreeCyclic_of_statedSU (hX : CFSG.IsQuasisimple X) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) {K : Type} [Field K] (hK : Nat.card K = (p ^ e) ^ 2)
    (e₁ : X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ e) K) : OutThreeCyclic X := by
  have hU : UnitaryFieldData p e K := ⟨Fact.out, he, by rw [hK, ← pow_mul, mul_comm]⟩
  rcases lt_or_ge 2 (p ^ e) with hq2 | hq2
  · have E : X ≃* unitarySU p e K 3 := e₁
    exact (outThreeCyclic_su3 hU hq2).of_mulEquiv E
  · exfalso
    obtain ⟨rfl, rfl⟩ := eq_two_and_eq_one_of_pow_le_two Fact.out he hq2
    have := hU.finite
    have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
    have := Fintype.ofFinite (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K)
    have hsolv : Group.IsSolvable (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
        (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    exact Sec4.false_of_isQuasisimple_of_isSolvable hX
      (Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective)

theorem outThreeCyclic_of_projSU (hX : CFSG.IsQuasisimple X) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (e₁ : X ≃* projSU 3 p e) : OutThreeCyclic X := by
  have hU := unitaryFieldData_galoisField p e he
  rcases lt_or_ge 2 (p ^ e) with hq2 | hq2
  · exact (outThreeCyclic_psu3 hU hq2).of_mulEquiv (e₁.trans (projSUEquivUnitaryPSU p e hU))
  · exfalso
    obtain ⟨rfl, rfl⟩ := eq_two_and_eq_one_of_pow_le_two Fact.out he hq2
    have := Sec13.isSolvable_projSU_two
    exact Sec4.false_of_isQuasisimple_of_isSolvable hX
      (Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective)

theorem outThreeCyclic_of_isSLThreePiAt (hX : CFSG.IsQuasisimple X) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : IsSLThreePiAt X (p ^ e)) : OutThreeCyclic X := by
  obtain ⟨K, _, _, ⟨-, -, ⟨e₁⟩⟩ | ⟨hK, -, ⟨e₁⟩⟩⟩ := h
  · exact (outThreeCyclic_sl3 K).of_mulEquiv
      (e₁.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm)
  · exact outThreeCyclic_of_statedSU hX he hK e₁

theorem outThreeCyclic_of_isoLThreePi (hX : CFSG.IsQuasisimple X) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : IsoLThreePi X p e) : OutThreeCyclic X := by
  rcases h with ⟨-, ⟨e₁⟩⟩ | ⟨-, ⟨e₁⟩⟩
  · exact (outThreeCyclic_psl3 _).of_mulEquiv (e₁.trans (projSLEquivProjectiveSL 3 _))
  · exact outThreeCyclic_of_projSU hX he e₁

theorem outThreeCyclic_of_g2_even
    {n : ℕ}
    (h : ChevalleyExceptionalModel X .G2 2 n) : OutThreeCyclic X := by
  have hf3 : 3 ≤ 2 ^ n := h.1.2.2.2
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_adjointGroup_G2 h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n <;> norm_num at hf3
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
  exact (outThreeCyclic_g2 K hK3 hK4).of_mulEquiv E

theorem outThreeCyclic_of_alt47W
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) (h : Alt47W L a) :
    OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨p, e, _, -, -, ⟨e₁⟩, -⟩ | ⟨p, e, _, -, he1, -, hL, -⟩ | ⟨h3, -⟩ |
    ⟨n, hn, hL, -⟩ | ⟨n, -, hD4⟩
  ·
    exact (outThreeCyclic_psl2 _).of_mulEquiv (e₁.trans (projSLEquivPSL _))
  ·
    rcases hL with hL | hL
    · exact outThreeCyclic_of_isSLThreePiAt hq he1 hL
    · exact outThreeCyclic_of_isoLThreePi hq he1 hL
  ·
    rcases h3 with ⟨m, hm, h3⟩ | ⟨n, -, h3⟩
    · rcases h3 with he₁ | ⟨K, _, _, hK, ⟨e₁⟩⟩ | he₁ | ⟨K, _, _, -, ⟨e₁⟩⟩
      · obtain ⟨e₁⟩ := he₁
        exact (outThreeCyclic_psl2 _).of_mulEquiv (e₁.trans (projSLEquivPSL _))
      · exact outThreeCyclic_of_statedSU hq hm hK e₁
      · obtain ⟨e₁⟩ := he₁
        exact outThreeCyclic_of_projSU hq hm e₁
      · exact (outThreeCyclic_sl3 K).of_mulEquiv
          (e₁.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm)
    · rcases h3 with hSz | he₁ | he₁ | hG2 | hRee
      · obtain ⟨-, b, hb, K, _, _, hfb, hK, ⟨E⟩⟩ := hSz
        exact (outThreeCyclic_sz hb (by rw [hK, hfb])).of_mulEquiv E
      · obtain ⟨e₁⟩ := he₁
        exact (outThreeCyclic_psl3 _).of_mulEquiv (e₁.trans (projSLEquivProjectiveSL 3 _))
      · obtain ⟨e₁⟩ := he₁
        exact (outThreeCyclic_psp4Even _).of_mulEquiv (e₁.trans (projSpEquivStatedProj 2 _))
      · exact outThreeCyclic_of_g2_even hG2
      · obtain ⟨-, b, hb, -, K, _, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_reeGamma hRee
        exact (outThreeCyclic_largeRee hb hK).of_mulEquiv E
  ·
    rcases hL with hL | hL
    · exact outThreeCyclic_of_isSLThreePiAt hq hn hL
    · exact outThreeCyclic_of_isoLThreePi hq hn hL
  ·
    have hf1 : 1 ≤ n := hD4.1.2.1
    obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := exists_mulEquiv_graphFixedRootGroup_D4 hD4
    exact (outThreeCyclic_triality hf1 hK hσ).of_mulEquiv E

theorem outThreeCyclic_of_alt47
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) (h : Alt47 L a) :
    OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L) :=
  outThreeCyclic_of_alt47W hq h.toW

end List47

section Main

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}

theorem thetaQuotMulAut_compAction_eq_conj {d : X} (hdL : d ∈ L)
    (hd : d ∈ Subgroup.normalizer (L : Set X)) :
    thetaQuotMulAut L (compAction L ⟨d, hd⟩) =
      MulAut.conj ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y => rfl

theorem mem_sup_thetaQuotCentralizer_of_not_inducesOuterTheta {x : X}
    (hx : x ∈ Subgroup.normalizer (L : Set X)) (hin : ¬ InducesOuterTheta x L) :
    x ∈ L ⊔ thetaQuotCentralizer L := by
  have hinn : thetaQuotMulAut L (compAction L ⟨x, hx⟩) ∈
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
    by_contra h'
    exact hin ⟨hx, h'⟩
  obtain ⟨y, hy⟩ := hinn
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have hlN : (l : X) ∈ Subgroup.normalizer (L : Set X) := Subgroup.le_normalizer l.2
  have hlxN : (l : X)⁻¹ * x ∈ Subgroup.normalizer (L : Set X) := mul_mem (inv_mem hlN) hx
  have hker : (⟨(l : X)⁻¹ * x, hlxN⟩ : Subgroup.normalizer (L : Set X)) ∈
      ((thetaQuotMulAut L).comp L.normalizerMonoidHom).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have : (⟨(l : X)⁻¹ * x, hlxN⟩ : Subgroup.normalizer (L : Set X)) =
        (⟨l, hlN⟩ : Subgroup.normalizer (L : Set X))⁻¹ * ⟨x, hx⟩ := rfl
    rw [this, map_mul, map_mul, map_inv, map_inv]
    change (thetaQuotMulAut L (compAction L ⟨l, hlN⟩))⁻¹ *
      thetaQuotMulAut L (compAction L ⟨x, hx⟩) = 1
    rw [thetaQuotMulAut_compAction_eq_conj l.2 hlN, ← hy]
    exact inv_mul_cancel _
  have hc : (l : X)⁻¹ * x ∈ thetaQuotCentralizer L := ⟨_, hker, rfl⟩
  rw [show x = (l : X) * ((l : X)⁻¹ * x) by group]
  exact mul_mem (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right hc)

theorem card_le_three_mul_card_inf_of_forall_pow_mul_mem {G : Type*} [Group G] [Finite G]
    {F C : Subgroup G} {a : G} (ha : a ∈ F) (h : ∀ b ∈ F, ∃ k < 3, a ^ k * b ∈ C) :
    Nat.card F ≤ 3 * Nat.card (F ⊓ C : Subgroup G) := by
  choose k hk hkC using h
  let φ : F → Fin 3 × (F ⊓ C : Subgroup G) := fun b =>
    (⟨k b b.2, hk b b.2⟩, ⟨a ^ k b b.2 * b, mul_mem (pow_mem ha _) b.2, hkC b b.2⟩)
  have hinj : Function.Injective φ := by
    intro b₁ b₂ hb
    simp only [φ, Prod.mk.injEq, Fin.mk.injEq] at hb
    obtain ⟨h1, h2⟩ := hb
    have h3 := congrArg Subtype.val h2
    simp only at h3
    rw [h1] at h3
    exact Subtype.ext (mul_left_cancel h3)
  have h := Nat.card_le_card_of_injective φ hinj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h

theorem ks6OuterIndex_of
    (h47 : Item4_7W) :
    KS6OuterIndex := by
  intro X _ _ hX h3 L hL F hF hFN
  by_cases hFC : ∀ b ∈ F, b ∈ L ⊔ thetaQuotCentralizer L
  · have hinf : F ⊓ (L ⊔ thetaQuotCentralizer L) = F := inf_eq_left.mpr hFC
    rw [hinf]
    omega
  push Not at hFC
  obtain ⟨a, haF, haC⟩ := hFC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : a ^ 3 = 1 := hF.2 a haF
  have ha1 : a ≠ 1 := fun h1 => haC (h1 ▸ one_mem _)
  have haN := hFN haF
  have hout : InducesOuterTheta a L := by
    by_contra h'
    exact haC (mem_sup_thetaQuotCentralizer_of_not_inducesOuterTheta haN h')
  have hcyc :=
    outThreeCyclic_of_alt47W hL.2.2 (h47 X hX h3 L hL a (orderOf_eq_prime ha3 ha1) hout)
  refine card_le_three_mul_card_inf_of_forall_pow_mul_mem haF fun b hbF => ?_
  have hbN := hFN hbF
  set Φ := (thetaQuotMulAut L).comp (compAction L) with hΦ
  have hab0 : a * b = b * a := congrArg Subtype.val (hF.1.is_comm.comm ⟨a, haF⟩ ⟨b, hbF⟩)
  have hab : (⟨a, haN⟩ : Subgroup.normalizer (L : Set X)) * ⟨b, hbN⟩ = ⟨b, hbN⟩ * ⟨a, haN⟩ :=
    Subtype.ext hab0
  have hpow : ∀ (x : X) (hx : x ∈ Subgroup.normalizer (L : Set X)), x ^ 3 = 1 →
      Φ ⟨x, hx⟩ ^ 3 = 1 := fun x hx hx3 => by
    rw [← map_pow]
    have : (⟨x, hx⟩ : Subgroup.normalizer (L : Set X)) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  obtain ⟨k, hk, hin⟩ := hcyc (Φ ⟨a, haN⟩) (Φ ⟨b, hbN⟩)
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hab]) (hpow a haN ha3)
    (hpow b hbN (hF.2 b hbF)) (fun hi => hout.2 hi)
  refine ⟨k, hk, mem_sup_thetaQuotCentralizer_of_not_inducesOuterTheta
    (mul_mem (pow_mem haN k) hbN) ?_⟩
  rintro ⟨hx, hnot⟩
  apply hnot
  have : (⟨a ^ k * b, hx⟩ : Subgroup.normalizer (L : Set X)) = ⟨a, haN⟩ ^ k * ⟨b, hbN⟩ :=
    Subtype.ext (by simp)
  change Φ ⟨a ^ k * b, hx⟩ ∈ _
  rw [this, map_mul, map_pow]
  exact hin

end Main

end CFSG.RankThree.PartTwo.KFacts

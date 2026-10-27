module

public import CFSG.Quasithin.H13.NQRigidAsmSingleData
public import CFSG.Quasithin.H13.NQTermEvenLinearThreeImage
public import CFSG.Quasithin.SteinbergCDScalarQuotientCentralCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj frattiniQuotConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique.Setup.SL2Modules (repOfSubgroup)
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem central_cover_excludes_odd_three {H : Type} [Group H] [Finite H] {K : Subgroup H}
    (hKq : CFSG.IsQuasisimple K) {X P : Subgroup H} (hXK : X ≤ K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hP : IsSylowOf p P X) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hX2 : NoPQuotient 2 X) (hO2 : CFSG.pCore 2 X ≠ ⊥) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hS : StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 ℓ 1 ∨
      StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSU 3 ℓ 1) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  set Q := (CFSG.pCore 2 X).map X.subtype with hQ
  have hQX : Q ≤ X := map_subtype_le _
  have hPX : P ≤ X := hP.le
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hPp : IsPGroup p P := hP.isPGroup
  have hPQ : P ≤ normalizer (Q : Set H) := hPX.trans (le_normalizer_pCore_map X)
  set QK := Q.subgroupOf K with hQK
  set PK := P.subgroupOf K with hPK
  have hQK2 : IsPGroup 2 QK := by
    rw [hQK, ← comap_subtype]
    exact hQ2.comap_subtype
  have hPKp : IsPGroup p PK := by
    rw [hPK, ← comap_subtype]
    exact hPp.comap_subtype
  have hPKQ : PK ≤ normalizer (QK : Set K) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro z
    simp only [hQK, mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hPQ (mem_subgroupOf.mp hy)) z
  have hne := commutator_pCore_ne_bot hp2 hXA hX2 hO2 hP
  set e₀ := centerQuotEquivOfQuasisimple hKq with he₀
  have hcomm : ⁅QK, PK⁆ = ⊥ := by
    rcases hS with hS | hS
    · obtain ⟨-, k, hkf, hkfin, hk, ⟨e⟩⟩ := hS
      have hch : CharP k ℓ :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ le_rfl hk
      have h2 : (2 : k) ≠ 0 := by
        intro h0
        have h1 : ((2 : ℕ) : k) = 0 := by exact_mod_cast h0
        rw [CharP.cast_eq_zero_iff k ℓ] at h1
        exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1)
      have hD : ∀ d ∈ (StatedScalars (Fin 3) k).subgroupOf (StatedSL 3 k), ∃ a : k,
          (((d : StatedSL 3 k) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
            Matrix.scalar (Fin 3) a := by
        intro d hd
        obtain ⟨u, hu⟩ := mem_subgroupOf.mp hd
        exact ⟨u.1, by rw [← hu]; rfl⟩
      exact (SteinbergCD.central_extensions_scalar_quotients_trivial_large_prime_two_action h2
        (n := 3) le_rfl (Γ := StatedSL 3 k)
        (D := (StatedScalars (Fin 3) k).subgroupOf (StatedSL 3 k)) hD (Z := center K) le_rfl
        (e₀.trans e) hQK2 hp hp5 hPKp hPKQ).1
    · obtain ⟨-, k, hkf, hkfin, hk, ⟨e⟩⟩ := hS
      have hch : CharP k ℓ :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (k := 2) hℓ
          (by norm_num) (by rw [hk, pow_one])
      have h2 : (2 : k) ≠ 0 := by
        intro h0
        have h1 : ((2 : ℕ) : k) = 0 := by exact_mod_cast h0
        rw [CharP.cast_eq_zero_iff k ℓ] at h1
        exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1)
      have hD : ∀ d ∈ (StatedScalars (Fin 3) k).subgroupOf (StatedSU 3 (ℓ ^ 1) k), ∃ a : k,
          (((d : StatedSU 3 (ℓ ^ 1) k) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
            Matrix.scalar (Fin 3) a := by
        intro d hd
        obtain ⟨u, hu⟩ := mem_subgroupOf.mp hd
        exact ⟨u.1, by rw [← hu]; rfl⟩
      exact (SteinbergCD.central_extensions_scalar_quotients_trivial_large_prime_two_action h2
        (n := 3) le_rfl (Γ := StatedSU 3 (ℓ ^ 1) k)
        (D := (StatedScalars (Fin 3) k).subgroupOf (StatedSU 3 (ℓ ^ 1) k)) hD (Z := center K)
        le_rfl (e₀.trans e) hQK2 hp hp5 hPKp hPKQ).1
  apply hne
  have h1 := congrArg (Subgroup.map K.subtype) hcomm
  rw [map_commutator, Subgroup.map_bot, hQK, hPK, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (hQX.trans hXK), inf_of_le_left (hPX.trans hXK)] at h1
  exact h1

theorem offender_excludes_odd_three {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Nontrivial W] (L₁ B₁ : Subgroup (Module.End (ZMod 2) W)ˣ) (hLq : CFSG.IsQuasisimple L₁)
    (hirr : (repOfSubgroup L₁).IsIrreducible) (hBe : CFSG.IsElementaryAbelian 2 B₁)
    (hB1 : B₁ ≠ ⊥) (hBN : B₁ ≤ normalizer (L₁ : Set (Module.End (ZMod 2) W)ˣ))
    (hoff : Nat.card W ≤ Nat.card B₁ * Nat.card {w : W // ∀ b ∈ B₁, b.val w = w})
    {S : Type} [Group S] (e : (L₁ ⧸ center L₁) ≃* S) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ)
    (hS : StatedClassicalModel S .PSL 3 ℓ 1 ∨ StatedClassicalModel S .PSU 3 ℓ 1) : False := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hlt : Nat.card B₁ * Nat.card {w : W // ∀ b ∈ B₁, b.val w = w} < Nat.card W := by
    rcases hS with hS | hS
    · exact NQBlock.offender_lt_of_mulAut_exclusion L₁ B₁ hirr hLq.1 hBe hB1 hBN
        fun L' hperf' hirr' ⟨e'⟩ A hA hA1 hAe =>
          CFSG.QuasithinUnique.Setup.Family.primeLinearThreeExclusion ℓ hℓ hℓ2 (Multiplicative W)
            NQBlock.multiplicative_mul_self L' hperf' ⟨inferInstance, hirr'⟩
            (CFSG.QuasithinUnique.Setup.Family.statedClassicalModel_of_mulEquiv (e'.trans e).symm
              hS) A hA hA1 hAe
    · exact NQBlock.offender_lt_of_mulAut_exclusion L₁ B₁ hirr hLq.1 hBe hB1 hBN
        fun L' hperf' hirr' ⟨e'⟩ A hA hA1 hAe =>
          CFSG.QuasithinUnique.Setup.Family.primeUnitaryThreeExclusion ℓ hℓ hℓ5 (Multiplicative W)
            NQBlock.multiplicative_mul_self L' hperf' ⟨inferInstance, hirr'⟩
            (CFSG.QuasithinUnique.Setup.Family.statedClassicalModel_of_mulEquiv (e'.trans e).symm
              hS) A hA hA1 hAe
  omega

section Even

variable {G : Type} [Group G] [Finite G]

theorem even_linear_three_ordinary_excluded {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (hO2 : CFSG.pCore 2 X ≠ ⊥)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirrL : IsFrattiniIrreducible X L) (hX2 : NoPQuotient 2 X) {H : Subgroup G} (hXH : X ≤ H)
    {K : Subgroup H} (hKq : CFSG.IsQuasisimple K) (hXK : X.subgroupOf H ≤ K)
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) {f : ℕ} (hf : 1 ≤ f)
    (hS : StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 2 f) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, k, hkf, hkfin, hk, ⟨e⟩⟩ := hS
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  set ψ : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 k).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 k)) with hψ
  set ι : X.subgroupOf L →* K := (inclusion hXK).comp
    ((subgroupOfEquivOfLe hXH).symm.toMonoidHom.comp (subgroupOfEquivOfLe hXL).toMonoidHom)
    with hι
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : ((ι a : K) : H) = ((ι b : K) : H) := congrArg (fun z : K => (z : H)) hab
    apply Subtype.ext
    apply Subtype.ext
    have h2 := congrArg Subtype.val h1
    exact h2
  set φ : X.subgroupOf L →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k :=
    ψ.toMonoidHom.comp ((coreCenterQuot K).comp ι) with hφ
  have hker : ∀ x, x ∈ φ.ker ↔ ι x ∈ (coreCenterQuot K).ker := by
    intro x
    simp only [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hσZ := ker_coreCenterQuot_of_quasisimple hKq
  have hcen : φ.ker ≤ center (X.subgroupOf L) := by
    intro x hx
    rw [mem_center_iff]
    intro y
    have hxZ : ι x ∈ center K := hσZ ▸ (hker x).mp hx
    apply hιinj
    rw [map_mul, map_mul]
    exact (mem_center_iff.mp hxZ (ι y))
  have hσp := not_dvd_card_ker_coreCenterQuot hp hp2 hZ
  have hX'A : IsPGroup p (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) :=
    (isPGroup_of_exponent hexp).of_equiv (coreQuotEquivSubgroupOf hXL).symm
  obtain ⟨a, b, hab⟩ := card_eq_two_pow_mul_prime_pow hX'A
  have h2 : IsPGroup 2 φ.ker := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx1 : orderOf (x : X.subgroupOf L) ∣ 2 ^ a * p ^ b := by
      rw [← hab]
      exact orderOf_dvd_natCard _
    have hx2 : ¬ p ∣ orderOf (x : X.subgroupOf L) := by
      intro hdvd
      apply hσp
      have h3 : orderOf (⟨ι x, (hker x).mp x.2⟩ : (coreCenterQuot K).ker) =
          orderOf (x : X.subgroupOf L) := by
        rw [← Subgroup.orderOf_coe, orderOf_injective ι hιinj]
      exact hdvd.trans (h3 ▸ orderOf_dvd_natCard _)
    have hx3 : orderOf (x : X.subgroupOf L) ∣ 2 ^ a := by
      have hcop : Nat.Coprime (orderOf (x : X.subgroupOf L)) (p ^ b) :=
        Nat.Coprime.pow_right b ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
          hx2)))
      exact hcop.dvd_of_dvd_mul_right hx1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx3
    exact ⟨m, by rw [← hm, Subgroup.orderOf_coe]⟩
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have hLperf : Group.IsPerfect L := ⟨by rw [commutator_def]; exact hLC.2.1⟩
  have hA1 : CFSG.pCore 2 (X.subgroupOf L) ≠ ⊥ := by
    intro h0
    apply hO2
    rw [← CFSG.pCore_map_iso 2 (subgroupOfEquivOfLe hXL), h0, Subgroup.map_bot]
  have hexp' : Monoid.exponent (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) = p := by
    rw [Monoid.exponent_eq_of_mulEquiv (coreQuotEquivSubgroupOf hXL), hexp]
  have hW' := card_frattini_subgroupOf hXL
  rw [hW] at hW'
  have hX2' : NoPQuotient 2 (X.subgroupOf L) :=
    NoPQuotient.of_surjective (subgroupOfEquivOfLe hXL).symm.toMonoidHom
      (subgroupOfEquivOfLe hXL).symm.surjective hX2
  exact NQTerm.original_perfect_plane_excludes_central_even_linear_three_image hLperf hp hp5 hA1
    hexp' hW' (frattiniQuotConj_irreducible_of hXL hirrL) hX2' k ⟨φ, h2, hcen⟩

end Even

end CFSG.Quasithin.H13.NQRigid

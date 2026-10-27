module

public import CFSG.RankThree.PartOne.S9.Alpha.Setup
public import CFSG.RankThree.PartOne.S9.Alpha.FixedGeneration
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeProductFixed

public section

namespace CFSG.RankThree.PartOne.AlphaTheory

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThreeEvenClassification.Helpers Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem not_dvd_card_of_isPGroup_two [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup G} (hS : IsPGroup 2 S) : ¬ p ∣ Nat.card S := by
  intro hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
  rw [hn] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

@[expose] def MixedBound (A : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → ⁅coreTwo a ⊓ centralizer ({b} : Set G), A⁆ ≤ coreTwo b

namespace AlphaSetup

variable {p : ℕ} {A B : Subgroup G} (h : AlphaSetup p A B)
include h

theorem isPGroup_B : IsPGroup p B := fun x =>
  ⟨1, Subtype.ext (by simpa using h.pow x (h.le x.2))⟩

theorem isElementaryAbelian_B : IsElementaryAbelian p B where
  toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (h.comm x (h.le x.2) y (h.le y.2))⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using h.pow x (h.le x.2))

theorem isPGroup_zpowers {c : G} (hc : c ∈ A) : IsPGroup p (zpowers c) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  refine ⟨1, Subtype.ext ?_⟩
  change (c ^ k) ^ p ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.pow c hc, one_zpow]

section Signalizer

variable [Finite G]

theorem fixed_J_le_U (hBcard : Nat.card B = p ^ 2) (hmix : MixedBound A) {d : G} (hd : d ∈ A)
    (hd1 : d ≠ 1) : ⁅coreTwo d, B⁆ ⊓ centralizer (B : Set G) ≤ centralizerCoreTwo B := by
  have hBd := h.B_le_centralizer_singleton hd
  have hJ2 := isPGroup_J hBd
  have hJB : B ≤ normalizer ((⁅coreTwo d, B⁆ : Subgroup G) : Set G) :=
    normalizer_commutator_ge_right _ B
  have hJid : ⁅⁅coreTwo d, B⁆, B⁆ = ⁅coreTwo d, B⁆ :=
    coprime_commutator_idempotent p h.prime B (coreTwo d) h.isPGroup_B
      (not_dvd_card_of_isPGroup_two h.prime h.odd (isPGroup_coreTwo d))
      (AlphaTheory.le_normalizer_coreTwo hBd)
  have hJnil : Group.IsNilpotent (⁅coreTwo d, B⁆ : Subgroup G) := hJ2.isNilpotent
  rw [nilpotent_fixed_generation_ambient h.prime h.isElementaryAbelian_B hBcard hJB hJnil
    (not_dvd_card_of_isPGroup_two h.prime h.odd hJ2) hJid]
  refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
  have hle1 : ⁅⁅coreTwo d, B⁆ ⊓ centralizer ({b} : Set G), B⁆ ≤ coreTwo b :=
    (Subgroup.commutator_mono (inf_le_inf_right _ (commutator_coreTwo_le hBd)) h.le).trans
      (hmix d hd hd1 b (h.le hb) hb1)
  refine (inf_le_inf_right _ hle1).trans ?_
  rw [inf_comm]
  exact SteinbergBY.inf_inSubgroup_pCore_le (centralizer_le (Set.singleton_subset_iff.mpr hb))

theorem gammaB_fixed_le_U (hBcard : Nat.card B = p ^ 2) (hmix : MixedBound A) {d : G} (hd : d ∈ A)
    (hd1 : d ≠ 1) : gammaB B d ⊓ centralizer (B : Set G) ≤ centralizerCoreTwo B := by
  have hBd := h.B_le_centralizer_singleton hd
  have hprod := normalized_sup_centralizer_eq_of_pGroup_prime_complement p h.prime B
    ⁅coreTwo d, B⁆ (centralizerCoreTwo B ⊓ centralizer ({d} : Set G)) h.isPGroup_B
    (normalizer_commutator_ge_right _ B) ((h.le).trans (h.le_normalizer_T hd))
    (T_le_normalizer_J B d)
    (not_dvd_card_of_isPGroup_two h.prime h.odd ((isPGroup_J hBd).to_le inf_le_left))
  change (⁅coreTwo d, B⁆ ⊔ (centralizerCoreTwo B ⊓ centralizer ({d} : Set G))) ⊓ _ ≤ _
  rw [hprod]
  exact sup_le (h.fixed_J_le_U hBcard hmix hd hd1) (inf_le_left.trans inf_le_left)

theorem gammaB_balance (hBcard : Nat.card B = p ^ 2) (hmix : MixedBound A) {c d : G} (hc : c ∈ A)
    (hc1 : c ≠ 1) (hd : d ∈ A) (hd1 : d ≠ 1) :
    gammaB B d ⊓ centralizer ({c} : Set G) ≤ gammaB B c := by
  have hBd := h.B_le_centralizer_singleton hd
  have hBc := h.B_le_centralizer_singleton hc
  have hcop2 := fun {S : Subgroup G} (hS : IsPGroup 2 S) =>
    not_dvd_card_of_isPGroup_two h.prime h.odd hS
  have hY : gammaB B d ⊓ centralizer ({c} : Set G) =
      ⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G) ⊔
        (centralizerCoreTwo B ⊓ centralizer ({d} : Set G)) ⊓ centralizer ({c} : Set G) := by
    have := normalized_sup_centralizer_eq_of_pGroup_prime_complement p h.prime (zpowers c)
      ⁅coreTwo d, B⁆ (centralizerCoreTwo B ⊓ centralizer ({d} : Set G)) (h.isPGroup_zpowers hc)
      (zpowers_le.mpr (h.le_normalizer_J hd hc)) (zpowers_le.mpr (h.le_normalizer_T hd hc))
      (T_le_normalizer_J B d) (hcop2 ((isPGroup_J hBd).to_le inf_le_left))
    rwa [← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at this
  have hF2 : IsPGroup 2 (⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G) : Subgroup G) :=
    (isPGroup_J hBd).to_le inf_le_left
  have hBF : B ≤ normalizer ((⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    fun x hx => SteinbergBY.mem_normalizer_inf (normalizer_commutator_ge_right _ B hx)
      (Subgroup.le_normalizer (hBc hx))
  have hFB : ⁅⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G), B⁆ ≤ ⁅coreTwo c, B⁆ := by
    have hFc : ⁅⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G), B⁆ ≤ coreTwo c :=
      (Subgroup.commutator_mono (inf_le_inf_right _ (commutator_coreTwo_le hBd)) h.le).trans
        (hmix d hd hd1 c hc hc1)
    calc ⁅⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G), B⁆
        = ⁅⁅⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G), B⁆, B⁆ :=
          (coprime_commutator_idempotent p h.prime B _ h.isPGroup_B (hcop2 hF2) hBF).symm
      _ ≤ ⁅coreTwo c, B⁆ := Subgroup.commutator_mono hFc le_rfl
  have hSF : (centralizerCoreTwo B ⊓ centralizer ({d} : Set G)) ⊓ centralizer ({c} : Set G) ≤
      normalizer ((⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    fun s hs => SteinbergBY.mem_normalizer_inf (T_le_normalizer_J B d hs.1)
      (Subgroup.le_normalizer hs.2)
  have hSB : (centralizerCoreTwo B ⊓ centralizer ({d} : Set G)) ⊓ centralizer ({c} : Set G) ≤
      centralizer (B : Set G) := fun s hs => centralizerCoreTwo_le_centralizer B hs.1.1
  have hYB : ⁅gammaB B d ⊓ centralizer ({c} : Set G), B⁆ ≤ ⁅coreTwo c, B⁆ := by
    rw [hY, Subgroup.commutator_le]
    intro y hy x hx
    have hy' : y ∈ ((⁅coreTwo d, B⁆ ⊓ centralizer ({c} : Set G) : Subgroup G) : Set G) *
        (((centralizerCoreTwo B ⊓ centralizer ({d} : Set G)) ⊓ centralizer ({c} : Set G) :
          Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hSF]
      exact hy
    obtain ⟨f, hf, s, hs, rfl⟩ := hy'
    have hsx : x * s = s * x := mem_centralizer_iff.mp (hSB hs) x hx
    have hcomm : ⁅f * s, x⁆ = ⁅f, x⁆ := by
      simp only [commutatorElement_def]
      calc f * s * x * (f * s)⁻¹ * x⁻¹ = f * (s * x * s⁻¹) * f⁻¹ * x⁻¹ := by group
        _ = f * x * f⁻¹ * x⁻¹ := by rw [← hsx, mul_inv_cancel_right]
    rw [hcomm]
    exact hFB (Subgroup.commutator_mem_commutator hf hx)
  have hBY : B ≤ normalizer ((gammaB B d ⊓ centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    fun x hx => SteinbergBY.mem_normalizer_inf (h.le_normalizer_gammaB hd (h.le hx))
      (Subgroup.le_normalizer (hBc hx))
  have hY2 : IsPGroup 2 (gammaB B d ⊓ centralizer ({c} : Set G) : Subgroup G) :=
    (isPGroup_gammaB hBd).to_le inf_le_left
  have hfac := coprime_commutator_centralizer_factorization p h.prime B _ h.isPGroup_B
    (hcop2 hY2) hBY
  have hfixed : gammaB B d ⊓ centralizer ({c} : Set G) ⊓ centralizer (B : Set G) ≤
      centralizerCoreTwo B ⊓ centralizer ({c} : Set G) := fun y hy =>
    ⟨h.gammaB_fixed_le_U hBcard hmix hd hd1 ⟨hy.1.1, hy.2⟩, hy.1.2⟩
  calc gammaB B d ⊓ centralizer ({c} : Set G)
      = ⁅gammaB B d ⊓ centralizer ({c} : Set G), B⁆ ⊔
          gammaB B d ⊓ centralizer ({c} : Set G) ⊓ centralizer (B : Set G) := hfac
    _ ≤ gammaB B c := sup_le_sup hYB hfixed

theorem gammaB_isSolvableSignalizerFunctor (hBcard : Nat.card B = p ^ 2) (hmix : MixedBound A) :
    CFSG.Open.IsSolvableSignalizerFunctor p A (gammaB B) where
  le_centralizer a ha _ := gammaB_le_centralizer (h.B_le_centralizer_singleton ha)
  coprime a ha _ := (Nat.Prime.coprime_iff_not_dvd h.prime).mpr
    (not_dvd_card_of_isPGroup_two h.prime h.odd
      (isPGroup_gammaB (h.B_le_centralizer_singleton ha)))
  invariant a ha _ x hx :=
    SteinbergBY.map_conj_eq_of_mem_normalizer (h.le_normalizer_gammaB ha hx)
  balance a ha ha1 b hb hb1 := h.gammaB_balance hBcard hmix hb hb1 ha ha1
  solvable a ha _ := by
    have := (isPGroup_gammaB (h.B_le_centralizer_singleton ha)).isNilpotent
    infer_instance

end Signalizer

end AlphaSetup

end CFSG.RankThree.PartOne.AlphaTheory

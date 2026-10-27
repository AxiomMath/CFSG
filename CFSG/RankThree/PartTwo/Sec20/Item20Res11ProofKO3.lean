module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res8ProofYKO3
import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofPGroup
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankBridge
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] noncomputable def oTwoLayer {G : Type} [Group G] (O : Subgroup G) : Subgroup G :=
  ((CFSG.layer (O ⧸ CFSG.pCore 2 O)).comap (QuotientGroup.mk' (CFSG.pCore 2 O))).map O.subtype

@[expose] def KFactKO3CentLayer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ K O : Subgroup G, O ≠ ⊤ → Group.IsPerfect K →
      ((∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) ∨
        (∃ n : ℕ, Even n ∧ 4 ≤ n ∧
          Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n)))) →
      K ≤ Subgroup.normalizer (O : Set G) → Nat.Coprime 3 (Nat.card O) →
      (∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p O ≤ 2) →
      ∀ k ∈ K, ∀ o ∈ oTwoLayer O, k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O

namespace Res11

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem kType_three_le {K : Subgroup G}
    (htype : (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, Even n ∧ 4 ≤ n ∧
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n)))) :
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n))) := by
  rcases htype with ⟨n, -, hn, he⟩ | ⟨n, -, hn, he⟩
  · exact Or.inl ⟨n, hn, he⟩
  · exact Or.inr ⟨n, by omega, he⟩

theorem pRank_quotient_le (O : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pRank p (O ⧸ CFSG.pCore 2 O) ≤ CFSG.Open.pRank p O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 O
  have hker : ¬ p ∣ Nat.card (QuotientGroup.mk' Q).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := O)).exists_card_eq
    rw [ha]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have h := Sec4.pRank_map_le_of_not_dvd hp (QuotientGroup.mk' Q) hker ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)] at h
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_pRank_top_subgroup O]
  exact h

@[expose] noncomputable def quotAction {K O : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (O : Set G)) : K →* MulAut (O ⧸ CFSG.pCore 2 O) :=
  (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (CFSG.pCore 2 O)).comp
    (O.normalizerMonoidHom.comp (Subgroup.inclusion hKN))

omit [Finite G] in
theorem quotAction_mk {K O : Subgroup G} (hKN : K ≤ Subgroup.normalizer (O : Set G))
    (k : K) (x : O) :
    quotAction hKN k (QuotientGroup.mk' (CFSG.pCore 2 O) x) =
      QuotientGroup.mk' (CFSG.pCore 2 O)
        ⟨k * x * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKN k.2) x).mp x.2⟩ :=
  rfl

omit [Finite G] in
theorem comm_mem_of_quotAction_fix {K O : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (O : Set G)) (k : K) (x : O)
    (h : quotAction hKN k (QuotientGroup.mk' (CFSG.pCore 2 O) x) =
      QuotientGroup.mk' (CFSG.pCore 2 O) x) :
    (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 O := by
  set Q := CFSG.pCore 2 O
  set y : O := ⟨k * x * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKN k.2) x).mp x.2⟩ with hy
  rw [quotAction_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  have h3 : y * x⁻¹ ∈ Q := by
    have h4 := (inferInstance : Q.Normal).conj_mem _ h y
    have h5 : y * (y⁻¹ * x) * y⁻¹ = (y * x⁻¹)⁻¹ := by group
    rw [h5] at h4
    exact (inv_mem_iff).mp h4
  show (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ ∈ (CFSG.Open.pCore 2 O).map O.subtype
  exact ⟨y * x⁻¹, h3, rfl⟩

omit [Finite G] in
theorem quotAction_fix_of_comm_mem {K O : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (O : Set G)) (k : K) (x : O)
    (h : (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 O) :
    quotAction hKN k (QuotientGroup.mk' (CFSG.pCore 2 O) x) =
      QuotientGroup.mk' (CFSG.pCore 2 O) x := by
  set Q := CFSG.pCore 2 O
  set y : O := ⟨k * x * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKN k.2) x).mp x.2⟩ with hy
  change _ ∈ (CFSG.Open.pCore 2 O).map O.subtype at h
  obtain ⟨q, hq, hqe⟩ := h
  have hyq : y = q * x := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← Subgroup.coe_subtype, hqe]
    simp [hy]
  rw [quotAction_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  change y⁻¹ * x ∈ Q
  rw [hyq]
  have h1 : (q * x)⁻¹ * x = x⁻¹ * q⁻¹ * x⁻¹⁻¹ := by group
  rw [h1]
  exact (inferInstance : Q.Normal).conj_mem _ (Q.inv_mem hq) x⁻¹

theorem fix_pCore {K O : Subgroup G} [Group.IsPerfect K]
    (htype : (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, Even n ∧ 4 ≤ n ∧
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n))))
    (hKN : K ≤ Subgroup.normalizer (O : Set G))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hrank : CFSG.Open.pRank p O ≤ 2) (k : K)
    {y : O ⧸ CFSG.pCore 2 O} (hy : y ∈ CFSG.pCore p (O ⧸ CFSG.pCore 2 O)) :
    quotAction hKN k y = y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set P := CFSG.pCore p (O ⧸ CFSG.pCore 2 O) with hP
  let ρ : K →* MulAut P := (MulAut.characteristic P).comp (quotAction hKN)
  have hrankP : CFSG.pRank p P ≤ 2 :=
    ((RankThree.PartOne.FixedRank36.pRank_le_of_injective P.subtype P.subtype_injective).trans
      (pRank_quotient_le O hp hp2)).trans hrank
  have hρ : ρ = 1 :=
    eq_one_of_pRank_le_two (kType_three_le htype) hp2 CFSG.pCore_isPGroup hrankP ρ
  exact congrArg (fun σ : MulAut P => ((σ ⟨y, hy⟩ : P) : O ⧸ CFSG.pCore 2 O))
    (DFunLike.congr_fun hρ k)

theorem eq_one_of_commute_image {K H : Type*} [Group K] [Group.IsPerfect K] [Group H]
    (f : K →* H) (hf : ∀ a b : K, f a * f b = f b * f a) : f = 1 := by
  have hker : commutator K ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hf a b
  rw [Group.IsPerfect.commutator_eq_top] at hker
  ext k
  exact hker (Subgroup.mem_top k)

theorem inv_mul_apply_mem_centralizer {Γ : Type*} [Group Γ] {F : Subgroup Γ} (hFn : F.Normal)
    (α : MulAut Γ) (hα : ∀ y ∈ F, α y = y) (x : Γ) :
    x⁻¹ * α x ∈ Subgroup.centralizer (F : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxy : x * y * x⁻¹ ∈ F := hFn.conj_mem y hy x
  have h1 := hα _ hxy
  rw [map_mul, map_mul, map_inv, hα y hy] at h1
  calc y * (x⁻¹ * α x) = x⁻¹ * (x * y * x⁻¹) * α x := by group
    _ = x⁻¹ * (α x * y * (α x)⁻¹) * α x := by rw [h1]
    _ = x⁻¹ * α x * y := by group

theorem eq_one_of_fix_generalizedFitting {K Γ : Type*} [Group K] [Group.IsPerfect K] [Group Γ]
    [Finite Γ] (σ : K →* MulAut Γ)
    (hfix : ∀ k : K, ∀ y ∈ CFSG.generalizedFitting Γ, σ k y = y) : σ = 1 := by
  set F := CFSG.generalizedFitting Γ with hF
  have hFn : F.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hcent : ∀ (k : K) (x : Γ), x⁻¹ * σ k x ∈ F := fun k x =>
    CFSG.centralizer_generalizedFitting_le Γ
      (inv_mul_apply_mem_centralizer hFn (σ k) (hfix k) x)
  ext k x
  let φ : K →* Γ :=
    { toFun := fun k => x⁻¹ * σ k x
      map_one' := by simp
      map_mul' := fun a b => by
        have hb : σ a (x⁻¹ * σ b x) = x⁻¹ * σ b x := hfix a _ (hcent b x)
        have hb' : σ a (σ b x) = σ a x * (x⁻¹ * σ b x) := by
          rw [← hb, ← map_mul, mul_inv_cancel_left]
        simp only [map_mul, MulAut.mul_apply]
        rw [hb']
        group }
  have hφ : φ = 1 := by
    apply eq_one_of_commute_image φ
    intro a b
    exact (Subgroup.mem_centralizer_iff.mp
      (inv_mul_apply_mem_centralizer hFn (σ a) (hfix a) x) _ (hcent b x)).symm
  have h := DFunLike.congr_fun hφ k
  change x⁻¹ * σ k x = 1 at h
  rw [inv_mul_eq_one] at h
  exact h.symm

omit [Finite G] in
theorem eq_one_of_mem_pCore_three {O : Subgroup G} (h3 : Nat.Coprime 3 (Nat.card O))
    {y : O ⧸ CFSG.pCore 2 O} (hy : y ∈ CFSG.pCore 3 (O ⧸ CFSG.pCore 2 O)) : y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 3) (G := O ⧸ CFSG.pCore 2 O) ⟨y, hy⟩
  have ha' : y ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have h1 : orderOf y ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ha'
  have h2 : orderOf y ∣ Nat.card O :=
    (orderOf_dvd_natCard y).trans (Subgroup.card_quotient_dvd_card _)
  have hcop : Nat.Coprime (3 ^ a) (Nat.card O) := Nat.Coprime.pow_left a h3
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end Res11

theorem kFactKO3Cent_of_layer (h : KFactKO3CentLayer) : KFactKO3Cent := by
  intro G _ _ hKP K O hO hperf htype hKN h3 hrank k hk o ho
  have := hperf
  set Q := CFSG.pCore 2 O with hQ
  set σ := Res11.quotAction hKN with hσdef
  have hfixP : ∀ p : ℕ, p.Prime → ∀ (k' : K), ∀ y ∈ CFSG.pCore p (O ⧸ Q), σ k' y = y := by
    intro p hp k' y hy
    by_cases hp5 : 5 ≤ p
    · exact Res11.fix_pCore htype hKN hp hp5 (hrank p hp hp5) k' hy
    · have hp23 : p = 2 ∨ p = 3 := by
        have := hp.two_le
        interval_cases p
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hp (by decide)
      rcases hp23 with rfl | rfl
      · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        rw [Sec18.pCore_quotient_pCore_eq_bot, Subgroup.mem_bot] at hy
        rw [hy, map_one]
      · rw [Res11.eq_one_of_mem_pCore_three h3 hy, map_one]
  have hfixF : ∀ (k' : K), ∀ y ∈ CFSG.fittingSubgroup (O ⧸ Q), σ k' y = y := by
    intro k' y hy
    rw [CFSG.fitting_eq_sup_pCore] at hy
    have hle : (⨆ p : (Nat.card (O ⧸ Q)).primeFactors.attach, CFSG.pCore p.1.1 (O ⧸ Q)) ≤
        RankThree.PartOne.FixedRank36.fixedSub (σ k') :=
      iSup_le fun p z hz => hfixP p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) k' z hz
    exact hle hy
  have hfixE : ∀ (k' : K), ∀ y ∈ CFSG.layer (O ⧸ Q), σ k' y = y := by
    intro k' y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q y
    have hmem : (x : G) ∈ oTwoLayer O := ⟨x, hy, rfl⟩
    exact Res11.quotAction_fix_of_comm_mem hKN k' x
      (h G hKP K O hO hperf htype hKN h3 hrank k' k'.2 x hmem)
  have hfix : ∀ k' : K, ∀ y ∈ CFSG.generalizedFitting (O ⧸ Q), σ k' y = y := by
    intro k' y hy
    have hle : CFSG.generalizedFitting (O ⧸ Q) ≤
        RankThree.PartOne.FixedRank36.fixedSub (σ k') :=
      sup_le (fun z hz => hfixF k' z hz) (fun z hz => hfixE k' z hz)
    exact hle hy
  have hσ : σ = 1 := Res11.eq_one_of_fix_generalizedFitting σ hfix
  exact Res11.comm_mem_of_quotAction_fix hKN ⟨k, hk⟩ ⟨o, ho⟩ (by rw [← hσdef, hσ]; rfl)

end CFSG.RankThree.PartTwo.Sec20

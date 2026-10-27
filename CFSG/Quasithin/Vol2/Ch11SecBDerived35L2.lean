module

public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Quasithin.Background.E2TwoCCases
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

structure L2Setting (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ)
    (H K : Subgroup G) (k : ℕ) : Prop where
  hyp : Hyp11 G T L I n
  hstar : IsHStar T (Subgroup.normalizer (L : Set G)) H
  moves : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥
  nParam : 1 < E1.nParam H ∧ E1.nParam H ≤ k
  two_le : 2 ≤ k
  comp : K ∈ cComp H
  gen : H = K ⊔ T
  quasisimple : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)
  cases : E2.E22CasesC H T (H ⊓ Subgroup.normalizer (L : Set G)) K

@[expose] def L2BadType (k : ℕ) (Y : Type) [Group Y] : Prop :=
  IsSz k Y ∨ IsPSU 3 2 k Y ∨ IsPSL 3 2 k Y ∨ E2.IsSp4Prime k Y

@[expose] def L2Faithful : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k → quasithinIsFaithfulLocal T K

@[expose] def L2Overgroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k → quasithinIsFaithfulLocal T K →
    L2BadType k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) →
      ∃ Kp Ip : Subgroup G, K ≤ Kp ∧ FSU G T Kp Ip

@[expose] def L2NotJ4Orth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k →
    L2BadType k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) →
    ∀ Kp Ip : Subgroup G, K ≤ Kp → FSU G T Kp Ip → ∀ _ : IsMulCommutative ↥(fsuV T Ip),
      ¬ Concl701J4 T Kp Ip ∧ ¬ Concl701Orth T Kp Ip

@[expose] def L2Graph : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k → T ≤ Subgroup.normalizer (K : Set G) →
    (IsPSL 3 2 k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) ∨
      E2.IsSp4Prime k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K)) →
    E2.IsDiagramNontrivial (E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H T)
      (E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K)
      (E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H (T ⊓ K)) →
    ∀ Kp Ip : Subgroup G, K ≤ Kp → FSU G T Kp Ip → ∀ _ : IsMulCommutative ↥(fsuV T Ip),
      Concl701FF T Kp Ip ∨ Concl701Four T Kp Ip → False

@[expose] def L2Suzuki : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k →
    IsSz k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) →
    ∀ Kp Ip : Subgroup G, K ≤ Kp → FSU G T Kp Ip → ∀ _ : IsMulCommutative ↥(fsuV T Ip),
      Concl701FF T Kp Ip ∨ Concl701Four T Kp Ip → False

@[expose] def L2Unitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k →
    IsPSU 3 2 k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) →
    ∀ Kp Ip : Subgroup G, K ≤ Kp → FSU G T Kp Ip → ∀ _ : IsMulCommutative ↥(fsuV T Ip),
      Concl701FF T Kp Ip ∨ Concl701Four T Kp Ip → False

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ker_le_center_of_starHom {H X K : Subgroup G} (hKH : K ≤ H)
    (hcent : ∀ k ∈ K, k ∈ kerIn X H → ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    {φ : ↥K ⧸ CFSG.Open.pCore 2 ↥K →* ↥(E2.star X H K)}
    (hφk : ∀ k : ↥K, ((φ (k : ↥K ⧸ CFSG.Open.pCore 2 ↥K) : ↥(E2.star X H K)) :
      E2.StarQuot X H) = QuotientGroup.mk' ((kerIn X H).subgroupOf H) (Subgroup.inclusion hKH k)) :
    φ.ker ≤ Subgroup.center (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
  have hmemO : ∀ x : ↥K, (x : G) ∈ pCoreOf 2 K → x ∈ CFSG.Open.pCore 2 ↥K := by
    rintro x ⟨x', hx', hxx'⟩
    rwa [show x = x' from Subtype.ext hxx'.symm]
  intro z hz
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  have hkJ : (k : G) ∈ kerIn X H := by
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    rw [hφk, QuotientGroup.mk'_apply, OneMemClass.coe_one, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  apply hmemO
  have := hcent _ (K.inv_mem k.2) ((kerIn X H).inv_mem hkJ) _ (K.inv_mem y.2)
  simpa [mul_assoc] using this

omit [Finite G] in
theorem exists_hom_SL2_of_isPSL {H X K : Subgroup G} (hKH : K ≤ H)
    (hOK : pCoreOf 2 K ≤ kerIn X H)
    (hcent : ∀ k ∈ K, k ∈ kerIn X H → ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K) {k : ℕ}
    (hP : IsPSL 2 2 k ↥(E2.star X H K)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      ∃ φ : ↥K ⧸ CFSG.pCore 2 ↥K →* Matrix.SpecialLinearGroup (Fin 2) F,
        Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨-, F, _, _, hFc, ⟨e⟩⟩ := hP
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := k) (by rw [← Nat.card_eq_fintype_card, hFc])
  have ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃*
      Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq KGNat.center_SL2_eq_bot).trans QuotientGroup.quotientBot
  have ε : ↥(E2.star X H K) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).trans
      ePSL
  obtain ⟨ψ, hψs, hψk⟩ := exists_starHom hKH hOK
  have hψc := ker_le_center_of_starHom hKH hcent hψk
  have e₀ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥K ⧸ CFSG.Open.pCore 2 ↥K :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)
  refine ⟨F, inferInstance, inferInstance, hFc, (ε.toMonoidHom.comp ψ).comp e₀.toMonoidHom,
    ε.surjective.comp (hψs.comp e₀.surjective), fun z hz => ?_⟩
  have h1 : e₀ z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    apply ε.injective
    rw [map_one]
    exact hz
  have h2 := Subgroup.mem_center_iff.mp (hψc h1)
  rw [Subgroup.mem_center_iff]
  intro g
  apply e₀.injective
  rw [map_mul, map_mul]
  exact h2 (e₀ g)

end CFSG.Quasithin.Vol2.Ch11.SecB

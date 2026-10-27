module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6Tw

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableB.TwE6

theorem cube_mem_torus₀ {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) {b : Fin 6 → Kˣ} (hb : b ∈ compat σ) :
    b ^ 3 ∈ torus₀ σ := by
  obtain ⟨x, hx⟩ := exists_mul_edge_inv_mem hq hK hσ hb
  have e : b ^ 3 = (b * (edge σ x)⁻¹) ^ 3 * edge σ (x ^ 3) := by
    rw [map_pow, mul_pow, inv_pow, inv_mul_cancel_right]
  rw [e]
  exact (torus₀ σ).mul_mem ((torus₀ σ).pow_mem hx 3) (edge_pow_three_mem (sigma_sigma hK hσ) x)

section RootSet

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r)) (n : ℕ) (K : Type)
  [Field K]

@[expose] def DiagCubeOn (S : (Fin r → ℤ) → Prop) : Prop :=
  ∀ a : Fin r → Kˣ,
    (∀ h ∈ MarkChev.twistedH A S K ρ n, ∃ h' ∈ MarkChev.twistedH A S K ρ n,
      (h' : Module.End K (MarkChev.Space S K)) * markDiag S K a = markDiag S K a * h) →
    ∃ g ∈ MarkChev.twistedH A S K ρ n,
      (g : Module.End K (MarkChev.Space S K)) = markDiag S K (a ^ 3)

variable {A ρ n K}

theorem DiagCubeOn.of_eq {S S' : (Fin r → ℤ) → Prop} (hS : S = S')
    (h : DiagCubeOn A ρ n K S) : DiagCubeOn A ρ n K S' :=
  hS ▸ h

theorem diagHom_pow_three_mem_of_diagCubeOn (h : DiagCubeOn A ρ n K (LargeEvenIsRoot A))
    {a : Fin r → Kˣ} (ha : ∀ x ∈ LargeEvenTwistedH A K ρ n,
      diagHom A K a * x * (diagHom A K a)⁻¹ ∈ LargeEvenTwistedH A K ρ n) :
    diagHom A K (a ^ 3) ∈ LargeEvenTwistedH A K ρ n := by
  rw [largeEvenTwistedH_eq] at ha ⊢
  obtain ⟨g, hg, hgd⟩ := h a fun x hx => ⟨_, ha x hx, by
    rw [← largeEvenDiagMap_eq_markDiag]
    exact (diag_rel_iff a x _).2 rfl⟩
  have hge : g = diagHom A K (a ^ 3) := Units.ext (by
    rw [hgd, coe_diagHom, largeEvenDiagMap_eq_markDiag])
  rw [← hge]
  exact hg

end RootSet


theorem diagCubeOn_isRoot {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    DiagCubeOn TwistTag.E6.tag.cartan TwistTag.E6.perm n K (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := iterateFrobenius_def 2 n
  have hq : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = graphFixedRootGroup TwistTag.E6 K σ := by
    rw [twistedH_eq_commutator K .E6 n σ hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  intro a ha
  rw [hC] at ha ⊢
  have hconj : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, rootDiagUnit TwistTag.E6.tag a * g *
      (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro g hg
    obtain ⟨h', hh', e⟩ := ha g hg
    rw [markDiag_isRoot] at e
    rw [← eq_conj_of_mul_rootDiag e]
    exact hh'
  have hT : ∀ c ∈ torus₀ σ,
      rootDiagUnit TwistTag.E6.tag c ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    rintro _ ⟨s, hs, rfl⟩
    exact rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs
  exact ⟨_, hT _ (cube_mem_torus₀ hq hK hσ fun i => compat_of_forall_conj_mem hconj i),
    (markDiag_isRoot _).symm⟩

theorem diagHom_pow_three_mem_twE6 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {a : Fin 6 → Kˣ}
    (ha : ∀ x ∈ LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n,
      diagHom (LargeEvenCartanE 6) K a * x * (diagHom (LargeEvenCartanE 6) K a)⁻¹ ∈
        LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) :
    diagHom (LargeEvenCartanE 6) K (a ^ 3) ∈
      LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n :=
  diagHom_pow_three_mem_of_diagCubeOn
    ((diagCubeOn_isRoot hn hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm) ha

end TableB.TwE6

namespace TwE6Delta

noncomputable abbrev RecipeH (K : Type) [Field K] (n : ℕ) :
    Subgroup (LargeEvenChevGL (LargeEvenCartanE 6) K) :=
  LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n

abbrev RecipeR (K : Type) [Field K] (n : ℕ) : Type :=
  LargeEvenCenterQuot (RecipeH K n)

abbrev RecipeI (K : Type) [Field K] (n : ℕ) : Set (MulAut (RecipeR K n)) :=
  LargeEvenChevIDImage (LargeEvenCartanE 6) K (RecipeH K n)

theorem odd_relIndex_of_pow_three_mem {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] {D : Subgroup G} (h : ∀ g ∈ D, g ^ 3 ∈ N) : Odd (N.relIndex D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (D ⧸ N.subgroupOf D) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H d =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact h d d.2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_card, hk]
  exact Odd.pow (by decide)

theorem center_quot_center_eq_bot {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥) :
    Subgroup.center (H ⧸ Subgroup.center H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H h =>
    have hh : h ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.mp hx (g : H ⧸ Subgroup.center H)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hZ,
        Subgroup.mem_bot] at h1
      exact inv_mul_eq_one.mp h1
    rw [hZ, Subgroup.mem_bot] at hh
    rw [hh, QuotientGroup.mk_one]
    exact Subgroup.one_mem _

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem finite_recipeH (hK : Nat.card K = (2 ^ n) ^ 2) :
    Finite (RecipeH K n) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨-, T, -, -⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n (iterateFrobenius K 2 n)
    (iterateFrobenius_def 2 n)
  exact Finite.of_equiv _ T.toEquiv

theorem finite_recipeR (hK : Nat.card K = (2 ^ n) ^ 2) :
    Finite (RecipeR K n) := by
  have := finite_recipeH hK
  infer_instance

theorem finite_mulAut_recipeR (hK : Nat.card K = (2 ^ n) ^ 2) :
    Finite (MulAut (RecipeR K n)) := by
  have := finite_recipeR hK
  exact Finite.of_injective (fun φ : MulAut (RecipeR K n) => (φ : RecipeR K n → RecipeR K n))
    DFunLike.coe_injective


theorem center_recipeH_eq_bot (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Subgroup.center (RecipeH K n) = ⊥ := by
  obtain ⟨hZ0, -⟩ := (InndiagE6.twistedNFOn_isRoot_E6 hn K hK).of_eq
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  show Subgroup.center (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) = ⊥
  rw [largeEvenTwistedH_eq]
  exact hZ0

theorem center_recipeR_eq_bot (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Subgroup.center (RecipeR K n) = ⊥ :=
  center_quot_center_eq_bot (center_recipeH_eq_bot hn hK)

theorem pow_three_mem_inn (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {φ : MulAut (RecipeR K n)} (hφ : φ ∈ RecipeI K n) :
    φ ^ 3 ∈ (MulAut.conj : RecipeR K n →* MulAut (RecipeR K n)).range := by
  set N := (MulAut.conj : RecipeR K n →* MulAut (RecipeR K n)).range with hN
  set π := QuotientGroup.mk' N with hπ
  set S : Set (MulAut (RecipeR K n) ⧸ N) :=
    π '' LargeEvenChevDiagImage (LargeEvenCartanE 6) K (RecipeH K n) with hS
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨φ₁, h₁, rfl⟩ _ ⟨φ₂, h₂, rfl⟩
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf h₁
    obtain ⟨b, hb⟩ := TableB.exists_isDiagOf h₂
    change π φ₁ * π φ₂ = π φ₂ * π φ₁
    rw [← map_mul, ← map_mul, TableBExc.isDiagOf_comm ha hb]
  have hcube : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro _ ⟨φ₁, h₁, rfl⟩
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf h₁
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      TableB.isDiagOf_eq_conj (TableB.isDiagOf_pow ha 3)
        (TableB.TwE6.diagHom_pow_three_mem_twE6 hn hK ha.1)]
    exact ⟨_, rfl⟩
  have hcS : ∀ x ∈ Subgroup.closure S, ∀ s ∈ S, Commute x s := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact fun s hs => hcomm y hy s hs
    | one => exact fun s _ => Commute.one_left s
    | mul y z _ _ hy hz => exact fun s hs => (hy s hs).mul_left (hz s hs)
    | inv y _ hy => exact fun s hs => (hy s hs).inv_left
  have hcC : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz => exact hcS x hx z hz
    | one => exact Commute.one_right x
    | mul z w _ _ hz hw => exact hz.mul_right hw
    | inv z _ hz => exact hz.inv_right
  have hC : ∀ x ∈ Subgroup.closure S, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hcube y hy
    | one => exact one_pow 3
    | mul y z hy' hz' hy hz => rw [(hcC y hy' z hz').mul_pow, hy, hz, one_mul]
    | inv y _ hy => rw [inv_pow, hy, inv_one]
  have hle : Subgroup.closure (LargeEvenInnSet (RecipeR K n) ∪
      LargeEvenChevDiagImage (LargeEvenCartanE 6) K (RecipeH K n)) ≤
      (Subgroup.closure S).comap π := by
    rw [Subgroup.closure_le]
    rintro ψ (⟨x, rfl⟩ | hψ)
    · show π (MulAut.conj x) ∈ Subgroup.closure S
      have hx : MulAut.conj x ∈ N := ⟨x, rfl⟩
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hx]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨ψ, hψ, rfl⟩
  have h1 := hC _ (hle hφ)
  rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem ggOutdiagPrime_twE6 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) : GGOutdiagPrime p (RecipeR K n) (RecipeI K n) := by
  intro φ hφ hφp
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)) hp.one_lt
  rw [← TableBExc.pow_mul_eq_self_of_mod hk hφp, pow_mul]
  exact Subgroup.pow_mem _ (pow_three_mem_inn hn hK hφ) k

theorem ggOutdiagOdd_twE6 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (p : ℕ) :
    GGOutdiagOdd p (RecipeR K n) (RecipeI K n) := by
  have := finite_mulAut_recipeR hK
  have hN := InndiagE6.ggInndiagNormal_twE6 hn K hK
  refine ⟨ggInndiag (RecipeR K n) (RecipeI K n), ⟨fun φ hφ α => hN.conj_mem α hφ⟩,
    fun φ hφ _ => subset_ggInndiag hφ, odd_relIndex_of_pow_three_mem fun φ hφ => ?_⟩
  have hle : ggInndiag (RecipeR K n) (RecipeI K n) ≤ Subgroup.closure (LargeEvenInnSet _ ∪
      LargeEvenChevDiagImage (LargeEvenCartanE 6) K (RecipeH K n)) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
    · rw [Subgroup.closure_le]
      exact fun ψ hψ => hψ
  exact pow_three_mem_inn hn hK (hle hφ)

end TwE6Delta

end CFSG.StandardType

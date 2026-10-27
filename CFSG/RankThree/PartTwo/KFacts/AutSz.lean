module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

variable (a : ℕ) (K : Type) [Field K]

@[expose] noncomputable def stdPinnedSz : PinnedAut (suzukiGroup a K) where
  inndiag := (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).range
  inn_le := le_rfl
  field := (szFieldAut a K).range
  graph := ∅

variable {a K}

theorem exists_conj_mul_szFieldAut (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : MulAut (suzukiGroup a K)) :
    ∃ (g : suzukiGroup a K) (σ : RingAut K), α = MulAut.conj g * szFieldAut a K σ := by
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  refine ⟨(e.symm α).left, (e.symm α).right, ?_⟩
  rw [← he]
  exact (e.apply_symm_apply α).symm

theorem stdPinnedSz_stable (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (stdPinnedSz a K).Stable := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hcomm : ∀ σ τ : RingAut K,
      szFieldAut a K σ * szFieldAut a K τ = szFieldAut a K τ * szFieldAut a K σ :=
    fun σ τ => by
      rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  have hconj : ∀ α : MulAut (suzukiGroup a K), ∃ g : suzukiGroup a K, ∀ τ : RingAut K,
      α * szFieldAut a K τ * α⁻¹ = MulAut.conj g * szFieldAut a K τ * (MulAut.conj g)⁻¹ := by
    intro α
    obtain ⟨g, σ, rfl⟩ := exists_conj_mul_szFieldAut ha hK α
    refine ⟨g, fun τ => ?_⟩
    have h1 := hcomm σ τ
    calc MulAut.conj g * szFieldAut a K σ * szFieldAut a K τ *
          (MulAut.conj g * szFieldAut a K σ)⁻¹ =
        MulAut.conj g * (szFieldAut a K σ * szFieldAut a K τ) * (szFieldAut a K σ)⁻¹ *
          (MulAut.conj g)⁻¹ := by group
      _ = MulAut.conj g * szFieldAut a K τ * (MulAut.conj g)⁻¹ := by rw [h1]; group
  refine ⟨⟨fun d hd α => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hd
    exact ⟨α y, (mul_mulAutConj_mul_inv α y).symm⟩
  · rintro α _ ⟨τ, rfl⟩ h1
    obtain ⟨g, hg⟩ := hconj α
    exact ⟨szFieldAut a K τ, ⟨τ, rfl⟩, h1, MulAut.conj g, ⟨g, rfl⟩, hg τ⟩
  · rintro α γ hγ
    exact absurd hγ (Set.notMem_empty γ)
  · rintro α γ φ hγ
    exact absurd hγ (Set.notMem_empty γ)

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (a K) in
@[expose] def InducesKindSz (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* suzukiGroup a K, InducesKind L (stdPinnedSz a K) e x k

theorem inducesKindSz_iff (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* suzukiGroup a K) (x : G) (k : AutKind) :
    InducesKindSz a K L x k ↔ InducesKind L (stdPinnedSz a K) e x k := by
  constructor
  · rintro ⟨e', h⟩
    exact (inducesKind_iff_of_stable L (stdPinnedSz_stable ha hK) e' e x k).1 h
  · intro h
    exact ⟨e, h⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts

module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

@[expose] def HasTwoSix (S : Type*) [Group S] : Prop :=
  ∃ T : Subgroup S, (∀ t ∈ T, t * t = 1) ∧ Nat.card T = 2 ^ 6

@[expose] def FourCubeSeven {S : Type*} [Group S] (A : Subgroup S) (x : S) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ Nat.card A = 4 ^ 3 ∧ (∀ a ∈ A, a ^ 4 = 1) ∧
    Nat.card {a : A | a ^ 2 = 1} = 2 ^ 3 ∧ orderOf x = 7 ∧ x ∈ normalizer (A : Set S) ∧
    ∀ a ∈ A, a ^ 2 = 1 → x * a * x⁻¹ = a → a = 1

@[expose] def fixedSubgroup {P : Type*} [Group P] (σ : MulAut P) : Subgroup P :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id P)

theorem mem_fixedSubgroup {P : Type*} [Group P] (σ : MulAut P) (x : P) :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

@[expose] noncomputable def conjAction {M : Type*} [Group M] (K S : Subgroup M)
    (hKS : K ≤ normalizer (S : Set M)) : ↥K →* MulAut ↥S :=
  S.normalizerMonoidHom.comp (Subgroup.inclusion hKS)

theorem conjAction_apply {M : Type*} [Group M] (K S : Subgroup M)
    (hKS : K ≤ normalizer (S : Set M)) (k : K) (s : S) :
    ((conjAction K S hKS k s : S) : M) = (k : M) * (s : M) * (k : M)⁻¹ := rfl


theorem isPGroup_pCoreOf {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) :
    IsPGroup p (CFSG.Open.pCoreOf p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

theorem mem_pCoreOf_conj {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) {g : G} (hg : g ∈ H)
    (x : G) : x ∈ CFSG.Open.pCoreOf p H ↔ g * x * g⁻¹ ∈ CFSG.Open.pCoreOf p H := by
  have key : ∀ {g : G}, g ∈ H → ∀ x : G, x ∈ CFSG.Open.pCoreOf p H →
      g * x * g⁻¹ ∈ CFSG.Open.pCoreOf p H := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : H) * y * (⟨g, hg⟩ : H)⁻¹, ?_, rfl⟩
    exact (CFSG.pCore_normal (p := p) (G := ↥H)).conj_mem y hy ⟨g, hg⟩
  refine ⟨key hg x, fun h => ?_⟩
  have h' := key (inv_mem hg) _ h
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h'

end CFSG.RankThree.PartTwo.Sec13.F135Last

module

public import CFSG.Quasithin.Vol2.Ch6Sec2Residuals

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

@[expose] def Res627T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    ∀ (t : G) (A D : Subgroup G) (g : G), t ∈ T → IsInvolutoryFieldAut L t →
    let U := V ⊓ Subgroup.centralizer ({t} : Set G)
    let H := Subgroup.centralizer (U : Set G)
    let UH := conjClosure V H
    let R := ch6Q T V ⊔ Subgroup.zpowers t
    let LU := oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G))
    let B := ⁅V, A⁆
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (M ⊓ Subgroup.normalizer (U : Set G)) →
    QuasithinUnique.CharTwo H → IsSylowIn 2 R H →
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (thompsonJ R : Set G) →
    Subgroup.normalizer (thompsonJ R : Set G) ≤ M →
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (Subgroup.normalizer (U : Set G)) →
    (T ⊓ Subgroup.normalizer (U : Set G)).relIndex T = 2 → wClos V 0 R ≤ ch6Q T V →
    IsElemAbelian 2 UH → UH ≤ pCoreOf 2 H → ⁅UH, pCoreOf 2 H⁆ ≤ U →
    centralizerMod U H UH = pCoreOf 2 H → IsReducedMod H UH U →
    Nat.card LU = 3 * Nat.card (pCoreOf 2 LU) → pCoreOf 2 LU = LU ⊓ H →
    A = conjSubgroup V g → V ≤ Subgroup.normalizer (A : Set G) →
    ¬ A ≤ Subgroup.normalizer (V : Set G) → V ⊓ Subgroup.centralizer (A : Set G) = U → A ≤ H →
    UH ≤ conjSubgroup T g → B = conjSubgroup (ch6ZS T L V) g → Nat.card B = 4 →
    A ⊓ Subgroup.normalizer (V : Set G) = B →
    UH ≤ Subgroup.normalizer (A : Set G) → UH = V ⊔ (UH ⊓ Subgroup.centralizer (A : Set G)) →
    ⁅UH, A⁆ = B → mQuot UH (UH ⊓ Subgroup.centralizer (A : Set G)) = 2 →
    (∀ U₀ : Subgroup G, UH ⊓ Subgroup.centralizer (A : Set G) < U₀ → U₀ ≤ UH →
      A ⊓ Subgroup.centralizer (U₀ : Set G) = B) →
    A ⊓ centralizerMod U H UH = B →
    D ≤ LU → Nat.card D = 3 → ⁅V, D⁆ = V →
    (∀ K : Subgroup G, K ≤ H → A ≤ K →
      (∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈
        centralizerMod U (Subgroup.normalizer (U : Set G)) UH) →
      ¬ ⁅⁅UH, K⁆, D⁆ ≤ U) →
        B ⊓ U ≠ ⊥ →
    False

@[expose] def Res627Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    ∀ (t : G) (A D : Subgroup G) (g : G), t ∈ T → IsInvolutoryFieldAut L t →
    let U := V ⊓ Subgroup.centralizer ({t} : Set G)
    let H := Subgroup.centralizer (U : Set G)
    let UH := conjClosure V H
    let R := ch6Q T V ⊔ Subgroup.zpowers t
    let LU := oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G))
    let B := ⁅V, A⁆
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (M ⊓ Subgroup.normalizer (U : Set G)) →
    QuasithinUnique.CharTwo H → IsSylowIn 2 R H →
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (thompsonJ R : Set G) →
    Subgroup.normalizer (thompsonJ R : Set G) ≤ M →
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (Subgroup.normalizer (U : Set G)) →
    (T ⊓ Subgroup.normalizer (U : Set G)).relIndex T = 2 → wClos V 0 R ≤ ch6Q T V →
    IsElemAbelian 2 UH → UH ≤ pCoreOf 2 H → ⁅UH, pCoreOf 2 H⁆ ≤ U →
    centralizerMod U H UH = pCoreOf 2 H → IsReducedMod H UH U →
    Nat.card LU = 3 * Nat.card (pCoreOf 2 LU) → pCoreOf 2 LU = LU ⊓ H →
    A = conjSubgroup V g → V ≤ Subgroup.normalizer (A : Set G) →
    ¬ A ≤ Subgroup.normalizer (V : Set G) → V ⊓ Subgroup.centralizer (A : Set G) = U → A ≤ H →
    UH ≤ conjSubgroup T g → B = conjSubgroup (ch6ZS T L V) g → Nat.card B = 4 →
    A ⊓ Subgroup.normalizer (V : Set G) = B →
    UH ≤ Subgroup.normalizer (A : Set G) → UH = V ⊔ (UH ⊓ Subgroup.centralizer (A : Set G)) →
    ⁅UH, A⁆ = B → mQuot UH (UH ⊓ Subgroup.centralizer (A : Set G)) = 2 →
    (∀ U₀ : Subgroup G, UH ⊓ Subgroup.centralizer (A : Set G) < U₀ → U₀ ≤ UH →
      A ⊓ Subgroup.centralizer (U₀ : Set G) = B) →
    A ⊓ centralizerMod U H UH = B →
    D ≤ LU → Nat.card D = 3 → ⁅V, D⁆ = V →
    (∀ K : Subgroup G, K ≤ H → A ≤ K →
      (∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈
        centralizerMod U (Subgroup.normalizer (U : Set G)) UH) →
      ¬ ⁅⁅UH, K⁆, D⁆ ≤ U) →
        B ⊓ U = ⊥ →
    (∀ A₁ : Subgroup G, B < A₁ → A₁ ≤ A →
      centralizerMod U UH A₁ ≤ Subgroup.centralizer (A : Set G)) →
    mQuot UH (centralizerMod U UH A) = 2 →
    False

theorem res627FF_of_TQ (hT : Res627T) (hQ : Res627Q) : Res627FF := by
  intro G _ _ T M L V h t A D g ht hf U H UH R LU B a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34
  by_cases hBU : B ⊓ U = ⊥
  · have hUHH : UH ≤ H := a10.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    have hstar : ∀ A₁ : Subgroup G, B < A₁ → A₁ ≤ A →
        centralizerMod U UH A₁ ≤ Subgroup.centralizer (A : Set G) := by
      intro A₁ hBA₁ hA₁A u hu
      obtain ⟨huUH, -, hc⟩ := hu
      have huA₁ : u ∈ Subgroup.centralizer (A₁ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h1 : u * a * u⁻¹ * a⁻¹ ∈ B := by
          rw [← a27]
          have := Subgroup.commutator_mem_commutator huUH (hA₁A ha)
          rwa [commutatorElement_def] at this
        have h2 : u * a * u⁻¹ * a⁻¹ ∈ B ⊓ U := ⟨h1, hc a ha⟩
        rw [hBU, Subgroup.mem_bot] at h2
        have e : u * a = a * u := by
          calc u * a = (u * a * u⁻¹ * a⁻¹) * (a * u) := by group
            _ = a * u := by rw [h2, one_mul]
        exact e.symm
      by_contra hu'
      have hlt : UH ⊓ Subgroup.centralizer (A : Set G) <
          UH ⊓ Subgroup.centralizer (A₁ : Set G) := by
        refine lt_of_le_of_ne (inf_le_inf_left _ (Subgroup.centralizer_le hA₁A)) ?_
        intro heq
        have : u ∈ UH ⊓ Subgroup.centralizer (A₁ : Set G) := ⟨huUH, huA₁⟩
        rw [← heq] at this
        exact hu' this.2
      have hcA := a29 _ hlt inf_le_left
      have hA₁B : A₁ ≤ B := by
        rw [← hcA]
        refine le_inf hA₁A fun a ha => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact ((Subgroup.mem_centralizer_iff.mp hw.2) a ha).symm
      exact hBA₁.not_ge hA₁B
    have hBA : B < A := by
      refine lt_of_le_of_ne (a24 ▸ inf_le_left) fun hBA => a18 ?_
      rw [← hBA, ← a24]
      exact inf_le_right
    have heq : centralizerMod U UH A = UH ⊓ Subgroup.centralizer (A : Set G) := by
      apply le_antisymm
      · exact fun u hu => ⟨hu.1, hstar A hBA le_rfl hu⟩
      · intro u hu
        refine ⟨hu.1, Subgroup.centralizer_le_normalizer _ (hUHH hu.1), fun a ha => ?_⟩
        have e : u * a * u⁻¹ * a⁻¹ = 1 := by
          rw [(Subgroup.mem_centralizer_iff.mp hu.2 a ha).symm]
          group
        rw [e]
        exact U.one_mem
    have hmq : mQuot UH (centralizerMod U UH A) = 2 := by rw [heq]; exact a28
    exact hQ G T M L V h t A D g ht hf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
      a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 hBU hstar hmq
  · exact hT G T M L V h t A D g ht hf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
      a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 hBU

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Background.C116Three.ModuleDefs

import CFSG.Quasithin.EmptyFaithful.T1515gD
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.EmptyFaithful.R3c23PairAFac

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

theorem le_ffJ_of_jPair {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V} (P : JPair X L₁ L₂ τ) :
    L₂ ≤ ffJ X := by
  intro k hk
  rw [P.conj] at hk
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
  exact (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X P.τ_mem) l).mp (P.L₁J hl)

theorem case1_false (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (P : JPair X L₁ L₂ τ) : ¬ B56Case1 (ffJ X) := by
  rintro ⟨hF, -, -⟩
  set J := ffJ X with hJdef
  set F := quasithinGenFitting J with hFdef
  have hJX : J ≤ X := B6.ffJ_le X
  have hFJ : F ≤ J := quasithinGenFitting_le J
  have hL₂J : L₂ ≤ J := le_ffJ_of_jPair P
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le P.L₁J hL₂J
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hL₁n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ :=
    InternalSec.conj_mem_of_mem_sup_of_commute P.comm
  have hL₂n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := by
    rw [sup_comm]
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc'
  have hLJn : ((L₁ ⊔ L₂).subgroupOf J).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g (hJX g.2) n hn⟩
  have hcomp : ∀ {A : Subgroup (MulAut V)}, A ≤ L₁ ⊔ L₂ →
      (∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ A, x * k * x⁻¹ ∈ A) → CFSG.IsQuasisimple ↥A → A ≤ F := by
    intro A hAL hAn hAq
    have hA : (A.subgroupOf (L₁ ⊔ L₂)).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hAn g g.2 n hn⟩
    have hsub : CFSG.Open.IsSubnormal A J :=
      CFSG.Open.IsSubnormal.step hAL hA
        (CFSG.Open.IsSubnormal.step hLJ hLJn (CFSG.Open.IsSubnormal.refl J))
    have hc : CFSG.Open.IsComponentOf A J :=
      ⟨hAL.trans hLJ, hsub, B1Red.isQuasisimple_to_open hAq⟩
    exact (le_sSup (show A ∈ {K | CFSG.Open.IsComponentOf K J} from hc)).trans le_sup_right
  have hL₁F : L₁ ≤ F := hcomp le_sup_left hL₁n P.q₁
  have hL₂F : L₂ ≤ F := hcomp le_sup_right hL₂n P.q₂
  have hLF : L₁ ⊔ L₂ ≤ F := sup_le hL₁F hL₂F
  have hLFn : ((L₁ ⊔ L₂).subgroupOf F).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g (hJX (hFJ g.2)) n hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hF) ((L₁ ⊔ L₂).subgroupOf F) with hcen | htop
  · refine InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb => ?_
    have h1 : (⟨a, hL₁F ha⟩ : ↥F) ∈ Subgroup.center ↥F :=
      hcen (show (⟨a, hL₁F ha⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F from Subgroup.mem_sup_left ha)
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hL₁F hb⟩
    exact (congrArg Subtype.val h2).symm
  · have hFL : F ≤ L₁ ⊔ L₂ := fun x hx => by
      have : (⟨x, hx⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F := htop ▸ Subgroup.mem_top _
      exact this
    have h1 : L₁ = F := twoG_eq_of_normal_of_isQuasisimple hL₁F
      (fun x hx k hk => hL₁n x (hFL hx) k hk) P.q₁ hF
    have h2 : L₂ = F := twoG_eq_of_normal_of_isQuasisimple hL₂F
      (fun x hx k hk => hL₂n x (hFL hx) k hk) P.q₂ hF
    have h12 : L₁ = L₂ := h1.trans h2.symm
    exact InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb =>
      P.comm a ha b (h12 ▸ hb)

theorem case2_false (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (P : JPair X L₁ L₂ τ) : ¬ B56Case2 (ffJ X) := by
  rintro ⟨⟨e⟩, -, -⟩
  exact InternalSec.not_le_perm_three P.q₁ P.L₁J e

theorem case4_false (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (P : JPair X L₁ L₂ τ) : ¬ B56Case4 (ffJ X) := by
  rintro ⟨G₁, G₂, t, hJt, -, hcomm, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -, -⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htN := InternalSec.mem_normalizer_sup ht₁ ht₂
  have hsol : Group.IsSolvable ↥G₂ := by
    have := isCyclic_of_prime_card hc₂
    infer_instance
  have hG₁J : G₁ ≤ ffJ X := by
    rw [hJt]
    exact (le_sup_left : G₁ ≤ G₁ ⊔ G₂).trans le_sup_left
  have hle : ∀ L : Subgroup (MulAut V), L ≤ ffJ X → CFSG.IsQuasisimple ↥L → L ≤ G₁ := by
    intro L hLJ hLq
    have h1 : L ≤ ⁅ffJ X, ffJ X⁆ := InternalSec.le_commutator_of_perfect hLJ hLq.1
    rw [hJt] at h1
    exact twoG_le_of_perfect_of_isSolvable hcomm
      (h1.trans (InternalSec.commutator_le_of_zpowers htN)) hLq.1 hsol
  have hL₁G : L₁ ≤ G₁ := hle L₁ P.L₁J P.q₁
  have hL₂G : L₂ ≤ G₁ := hle L₂ (le_ffJ_of_jPair P) P.q₂
  have hG₁q : CFSG.IsQuasisimple ↥G₁ :=
    LocalCores.isQuasisimple_of_mulEquiv e₁.symm a7_isQuasisimple_alt6
  have hn : ∀ x ∈ G₁, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.mp (P.Jn x (hG₁J hx)) k).mp hk
  have h1 : L₁ = G₁ := twoG_eq_of_normal_of_isQuasisimple hL₁G hn P.q₁ hG₁q
  have hL₂L₁ : L₂ ≤ L₁ := by
    rw [h1]
    exact hL₂G
  exact InternalSec.not_commute_of_isQuasisimple P.q₂ fun a ha b hb =>
    P.comm a (hL₂L₁ ha) b hb

end CFSG.Quasithin.C116Three

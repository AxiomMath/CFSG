module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BSplit
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BFrames
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoTorus
public import CFSG.RankThree.PartOne.KF4.A2FrameToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open scoped MatrixGroups

private theorem noOrthSameLength_holds :
    ∀ κ ∈ [(1 : ℤ), 2], ∀ s ∈ rts, ipL s s = 2 * κ → ∀ t ∈ rts, ipL t t = 2 * κ → ipL s t = -κ →
      ∀ u ∈ rts, ipL u u = 2 * κ → ipL s u = 0 → ipL t u = 0 → False := by decide +kernel

private theorem not_orth_same_length {κ : ℤ} (hκ : κ = 1 ∨ κ = 2)
    {s t u : V4} (hs : IsRoot Tag.F4 s) (ht : IsRoot Tag.F4 t) (hu : IsRoot Tag.F4 u)
    (hss : ipF4 s s = 2 * κ) (htt : ipF4 t t = 2 * κ) (hst : ipF4 s t = -κ)
    (huu : ipF4 u u = 2 * κ) (hsu : ipF4 s u = 0) (htu : ipF4 t u = 0) : False := by
  obtain ⟨ls, hls, rfl⟩ := (mem_rts_iff s).1 hs
  obtain ⟨lt, hlt, rfl⟩ := (mem_rts_iff t).1 ht
  obtain ⟨lu, hlu, rfl⟩ := (mem_rts_iff u).1 hu
  rw [ipF4_vec4] at hss htt hst huu hsu htu
  exact noOrthSameLength_holds κ (by rcases hκ with rfl | rfl <;> simp) ls hls hss lt hlt htt hst
    lu hlu huu hsu htu

private theorem ipF4_self_of_mem_a2Roots {α β γ : V4} (h : IsA2Pair α β)
    (hγ : γ ∈ a2Roots α β) : ipF4 γ γ = ipF4 α α := by
  have hβ : ipF4 β β = ipF4 α α := by rw [← iform_F4, ← iform_F4]; exact h.iform_snd
  have hαβ : 2 * ipF4 α β = -ipF4 α α := by rw [← iform_F4, ← iform_F4]; exact h.two_iform
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact ipF4_neg_neg α
  · exact hβ
  · rw [ipF4_neg_neg]; exact hβ
  · rw [ipF4_add_left, ipF4_add_right, ipF4_add_right, ipF4_comm β α]; linarith
  · rw [ipF4_neg_neg, ipF4_add_left, ipF4_add_right, ipF4_add_right, ipF4_comm β α]; linarith


theorem f4_a2Pair_of_strOrth {α β α' β' : Fin Tag.F4.rank → ℤ} (h₁ : IsA2Pair α β)
    (h₂ : IsA2Pair α' β') (ho : PairsStrOrth (α, β) (α', β')) {σ τ : Fin 3 → Fin 3 → V4}
    (hσ : ∀ x y, x ≠ y → σ x y ∈ a2Roots α β) (hτ : ∀ x y, x ≠ y → τ x y ∈ a2Roots α' β')
    (hσadd : ∀ x y z, σ x y + σ y z = σ x z) (hτadd : ∀ x y z, τ x y + τ y z = τ x z) :
    ∃ κ κ', A2Pair σ τ κ κ' := by
  have hn₁ := iform_self_cases noG2_F4 h₁.isRoot_fst
  have hn₂ := iform_self_cases noG2_F4 h₂.isRoot_fst
  rw [iform_F4] at hn₁ hn₂
  obtain ⟨κ, hκ, hακ⟩ : ∃ κ : ℤ, (κ = 1 ∨ κ = 2) ∧ ipF4 α α = 2 * κ := by
    rcases hn₁ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨2, Or.inr rfl, by rw [h]; norm_num⟩
  obtain ⟨κ', hκ', hακ'⟩ : ∃ κ' : ℤ, (κ' = 1 ∨ κ' = 2) ∧ ipF4 α' α' = 2 * κ' := by
    rcases hn₂ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨2, Or.inr rfl, by rw [h]; norm_num⟩
  have hα_mem : α ∈ a2Roots α β := by simp [a2Roots]
  have hβ_mem : β ∈ a2Roots α β := by simp [a2Roots]
  have hα'_mem : α' ∈ a2Roots α' β' := by simp [a2Roots]
  have hβ : ipF4 β β = 2 * κ := by rw [ipF4_self_of_mem_a2Roots h₁ hβ_mem, hακ]
  have hαβ : ipF4 α β = -κ := by
    have := h₁.two_iform
    rw [iform_F4, iform_F4, hακ] at this
    linarith
  have horth : ∀ γ ∈ a2Roots α β, ∀ δ ∈ a2Roots α' β', ipF4 γ δ = 0 := fun γ hγ δ hδ => by
    rw [← iform_F4]
    exact (ho γ hγ δ hδ).1
  have hκκ' : κ ≠ κ' := by
    intro he
    subst he
    exact not_orth_same_length hκ h₁.isRoot_fst h₁.isRoot_snd h₂.isRoot_fst hακ hβ hαβ hακ'
      (horth α hα_mem α' hα'_mem) (horth β hβ_mem α' hα'_mem)
  refine ⟨κ, κ', ⟨?_, fun x y hxy => a2Roots_isRoot h₁ _ (hσ x y hxy),
    fun x y hxy => a2Roots_isRoot h₂ _ (hτ x y hxy), hσadd, hτadd,
    fun x y hxy => by rw [ipF4_self_of_mem_a2Roots h₁ (hσ x y hxy), hακ],
    fun x y hxy => by rw [ipF4_self_of_mem_a2Roots h₂ (hτ x y hxy), hακ'],
    fun x y x' y' hxy hxy' => horth _ (hσ x y hxy) _ (hτ x' y' hxy')⟩⟩
  rcases hκ with rfl | rfl <;> rcases hκ' with rfl | rfl
  · exact absurd rfl hκκ'
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hκκ'


theorem f4_a2a2_exists_cover {L : Type} [Field L] [IsAlgClosed L] (a : Fin Tag.F4.rank → Lˣ)
    (ha : ∀ i, a i ^ 3 = 1) (h12 : (rootCharKernel (τ := Tag.F4) a).ncard = 12) :
    ∃ (σ τ : Fin 3 → Fin 3 → V4) (κ κ' : ℤ) (ψ ψ' : SL(3, L) →* ModGL Tag.F4 L)
      (hc : ∀ A B, Commute (ψ A) (ψ' B)),
      A2Pair σ τ κ κ' ∧ IsA2Frame ψ σ ∧ IsA2Frame ψ' τ ∧
      toralCentralizer Tag.F4 L a = (ψ.noncommCoprod ψ' hc).range ∧
      (ψ.noncommCoprod ψ' hc).ker ≤ Subgroup.center (SL(3, L) × SL(3, L)) := by
  obtain ⟨α, β, α', β', h₁, h₂, ho, hk⟩ := f4_a2a2_kernel_split L a ha h12
  obtain ⟨hM, -, -, -⟩ := f4_a2a2_group_split L a ha h₁ h₂ ho hk
  obtain ⟨ψ, σ, hψ, -, -, hσset⟩ := f4_exists_a2Frame h₁ L
  obtain ⟨ψ', τ, hψ', -, -, hτset⟩ := f4_exists_a2Frame h₂ L
  have hσ : ∀ x y, x ≠ y → σ x y ∈ a2Roots α β := fun x y hxy => by
    rw [← hσset]
    exact ⟨x, y, hxy, rfl⟩
  have hτ : ∀ x y, x ≠ y → τ x y ∈ a2Roots α' β' := fun x y hxy => by
    rw [← hτset]
    exact ⟨x, y, hxy, rfl⟩
  obtain ⟨κ, κ', hP⟩ := f4_a2Pair_of_strOrth h₁ h₂ ho hσ hτ hψ.add hψ'.add
  have hc : ∀ A B, Commute (ψ A) (ψ' B) := fun A B => hP.commute_frames hψ hψ' A B
  refine ⟨σ, τ, κ, κ', ψ, ψ', hc, hP, hψ, hψ', ?_,
    IsA2Frame.ker_noncommCoprod_le_center hψ hψ' hc⟩
  have hrψ : ψ.range = rootSpan Tag.F4 L (a2Roots α β) := by rw [hψ.range, hσset]
  have hrψ' : ψ'.range = rootSpan Tag.F4 L (a2Roots α' β') := by rw [hψ'.range, hτset]
  rw [MonoidHom.noncommCoprod_range, hM]
  refine le_antisymm (sup_le (hP.torusGroup_le_sup_range hψ hψ') (le_of_eq ?_)) ?_
  · rw [hrψ, hrψ']
  · rw [hrψ, hrψ']
    exact le_sup_right

end Irred937

end CFSG.StandardType

end

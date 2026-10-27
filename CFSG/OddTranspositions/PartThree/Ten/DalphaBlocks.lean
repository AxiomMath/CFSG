module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.BlockGraph

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem smul_mem_Dalpha_of_mem_Halpha (hC : HypothesisC D) {h : G}
    (hh : h ∈ Halpha D hC.alpha) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    (fun y => h * y * h⁻¹) '' β ∈ Dalpha D hC.alpha := by
  have hstab : Halpha D hC.alpha ≤ (MulAction.stabilizer (ConjAct G)
      (Dalpha D hC.alpha)).comap (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom := by
    rw [Halpha, Subgroup.closure_le]
    rintro x ⟨γ, hγ, hxγ⟩
    change ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct G) (Dalpha D hC.alpha)
    have hfix : ConjAct.toConjAct x • hC.alpha = hC.alpha := by
      rw [← Set.image_smul]
      have : ∀ a ∈ hC.alpha, ConjAct.toConjAct x • a = a := fun a ha => by
        rw [ConjAct.toConjAct_smul, ← (hγ.2.2.2 a ha x hxγ).eq, mul_inv_cancel_right]
      rw [Set.image_congr this, Set.image_id']
    rw [MulAction.mem_stabilizer_iff, smul_Dalpha hC.setup.normal, hfix]
  have h1 : ConjAct.toConjAct h ∈ MulAction.stabilizer (ConjAct G) (Dalpha D hC.alpha) :=
    hstab hh
  rw [MulAction.mem_stabilizer_iff] at h1
  have h2 : ConjAct.toConjAct h • β ∈ ConjAct.toConjAct h • Dalpha D hC.alpha :=
    Set.smul_mem_smul_set hβ
  rw [h1] at h2
  have himg : ConjAct.toConjAct h • β = (fun y => h * y * h⁻¹) '' β := by
    rw [← Set.image_smul]
    rfl
  rwa [himg] at h2

omit [Finite G] in
theorem eq_or_disjoint_of_mem_blockClass {α γ δ : Set G} (hN : IsNormalSet D) (hα : IsBlock D α)
    (hγ : γ ∈ blockClass α) (hδ : δ ∈ blockClass α) : γ = δ ∨ Disjoint γ δ := by
  by_cases h : γ = δ
  · exact Or.inl h
  right
  obtain ⟨g, hg⟩ := mem_blockClass_of_mem_blockClass hγ hδ
  have hγb : MulAction.IsBlock (ConjAct G) γ := (isBlock_of_mem_blockClass hN hα hγ).isBlock
  rw [MulAction.isBlock_iff_disjoint_smul_of_ne] at hγb
  have hne : g • γ ≠ γ := by
    rw [← hg]
    exact fun h' => h h'.symm
  rw [hg] at *
  exact (hγb hne).symm

theorem conj_image_eq_of_mem (hC : HypothesisC D) {h : G} (hh : h ∈ Halpha D hC.alpha)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {x : G} (hx : x ∈ β) (hhx : h * x * h⁻¹ ∈ β) :
    (fun y => h * y * h⁻¹) '' β = β := by
  have hγ := smul_mem_Dalpha_of_mem_Halpha hC hh hβ
  rcases eq_or_disjoint_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ.1 hβ.1 with
    h' | h'
  · exact h'
  · exact absurd hhx (Set.disjoint_left.1 h' ⟨x, hx, rfl⟩)

omit [Finite G] in
theorem conj_mem_iff_of_conj_image_eq {h : G} {β : Set G}
    (himg : (fun y => h * y * h⁻¹) '' β = β) (z : G) : h * z * h⁻¹ ∈ β ↔ z ∈ β := by
  constructor
  · intro hz
    rw [← himg] at hz
    obtain ⟨z', hz', hz'eq⟩ := hz
    have : z' = z := by simpa using hz'eq
    rwa [← this]
  · intro hz
    rw [← himg]
    exact ⟨z, hz, rfl⟩

theorem alpha_eq_singleton_of_mem_Dalpha (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {v : G} (hv : β = {v}) : hC.alpha = {hC.d} := by
  obtain ⟨g, hg⟩ := hβ.1
  have hα : hC.alpha = g⁻¹ • β := by rw [hg, inv_smul_smul]
  rw [hv, Set.smul_set_singleton] at hα
  have hd : hC.d = g⁻¹ • v := by
    have := hC.d_mem_alpha
    rwa [hα, Set.mem_singleton_iff] at this
  rw [hα, hd]

omit [Finite G] in
theorem mem_DalphaStar_of_alpha_eq_singleton (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {x : G} (hxD : x ∈ D) (hxd : x ≠ hC.d) (hcomm : Commute x hC.d) :
    x ∈ DalphaStar D hC.alpha := by
  obtain ⟨k, hk⟩ := isConj_iff.1 (hC.setup.isConj hC.hd hxD)
  refine ⟨{x}, ⟨⟨ConjAct.toConjAct k, ?_⟩, ?_, ?_, ?_⟩, rfl⟩
  · rw [hα, Set.smul_set_singleton, ConjAct.toConjAct_smul, hk]
  · simpa using hxD
  · rw [hα]
    exact fun h => hxd (Set.singleton_eq_singleton_iff.1 h)
  · rw [hα]
    rintro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
    exact hcomm.symm

omit [Finite G] in
theorem Dalpha_eq_singleton_of_Dalpha_eq_singleton {α β : Set G} (hN : IsNormalSet D)
    (hαD : α ⊆ D) (hβ : β ∈ Dalpha D α) (hDα : Dalpha D α = {β}) : Dalpha D β = {α} := by
  obtain ⟨g, hg⟩ := hβ.1
  have hαDβ : α ∈ Dalpha D β :=
    ⟨mem_blockClass_of_mem_blockClass hβ.1 (mem_blockClass_self _), hαD, hβ.2.2.1.symm,
      fun a ha b hb => (hβ.2.2.2 b hb a ha).symm⟩
  have h1 : Dalpha D β = {g • β} := by
    rw [hg, ← smul_Dalpha hN g, hDα, Set.smul_set_singleton, ← hg]
  rw [h1] at hαDβ ⊢
  rw [Set.mem_singleton_iff] at hαDβ
  rw [← hαDβ]

theorem subset_alpha_union_of_Dalpha_eq_singleton (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hDα : Dalpha D hC.alpha = {β}) :
    ∀ x ∈ D, x ∈ hC.alpha ∨ x ∈ β := by
  have hN := hC.setup.normal
  have hodd := hC.setup.oddT
  have hα : IsBlock D hC.alpha := hC.isBlock_alpha
  have hDβ := Dalpha_eq_singleton_of_Dalpha_eq_singleton hN hα.subset hβ hDα
  intro x hx
  have hreach : Reach D hC.d x := reach_of_not_disconnected hC.conn hC.hd hx
  refine WreathEndgame.reach_invariant (P := fun y => y ∈ hC.alpha ∨ y ∈ β) ?_ hreach
    (Or.inl hC.d_mem_alpha)
  intro b c hb hc hbc hP
  obtain ⟨γ, hγ, hcγ⟩ := exists_mem_blockClass_of_mem hC.setup.isClass hα hc
  by_cases hγα : γ = hC.alpha
  · exact Or.inl (hγα ▸ hcγ)
  by_cases hγβ : γ = β
  · exact Or.inr (hγβ ▸ hcγ)
  exfalso
  rcases hP with hbα | hbβ
  · have h := mem_Dalpha_of_commute_mem hN hodd hα (mem_blockClass_self _) hγ
      (Ne.symm hγα) hbα hcγ hbc
    rw [hDα, Set.mem_singleton_iff] at h
    exact hγβ h
  · have h := mem_Dalpha_of_commute_mem hN hodd hα hβ.1 hγ (Ne.symm hγβ) hbβ hcγ hbc
    rw [hDβ, Set.mem_singleton_iff] at h
    exact hγα h

theorem alpha_subset_Halpha (hC : HypothesisC D) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hsing : ∀ γ ∈ Dalpha D hC.alpha, γ = β) : hC.alpha ⊆ (Halpha D hC.alpha : Set G) := by
  have hα : IsBlock D hC.alpha := hC.isBlock_alpha
  have hDα : Dalpha D hC.alpha = {β} := Set.eq_singleton_iff_unique_mem.2 ⟨hβ, hsing⟩
  have hDsub := subset_alpha_union_of_Dalpha_eq_singleton hC hβ hDα
  have hβH : β ⊆ (Halpha D hC.alpha : Set G) := fun x hx =>
    Subgroup.subset_closure ⟨β, hβ, hx⟩
  have hnorm : ∀ x ∈ D, x ∈ Subgroup.normalizer (Halpha D hC.alpha : Set G) := by
    intro x hx
    rcases hDsub x hx with hxα | hxβ
    · have hle : Halpha D hC.alpha ≤ Subgroup.centralizer {x} := by
        rw [Halpha, Subgroup.closure_le]
        intro z hz
        obtain ⟨γ, hγ, hzγ⟩ := hz
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hγ.2.2.2 x hxα z hzγ).eq.symm
      have hcent : x ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
      exact Subgroup.centralizer_le_normalizer (Halpha D hC.alpha : Set G) hcent
    · exact Subgroup.le_normalizer (hβH hxβ)
  have hnormal : (Halpha D hC.alpha).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hC.setup.gen, Subgroup.closure_le]
    exact hnorm
  obtain ⟨x, hx⟩ := nonempty_of_mem_blockClass hα.nonempty hβ.1
  rcases hC.setup.subset_or_disjoint (Halpha D hC.alpha) with hsub | hdisj
  · exact fun a ha => hsub (hα.subset ha)
  · exact absurd (hβH hx) (hdisj x (hβ.2.1 hx))

end CFSG.OddTranspositions.PartThree

end

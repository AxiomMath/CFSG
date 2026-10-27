module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSignedTop
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpMemberL

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem eq_signedA_of_ggDDot_eq_zero {k : ℕ} {ε : Fin k → ℤ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) {γ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (h0 : ggDDot ε γ = 0) :
    ∃ a b : Fin k, a ≠ b ∧ γ = Pi.single a (ε a) - Pi.single b (ε b) := by
  obtain ⟨a, b, s, u, hab, hs, hu, rfl⟩ := hγ
  rw [ggDDot_comm, ggDDot_single_add_single] at h0
  have hb := hε b
  have key : (s = ε a ∧ u = -ε b) ∨ (s = -ε a ∧ u = ε b) := by
    rcases hs with rfl | rfl <;> rcases hu with rfl | rfl <;> omega
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, b, hab, by rw [Pi.single_neg, sub_eq_add_neg]⟩
  · exact ⟨b, a, hab.symm, by rw [Pi.single_neg, sub_eq_add_neg, add_comm]⟩

theorem ggDk_automizerJoin_le_of_signed {G : Type} [Group G] {x : G}
    {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (hL : ggDMemberRoots e φ L =
      {η | ∃ a b : Fin k, a ≠ b ∧ η = Pi.single a (ε a) - Pi.single b (ε b)})
    (hfix : ∃ xb : ↥Bs, (xb : G) = x ∧ ∀ (u : M.Group) (η : Fin k → ℤ),
      GGDReflRoot k (φ u) η →
        ((((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb) ↔ ggDDot ε η = 0))
    {r : MulAut ↥Bs} (hr : r ∈ ggCoxRefl M e) (hmove : ∃ xb : ↥Bs, (xb : G) = x ∧ r xb ≠ xb) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs ⊔ Subgroup.closure {r} := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨xb, hxb, hfix⟩ := hfix
  obtain ⟨xb', hxb', hmv⟩ := hmove
  obtain rfl : xb' = xb := Subtype.ext (hxb'.trans hxb.symm)
  obtain ⟨w, i, hri⟩ := hr
  rw [hri] at hmv
  obtain ⟨η, hη⟩ := exists_ggDReflRoot_of_conj φ hφ w i
  let F : M.Group →* MulAut ↥Bs := (ggAutomizerJoin L Bs 𝒦).subtype.comp e.toMonoidHom
  let H : Subgroup (ggWeylD k) :=
    ((ggAutomizer L Bs ⊔ Subgroup.closure {r}).comap F).comap φ.symm.toMonoidHom
  have hH : ∀ u : M.Group, φ u ∈ H ↔ ((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
      ggAutomizer L Bs ⊔ Subgroup.closure {r} := fun u => by
    show F (φ.symm (φ u)) ∈ ggAutomizer L Bs ⊔ Subgroup.closure {r} ↔ _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have htop : H = ⊤ := by
    refine ggDk_eq_top_of_signedA hk hε (fun t γ ht h0 => ?_) hη
      (fun h0 => hmv ((hfix _ η hη).2 h0))
      ((hH _).2 (Subgroup.mem_sup_right (Subgroup.subset_closure
        (Set.mem_singleton_iff.2 hri.symm))))
    obtain ⟨t', ht', ht'L⟩ : γ ∈ ggDMemberRoots e φ L := by
      rw [hL]
      exact eq_signedA_of_ggDDot_eq_zero hε (ht.mem (by omega)) h0
    rw [ht.unique hk2 ht' (Or.inl rfl)]
    exact (hH t').2 (Subgroup.mem_sup_left ht'L)
  intro y hy
  have h1 := (hH (e.symm ⟨y, hy⟩)).1 (by rw [htop]; exact Subgroup.mem_top _)
  rwa [MulEquiv.apply_symm_apply] at h1

theorem ggDk_automizerJoin_le
    (hKG : GGSecFiveKGPosInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hss : GGDNoSameSupp e φ) {r : MulAut ↥Bs} (hr : r ∈ ggCoxRefl M e)
    (hmove : ∃ xb : ↥Bs, (xb : G) = x ∧ r xb ≠ xb) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs ⊔ Subgroup.closure {r} := by
  obtain ⟨-, ε, hε, hL, hfix⟩ := ggDk_memberRoots_L hKG hcfg hsplit hpres hle3 hk hM φ hφ hss
  exact ggDk_automizerJoin_le_of_signed hk φ hφ hε hL hfix hr hmove

end CFSG.StandardType

end

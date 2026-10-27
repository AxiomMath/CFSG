module

public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem closure_cenGen_eq_top_of_coatoms [Finite G] [IsSimpleGroup G] {p e : ℕ} [Fact p.Prime]
    (M₀ S E' : Subgroup G) (φ : ↥S ≃* (Fin 2 → Multiplicative (ZMod (p ^ e))))
    (hSp : IsPGroup p ↥S) (hSidx : ¬ p ∣ S.index)
    (hE'S : E' ≤ S) (hE'p : ∀ x ∈ E', x ^ p = 1) (hE'c : Nat.card E' = p ^ 2)
    (hcoatom : ∀ N : Subgroup G, IsCoatom N → M₀ ≤ N → ¬ N.index ≡ 1 [MOD p])
    (hgen : M₀ ≤ closure (cenGen E'))
    (F : Subgroup G) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    closure (cenGen F) = ⊤ := by
  have hp : p.Prime := Fact.out
  have hE'ne : E' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE'c
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hE'le : E' ≤ closure (cenGen E') := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · exact subset_closure ⟨x, hx, hx1, rfl⟩
  have hbot : closure (cenGen E') ≠ ⊥ := fun h => hE'ne (eq_bot_iff.2 (h ▸ hE'le))
  have hmain : closure (cenGen E') = ⊤ := by
    by_contra hne
    have hNtop : normalizer (closure (cenGen E') : Set G) ≠ ⊤ := by
      intro h6
      have hnormal : (closure (cenGen E')).Normal := normalizer_eq_top_iff.1 h6
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (closure (cenGen E')) with h7 | h7
      · exact hbot h7
      · exact hne h7
    obtain ⟨M, hM, hleM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hNtop
    have hind : ¬ M.index ≡ 1 [MOD p] :=
      hcoatom M hM (hgen.trans (le_normalizer.trans hleM))
    have hNS : ∀ n ∈ normalizer (S : Set G), n ∈ M := by
      intro n hn
      have hnS : cj S n = S := mem_normalizer_iff_cj.1 hn
      have h1 : cj E' n ≤ S := by
        intro x hx
        have : x ∈ cj S n := cj_le_cj hE'S n hx
        rwa [hnS] at this
      have h2 : cj E' n = E' :=
        plane_unique hp φ h1 hE'S (fun x hx => pow_eq_one_of_mem_cj hE'p hx) hE'p
          (by rw [card_cj]; exact hE'c) hE'c
      have h3 : closure (cenGen (cj E' n)) = closure (cenGen E') := by rw [h2]
      rw [closure_cenGen_cj] at h3
      have h4 : cj (closure (cenGen E')) n = closure (cenGen E') := h3
      exact hleM (mem_normalizer_iff_cj.2 h4)
    have hSM : S ≤ M := fun s hs => hNS s (le_normalizer hs)
    have hmod : Nat.card (G ⧸ M) ≡ Nat.card (MulAction.fixedPoints S (G ⧸ M)) [MOD p] :=
      hSp.card_modEq_card_fixedPoints (G ⧸ M)
    have hfixed_iff : ∀ g : G, ((g : G ⧸ M) ∈ MulAction.fixedPoints S (G ⧸ M)) ↔
        ∀ s ∈ S, g⁻¹ * s * g ∈ M := by
      intro g
      rw [MulAction.mem_fixedPoints]
      have key : ∀ s : ↥S, s • (g : G ⧸ M) = (g : G ⧸ M) ↔ g⁻¹ * (s : G)⁻¹ * g ∈ M := by
        intro s
        rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
        have e : ((s : G) * g)⁻¹ * g = g⁻¹ * (s : G)⁻¹ * g := by group
        rw [e]
      simp only [key]
      constructor
      · intro h s hs
        have h1 := h ⟨s⁻¹, S.inv_mem hs⟩
        have e2 : g⁻¹ * (((⟨s⁻¹, S.inv_mem hs⟩ : ↥S) : G))⁻¹ * g = g⁻¹ * s * g := by
          simp
        rwa [e2] at h1
      · intro h s
        exact h _ (S.inv_mem s.2)
    have hfix : MulAction.fixedPoints S (G ⧸ M) = {((1 : G) : G ⧸ M)} := by
      ext x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rw [Set.mem_singleton_iff, hfixed_iff, QuotientGroup.eq]
      constructor
      · intro hg
        obtain ⟨m, hmM, hmn⟩ := exists_mem_normalizer_of_conj_le hSM hSp hSidx hg
        have hgm : g * m ∈ M := hNS _ hmn
        have h6 := M.mul_mem hgm (M.inv_mem hmM)
        have h7 : g⁻¹ * 1 = (g * m * (m : G)⁻¹)⁻¹ := by group
        rw [h7]
        exact M.inv_mem (by simpa using h6)
      · intro hg s hs
        have hgM : g ∈ M := by simpa using M.inv_mem hg
        exact M.mul_mem (M.mul_mem (M.inv_mem hgM) (hSM hs)) hgM
    have hcard : Nat.card (MulAction.fixedPoints S (G ⧸ M)) = 1 := by
      rw [hfix]
      exact Nat.card_unique
    rw [hcard] at hmod
    exact hind hmod
  have hFpg : IsPGroup p ↥F := IsPGroup.of_card hFc
  obtain ⟨Q, hQ⟩ := hFpg.exists_le_sylow
  let S₀ : Sylow p G := hSp.toSylow hSidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S₀ Q
  have hQS : (Q : Subgroup G) = cj S c := by
    have h1 : ((c • S₀ : Sylow p G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
    have hS₀ : ((S₀ : Sylow p G) : Subgroup G) = S := rfl
    rw [← h1, Sylow.coe_subgroup_smul, hS₀]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_cj]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
  have hFS : cj F c⁻¹ ≤ S := by
    intro x hx
    have h1 : x ∈ cj (cj S c) c⁻¹ := cj_le_cj (hQ.trans hQS.le) c⁻¹ hx
    rwa [cj_cj] at h1
  have hF' : cj F c⁻¹ = E' :=
    plane_unique hp φ hFS hE'S (fun x hx => pow_eq_one_of_mem_cj hFp hx) hE'p
      (by rw [card_cj]; exact hFc) hE'c
  have hF'' : F = cj E' c := by
    rw [← hF', cj_inv_cj]
  rw [hF'', closure_cenGen_cj, hmain]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective

end CFSG.RankThree.PartOne.SEITZ3

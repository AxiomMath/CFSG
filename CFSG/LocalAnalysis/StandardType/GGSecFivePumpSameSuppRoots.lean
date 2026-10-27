module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpMemberL
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSignedTop
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupMemberRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJoin
import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRoots

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem sameSupp_of_signed {k : ℕ} {t t' : ggWeylD k} {a b : Fin k} (hab : a ≠ b)
    {s u : ℤ} (hs : s = 1 ∨ s = -1) (hu : u = 1 ∨ u = -1)
    (h : GGDReflRoot k t (Pi.single a s - Pi.single b u))
    (h' : GGDReflRoot k t' (Pi.single a s + Pi.single b u)) : GGDSameSupp k t t' := by
  rcases hs with rfl | rfl
  · refine ⟨a, b, -u, hab, by rcases hu with rfl | rfl <;> norm_num, h.of_pm (Or.inl ?_),
      h'.of_pm (Or.inl ?_)⟩ <;> funext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply] <;> split_ifs <;> ring
  · refine ⟨a, b, u, hab, hu, h.of_pm (Or.inr ?_), h'.of_pm (Or.inr ?_)⟩ <;> funext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.single_apply] <;> split_ifs <;> ring

private theorem ggDReflRoot_inv {k : ℕ} {t : ggWeylD k} {γ : Fin k → ℤ}
    (h : GGDReflRoot k t γ) : t⁻¹ = t := by
  obtain ⟨w, i, rfl, -⟩ := h
  have hs : ((coxeterMatrix (isFiniteType_cartanD k)).simple i)⁻¹ =
      (coxeterMatrix (isFiniteType_cartanD k)).simple i :=
    (coxeterMatrix (isFiniteType_cartanD k)).toCoxeterSystem.inv_simple i
  rw [mul_inv_rev, mul_inv_rev, inv_inv, hs, mul_assoc]

theorem ggDk_pumpup_roots
    (hKG : GGSecFiveKGPosInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hss : GGDNoSameSupp e φ) {a₀ : Fin k} {d₀ : ↥Bs} (hpt : GGDPumpPt e φ a₀ d₀)
    (hpJ : p ∣ Nat.card J)
    (hJ : ∀ η : Fin k → ℤ, η ∈ ggDMemberRoots e φ J ↔ η ∈ ggDMemberRoots e φ L ∧ η a₀ = 0) :
    ∃ K₁ ∈ 𝒦, ∃ t₁ tδ tρ tσ : M.Group,
      ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer K₁ Bs ∧
      GGIsReflection p ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∧
      ((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs ∧
      ((e tρ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer J Bs ∧
      ((e tσ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer J Bs ∧
      GGDSameSupp k (φ tσ) (φ (tδ * t₁ * tδ⁻¹)) ∧
      (∃ xb : ↥Bs, (xb : G) = x ∧
        ((e (tδ * t₁ * tδ⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb ≠ xb) ∧
      ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) d₀ ≠ d₀ ∧
      ((e (tδ * t₁ * tδ⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) d₀ = d₀ ∧
      ((e (tδ * t₁ * tδ⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
          (((e tρ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
            (((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) d₀)) =
        ((e tρ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
          (((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) d₀) := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨-, ε, hε, hΦL, xb, hxb, hfix⟩ :=
    ggDk_memberRoots_L hKG hcfg hsplit hpres hle3 hk hM φ hφ hss
  obtain ⟨-, -, hspan⟩ := ggDk_memberRoots_subsys hKG hcfg hsplit hpres hle3 hk φ hφ
  have hsq : ∀ a, ε a * ε a = 1 := fun a => by rcases hε a with h | h <;> rw [h] <;> norm_num
  have hL : ∀ a b : Fin k, a ≠ b →
      Pi.single a (ε a) - Pi.single b (ε b) ∈ ggDMemberRoots e φ L :=
    fun a b hab => (Set.ext_iff.1 hΦL _).2 ⟨a, b, hab, rfl⟩
  have hLJ : ∀ a b : Fin k, a ≠ b → a ≠ a₀ → b ≠ a₀ →
      Pi.single a (ε a) - Pi.single b (ε b) ∈ ggDMemberRoots e φ J := fun a b hab ha hb =>
    (hJ _).2 ⟨hL a b hab, by simp [ha.symm, hb.symm]⟩
  obtain ⟨K₁, hK₁, η₁, ⟨t₁, ht₁, ht₁K⟩, h0⟩ :
      ∃ K₁ ∈ 𝒦, ∃ η ∈ ggDMemberRoots e φ K₁, ggDDot ε η ≠ 0 := by
    by_contra hno
    push Not at hno
    have hv := hspan ε fun X hX η hη => by
      rcases hX with hX | hX
      · rw [hX, hΦL] at hη
        obtain ⟨a, b, -, rfl⟩ := hη
        rw [ggDDot_comm, sub_eq_add_neg, ← Pi.single_neg, ggDDot_single_add_single, neg_mul,
          hsq, hsq, add_neg_cancel]
      · exact hno X hX η hη
    have h := congrFun hv ⟨0, by omega⟩
    rw [Pi.zero_apply] at h
    rcases hε ⟨0, by omega⟩ with h' | h' <;> omega
  obtain ⟨a, b, hab, hη₁⟩ := eq_pm_of_ggDDot_ne_zero hε (ht₁.mem (by omega)) h0
  have hP := ht₁.of_pm hη₁
  have ha₀ : a₀ = a ∨ a₀ = b := by
    by_contra hne
    push Not at hne
    obtain ⟨t, ht, htJ⟩ := hLJ a b hab (Ne.symm hne.1) (Ne.symm hne.2)
    have htK := ggTBJ_automizer_le hLB hcfg hpJ (Or.inr hK₁) htJ
    obtain ⟨a', b', s, hab', hs, h1, h2⟩ := sameSupp_of_signed hab (hε a) (hε b) ht hP
    refine hss K₁ (Or.inr hK₁) a' b' hab' ?_
    rcases hs with rfl | rfl
    · exact ⟨⟨t, h1, htK⟩, t₁, h2, ht₁K⟩
    · exact ⟨⟨t₁, by rwa [Pi.single_neg, sub_neg_eq_add] at h2, ht₁K⟩, t,
        by rwa [Pi.single_neg, ← sub_eq_add_neg] at h1, htK⟩
  obtain ⟨b, hb, hroot₁⟩ : ∃ b, b ≠ a₀ ∧
      GGDReflRoot k (φ t₁) (Pi.single a₀ (ε a₀) + Pi.single b (ε b)) := by
    rcases ha₀ with h | h
    · rw [← h] at hab hP
      exact ⟨b, Ne.symm hab, hP⟩
    · rw [← h] at hab hP
      exact ⟨a, hab, by rwa [add_comm] at hP⟩
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a₀, b}) (t := .univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_two.trans_lt (by omega))
  obtain ⟨b', -, hb'⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a₀, b, c}) (t := .univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hb'
  obtain ⟨⟨hca, hcb⟩, hb'a, hb'b, hb'c⟩ := And.intro hc hb'
  obtain ⟨tδ, hδ, htδ⟩ := hL a₀ c (Ne.symm hca)
  obtain ⟨tσ, hσ, htσ⟩ := hLJ c b hcb hca hb
  obtain ⟨tρ, hρ, htρ⟩ := hLJ c b' (Ne.symm hb'c) hca hb'a
  have hroot' : GGDReflRoot k (φ (tδ * t₁ * tδ⁻¹)) (Pi.single c (ε c) + Pi.single b (ε b)) := by
    have h1 : ggDDot (Pi.single a₀ (ε a₀) + Pi.single b (ε b))
        (Pi.single a₀ (ε a₀) - Pi.single c (ε c)) = 1 := by
      rw [ggDDot_single_add_single]
      simp [Ne.symm hca, hb, Ne.symm hcb, hsq]
    rw [map_mul, map_mul, map_inv]
    convert hroot₁.conj (hδ.action hk2) using 1
    rw [ggDReflect, h1, one_smul]
    abel
  have hroot'' : GGDReflRoot k (φ ((tρ * tδ)⁻¹ * (tδ * t₁ * tδ⁻¹) * (tρ * tδ)))
      (Pi.single b (ε b) + Pi.single b' (ε b')) := by
    have h1 : ggDDot (Pi.single c (ε c) + Pi.single b (ε b))
        (Pi.single c (ε c) - Pi.single b' (ε b')) = 1 := by
      rw [ggDDot_single_add_single]
      simp [Ne.symm hb'c, Ne.symm hcb, Ne.symm hb'b, hsq]
    have h2 : ggDDot (Pi.single b (ε b) + Pi.single b' (ε b'))
        (Pi.single a₀ (ε a₀) - Pi.single c (ε c)) = 0 := by
      rw [ggDDot_single_add_single]
      simp [hb, Ne.symm hcb, hb'a, hb'c]
    have e1 : ggDReflect (Pi.single c (ε c) - Pi.single b' (ε b'))
        (Pi.single c (ε c) + Pi.single b (ε b)) = Pi.single b (ε b) + Pi.single b' (ε b') := by
      rw [ggDReflect, h1, one_smul]
      abel
    have e2 : ggDReflect (Pi.single a₀ (ε a₀) - Pi.single c (ε c))
        (Pi.single b (ε b) + Pi.single b' (ε b')) = Pi.single b (ε b) + Pi.single b' (ε b') := by
      rw [ggDReflect, h2, zero_smul, sub_zero]
    have h := hroot'.conj (g := φ tδ * φ tρ)
      (f := fun u => ggDReflect (Pi.single a₀ (ε a₀) - Pi.single c (ε c))
        (ggDReflect (Pi.single c (ε c) - Pi.single b' (ε b')) u)) fun v => by
      rw [weylAction_mul_apply, hδ.action hk2, hρ.action hk2]
    rw [e1, e2] at h
    convert h using 1
    simp only [map_mul, map_inv, mul_inv_rev, ggDReflRoot_inv hδ, ggDReflRoot_inv hρ, mul_assoc]
  have hrefl : GGIsReflection p ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    refine ggCoxRefl_isReflection (fun i => hpres.2 i) ?_
    obtain ⟨w, j, hw, -⟩ := id hroot₁
    refine ⟨φ.symm w, σ j, ?_⟩
    rw [show t₁ = φ.symm w * M.simple (σ j) * (φ.symm w)⁻¹ from φ.injective (by
      rw [hw, map_mul, map_mul, map_inv, hφ, MulEquiv.apply_symm_apply])]
  refine ⟨K₁, hK₁, t₁, tδ, tρ, tσ, ht₁K, hrefl, htδ, htρ, htσ,
    sameSupp_of_signed hcb (hε c) (hε b) hσ hroot', ⟨xb, hxb, fun h => ?_⟩, fun h => ?_,
    (hpt.2 _ _ hroot').2 (ggDPair_apply_of_ne (Ne.symm hca) (Ne.symm hb) _ _), ?_⟩
  · have h2 := (hfix _ _ hroot').1 h
    rw [ggDDot_comm, ggDDot_single_add_single, hsq, hsq] at h2
    norm_num at h2
  · have h2 := (hpt.2 _ _ hroot₁).1 h
    rw [ggDPair_apply_left (Ne.symm hb)] at h2
    rcases hε a₀ with h3 | h3 <;> omega
  ·
    have h := (hpt.2 _ _ hroot'').2 (ggDPair_apply_of_ne (Ne.symm hb) (Ne.symm hb'a) _ _)
    rwa [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_def, MulEquiv.symm_apply_eq, map_mul e tρ tδ,
      Subgroup.coe_mul, MulAut.mul_apply] at h

end CFSG.StandardType

end

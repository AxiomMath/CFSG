module

public import CFSG.RankThree.GF2n.Smith81.S81E5Uni
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


private def pattern (a : Fin e7Data.d) : List Bool :=
  (List.finRange 126).map fun k : Fin 126 =>
    decide (pr a ((Tag.rootCertificate .E7).root (k : ℕ)) = -1)

private theorem pattern_nodup : ((List.finRange e7Data.d).map pattern).Nodup := by
  unfold pattern pr
  decide +kernel

theorem weights_separated_aux : ∀ a a' : Fin e7Data.d, a ≠ a' →
    ∃ k : Fin 126, ¬ (pr a ((Tag.rootCertificate .E7).root k) = -1 ↔
        pr a' ((Tag.rootCertificate .E7).root k) = -1) := by
  intro a a' hne
  by_contra hcon
  push Not at hcon
  have h : pattern a = pattern a' := by
    unfold pattern
    apply List.map_congr_left
    intro k _
    simp [hcon k]
  exact hne (List.inj_on_of_nodup_map pattern_nodup (List.mem_finRange a)
    (List.mem_finRange a') h)

theorem weights_separated {a a' : Fin e7Data.d} (hne : a ≠ a') :
    ∃ β : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 β ∧ ¬ (pr a β = -1 ↔ pr a' β = -1) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk⟩ := weights_separated_aux a a' hne
  exact ⟨(Tag.rootCertificate .E7).root k,
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega), hk⟩

theorem exists_root_neg_aux : ∀ a : Fin e7Data.d,
    ∃ k : Fin 126, pr a ((Tag.rootCertificate .E7).root k) = -1 := by
  unfold pr
  decide +kernel

theorem exists_root_neg (a : Fin e7Data.d) :
    ∃ β : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 β ∧ pr a β = -1 := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk⟩ := exists_root_neg_aux a
  exact ⟨(Tag.rootCertificate .E7).root k,
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega), hk⟩

section Irred

variable {K : Type} [Field K] [CharP K 2] (S : AddSubgroup (V K))

theorem scalar_closure_all (hE : ∀ g ∈ EGrp K, ∀ s ∈ S, (g : Module.End K (V K)) s ∈ S)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (c : K) {s : V K} (hs : s ∈ S) :
    c • e7Data.rootOp K β s ∈ S := by
  have h1 : (e7Data_valid.xu K β c : Module.End K (V K)) s ∈ S :=
    hE _ (e7Data_valid.xu_mem K β c) s hs
  have h2 : (e7Data_valid.xu K β c : Module.End K (V K)) s = s + c • e7Data.rootOp K β s := by
    rw [e7Data_valid.xu_apply]
  have h3 : c • e7Data.rootOp K β s = (e7Data_valid.xu K β c : Module.End K (V K)) s - s := by
    rw [h2]
    abel
  rw [h3]
  exact S.sub_mem h1 hs

set_option linter.constructorNameAsVariable false in
theorem exists_single_of_ne_bot_all
    (hE : ∀ g ∈ EGrp K, ∀ s ∈ S, (g : Module.End K (V K)) s ∈ S) (hne : S ≠ ⊥) :
    ∃ a : Fin e7Data.d, ∃ c : K, c ≠ 0 ∧ c • Finsupp.single a (1 : K) ∈ S := by
  classical
  obtain ⟨s₀, hs₀, hs₀0⟩ : ∃ t : V K, t ∈ S ∧ t ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    rw [AddSubgroup.mem_bot]
    exact h x hx
  have hex : ∃ n : ℕ, ∃ t : V K, t ∈ S ∧ t ≠ 0 ∧ t.support.card = n :=
    ⟨s₀.support.card, s₀, hs₀, hs₀0, rfl⟩
  obtain ⟨s, hs, hs0, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ t ∈ S, t ≠ 0 → s.support.card ≤ t.support.card := by
    intro t ht ht0
    rw [hcard]
    exact Nat.find_min' hex ⟨t, ht, ht0, rfl⟩
  have key : ∀ x y : Fin e7Data.d, x ∈ s.support → y ∈ s.support →
      ∀ β : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 β → pr x β = -1 → pr y β ≠ -1 → False := by
    intro x y hx hy β hβ hx1 hy1
    have hs' : e7Data.rootOp K β s ∈ S := by
      have h := scalar_closure_all S hE hβ 1 hs
      rwa [one_smul] at h
    have hval : (e7Data.rootOp K β s) (shift β x) = s x := by
      rw [rootOp_apply (K := K) hβ s (shift β x), if_pos (pr_shift_self hβ hx1),
        shift_neg_shift hβ hx1]
    have hs'0 : e7Data.rootOp K β s ≠ 0 := by
      intro h0
      apply Finsupp.mem_support_iff.mp hx
      rw [← hval, h0, Finsupp.zero_apply]
    have hsub : (e7Data.rootOp K β s).support ⊆ (s.support.erase y).image (shift β) := by
      intro b hb
      rw [Finsupp.mem_support_iff, rootOp_apply (K := K) hβ s b] at hb
      by_cases hb1 : pr b β = 1
      · rw [if_pos hb1] at hb
        rw [Finset.mem_image]
        refine ⟨shift (-β) b, ?_, shift_shift_neg hβ hb1⟩
        rw [Finset.mem_erase, Finsupp.mem_support_iff]
        refine ⟨?_, hb⟩
        intro h
        have hpa : pr (shift (-β) b) β = -1 := pr_shift_neg hβ hb1
        rw [h] at hpa
        exact hy1 hpa
      · rw [if_neg hb1] at hb
        exact absurd rfl hb
    have hcard1 : (e7Data.rootOp K β s).support.card ≤ (s.support.erase y).card :=
      (Finset.card_le_card hsub).trans Finset.card_image_le
    have hcard2 : (s.support.erase y).card < s.support.card :=
      Finset.card_erase_lt_of_mem hy
    have hmin' := hmin _ hs' hs'0
    omega
  have hone : s.support.card = 1 := by
    by_contra hne1
    have hpos : 0 < s.support.card := by
      obtain ⟨x, hx⟩ : ∃ x, s x ≠ 0 := by
        by_contra h
        push Not at h
        exact hs0 (Finsupp.ext fun x => by simpa using h x)
      exact Finset.card_pos.mpr ⟨x, Finsupp.mem_support_iff.mpr hx⟩
    have hgt : 1 < s.support.card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hgt
    obtain ⟨β, hβ, hiff⟩ := weights_separated hxy
    by_cases h1 : pr x β = -1
    · exact key x y hx hy β hβ h1 (fun h2 => hiff ⟨fun _ => h2, fun _ => h1⟩)
    · have h2 : pr y β = -1 := by
        by_contra h2
        exact hiff ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      exact key y x hy hx β hβ h2 h1
  obtain ⟨a, hsupp⟩ := Finset.card_eq_one.mp hone
  have ha : a ∈ s.support := by
    rw [hsupp]
    exact Finset.mem_singleton_self a
  have hsa : s a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hseq : s = s a • Finsupp.single a (1 : K) := by
    ext b
    by_cases hb : b = a
    · subst hb
      simp
    · have hb0 : s b = 0 := by
        by_contra hne2
        have hbm : b ∈ s.support := Finsupp.mem_support_iff.mpr hne2
        rw [hsupp, Finset.mem_singleton] at hbm
        exact hb hbm
      rw [hb0, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hb), smul_zero]
  refine ⟨a, s a, hsa, ?_⟩
  rw [← hseq]
  exact hs

theorem EGrp_irreducible_V (hE : ∀ g ∈ EGrp K, ∀ s ∈ S, (g : Module.End K (V K)) s ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨a, c, hc0, hca⟩ := exists_single_of_ne_bot_all S hE hbot
  have hmult : ∀ b : Fin e7Data.d, c • Finsupp.single b (1 : K) ∈ S := by
    intro b
    obtain ⟨ga, hga, hgaw⟩ := weight_vec_mem_orbit (K := K) a
    obtain ⟨gb, hgb, hgbw⟩ := weight_vec_mem_orbit (K := K) b
    have hinv : ((ga⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
        (Finsupp.single a (1 : K)) = (w0 : V K) := by
      rw [← hgaw, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    have h2 := hE _ (inv_mem hga) _ hca
    rw [map_smul, hinv] at h2
    have h3 := hE _ hgb _ h2
    rwa [map_smul, hgbw] at h3
  have hfull : ∀ b : Fin e7Data.d, ∀ c'' : K, c'' • Finsupp.single b (1 : K) ∈ S := by
    intro b c''
    obtain ⟨β, hβ, hpa⟩ := exists_root_neg b
    have hb' : pr (shift β b) (-β) = -1 := by rw [pr_neg, pr_shift_self hβ hpa]
    have h1 := scalar_closure_all S hE (isRoot_neg hβ) (c'' / c) (hmult (shift β b))
    have h2 : e7Data.rootOp K (-β) (c • Finsupp.single (shift β b) (1 : K)) =
        c • Finsupp.single b (1 : K) := by
      rw [map_smul, rootOp_single (K := K) (isRoot_neg hβ) (shift β b), if_pos hb',
        shift_neg_shift hβ hpa]
    have hcc : c'' / c * c = c'' := by field_simp
    rw [h2, smul_smul, hcc] at h1
    exact h1
  rw [eq_top_iff]
  intro v _
  have hsum : v = ∑ d ∈ v.support, v d • Finsupp.single d (1 : K) := by
    have h := Finsupp.sum_single v
    rw [Finsupp.sum] at h
    conv_lhs => rw [← h]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finsupp.smul_single_one]
  have hmem : ∑ d ∈ v.support, v d • Finsupp.single d (1 : K) ∈ S := by
    apply AddSubgroup.sum_mem
    intro d _
    exact hfull d (v d)
  rw [← hsum] at hmem
  exact hmem

end Irred

variable {K : Type} [Field K] [CharP K 2]

theorem EAut_irreducible_V (S : AddSubgroup (V K)) (hS : ∀ g ∈ EAut K, ∀ s ∈ S, g s ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  refine EGrp_irreducible_V S fun g hg s hs => ?_
  exact hS (vAut K g) (Subgroup.mem_map_of_mem _ hg) s hs

end CFSG.RankThree.GF2n.Smith81.E7Model

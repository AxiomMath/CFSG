module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BNGenerationOpp
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BNConj
public import CFSG.Open.SplitBNPair
public import CFSG.Blueprint.Catalog
import TauCeti.Algebra.Group.Subgroup.Map
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigFix
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BN
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Milestones.ASVolI.I2
import CFSG.Milestones.ASVolI.I2BNWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem CFSG.ASVolI.ChIJK

theorem k_19_21_opp_of_splitBN {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    {B N : Subgroup S} (hBN : IsSplitBNPair 2 B N) : K_19_21_opp S := by
  intro U hU r hr hr2 Eh hEh hEhU
  classical
  have map_normalizer_inf : ∀ (U V : Subgroup S) (f : S ≃* S),
      (normalizer (U : Set S) ⊓ normalizer (V : Set S)).map f.toMonoidHom =
        normalizer ((U.map f.toMonoidHom : Subgroup S) : Set S) ⊓
          normalizer ((V.map f.toMonoidHom : Subgroup S) : Set S) := fun U V f => by
    rw [Subgroup.map_inf_eq _ _ _ f.injective, Subgroup.map_equiv_normalizer_eq,
      Subgroup.map_equiv_normalizer_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨B', N', hBN', hUB', hNU, hBUH⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22k108bn_exists_conj_split hBN U.isPGroup'
      U.not_dvd_index
  have : (cartan B' N').Normal := hBN'.normal_inter
  obtain ⟨W, hW⟩ := burnsideI2BN_exists_isBNPair (burnsideI2BN_toPre hBN')
  obtain ⟨n₀, -, hmax⟩ := CFSG.ASVolI.burnsideI25b_exists_max (B := B') (N := N') W W
  have hmax' : ∀ w, wordLength W w ≤ wordLength W (n₀ : WeylGroup B' N') := fun w =>
    hmax w (hW.mem_closure w)
  have hw₀ : (n₀ : WeylGroup B' N') * (n₀ : WeylGroup B' N') = 1 := by
    have h1 := CFSG.ASVolI.burnsideI25c_prefix_longest hW (subset_refl W) (hW.mem_closure _)
      (fun w _ => hmax' w) (x := (n₀ : WeylGroup B' N')⁻¹) (hW.mem_closure _)
    rw [hW.length_inv, inv_inv] at h1
    have h0 : wordLength W ((n₀ : WeylGroup B' N') * n₀) = 0 := by omega
    exact (wordLength_eq_zero_iff hW.bnCore.mul_self_eq_one (hW.mem_closure _)).1 h0
  let φ : ↥Eh →* MulAut S := Eh.subtype
  have hφU : ∀ a : ↥Eh, (U : Subgroup S).map (φ a).toMonoidHom = U := fun a => hEhU a a.2
  have hφB : ∀ (a : ↥Eh) (y : S), φ a y ∈ B' ↔ y ∈ B' := fun a y => by
    rw [← hNU]
    exact CFSG.LieType.Ree.apply_mem_iff_of_map_eq
      (by rw [Subgroup.map_equiv_normalizer_eq, hφU a]) y
  obtain ⟨g, hg, hfix⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.F10.k108big_exists_conj_fixed
    hW (Ne.symm hr2) U.isPGroup' hUB' hNU.ge hBUH hmax' hEh φ hφB hφU
  have htop := CFSG.LocalAnalysis.UniquenessCase.UC22.F10.k108big_sup_conj_eq_top hW hU hNU.ge
    hBUH hmax' hg
  obtain ⟨n₁, hn₁, b₁, hb₁, b₂, hb₂, rfl⟩ := mem_dc_iff.1 hg
  set V : Subgroup S := (U : Subgroup S).map (MulAut.conj (b₁ * n₁ * b₂)).toMonoidHom with hV
  have hfixB : ∀ b ∈ B', (U : Subgroup S).map (MulAut.conj b).toMonoidHom = U := fun b hb =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hNU.ge hb)
  have hn₁sq : (n₁ : S) * n₁ ∈ B' := by
    have h1 : ((n₁ * n₁ : N') : WeylGroup B' N') = 1 := by
      rw [QuotientGroup.mk_mul, hn₁, hw₀]
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    exact (Subgroup.mem_subgroupOf.1 h2).1
  set n : S := b₁ * n₁ * b₁⁻¹ with hn
  have hVn : V = (U : Subgroup S).map (MulAut.conj (b₁ * n₁)).toMonoidHom := by
    rw [hV, ← Subgroup.map_conj_map_conj (U : Subgroup S) b₂ (b₁ * n₁),
      hfixB b₂ hb₂]
  have hnU : (U : Subgroup S).map (MulAut.conj n).toMonoidHom = V := by
    rw [hVn, hn, ← Subgroup.map_conj_map_conj (U : Subgroup S) b₁⁻¹ (b₁ * n₁),
      hfixB _ (B'.inv_mem hb₁)]
  have hnV : V.map (MulAut.conj n).toMonoidHom = U := by
    rw [hVn, Subgroup.map_conj_map_conj]
    have e1 : n * (b₁ * n₁) = b₁ * ((n₁ : S) * n₁) := by
      rw [hn]
      group
    rw [e1, ← Subgroup.map_conj_map_conj (U : Subgroup S) ((n₁ : S) * n₁) b₁,
      hfixB _ hn₁sq, hfixB _ hb₁]
  have hVfix : ∀ α ∈ Eh, V.map (MulEquiv.toMonoidHom α) = V := fun α hα => hfix ⟨α, hα⟩
  refine ⟨normalizer ((U : Subgroup S) : Set S) ⊓ normalizer (V : Set S), n, inf_le_left, ?_, ?_,
    ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, map_normalizer_inf,
      hnU, hnV, inf_comm]
  · intro α hα
    rw [map_normalizer_inf, hEhU α hα, hVfix α hα]
  · intro α hα
    have hαU : (U : Subgroup S).map (MulAut.conj (α n)).toMonoidHom = V := by
      rw [← hEhU α hα]
      show ((U : Subgroup S).map (MulEquiv.toMonoidHom α)).map
        (MulAut.conj ((MulEquiv.toMonoidHom α) n)).toMonoidHom = V
      rw [← Subgroup.map_map_conj (U : Subgroup S) (MulEquiv.toMonoidHom α) n,
        hnU, hVfix α hα]
    have hαV : V.map (MulAut.conj (α n)).toMonoidHom = U := by
      rw [← hVfix α hα]
      show ((V : Subgroup S).map (MulEquiv.toMonoidHom α)).map
        (MulAut.conj ((MulEquiv.toMonoidHom α) n)).toMonoidHom = U
      rw [← Subgroup.map_map_conj V (MulEquiv.toMonoidHom α) n, hnV, hEhU α hα]
    have hinvU : V.map (MulAut.conj n⁻¹).toMonoidHom = U := by
      rw [← hnU, Subgroup.map_conj_map_conj (U : Subgroup S) n n⁻¹, inv_mul_cancel]
      ext x
      simp
    have hinvV : (U : Subgroup S).map (MulAut.conj n⁻¹).toMonoidHom = V := by
      rw [← hnV, Subgroup.map_conj_map_conj V n n⁻¹, inv_mul_cancel]
      ext x
      simp
    refine ⟨Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_,
      Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_⟩
    · rw [← MulEquiv.toMonoidHom_eq_coe, ← Subgroup.map_conj_map_conj, hαU, hinvU]
    · rw [← MulEquiv.toMonoidHom_eq_coe, ← Subgroup.map_conj_map_conj, hαV, hinvV]
  · intro h hh
    have hhV : V.map (MulAut.conj h).toMonoidHom = V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.mem_inf.1 hh).2
    have hVle : V ≤ (U : Subgroup S) ⊔ zpowers (h * n) := by
      rw [← hhV, ← hnU, Subgroup.map_conj_map_conj]
      rintro _ ⟨u, hu, rfl⟩
      have hm : h * n ∈ (U : Subgroup S) ⊔ zpowers (h * n) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hm (Subgroup.mem_sup_left hu))
        (Subgroup.inv_mem _ hm)
    rw [eq_top_iff, ← htop]
    exact sup_le le_sup_left hVle

theorem k_19_21_opp_of_classical {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus)
    (h : CFSG.Blueprint.LieModel S t n 2 f) : K_19_21_opp S := by
  have hadm := CFSG.Blueprint.LieModel.admissible h
  have hc := CFSG.Blueprint.LieModel.statedClassicalModel h
    (by rcases ht with rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨B, N, hBN⟩ : ∃ B N : Subgroup S, IsSplitBNPair 2 B N := by
    rcases ht with rfl | rfl | rfl | rfl
    · exact burnsideI2BN_PSL Nat.prime_two hadm hc
    · exact burnsideI2BN_PSU Nat.prime_two hadm hc
    · exact burnsideI2BN_PSp Nat.prime_two hadm hc
    · exact burnsideI2BN_POmegaMinus Nat.prime_two hadm hc
  exact k_19_21_opp_of_splitBN hBN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end

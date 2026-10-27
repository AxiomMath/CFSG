module

public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofLF
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Defs
public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs
import CFSG.Models.PGLSimple
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (projSL)

private theorem exists_two_element_fixed_of_L38 {X : Type} [Group X] [Finite X] {N : Subgroup X}
    [N.Normal] {p : ℕ} [Fact p.Prime] (hFF : SimsR1L38FaithfulFix) (hp5 : 5 ≤ p)
    (e : X ⧸ N ≃* projSL 3 (GaloisField 2 3)) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : X →* (V →ₗ[ZMod p] V)) (hN : N ≤ ρ.ker)
    (hρ : ∃ x, ρ x ≠ 1) :
    ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1)) := by
  have : IsSimpleGroup (projSL 3 (GaloisField 2 3)) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  set ρbar := QuotientGroup.lift N ρ hN with hρbar
  have hinj : Function.Injective ρbar := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρbar.ker with hb | ht
    · exact hb
    · exfalso
      obtain ⟨x, hx⟩ := hρ
      apply hx
      have hmem : (x : X ⧸ N) ∈ ρbar.ker := ht ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hρbar, QuotientGroup.lift_mk] at hmem
      exact hmem
  set ρ' := ρbar.comp e.symm.toMonoidHom with hρ'
  have hρ'inj : Function.Injective ρ' := hinj.comp e.symm.injective
  obtain ⟨s, hord, hdim⟩ := hFF p hp5 V ρ' hρ'inj
  have hss : s * s = 1 := by
    have h2 : s ^ orderOf s = 1 := pow_orderOf_eq_one s
    rw [hord] at h2
    rw [← sq]
    exact h2
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  obtain ⟨t, htu, k, htk⟩ := TwoStarProof.exists_two_element_lift (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (y := e.symm s) (by rw [← map_mul, hss, map_one])
  have hρt : ρ t = ρ' s := by
    rw [hρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← htu, QuotientGroup.mk'_apply,
      hρbar, QuotientGroup.lift_mk]
  refine ⟨t, ?_, ⟨k, htk⟩, ?_⟩
  · rw [hρt]
    intro h1
    exact hs1 (hρ'inj (h1.trans (map_one ρ').symm))
  · rw [hρt]
    exact hdim

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

open TwoStarProof in
theorem lfAt_c_L38 (hFF : SimsR1L38FaithfulFix) (hSF : SimsR1L38SolvableFix)
    (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hL : IsL3Eight L) : LFAt L c := by
  obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 3)) := by
    rcases hL with ⟨h1, -⟩ | ⟨-, he⟩
    · norm_num at h1
    · exact he
  have hLC := le_centralizer_of_config h
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) : Set G) :=
    Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _)
  have hLH := hLC.trans hCH
  have : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have := Sec4.aschbacherSolvableCore_characteristic L
  have hfix : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (V : Type) [AddCommGroup V]
      [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : L →* (V →ₗ[ZMod p] V)),
        (∃ x, ρ x ≠ 1) → ∃ t : L, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
          3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1)) := by
    intro p _ hp5 V _ _ _ ρ hρ
    by_cases hθ : aschbacherSolvableCore 3 L ≤ ρ.ker
    · exact exists_two_element_fixed_of_L38 hFF hp5 e ρ hθ hρ
    · have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
        (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
      have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
        (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
      exact hSF p hp5 L inferInstance (aschbacherSolvableCore 3 L) hθs hθ3 ⟨e⟩ V ρ hθ
  by_contra hnot
  obtain ⟨p, _, hp5, t, ht1, ⟨k, htk⟩, EΘ, r, hr, hEcard, hEcomm, hEexp, hEfix⟩ :=
    exists_fixed_elemAbelian hLH (not_three_dvd_card_inSubgroup_theta _) hnot hfix
  obtain ⟨X₂, hX₂, R', hR'X₂, hR'e, hR'card⟩ := exists_twoLocal_elemAbelian (Sec6.theta_le _)
    (pCore_theta_le_pCore _) hLH (by omega) ht1 htk hEcard hEcomm hEexp hEfix
  have h1 := Sec5.le_pRank_of_elemAbelian (Fact.out : p.Prime) hR'X₂ hR'e hR'card
  have h2 := CFSG.RankThree.Classical.pRank_le_localRank (Fact.out : p.Prime).one_lt hX₂
  have h3 := h.localRank_lt p Fact.out (by omega)
  omega

end Certified

end CFSG.RankThree.PartTwo.Sec11.SimsR1

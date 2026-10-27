module

public import CFSG.RankThree.PartOne.S12.Sec12Fus
import CFSG.RankThree.PartOne.S12.Sec12FusMove
import CFSG.RankThree.PartOne.S12.Sec12FusGen
import CFSG.RankThree.PartOne.S12.Sec125Moved
import CFSG.RankThree.PartOne.S12.Sec13Zero
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Sec12Fus

theorem mem_sup_of_commute' {S T : Subgroup G} (hc : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : G}
    (hx : x ∈ S ⊔ T) : ∃ s ∈ S, ∃ t ∈ T, s * t = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ s ∈ S, ∃ t ∈ T, s * t = x) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, T.one_mem, mul_one x⟩
    · exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  · exact ⟨1, S.one_mem, 1, T.one_mem, one_mul 1⟩
  · rintro x y - - ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
    refine ⟨s * s', S.mul_mem hs hs', t * t', T.mul_mem ht ht', ?_⟩
    calc s * s' * (t * t') = s * (s' * t) * t' := by group
      _ = s * (t * s') * t' := by rw [hc s' hs' t ht]
      _ = s * t * (s' * t') := by group
  · rintro x - ⟨s, hs, t, ht, rfl⟩
    refine ⟨s⁻¹, S.inv_mem hs, t⁻¹, T.inv_mem ht, ?_⟩
    have h1 : s⁻¹ * t⁻¹ = t⁻¹ * s⁻¹ := by
      calc s⁻¹ * t⁻¹ = (t * s)⁻¹ := by group
        _ = (s * t)⁻¹ := by rw [hc s hs t ht]
        _ = t⁻¹ * s⁻¹ := by group
    rw [h1]
    group

theorem eq_of_sectionTenRel_of_mem_thetaComponentsAt [Finite G] {p : ℕ} (hp : p.Prime) {b : G}
    {I J : Subgroup G} (hI : I ∈ thetaComponentsAt p b) (hJ : J ∈ thetaComponentsAt p b)
    (hrel : sectionTenRel p I J) : I = J := by
  by_contra hne
  have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
  have hYsol : Group.IsSolvable ↥(I ⊓ J) := by
    by_contra hns
    apply hne
    refine EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt hp hI hJ
      (EmbeddingFixedResidual.ne_bot_inSubgroup_perfectResidual_of_not_isSolvable hns)
      (EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _) ?_ ?_
    · exact (Subgroup.map_subtype_le _).trans inf_le_left
    · exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hsurj := EmbeddingFixedResidual.surjective_inclusion_quotient (inf_le_left : I ⊓ J ≤ I) hrel
  have hsolQ : Group.IsSolvable (↥I ⧸ aschbacherSolvableCore p ↥I) :=
    Group.isSolvable_of_surjective hsurj
  have := LocalCores.isQuasisimple_nontrivial hq
  have := hq.1
  exact Group.IsPerfect.not_isSolvable _ hsolQ

end Sec12Fus

theorem node1213Max_of_inputs : Node1213Max := by
  classical
  intro G _ _ p A c L E ctx b K I X P Q hL hC hne hcomm
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) x hx
  have hcA : c ∈ A := h.c_mem
  obtain ⟨hbA, hbL, hb1⟩ := hL.b_mem
  have hIF : I ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.2 ⟨b, hbA, hb1, hL.I_mem⟩
  have hI0 : I ∈ sectionTenZero p A := by
    obtain ⟨S, hSK, hS1, hS2, hSA, hSc⟩ := hL.two
    exact ⟨hIF, S, hSK.trans hL.K_le, hS1, hS2, hSA, hSc⟩
  have hAP : A ≤ P := h.A_le_E.trans (hC.X_sylow.2.trans hC.P_sylow.2)
  have hAI : A ≤ Subgroup.normalizer (I : Set G) := fun a ha => hC.P_norm (hAP ha)
  have hIb : I ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.1 hL.I_mem).1
  have hKne : K ≠ ⊥ := Sec125.ne_bot_of_isQuasisimple hL.K_qs
  have hKnorm : ∀ a ∈ A, a ∈ Subgroup.normalizer (K : Set G) := by
    intro a ha
    have hac : a ∈ cNormalizer c := Sec12Fus.mem_cNormalizer_of_commute (hAcomm a ha c hcA)
    have haW : a ∈ torusNormalizer E := Subgroup.le_normalizer (h.A_le_E ha)
    have haL : a ∈ Subgroup.normalizer (L : Set G) := ctx.facts.twoB ⟨hac, haW⟩
    have hab : a * b * a⁻¹ = b := by
      rw [hAcomm a ha b hbA]
      group
    have hLC : conjBy a (L ⊓ Subgroup.centralizer ({b} : Set G)) =
        L ⊓ Subgroup.centralizer ({b} : Set G) := by
      ext x
      rw [Equivariance.mem_conjBy, Subgroup.mem_inf, Subgroup.mem_inf]
      have hCb : a⁻¹ * x * a ∈ Subgroup.centralizer ({b} : Set G) ↔
          x ∈ Subgroup.centralizer ({b} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff, Sec12Fus.conj_comm_iff, hab,
          ← Subgroup.mem_centralizer_singleton_iff]
      have hLn : a⁻¹ * x * a ∈ L ↔ x ∈ L := by
        constructor
        · intro h1
          have := (Subgroup.mem_normalizer_iff.1 haL (a⁻¹ * x * a)).1 h1
          simpa [mul_assoc] using this
        · intro h1
          have hn' : a⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
            (Subgroup.normalizer (L : Set G)).inv_mem haL
          have := (Subgroup.mem_normalizer_iff.1 hn' x).1 h1
          simpa [mul_assoc] using this
      rw [hCb, hLn]
    have hKa : conjBy a K = K := by
      rw [hL.K_eq]
      unfold kLayer
      rw [← Equivariance.inSubgroup_layer_conjBy, hLC]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hKa
  have hIstar : ∀ J ∈ thetaComponentFamily p A, sectionTenRel p I J → sectionTenRel p J I := by
    intro J hJ hrel
    obtain ⟨a, haA, ha1, hJa⟩ := mem_thetaComponentFamily_iff.1 hJ
    have hJC : J ≤ Subgroup.centralizer ({a} : Set G) := (mem_thetaComponentsAt_iff.1 hJa).1
    have htriv : ∀ i ∈ I, a * i * a⁻¹ * i⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I :=
      EmbeddingFixedResidual.trivial_action_of_eq_sup_centralizing (hAI haA) hJC hrel
    have haK : a ∈ Subgroup.centralizer (K : Set G) := by
      have hKa : ⁅K, Subgroup.zpowers a⁆ = ⊥ := by
        refine Sec12Fus.commutator_eq_bot_of_le_theta hp hL.K_qs (I := I)
          (Subgroup.zpowers_le.2 (hKnorm a haA)) ?_
        intro y hy k hk
        exact (EmbeddingFixedResidual.forall_mem_zpowers_trivial_action (hAI haA) htriv y hy).2 k
          (hL.K_le hk)
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKa
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.1 (hle hk) a (Subgroup.mem_zpowers a)).symm
    have haBC : a ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c := by
      rw [← hL.C_A]
      exact ⟨haA, haK⟩
    obtain ⟨s, hs, t, ht, hst⟩ := Sec12Fus.mem_sup_of_commute'
      (S := Subgroup.zpowers b) (T := Subgroup.zpowers c)
      (fun s hs t ht => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
        exact ((show Commute b c from hAcomm b hbA c hcA).zpow_zpow i j).eq) haBC
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    have hcp : c ^ p = 1 := hApow c hcA
    have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
    have hbord : orderOf b = p := orderOf_eq_prime (hApow b hbA) hb1
    have hpj : (p : ℤ) ∣ j := by
      by_contra hpj
      have hbE : b ∈ thetaQuotientCentralizer p A I := by
        rw [mem_thetaQuotientCentralizer_iff]
        refine ⟨hbA, hAI hbA, fun i hi => ?_⟩
        have hbi : i * b = b * i := Subgroup.mem_centralizer_singleton_iff.1 (hIb hi)
        have : b * i * b⁻¹ * i⁻¹ = 1 := by
          rw [← hbi]
          group
        rw [this]
        exact Subgroup.one_mem _
      have haE : a ∈ thetaQuotientCentralizer p A I :=
        mem_thetaQuotientCentralizer_iff.2 ⟨haA, hAI haA, htriv⟩
      have htE : c ^ j ∈ thetaQuotientCentralizer p A I := by
        have h1 : c ^ j = (b ^ i)⁻¹ * a := by
          rw [← hst]
          group
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hbE i)) haE
      have hcj1 : c ^ j ≠ 1 := by
        intro h1
        exact hpj (by
          have := (orderOf_dvd_iff_zpow_eq_one).2 h1
          rwa [hcord] at this)
      have hzp : Subgroup.zpowers (c ^ j) = Subgroup.zpowers c :=
        zpowers_eq_of_mem_of_ne_one hp hcord (Subgroup.zpow_mem_zpowers c j) hcj1
      have hcE' : c ∈ thetaQuotientCentralizer p A I := by
        have : c ∈ Subgroup.zpowers (c ^ j) := by
          rw [hzp]
          exact Subgroup.mem_zpowers c
        exact (Subgroup.zpowers_le.2 htE) this
      have hctriv := (mem_thetaQuotientCentralizer_iff.1 hcE').2.2
      have hI_le : I ≤ inSubgroup (aschbacherSolvableCore p) I := by
        calc I = ⁅I, Subgroup.zpowers c⁆ := hcomm.symm
          _ ≤ inSubgroup (aschbacherSolvableCore p) I := by
            rw [Subgroup.commutator_le]
            intro i hi y hy
            have h2 := (EmbeddingFixedResidual.forall_mem_zpowers_trivial_action
              (hAI hcA) hctriv y hy).2 i hi
            have e : ⁅i, y⁆ = (y * i * y⁻¹ * i⁻¹)⁻¹ := by
              simp only [commutatorElement_def]
              group
            rw [e]
            exact Subgroup.inv_mem _ h2
      exact Sec12Fus.not_le_theta_of_isQuasisimple hp hL.K_qs (I := I) (hL.K_le.trans hI_le)
    have hctj : c ^ j = 1 := by
      obtain ⟨m, rfl⟩ := hpj
      rw [zpow_mul, zpow_natCast, hcp, one_zpow]
    have ha_b : a = b ^ i := by
      rw [← hst, hctj, mul_one]
    have hab1 : b ^ i ≠ 1 := by
      rw [← ha_b]
      exact ha1
    have hzab : Subgroup.zpowers a = Subgroup.zpowers b := by
      rw [ha_b]
      exact zpowers_eq_of_mem_of_ne_one hp hbord (Subgroup.zpow_mem_zpowers b i) hab1
    have hJb : J ∈ thetaComponentsAt p b := by
      have := thetaComponentsAt_eq_of_zpowers_eq p hzab
      rw [← this]
      exact hJa
    have hIJ := Sec12Fus.eq_of_sectionTenRel_of_mem_thetaComponentsAt hp hL.I_mem hJb hrel
    rw [← hIJ]
    exact sectionTenRel_refl p I
  exact ⟨⟨hI0, hIF, hIstar⟩, hL.I_mem⟩

end CFSG.RankThree.PartOne

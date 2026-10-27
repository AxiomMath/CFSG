module

public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofTheta
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Res148

theorem ker_le_theta_or_subsingleton {K Q : Type*} [Group K] [Group Q] [Finite K] (ψ : K →* Q)
    (hψ : Function.Surjective ψ) (hQ : Group.IsPerfect Q)
    (hKq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K)) (hker : ¬ 3 ∣ Nat.card ψ.ker) :
    ψ.ker ≤ aschbacherSolvableCore 3 K ∨ Subsingleton Q := by
  set θK := aschbacherSolvableCore 3 K with hθK
  obtain ⟨hθs, hθc, -, -⟩ := solvable_prime_complement_core_characterization (H := K)
    Nat.prime_three
  have hθn : θK.Normal := Subgroup.normal_of_characteristic θK
  set T := ψ.ker.map (QuotientGroup.mk' θK) with hT
  have hTn : T.Normal := (MonoidHom.normal_ker ψ).map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hTn with htop | hcen
  · right
    have hall : ∀ k : K, ψ k ∈ θK.map ψ := by
      intro k
      have hk : (QuotientGroup.mk' θK k) ∈ T := htop ▸ Subgroup.mem_top _
      obtain ⟨k', hk', hkk'⟩ := hk
      have h1 : k'⁻¹ * k ∈ θK := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkk'
        exact hkk'
      refine ⟨k'⁻¹ * k, h1, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk', inv_one, one_mul]
    have hsol : Group.IsSolvable Q := by
      have h1 : Group.IsSolvable ↥(θK.map ψ) :=
        Group.isSolvable_of_surjective (f := ψ.subgroupMap θK) (ψ.subgroupMap_surjective θK)
      have htopQ : θK.map ψ = ⊤ := by
        rw [eq_top_iff]
        intro q _
        obtain ⟨k, rfl⟩ := hψ q
        exact hall k
      rw [htopQ] at h1
      exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom)
        (MulEquiv.surjective _)
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable Q hsol
  · left
    have hTs : Group.IsSolvable ↥T := by
      refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
      exact (Subgroup.mem_center_iff.mp (hcen b.2) a)
    have hT3 : ¬ 3 ∣ Nat.card ↥T := fun h3 => hker (h3.trans (Subgroup.card_map_dvd _ _))
    have hle := (solvable_prime_complement_core_characterization (H := K ⧸ θK)
      Nat.prime_three).2.2.2.1 T hTn hTs hT3
    rw [(theta_quotient_core_and_ranks (G := K)).1, le_bot_iff, hT, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hle
    exact hle

theorem theta_quot_of_ker_le {K Q : Type*} [Group K] [Group Q] [Finite K] [Finite Q]
    (ψ : K →* Q) (hψ : Function.Surjective ψ) (hkerθ : ψ.ker ≤ aschbacherSolvableCore 3 K)
    (hker : ¬ 3 ∣ Nat.card ψ.ker) :
    aschbacherSolvableCore 3 Q = (aschbacherSolvableCore 3 K).map ψ ∧
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* Q ⧸ aschbacherSolvableCore 3 Q) := by
  set θK := aschbacherSolvableCore 3 K with hθK
  set θQ := aschbacherSolvableCore 3 Q with hθQ
  obtain ⟨hθKs, hθKc, hθK3, -⟩ := solvable_prime_complement_core_characterization (H := K)
    Nat.prime_three
  obtain ⟨hθQs, hθQc, hθQ3, hθQmax, -⟩ := solvable_prime_complement_core_characterization
    (H := Q) Nat.prime_three
  have hθKn : θK.Normal := Subgroup.normal_of_characteristic θK
  have hθQn : θQ.Normal := Subgroup.normal_of_characteristic θQ
  have h1 : θK.map ψ ≤ θQ := by
    refine hθQmax _ (hθKn.map ψ hψ) ?_ ?_
    · exact Group.isSolvable_of_surjective (f := ψ.subgroupMap θK) (ψ.subgroupMap_surjective θK)
    · exact fun h3 => hθK3 (h3.trans (Subgroup.card_map_dvd _ _))
  set M := θQ.comap ψ with hM
  have hMn : M.Normal := hθQn.comap ψ
  have hθKM : θK ≤ M := fun k hk => h1 ⟨k, hk, rfl⟩
  set g : ↥M →* ↥θQ := (ψ.comp M.subtype).codRestrict θQ (fun m => m.2) with hg
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨k, hk⟩ := hψ q
    refine ⟨⟨k, show ψ k ∈ θQ by rw [hk]; exact q.2⟩, Subtype.ext ?_⟩
    exact hk
  have hgker : g.ker ≤ (θK.subgroupOf M) := by
    intro m hm
    have hm' : ψ m = 1 := congrArg Subtype.val hm
    exact hkerθ hm'
  have hMs : Group.IsSolvable ↥M := by
    have : Group.IsSolvable ↥(θK.subgroupOf M) := by
      have e := Subgroup.subgroupOfEquivOfLe hθKM
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hrange : g.ker ≤ (θK.subgroupOf M).subtype.range := by
      rw [Subgroup.range_subtype]
      exact hgker
    exact Group.isSolvable_of_ker_le_range (θK.subgroupOf M).subtype g hrange
  have hM3 : ¬ 3 ∣ Nat.card ↥M := by
    intro h3
    have hcard : Nat.card ↥M = Nat.card ↥g.range * Nat.card ↥g.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    have hr : ¬ 3 ∣ Nat.card ↥g.range := by
      intro h
      apply hθQ3
      exact h.trans (Subgroup.card_subgroup_dvd_card _)
    have hk : ¬ 3 ∣ Nat.card ↥g.ker := by
      intro h
      apply hker
      refine h.trans ?_
      have hle : g.ker.map M.subtype ≤ ψ.ker := by
        rintro _ ⟨m, hm, rfl⟩
        exact congrArg Subtype.val hm
      rw [← Subgroup.card_map_of_injective M.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    rw [hcard] at h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hr h
    · exact hk h
  have hMθ : M ≤ θK :=
    (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.2.1 M hMn hMs
      hM3
  have hMeq : M = θK := le_antisymm hMθ hθKM
  have hθeq : θQ = θK.map ψ := by
    refine le_antisymm ?_ h1
    intro q hq
    obtain ⟨k, rfl⟩ := hψ q
    exact ⟨k, hMθ hq, rfl⟩
  refine ⟨hθeq, ⟨?_⟩⟩
  set f : K →* Q ⧸ θQ := (QuotientGroup.mk' θQ).comp ψ with hf
  have hfs : Function.Surjective f := (QuotientGroup.mk'_surjective θQ).comp hψ
  have hfker : f.ker = θK := by
    rw [← hMeq]
    ext k
    simp [hf, hM, QuotientGroup.eq_one_iff]
  exact (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs)

end Res148

open Res148 Main148

end CFSG.RankThree.PartTwo.Sec14

module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.SteinbergBK

open Subgroup CFSG

theorem perfect_subgroup_prime_kernel_surjection {p : ℕ} (hp : p.Prime) {E : Type*} [Group E]
    [Finite E] (N : Subgroup E) [N.Normal] (hN : IsPGroup p N) (hsimple : IsSimpleGroup (E ⧸ N))
    (hnab : ∃ a b : E ⧸ N, a * b ≠ b * a)
    (hsolv : ∀ H : Subgroup (E ⧸ N), H ≠ ⊤ → Group.IsSolvable H)
    (K : Subgroup E) (hK1 : K ≠ ⊥) (hKperf : Group.IsPerfect K) :
    K ⊔ N = ⊤ ∧ N.subgroupOf K = pCore p K ∧
      ∃ e : K ⧸ pCore p K ≃* E ⧸ N, ∀ k : K, e (k : K ⧸ pCore p K) = ((k : E) : E ⧸ N) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set f : K →* E ⧸ N := (QuotientGroup.mk' N).comp K.subtype with hf
  have hkerf : f.ker = N.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rfl
  have hfK : f.range = ⊤ := by
    by_contra hne
    have hsol : Group.IsSolvable f.range := hsolv _ hne
    have hperf : Group.IsPerfect f.range := Group.IsPerfect.range f
    have hsub : Subsingleton f.range := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact Group.IsPerfect.not_isSolvable f.range hsol
    have hKN : K ≤ N := by
      intro k hk
      have h1 : f ⟨k, hk⟩ = 1 := by
        have := Subsingleton.elim (⟨f ⟨k, hk⟩, ⟨_, rfl⟩⟩ : f.range) 1
        exact congrArg Subtype.val this
      have h2 : (⟨k, hk⟩ : K) ∈ f.ker := h1
      rw [hkerf, mem_subgroupOf] at h2
      exact h2
    have hKp : IsPGroup p K := hN.to_le hKN
    have : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hK1
    have := hKp.isNilpotent
    exact Group.IsPerfect.not_isSolvable K inferInstance
  have hfs : Function.Surjective f := MonoidHom.range_eq_top.mp hfK
  have hKN : K ⊔ N = ⊤ := by
    have hmap : K.map (QuotientGroup.mk' N) = ⊤ := by
      rw [← hfK, hf, MonoidHom.range_comp, range_subtype]
    have h := comap_map_eq (QuotientGroup.mk' N) K
    rw [hmap, comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hNKp : IsPGroup p (N.subgroupOf K) := fun x => by
    obtain ⟨n, hn⟩ := hN ⟨((x : K) : E), x.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hNK : N.subgroupOf K ≤ pCore p K := le_sSup ⟨hkerf ▸ f.normal_ker, hNKp⟩
  have hpN : pCore p K ≤ N.subgroupOf K := by
    have : ((pCore p K).map f).Normal := (pCore_normal).map f hfs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pCore p K).map f) with h | h
    · rw [← hkerf]
      exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have hp : IsPGroup p (E ⧸ N) := by
        have h1 : IsPGroup p ((pCore p K).map f) := pCore_isPGroup.map f
        rw [h] at h1
        exact h1.of_equiv topEquiv
      have := hp.isNilpotent
      have hZ := IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (E ⧸ N))
      have hZne : center (E ⧸ N) ≠ ⊥ := by
        have := hp.center_nontrivial
        exact (nontrivial_iff_ne_bot _).mp this
      obtain ⟨a, b, hab⟩ := hnab
      have hZt := hZ.resolve_left hZne
      exact hab ((mem_center_iff.mp (hZt ▸ mem_top b) a))
  have hcore : N.subgroupOf K = pCore p K := le_antisymm hNK hpN
  refine ⟨hKN, hcore, (QuotientGroup.quotientMulEquivOfEq (hcore.symm.trans hkerf.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun k => rfl⟩

end CFSG.Quasithin.SteinbergBK

module

public import CFSG.Quasithin.H13.AS91Sec5Act
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13.AS91

open MulAction

variable {G : Type*} [Group G]

theorem ker_le_of_S5 [Finite G] (A B S R : Subgroup G) (hSB : S ≤ B)
    (hcard : Nat.card (objOf A B (basePt B)) = 5)
    (hφ : ∃ φ : ↥S →* Equiv.Perm (Fin 5), Function.Surjective φ ∧ φ.ker = R.subgroupOf S)
    (hRfix : ∀ r ∈ R, ∀ p ∈ objOf A B (basePt B), r • p = p)
    (htrans : ∀ p ∈ objOf A B (basePt B), ∀ q ∈ objOf A B (basePt B), ∃ s ∈ S, s • p = q) :
    ∀ s ∈ S, (∀ p ∈ objOf A B (basePt B), s • p = p) → s ∈ R := by
  obtain ⟨f, hfs, hfk⟩ := hφ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥S →* Equiv.Perm ↥(objOf A B (basePt B)),
      ∀ (s : ↥S) (p : ↥(objOf A B (basePt B))),
        ((ρ s p : ↥(objOf A B (basePt B))) : G ⧸ A) = (s : G) • (p : G ⧸ A) :=
    ⟨(residuePerm A B).comp (Subgroup.inclusion hSB),
      fun s p => residuePerm_apply A B (Subgroup.inclusion hSB s) p⟩
  obtain ⟨N, hN⟩ : ∃ N : Subgroup ↥S, N = ρ.ker := ⟨_, rfl⟩
  have hNnormal : N.Normal := by
    rw [hN]
    infer_instance
  have hchar : ∀ n : ↥S, n ∈ N ↔ ∀ p ∈ objOf A B (basePt B), (n : G) • p = p := by
    intro n
    rw [hN, MonoidHom.mem_ker]
    constructor
    · intro h p hp
      have h1 := hρ n ⟨p, hp⟩
      rw [h, Equiv.Perm.one_apply] at h1
      exact h1.symm
    · intro h
      refine Equiv.ext fun p => Subtype.ext ?_
      rw [hρ n p, Equiv.Perm.one_apply]
      exact h (p : G ⧸ A) p.2
  have hfle : f.ker ≤ N := by
    intro s hs
    rw [hfk, Subgroup.mem_subgroupOf] at hs
    rw [hchar]
    intro p hp
    exact hRfix _ hs p hp
  have hNle : N ≤ f.ker := by
    by_contra hne
    obtain ⟨n, hnN, hnf⟩ : ∃ n ∈ N, f n ≠ 1 := by
      by_contra h
      apply hne
      intro x hx
      rw [MonoidHom.mem_ker]
      by_contra hfx
      exact h ⟨x, hx, hfx⟩
    haveI hN'normal : (N.map f).Normal := hNnormal.map f hfs
    have hN'ne : N.map f ≠ ⊥ := by
      intro h
      have hmem : f n ∈ N.map f := Subgroup.mem_map_of_mem f hnN
      rw [h, Subgroup.mem_bot] at hmem
      exact hnf hmem
    haveI hN'triv : Nontrivial (N.map f) := (Subgroup.nontrivial_iff_ne_bot (N.map f)).mpr hN'ne
    have hA5 : alternatingGroup (Fin 5) ≤ N.map f :=
      Equiv.Perm.alternatingGroup_le_of_normal (N := N.map f) (by simp) inferInstance
    have hdvd2 : (N.map f).index ∣ 2 := by
      have h := Subgroup.index_dvd_of_le hA5
      rwa [alternatingGroup.index_eq_two] at h
    have hidx : (N.map f).index = N.index := Subgroup.index_map_eq N hfs hfle
    rw [hidx] at hdvd2
    have hT : (MulAction.stabilizer S (basePt A)).index ∣ N.index := by
      apply Subgroup.index_dvd_of_le
      intro n hn
      rw [MulAction.mem_stabilizer_iff]
      exact (hchar n).mp hn _ (basePt_mem_objOf_base A B)
    have horb : MulAction.orbit S (basePt A) = objOf A B (basePt B) := by
      ext z
      constructor
      · intro hz
        obtain ⟨s, hsz⟩ := MulAction.mem_orbit_iff.mp hz
        rw [← hsz]
        exact smul_mem_objOf_base (hSB s.2) (basePt_mem_objOf_base A B)
      · intro hz
        obtain ⟨s, hs, hsz⟩ := htrans (basePt A) (basePt_mem_objOf_base A B) z hz
        exact MulAction.mem_orbit_iff.mpr ⟨⟨s, hs⟩, hsz⟩
    have hT5 : (MulAction.stabilizer S (basePt A)).index = 5 := by
      rw [MulAction.index_stabilizer, horb, ← Nat.card_coe_set_eq, hcard]
    rw [hT5] at hT
    have h52 : 5 ∣ 2 := dvd_trans hT hdvd2
    omega
  intro s hs hfix
  have hsN : (⟨s, hs⟩ : ↥S) ∈ N := (hchar ⟨s, hs⟩).mpr hfix
  have hsf : (⟨s, hs⟩ : ↥S) ∈ f.ker := hNle hsN
  rw [hfk, Subgroup.mem_subgroupOf] at hsf
  exact hsf

end CFSG.Quasithin.H13.AS91

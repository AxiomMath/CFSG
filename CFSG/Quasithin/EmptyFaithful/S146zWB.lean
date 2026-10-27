module

public import CFSG.Quasithin.Background.C2PushY
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.C2Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure WreathCfg (H R J : Subgroup G) : Prop where
  sqtk : IsSQTKIn H
  charTwo : CharTwo H
  radical : IsTwoRadicalIn H R
  cpu : cgsIn H R ≤ H ⊓ Subgroup.normalizer (R : Set G)
  comp : J ∈ cComp H
  quasi : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)
  move : ¬ R ≤ Subgroup.normalizer (J : Set G)

structure WreathData (H R J J' : Subgroup G) (ρ : G) : Prop where
  cfg : WreathCfg H R J
  mem : ρ ∈ R
  eq : J' = conjByElt ρ J
  ne : J' ≠ J
  orb : ∀ x ∈ H, conjByElt x J = J ∨ conjByElt x J = J'
  comm : ⁅J, J'⁆ ≤ pCoreOf 2 H
  inter : (J ⊔ pCoreOf 2 H) ⊓ (J' ⊔ pCoreOf 2 H) = pCoreOf 2 H

omit [Finite G] in
theorem conjByElt_eq_self_iff {J : Subgroup G} {r : G} :
    conjByElt r J = J ↔ r ∈ Subgroup.normalizer (J : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.symm

theorem WreathCfg.exists_data {H R J : Subgroup G} (hOrb : A3Orbits G) (h : WreathCfg H R J) :
    ∃ (J' : Subgroup G) (ρ : G), WreathData H R J J' ρ := by
  obtain ⟨T, hT, hRT⟩ := exists_isSylowTwoOf_ge_of_isPGroup h.radical.1 h.radical.isPGroup
  obtain ⟨hconj, hcase⟩ := hOrb H T J h.sqtk hT h.comp
  rcases hcase with hall | ⟨t, htT, htn, hTJ, hcomm, hint, -⟩
  · exact absurd (fun r hr => hall r (hRT hr)) h.move
  · obtain ⟨r, hrR, hrn⟩ : ∃ r ∈ R, r ∉ Subgroup.normalizer (J : Set G) := by
      by_contra hcon
      push Not at hcon
      exact h.move hcon
    have hr : conjByElt r J ∈ conjSubgroupsBy T J := ⟨r, hRT hrR, rfl⟩
    rw [hTJ] at hr
    have hJr : conjByElt r J = conjByElt t J := by
      rcases hr with h1 | h1
      · exact absurd (conjByElt_eq_self_iff.mp h1) hrn
      · exact h1
    refine ⟨conjByElt r J, r, h, hrR, rfl, fun h1 => hrn (conjByElt_eq_self_iff.mp h1), ?_, ?_, ?_⟩
    · intro x hx
      have hx' : conjByElt x J ∈ conjSubgroupsBy H J := ⟨x, hx, rfl⟩
      rw [hconj, hTJ] at hx'
      rcases hx' with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans hJr.symm)
    · rw [hJr]
      exact hcomm
    · rw [hJr]
      exact hint

omit [Finite G] in
theorem conjByElt_mul_W (x y : G) (K : Subgroup G) :
    conjByElt (x * y) K = conjByElt x (conjByElt y K) := by
  ext z
  simp only [mem_conjByElt, mul_inv_rev, mul_assoc]

omit [Finite G] in
theorem conjByElt_injective_W (x : G) {A B : Subgroup G} (h : conjByElt x A = conjByElt x B) :
    A = B := by
  ext z
  have := Iff.of_eq (congrArg (fun K : Subgroup G => x * z * x⁻¹ ∈ K) h)
  simpa [mem_conjByElt, mul_assoc] using this

omit [Finite G] in
theorem isQuasisimple_conjByElt {L : Subgroup G} (g : G)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    CFSG.IsQuasisimple (↥(conjByElt g L) ⧸ CFSG.pCore 2 ↥(conjByElt g L)) := by
  set f : G ≃* G := MulAut.conj g with hf
  let φ : L ≃* (L.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      ((L.map f.toMonoidHom : Subgroup G) ⧸ CFSG.pCore 2 (L.map f.toMonoidHom : Subgroup G)) :=
    QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

namespace WreathData

variable {H R J J' : Subgroup G} {ρ : G} (d : WreathData H R J J' ρ)

include d

theorem R_le_H : R ≤ H := d.cfg.radical.1

theorem mem_H : ρ ∈ H := d.R_le_H d.mem

theorem comp_J' : J' ∈ cComp H := by
  rw [d.eq]
  exact C2Nine.conjByElt_mem_cComp d.cfg.comp (Subgroup.le_normalizer d.mem_H)

theorem quasi_J' : CFSG.IsQuasisimple (↥J' ⧸ CFSG.pCore 2 ↥J') := by
  rw [d.eq]
  exact isQuasisimple_conjByElt ρ d.cfg.quasi

theorem J_le_H : J ≤ H := le_of_mem_cComp d.cfg.comp

theorem J'_le_H : J' ≤ H := le_of_mem_cComp d.comp_J'

theorem orb' : ∀ x ∈ H, conjByElt x J' = J ∨ conjByElt x J' = J' := by
  intro x hx
  rw [d.eq, ← conjByElt_mul_W]
  rcases d.orb (x * ρ) (H.mul_mem hx d.mem_H) with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans d.eq)

theorem normalizer_sup : H ≤ Subgroup.normalizer ((J ⊔ J' : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 : (J ⊔ J').map (MulAut.conj x : G →* G) =
      conjByElt x J ⊔ conjByElt x J' := Subgroup.map_sup _ _ _
  rw [h1]
  have hne : conjByElt x J ≠ conjByElt x J' := fun h =>
    d.ne (conjByElt_injective_W x h).symm
  rcases d.orb x hx with h | h <;> rcases d.orb' x hx with h' | h'
  · exact absurd (h.trans h'.symm) hne
  · rw [h, h']
  · rw [h, h', sup_comm]
  · exact absurd (h.trans h'.symm) hne

theorem R_le_normalizer_sup : R ≤ Subgroup.normalizer ((J ⊔ J' : Subgroup G) : Set G) :=
  fun _ hr => d.normalizer_sup (d.R_le_H hr)

theorem sup_le_H : (J ⊔ J') ⊔ R ≤ H := sup_le (sup_le d.J_le_H d.J'_le_H) d.R_le_H

theorem isTwoRadicalIn_Y : IsTwoRadicalIn ((J ⊔ J') ⊔ R) R := by
  have hRp := d.cfg.radical.isPGroup
  refine ⟨le_sup_right, d.cfg.radical.2.1, le_antisymm
    (le_pCoreOf_inf_normalizer le_sup_right hRp) ?_⟩
  have hYH := d.sup_le_H
  have hYN : H ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (((J ⊔ J') ⊔ R : Subgroup G) : Set G) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨d.normalizer_sup hn.1, hn.2⟩
  have hB : H ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((((J ⊔ J') ⊔ R) ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) :
        Set G) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hYN hn, Subgroup.le_normalizer hn.2⟩
  have hle : pCoreOf 2 (((J ⊔ J') ⊔ R) ⊓ Subgroup.normalizer (R : Set G)) ≤
      pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (inf_le_inf_right _ hYH))
      (fun x hx => normalizer_le_normalizer_pCoreOf 2 _ (hB hx)) (pCoreOf_isPGroup 2 _)
  rw [← d.cfg.radical.2.2] at hle
  exact hle

theorem pCoreOf_Y_le : pCoreOf 2 ((J ⊔ J') ⊔ R) ≤ R := c2_1_pCore_le d.isTwoRadicalIn_Y

theorem pCoreOf_H_le : pCoreOf 2 H ≤ R := c2_1_pCore_le d.cfg.radical

theorem pCoreOf_H_le_Y : pCoreOf 2 H ≤ pCoreOf 2 ((J ⊔ J') ⊔ R) :=
  le_pCoreOf_of_le_normalizer 2 (d.pCoreOf_H_le.trans le_sup_right)
    (d.sup_le_H.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)

theorem charTwo_Y : CharTwo ((J ⊔ J') ⊔ R) :=
  charTwo_of_pCoreOf_le d.cfg.charTwo (d.pCoreOf_H_le.trans le_sup_right) d.sup_le_H

theorem sqtk_Y : IsSQTKIn ((J ⊔ J') ⊔ R) := d.cfg.sqtk.mono d.sup_le_H

end WreathData

end CFSG.Quasithin.S146zW

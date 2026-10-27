module

public import CFSG.Quasithin.Background.B56Inputs
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B1MoreElevenC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B56

section Glue

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)}

theorem exists_isFFStarMin (hne : G ≠ ⊥) (hJ : G = ffJ G) : ∃ A, IsFFStarMin G A := by
  by_contra hnone
  push Not at hnone
  have hno : ∀ A, ¬ IsFFStarOffender G A := fun A hA => by
    obtain ⟨B, hB, -⟩ := B1Red.exists_isFFStarMin_below hA
    exact hnone B hB
  have hJ' : ffJ G = ⊥ := by
    unfold ffJ
    simp [hno]
  exact hne (hJ.trans hJ')

omit [Finite V] in
theorem le_fittingOf_of_nilpotent_normal {N : Subgroup (MulAut V)} (hNG : N ≤ G)
    (hn : (N.subgroupOf G).Normal) (hnil : Group.IsNilpotent ↥N) : N ≤ fittingOf G := by
  have hnil' : Group.IsNilpotent ↥(N.subgroupOf G) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNG)).mpr hnil
  have h1 : N.subgroupOf G ≤ CFSG.fittingSubgroup ↥G := le_sSup ⟨hn, hnil'⟩
  have h2 := Subgroup.map_mono (f := G.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hNG] at h2

theorem exists_component (hP4 : AsB15Part4) (hc : B56Counterex G) {A : Subgroup (MulAut V)}
    (hA : IsFFStarMin G A) (hcent : A ≤ Subgroup.centralizer (fittingOf G : Set (MulAut V))) :
    ∃ L, CFSG.Open.IsComponentOf L G ∧ ⁅L, A⁆ = L := by
  have hAG : A ≤ G := hA.1.1
  have hAel : IsElemAbelian2 A := hA.1.2.2.1
  have hA2 : IsPGroup 2 A := hAel.isPGroup
  have hJ : G = ffJ G := hc.hyp.2.1
  by_contra hnone
  push Not at hnone
  have hcomp : ∀ L, CFSG.Open.IsComponentOf L G → A ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    intro L hL
    have hn : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B55.normalizes_comp hP4 hc.hV hJ hL
    have hAn : ∀ b ∈ A, ∀ k ∈ L, b * k * b⁻¹ ∈ L := fun b hb k hk =>
      B19Aux.conj_mem_of_le_normalizer (hAG.trans hn) hb hk
    rcases B1Red.commutator_eq_or_commute (Or.inl hL.2.2) hAn with h1 | h1
    · exact absurd h1 (hnone L hL)
    · intro a ha
      exact Subgroup.mem_centralizer_iff.2 fun l hl => (h1 a ha l hl).symm
  have hF : quasithinGenFitting G ≤ Subgroup.centralizer (A : Set (MulAut V)) := by
    unfold quasithinGenFitting
    refine sup_le ?_ (sSup_le fun K hK x hx => ?_)
    · refine sSup_le fun N hN x hx => ?_
      have hxF : x ∈ fittingOf G := le_fittingOf_of_nilpotent_normal hN.1 hN.2.1 hN.2.2 hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.1 (hcent ha) x hxF).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.1 (hcomp K hK ha) x hx).symm
  have hAc : A ≤ Subgroup.centralizer (quasithinGenFitting G : Set (MulAut V)) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun x hx => (Subgroup.mem_centralizer_iff.1 (hF hx) a ha).symm
  have hAF : A ≤ quasithinGenFitting G := fun a ha =>
    centralizer_quasithinGenFitting_le G ⟨hAG ha, hAc ha⟩
  exact hA.1.2.1 (B1More.eq_bot_of_le_center_genFitting hc.hyp.1 hA2 hAF hAc)

end Glue

theorem asB56_of_lemmas (hP4 : AsB15Part4) (h58 : AsB58) (h59 : AsB59) (h5610 : AsB5610)
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (G : Subgroup (MulAut V))
    (hne : G ≠ ⊥) (hB : B53Hyp G) : B56Cases G := by
  suffices H : ∀ N : ℕ, ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ G : Subgroup (MulAut V), Nat.card ↥G = N → G ≠ ⊥ → B53Hyp G → B56Cases G from
    H _ V hV G rfl hne hB
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ hV G hN hne hB
    by_contra hcase
    have hc : B56Counterex G :=
      ⟨hV, hne, hB, hcase, fun V' _ _ hV' G' hne' hB' hlt =>
        ih (Nat.card ↥G') (hN ▸ hlt) V' hV' G' rfl hne' hB'⟩
    obtain ⟨A, hA⟩ := exists_isFFStarMin hne hB.2.1
    obtain ⟨L, hL, hLA⟩ := exists_component hP4 hc hA (h58 V G hc A hA)
    exact h5610 V G hc A L hA hL hLA (h59 V G hc A L hA hL hLA)


end B56

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenTransport

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

section Conj

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_mem_ggAutomizerJoin {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {a : MulAut ↥Bs} (ha : a ∈ ggAutomizerJoin L Bs 𝒦) :
    ∃ g : G, (∀ r : MulAut ↥Bs, (ggRankOne Bs r).map (MulAut.conj g).toMonoidHom =
        ggRankOne Bs (a * r * a⁻¹)) ∧
      ∀ r r' : MulAut ↥Bs, (ggRankTwo Bs r r').map (MulAut.conj g).toMonoidHom =
        ggRankTwo Bs (a * r * a⁻¹) (a * r' * a⁻¹) := by
  obtain ⟨g, -, -, hg⟩ := exists_lift_of_mem_ggAutomizerJoin ha
  exact ⟨g, fun r => ggRankOne_map_conj hg r, fun r r' => ggRankTwo_map_conj hg r r'⟩

theorem map_conj_map_conj_inv (S : Subgroup G) (g : G) :
    (S.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = S := by
  rw [Subgroup.map_map]
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [hid, Subgroup.map_id]

theorem exists_su_four_hom_of_map_conj {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    {S T : Subgroup G} (g : G)
    (h : ∃ θ : Su K 2 f 4 →* G, θ.range =
      S.map (MulAut.conj g).toMonoidHom ⊔ T.map (MulAut.conj g).toMonoidHom) :
    ∃ θ : Su K 2 f 4 →* G, θ.range = S ⊔ T := by
  obtain ⟨θ, hθ⟩ := exists_su_four_hom_map_conj g⁻¹ h
  refine ⟨θ, ?_⟩
  rw [hθ, map_conj_map_conj_inv, map_conj_map_conj_inv]

end Conj

section Cfg

variable {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {L : Subgroup G}
  {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
  {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ} {e' : Fin m ≃ ι}

@[expose] def qtwoConjRefl (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) (e' : Fin m ≃ ι)
    (w : M.Group) (t : Fin m) : MulAut ↥Bs :=
  ((e (w * M.simple (e' t) * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)

theorem qtwo_transport (hfacts : QTwoMemberFacts Bs X M (ggAutomizerJoin L Bs 𝒦) e)
    {T : Finset (Fin m)} {w : M.Group}
    (hw : ∀ t ∈ T, qtwoConjRefl e e' w t ∈ ggAutomizer X Bs) :
    ∃ g : G, (∀ t ∈ T, (qtwoNode Bs (qtwoRefl e e') t).map (MulAut.conj g).toMonoidHom =
        ggRankOneIn X Bs (qtwoConjRefl e e' w t)) ∧
      ∀ s t : Fin m, (ggRankTwo Bs (qtwoRefl e e' s) (qtwoRefl e e' t)).map
          (MulAut.conj g).toMonoidHom =
        ggRankTwo Bs (qtwoConjRefl e e' w s) (qtwoConjRefl e e' w t) := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_of_mem_ggAutomizerJoin (𝒦 := 𝒦) (e w).2
  have hconj : ∀ t : Fin m, ((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
      qtwoRefl e e' t * ((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹ =
        qtwoConjRefl e e' w t := fun t => coe_conj_simple e w (e' t)
  refine ⟨g, fun t ht => ?_, fun s t => ?_⟩
  · have h1 : (qtwoNode Bs (qtwoRefl e e') t).map (MulAut.conj g).toMonoidHom =
        ggRankOne Bs (qtwoConjRefl e e' w t) := by
      rw [← hconj t]
      exact hg1 _
    rw [h1]
    exact hfacts.1 _ (hw t ht) (conjRefl_mem_ggCoxRefl e e' w t)
  · rw [hg2, hconj s, hconj t]

theorem qtwo_pair_of_orb (hfacts : QTwoMemberFacts Bs X M (ggAutomizerJoin L Bs 𝒦) e)
    (hM : M = (ggCoxeterMatrixD m).reindex e')
    (h6 : ∀ i, Nat.card ↥(qtwoNode Bs (qtwoRefl e e') i) = 6) {i j : Fin m}
    (hij : ggCoxeterMatrixD m i j = 3) (horb : GGOrbAt X Bs e e' {i, j}) :
    UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (qtwoW Bs (qtwoRefl e e') i j)
      (qtwoNode Bs (qtwoRefl e e') i) (qtwoNode Bs (qtwoRefl e e') j) := by
  haveI : Finite ι := Finite.of_equiv (Fin m) e'
  obtain ⟨w, hw⟩ := horb
  have hwi : qtwoConjRefl e e' w i ∈ ggAutomizer X Bs := hw i (by simp)
  have hwj : qtwoConjRefl e e' w j ∈ ggAutomizer X Bs := hw j (by simp)
  obtain ⟨g, hg1, hg2⟩ := qtwo_transport hfacts (T := {i, j}) hw
  have hnc := conjRefl_noncomm e e' hM w hij
  have hci : Nat.card ↥(ggRankOneIn X Bs (qtwoConjRefl e e' w i)) = 6 := by
    rw [← hg1 i (by simp), Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h6 i
  have hE1 := hfacts.2.1 _ hwi (conjRefl_mem_ggCoxRefl e e' w i) _ hwj
    (conjRefl_mem_ggCoxRefl e e' w j) hnc
  have hE2 := hfacts.2.2.1 _ hwi (conjRefl_mem_ggCoxRefl e e' w i) _ hwj
    (conjRefl_mem_ggCoxRefl e e' w j) hnc hci
  refine UnitaryBlockStandardPair.of_map_conj g ?_
  rw [qtwoW_of_edge _ hij, hg2, hE1, hg1 i (by simp), hg1 j (by simp)]
  exact hE2

theorem qtwo_adjA3_of_orb (hfacts : QTwoMemberFacts Bs X M (ggAutomizerJoin L Bs 𝒦) e)
    (hM : M = (ggCoxeterMatrixD m).reindex e')
    (h6 : ∀ i, Nat.card ↥(qtwoNode Bs (qtwoRefl e e') i) = 6) {i j k : Fin m}
    (hij : ggCoxeterMatrixD m i j = 3) (hjk : ggCoxeterMatrixD m j k = 3)
    (hik : ggCoxeterMatrixD m i k = 2) (horb : GGOrbAt X Bs e e' {i, j, k}) :
    ∃ θ : Su (GaloisField 2 2) 2 1 4 →* G,
      θ.range = qtwoW Bs (qtwoRefl e e') i j ⊔ qtwoW Bs (qtwoRefl e e') j k := by
  haveI : Finite ι := Finite.of_equiv (Fin m) e'
  obtain ⟨w, hw⟩ := horb
  have hwi : qtwoConjRefl e e' w i ∈ ggAutomizer X Bs := hw i (by simp)
  have hwj : qtwoConjRefl e e' w j ∈ ggAutomizer X Bs := hw j (by simp)
  have hwk : qtwoConjRefl e e' w k ∈ ggAutomizer X Bs := hw k (by simp)
  obtain ⟨g, hg1, hg2⟩ := qtwo_transport hfacts (T := {i, j, k}) hw
  have hne : i ≠ k := by
    rintro rfl
    have h1 : ggCoxeterMatrixD m i i = 1 := (ggCoxeterMatrixD m).diagonal i
    omega
  have hci : Nat.card ↥(ggRankOneIn X Bs (qtwoConjRefl e e' w i)) = 6 := by
    rw [← hg1 i (by simp), Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h6 i
  have hE1 := hfacts.2.1 _ hwi (conjRefl_mem_ggCoxRefl e e' w i) _ hwj
    (conjRefl_mem_ggCoxRefl e e' w j) (conjRefl_noncomm e e' hM w hij)
  have hE2 := hfacts.2.1 _ hwj (conjRefl_mem_ggCoxRefl e e' w j) _ hwk
    (conjRefl_mem_ggCoxRefl e e' w k) (conjRefl_noncomm e e' hM w hjk)
  obtain ⟨θ, hθ⟩ := hfacts.2.2.2.1 _ hwi (conjRefl_mem_ggCoxRefl e e' w i) _ hwj
    (conjRefl_mem_ggCoxRefl e e' w j) _ hwk (conjRefl_mem_ggCoxRefl e e' w k)
    (conjRefl_noncomm e e' hM w hij) (conjRefl_noncomm e e' hM w hjk)
    (conjRefl_comm e e' hM w hik) (conjRefl_ne e e' w hne) hci
  refine exists_su_four_hom_of_map_conj g ⟨θ, ?_⟩
  rw [qtwoW_of_edge _ hij, qtwoW_of_edge _ hjk, hg2, hg2, hE1, hE2]
  exact hθ

theorem qtwo_far2_of_orb (hfacts : QTwoMemberFacts Bs X M (ggAutomizerJoin L Bs 𝒦) e)
    (hM : M = (ggCoxeterMatrixD m).reindex e') {i k j l : Fin m}
    (hik : ggCoxeterMatrixD m i k = 3) (hjl : ggCoxeterMatrixD m j l = 3)
    (hij : ggCoxeterMatrixD m i j = 2) (hil : ggCoxeterMatrixD m i l = 2)
    (hkj : ggCoxeterMatrixD m k j = 2) (hkl : ggCoxeterMatrixD m k l = 2)
    (horb : GGOrbAt X Bs e e' {i, k, j, l}) :
    ∀ x ∈ qtwoW Bs (qtwoRefl e e') i k, ∀ y ∈ qtwoW Bs (qtwoRefl e e') j l, x * y = y * x := by
  haveI : Finite ι := Finite.of_equiv (Fin m) e'
  obtain ⟨w, hw⟩ := horb
  have hwi : qtwoConjRefl e e' w i ∈ ggAutomizer X Bs := hw i (by simp)
  have hwk : qtwoConjRefl e e' w k ∈ ggAutomizer X Bs := hw k (by simp)
  have hwj : qtwoConjRefl e e' w j ∈ ggAutomizer X Bs := hw j (by simp)
  have hwl : qtwoConjRefl e e' w l ∈ ggAutomizer X Bs := hw l (by simp)
  obtain ⟨g, hg1, hg2⟩ := qtwo_transport hfacts (T := {i, k, j, l}) hw
  have hE1 := hfacts.2.1 _ hwi (conjRefl_mem_ggCoxRefl e e' w i) _ hwk
    (conjRefl_mem_ggCoxRefl e e' w k) (conjRefl_noncomm e e' hM w hik)
  have hE2 := hfacts.2.1 _ hwj (conjRefl_mem_ggCoxRefl e e' w j) _ hwl
    (conjRefl_mem_ggCoxRefl e e' w l) (conjRefl_noncomm e e' hM w hjl)
  have hfar := hfacts.2.2.2.2 _ hwi (conjRefl_mem_ggCoxRefl e e' w i) _ hwk
    (conjRefl_mem_ggCoxRefl e e' w k) _ hwj (conjRefl_mem_ggCoxRefl e e' w j) _ hwl
    (conjRefl_mem_ggCoxRefl e e' w l) (conjRefl_noncomm e e' hM w hik)
    (conjRefl_noncomm e e' hM w hjl) (conjRefl_comm e e' hM w hij)
    (conjRefl_comm e e' hM w hil) (conjRefl_comm e e' hM w hkj) (conjRefl_comm e e' hM w hkl)
  refine (commute_map_conj_iff g).mp ?_
  rw [qtwoW_of_edge _ hik, qtwoW_of_edge _ hjl, hg2, hg2, hE1, hE2]
  exact hfar

end Cfg

end CFSG.StandardType.QTwo

end

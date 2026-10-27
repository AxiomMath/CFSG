module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProof
import CFSG.RankThree.PartTwo.Sec16.Item162Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] def Step163A7PassX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    WStarS4 A → TransOmegaThree A c →
    ∀ Y ∈ scriptY0Star A (lB A), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) →
    ∀ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a → La ≤ Y →
      Subgroup.zpowers a ≠ Subgroup.zpowers c →
      (∃ Q ∈ scriptQPi A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))
          (piOf 2), Q ≠ ⊥) →
      ∀ w ∈ Subgroup.normalizer (A : Set G),
        Subgroup.zpowers c = (Subgroup.zpowers a).map (MulAut.conj w).toMonoidHom →
          ∃ x ∈ xA A, QTwoNe A Y
            ((Y.map (MulAut.conj w).toMonoidHom).map (MulAut.conj x).toMonoidHom)

theorem step163A7_of_passX (h162 : Item162R) (h142 : Concl142R) (h153 : Item153MainR)
    (hP : Step163A7PassX) : Step163A7 := by
  intro G _ _ A c L h hΩ h7 hW hT Y hY hpt
  obtain ⟨a, La, ha, hLa, hLaY⟩ := hpt
  refine ⟨fun φ => ?_⟩
  have hsc := Step163Alt.sectionCentralizer_eq_of_config h h7 hT hY φ ha hLa hLaY
  obtain ⟨v₁, hv₁, hav₁⟩ := hT.2 _ ha
  obtain ⟨F, hF, hFa⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hT.1]; norm_num)
    (Subgroup.zpowers a)
  obtain ⟨v₂, hv₂, hFv₂⟩ := hT.2 F hF
  set c' := v₂ * c * v₂⁻¹ with hc'
  have hFc' : F = Subgroup.zpowers c' := by
    rw [hFv₂, MonoidHom.map_zpowers]
    rfl
  have hc'Ω : Subgroup.zpowers c' ∈ omegaA A := hFc' ▸ hF
  set L' := L.map (MulAut.conj v₂).toMonoidHom with hL'
  have hL'mem : L' ∈ lA A c' := (map_conj_mem_lA_iff hv₂).mpr h.mem_lA
  have h' : Sec15R G A c' L' := sec15R_of_point h hc'Ω hL'mem
  have h7' : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) :=
    nonempty_a7_of_map_conj rfl h7
  have hcv₂ : Subgroup.zpowers c' = (Subgroup.zpowers c).map (MulAut.conj v₂).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hT' : TransOmegaThree A c' := transOmegaThree_of_conj hv₂ hT hcv₂
  set w := v₂ * v₁⁻¹ with hw
  have hwN : w ∈ Subgroup.normalizer (A : Set G) := mul_mem hv₂ (inv_mem hv₁)
  have hcw : Subgroup.zpowers c' = (Subgroup.zpowers a).map (MulAut.conj w).toMonoidHom := by
    rw [hav₁, Late.map_conj_map_conj, hw, inv_mul_cancel_right, ← hcv₂]
  have hac' : Subgroup.zpowers a ≠ Subgroup.zpowers c' := fun hac => hFa (hFc'.trans hac.symm)
  have hClaim := step163A7Claim_of h142 h153 G A c' L' h' h7' hW hT' Y hY ⟨φ⟩ a La ha hLa
    hLaY hac'
  obtain ⟨x, hx, hQ'⟩ := hP G A c' L' h' h7' hW hT' Y hY ⟨φ⟩ a La ha hLa hLaY hac' hClaim w
    hwN hcw
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hx
  have hxN : x ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hxC
  have hYwx : (Y.map (MulAut.conj w).toMonoidHom).map (MulAut.conj x).toMonoidHom ∈
      scriptY0Star A (lB A) :=
    map_conj_mem_scriptY0Star hxN (map_conj_mem_scriptY0Star hwN hY)
  obtain ⟨x', hx', hxY⟩ := h162 G A c L h Y hY _ hYwx hQ'
  have hx'C : x' ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hx'
  have hx'N : x' ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hx'C
  have hscA : Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) ⊆ (A : Set G) :=
    fun t ht => ht.1
  have hwA : (MulAut.conj w) '' Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) ⊆
      (A : Set G) := fun t ht => by
    obtain ⟨s, hs, rfl⟩ := ht
    exact (Subgroup.mem_normalizer_iff.mp hwN s).mp (hscA hs)
  have hxA : (MulAut.conj x) '' ((MulAut.conj w) ''
      Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y)) ⊆ (A : Set G) := by
    rw [Step163Alt.image_conj_eq_of_mem_centralizer hxC hwA]
    exact hwA
  have key : (Subgroup.zpowers a : Set G) = (Subgroup.zpowers c' : Set G) := by
    rw [← hsc]
    conv_lhs => rw [hxY]
    rw [Step163Alt.sectionCentralizer_map_conj hx'N, Step163Alt.sectionCentralizer_map_conj hxN,
      Step163Alt.sectionCentralizer_map_conj hwN,
      Step163Alt.image_conj_eq_of_mem_centralizer hx'C hxA,
      Step163Alt.image_conj_eq_of_mem_centralizer hxC hwA, hsc, hcw]
    ext t
    simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  exact hac' (SetLike.coe_injective key)

end CFSG.RankThree.PartTwo.Sec16

module

public import CFSG.RankThree.PartTwo.Sec10.Item1014Proof
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.RankThree.PartTwo.Sec10.Item104

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Sec10X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      ∃ X ∈ thetaComponentsAt 3 d,
        ((Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* alternatingGroup (Fin 7)) ∨
            Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
            Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
            Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
            ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
              (Sec4.IsoLThreePi (X ⧸ aschbacherSolvableCore 3 X) p e ∨
                Sec4.IsSLThreePiAt (X ⧸ aschbacherSolvableCore 3 X) (p ^ e))) ∨
          Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField 3 3))) ∧
        ∃ U ∈ invariantPiSubgroups X (Subgroup.zpowers c) (piOf 2), U ≠ ⊥

namespace Sec10X

theorem not_nonempty_mulEquiv_of_mem_thetaComponentsAt (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R : Subgroup G} (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 d) :
    ¬ Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField 3 3)) := by
  rintro ⟨eX⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, R', h'⟩ := Item1014Proof.sec10Std_of_mem_thetaComponentsAt h45 h97 h hdL hX eX
  have hdo : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  obtain ⟨hΩ, ⟨e, heRL, hW, hcl⟩, -, -⟩ := rank3II_10_2 h45 h97 G A c L a R h
  have hD := commutator_commutator_omega_eq h hdL hdo hΩ heRL hW hcl
  obtain ⟨x, hxX, hxo, -⟩ := exists_inf_eq_zpowers h97 h'.toHyp91
  obtain ⟨hΩ', ⟨e', he'RL, hW', hcl'⟩, -, -⟩ := rank3II_10_2 h45 h97 G A d X y R' h'
  have hD' := commutator_commutator_omega_eq h' hxX hxo hΩ' he'RL hW' hcl'
  have hRN : R ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := fun r hr =>
    mem_normalizer_zpowers_of_conj_mem (by
      rw [h.d_commute_of_mem_R h45 hdL hr, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers d)
  obtain ⟨Q, hQ⟩ := (h.isPGroup_R.comap_subtype
    (K := Subgroup.normalizer (Subgroup.zpowers d : Set G))).exists_le_sylow
  have hS : IsSylowOf 3 ((Q : Subgroup (Subgroup.normalizer (Subgroup.zpowers d : Set G))).map
      (Subgroup.normalizer (Subgroup.zpowers d : Set G)).subtype)
      (Subgroup.normalizer (Subgroup.zpowers d : Set G)) := ⟨Q, rfl⟩
  obtain ⟨k, -, hk⟩ := IsSylowOf.exists_mem_conj h'.isSylowOf hS
  have hkR : ∀ r ∈ R, k⁻¹ * r * k ∈ R' := fun r hr =>
    (hk r).mp ⟨⟨r, hRN hr⟩, hQ (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hle := Item1014Proof.map_conj_commutator_omega_le hkR
  rw [hD, hD'] at hle
  have hdx : k⁻¹ * d * k⁻¹⁻¹ ∈ Subgroup.zpowers x := hle ⟨d, Subgroup.mem_zpowers d, rfl⟩
  have hxle : Subgroup.zpowers x ≤ X := by
    rw [← hxX]
    exact inf_le_right
  exact rank3II_10_3 h45 h97 G A d X y R' h' k⁻¹ (hxle hdx)

end Sec10X

section List

theorem sec10Never_of_sec10X (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h10X : Sec10X) :
    Sec10Never := by
  intro G _ _ A c L a R h
  obtain ⟨d, hdL, -, -⟩ := exists_inf_eq_zpowers h97 h.toHyp91
  obtain ⟨X, hX, hcase, U, hU, hU1⟩ := h10X G A c L a R h d hdL
  rcases hcase with hlist | h27
  · exact Item1015Proof.false_of_listFacts h45 h97 h hdL hX
      (Item1015Proof.listFacts_of_list hlist) hU hU1
  · exact Sec10X.not_nonempty_mulEquiv_of_mem_thetaComponentsAt h45 h97 h hdL hX h27

end List

end CFSG.RankThree.PartTwo.Sec10

module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGOutsideInndiag {L' : Type} [Group L'] (J₁ : Subgroup L') (a : MulAut L') : Prop :=
  (∀ l ∈ J₁, a l ∈ J₁) ∧
    GGMarkingAll (K := ↥J₁) fun _ _ _ I' _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I',
        LargeEvenInduces θ (fun l l' : ↥J₁ => (l' : L') = a l) φ

theorem ggOutsideInndiag_ggGamma_of_le {G : Type} [Group G] {Bs K L J : Subgroup G}
    (hNK : Bs ≤ Subgroup.normalizer (K : Set G)) (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hJK : J ≤ K) (hJL : J ≤ L) (b : Bs)
    (h : GGOutsideInndiag (J.subgroupOf K) (ggGamma K hNK b)) :
    GGOutsideInndiag (J.subgroupOf L) (ggGamma L hNL b) := by
  obtain ⟨hinv, hall⟩ := h
  let e : ↥(J.subgroupOf K) ≃* ↥(J.subgroupOf L) :=
    (Subgroup.subgroupOfEquivOfLe hJK).trans (Subgroup.subgroupOfEquivOfLe hJL).symm
  have he : ∀ l : ↥(J.subgroupOf K), (((e l : ↥(J.subgroupOf L)) : ↥L) : G) = ((l : ↥K) : G) :=
    fun _ => rfl
  refine ⟨fun l hl => ?_, ggMarkingAll_congr e (fun lab R _ I F θ hQ => ?_) hall⟩
  · have hlJ : (l : G) ∈ J := Subgroup.mem_subgroupOf.mp hl
    have h1 := Subgroup.mem_subgroupOf.mp
      (hinv ⟨(l : G), hJK hlJ⟩ (Subgroup.mem_subgroupOf.mpr hlJ))
    rw [ggGamma_coe] at h1
    rw [Subgroup.mem_subgroupOf, ggGamma_coe]
    exact h1
  · rintro ⟨φ, hφ, hind⟩
    have key := largeEvenInduces_congr_equiv e θ
      (fun l l' : ↥(J.subgroupOf K) => (l' : ↥K) = ggGamma K hNK b l)
      (fun l l' : ↥(J.subgroupOf L) => (l' : ↥L) = ggGamma L hNL b l)
      (fun l l' => by simp only [Subtype.ext_iff, ggGamma_coe, he]) φ
    exact hQ ⟨φ, hφ, key.2 hind⟩

end CFSG.StandardType

end

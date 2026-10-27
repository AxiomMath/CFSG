module

public import CFSG.Quasithin.Recognition.F112RShapes
public import CFSG.Quasithin.EmptyFaithful.Insp7RedA
public import CFSG.Quasithin.EmptyFaithful.S143UE

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

theorem exists_embedding_of_ker {G : Type} [Group G] {H L : Subgroup G} {N : Subgroup ↥H}
    [N.Normal] (hLN : H ≤ Subgroup.normalizer (L : Set G))
    (hker : ∀ k : ↥H, (k : G) ∈ Subgroup.centralizer (L : Set G) ↔ k ∈ N) :
    ∃ ρ : (↥H ⧸ N) →* MulAut ↥L, Function.Injective ρ ∧
      ∀ k : ↥H, ρ (QuotientGroup.mk k) = Insp7.actOn hLN k := by
  have hle : N ≤ (Insp7.actOn hLN).ker := fun n hn =>
    (Insp7.mem_ker_actOn hLN n).mpr ((hker n).mpr hn)
  refine ⟨QuotientGroup.lift N (Insp7.actOn hLN) hle, ?_, fun k => rfl⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : Insp7.actOn hLN k = 1 := hq
  have h2 : k ∈ N := (hker k).mp ((Insp7.mem_ker_actOn hLN k).mp h1)
  exact (QuotientGroup.eq_one_iff k).mpr h2

theorem isZ4StarSL23_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : IsZ4StarSL23 P) : IsZ4StarSL23 Q := by
  obtain ⟨hcard, A, B, hAB, hA4, hAc, ⟨eB⟩⟩ := h
  refine ⟨by rw [← Nat.card_congr e.toEquiv, hcard], A.map e.toMonoidHom, B.map e.toMonoidHom,
    isCommutingGeneration_map e hAB, ?_, ?_, ⟨(e.subgroupMap B).symm.trans eB⟩⟩
  · exact (Nat.card_congr (e.subgroupMap A).toEquiv).symm.trans hA4
  · exact ((e.subgroupMap A).isCyclic).mp hAc

theorem exists_mulEquiv_map {A B : Type*} [Group A] [Group B] (K : Subgroup A) (φ : A →* B)
    (h : K ⊓ φ.ker = ⊥) : Nonempty (↥K ≃* ↥(K.map φ)) := by
  refine ⟨MulEquiv.ofBijective (φ.subgroupMap K) ⟨?_, MonoidHom.subgroupMap_surjective φ K⟩⟩
  rw [injective_iff_map_eq_one]
  intro k hk
  have h1 : φ k = 1 := congrArg Subtype.val hk
  have h2 : (k : A) ∈ K ⊓ φ.ker := ⟨k.2, h1⟩
  rw [h, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

end InspW2

end S143

end CFSG.Quasithin

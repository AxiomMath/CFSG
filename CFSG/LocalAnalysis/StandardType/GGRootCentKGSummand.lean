module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGPiece
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

open scoped Pointwise commutatorElement

theorem exists_mul_mul_of_mem_sup_sup {G : Type*} [Group G] {Q S T : Subgroup G}
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hST : S ≤ Subgroup.centralizer (T : Set G)) {x : G} (hx : x ∈ Q ⊔ (S ⊔ T)) :
    ∃ q ∈ Q, ∃ s ∈ S, ∃ t ∈ T, x = q * s * t := by
  have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.le_centralizer_iff.mp hST).trans (Subgroup.centralizer_le_normalizer (S : Set G))
  have hQST : S ⊔ T ≤ Subgroup.normalizer (Q : Set G) := sup_le hSQ hTQ
  have hx' : x ∈ (↑(Q ⊔ (S ⊔ T)) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q (S ⊔ T) hQST] at hx'
  obtain ⟨q, hq, y, hy, rfl⟩ := hx'
  have hy' : y ∈ (↑(S ⊔ T) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left S T hTS] at hy'
  obtain ⟨s, hs, t, ht, rfl⟩ := hy'
  exact ⟨q, hq, s, hs, t, ht, (mul_assoc q s t).symm⟩

theorem ggRCSKGPiece_of_summand_normal {G : Type} [Group G] [Finite G]
    {C₀ E Q L N M : Subgroup G} (hC₀ : C₀ = Q ⊔ (N ⊔ M)) (hQ : pCoreOf 2 C₀ = Q)
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G)) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hNM : N ≤ Subgroup.centralizer (M : Set G)) (hQN : Q ⊓ N = ⊥)
    (hperf : ⁅Q ⊔ L, Q ⊔ L⁆ = Q ⊔ L) (hLq : CFSG.Assembly.IsQuasisimple ↥L)
    (hLm : LargeEvenMarking ↥L (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ {α : MulAut ↥L | ∃ t ∈ N, ∀ y : ↥L, ((α y : ↥L) : G) = t⁻¹ * (y : G) * t},
        ∃ φ ∈ I, ∀ y : ↥L, φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))))
    (hE : E ≤ C₀) : GGRCSKGPiece C₀ E (Q ⊔ L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := hLN.trans hNQ
  have hQL : Q ⊓ L = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left Q hLN).trans (le_of_eq hQN))
  have hJC : Q ⊔ L ≤ C₀ := by
    rw [hC₀]
    exact sup_le le_sup_left (hLN.trans (le_sup_left.trans le_sup_right))
  have hQJ : Q ≤ Subgroup.normalizer ((Q ⊔ L : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hNJ : N ≤ Subgroup.normalizer ((Q ⊔ L : Subgroup G) : Set G) := by
    intro n hn
    exact Subgroup.inf_normalizer_le_normalizer_sup Q L ⟨hNQ hn, hNL hn⟩
  have hML : M ≤ Subgroup.centralizer (L : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hNM (hLN hl)) m hm).symm
  have hMJ : M ≤ Subgroup.normalizer ((Q ⊔ L : Subgroup G) : Set G) := by
    intro m hm
    exact Subgroup.inf_normalizer_le_normalizer_sup Q L
      ⟨hMQ hm, Subgroup.centralizer_le_normalizer (L : Set G) (hML hm)⟩
  have hC₀N : C₀ ≤ Subgroup.normalizer ((Q ⊔ L : Subgroup G) : Set G) := by
    rw [hC₀]
    exact sup_le hQJ (sup_le hNJ hMJ)
  have hperfQ : Q ≤ ⁅Q ⊔ L, Q⁆ := by
    have hQ2grp : IsPGroup 2 Q :=
      hQ ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C₀
    have h := le_commutator_sup_of_perfect (p := 2) (Q := Q) (L := L) hQ2grp hLQ hperf
    rwa [hQL, sup_bot_eq] at h
  have hQ1 : pCoreOf 2 C₀ ≤
      (Q ⊔ L) ⊔ (pCoreOf 2 C₀ ⊓ Subgroup.centralizer (pCoreOf 2 C₀ : Set G)) := by
    rw [hQ]
    exact le_sup_left.trans le_sup_left
  have hQ2 : pCoreOf 2 C₀ ≤
      ⁅Q ⊔ L, pCoreOf 2 C₀⁆ ⊔
        (pCoreOf 2 C₀ ⊓ Subgroup.centralizer (pCoreOf 2 C₀ : Set G)) := by
    rw [hQ]
    exact hperfQ.trans le_sup_left
  have hEJ : E ≤ Subgroup.normalizer ((Q ⊔ L : Subgroup G) : Set G) := hE.trans hC₀N
  obtain ⟨π, hπsurj, hπker, hπ⟩ := exists_sup_proj (Q := Q) (L := L) hLQ hQL
  have hker : π.ker = (pCoreOf 2 C₀).subgroupOf (Q ⊔ L) := by
    rw [hQ]
    exact hπker
  let 𝒜 : Set (MulAut ↥L) :=
    {α : MulAut ↥L | ∃ t ∈ N, ∀ y : ↥L, ((α y : ↥L) : G) = t⁻¹ * (y : G) * t}
  have hLm𝒜 : LargeEvenMarking ↥L (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ 𝒜, ∃ φ ∈ I, ∀ y : ↥L,
        φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) := hLm
  refine ggRCSKGPiece_of_marking hJC hC₀N hperf hQ1 hQ2 hEJ hLq 𝒜 hLm𝒜 π hπsurj hker ?_
  intro ε hε
  have hε' : ε ∈ Q ⊔ (N ⊔ M) := hC₀ ▸ hE hε
  obtain ⟨q, hq, t, ht, m, hm, hεqtm⟩ :=
    exists_mul_mul_of_mem_sup_sup (Q := Q) (S := N) (T := M) hNQ hMQ hNM hε'
  have htQ : t ∈ Subgroup.normalizer (Q : Set G) := hNQ ht
  have htL : t ∈ Subgroup.normalizer (L : Set G) := hNL ht
  have hmQ : m ∈ Subgroup.normalizer (Q : Set G) := hMQ hm
  have hmL : m ∈ Subgroup.centralizer (L : Set G) := hML hm
  let α : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨t⁻¹, Subgroup.inv_mem _ htL⟩
  have hαcoe : ∀ y : ↥L, ((α y : ↥L) : G) = t⁻¹ * (y : G) * t := by
    intro y
    simpa [α] using
      Subgroup.normalizerMonoidHom_apply_apply_coe L
        ⟨t⁻¹, Subgroup.inv_mem _ htL⟩ y
  have hαA : α ∈ 𝒜 := ⟨t, ht, hαcoe⟩
  refine ⟨α, hαA, ?_⟩
  intro s s' hs
  have hconj := proj_conj_of_eq_mul (Q := Q) (L := L) π hπ hLQ hq htQ htL hmQ hmL hεqtm s s' hs
  apply Subtype.ext
  rw [hαcoe (π s)]
  exact hconj

theorem ggRCSKGPiece_of_summand {G : Type} [Group G] [Finite G] {C₀ E Q L M : Subgroup G}
    (hC₀ : C₀ = Q ⊔ (L ⊔ M)) (hQ : pCoreOf 2 C₀ = Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hLM : L ≤ Subgroup.centralizer (M : Set G)) (hQL : Q ⊓ L = ⊥)
    (hperf : ⁅Q ⊔ L, Q ⊔ L⁆ = Q ⊔ L) (hLq : CFSG.Assembly.IsQuasisimple ↥L)
    (hLm : LargeEvenMarking ↥L
      (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I))
    (hE : E ≤ C₀) : GGRCSKGPiece C₀ E (Q ⊔ L) := by
  have hInn : LargeEvenMarking ↥L (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ LargeEvenInnSet ↥L, ∃ φ ∈ I, ∀ y : ↥L,
        φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) :=
    largeEvenMarking_innAct hLm
  have hsub : {α : MulAut ↥L | ∃ t ∈ L, ∀ y : ↥L, ((α y : ↥L) : G) = t⁻¹ * (y : G) * t} ⊆
      LargeEvenInnSet ↥L := by
    rintro α ⟨t, ht, hα⟩
    refine ⟨(⟨t, ht⟩ : ↥L)⁻¹, ?_⟩
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    simp [MulAut.conj_apply, hα y]
  have hLm' : LargeEvenMarking ↥L (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ {α : MulAut ↥L | ∃ t ∈ L, ∀ y : ↥L, ((α y : ↥L) : G) = t⁻¹ * (y : G) * t},
        ∃ φ ∈ I, ∀ y : ↥L,
          φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) := by
    refine largeEvenMarking_mono ?_ hInn
    intro lab R _ I F θ hθ
    exact ⟨hθ.1, fun α hα => hθ.2 α (hsub hα)⟩
  exact ggRCSKGPiece_of_summand_normal hC₀ hQ le_rfl Subgroup.le_normalizer hLQ hMQ hLM hQL
    hperf hLq hLm' hE

end CFSG.StandardType

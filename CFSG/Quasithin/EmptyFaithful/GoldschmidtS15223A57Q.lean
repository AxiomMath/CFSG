module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223QJ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_inf_normalizer {I S X : Subgroup G} (hSI : S ≤ I)
    (hN : ((Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I).Normal) :
    S ≤ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ s ∈ S, ∀ y : G, y ∈ S ⊓ Subgroup.normalizer (X : Set G) →
      s * y * s⁻¹ ∈ S ⊓ Subgroup.normalizer (X : Set G) := by
    intro s hs y hy
    refine ⟨S.mul_mem (S.mul_mem hs hy.1) (S.inv_mem hs), ?_⟩
    have hyI : (⟨y, hSI hy.1⟩ : ↥I) ∈ (Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I :=
      Subgroup.mem_subgroupOf.mpr ⟨hy.2, hSI hy.1⟩
    have := hN.conj_mem _ hyI ⟨s, hSI hs⟩
    have h2 := (Subgroup.mem_subgroupOf.mp this).1
    simpa using h2
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key s hs y, fun h => ?_⟩
  have := key s⁻¹ (S.inv_mem hs) _ h
  simpa [mul_assoc] using this

theorem isSylowTwoOf_inf_normalizer {I S X : Subgroup G} (hS : IsSylowTwoOf S I)
    (hN : ((Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I).Normal) :
    IsSylowTwoOf (S ⊓ Subgroup.normalizer (X : Set G)) (Subgroup.normalizer (X : Set G) ⊓ I) := by
  have hS' : IsSylowIn 2 S I := ⟨hS.1, hS.2.1, hS.2.2⟩
  have h := hS'.inf_normal (inf_le_right : Subgroup.normalizer (X : Set G) ⊓ I ≤ I) hN
  have e : S ⊓ (Subgroup.normalizer (X : Set G) ⊓ I) = S ⊓ Subgroup.normalizer (X : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hS.1 h.1⟩⟩
  rw [e] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

structure BlkCfg (I S K X Mc : Subgroup G) : Prop where
  sylow : IsSylowTwoOf S I
  K_le : K ≤ I
  S_normK : S ≤ Subgroup.normalizer (K : Set G)
  K_normX : K ≤ Subgroup.normalizer (X : Set G)
  K_Mc : K ≤ Mc
  S_Mc : S ≤ Mc
  normal : ((Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I).Normal
  sylowX : IsSylowTwoOf (S ⊓ X) X

namespace BlkCfg

variable {I S K X Mc : Subgroup G} (c : BlkCfg I S K X Mc)
include c

omit [Finite G] in
theorem S₁_normal : S ≤ Subgroup.normalizer
    ((S ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf_normalizer c.sylow.1 c.normal

omit [Finite G] in
theorem K_le_N : K ≤ Subgroup.normalizer (X : Set G) ⊓ I := le_inf c.K_normX c.K_le

theorem sylow_N : IsSylowTwoOf (S ⊓ Subgroup.normalizer (X : Set G))
    (Subgroup.normalizer (X : Set G) ⊓ I) := isSylowTwoOf_inf_normalizer c.sylow c.normal

omit [Finite G] in
theorem S_normalizer_sup : S ≤ Subgroup.normalizer
    ((K ⊔ (S ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) := fun _ hs =>
  Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨c.S_normK hs, c.S₁_normal hs⟩

theorem pCoreOf_sup_le_S₁ : pCoreOf 2 (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G))) ≤
    S ⊓ Subgroup.normalizer (X : Set G) :=
  pCoreOf_sup_le c.sylow_N c.K_le_N

theorem pCoreOf_sup_inf_le : pCoreOf 2 (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G))) ≤
    pCoreOf 2 (K ⊔ S) := by
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (sup_le_sup_left inf_le_left _))
    (sup_le ?_ ?_) (pCoreOf_isPGroup 2 _)
  · exact le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  · exact c.S_normalizer_sup.trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem pCoreOf_le_pCoreOf_sup_inf : pCoreOf 2 X ≤
    pCoreOf 2 (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G))) := by
  have h1 : pCoreOf 2 X ≤ S ⊓ X := pCoreOf_le_of_isSylowTwoOf c.sylowX
  have h2 : S ⊓ X ≤ S ⊓ Subgroup.normalizer (X : Set G) :=
    inf_le_inf_left _ Subgroup.le_normalizer
  refine le_pCoreOf_of_le_normalizer 2 ((h1.trans h2).trans le_sup_right) (sup_le ?_ ?_)
    (pCoreOf_isPGroup 2 X)
  · exact c.K_normX.trans (normalizer_le_normalizer_pCoreOf 2 X)
  · exact inf_le_right.trans (normalizer_le_normalizer_pCoreOf 2 X)

theorem inf_normalizer_le_pCoreOf_sup_inf : pCoreOf 2 (K ⊔ S) ⊓ Subgroup.normalizer (X : Set G) ≤
    pCoreOf 2 (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G))) := by
  have hQS : pCoreOf 2 (K ⊔ S) ≤ S := pCoreOf_sup_le c.sylow c.K_le
  have hQ2 : IsPGroup 2 (pCoreOf 2 (K ⊔ S) ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) :=
    (pCoreOf_isPGroup 2 _).to_inf_left
  refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ hQ2
  · exact (inf_le_inf_right _ hQS).trans le_sup_right
  · refine sup_le (fun k hk => ?_) (fun s hs => ?_)
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ S)) hk,
          Subgroup.le_normalizer (c.K_normX hk)⟩
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_sup_right.trans (le_normalizer_pCoreOf 2 (K ⊔ S)) hs.1, Subgroup.le_normalizer hs.2⟩

omit [Finite G] in
theorem sylowX₁ : IsSylowTwoOf (S ⊓ Subgroup.normalizer (X : Set G) ⊓ X) X := by
  have : S ⊓ Subgroup.normalizer (X : Set G) ⊓ X = S ⊓ X := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.le_normalizer h.2⟩, h.2⟩⟩
  rw [this]
  exact c.sylowX

theorem pCoreOf_sup_le_pCoreOf_sup_inf : pCoreOf 2 (X ⊔ pCoreOf 2
      (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G)))) ≤
    pCoreOf 2 (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G))) :=
  pCoreOf_sup_le_Q c.sylow_N c.K_le_N c.K_normX inf_le_right c.K_Mc (inf_le_left.trans c.S_Mc)
    c.sylowX₁

end BlkCfg

end S15223

end CFSG.Quasithin

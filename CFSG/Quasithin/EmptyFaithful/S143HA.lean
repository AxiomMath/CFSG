module

public import CFSG.Quasithin.EmptyFaithful.S143GD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

@[expose] def Lemma14319Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl19a T M → IsA6Block (kOf T M A) A

@[expose] def Lemma14319TenFiveSixSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl19a T M → IsA6Block (kOf T M A) A →
      Subgroup.centralizer (kOf T M A : Set G) = ⊥ ∧
        Subgroup.normalizer (kOf T M A : Set G) = kOf T M A ⊔ dOf T M ∧
        (∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X)) ∧
        (Nonempty (↥(dOf T M) ≃* DihedralGroup 4) ↔
          ((kOf T M A).relIndex (Subgroup.normalizer (kOf T M A : Set G)) = 4 ∧
            A < Subgroup.centralizer (A : Set G))) ∧
        Subgroup.normalizer (A : Set G) = Subgroup.normalizer (kOf T M A : Set G)

section Eight

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

omit [Finite G] c in
theorem card_kOf_of_isA6Block {A : Subgroup G} (hA : Nat.card A = 16) (hK : IsA6Block (kOf T M A) A) :
    Nat.card ↥(kOf T M A) = 5760 := by
  obtain ⟨-, hAK, φ, -, -⟩ := hK
  have h1 : Nat.card ↥(kOf T M A) = Nat.card (OTwoQuot (kOf T M A)) *
      Nat.card (CFSG.Open.pCore 2 ↥(kOf T M A)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥(kOf T M A))
  have h2 : Nat.card (OTwoQuot (kOf T M A)) = 360 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  have h3 : Nat.card (CFSG.Open.pCore 2 ↥(kOf T M A)) = 16 := by
    have : Nat.card (pCoreOf 2 (kOf T M A)) = Nat.card (CFSG.Open.pCore 2 ↥(kOf T M A)) :=
      Subgroup.card_map_of_injective (kOf T M A).subtype_injective
    rw [← this, ← hAK]
    exact hA
  rw [h1, h2, h3]

theorem Counter.isSylowTwoOf_rOf_sup_uOfL22 {A : Subgroup G} {t : G} (hb : Concl18b T M A t)
    (hK : IsA6Block (kOf T M A) A) : IsSylowTwoOf (rOf T M ⊔ uOfL22 T M) (kOf T M A) := by
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq hb
  have hle := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hKcard := card_kOf_of_isA6Block (c.card_Ac hrW hrV hr2) hK
  have hRT : rOf T M ≤ T := le_sup_left.trans (rq_le_of_hyp c.h1281)
  have hUT : uOfL22 T M ≤ T := uOfL22_le_T_of_hyp c.h1281
  have hRUT : rOf T M ⊔ uOfL22 T M ≤ T := sup_le hRT hUT
  have hUR : uOfL22 T M ≤ Subgroup.normalizer (rOf T M : Set G) :=
    hUT.trans (c.hyp.m_max.1.2.trans (M_le_normalizer_rOf c))
  have hRU : rOf T M ⊓ uOfL22 T M = Hyp1281Two.wOfU T M := by
    apply le_antisymm
    · intro x hx
      have : x ∈ rOf T M ⊓ qOf T := ⟨hx.1, uOfL22_le_qOf c hx.2⟩
      rwa [rOf_inf_qOf c] at this
    · exact le_inf (fun w hw => c.mem_rOf_of_mem_wOfU hw) (Hyp1281Two.wOfU_le_uOfL22 T M)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hUR
  have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
  rw [hRU, hW, card_rOf c, c.c15.q8sq.1] at hprod
  have hRUcard : Nat.card ↥(rOf T M ⊔ uOfL22 T M) = 128 := by omega
  refine ⟨hle, c.hyp.sylow.1.to_le hRUT, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (rOf T M ⊔ uOfL22 T M) (kOf T M (c.Ac hrW hrV hr2))
  rw [inf_eq_left.mpr hle, hRUcard, hKcard] at h1
  have h2 : (rOf T M ⊔ uOfL22 T M).relIndex (kOf T M (c.Ac hrW hrV hr2)) = 45 := by omega
  change ¬ 2 ∣ (rOf T M ⊔ uOfL22 T M).relIndex (kOf T M (c.Ac hrW hrV hr2))
  rw [h2]
  decide

end Eight

end S143

end CFSG.Quasithin

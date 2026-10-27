module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32e

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open CFSG.Quasithin S126 L1233 Equiv

section Case3

variable {Q : Type} [Group Q]

theorem eq_bot_or_eq_of_isSubnormal {P N : Subgroup Q} (h : IsSubnormal P N) :
    IsSimpleGroup ↥N → P = ⊥ ∨ P = N := by
  induction h with
  | refl => intro _; right; rfl
  | step hle hn hsub ih =>
    intro hs
    rcases ih hs with hM | hM
    · left
      exact le_bot_iff.1 (hM ▸ hle)
    · subst hM
      rcases hn.eq_bot_or_eq_top with h0 | h0
      · left
        rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hle] at h0
        exact h0
      · right
        exact le_antisymm hle ((Subgroup.subgroupOf_eq_top).1 h0)

theorem le_alt_prod_bot {P : Subgroup (Perm (Fin 5) × Perm (Fin 3))} (hP : ⁅P, P⁆ = P) :
    P ≤ (alternatingGroup (Fin 5)).prod ⊥ := by
  have h1 : ⁅(⊤ : Subgroup (Perm (Fin 5) × Perm (Fin 3))), ⊤⁆ ≤
      (alternatingGroup (Fin 5)).prod (alternatingGroup (Fin 3)) := by
    rw [← Subgroup.top_prod_top, Subgroup.commutator_prod_prod]
    exact Subgroup.prod_mono alternatingGroup.commutator_perm_le alternatingGroup.commutator_perm_le
  have hA3 : ⁅alternatingGroup (Fin 3), alternatingGroup (Fin 3)⁆ = ⊥ := by
    have := alternatingGroup.isMulCommutative_of_card_le_three (α := Fin 3) (by simp)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (this.is_comm.comm (⟨y, hy⟩ : ↥(alternatingGroup (Fin 3))) ⟨x, hx⟩)
  have h2 : ⁅(alternatingGroup (Fin 5)).prod (alternatingGroup (Fin 3)),
      (alternatingGroup (Fin 5)).prod (alternatingGroup (Fin 3))⁆ ≤
      (alternatingGroup (Fin 5)).prod ⊥ := by
    rw [Subgroup.commutator_prod_prod, hA3]
    exact Subgroup.prod_mono (Subgroup.commutator_le_left _ _) le_rfl
  calc P = ⁅⁅P, P⁆, ⁅P, P⁆⁆ := by rw [hP, hP]
    _ ≤ ⁅⁅(⊤ : Subgroup (Perm (Fin 5) × Perm (Fin 3))), ⊤⁆,
        ⁅(⊤ : Subgroup (Perm (Fin 5) × Perm (Fin 3))), ⊤⁆⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
        (Subgroup.commutator_mono le_top le_top)
    _ ≤ _ := (Subgroup.commutator_mono h1 h1).trans h2

noncomputable def altProdBotEquiv :
    ↥((alternatingGroup (Fin 5)).prod (⊥ : Subgroup (Perm (Fin 3)))) ≃*
      ↥(alternatingGroup (Fin 5)) :=
  (Subgroup.prodEquiv _ _).trans (MulEquiv.prodUnique)

end Case3

variable {G : Type} [Group G] [Finite G]

theorem alt5_of_case3 {H K : Subgroup G} (hK : K ∈ cComp H)
    (e : S126.HStar H ≃* Perm (Fin 5) × Perm (Fin 3)) :
    Nonempty (↥(S126.star H K) ≃* alternatingGroup (Fin 5)) := by
  have hC := cComp_map_mulEquiv e (star_mem_cComp hK)
  rw [Subgroup.map_top_of_surjective _ e.surjective] at hC
  set P := (S126.star H K).map e.toMonoidHom with hP
  have hPN := le_alt_prod_bot (perfect_of_mem_cComp hC)
  have hsub : IsSubnormal P ((alternatingGroup (Fin 5)).prod ⊥) :=
    A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hC) hPN le_top
  have hA5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥((alternatingGroup (Fin 5)).prod (⊥ : Subgroup (Perm (Fin 3)))) :=
    altProdBotEquiv.isSimpleGroup
  rcases eq_bot_or_eq_of_isSubnormal hsub hs with h0 | h0
  · exact absurd h0 (ne_bot_of_mem_cComp hC)
  · exact ⟨(((S126.star H K).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr h0)).trans altProdBotEquiv⟩

theorem lemma12_6_32_of (h30 : Lemma12_6_30) (h31 : Lemma12_6_31) (h1262 : Theorem12_6_2)
    (hcl : Claim12_6_32) : Lemma12_6_32 := by
  intro G _ _ T L V _ F hH hZ H K hIs
  have h918 := ((h30 G T L V F hH hZ).2 H K hIs).2.2
  rcases h31 G T L V F hH hZ H K hIs with h1 | h2 | h3
  · exact (false_of_case1 hcl h1262 F hH hZ hIs h918 h1).elim
  · exact h2.2.1
  · obtain ⟨e⟩ := h3.1
    exact alt5_of_case3 h918.K_cComp e

end CFSG.Quasithin.H13.L1232

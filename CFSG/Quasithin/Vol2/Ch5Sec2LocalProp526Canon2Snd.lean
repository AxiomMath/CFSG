module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34U4Vertex
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526SndC
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526SndD
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526SndE

public section

namespace CFSG.Quasithin.H13

section Defs

variable {G : Type} [Group G]

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def F112E6ExtC (L1 L2 S : Subgroup G) : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧
    IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) ∧
    IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
    IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 f

end Defs

namespace Sec526

section Entry

variable {G : Type} [Group G]

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem entry_factorizationC
    [Finite G] {L1 L2 S : Subgroup G} (h : F112ListA L1 L2 S) :
    F112E6ExtC L1 L2 S ∨
      (∃ f, 2 ≤ f ∧ (Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))).factorization 2 =
        3 * f ∧ IsLin2Type L1 f ∧ IsLin2Type L2 f) ∨
      (∃ f, 2 ≤ f ∧ (Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))).factorization 2 =
        4 * f ∧ IsLin2Type L1 f ∧ IsLin2Type L2 f) ∨
      (∃ m, 2 ≤ m ∧ (Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))).factorization 2 =
        6 * m) ∨
      (Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))).factorization 2 = 20 := by
  simp only [F112ListA] at h
  rcases h with ⟨f, hf, hA, -, hl1, -, hl2⟩ | ⟨f, hf, hA, -, hl1, -, hl2⟩ | ⟨f, hf, hA, -⟩ |
    ⟨f, hf, hA, -⟩ | ⟨a, ha, hA, -⟩ | ⟨f, hf, hA, h1, h2, h3, h4, h5⟩ | ⟨hA, -⟩
  · refine Or.inr (Or.inl ⟨f, hf, factorization_eq_of_isAmalgamOfGroup hA fun Y _ hY => ?_,
      hl1, hl2⟩)
    rw [(factorization_of_lieModel (adm_psl3 (by omega)) hY).2]
    rfl
  · refine Or.inr (Or.inr (Or.inl ⟨f, hf, factorization_eq_of_isAmalgamOfGroup hA
      fun Y _ hY => ?_, hl1, hl2⟩))
    rcases hY with ⟨h1, -⟩ | ⟨-, hY⟩
    · omega
    · rw [(factorization_of_lieModel (adm_psp2 hf) hY).2]
      rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, factorization_eq_of_isAmalgamOfGroup hA
      fun Y _ hY => ?_⟩)))
    rcases hY with ⟨h1, -⟩ | ⟨-, hY⟩
    · omega
    · rw [(factorization_of_lieModel (adm_g2 hf) hY).2]
      rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨2 * f, by omega, factorization_eq_of_isAmalgamOfGroup
      hA fun Y _ hY => ?_⟩)))
    rw [(factorization_of_lieModel (adm_d4 (by omega)) hY).2]
    simp only [lieSylowExponent]
    ring
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨2 * (2 * a + 1), by omega,
      factorization_eq_of_isAmalgamOfGroup hA fun Y _ hY => ?_⟩)))
    rcases hY with ⟨h1, -⟩ | ⟨-, -, hY⟩
    · omega
    · rw [(factorization_of_lieModel (adm_f4 ha) hY).2]
      simp only [lieSylowExponent]
      ring
  · rcases hA with hA | hext
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, factorization_eq_of_isAmalgamOfGroup hA
        fun Y _ hY => ?_⟩)))
      rw [(factorization_of_lieModel (adm_psu le_rfl (by omega)) hY).2]
      rfl
    · exact Or.inl ⟨f, hf, hext, h1, h2, h3, h4, h5⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr (factorization_eq_of_isAmalgamOfGroup hA
      fun Y _ hY => ?_))))
    rw [(factorization_of_lieModel (adm_psu (by norm_num) (by norm_num)) hY).2]
    rfl

end Entry

end Sec526

section Stmt

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_6_secondC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → ¬ Group.IsSolvable ↥L2 →
    F112ListA L1 L2 S → F112Second L1 L2 S →
      (perfectCore L1 = L1 ∧ perfectCore L2 = L2 ∧ S ≤ L1 ∧ S ≤ L2) ∨ F112E6ExtC L1 L2 S

end Stmt

section StmtProof

open CFSG.QuasithinUnique CFSG.Quasithin Sec526

theorem stmt5_2_6_second_holdsC
    : Stmt5_2_6_secondC := by
  intro G _ _ L1 L2 S _ _ _ hns1 hns2 hlist hsec
  rcases entry_factorizationC hlist with hext | hE
  · exact Or.inr hext
  set P₁ := L1 ⊔ bigB L1 L2 S with hP₁
  set P₂ := L2 ⊔ bigB L1 L2 S with hP₂
  have hsolv : ∀ {Y : Type} [Group Y] {M₁ M₂ : Subgroup Y}, VertexIso P₁ P₂ M₁ M₂ →
      (Group.IsSolvable ↥M₁ ∨ Group.IsSolvable ↥M₂) → False := by
    intro Y _ M₁ M₂ hv hs
    rcases isSolvable_of_vertexIso hv hs with h | h
    · exact hns1 (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_sup_left : L1 ≤ P₁)) (Subgroup.inclusion_injective _))
    · exact hns2 (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_sup_left : L2 ≤ P₂)) (Subgroup.inclusion_injective _))
  have h5 : ∀ {f : ℕ}, f = 2 → IsLin2Type L1 f → IsLin2Type L2 f →
      5 ∣ Nat.card ↥P₁ ∧ 5 ∣ Nat.card ↥P₂ := by
    rintro f rfl h1 h2
    exact ⟨(five_dvd_card_of_isLin2Type_two h1).trans (Subgroup.card_dvd_of_le le_sup_left),
      (five_dvd_card_of_isLin2Type_two h2).trans (Subgroup.card_dvd_of_le le_sup_left)⟩
  have hcard : ∀ {Y : Type} [Group Y] {M₁ M₂ : Subgroup Y}, VertexIso P₁ P₂ M₁ M₂ →
      Nat.card ↥P₁ = Nat.card ↥M₁ ∧ Nat.card ↥P₂ = Nat.card ↥M₂ := by
    intro Y _ M₁ M₂ hv
    obtain ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ := hv
    exact ⟨Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv⟩
  simp only [F112Second] at hsec
  rcases hsec with hi | h1 | h2 | h3 | h4 | h5' | h6 | h7 | h8 | h9 | h10 | h11 | h12 |
    ⟨f', hf', hU4⟩
  · exact Or.inl hi
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h1
    have hs := (factorization_eq_of_vertexIso hpair hv).2
    rw [fac_l32 Y hY] at hs
    rw [← hs] at hE
    rcases hE with ⟨f, hf, hEf, -⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20 <;> omega
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h2
    have hs := (factorization_eq_of_vertexIso hpair hv).2
    rw [fac_sp42 Y hY] at hs
    rw [← hs] at hE
    rcases hE with ⟨f, hf, hEf, -⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20 <;> omega
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h3
    obtain ⟨hfin, hs⟩ := factorization_eq_of_vertexIso hpair hv
    have hY5 : ¬ 5 ∣ Nat.card Y := by
      rcases card_g22 Y hY with h | h <;> rw [h] <;> norm_num
    have hY2 : (Nat.card Y).factorization 2 = 5 ∨ (Nat.card Y).factorization 2 = 6 := by
      rcases card_g22 Y hY with h | h <;> rw [h]
      · exact Or.inl (factorization_two_of_eq (m := 189) (by norm_num) (by norm_num))
      · exact Or.inr (factorization_two_of_eq (m := 189) (by norm_num) (by norm_num))
    rw [hs] at hY2
    rcases hE with ⟨f, hf, hEf, hl1, hl2⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20
    · by_cases hf2 : f = 2
      · exact hY5 ((h5 hf2 hl1 hl2).1.trans (card_dvd_of_vertexIso hv).1)
      · rw [hEf] at hY2
        omega
    · rw [hEf] at hY2
      omega
    · rw [hEm] at hY2
      omega
    · rw [hE20] at hY2
      omega
  ·
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h4
    exact (hsolv hv (isSolvable_member_d42 hY hpair)).elim
  ·
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h5'
    exact (hsolv hv (Or.inl (isSolvable_members_twoF4 hY hpair).1)).elim
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h6
    have hs := (factorization_eq_of_vertexIso hpair hv).2
    rw [fac_tits Y hY] at hs
    rw [← hs] at hE
    rcases hE with ⟨f, hf, hEf, -⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20 <;> omega
  ·
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h7
    exact (hsolv hv (U4V.exists_isSolvable_of_isYAmalgamPair (Or.inl hY) hpair)).elim
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h8
    have hs := (factorization_eq_of_vertexIso hpair hv).2
    rw [fac_u33 Y hY] at hs
    rw [← hs] at hE
    rcases hE with ⟨f, hf, hEf, -⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20 <;> omega
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isParabolicAmalgamOfGroup h9
    have hs := (factorization_eq_of_vertexIso hpair hv).2
    rw [fac_j2 Y hY] at hs
    rw [← hs] at hE
    rcases hE with ⟨f, hf, hEf, -⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20 <;> omega
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isParabolicAmalgamOfGroup h10
    have hs := (factorization_eq_of_vertexIso hpair hv).2
    rw [fac_autj2 Y hY] at hs
    rw [← hs] at hE
    rcases hE with ⟨f, hf, hEf, -⟩ | ⟨f, hf, hEf, hl1, hl2⟩ | ⟨m, hm, hEm⟩ | hE20
    · omega
    · have hf2 : f = 2 := by omega
      obtain ⟨h51, h52⟩ := h5 hf2 hl1 hl2
      obtain ⟨hc1, hc2⟩ := hcard hv
      rw [hc1] at h51
      rw [hc2] at h52
      exact false_of_five_dvd_members_autj2 hY hpair h51 h52
    · omega
    · omega
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h11
    have hs := (factorization_eq_of_vertexIso hpair hv).2
    rw [fac_m12 Y hY] at hs
    rw [← hs] at hE
    rcases hE with ⟨f, hf, hEf, hl1, hl2⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20
    · have hf2 : f = 2 := by omega
      obtain ⟨h51, -⟩ := h5 hf2 hl1 hl2
      rw [(hcard hv).1] at h51
      exact (not_five_dvd_member_m12 hY hpair).1 h51
    all_goals omega
  ·
    exfalso
    obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h12
    have hs := (factorization_eq_of_vertexIso hpair hv).2
    rw [fac_autm12 Y hY] at hs
    rw [← hs] at hE
    rcases hE with ⟨f, hf, hEf, -⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20 <;> omega
  ·
    exfalso
    have hs := factorization_of_u4ext hf' hU4
    rw [hs] at hE
    rcases hE with ⟨f, hf, hEf, -⟩ | ⟨f, hf, hEf, -⟩ | ⟨m, hm, hEm⟩ | hE20 <;> omega

end StmtProof

end CFSG.Quasithin.H13

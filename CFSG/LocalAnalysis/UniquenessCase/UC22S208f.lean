module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S208d
public import CFSG.LocalAnalysis.UniquenessCase.UC22S208e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S208Config (D : Data G) (L A : Subgroup G) (n : ℕ) : Prop :=
  L ∈ calLStar D.T D.M ∧ A ∈ calL D.T D.M ∧ A ≤ normalizer (L : Set G) ∧ ¬ A ≤ L ∧
    A ∉ calLOf D.T D.M (normalizer (L : Set G)) ∧ 2 < n ∧
    (((IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n) ∧ IsSzL2Product (Bar2 A) n) ∨
      (IsSzL2Product (Bar2 L) n ∧ (IsSz (Bar2 A) n ∨ IsL2 (Bar2 A) n)))

theorem s208f_exists_odd_prime {n : ℕ} (hn : 2 < n) : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 := by
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  refine ⟨p, hp, ?_, hpd⟩
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  omega

omit [Finite G] in
theorem s208f_shape_of_cj {g : G} {K : Subgroup G} {n : ℕ}
    (h : IsSz (Bar2 (uc22p20bCj g K)) n ∨ IsL2 (Bar2 (uc22p20bCj g K)) n) :
    IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n := by
  obtain ⟨e⟩ := s208a_bar2_cj_equiv g K
  rcases h with h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h)

omit [Finite G] in
theorem s208f_shape_cj {g : G} {K : Subgroup G} {n : ℕ} (h : IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n) :
    IsSz (Bar2 (uc22p20bCj g K)) n ∨ IsL2 (Bar2 (uc22p20bCj g K)) n := by
  obtain ⟨e⟩ := s208a_bar2_cj_equiv g K
  rcases h with h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)

theorem s208f_injective_four {α : Type*} {f : Fin 4 → α} (h01 : f 0 ≠ f 1) (h02 : f 0 ≠ f 2)
    (h03 : f 0 ≠ f 3) (h12 : f 1 ≠ f 2) (h13 : f 1 ≠ f 3) (h23 : f 2 ≠ f 3) :
    Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij h01 | exact absurd hij.symm h01
    | exact absurd hij h02 | exact absurd hij.symm h02
    | exact absurd hij h03 | exact absurd hij.symm h03
    | exact absurd hij h12 | exact absurd hij.symm h12
    | exact absurd hij h13 | exact absurd hij.symm h13
    | exact absurd hij h23 | exact absurd hij.symm h23

theorem s208f_injective_three {α : Type*} {f : Fin 3 → α} (h01 : f 0 ≠ f 1) (h02 : f 0 ≠ f 2)
    (h12 : f 1 ≠ f 2) : Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij h01 | exact absurd hij.symm h01
    | exact absurd hij h02 | exact absurd hij.symm h02
    | exact absurd hij h12 | exact absurd hij.symm h12

omit [Finite G] in
theorem s208f_le_normalizer_sup {X L A : Subgroup G} (hL : X ≤ normalizer (L : Set G))
    (hA : X ≤ normalizer (A : Set G)) : X ≤ normalizer ((L ⊔ A : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show uc22p20bCj x (L ⊔ A) = L ⊔ A
  rw [s208a_cj_sup, s208a_cj_eq_of_mem_normalizer (hL hx), s208a_cj_eq_of_mem_normalizer (hA hx)]

section Context

variable (D : Data G) (h1930 : H1930 D) (h204 : S20_4 D) (h205 : S20_5 D)
  {L N K : Subgroup G} (hL : L ∈ calLStar D.T D.M) (hN : N ∈ calMOf (L ⊔ D.T))
  (hK : K ∈ calC L) (hLK : L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
include h1930 h204 h205 hL hN hK hLK

theorem s208f_exists_moved (hXN : ¬ s208Gen D (normalizer (L : Set G)) ≤ N) :
    ∃ C ∈ s208Delta N K, ∃ t ∈ D.T, uc22p20bCj t C ≠ C := by
  by_contra h
  push Not at h
  exact hXN (s208c_X_le_of_fixed D h1930 h204 h205 hL hN hK hLK h)

theorem s208f_exists_outside (hXN : ¬ s208Gen D (normalizer (L : Set G)) ≤ N) :
    ∃ C ∈ s208Delta N K, ∀ t ∈ D.T, C ≠ uc22p20bCj t K := by
  by_contra h
  push Not at h
  exact hXN (s208c_X_le_of_subset_orbit D h1930 h204 h205 hL hN hK hLK h)

theorem s208f_orb_data {C : Subgroup G} (hC : C ∈ s208Delta N K) :
    uc22p20bOrb D.T C ∈ calLOf D.T D.M N ∧ C ∈ calC (uc22p20bOrb D.T C) :=
  s208b_orb_mem_calLOf D (s208a_mem_hSet_of_mem_calMOf D hL.1 hN)
    (s208c_delta_subset D h1930 h204 h205 hL hN hK hLK hC)

theorem s208f_not_mem_of_cover (hXN : ¬ s208Gen D (normalizer (L : Set G)) ≤ N) {A : Subgroup G}
    (hW : sSup (s208Delta N K) = L ⊔ A) : A ∉ calLOf D.T D.M (normalizer (L : Set G)) := by
  intro hA
  apply hXN
  refine s208c_X_le_of_le_normalizer D h1930 h204 h205 hL hN hK hLK ?_
  rw [hW]
  refine s208f_le_normalizer_sup ((s208a_gen_le D _).trans le_rfl) ?_
  exact (s208a_gen_le_cCompSpan D hL.1.1).trans
    (s208a_cCompSpan_le_normalizer_of_mem D hL.1.1 hA)

theorem s208f_config (hE : UC22P20gExcFacts) (h207 : S20_7 D) (hB : ListBNonabelian)
    (h66 : UC6.R6_6 D) (hU38 : uc22p20oU38Witness)
    (hXN : ¬ s208Gen D (normalizer (L : Set G)) ≤ N) :
    ∃ (A : Subgroup G) (n : ℕ), S208Config D L A n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNH : N ∈ hSet D.T D.M := s208a_mem_hSet_of_mem_calMOf D hL.1 hN
  have hTN : D.T ≤ N := s208c_T_le D hN
  have hLN : L ∈ calLOf D.T D.M N := s208c_mem_calLOf D h1930 h205 hL hN
  have hKcomp : K ∈ CFSG.Quasithin.cComp N := (s208c_K_mem_comps D h1930 h205 hL hN hK hLK).1
  have hKq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hLorb : L = uc22p20bOrb D.T K := hLK
  have hCNL : CFSG.Quasithin.cCompSpan N ≤ normalizer (L : Set G) :=
    s208a_cCompSpan_le_normalizer_of_mem D hTN hLN
  have no4 : ∀ {n : ℕ}, 2 < n → (IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n) → ∀ g : Fin 4 → G,
      (∀ i, g i ∈ N) → ¬ Function.Injective fun i => uc22p20bCj (g i) K := by
    intro n hn hsh g hg hinj
    obtain ⟨p, hp, hp2, hpn⟩ := s208f_exists_odd_prime hn
    obtain ⟨E, hEN, hEe, hEc, Z, hTZ, hZN, hZs, hEZ⟩ :=
      s208e_rank_four D hNH hKcomp hKq g hg hinj hp hp2 (s208e_borel_prop hn hsh hp hpn)
    exact uc22p20o_false_of_rank4 D hB (s20_1_124 D h66 hB) h1930 hNH hp hp2 hEN hEe hEc
      (Or.inr ⟨Z, hTZ, hZN, hZs, hEZ⟩)
  have noSU3 : ∀ g : Fin 3 → G, (∀ i, g i ∈ N) →
      Function.Injective (fun i => uc22p20bCj (g i) K) → ¬ IsSU3 (Bar2 K) 3 := by
    intro g hg hinj hU
    obtain ⟨E, hEN, hEe, hEc⟩ := s208e_rank_SU3 hU38 hKcomp hU g hg hinj
    have h4 : 4 ≤ CFSG.Open.pRank 3 N := CFSG.SectionRank.le_pRank (by norm_num) hEN hEe hEc
    have h3 := (s20_1_12 D h66 N hNH).1
    omega
  by_cases hKfix : ∀ t ∈ D.T, uc22p20bCj t K = K
  ·
    have hLK' : L = K := by
      rw [hLorb]
      exact le_antisymm (iSup_le fun t => (hKfix t t.2).le) (uc22p20b_le_orb D.T K)
    obtain ⟨C₀, hC₀Δ, t, ht, hmov⟩ := s208f_exists_moved D h1930 h204 h205 hL hN hK hLK hXN
    obtain ⟨hOrb, hC₀c⟩ := s208f_orb_data D h1930 h204 h205 hL hN hK hLK hC₀Δ
    obtain ⟨horb2, hshape⟩ := s208d_orbit_two D hE h207 h1930 hOrb.1 hC₀c ht hmov
    obtain ⟨h₀, hh₀, hC₀eq⟩ := hC₀Δ
    have hne1 : uc22p20bCj 1 K ≠ uc22p20bCj h₀ K := by
      rw [uc22p20b_cj_one, ← hC₀eq]
      intro h
      apply hmov
      rw [← h]
      exact hKfix t ht
    have hne2 : uc22p20bCj 1 K ≠ uc22p20bCj (t * h₀) K := by
      rw [uc22p20b_cj_one, ← uc22p20b_cj_cj, ← hC₀eq]
      intro h
      apply hmov
      have hC₀K : C₀ = K := by
        have := congrArg (uc22p20bCj t⁻¹) h
        rw [s208a_cj_inv_cj, hKfix t⁻¹ (D.T.inv_mem ht)] at this
        exact this.symm
      rw [hC₀K, hKfix t ht]
    have hne3 : uc22p20bCj h₀ K ≠ uc22p20bCj (t * h₀) K := by
      rw [← uc22p20b_cj_cj, ← hC₀eq]
      exact fun h => hmov h.symm
    rcases hshape with ⟨n, hn, hprod, hsh⟩ | ⟨-, hU⟩
    · have hshK : IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n := by
        rw [hC₀eq] at hsh
        exact s208f_shape_of_cj hsh
      have hcov : ∀ C ∈ s208Delta N K, C = K ∨ C = C₀ ∨ C = uc22p20bCj t C₀ := by
        rintro C ⟨h, hh, rfl⟩
        by_contra hcon
        push Not at hcon
        obtain ⟨c1, c2, c3⟩ := hcon
        refine no4 hn hshK ![1, h₀, t * h₀, h] ?_ (s208f_injective_four ?_ ?_ ?_ ?_ ?_ ?_)
        · intro i
          fin_cases i
          · exact N.one_mem
          · exact hh₀
          · exact N.mul_mem (hTN ht) hh₀
          · exact hh
        · exact hne1
        · exact hne2
        · show uc22p20bCj 1 K ≠ uc22p20bCj h K
          rw [uc22p20b_cj_one]
          exact fun e => c1 e.symm
        · exact hne3
        · show uc22p20bCj h₀ K ≠ uc22p20bCj h K
          rw [← hC₀eq]
          exact fun e => c2 e.symm
        · show uc22p20bCj (t * h₀) K ≠ uc22p20bCj h K
          rw [← uc22p20b_cj_cj, ← hC₀eq]
          exact fun e => c3 e.symm
      have hAeq : uc22p20bOrb D.T C₀ = C₀ ⊔ uc22p20bCj t C₀ :=
        s208d_orb_eq_sup D hE h207 h1930 hOrb.1 hC₀c ht hmov
      have hW : sSup (s208Delta N K) = L ⊔ uc22p20bOrb D.T C₀ := by
        apply le_antisymm
        · refine sSup_le fun C hC => ?_
          rcases hcov C hC with rfl | rfl | rfl
          · rw [hLK']
            exact le_sup_left
          · exact (uc22p20b_le_orb D.T _).trans le_sup_right
          · exact (uc22p20b_cj_le_orb ht).trans le_sup_right
        · refine sup_le ?_ ?_
          · rw [hLK']
            exact le_sSup s208c_mem_delta_self
          · rw [hAeq]
            refine sup_le (le_sSup ⟨h₀, hh₀, hC₀eq⟩) (le_sSup ?_)
            rw [hC₀eq, uc22p20b_cj_cj]
            exact ⟨t * h₀, N.mul_mem (hTN ht) hh₀, rfl⟩
      refine ⟨uc22p20bOrb D.T C₀, n, hL, hOrb.1, ?_, ?_,
        s208f_not_mem_of_cover D h1930 h204 h205 hL hN hK hLK hXN hW, hn,
        Or.inl ⟨?_, hprod⟩⟩
      · exact ((s208a_le_gen D hOrb).trans (s208a_gen_le_cCompSpan D hTN)).trans hCNL
      ·
        intro hAL
        have hC₀comp : C₀ ∈ CFSG.Quasithin.cComp N :=
          (s208c_delta_subset D h1930 h204 h205 hL hN hK hLK ⟨h₀, hh₀, hC₀eq⟩).1
        have hC₀K : C₀ ≤ sSup ({K} : Set (Subgroup G)) := by
          rw [sSup_singleton, ← hLK']
          exact (uc22p20b_le_orb D.T C₀).trans hAL
        have hmem := uc22p20b_mem_of_le_sSup {K} (Set.singleton_subset_iff.2 hKcomp) hC₀comp hC₀K
        apply hne1
        rw [uc22p20b_cj_one, ← hC₀eq]
        exact (Set.mem_singleton_iff.1 hmem).symm
      · rw [hLK']
        exact hshK
    · exfalso
      have hUK : IsSU3 (Bar2 K) 3 := by
        obtain ⟨e⟩ := s208a_bar2_cj_equiv h₀ K
        rw [hC₀eq] at hU
        exact uc22p20p_isSU3_of_mulEquiv e hU
      refine noSU3 ![1, h₀, t * h₀] ?_ (s208f_injective_three hne1 hne2 hne3) hUK
      intro i
      fin_cases i
      · exact N.one_mem
      · exact hh₀
      · exact N.mul_mem (hTN ht) hh₀
  ·
    push Not at hKfix
    obtain ⟨t₀, ht₀, hmov₀⟩ := hKfix
    have hLcal : uc22p20bOrb D.T K ∈ calL D.T D.M := hLorb ▸ hL.1
    have hKc' : K ∈ calC (uc22p20bOrb D.T K) := hLorb ▸ hK
    obtain ⟨horb2, hshape⟩ := s208d_orbit_two D hE h207 h1930 hLcal hKc' ht₀ hmov₀
    have hLeq : L = K ⊔ uc22p20bCj t₀ K := by
      rw [hLorb]
      exact s208d_orb_eq_sup D hE h207 h1930 hLcal hKc' ht₀ hmov₀
    obtain ⟨C₁, hC₁Δ, hC₁out⟩ := s208f_exists_outside D h1930 h204 h205 hL hN hK hLK hXN
    obtain ⟨h₁, hh₁, hC₁eq⟩ := hC₁Δ
    have hne1 : uc22p20bCj 1 K ≠ uc22p20bCj t₀ K := by
      rw [uc22p20b_cj_one]
      exact fun h => hmov₀ h.symm
    have hne2 : uc22p20bCj 1 K ≠ uc22p20bCj h₁ K := by
      rw [← hC₁eq]
      exact fun h => hC₁out 1 D.T.one_mem h.symm
    have hne3 : uc22p20bCj t₀ K ≠ uc22p20bCj h₁ K := by
      rw [← hC₁eq]
      exact fun h => hC₁out t₀ ht₀ h.symm
    rcases hshape with ⟨n, hn, hprod, hshK⟩ | ⟨-, hUK⟩
    ·
      have hC₁fix : ∀ t ∈ D.T, uc22p20bCj t C₁ = C₁ := by
        intro t ht
        by_contra hmov1
        refine no4 hn hshK ![1, t₀, h₁, t * h₁] ?_ (s208f_injective_four hne1 hne2 ?_ hne3 ?_ ?_)
        · intro i
          fin_cases i
          · exact N.one_mem
          · exact hTN ht₀
          · exact hh₁
          · exact N.mul_mem (hTN ht) hh₁
        · show uc22p20bCj 1 K ≠ uc22p20bCj (t * h₁) K
          rw [uc22p20b_cj_one, ← uc22p20b_cj_cj, ← hC₁eq]
          intro h
          apply hC₁out t⁻¹ (D.T.inv_mem ht)
          rw [h, s208a_cj_inv_cj]
        · show uc22p20bCj t₀ K ≠ uc22p20bCj (t * h₁) K
          rw [← uc22p20b_cj_cj, ← hC₁eq]
          intro h
          apply hC₁out (t⁻¹ * t₀) (D.T.mul_mem (D.T.inv_mem ht) ht₀)
          rw [← uc22p20b_cj_cj, h, s208a_cj_inv_cj]
        · show uc22p20bCj h₁ K ≠ uc22p20bCj (t * h₁) K
          rw [← uc22p20b_cj_cj, ← hC₁eq]
          exact fun h => hmov1 h.symm
      have hC₁orb : uc22p20bOrb D.T C₁ = C₁ :=
        le_antisymm (iSup_le fun t => (hC₁fix t t.2).le) (uc22p20b_le_orb D.T C₁)
      have hOrb := (s208f_orb_data D h1930 h204 h205 hL hN hK hLK ⟨h₁, hh₁, hC₁eq⟩).1
      rw [hC₁orb] at hOrb
      have hcov : ∀ C ∈ s208Delta N K, C = K ∨ C = uc22p20bCj t₀ K ∨ C = C₁ := by
        rintro C ⟨h, hh, rfl⟩
        by_contra hcon
        push Not at hcon
        obtain ⟨c1, c2, c3⟩ := hcon
        refine no4 hn hshK ![1, t₀, h₁, h] ?_ (s208f_injective_four hne1 hne2 ?_ hne3 ?_ ?_)
        · intro i
          fin_cases i
          · exact N.one_mem
          · exact hTN ht₀
          · exact hh₁
          · exact hh
        · show uc22p20bCj 1 K ≠ uc22p20bCj h K
          rw [uc22p20b_cj_one]
          exact fun e => c1 e.symm
        · show uc22p20bCj t₀ K ≠ uc22p20bCj h K
          exact fun e => c2 e.symm
        · show uc22p20bCj h₁ K ≠ uc22p20bCj h K
          rw [← hC₁eq]
          exact fun e => c3 e.symm
      have hW : sSup (s208Delta N K) = L ⊔ C₁ := by
        apply le_antisymm
        · refine sSup_le fun C hC => ?_
          rcases hcov C hC with rfl | rfl | rfl
          · rw [hLeq]
            exact le_sup_left.trans le_sup_left
          · rw [hLeq]
            exact le_sup_right.trans le_sup_left
          · exact le_sup_right
        · refine sup_le ?_ (le_sSup ⟨h₁, hh₁, hC₁eq⟩)
          rw [hLeq]
          exact sup_le (le_sSup s208c_mem_delta_self) (le_sSup ⟨t₀, hTN ht₀, rfl⟩)
      have hC₁comp : C₁ ∈ CFSG.Quasithin.cComp N :=
        (s208c_delta_subset D h1930 h204 h205 hL hN hK hLK ⟨h₁, hh₁, hC₁eq⟩).1
      refine ⟨C₁, n, hL, hOrb.1, ?_, ?_,
        s208f_not_mem_of_cover D h1930 h204 h205 hL hN hK hLK hXN hW, hn,
        Or.inr ⟨?_, ?_⟩⟩
      · exact (CFSG.Quasithin.le_cCompSpan hC₁comp).trans hCNL
      ·
        intro hAL
        have hsub : ({K, uc22p20bCj t₀ K} : Set (Subgroup G)) ⊆ CFSG.Quasithin.cComp N := by
          intro C hC
          rcases hC with rfl | rfl
          · exact hKcomp
          · exact uc22p20b_cj_mem_cComp hKcomp (hTN ht₀)
        have hC₁le : C₁ ≤ sSup ({K, uc22p20bCj t₀ K} : Set (Subgroup G)) := by
          rw [sSup_pair, ← hLeq]
          exact hAL
        rcases uc22p20b_mem_of_le_sSup _ hsub hC₁comp hC₁le with h | h
        · apply hne2
          rw [uc22p20b_cj_one, ← hC₁eq, h]
        · apply hne3
          rw [← hC₁eq, h]
      · rw [hLorb]
        exact hprod
      · rw [hC₁eq]
        exact s208f_shape_cj hshK
    · exfalso
      refine noSU3 ![1, t₀, h₁] ?_ (s208f_injective_three hne1 hne2 hne3) hUK
      intro i
      fin_cases i
      · exact N.one_mem
      · exact hTN ht₀
      · exact hh₁

end Context

theorem s20_8_of_not_config (D : Data G) (hE : UC22P20gExcFacts) (hB : ListBNonabelian)
    (hU38 : uc22p20oU38Witness) (h66 : UC6.R6_6 D) (h204 : S20_4 D) (h205 : S20_5 D)
    (h207 : S20_7 D) (hno : H1930 D → ∀ (L A : Subgroup G) (n : ℕ), ¬ S208Config D L A n) :
    S20_8 D := by
  refine s208b_s20_8_of_le D h204 h205 fun h1930 L hL N hN => ?_
  by_contra hXN
  obtain ⟨-, -, -, K, hK, hLK⟩ := hL.1
  obtain ⟨A, n, hc⟩ :=
    s208f_config D h1930 h204 h205 hL hN hK hLK hE h207 hB h66 hU38 hXN
  exact hno h1930 L A n hc

end CFSG.LocalAnalysis.UniquenessCase.UC22

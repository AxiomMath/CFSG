module

public import CFSG.Quasithin.EmptyFaithful.S151WB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise commutatorElement

@[expose] def Input15122ThreeEFlip4Star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L P : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeE T Mc Z₁ L → IsPSL 4 2 1 ↥L →
    ¬ SActsTrivially L (s1516 T Z₁) → SMin L (s1516 T Z₁) P →
    C126Third (P ⊔ s1516 T Z₁) (s1516 T Z₁) → P ≤ M ∨ P ≤ mZ1516 Mc Z₁

theorem s151s_localCore_of {G : Type} [Group G] [Finite G] (L S P : Subgroup G)
    (htype : IsPSL 4 2 1 ↥L ∨ IsPSL 5 2 1 ↥L) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (hS2 : IsPGroup 2 ↥S) (hP : SMin L S P) :
    CharTwo P ∧ oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  obtain ⟨n, hn, e₀⟩ : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ Nonempty (↥L ≃* SLt n) := by
    rcases htype with h | h
    · exact ⟨4, Or.inl rfl, nonempty_equiv_SLt_of_isPSL h⟩
    · exact ⟨5, Or.inr rfl, nonempty_equiv_SLt_of_isPSL h⟩
  obtain ⟨e₀⟩ := e₀
  obtain ⟨D'⟩ := exists_borelIso (by omega) hsyl e₀
  let D : SurjBorel n L (S ⊓ L) := borelIso_toSurjBorel D' hsyl.1
  have hker : D.e.ker ≤ CFSG.pCore 2 ↥L := by
    have : D.e.ker = ⊥ := MonoidHom.ker_eq_bot_iff _ |>.mpr D'.e.injective
    rw [this]
    exact bot_le
  have hk : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set G), ∀ x : ↥L, D.e x = 1 →
      D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1 := by
    intro s hs hsN x hx
    have hx' : D'.e x = 1 := hx
    have : x = 1 := (MulEquiv.map_eq_one_iff D'.e).mp hx'
    subst this
    rw [map_one, map_one]
  obtain ⟨i, hi, hshape⟩ := smin_shape rfl (by omega) D hSN hk hP
  have hBP : S ⊓ L ≤ P := hP.sl
  have hPL : P ≤ L := hP.le
  obtain ⟨a, ha⟩ : ∃ a, a ∈ D.cutsOf P := by
    rcases hshape with hc | ⟨j, hj, hij, hc⟩
    · refine ⟨if i = 1 then 2 else 1, ?_⟩
      rw [hc]
      refine ⟨⟨by split_ifs <;> omega, by split_ifs <;> omega⟩, ?_⟩
      simp only [Set.mem_singleton_iff]
      split_ifs with h <;> omega
    · refine ⟨if i = 1 ∨ j = 1 then (if i = 2 ∨ j = 2 then 3 else 2) else 1, ?_⟩
      rw [hc]
      have hn4 : 4 ≤ n := by omega
      refine ⟨⟨by split_ifs <;> omega, by split_ifs <;> omega⟩, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      split_ifs <;> omega
  exact ⟨charTwo_of_cut D hker hBP hPL ha, oPrime_of_shape D (hS2.to_le inf_le_left) hBP hPL hi hshape⟩

theorem input15122ThreeEFlip4_of_star (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kN : L45NotA38Type) (hstar : Input15122ThreeEFlip4Star) :
    Input15122ThreeEFlip4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h3E h4 hfl
  have h3E' := h3E
  obtain ⟨htype, hMLpar, hMLne, hCML⟩ := h3E
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  have htypeq : IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    htype.imp (isPSL_quotient_pCore (by norm_num)) (isPSL_quotient_pCore (by norm_num))
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L htypeq)
  have hselfN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L := by
    rcases htypeq with h4' | h5
    · exact FLc.normalizer_inf_le_of_isPSL (n := 4) (by norm_num) h4' hsyl
    · exact FLc.normalizer_inf_le_of_isPSL (n := 5) (by norm_num) h5 hsyl
  have hSM : S ≤ M := (s1516_le T Z₁).trans hMf.1.1.2
  have hMLne' : M ⊓ L ≠ L := fun h => hc.h20.one (by rw [← h]; exact inf_le_left)
  have hBM : S ⊓ L ≤ M ⊓ L := le_inf (inf_le_left.trans hSM) inf_le_right
  have hstar' : ∀ P : Subgroup G, SMin L S P → P ≤ M ∨ P ≤ mZ1516 Mc Z₁ := by
    intro P hP
    by_cases h3 : C126Third (P ⊔ S) S
    · exact hstar G T Mc M Z₁ Z₂ V₁ V₂ L P hc h3E' h4 hfl hP h3
    · obtain ⟨hchP, -⟩ := s151s_localCore_of L S P htype hSN hsyl hS2 hP
      have hchH : CharTwo (P ⊔ S) := zb_charTwo_sup hP.sP hS2 hchP
      have hmin : IsMinParabolicOf (P ⊔ S) (P ⊔ S) := hP.isMinParabolic hS2 hsyl hselfN
      exact bang_of_good h118 h126 hc hP.le hchH hmin h3
  have hQ : ∀ P : Subgroup G, SMin L S P → P ≤ (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) := by
    intro P hP
    rcases hstar' P hP with h | h
    · exact le_sup_of_le_right (le_inf h hP.le)
    · exact le_sup_of_le_left (le_inf h hP.le)
  have hjoin : (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) = L :=
    le_antisymm (sup_le inf_le_right inf_le_right)
      (input15122L45Gen_holds G L S htypeq hS2 hSN hsyl _ hQ)
  obtain ⟨P, hP, hPnot⟩ : ∃ P : Subgroup G, SMin L S P ∧ ¬ P ≤ mZ1516 Mc Z₁ ⊓ L := by
    by_contra hall
    push Not at hall
    exact hMLne (le_antisymm inf_le_right
      (input15122L45Gen_holds G L S htypeq hS2 hSN hsyl _ hall))
  have hPnotZ : ¬ P ≤ mZ1516 Mc Z₁ := fun h => hPnot (le_inf h hP.le)
  have hPM : P ≤ M := (hstar' P hP).resolve_right hPnotZ
  have hPML : P ≤ M ⊓ L := le_inf hPM hP.le
  obtain ⟨-, hoP⟩ := s151s_localCore_of L S P htype hSN hsyl hS2 hP
  have hzl := input15122ThreeEZL2_of h37 h38 kN G T Mc M Z₁ Z₂ V₁ V₂ L hc h3E'
  have hCent : CentS15122 T M Z₁ L := centS15122_of hc hSN hzl hPML hPnotZ hoP
  exact ⟨htype, hjoin, hMLpar, hMLne, hCML, ⟨inf_le_right, S ⊓ L, hsyl, hselfN.trans hBM⟩, hMLne',
    hCent⟩

end CFSG.Quasithin

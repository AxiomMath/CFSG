module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem515

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_2_FF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → ⁅V, thompsonJ T⁆ ≠ ⊥ →
      IsNatQuotCh5 L V n ∨
        (n = 2 ∧ IsCommCentralSplit L T V ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆)

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem T_ne_bot (h : Hyp5_0_1 G T M L n) : T ≠ ⊥ := by
  intro hT
  apply h.maximal.1.2.2.2
  have := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf (le_sup_right : T ≤ L ⊔ T))
  exact le_bot_iff.mp (this.trans hT.le)

omit [Finite G] in
theorem le_pCoreOf_of_isCh5Module (hV : IsCh5Module T L V) : V ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hV2 : IsPGroup 2 V := by
    intro v
    refine ⟨1, Subtype.ext ?_⟩
    simpa [pow_one] using hred.2.2.1.2 v v.2
  exact le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1 hV2

theorem isUniqueM_of_le (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) {X : Subgroup G}
    (hX : IsTwoLocal X) (hLT : L ⊔ T ≤ X) : IsUniqueM X M := by
  have hU := h.isUniqueM h331
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hX
  have hM'eq : M' = M := hU.2 M' ⟨hM', hLT.trans hle⟩
  refine ⟨⟨hU.1.1, hM'eq ▸ hle⟩, fun M'' hM'' => hU.2 M'' ⟨hM''.1, hLT.trans hM''.2⟩⟩

omit [Finite G] in
theorem isTwoLocal_normalizer {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    IsTwoLocal (Subgroup.normalizer (P : Set G)) :=
  ⟨P, hne, hP, rfl⟩

theorem thompsonJ_ne_bot_of {S : Subgroup G} (hS : IsPGroup 2 S) (hne : S ≠ ⊥) :
    thompsonJ S ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian S
  have hnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  have h2 : 2 ∣ Nat.card S := by
    rcases hS.card_eq_or_dvd with h1 | h2
    · exact absurd h1 (Finite.one_lt_card).ne'
    · exact h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2 h2
  have hx2 : (x : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have hxe : IsElemAbelian 2 (Subgroup.zpowers (x : G)) := by
    refine ⟨inferInstance, ?_⟩
    rintro y ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  have hle : Subgroup.zpowers (x : G) ≤ S := Subgroup.zpowers_le.mpr x.2
  have hcard := hA.2.2 _ hle hxe
  have hc2 : Nat.card (Subgroup.zpowers (x : G)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  intro hJ
  have hAJ : A ≤ thompsonJ S := le_iSup₂_of_le A hA le_rfl
  rw [hJ, le_bot_iff] at hAJ
  rw [hAJ, Subgroup.card_bot, hc2] at hcard
  omega

theorem lemma_5_1_2_one (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) (hV : IsCh5Module T L V)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G) ∧
      L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
      L ⊔ T ≤ Subgroup.normalizer (baum T : Set G) ∧
      IsUniqueM (Subgroup.normalizer (thompsonJ T : Set G)) M ∧
      IsUniqueM (Subgroup.normalizer (baum T : Set G)) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
  have hCR : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) :=
    h.centralizer_eq_pCoreOf hV
  have hRT : pCoreOf 2 (L ⊔ T) ≤ T := hCR ▸ inf_le_left
  have hJR : thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := hCR ▸ le_inf hJT hJ
  have hJeq : thompsonJ T = thompsonJ (pCoreOf 2 (L ⊔ T)) := thompsonJ_eq_of_le hJR hRT
  have hVT : V ≤ T := (le_pCoreOf_of_isCh5Module hV).trans hRT
  have hVe : IsElemAbelian 2 V := hV.isTwoReducedIn.2.2.1
  have hBeq : baum T = baum (pCoreOf 2 (L ⊔ T)) := by
    rw [← hCR]
    exact baum_eq_baum_centralizer hVe hVT (le_inf hJT hJ)
  have hXN : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 (L ⊔ T)
  have hXJ : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [hJeq]
    exact hXN.trans (normalizer_le_normalizer_thompsonJ _)
  have hXB : L ⊔ T ≤ Subgroup.normalizer (baum T : Set G) := by
    rw [hBeq]
    exact hXN.trans (normalizer_le_normalizer_baum _)
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hJne : thompsonJ T ≠ ⊥ := thompsonJ_ne_bot_of hT2 h.T_ne_bot
  have hBne : baum T ≠ ⊥ := fun hb => hJne (le_bot_iff.mp (hb ▸ B2F.thompsonJ_le_baum T))
  refine ⟨le_inf (hJT.trans h.T_le) hJ, hXJ, hXB, ?_, ?_⟩
  · exact h.isUniqueM_of_le h331 (isTwoLocal_normalizer (hT2.to_le hJT) hJne) hXJ
  · exact h.isUniqueM_of_le h331 (isTwoLocal_normalizer (hT2.to_le inf_le_left) hBne) hXB

end Hyp5_0_1

theorem stmt5_1_2_of (h331 : Stmt3_3_1) (hFF : Stmt5_1_2_FF) : Stmt5_1_2 := by
  intro G _ _ T M L V n h hV
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  · exact Or.inl (h.lemma_5_1_2_one h331 hV hJ)
  · have hVJ : ⁅V, thompsonJ T⁆ ≠ ⊥ := by
      intro hb
      apply hJ
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
      exact Subgroup.le_centralizer_iff.mp hb
    rcases hFF G T M L V n h hV hVJ with h2 | ⟨h2, hs, hb, h5⟩
    · exact Or.inr (Or.inl ⟨hVJ, h2⟩)
    · exact Or.inr (Or.inr ⟨hVJ, h2, hs, hb, h5⟩)

end CFSG.Quasithin.H13

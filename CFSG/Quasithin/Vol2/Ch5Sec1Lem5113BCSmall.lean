module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BCOrder
public import CFSG.Quasithin.H13.A6S13825g

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A7Pack

variable {G : Type} [Group G] [Finite G] {T K Kh W : Subgroup G}
  {e : O2Q Kh ≃* alternatingGroup (Fin 7)}

theorem pCoreOf_le_T (pk : A7Pack T K Kh W e) : pCoreOf 2 Kh ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 Kh ≤ pCoreOf 2 (Kh ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((CFSG.LieType.BorelTits.pCoreOf_le 2 Kh).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 _)
        (pk.T_le.trans (normalizer_le_normalizer_pCoreOf 2 _)))
      (pCoreOf_isPGroup 2 _)
  exact h1.trans (F7.isSylowTwoOf_pCoreOf_le pk.sylow)

theorem card_inf_eq_eight_mul (pk : A7Pack T K Kh W e) :
    Nat.card ↥(T ⊓ Kh) = 8 * Nat.card ↥(pCoreOf 2 Kh) := by
  have h8 : Nat.card (modO2Image Kh (T ⊓ Kh)) = 8 := by
    rw [← A7Std.card_p0, ← pk.p0, Subgroup.card_map_of_injective e.injective]
  rw [A6.L13825.card_modO2Image inf_le_right, Subgroup.inf_relIndex_left] at h8
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 Kh) (T ⊓ Kh)
  rw [inf_of_le_left (le_inf pk.pCoreOf_le_T (CFSG.LieType.BorelTits.pCoreOf_le 2 Kh)), h8] at h1
  exact h1.symm

omit [Finite G] in
theorem commutator_le_pCoreOf (pk : A7Pack T K Kh W e) (hT2 : IsPGroup 2 T) :
    ⁅W, Kh⁆ ≤ pCoreOf 2 Kh := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUK : ⁅W, Kh⁆ ≤ Kh :=
    (BCOrd.commutator_le_inf_of_le_normalizer (pk.le_T.trans pk.T_le)
      (le_sup_left.trans pk.red.2.1)).trans inf_le_right
  exact le_pCoreOf_of_le_normalizer 2 hUK pk.le_normalizer (hT2.to_le (pk.U_le.trans pk.le_T))

end A7Pack

theorem stmt5_1_13_bc_small_of (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
      Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
      Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
      quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
      ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
      Nat.card T ≤ 2 ^ 7 →
        pCoreOf 2 (conjClosure Kh₁ T) = ⁅conjClosure (quasithinOmegaOneCenter T)
            (conjClosure Kh₁ T ⊔ T), conjClosure Kh₁ T⁆ ∧
          Nat.card ↥(pCoreOf 2 (conjClosure Kh₁ T)) = 2 ^ 4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 _ hX hnZ hA7 _ _ hT
  obtain ⟨e, pk⟩ := m.exists_a7Pack h5171 h51 hc5 hX hnZ hA7
  have hT2 : IsPGroup 2 T := m.hyp.toHyp5_0_1.sylow.1
  have hTK := pk.card_inf_eq_eight_mul
  have hUO := pk.commutator_le_pCoreOf hT2
  have hU16 : 16 ≤ Nat.card ↥⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆ := by
    rcases pk.card with h | h <;> rw [h] <;> norm_num
  have hcU := Subgroup.card_le_of_le hUO
  have hcT := Subgroup.card_le_of_le (inf_le_left : T ⊓ conjClosure Kh₁ T ≤ T)
  have hT' : Nat.card T ≤ 128 := by simpa using hT
  have hO16 : Nat.card ↥(pCoreOf 2 (conjClosure Kh₁ T)) = 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
    omega
  exact ⟨(Subgroup.eq_of_le_of_card_ge hUO (by omega)).symm, hO16⟩

end CFSG.Quasithin.H13

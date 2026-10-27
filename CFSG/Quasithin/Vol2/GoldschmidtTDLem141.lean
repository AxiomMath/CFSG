module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

namespace L141

variable {G : Type} [Group G]

theorem mem_of_pow_mem_of_coprime {B : Subgroup G} {a : G} {m n : ℕ} (hm : a ^ m ∈ B)
    (hn : a ^ n ∈ B) (hmn : Nat.Coprime m n) : a ∈ B := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hmn
  have h : a = (a ^ m) ^ u * (a ^ n) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm _ u,
      mul_comm _ v, huv, zpow_one]
  rw [h]
  exact B.mul_mem (B.zpow_mem hm u) (B.zpow_mem hn v)

theorem conjClosure_sup_eq_sup (L T : Subgroup G) : conjClosure L T ⊔ T = L ⊔ T := by
  apply le_antisymm
  · refine sup_le (conjClosure_le fun t ht l hl => ?_) le_sup_right
    exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht)
      (Subgroup.mem_sup_left hl)) ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
  · exact sup_le ((le_conjClosure L T).trans le_sup_left) le_sup_right

theorem noncentralTwoChiefFactorsInO2_of_isXi {T X : Subgroup G} (hX : IsXi T X) :
    NoncentralTwoChiefFactorsInO2 X := by
  obtain ⟨-, -, -, p, hp, hp2, hpow, -, -⟩ := hX
  intro A B hAB
  obtain ⟨hOB, hBA, hAX, -, -, -, h2⟩ := hAB
  exfalso
  refine hBA.not_ge fun a ha => ?_
  obtain ⟨k, hk⟩ := h2 a ha
  exact mem_of_pow_mem_of_coprime (hOB (hpow a (hAX ha))) hk
    (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))

end L141

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tmp1_4_1_four_of_exists {T L : Subgroup G}
    (h : ∃ V, IsTwoReducedIn (L ⊔ T) V ∧ ⁅V, L⁆ ≠ ⊥) :
    ∃ V : Subgroup G, V ≤ fsuL0 T L ⊔ T ∧
      IsPrimeReduced 2 (V.subgroupOf (fsuL0 T L ⊔ T)) ∧ ⁅V, fsuL0 T L⁆ ≠ ⊥ := by
  obtain ⟨V, hV, hne⟩ := h
  obtain ⟨hVle, hred⟩ := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hV
  refine ⟨V, ?_⟩
  show V ≤ conjClosure L T ⊔ T ∧ IsPrimeReduced 2 (V.subgroupOf (conjClosure L T ⊔ T)) ∧
    ⁅V, conjClosure L T⁆ ≠ ⊥
  rw [L141.conjClosure_sup_eq_sup]
  exact ⟨hVle, hred, fun h => hne (le_bot_iff.mp
    (h ▸ Subgroup.commutator_mono le_rfl (le_conjClosure L T)))⟩

theorem tmp1_4_1_four_of_a36 (h36 : A36ForSQTK) : Tmp1_4_1_four := by
  intro G _ _ T L hs hnab hK hT hL hXf
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  refine tmp1_4_1_four_of_exists ?_
  rcases hL with hmax | hXiStar
  · have hloc : quasithinIsLocal T L := hmax.1
    have hcc : L ∈ cComp (L ⊔ T) := hloc.2.1
    have hInH : InH (S : Subgroup G) (L ⊔ T) := ⟨hS ▸ le_sup_right, hloc.2.2.2⟩
    have hf : quasithinIsFaithfulLocal (S : Subgroup G) L := by
      rw [hS]
      exact isFaithfulLocal_iff_isXf.mpr ⟨hloc, hXf⟩
    exact ((lemma_1_2_10_of_a36 hK hs hnab h36 S hInH hcc).out 1 2).mp hf
  · have hXi : IsXi T L := hXiStar.1
    obtain ⟨hLO, hTN, hO2, -⟩ := hXi
    have hInH : InH (S : Subgroup G) (L ⊔ T) := ⟨hS ▸ le_sup_right, hO2⟩
    have hFM : CharTwo (L ⊔ T) := charTwo_of_inH hK.2.1 S hInH
    have hsub : IsSubnormal L (L ⊔ T) :=
      A4.subnormal_of_normal le_sup_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
          (sup_le Subgroup.le_normalizer hTN))
    exact ((a4_11 hFM hLO hsub (L141.noncentralTwoChiefFactorsInO2_of_isXi hXiStar.1)).out 1 2).mp
      hXf

end CFSG.Quasithin.Vol2.Ch10

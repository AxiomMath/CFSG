module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.CoreFree
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem424N

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise commutatorElement

structure LocConf (H : Type) [Group H] [Finite H] (V L S M : Subgroup H) : Prop where
  qt : IsQuasithin H
  kgroup : CFSG.SectionRank.IsKGroupCat H
  o2 : pCoreOf 2 (⊤ : Subgroup H) = ⊥
  v_two : IsPGroup 2 V
  v_ne : V ≠ ⊥
  v_odd : V ≤ Subgroup.centralizer (CFSG.oddCore H : Set H)
  v_eq : V = ⁅V, L⁆
  l_perfect : ⁅L, L⁆ = L
  l_le : L ≤ M
  l_normal : M ≤ Subgroup.normalizer (L : Set H)
  s_two : IsPGroup 2 S
  s_le : S ≤ M
  v_norm : L ⊔ S ≤ Subgroup.normalizer (V : Set H)
  v_le : V ≤ pCoreOf 2 M
  uniq : ∀ P : Subgroup H, P ≠ ⊥ → IsPGroup 2 P → L ⊔ S ≤ Subgroup.normalizer (P : Set H) →
    Subgroup.normalizer (P : Set H) ≤ M
  cent : Subgroup.centralizer (V : Set H) ≤ M
  cent_mod : ∀ N : Subgroup H, N ≤ L → L ≤ Subgroup.normalizer (N : Set H) →
    N ≤ Subgroup.centralizer (V : Set H) → ⁅N, L⁆ ≤ pCoreOf 2 L

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem pCore_le_pCoreOf_top : CFSG.pCore 2 H ≤ pCoreOf 2 (⊤ : Subgroup H) :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
    (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance])
    (CFSG.pCore_isPGroup (p := 2) (G := H))

omit [Finite H] in
theorem pCore_eq_bot_of_isComponent (hO2 : pCoreOf 2 (⊤ : Subgroup H) = ⊥) {K : Subgroup H}
    (hK : CFSG.IsComponent K) : CFSG.pCore 2 ↥K = ⊥ := by
  have h1 := CFSG.LyonsUnitaryFour.map_pCore_le_pCore_of_isSubnormal (p := 2) hK.2
  rw [← le_bot_iff, ← Subgroup.map_le_map_iff_of_injective K.subtype_injective, Subgroup.map_bot]
  exact h1.trans (pCore_le_pCoreOf_top.trans hO2.le)

omit [Finite H] in
theorem pCoreOf_eq_bot_of_pCore {K : Subgroup H} (hK : CFSG.pCore 2 ↥K = ⊥) : pCoreOf 2 K = ⊥ := by
  unfold pCoreOf
  rw [hK, Subgroup.map_bot]

theorem not_le_of_commutator_ne_bot {V L S M : Subgroup H} (hc : LocConf H V L S M)
    {K : Subgroup H} (hO2K : pCoreOf 2 K = ⊥) (hVK : V ≤ Subgroup.normalizer (K : Set H))
    (hKV : ⁅K, V⁆ ≠ ⊥) : ¬ K ≤ M := by
  intro hKM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hKV
  have h1 : ⁅K, V⁆ ≤ K := commutator_le_left_of_le_normalizer hVK
  have h2 : ⁅K, V⁆ ≤ pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl hc.v_le).trans
      (commutator_le_right_of_le_normalizer (hKM.trans (le_normalizer_pCoreOf 2 M)))
  have hN : K ≤ Subgroup.normalizer ((K ⊓ pCoreOf 2 M : Subgroup H) : Set H) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hk, hKM.trans (le_normalizer_pCoreOf 2 M) hk⟩
  have h3 : K ⊓ pCoreOf 2 M ≤ pCoreOf 2 K :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hN
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
  rw [hO2K] at h3
  exact le_bot_iff.mp ((le_inf h1 h2).trans h3)

end CFSG.Quasithin.H13.Ch4.E443

module

public import CFSG.Quasithin.Background.C124AsmEntry
public import CFSG.Quasithin.H13.GoldschmidtC137KMod3
public import CFSG.Quasithin.Background.C124AsmNormal
public import CFSG.Quasithin.H13.GoldschmidtC137Inner

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure S6Ctx [Finite G] (X T V L P M : Subgroup G) : Prop where
  hX : CharTwo X
  hSQ : SQTKGroup ↥X
  hT : IsSylowTwoOf T X
  hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  hL : L ∈ cComp X
  hL2 : CharTwo L
  hA6 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))
  hnin : ¬ autOn T V ≤ autOn L V
  hTP : T ≤ P
  hPM : P ≤ M
  hMX : M < X
  hmax : ∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X
  hPeq : P = M
  hred : IsTwoReducedIn X V
  hVL : ⁅V, L⁆ ≠ ⊥
  hmod : ∃ k, (k = B3.Mod.ut0 ∨ k = B3.Mod.u0) ∧ Nonempty (KModel k (autI hred.2.2.1 L))

namespace S6Ctx

variable [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M)
include h

theorem hLX : L ≤ X := le_of_mem_cComp h.hL

theorem hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod h.hT h.hprod h.hL

theorem hXN : X ≤ normalizer (V : Set G) := h.hred.2.1

theorem hVe : IsElemAbelian 2 V := h.hred.2.2.1

theorem hPX : P < X := lt_of_le_of_lt h.hPM h.hMX

theorem hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
  have h3 := Subgroup.relIndex_mul_relIndex T P X h.hTP h.hPX.le
  have h4 : 2 ∣ T.relIndex X := by
    rw [← h3]
    exact Dvd.dvd.mul_right h2 _
  exact h.hT.2.2 h4

theorem hRT : pCoreOf 2 P ≤ T :=
  pCoreOf_two_le_of_sylowIn h.hTP h.hT.2.1 h.hTodd

theorem hQR : pCoreOf 2 X ≤ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn h.hT.1 h.hT.2.1 h.hT.2.2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans h.hTP)
    (h.hPX.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem isAltQuotient : IsAltQuotient L (oTwoZIn L) 6 := isAltQuotient_of_a6 h.hA6

theorem hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
  C124.isQuasisimple_of_altQuotient h.hL h.isAltQuotient (by norm_num)

theorem pCoreOf_le_centralizer : pCoreOf 2 L ≤ centralizer (V : Set G) := by
  have hLN : L ≤ normalizer (V : Set G) := h.hLX.trans h.hXN
  have hO2 : pCoreOf 2 (autOn L V) = ⊥ :=
    C124.pCoreOf_autI_L_eq_bot h.hVe h.hred h.hLX h.hn
  have hle := InternalSec.pCore_le_ker_autOnHom hLN hO2
  rw [C124.pCoreOf_eq_map_pCore]
  rintro _ ⟨y, hy, rfl⟩
  exact (InternalSec.mem_ker_autOnHom hLN y).1 (hle hy)

theorem CLV : L ⊓ centralizer (V : Set G) = pCoreOf 2 L := by
  have hLN : L ≤ normalizer (V : Set G) := h.hLX.trans h.hXN
  apply le_antisymm _ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) h.pCoreOf_le_centralizer)
  obtain ⟨e⟩ := h.hA6
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  set D' : Subgroup ↥L := (L ⊓ centralizer (V : Set G)).subgroupOf L with hD'
  have hD'n : D'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hD', Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), ?_⟩
    exact C124.conj_mem_centralizer_of_le hLN g.2 hn.2
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hN1 : (D'.map π).Normal := Subgroup.Normal.map hD'n π (QuotientGroup.mk'_surjective _)
  rcases hsimp.eq_bot_or_eq_top_of_normal (D'.map π) with h1 | h1
  · intro d hd
    have hd' : (⟨d, hd.1⟩ : ↥L) ∈ D' := Subgroup.mem_subgroupOf.2 hd
    have h2 : π ⟨d, hd.1⟩ ∈ D'.map π := ⟨_, hd', rfl⟩
    rw [h1, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    rw [C124.pCoreOf_eq_map_pCore]
    exact ⟨_, h2, rfl⟩
  · exfalso
    apply h.hVL
    have hLC : L ≤ centralizer (V : Set G) := by
      intro l hl
      obtain ⟨d, hd, hdl⟩ := (h1 ▸ Subgroup.mem_top (π ⟨l, hl⟩) : π ⟨l, hl⟩ ∈ D'.map π)
      have hdl' : d⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdl
        exact hdl
      have h3 : ((d⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := by
        rw [C124.pCoreOf_eq_map_pCore]
        exact ⟨_, hdl', rfl⟩
      have h4 := h.pCoreOf_le_centralizer h3
      have h5 : (d : G) ∈ centralizer (V : Set G) := (Subgroup.mem_subgroupOf.1 hd).2
      have h6 : l = (d : G) * ((d⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by
        simp
      rw [h6]
      exact Subgroup.mul_mem _ h5 h4
    rw [← Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hLC

theorem CXV : X ⊓ centralizer (V : Set G) = pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm _ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
    (C124.pCoreOf_le_centralizer h.hred))
  set K := X ⊓ centralizer (V : Set G) with hK
  have hKX : K ≤ X := inf_le_left
  have hXK : X ≤ normalizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · rintro ⟨hk1, hk2⟩
      exact ⟨X.mul_mem (X.mul_mem hx hk1) (X.inv_mem hx),
        C124.conj_mem_centralizer_of_le h.hXN hx hk2⟩
    · rintro ⟨hk1, hk2⟩
      refine ⟨?_, ?_⟩
      · have := X.mul_mem (X.mul_mem (X.inv_mem hx) hk1) hx
        simpa [mul_assoc] using this
      · have := C124.conj_mem_centralizer_of_le h.hXN (X.inv_mem hx) hk2
        simpa [mul_assoc] using this
  have hK2 : IsPGroup 2 K := by
    intro k
    obtain ⟨j, hj⟩ := C124.exists_pow_mem_of_prod h.hLX h.hn h.hT.1 h.hT.2.1 (hKX k.2)
      (h.hprod _ (hKX k.2))
    have hk : (k : G) ^ 2 ^ j ∈ pCoreOf 2 L := by
      rw [← h.CLV]
      exact ⟨hj, Subgroup.pow_mem _ k.2.2 _⟩
    obtain ⟨i, hi⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hk⟩
    refine ⟨j + i, Subtype.ext ?_⟩
    have hi' : ((k : G) ^ 2 ^ j) ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    rw [pow_add, pow_mul]
    simpa using hi'
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKX hXK hK2

end S6Ctx

end CFSG.Quasithin.H13.U3.GC137

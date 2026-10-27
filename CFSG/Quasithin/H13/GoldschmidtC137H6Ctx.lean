module

public import CFSG.Quasithin.Background.C124AsmEntry
public import CFSG.Quasithin.Background.C124AsmNormal
public import CFSG.Quasithin.H13.GoldschmidtC137Inner
public import CFSG.Quasithin.H13.GoldschmidtC137KMod3

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure H6Ctx [Finite G] (X T V L P : Subgroup G) : Prop where
  hX : CharTwo X
  hSQ : SQTKGroup ↥X
  hT : IsSylowTwoOf T X
  hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  hL : L ∈ cComp X
  hL2 : CharTwo L
  hhat : A6.IsHatA6 L
  hnin : ¬ autOn T V ≤ autOn L V
  hTP : T ≤ P
  hPX : P < X
  hred : IsTwoReducedIn X V
  hVL : ⁅V, L⁆ ≠ ⊥
  hmod : ∃ k, (k = B3.Mod.ut0 ∨ k = B3.Mod.u0) ∧ Nonempty (KModel k (autI hred.2.2.1 L))

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem hLX : L ≤ X := le_of_mem_cComp h.hL

theorem hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod h.hT h.hprod h.hL

theorem hXN : X ≤ normalizer (V : Set G) := h.hred.2.1

theorem hVe : IsElemAbelian 2 V := h.hred.2.2.1

theorem hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
  have h3 := Subgroup.relIndex_mul_relIndex T P X h.hTP h.hPX.le
  have h4 : 2 ∣ T.relIndex X := by
    rw [← h3]
    exact Dvd.dvd.mul_right h2 _
  exact h.hT.2.2 h4

theorem hRT : pCoreOf 2 P ≤ T :=
  pCoreOf_two_le_of_sylowIn h.hTP h.hT.2.1 h.hTodd

theorem hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn h.hT.1 h.hT.2.1 h.hT.2.2

theorem hQR : pCoreOf 2 X ≤ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.hQT.trans h.hTP)
    (h.hPX.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem isAltQuotient : IsAltQuotient L (oTwoZIn L) 6 := isAltQuotient_of_hatA6 h.hhat

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

theorem hTC : T ⊓ centralizer (V : Set G) = pCoreOf 2 X :=
  (C124.B2_10_2 h.hVe h.hred h.hQT le_rfl h.hT h.hLX h.hn h.hprod h.hVL (Or.inl h.hLq)).1.2.symm

theorem hTCR : T ⊓ centralizer (V : Set G) ≤ pCoreOf 2 P := h.hTC ▸ h.hQR

end H6Ctx

end CFSG.Quasithin.H13.U3.GC137

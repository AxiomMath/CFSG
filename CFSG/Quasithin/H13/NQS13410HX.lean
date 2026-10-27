module

public import CFSG.Quasithin.H13.NQS13410HL
public import CFSG.Quasithin.H13.NQS13410Z

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem not_l32_of_hat (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L)
    {K W : Subgroup G} (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1W : L₁Of L (fsuV1 T V) ≤ normalizer (W : Set G))
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    [IsMulCommutative ↥W] (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G)) (hWK : ⁅W, K⁆ = W)
    (hWR : W ≤ reducedAggregate (K ⊔ T)) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
  have hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K := by
    rw [← ho2Z]
    exact o2Z_le_pCoreOf_of_center hZK
  obtain ⟨y, hyK, ⟨m, hm, hym⟩, hyW, hy3W, hyfix⟩ := exists_three_of_l32 hKW hnat hsyl
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨s, hs⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 K
      ⟨_, hCK (mem_inf.2 ⟨pow_mem hyK 3, hy3W⟩)⟩
    have hs' : (y ^ 3) ^ 2 ^ s = 1 := by
      have := congrArg Subtype.val hs
      simpa using this
    have hm' : (y ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
    exact mem_bot.1 (mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _))
  have hy1 : y ≠ 1 := fun h => hyW (h ▸ one_mem _)
  have hyZ := mem_centralizer_Z_of hTW hZW hyK hyfix
  have hyL1 := mem_L1_of_orderOf_three h1332 h1228 S hyZ (orderOf_eq_prime hy3 hy1)
  by_cases hyV : y ∈ centralizer (V : Set G)
  · exact not_l32_of_hat_of_mem hC137 h1332 h1228 S hhat hKf hKM hL1K hL1Z hK3 hnat hKW hTW hWK
      hWR hZW ho2Z hyK hyL1 hy3 hyW hyV
  · exact not_l32_of_hat_of_not_mem h1332 S hhat hKf hKM hL1K hL1Z hL1W hK3 hnat hKW hTW hWR
      ho2Z hyK hyL1 hy3 hyW hyV

theorem not_isHatA6_of_irr (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1W : L₁Of L (fsuV1 T V) ≤ normalizer (W : Set G))
    (hW : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W) [IsMulCommutative ↥W]
    (hTW : T ≤ normalizer (W : Set G)) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    (hcase : (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∧
        AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5) ∨
      (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
        BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1) ∨
      ((Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K) ∧
        ((AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
          (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
            FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥)))) :
    ¬ A6.IsHatA6 L := by
  intro hhat
  obtain ⟨-, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hKW : K ≤ normalizer (W : Set G) := hW.2.2.1
  have hWR : W ≤ reducedAggregate (K ⊔ T) := hW.1
  have hWK : ⁅W, K⁆ = W := hW.2.2.2.1
  have hWK' : W ≤ K := by
    rw [← hWK]
    have hWT : W ≤ T := (hWR.trans (R2_le_pCoreOf (K ⊔ T))).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
    exact le_normalizer_iff_commutator_le_right.mp (hWT.trans hTK)
  rcases hcase with ⟨hK5, hW5⟩ | ⟨hK3, hnat⟩ | ⟨hK6 | hhatK, hmod⟩
  · exact not_a5_of_hat h1332 h1228 S hhat hKf hKM hL1K hK5 hW5 hKW hTW hWK' hWR hZW ho2Z
  · exact not_l32_of_hat hC137 h1332 h1228 S hhat hKf hKM hL1K hL1Z hL1W hK3 hnat hKW hTW hWK
      hWR hZW ho2Z
  · exact not_a6_of_hat h1332 h1228 S hhat hKf hL1K hL1Z hL1W hK6 hW hmod hTW ho2Z
  · exact not_hatK_of_hat h1332 h1228 S hhat hKf hKM hL1K hL1Z hL1W hhatK hW hmod hTW hZW ho2Z

end CFSG.Quasithin.H13.NQS134

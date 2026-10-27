module

public import CFSG.Quasithin.H13.NQS134YA
public import CFSG.Quasithin.H13.NQS13410P

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace KWData

variable {S : A6.Setting134 G T L V} {K W : Subgroup G} [IsMulCommutative ↥W]
  (D : KWData S K W)
include D

theorem false_of_cZ_eq_bot (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (h56 : AsB56)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K)
    (hK : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (hcZ : U3.cZ T K = ⊥) (hZ2 : 2 < Nat.card ↥(quasithinOmegaOneCenter T)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hab2, hi | hii⟩ := D.split h56
  swap
  ·
    have hK3 := l32_of_case1ii (le_sup_left.trans (twoReduced_R2 (K ⊔ T)).2.1)
      D.pCoreOf_le_R2 hii D.Ktype
    exact not_case1ii_of_a6 hC137 h1332 h1228 S he D.Kf D.KM (hL1.trans le_normalizer) hK3
      (nat_of_l32 D.Wirr.2.2.1 D.o2Z hK3 D.mod) D.Wirr.2.2.1 D.TW D.W_le_comm D.o2Z hii
      D.Z_le_comm
  obtain ⟨hWR, hVK⟩ := D.comm_eq_of_irr hi
  have hZW : quasithinOmegaOneCenter T ≤ W := by
    have h := D.Z_le_vK
    rwa [← hVK, hWR, hcZ, sup_bot_eq] at h
  have hZT : quasithinOmegaOneCenter T ≤ W ⊓ centralizer (T : Set G) :=
    le_inf hZW ((U3.s134_Z_le_center T).trans inf_le_right)
  have hcard := card_le_of_le hZT
  obtain ⟨c5, c3, c6, -⟩ := card_quot_of_type K
  rcases match13410 D.Wirr.2.2.1 D.o2Z D.Ktype D.mod with ⟨hK5, -⟩ | ⟨-, hnat⟩ | ⟨-, h6 | hc⟩
  ·
    have h60 := c5 hK5
    rcases hK with h | h
    · rw [c3 h] at h60
      norm_num at h60
    · rw [c6 h] at h60
      norm_num at h60
  ·
    have := card_cT_le_of_l32 D.Wirr.2.2.1 hnat D.isSylowTwoOf_inf
    omega
  ·
    obtain ⟨R⟩ := exists_rawData4 D.Wirr.2.2.1 h6.1
    obtain ⟨F⟩ := exists_frame4 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW
      D.isSylowTwoOf_inf
    have := card_cT_le_of_frame4 F
    omega
  ·
    obtain ⟨-, hc2, -⟩ := hc
    have hXT : W ⊓ centralizer (K : Set G) ≤ T := inf_le_left.trans D.W_le_T
    have hTX : T ≤ normalizer ((W ⊓ centralizer (K : Set G) : Subgroup G) : Set G) := fun t ht =>
      inf_normalizer_le_normalizer_inf ⟨D.TW ht, le_normalizer_centralizer_of D.TK ht⟩
    have hX1 : W ⊓ centralizer (K : Set G) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hc2
      omega
    obtain ⟨x, hxX, hxT, hx1⟩ := exists_mem_centralizer_ne_one S.h13.sylow.1 hXT hTX hX1
    have hx2 : x ^ 2 = 1 := D.sq_eq_one (mem_inf.1 hxX).1
    have hxc : x ∈ U3.cZ T K :=
      ⟨mem_quasithinOmegaOneCenter_iff.2 ⟨hXT hxX, hxT, hx2⟩, (mem_inf.1 hxX).2⟩
    rw [hcZ, mem_bot] at hxc
    exact hx1 hxc

end KWData

end CFSG.Quasithin.H13.NQS134

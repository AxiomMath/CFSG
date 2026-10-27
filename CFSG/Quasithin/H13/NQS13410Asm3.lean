module

public import CFSG.Quasithin.H13.NQS13410Asm2
public import CFSG.Quasithin.H13.NQS13410G
public import CFSG.Quasithin.H13.NQS13410J
public import CFSG.Quasithin.H13.NQS13410P

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem z_ne_one : z ≠ 1 := fun h => D.zL (h ▸ one_mem _)

theorem z_sq : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 D.zV1.2).2.2

theorem card_zpowers_z : Nat.card (zpowers z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime D.z_sq D.z_ne_one

theorem main_of_a6 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ = W ∧ ⁅reducedAggregate (K ⊔ T), K⁆ = W ∧
      quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K ∧ L₁Of L (fsuV1 T V) ≤ K ∧
      U3.cZ T K = zpowers z ∧
      ((LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
          BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1) ∨
        (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∧
          ((AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧
              W ⊓ centralizer (K : Set G) = ⊥) ∨
            (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
              FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥)))) := by
  obtain ⟨hab2, hi | hii⟩ := D.split h56
  swap
  · exfalso
    have hK3 := l32_of_case1ii (le_sup_left.trans (twoReduced_R2 (K ⊔ T)).2.1)
      D.pCoreOf_le_R2 hii D.Ktype
    exact not_case1ii_of_a6 hC137 h1332 h1228 S he D.Kf D.KM D.L1_le_K hK3
      (nat_of_l32 D.Wirr.2.2.1 D.o2Z hK3 D.mod) D.Wirr.2.2.1 D.TW D.W_le_comm D.o2Z hii
      D.Z_le_comm
  obtain ⟨hWR, hVK⟩ := D.comm_eq_of_irr hi
  have hVKW : ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ = W := hVK.symm.trans hWR
  have hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K := by
    have h := D.Z_le_vK
    rwa [hVKW] at h
  have hy := exists_three_K h1332 S D.Kf D.Wirr.2.2.1 D.TW D.Wirr.2.1
    (S.h13.sylow.1.to_le D.W_le_T) ⟨‹_›, D.mod⟩
  have hL1 := (L1_le_of_a6 h1332 h1228 hC58 h317 h56 S he D.exists_inH D.Ktype D.L1_le_K D.TW
    hZW D.o2Z hy).trans inf_le_left
  have hcZ := cZ_K_eq S D.KM D.zV1.2 D.z_ne_one D.Kz
    (U3.s134_card_Z h1332 hC58 h317 h56 S D.exists_inH)
  refine ⟨hVKW, hWR, hZW, hL1, hcZ, ?_⟩
  rcases match13410 D.Wirr.2.2.1 D.o2Z D.Ktype D.mod with ⟨hK5, hW5⟩ | h3 | ⟨hK6 | hhatK, hmod⟩
  · exact (not_a5_of_a6 hC137 h1332 h1228 S he D.Kf D.KM D.L1_le_K hK5 hW5 D.Wirr.2.2.1 D.TW
      D.Wirr.1 hZW D.o2Z).elim
  · exact Or.inl h3
  · exact Or.inr ⟨hK6, hmod⟩
  · exact (not_isHatA6_of_a6 h1332 h1228 S he D.L1_le_K D.TW hZW D.o2Z hy hhatK).elim

theorem zpowers_eq_inf (hcZ : U3.cZ T K = zpowers z)
    (hc2 : Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2) :
    zpowers z = W ⊓ centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXT : W ⊓ centralizer (K : Set G) ≤ T := inf_le_left.trans D.W_le_T
  have hTX : T ≤ normalizer ((W ⊓ centralizer (K : Set G) : Subgroup G) : Set G) := fun t ht =>
    inf_normalizer_le_normalizer_inf ⟨D.TW ht, le_normalizer_centralizer_of D.T_le_K ht⟩
  have hX1 : W ⊓ centralizer (K : Set G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc2
    omega
  obtain ⟨x, hxX, hxT, hx1⟩ := exists_mem_centralizer_ne_one S.h13.sylow.1 hXT hTX hX1
  have hx2 : x ^ 2 = 1 := D.sq_eq_one (mem_inf.1 hxX).1
  have hxc : x ∈ U3.cZ T K :=
    ⟨mem_quasithinOmegaOneCenter_iff.2 ⟨hXT hxX, hxT, hx2⟩, (mem_inf.1 hxX).2⟩
  rw [hcZ] at hxc
  have hcx : Nat.card (zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx2 hx1
  have e1 : zpowers x = zpowers z :=
    eq_of_le_of_card_ge (zpowers_le.mpr hxc) (by rw [D.card_zpowers_z, hcx])
  have e2 : zpowers x = W ⊓ centralizer (K : Set G) :=
    eq_of_le_of_card_ge (zpowers_le.mpr hxX) (by rw [hc2, hcx])
  rw [← e1, e2]

theorem one_six (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    (Nonempty (↥(autOn K (conjClosure (quasithinOmegaOneCenter T) K)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (↥(autOn K (conjClosure (quasithinOmegaOneCenter T) K)) ≃*
        ↥(alternatingGroup (Fin 6)))) ∧
    L₁Of L (fsuV1 T V) ≤ K ∧
    (Nonempty (↥(autOn K (conjClosure (quasithinOmegaOneCenter T) K)) ≃*
        ↥(alternatingGroup (Fin 6))) →
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(alternatingGroup (Fin 6)))) ∧
    ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ = ⁅reducedAggregate (K ⊔ T), K⁆ ∧
    (IsNat13410 K ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ∨
      (IsCore5 K ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ∧
        zpowers z = ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ⊓
          centralizer (K : Set G))) ∧
    Nat.card ↥(quasithinOmegaOneCenter T) = 4 ∧ quasithinOmegaOneCenter T = fsuV1 T V ∧
    Nat.card ↥(U3.cZ T L) = 2 ∧ U3.cZ T K = zpowers z ∧
    V ⊓ centralizer (L : Set G) = U3.cZ T L := by
  obtain ⟨hVKW, hWR, hZW, hL1, hcZ, htype⟩ := D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he
  have hcent : K ⊓ centralizer (conjClosure (quasithinOmegaOneCenter T) K : Set G) =
      K ⊓ centralizer (W : Set G) := by
    have h := cent_vH_eq D.isSylowTwoOf D.charTwo D.T_le_K
    rw [hVKW] at h
    have hKK : ∀ X : Subgroup G, K ⊓ ((K ⊔ T) ⊓ X) = K ⊓ X := fun X => by
      rw [← inf_assoc, inf_eq_left.2 (le_sup_left : K ≤ K ⊔ T)]
    rw [← hKK (centralizer (conjClosure (quasithinOmegaOneCenter T) K : Set G)), h, hKK]
  obtain ⟨e⟩ := autOn_mulEquiv_of_inf_eq (le_normalizer_conjClosure _ K) D.Wirr.2.2.1 hcent
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hcZ2 : Nat.card ↥(U3.cZ T K) ≤ 2 :=
    (show Nat.card ↥(U3.cZ T K) = 2 by rw [hcZ, D.card_zpowers_z]).le
  have hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) ≤ 4 := by
    refine card_Z_le_four D.TW hZW hcZ2 ?_
    rcases htype with ⟨-, hnat⟩ | ⟨-, h6 | hc⟩
    · exact Or.inl (card_cT_le_of_l32 D.Wirr.2.2.1 hnat D.isSylowTwoOf_inf)
    · obtain ⟨R⟩ := exists_rawData4 D.Wirr.2.2.1 h6.1
      obtain ⟨F⟩ := exists_frame4 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW
        D.isSylowTwoOf_inf
      exact Or.inl (card_cT_le_of_frame4 F)
    · obtain ⟨R⟩ := exists_rawData6 D.Wirr.2.2.1 hc.2.2
      obtain ⟨F⟩ := exists_frame5 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW
        D.isSylowTwoOf_inf
      refine Or.inr ⟨?_, card_cT_le_of_frame5 F⟩
      rw [hcZ, D.zpowers_eq_inf hcZ hc.2.1]
      exact inf_le_left
  obtain ⟨c7, c8, c9, c10, c11⟩ := five_six h1332 hC58 h317 h56 S D.exists_inH D.KM D.zV1.2
    D.z_ne_one D.Kz hZ4
  refine ⟨?_, hL1, ?_, hVKW.trans hWR.symm, ?_, c7, c8, c9, c10, c11⟩
  ·
    rcases htype with ⟨-, hnat⟩ | ⟨-, h6 | hc⟩
    · obtain ⟨f⟩ := autOn_mulEquiv_SL32 hnat
      exact Or.inl ⟨e.trans f⟩
    · obtain ⟨f⟩ := autOn_mulEquiv_alt (by norm_num) h6.1
      exact Or.inr ⟨e.trans f⟩
    · obtain ⟨f⟩ := autOn_mulEquiv_A6_of_core hc.2.2
      exact Or.inr ⟨e.trans f⟩
  ·
    intro hf
    obtain ⟨f⟩ := hf
    rcases htype with ⟨-, hnat⟩ | ⟨hK6, -⟩
    · exfalso
      have h1 := Nat.card_congr (e.symm.trans f).toEquiv
      rw [(card_autOn_of_module (K := K) (W := W)).2.2.2 hnat, h360] at h1
      omega
    · exact hK6
  ·
    rw [hVKW]
    rcases htype with ⟨-, hnat⟩ | ⟨-, h6 | hc⟩
    · exact Or.inl ⟨‹_›, Or.inl hnat⟩
    · exact Or.inl ⟨‹_›, Or.inr h6.1⟩
    · exact Or.inr ⟨⟨‹_›, hc.1, hc.2.2⟩, D.zpowers_eq_inf hcZ hc.2.1⟩

end Data13410

end CFSG.Quasithin.H13.NQS134

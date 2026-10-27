module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10SecQ4A2
public import CFSG.Quasithin.Vol2.Ch10SecQ4A7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

theorem zpow_two_eq_one_cases {M : Type*} [Group M] {a : M} (ha : a ^ 2 = 1) (n : ℤ) :
    a ^ n = 1 ∨ a ^ n = a := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, zpow_ofNat, ha, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, ha, one_zpow, one_mul, zpow_one]

variable {G : Type} [Group G] [Finite G] {K J : Subgroup G}

theorem pCore_le_ker_convHom (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G))
    (hW : IsElemAbelian 2 (conjClosure (blockU K) J)) :
    CFSG.pCore 2 ↥J ≤ (convHom hW J (le_normalizer_conjClosure _ J)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, convHom_apply, convI_eq_one_iff]
  refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
  exact (Subgroup.mem_centralizer_iff.mp (conjClosure_le_centralizer hK hKJ hQK hw) x
    (mem_blockQ_of_mem_pCore hx)).symm

@[expose] noncomputable def rhoW (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G))
    (hW : IsElemAbelian 2 (conjClosure (blockU K) J)) :
    ↥J ⧸ CFSG.pCore 2 ↥J →* MulAut (IntMod (conjClosure (blockU K) J) hW) :=
  QuotientGroup.lift _ (convHom hW J (le_normalizer_conjClosure _ J))
    (pCore_le_ker_convHom hK hKJ hQK hW)

theorem rhoW_mk (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G))
    (hW : IsElemAbelian 2 (conjClosure (blockU K) J)) (j : ↥J) :
    rhoW hK hKJ hQK hW (QuotientGroup.mk j) =
      convI hW ⟨j, le_normalizer_conjClosure _ J j.2⟩ := rfl

theorem rhoW_eq_one_iff (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G))
    (hW : IsElemAbelian 2 (conjClosure (blockU K) J)) (j : ↥J) :
    rhoW hK hKJ hQK hW (QuotientGroup.mk j) = 1 ↔
      (j : G) ∈ Subgroup.centralizer (conjClosure (blockU K) J : Set G) := by
  rw [rhoW_mk, convI_eq_one_iff]

theorem card_commV_le (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) (hUQ : blockU K ≤ pCoreOf 2 J)
    (hW : IsElemAbelian 2 (conjClosure (blockU K) J)) {k : G} (hk : k ∈ K)
    (hk2 : k ^ 2 ∈ pCoreOf 2 J) :
    Nat.card ↥(commV (Subgroup.zpowers (convI hW ⟨k, le_normalizer_conjClosure _ J (hKJ hk)⟩))) ≤
      Nat.card ↥(blockU K ⊓ Subgroup.centralizer ({k} : Set G)) := by
  set W := conjClosure (blockU K) J
  set β := convI hW ⟨k, le_normalizer_conjClosure _ J (hKJ hk)⟩ with hβ
  have hWQ : W ≤ pCoreOf 2 J := conjClosure_le_pCoreOf hUQ
  have hWC := conjClosure_le_centralizer (K := K) (J := J) hK hKJ hQK
  have hUW : blockU K ≤ W := le_conjClosure _ J
  have hβ2 : β ^ 2 = 1 := by
    rw [hβ, ← map_pow, convI_eq_one_iff]
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have := Subgroup.mem_centralizer_iff.mp (hWC hw) _ hk2
    simpa using this.symm
  let C : Subgroup (IntMod W hW) :=
    { carrier := {w | w.val ∈ blockU K ⊓ Subgroup.centralizer ({k} : Set G)}
      one_mem' := by simp only [Set.mem_ofPred_eq, IntMod.val_one]; exact Subgroup.one_mem _
      mul_mem' := fun ha hb => by
        simp only [Set.mem_ofPred_eq, IntMod.val_mul] at ha hb ⊢
        exact Subgroup.mul_mem _ ha hb
      inv_mem' := fun ha => by
        simp only [Set.mem_ofPred_eq, IntMod.val_inv] at ha ⊢
        exact Subgroup.inv_mem _ ha }
  have hle : commV (Subgroup.zpowers β) ≤ C := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, ⟨n, rfl⟩, w, rfl⟩
    rcases zpow_two_eq_one_cases hβ2 n with h | h
    · simp only [h, MulAut.one_apply, mul_inv_cancel]
      exact C.one_mem
    · simp only [h]
      show (β w * w⁻¹).val ∈ blockU K ⊓ Subgroup.centralizer ({k} : Set G)
      have hwW := IntMod.val_mem w
      rw [IntMod.val_mul, IntMod.val_inv, hβ, convI_apply_val]
      set a := k * w.val * k⁻¹ with ha
      have haW : a ∈ W := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure _ J (hKJ hk)) _).mp hwW
      refine ⟨commutator_mem_blockU_of_pCoreOf' hK hKJ hQK (hWQ hwW) hk,
        Subgroup.mem_centralizer_singleton_iff.mpr (Eq.symm ?_)⟩
      have hk2w : k ^ 2 * w.val = w.val * k ^ 2 := Subgroup.mem_centralizer_iff.mp (hWC hwW) _ hk2
      have hcomm := commute_of_mem_conjClosure hK hKJ hQK hUQ haW hwW
      have ha2 : a * a = 1 := by rw [← sq]; exact hW.2 a haW
      have hw2 : w.val * w.val = 1 := by rw [← sq]; exact hW.2 _ hwW
      have h1 : k * (a * w.val⁻¹) * k⁻¹ = w.val * a⁻¹ := by
        rw [ha]
        calc k * (k * w.val * k⁻¹ * w.val⁻¹) * k⁻¹ = (k ^ 2 * w.val) * k⁻¹ ^ 2 *
              (k * w.val⁻¹ * k⁻¹) := by rw [sq, sq]; group
          _ = w.val * (k * w.val * k⁻¹)⁻¹ := by rw [hk2w, sq, sq]; group
      have h2 : w.val * a⁻¹ = a * w.val⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hw2, hcomm]
      calc k * (a * w.val⁻¹) = (k * (a * w.val⁻¹) * k⁻¹) * k := by group
        _ = a * w.val⁻¹ * k := by rw [h1, h2]
  calc Nat.card ↥(commV (Subgroup.zpowers β)) ≤ Nat.card ↥C := Subgroup.card_le_of_le hle
    _ ≤ Nat.card ↥(blockU K ⊓ Subgroup.centralizer ({k} : Set G)) := by
      refine Nat.card_le_card_of_injective (fun w => ⟨w.1.val, w.2⟩) fun w w' h => ?_
      exact Subtype.ext (IntMod.val_injective (by simpa using congrArg Subtype.val h))

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

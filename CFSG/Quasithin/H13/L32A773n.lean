module

public import CFSG.Quasithin.H13.L32A773m

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf' {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(B ⊔ A) * Nat.card ↥(B ⊓ A) = Nat.card ↥B * Nat.card ↥A := by
  have h1 := B6.relIndex_inf_eq_relIndex_sup hB
  have h2 := Subgroup.relIndex_mul_card B (B ⊔ A)
  rw [inf_eq_left.mpr le_sup_left] at h2
  have h3 := Subgroup.relIndex_mul_card (B ⊓ A) A
  rw [inf_eq_left.mpr inf_le_right] at h3
  rw [← h2, ← h3, h1]
  ring

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem card_sL_inf_kz : Nat.card ↥(sL T L V ⊓ pCoreOf 2 (kz T V)) = 2 ^ 9 := by
  rw [← C.pCoreOf_hz_eq]
  exact C.card_sL_inf_QH

variable {k : G} (hk : k ∈ kz T V) (hkM : k ∉ m1 T L V)
include hk

omit [Finite G] C in
theorem conjSub_kz : conjSub k (pCoreOf 2 (kz T V)) = pCoreOf 2 (kz T V) :=
  conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 (kz T V) hk)

omit [Finite G] C in
theorem conj_inf_kz : (sL T L V).map (MulAut.conj k).toMonoidHom ⊓ pCoreOf 2 (kz T V) =
    conjSub k (sL T L V ⊓ pCoreOf 2 (kz T V)) := by
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective]
  congr 1
  exact (conjSub_kz hk).symm

include hkM

theorem pCoreOf_kz_eq_sup : pCoreOf 2 (kz T V) = (sL T L V ⊓ pCoreOf 2 (kz T V)) ⊔
    ((sL T L V).map (MulAut.conj k).toMonoidHom ⊓ pCoreOf 2 (kz T V)) := by
  set A := sL T L V ⊓ pCoreOf 2 (kz T V) with hA
  set B := (sL T L V).map (MulAut.conj k).toMonoidHom ⊓ pCoreOf 2 (kz T V) with hB
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hO := C.pCoreOf_hz_eq
  have hA9 : Nat.card ↥A = 2 ^ 9 := C.card_sL_inf_kz
  have hB9 : Nat.card ↥B = 2 ^ 9 := by
    rw [hB, conj_inf_kz hk, conjSub, Subgroup.card_map_of_injective (MulAut.conj k).injective,
      hA9]
  have hAB : B ⊓ A = sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom := by
    rw [hA, hB, C.sL_inf_conj_eq hk hkM]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxSk, hxO⟩, hxS, -⟩
      exact ⟨hxO, by
        have := (C.sL_inf_conj_eq hk hkM ▸ Subgroup.mem_inf.mpr ⟨hxS, hxSk⟩ :
          x ∈ pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))
        exact (Subgroup.mem_inf.mp this).2⟩
    · rintro ⟨hxO, hxC⟩
      have hx : x ∈ sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom := by
        rw [C.sL_inf_conj_eq hk hkM]
        exact Subgroup.mem_inf.mpr ⟨hxO, hxC⟩
      exact ⟨⟨(Subgroup.mem_inf.mp hx).2, hxO⟩, (Subgroup.mem_inf.mp hx).1, hxO⟩
  have hAB7 : Nat.card ↥(B ⊓ A) = 2 ^ 7 := by
    rw [hAB, C.sL_inf_conj_eq hk hkM, ← hO]
    exact C.card_CU
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    have hbO := (Subgroup.mem_inf.mp hb).2
    have hbQ : b ∈ pCoreOf 2 (hz T V) := by rw [hO]; exact hbO
    refine le_normalizer_of_conj_mem' (H := Subgroup.normalizer (sL T L V : Set G) ⊓
      Subgroup.normalizer (pCoreOf 2 (kz T V) : Set G)) (fun g hg x hx => ?_)
      (Subgroup.mem_inf.mpr ⟨C.T_le_normalizer_sL (pCoreOf_le_of_le C.hyp hTH hbQ),
        Subgroup.le_normalizer hbO⟩)
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hg).1 x).mp
      (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hg).2 x).mp
      (Subgroup.mem_inf.mp hx).2⟩
  have hprod := card_sup_mul_card_inf' hBN
  rw [hAB7, hA9, hB9] at hprod
  have hsup : Nat.card ↥(B ⊔ A) = 2 ^ 11 := by omega
  have hle : A ⊔ B ≤ pCoreOf 2 (kz T V) := sup_le inf_le_right inf_le_right
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [sup_comm, hsup, ← hO, C.card_QH]

theorem isElemSection_kz : IsElemSection (pCoreOf 2 (kz T V)) (fsuU T V) := by
  have hO := C.pCoreOf_hz_eq
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  have hUO : fsuU T V ≤ pCoreOf 2 (kz T V) := by
    rw [← hO]
    exact fun u hu => (Subgroup.mem_inf.mp (C.fsuU_le_CU hu)).1
  have hUn : ∀ x ∈ pCoreOf 2 (kz T V), ∀ u ∈ fsuU T V, x * u * x⁻¹ ∈ fsuU T V := fun x hx u hu =>
    (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU
      (pCoreOf_le 2 _ (by rw [hO]; exact hx))) u).mp hu
  have hdec := C.pCoreOf_kz_eq_sup hk hkM
  have hA : ∀ x ∈ pCoreOf 2 (kz T V), ∀ a ∈ sL T L V ⊓ pCoreOf 2 (kz T V),
      x * a * x⁻¹ * a⁻¹ ∈ fsuU T V := fun x hx a ha => by
    rw [← hO] at hx ha
    exact C.comm_mem_fsuU_QH hx ha
  have hB : ∀ x ∈ pCoreOf 2 (kz T V),
      ∀ b ∈ (sL T L V).map (MulAut.conj k).toMonoidHom ⊓ pCoreOf 2 (kz T V),
      x * b * x⁻¹ * b⁻¹ ∈ fsuU T V := fun x hx b hb => by
    rw [conj_inf_kz hk, mem_conjSub] at hb
    have hx' : k⁻¹ * x * k ∈ pCoreOf 2 (kz T V) := by
      rw [← conjSub_kz hk, mem_conjSub] at hx
      exact hx
    have h1 := hA _ hx' _ hb
    have h2 := (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU hkH) _).mp h1
    convert h2 using 1
    group
  refine ⟨hUO, fun x hx x' hx' => ⟨?_, ?_⟩⟩
  ·
    let Z : Subgroup G :=
      { carrier := {y | y ∈ pCoreOf 2 (kz T V) ∧ x * y * x⁻¹ * y⁻¹ ∈ fsuU T V}
        one_mem' := ⟨one_mem _, by simp⟩
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          rw [show x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) by group]
          exact mul_mem ha.2 (hUn a ha.1 _ hb.2)⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
          rw [show x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ by group]
          exact hUn _ (inv_mem ha.1) _ (inv_mem ha.2)⟩ }
    have hZ : pCoreOf 2 (kz T V) ≤ Z := by
      rw [hdec]
      exact sup_le (fun a ha => ⟨(Subgroup.mem_inf.mp ha).2, hA x hx a ha⟩)
        (fun b hb => ⟨(Subgroup.mem_inf.mp hb).2, hB x hx b hb⟩)
    exact (hZ hx').2
  ·
    have hcomm : ∀ a ∈ pCoreOf 2 (kz T V), ∀ b ∈ pCoreOf 2 (kz T V),
        a * b * a⁻¹ * b⁻¹ ∈ fsuU T V := by
      intro a ha b hb
      let Z : Subgroup G :=
        { carrier := {y | y ∈ pCoreOf 2 (kz T V) ∧ a * y * a⁻¹ * y⁻¹ ∈ fsuU T V}
          one_mem' := ⟨one_mem _, by simp⟩
          mul_mem' := fun {c d} hc hd => ⟨mul_mem hc.1 hd.1, by
            rw [show a * (c * d) * a⁻¹ * (c * d)⁻¹ =
              (a * c * a⁻¹ * c⁻¹) * (c * (a * d * a⁻¹ * d⁻¹) * c⁻¹) by group]
            exact mul_mem hc.2 (hUn c hc.1 _ hd.2)⟩
          inv_mem' := fun {c} hc => ⟨inv_mem hc.1, by
            rw [show a * c⁻¹ * a⁻¹ * c⁻¹⁻¹ = c⁻¹ * (a * c * a⁻¹ * c⁻¹)⁻¹ * c⁻¹⁻¹ by group]
            exact hUn _ (inv_mem hc.1) _ (inv_mem hc.2)⟩ }
      have hZ : pCoreOf 2 (kz T V) ≤ Z := by
        rw [hdec]
        exact sup_le (fun c hc => ⟨(Subgroup.mem_inf.mp hc).2, hA a ha c hc⟩)
          (fun c hc => ⟨(Subgroup.mem_inf.mp hc).2, hB a ha c hc⟩)
      exact (hZ hb).2
    let Sq : Subgroup G :=
      { carrier := {y | y ∈ pCoreOf 2 (kz T V) ∧ y ^ 2 ∈ fsuU T V}
        one_mem' := ⟨one_mem _, by simp⟩
        mul_mem' := fun {c d} hc hd => ⟨mul_mem hc.1 hd.1, by
          rw [show (c * d) ^ 2 = c ^ 2 * (c⁻¹ * d * c⁻¹⁻¹ * d⁻¹) * d ^ 2 by
            simp only [pow_two]; group]
          exact mul_mem (mul_mem hc.2 (hcomm _ (inv_mem hc.1) _ hd.1)) hd.2⟩
        inv_mem' := fun {c} hc => ⟨inv_mem hc.1, by
          rw [inv_pow]
          exact inv_mem hc.2⟩ }
    have hSq : pCoreOf 2 (kz T V) ≤ Sq := by
      rw [hdec]
      refine sup_le (fun a ha => ⟨(Subgroup.mem_inf.mp ha).2,
        v_le_fsuU (C.sq_mem C.u0_eq (Subgroup.mem_inf.mp ha).1)⟩) fun b hb => ?_
      refine ⟨(Subgroup.mem_inf.mp hb).2, ?_⟩
      have hb' := hb
      rw [conj_inf_kz hk, mem_conjSub] at hb'
      have h1 : (k⁻¹ * b * k) ^ 2 ∈ fsuU T V :=
        v_le_fsuU (C.sq_mem C.u0_eq (Subgroup.mem_inf.mp hb').1)
      have h2 := (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU hkH) _).mp h1
      convert h2 using 1
      rw [show (k⁻¹ * b * k) ^ 2 = k⁻¹ * b ^ 2 * k by simp only [pow_two]; group]
      group
    exact (hSq hx).2

end Ctx73

end CFSG.Quasithin.H13.L32A

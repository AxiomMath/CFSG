module

public import CFSG.Quasithin.H13.L32A774f
public import CFSG.Quasithin.H13.L32A774b
public import CFSG.Quasithin.H13.L32A774e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem eq_one_of_mem_fsuU {u : G} (hu : u ∈ fsuU T V) (huL : ∀ l ∈ L, l * u = u * l) :
    u = 1 := by
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  have huV1 := C.mem_fsuV1_of_comm hxL1 hx3 hx1 hu (by
    rw [huL x hxL, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _)
  have h1 : u ∈ V ⊓ Subgroup.centralizer (L : Set G) := Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_inf.mp huV1).1, Subgroup.mem_centralizer_iff.mpr fun l hl => huL l hl⟩
  rw [C.hyp.inf_centralizer_eq_bot C.h13322 C.hMod] at h1
  exact h1

theorem odd_relIndex_kz : Odd ((T ⊓ kz T V).relIndex (kz T V)) := by
  have hT := C.hyp.fsu.sylow
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hTK : T ≤ Subgroup.normalizer (kz T V : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper (hz T V))
  rw [B6.relIndex_inf_eq_relIndex_sup hTK]
  have hle : T ⊔ kz T V ≤ hz T V := sup_le hTH (oTwoUpper_le _)
  have h1 := Subgroup.relIndex_mul_relIndex T (T ⊔ kz T V) (hz T V) le_sup_left hle
  have h2 : ¬ 2 ∣ T.relIndex (hz T V) := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTH]
    exact Dvd.dvd.mul_right hd _
  rw [Nat.odd_iff]
  by_contra h
  apply h2
  rw [← h1]
  exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega)) _

theorem eq_one_of_mem_pCoreOf {c : G} (hc : c ∈ pCoreOf 2 L) (hcL : ∀ l ∈ L, l * c = c * l) :
    c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hKU : kz T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    hKH.trans C.hz_le_normalizer_fsuU
  let Z₀ : Subgroup G := pCoreOf 2 L ⊓ Subgroup.centralizer (L : Set G)
  have hmemZ : ∀ {y : G}, y ∈ Z₀ ↔ y ∈ pCoreOf 2 L ∧ ∀ l ∈ L, l * y = y * l := fun {y} => by
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hZK : ∀ y ∈ Z₀, ∀ k ∈ kz T V, k * y = y * k := by
    intro y hy
    obtain ⟨hyP, hyL⟩ := hmemZ.mp hy
    have hyL' : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ V := fun l hl => by
      rw [hyL l hl, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    have hyS : ∀ s ∈ sL T L V, y * s = s * y := fun s hs => C.comm_sL_eq_one hyP hyL' hs
    have hyU : ∀ u ∈ fsuU T V, y * u = u * y := fun u hu => hyS u (le_conjClosure _ _ hu)
    have hyV : y ∈ Subgroup.centralizer (V : Set G) := by
      rw [C.pCoreOf_eq] at hyP
      exact (Subgroup.mem_inf.mp hyP).2
    have hyH : y ∈ hz T V := by
      show y ∈ Subgroup.centralizer (fsuV1 T V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_iff.mp hyV w (Subgroup.mem_inf.mp hw).1
    have hyQ := C.mem_QH_of hyH hyU
    have hyC : y ∈ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun u hu => (hyU u hu).symm⟩
    have hκU : ∀ k ∈ kz T V, k * y * k⁻¹ * y⁻¹ ∈ fsuU T V := fun k hk => by
      have h := (C.l71 G T L V C.hyp).1.2 (Subgroup.commutator_mem_commutator hyC hk)
      have := inv_mem h
      rwa [commutatorElement_def, show (y * k * y⁻¹ * k⁻¹)⁻¹ = k * y * k⁻¹ * y⁻¹ by group]
        at this
    have hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a := fun a ha b hb =>
      F7.isElemAbelian_comm hUe ha hb
    obtain ⟨a, haU, ha⟩ := exists_coboundary_of_odd (K := kz T V) (X := T ⊓ kz T V)
      (A := fsuU T V) (B := ⊥) C.odd_relIndex_kz hUc
      (fun a ha => by rw [← pow_two]; exact F7.isElemAbelian_pow_eq_one hUe ha) bot_le hKU
      (fun g _ => by
        rw [Subgroup.mem_normalizer_iff]
        intro w
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl
          group
        · intro h
          calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group)
      (fun k => k * y * k⁻¹ * y⁻¹) hκU
      (fun k hk k' hk' => by
        have h1 := hUc _ (hκU k hk) _
          ((Subgroup.mem_normalizer_iff.mp (hKU hk) _).mp (hκU k' hk'))
        calc k * k' * y * (k * k')⁻¹ * y⁻¹ =
            (k * (k' * y * k'⁻¹ * y⁻¹) * k⁻¹) * (k * y * k⁻¹ * y⁻¹) := by group
          _ = (k * y * k⁻¹ * y⁻¹) * (k * (k' * y * k'⁻¹ * y⁻¹) * k⁻¹) := h1.symm)
      (fun t ht => by
        obtain ⟨htT, htK⟩ := Subgroup.mem_inf.mp ht
        have htL : t ∈ Subgroup.normalizer (L : Set G) := C.hyp.normalizes C.h13322 htT
        rw [Subgroup.mem_bot]
        refine C.eq_one_of_mem_fsuU (hκU t htK) fun l hl => ?_
        have hl' : t⁻¹ * l * t ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem htL) l).mp hl
          simpa using this
        have h1 := hyL _ hl'
        calc l * (t * y * t⁻¹ * y⁻¹) = t * ((t⁻¹ * l * t) * y) * t⁻¹ * y⁻¹ := by group
          _ = t * (y * (t⁻¹ * l * t)) * t⁻¹ * y⁻¹ := by rw [h1]
          _ = (t * y * t⁻¹) * l * y⁻¹ := by group
          _ = (t * y * t⁻¹) * (y⁻¹ * (y * l * y⁻¹)) := by group
          _ = (t * y * t⁻¹) * (y⁻¹ * l) := by
            rw [← hyL l hl, mul_inv_cancel_right]
          _ = (t * y * t⁻¹ * y⁻¹) * l := by group)
    simp only [Subgroup.mem_bot] at ha
    obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
    have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
    have hxK : x ∈ kz T V := l1_le_kz C.hyp C.hMod hxL1
    have hκx : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [hyL x hxL, mul_inv_cancel_right, mul_inv_cancel]
    have hax : x * a * x⁻¹ = a := by
      have h1 := ha x hxK
      rw [hκx, one_mul, inv_eq_one, mul_inv_eq_one] at h1
      exact h1.symm
    have haV1 : a ∈ fsuV1 T V := C.mem_fsuV1_of_comm hxL1 hx3 hx1 haU (by
      rw [hax, mul_inv_cancel]
      exact one_mem _)
    intro k hk
    have hka : k * a * k⁻¹ = a := by
      rw [(Subgroup.mem_centralizer_iff.mp (hKH hk) a haV1).symm, mul_inv_cancel_right]
    have h1 := ha k hk
    rw [hka, mul_inv_cancel, inv_one, mul_one] at h1
    calc k * y = (k * y * k⁻¹ * y⁻¹) * y * k := by group
      _ = y * k := by rw [h1, one_mul]
  have hZn : (L ⊔ T) ⊔ hz T V ≤ Subgroup.normalizer (Z₀ : Set G) := by
    have hH : hz T V = kz T V ⊔ T := (C.h63 G T L V C.hyp).2.2.1
    have hL : L ≤ Subgroup.normalizer (Z₀ : Set G) :=
      le_normalizer_of_conj_mem' fun l hl y hy => by
        rw [(hmemZ.mp hy).2 l hl, mul_inv_cancel_right]
        exact hy
    have hT : T ≤ Subgroup.normalizer (Z₀ : Set G) :=
      le_normalizer_of_conj_mem' fun t ht y hy => by
        obtain ⟨hyP, hyL⟩ := hmemZ.mp hy
        have htL : t ∈ Subgroup.normalizer (L : Set G) := C.hyp.normalizes C.h13322 ht
        refine hmemZ.mpr ⟨(Subgroup.mem_normalizer_iff.mp
          (F7.le_normalizer_pCoreOf_of_le_normalizer (C.hyp.normalizes C.h13322) ht) y).mp hyP,
          fun l hl => ?_⟩
        have hl' : t⁻¹ * l * t ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem htL) l).mp hl
          simpa using this
        have h1 := hyL _ hl'
        calc l * (t * y * t⁻¹) = t * ((t⁻¹ * l * t) * y) * t⁻¹ := by group
          _ = t * (y * (t⁻¹ * l * t)) * t⁻¹ := by rw [h1]
          _ = t * y * t⁻¹ * l := by group
    have hK : kz T V ≤ Subgroup.normalizer (Z₀ : Set G) :=
      le_normalizer_of_conj_mem' fun k hk y hy => by
        rw [hZK y hy k hk, mul_inv_cancel_right]
        exact hy
    rw [hH]
    exact sup_le (sup_le hL hT) (sup_le hK hT)
  have hZle : Z₀ ≤ pCoreOf 2 ((L ⊔ T) ⊔ hz T V) :=
    le_pCoreOf_of_le_normalizer 2
      (inf_le_left.trans ((pCoreOf_le 2 L).trans (le_sup_left.trans le_sup_left))) hZn
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left)
  rw [C.hF.o2_trivial] at hZle
  exact hZle (hmemZ.mpr ⟨hc, hcL⟩)

end Ctx73

end CFSG.Quasithin.H13.L32A

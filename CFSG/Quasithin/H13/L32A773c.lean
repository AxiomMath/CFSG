module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32A774g
public import CFSG.Quasithin.H13.L32A774h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem Q_le_R1 : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := L32NSet14.Setting.L1_le.trans inf_le_left
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := by
    rw [← C.hF.cT]
    exact inf_le_left
  exact le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
    ((sup_le_sup_right hL1L T).trans (le_normalizer_pCoreOf 2 (L ⊔ T)))
    (pCoreOf_isPGroup 2 (L ⊔ T))

theorem comm_mem_v_Q_sL {q s : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hs : s ∈ sL T L V) :
    q * s * q⁻¹ * s⁻¹ ∈ V := by
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hR1 := C.commutator_fsuU_le_v C.u0_eq
  have hSV := C.sL_le_normalizer
  have hS : s ∈ Subgroup.closure {x | ∃ h ∈ L, ∃ z ∈ fsuU T V, h * z * h⁻¹ = x} := hs
  clear hs
  induction hS using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, u, hu, rfl⟩ := hx
    have hkV : k ∈ Subgroup.normalizer (V : Set G) := hLTV (Subgroup.mem_sup_left hk)
    have hq' : k⁻¹ * q * k ∈ pCoreOf 2 (L ⊔ T) := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((le_normalizer_pCoreOf 2 (L ⊔ T)) (Subgroup.mem_sup_left (inv_mem hk))) q).mp hq
      simpa using this
    have h1 := hR1 (Subgroup.commutator_mem_commutator hu (C.Q_le_R1 hq'))
    rw [commutatorElement_def] at h1
    have h2 := (Subgroup.mem_normalizer_iff.mp hkV _).mp (inv_mem h1)
    convert h2 using 1
    group
  | one => simp
  | mul a b ha hb iha ihb =>
    have haV := hSV ha
    rw [show q * (a * b) * q⁻¹ * (a * b)⁻¹ =
      (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) by group]
    exact mul_mem iha ((Subgroup.mem_normalizer_iff.mp haV _).mp ihb)
  | inv a ha iha =>
    have haV := hSV ha
    rw [show q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem haV) _).mp (inv_mem iha)

theorem mem_centralizer_of_mem_Q {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) :
    q ∈ Subgroup.centralizer (V : Set G) :=
  C.Q_le_centralizer hq

theorem comm_sL_eq_one_Q {p : G} (hp : p ∈ pCoreOf 2 (L ⊔ T))
    (hpL : ∀ l ∈ L, l * p * l⁻¹ * p⁻¹ ∈ V) {s : G} (hs : s ∈ sL T L V) : p * s = s * p := by
  have hLV := C.L_le_normalizer_V
  have key : ∀ l ∈ L, ∀ u ∈ fsuU T V, p * (l * u * l⁻¹) = (l * u * l⁻¹) * p := by
    intro l hl u hu
    obtain ⟨q, hq⟩ : ∃ q, q = l⁻¹ * p * l := ⟨_, rfl⟩
    have hqQ : q ∈ pCoreOf 2 (L ⊔ T) := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((le_normalizer_pCoreOf 2 (L ⊔ T)) (Subgroup.mem_sup_left (inv_mem hl))) p).mp hp
      rw [hq]
      simpa using this
    have hqL : ∀ l' ∈ L, l' * q * l'⁻¹ * q⁻¹ ∈ V := by
      intro l' hl'
      have h1 := hpL (l * l' * l⁻¹) (mul_mem (mul_mem hl hl') (inv_mem hl))
      have h2 := (Subgroup.mem_normalizer_iff.mp (hLV (inv_mem hl)) _).mp h1
      rwa [show l⁻¹ * (l * l' * l⁻¹ * p * (l * l' * l⁻¹)⁻¹ * p⁻¹) * l⁻¹⁻¹ =
        l' * q * l'⁻¹ * q⁻¹ by rw [hq]; group] at h2
    have h := C.comm_eq_one_of_comm_mem (C.mem_centralizer_of_mem_Q hqQ)
      (fun u hu => C.comm_mem_v_Q_sL hqQ (le_conjClosure _ _ hu)) hqL hu
    calc p * (l * u * l⁻¹) = l * (q * u) * l⁻¹ := by rw [hq]; group
      _ = l * (u * q) * l⁻¹ := by rw [h]
      _ = (l * u * l⁻¹) * p := by rw [hq]; group
  have hs' : s ∈ Subgroup.closure {y | ∃ l ∈ L, ∃ u ∈ fsuU T V, l * u * l⁻¹ = y} := hs
  clear hs
  induction hs' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, u, hu, rfl⟩ := hy
    exact key l hl u hu
  | one => simp
  | mul a b _ _ iha ihb =>
    calc p * (a * b) = (p * a) * b := by group
      _ = a * (p * b) := by rw [iha]; group
      _ = a * b * p := by rw [ihb]; group
  | inv a _ iha =>
    calc p * a⁻¹ = a⁻¹ * (a * p) * a⁻¹ := by group
      _ = a⁻¹ * (p * a) * a⁻¹ := by rw [iha]
      _ = a⁻¹ * p := by group

theorem eq_one_of_mem_Q {c : G} (hc : c ∈ pCoreOf 2 (L ⊔ T)) (hcL : ∀ l ∈ L, l * c = c * l) :
    c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hKU : kz T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    hKH.trans C.hz_le_normalizer_fsuU
  let Z₀ : Subgroup G := pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G)
  have hmemZ : ∀ {y : G}, y ∈ Z₀ ↔ y ∈ pCoreOf 2 (L ⊔ T) ∧ ∀ l ∈ L, l * y = y * l :=
    fun {y} => by
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      rfl
  have hZK : ∀ y ∈ Z₀, ∀ k ∈ kz T V, k * y = y * k := by
    intro y hy
    obtain ⟨hyQ, hyL⟩ := hmemZ.mp hy
    have hyS : ∀ s ∈ sL T L V, y * s = s * y := fun s hs =>
      (hyL s (C.sL_le_L C.u0_eq hs)).symm
    have hyU : ∀ u ∈ fsuU T V, y * u = u * y := fun u hu => hyS u (le_conjClosure _ _ hu)
    have hyV := C.mem_centralizer_of_mem_Q hyQ
    have hyH : y ∈ hz T V := by
      show y ∈ Subgroup.centralizer (fsuV1 T V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_iff.mp hyV w (Subgroup.mem_inf.mp hw).1
    have hyQH := C.mem_QH_of hyH hyU
    have hyC : y ∈ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyQH, Subgroup.mem_centralizer_iff.mpr fun u hu => (hyU u hu).symm⟩
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
        obtain ⟨hyQ, hyL⟩ := hmemZ.mp hy
        have htL : t ∈ Subgroup.normalizer (L : Set G) := C.hyp.normalizes C.h13322 ht
        refine hmemZ.mpr ⟨(Subgroup.mem_normalizer_iff.mp
          ((le_normalizer_pCoreOf 2 (L ⊔ T)) (Subgroup.mem_sup_right ht)) y).mp hyQ,
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
      (inf_le_left.trans ((pCoreOf_le 2 (L ⊔ T)).trans le_sup_left)) hZn
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_left)
  rw [C.hF.o2_trivial] at hZle
  exact hZle (hmemZ.mpr ⟨hc, hcL⟩)

end Ctx73

end CFSG.Quasithin.H13.L32A

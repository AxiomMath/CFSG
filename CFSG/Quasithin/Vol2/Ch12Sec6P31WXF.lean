module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXE

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  Equiv
open scoped IsMulCommutative

structure SingleData' (Y : Type) [Group Y] (Ts Ms Ls Tls X : Subgroup Y) : Prop where
  threeRank : P31D.ThreeRankLE2 Y
  sylow : IsSylowTwoOf Ts ⊤
  three : 3 ∣ Nat.card ↥X
  normal : X.Normal
  Ts_le : Ts ≤ Ms
  borel_le : borel X Ts ≤ Ms
  not_le : ¬ X ≤ Ms
  Ls_le : Ls ≤ Ms
  Ls_solvable : Group.IsSolvable ↥Ls
  Ts_norm_Ls : Ts ≤ Subgroup.normalizer (Ls : Set Y)
  Tls_le : Tls ≤ Ts
  f7 : ∃ r ∈ Tls, ∃ S : Subgroup Y, S ≤ Ls ∧ IsElemAbelian 3 S ∧ Nat.card S = 9 ∧
    ∀ s ∈ S, r * s * r⁻¹ * s ∈ pCoreOf 2 Ls

section Prep

variable {Y : Type} [Group Y] [Finite Y]

theorem single_prep' {Ts Ms Ls Tls X : Subgroup Y} (h : SingleData' Y Ts Ms Ls Tls X)
    (hcoat : IsCoatom ((borel X Ts).subgroupOf X))
    (hcyc : ∃ g ∈ borel X Ts, ∀ b ∈ borel X Ts, ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ Ts ⊓ X)
    (hfrob : ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓
        Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y),
      ∃ j : ℕ, ∀ b ∈ borel X Ts, r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ Ts ⊓ X) :
    ∃ (r : Y) (j : ℕ) (c : Y), r ∈ Tls ∧ Odd j ∧ c ∈ borel X Ts ∧ c ∉ Ts ⊓ X ∧ c ^ 3 = 1 ∧
      (∀ b ∈ borel X Ts, r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ Ts ⊓ X) ∧
      (9 ∣ Nat.card ↥(borel X Ts) → 27 ∣ Nat.card ↥Ms) := by
  obtain ⟨hR, hTs, hP, hnormal, hTsMs, hBM, hKM, hLM, -, -, hTlsTs, r, hrTls, S, hSL, hSe, hS9, hSinv⟩ := h
  haveI : X.Normal := hnormal
  have hXn : ∀ x : Y, x ∈ Subgroup.normalizer (X : Set Y) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.2 hnormal]
    exact Subgroup.mem_top x
  have hMB : Ms ⊓ X = borel X Ts := by
    rcases P31Grp.eq_or_eq_of_isCoatom_subgroupOf hcoat (le_inf hBM inf_le_left)
      (inf_le_right : Ms ⊓ X ≤ X) with h1 | h1
    · exact h1
    · exact absurd (inf_eq_right.1 h1) hKM
  have hSylX : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal hTs le_top Subgroup.le_normalizer_of_normal
  have hUB : Ts ⊓ X ≤ borel X Ts := le_inf inf_le_right Subgroup.le_normalizer
  have hBN : borel X Ts ≤ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := inf_le_right
  have hSylB : IsSylowTwoOf (Ts ⊓ X) (borel X Ts) :=
    A4.isSylowTwoOf_mono hSylX hUB inf_le_left
  have hS3 : ∀ x ∈ S, x ^ 3 = 1 := hSe.2
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hSe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hSp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hS3 g g.2)⟩
  obtain ⟨y, hyX, hyo, hyc⟩ := exists_centralizes_order_three hSp
    (fun s _ => hXn s) hP
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyo; omega
  have hyS : y ∈ S := by
    by_contra hyS
    obtain ⟨u, v, huS, hvS, hu1, hu3, hv3, hvu⟩ := exists_indep_pair hSe hS9
    have hcu : Commute u y := by
      have := hyc u huS
      exact (calc u * y = (u * y * u⁻¹) * u := by group
        _ = y * u := by rw [this])
    have hcv : Commute v y := by
      have := hyc v hvS
      exact (calc v * y = (v * y * v⁻¹) * v := by group
        _ = y * v := by rw [this])
    have hcuv : Commute u v := hScomm u huS v hvS
    refine hR u v y hu3 hv3 hy3 hcuv hcu hcv ?_
    intro a b c habc
    have hyc' : y ^ c = (u ^ a * v ^ b)⁻¹ := eq_inv_of_mul_eq_one_right habc
    have hmem : y ^ c ∈ S := by
      rw [hyc']
      exact S.inv_mem (S.mul_mem (S.pow_mem huS a) (S.pow_mem hvS b))
    have h3c : 3 ∣ c := by
      by_contra h3c
      apply hyS
      have hmod : c % 3 = 1 ∨ c % 3 = 2 := by omega
      have hpow : y ^ c = y ^ (c % 3) := by
        conv_lhs => rw [← Nat.div_add_mod c 3, pow_add, pow_mul, hy3, one_pow, one_mul]
      rcases hmod with h1 | h1
      · rw [hpow, h1, pow_one] at hmem
        exact hmem
      · rw [hpow, h1] at hmem
        have : y = (y ^ 2) ^ 2 := by
          calc y = y ^ 3 * y := by rw [hy3, one_mul]
            _ = (y ^ 2) ^ 2 := by group
        rw [this]
        exact S.pow_mem hmem 2
    have hyc1 : y ^ c = 1 := by
      obtain ⟨t, rfl⟩ := h3c
      rw [pow_mul, hy3, one_pow]
    rw [hyc1] at hyc'
    obtain ⟨ha, hb⟩ := indep_of_not_mem_zpowers hu3 hu1 hv3 hvu (inv_eq_one.1 hyc'.symm)
    exact ⟨ha, hb, h3c⟩
  have hcB : y ∈ borel X Ts := by
    rw [← hMB]
    exact ⟨hLM (hSL hyS), hyX⟩
  have hrTs : r ∈ Ts := hTlsTs hrTls
  have hrU : r ∈ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hrTs) x
    have h2 := Subgroup.mem_normalizer_iff.1 (hXn r) x
    exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
  have hO2 : pCoreOf 2 Ls ⊓ X ≤ Ts ⊓ X := by
    refine le_of_normal_sylow hSylB hBN ?_ (pCoreOf_isPGroup 2 Ls).to_inf_left
    rw [← hMB]
    exact le_inf (inf_le_left.trans ((pCoreOf_le 2 Ls).trans hLM)) inf_le_right
  have hcU : y ∉ Ts ⊓ X := fun hh => hy1 (eq_one_of_pow_three hTs.2.1 hh.1 hy3)
  have hinvU : r * y * r⁻¹ * y ∈ Ts ⊓ X := by
    have h1 := hSinv y hyS
    refine hO2 ⟨h1, ?_⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 (hXn r) y).1 hyX
    exact X.mul_mem h2 hyX
  obtain ⟨j, hj⟩ := hfrob r ⟨hXn r, hrU⟩
  have hjodd : Odd j := by
    by_contra hje
    rw [Nat.not_odd_iff_even] at hje
    have h3j : 3 ∣ 2 ^ j - 1 := P31NT.three_dvd_two_pow_sub_one_iff.2 hje
    have hpow : y ^ (2 ^ j) = y := by
      obtain ⟨t', ht'⟩ := h3j
      have h2j : 2 ^ j = 3 * t' + 1 := by
        have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
      rw [h2j, pow_succ, pow_mul, hy3, one_pow, one_mul]
    have h1 := hj y hcB
    rw [hpow] at h1
    have h2 : y * y ∈ Ts ⊓ X := by
      have e : y * y = (r * y * r⁻¹ * y⁻¹)⁻¹ * (r * y * r⁻¹ * y) := by group
      rw [e]
      exact (Ts ⊓ X).mul_mem ((Ts ⊓ X).inv_mem h1) hinvU
    apply hcU
    have e : y = (y * y)⁻¹ := by
      calc y = (y * y)⁻¹ * (y * y * y) := by group
        _ = (y * y)⁻¹ := by rw [← pow_three', hy3, mul_one]
    rw [e]
    exact (Ts ⊓ X).inv_mem h2
  refine ⟨r, j, y, hrTls, hjodd, hcB, hcU, hy3, hj, ?_⟩
  intro h9
  have hSN : S ≤ Subgroup.normalizer ((borel X Ts : Subgroup Y) : Set Y) := by
    rw [← hMB]
    intro s hs
    have hsM : s ∈ Ms := hLM (hSL hs)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hXn s) x
    exact ⟨fun hx => ⟨Ms.mul_mem (Ms.mul_mem hsM hx.1) (Ms.inv_mem hsM), h1.1 hx.2⟩,
      fun hx => ⟨by simpa [mul_assoc] using Ms.mul_mem (Ms.mul_mem (Ms.inv_mem hsM) hx.1) hsM,
        h1.2 hx.2⟩⟩
  have hW3 : Nat.card ↥(borel X Ts ⊓ S) = 3 := by
    have hWB : borel X Ts ⊓ S ≤ borel X Ts := inf_le_left
    have hle : Nat.card ↥(borel X Ts ⊓ S) ≤ 3 := by
      refine card_le_three_of_cyclic hUB hBN hcyc hWB (fun w hw => hS3 w hw.2) ?_
      rw [eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_bot]
      exact eq_one_of_pow_three hTs.2.1 (hw.2.1) (hS3 w hw.1.2)
    have hdvd : Nat.card ↥(borel X Ts ⊓ S) ∣ 9 := hS9 ▸ Subgroup.card_dvd_of_le inf_le_right
    have hne : Nat.card ↥(borel X Ts ⊓ S) ≠ 1 := by
      intro h1
      have hmem : y ∈ borel X Ts ⊓ S := ⟨hcB, hyS⟩
      have := Subgroup.eq_bot_of_card_eq _ h1
      rw [this, Subgroup.mem_bot] at hmem
      exact hy1 hmem
    have hpos : 0 < Nat.card ↥(borel X Ts ⊓ S) := Nat.card_pos
    interval_cases hh : Nat.card ↥(borel X Ts ⊓ S)
    · omega
    · omega
    · rfl
  have hcard := card_sup_mul_card_inf hSN
  rw [hW3, hS9] at hcard
  have hSBM : S ⊔ borel X Ts ≤ Ms := sup_le (hSL.trans hLM) hBM
  have h27 : 27 ∣ Nat.card ↥(S ⊔ borel X Ts) := by
    have h3 : 3 * Nat.card ↥(S ⊔ borel X Ts) = 9 * Nat.card ↥(borel X Ts) := by
      calc 3 * Nat.card ↥(S ⊔ borel X Ts) = Nat.card ↥(S ⊔ borel X Ts) * 3 := by ring
        _ = 9 * Nat.card ↥(borel X Ts) := hcard
    obtain ⟨t, ht⟩ := h9
    refine ⟨t, ?_⟩
    omega
  exact h27.trans (Subgroup.card_dvd_of_le hSBM)


theorem permData_of_single' {Ts Ms Ls Tls X : Subgroup Y} (h : SingleData' Y Ts Ms Ls Tls X)
    (hcoat : IsCoatom ((borel X Ts).subgroupOf X))
    (hcyc : ∃ g ∈ borel X Ts, ∀ b ∈ borel X Ts, ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ Ts ⊓ X)
    (habel : ∀ a ∈ borel X Ts, ∀ b ∈ borel X Ts, a * b * a⁻¹ * b⁻¹ ∈ Ts ⊓ X)
    (hfrob : ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓
        Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y),
      ∃ j : ℕ, ∀ b ∈ borel X Ts, r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ Ts ⊓ X)
    {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpk : p ∣ 2 ^ k + 1)
    (hpN : p ∣ ((Ts ⊓ X).subgroupOf (borel X Ts)).index) : PermData Ts Ms Tls := by
  obtain ⟨r, j, c, hrTls, hj, -, -, -, hfr, -⟩ := single_prep' h hcoat hcyc hfrob
  have hUB : Ts ⊓ X ≤ borel X Ts := le_inf inf_le_right Subgroup.le_normalizer
  have hBN : borel X Ts ≤ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := inf_le_right
  obtain ⟨n, hnB, hnp, hnr⟩ := exists_moved_p_element_of_dvd (B := borel X Ts) (U := Ts ⊓ X)
    (r := r) (k := k) (j := j) (p := p) hUB hBN hpN hfr hp (by omega) hpk hj
  have hXn : ∀ x : Y, x ∈ Subgroup.normalizer (X : Set Y) := fun x => by
    haveI := h.normal
    rw [Subgroup.normalizer_eq_top_iff.2 h.normal]
    exact Subgroup.mem_top x
  refine permData_build (n := n) hp (by omega) hUB hBN habel h.borel_le ?_ ?_ inf_le_left hnB hnp
    hrTls hnr
  · intro t ht b hb
    have htU : t ∈ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht) x
      have h2 := Subgroup.mem_normalizer_iff.1 (hXn t) x
      exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hXn t) b).1 hb.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htU (hBN hb)) (Subgroup.inv_mem _ htU)
  · intro t ht u hu
    exact ⟨Ts.mul_mem (Ts.mul_mem ht hu.1) (Ts.inv_mem ht),
      (Subgroup.mem_normalizer_iff.1 (hXn t) u).1 hu.2⟩



end Prep

end CFSG.Quasithin.H13.P31X

module

public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.RankThree.PartTwo.Sec3.ThompsonParabolic
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_centralizer_le_of_famG {T W A : Subgroup G} {i : ℕ} (hWT : W ≤ T)
    (hW : IsElemTwo W) (hA : A ∈ famG T i) :
    (centralizer (A : Set G)).relIndex W ≤ 2 ^ i * (centralizer (W : Set G)).relIndex A := by
  obtain ⟨hAT, hA2, hAcard⟩ := hA
  set C := A ⊓ centralizer (W : Set G) with hCdef
  have hcomm : ∀ c ∈ C, ∀ w ∈ W, c * w = w * c := fun c hc w hw =>
    ((Subgroup.mem_centralizer_iff.mp hc.2 w hw)).symm
  have hD := card_sup_mul_card_inf_of_commute hcomm
  have hDel : IsElemTwo (C ⊔ W) :=
    isElemTwo_sup ⟨fun a ha b hb => hA2.1 a ha.1 b hb.1, fun a ha => hA2.2 a ha.1⟩ hW hcomm
  have hle := card_le_two_pow_pRank (sup_le (inf_le_left.trans hAT) hWT) hDel
  have h1 := Subgroup.relIndex_mul_card (H := centralizer (A : Set G)) (K := W)
  have h2 := Subgroup.relIndex_mul_card (H := centralizer (W : Set G)) (K := A)
  rw [inf_comm] at h2
  have hCW : Nat.card ↥(C ⊓ W) ≤ Nat.card ↥(centralizer (A : Set G) ⊓ W) := by
    apply Subgroup.card_le_of_le
    rintro x ⟨hxC, hxW⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, hxW⟩
    exact hA2.1 a ha x hxC.1
  have h2r : 2 ^ CFSG.pRank 2 T ≤ 2 ^ i * Nat.card A := by
    rw [hAcard, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(centralizer (A : Set G) ⊓ W) := Nat.card_pos
  have key : (centralizer (A : Set G)).relIndex W * Nat.card ↥(centralizer (A : Set G) ⊓ W) *
      Nat.card C ≤ 2 ^ i * (centralizer (W : Set G)).relIndex A * Nat.card C *
        Nat.card ↥(centralizer (A : Set G) ⊓ W) := by
    rw [h1]
    calc Nat.card W * Nat.card C = Nat.card ↥(C ⊔ W) * Nat.card ↥(C ⊓ W) := by
          rw [hD, mul_comm]
      _ ≤ 2 ^ i * Nat.card A * Nat.card ↥(centralizer (A : Set G) ⊓ W) :=
          Nat.mul_le_mul (hle.trans h2r) hCW
      _ = 2 ^ i * (centralizer (W : Set G)).relIndex A * Nat.card C *
          Nat.card ↥(centralizer (A : Set G) ⊓ W) := by rw [← h2]; ring
  have key' : (centralizer (A : Set G)).relIndex W *
      (Nat.card ↥(centralizer (A : Set G) ⊓ W) * Nat.card C) ≤
      2 ^ i * (centralizer (W : Set G)).relIndex A *
        (Nat.card ↥(centralizer (A : Set G) ⊓ W) * Nat.card C) := by
    calc _ = (centralizer (A : Set G)).relIndex W * Nat.card ↥(centralizer (A : Set G) ⊓ W) *
          Nat.card C := by ring
      _ ≤ _ := key
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right key' (Nat.mul_pos hpos2 hCpos)

omit [Finite G] in
theorem conj_mem_jG {T : Subgroup G} {i : ℕ} {t : G} (ht : t ∈ T) {x : G} (hx : x ∈ jG T i) :
    t * x * t⁻¹ ∈ jG T i := by
  have hle : (jG T i).map (MulAut.conj t).toMonoidHom ≤ jG T i := by
    rw [jG, (Subgroup.gc_map_comap (MulAut.conj t).toMonoidHom).l_sSup]
    exact iSup₂_le fun A hA => le_sSup (map_conj_mem_famG hA t
      (fun a ha => T.mul_mem (T.mul_mem ht (hA.1 ha)) (T.inv_mem ht)))
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_mem_omegaG_jG {T : Subgroup G} {i : ℕ} {t : G} (ht : t ∈ T) {e : G}
    (he : e ∈ omegaG (jG T i)) : t * e * t⁻¹ ∈ omegaG (jG T i) :=
  conj_mem_omegaG (fun x hx => conj_mem_jG ht hx)
    (fun x hx => by
      have := conj_mem_jG (T.inv_mem ht) hx
      rwa [inv_inv] at this) he

omit [Finite G] in
theorem jG_le (T : Subgroup G) (i : ℕ) : jG T i ≤ T := sSup_le fun _ h => h.1

omit [Finite G] in
theorem omegaG_jG_one_eq_bot_of_pRank_le {T : Subgroup G} (hr : CFSG.pRank 2 T ≤ 1) :
    omegaG (jG T 1) = ⊥ := by
  rw [eq_bot_iff]
  intro e he
  have hJ : jG T 1 = ⊥ := by
    rw [eq_bot_iff, jG]
    refine sSup_le fun A hA => ?_
    have hcard := hA.2.2
    rw [show CFSG.pRank 2 T - 1 = 0 by omega, pow_zero] at hcard
    rw [Subgroup.card_eq_one.mp hcard]
  have := omegaG_le _ he
  rwa [hJ] at this

theorem mem_normalizer_of_conj_mem {P : Subgroup G} {g : G}
    (h : ∀ p ∈ P, g * p * g⁻¹ ∈ P) : g ∈ normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  let f : P → P := fun p => ⟨g * p * g⁻¹, h p p.2⟩
  have hf : Function.Injective f := fun p p' hpp' => by
    have h1 : g * (p : G) * g⁻¹ = g * p' * g⁻¹ := congrArg Subtype.val hpp'
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.mp hf) ⟨g * x * g⁻¹, hx⟩
  have h1 : g * (p : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hp
  have hpx : (p : G) = x := mul_left_cancel (mul_right_cancel h1)
  rw [← hpx]
  exact p.2

omit [Finite G] in
theorem mul_inv_conj_mem_of_inv {N : Subgroup G} (hN : N.Normal) {e z b : G}
    (he : e * b * e⁻¹ * b ∈ N) (hz : z * b * z⁻¹ * b ∈ N) :
    e * z⁻¹ * b * (e * z⁻¹)⁻¹ * b⁻¹ ∈ N := by
  have : e * z⁻¹ * b * (e * z⁻¹)⁻¹ * b⁻¹ =
      b * ((e * b * e⁻¹ * b)⁻¹ * ((e * z⁻¹) * (z * b * z⁻¹ * b) * (e * z⁻¹)⁻¹)) * b⁻¹ := by
    group
  rw [this]
  exact hN.conj_mem _ (N.mul_mem (N.inv_mem he) (hN.conj_mem _ hz _)) b

section Main

variable (T : Sylow 2 G) (B : Sylow 3 G) (hB9 : Nat.card (B : Subgroup G) = 9)
  (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
  (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a)
  (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
  (hCQ : centralizer (CFSG.pCore 2 G : Set G) ≤ CFSG.pCore 2 G)
  (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
    K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
      (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2))
include hB9 hTB hBc hB3 hQ8

omit hTB in
theorem htr_of_quaternion : ∀ d ∈ (B : Subgroup G), ∀ d' ∈ (B : Subgroup G), d ≠ 1 → d' ≠ 1 →
    ∃ n ∈ normalizer ((B : Subgroup G) : Set G), n * d * n⁻¹ = d' := by
  intro d hd d' hd' hd1 hd'1
  obtain ⟨n, -, hn, hnd⟩ := exists_conj_eq_of_quaternion T B hB9 hBc hB3 hQ8 hd hd' hd1 hd'1
  exact ⟨n, hn, hnd⟩

theorem le_pCore_of_mem_famG
    (hV : ∃ b ∈ (B : Subgroup G), ∃ v ∈ omegaG (CFSG.pCore 2 G), b * v * b⁻¹ ≠ v) {i : ℕ}
    (hi : i ≤ 1) {A : Subgroup G} (hA : A ∈ famG (T : Subgroup G) i) :
    A ≤ CFSG.pCore 2 G := by
  set Q := CFSG.pCore 2 G with hQdef
  have hQ2 : IsPGroup 2 Q := pCore_two_isPGroup
  have htr := htr_of_quaternion T B hB9 hBc hB3 hQ8
  set V := omegaG Q with hVdef
  have hVn : V.Normal := omegaG_normal CFSG.pCore_normal
  have hVQ : V ≤ Q := omegaG_le Q
  have hVel : IsElemTwo V := isElemTwo_omegaG Q
  have hQV : Q ≤ centralizer (V : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hv.2.1 q hq
  have hAT : A ≤ (T : Subgroup G) := hA.1
  have hk4 := relIndex_le_four T B hB9 hTB hBc hB3 hAT hA.2.1.2 hA.2.1.1
  have hkdvd : Q.relIndex A ∣ 2 ^ (CFSG.pRank 2 (T : Subgroup G) - i) :=
    hA.2.2 ▸ Subgroup.relIndex_dvd_card Q A
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hkdvd
  have hstd := relIndex_centralizer_le_of_famG (hVQ.trans (pCore_two_le_sylow T)) hVel hA
  have hcv : (centralizer (V : Set G)).relIndex A ≤ Q.relIndex A :=
    Subgroup.relIndex_le_of_le_left hQV (relIndex_ne_zero_of_finite _ _)
  have h2i : 2 ^ i ≤ 2 := by
    calc 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hi
      _ = 2 := by norm_num
  have hjle : j ≤ 2 := by
    rw [hj] at hk4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk4.trans (by norm_num))
  have hcentA : ∀ t ∈ A, (centralizer ({t} : Set G)).relIndex V ≤
      (centralizer (A : Set G)).relIndex V := fun t ht =>
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le (by simpa using ht))
      (relIndex_ne_zero_of_finite _ _)
  interval_cases j
  · rw [pow_zero] at hj
    exact Subgroup.relIndex_eq_one.mp hj
  · exfalso
    obtain ⟨t, htA, htQ⟩ : ∃ t ∈ A, t ∉ Q := by
      by_contra h
      push Not at h
      rw [Subgroup.relIndex_eq_one.mpr h] at hj
      norm_num at hj
    obtain ⟨d, hdB, hd1, htd⟩ := exists_inv_mod_of_mul_self_mem T B hB9 hTB hBc hB3 (hAT htA)
      htQ (by rw [hA.2.1.2 t htA]; exact Q.one_mem)
    have h8 := eight_le_relIndex_centralizer hQ2 hBc hB3 hB9 htr hdB hd1 htd V hVn hVQ
      hVel.1 hVel.2 hV
    have := (h8.trans (hcentA t htA)).trans hstd
    rw [hj] at hcv
    have : 8 ≤ 2 ^ i * 2 := this.trans (Nat.mul_le_mul_left _ hcv)
    omega
  · exfalso
    obtain ⟨⟨z, hzA, hz⟩, -⟩ := exists_of_relIndex_eq_four T B hB9 hTB hBc hB3 hAT
      hA.2.1.2 hA.2.1.1 hj
    have h16 := sixteen_le_relIndex_centralizer hQ2 hBc hB3 hB9 htr hz V hVn hVQ hVel.1 hVel.2
      hV
    have := (h16.trans (hcentA z hzA)).trans hstd
    rw [hj] at hcv
    have : 16 ≤ 2 ^ i * 4 := this.trans (Nat.mul_le_mul_left _ hcv)
    omega

include hCQ in
theorem relIndex_ne_two (hEnn : ¬ (omegaG (jG (T : Subgroup G) 1)).Normal) {A : Subgroup G}
    (hA : A ∈ famG (T : Subgroup G) 0) : (CFSG.pCore 2 G).relIndex A ≠ 2 := by
  intro h2
  set Q := CFSG.pCore 2 G with hQdef
  have hQ2 : IsPGroup 2 Q := pCore_two_isPGroup
  have hQT : Q ≤ (T : Subgroup G) := pCore_two_le_sylow T
  have htr := htr_of_quaternion T B hB9 hBc hB3 hQ8
  have hr : 2 ≤ CFSG.pRank 2 (T : Subgroup G) := by
    by_contra h
    push Not at h
    apply hEnn
    rw [omegaG_jG_one_eq_bot_of_pRank_le (by omega)]
    exact Subgroup.normal_bot
  obtain ⟨t, htA, htQ⟩ : ∃ t ∈ A, t ∉ Q := by
    by_contra h
    push Not at h
    rw [Subgroup.relIndex_eq_one.mpr h] at h2
    norm_num at h2
  have hAQ : A ⊓ Q ∈ famG (T : Subgroup G) 1 := by
    refine ⟨inf_le_left.trans hA.1, ⟨fun a ha b hb => hA.2.1.1 a ha.1 b hb.1,
      fun a ha => hA.2.1.2 a ha.1⟩, ?_⟩
    have h := Subgroup.relIndex_mul_card (H := Q) (K := A)
    rw [h2, hA.2.2, inf_comm] at h
    have h' : 2 ^ (CFSG.pRank 2 (T : Subgroup G) - 0) =
        2 * 2 ^ (CFSG.pRank 2 (T : Subgroup G) - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h'] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hO2 : ∀ K : Subgroup G, K ≤ ⊤ → (∀ h ∈ (⊤ : Subgroup G), ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
      IsPGroup 2 K → K ≤ Q := fun K _ hK hK2 =>
    le_sSup ⟨⟨fun k hk g => hK g trivial k hk⟩, hK2⟩
  have hgen : ∀ N : Subgroup G, (∀ t ∈ (T : Subgroup G), ∀ n ∈ N, t * n * t⁻¹ ∈ N) →
      (∀ x ∈ (B : Subgroup G), ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N.Normal := by
    intro N hNT hNB
    constructor
    intro n hn g
    obtain ⟨t, ht, b, hb, rfl⟩ := hTB g
    have := hNT t ht _ (hNB b hb n hn)
    rw [show t * b * n * (t * b)⁻¹ = t * (b * n * b⁻¹) * t⁻¹ by group]
    exact this
  have hQn : ∀ h ∈ (⊤ : Subgroup G), ∀ p ∈ Q, h * p * h⁻¹ ∈ Q := fun h _ p hp =>
    CFSG.pCore_normal.conj_mem p hp h
  have hXnc := not_centralizes_omegaG_pOne (X := (B : Subgroup G)) le_rfl hQT hQ2 hQ2 hCQ
    hQn hO2 le_top (fun t ht e he => conj_mem_omegaG_jG ht he) hr hAQ inf_le_right hgen hEnn
  push Not at hXnc
  set W := omegaG (pOne (T : Subgroup G) Q) with hWdef
  have hWn : W.Normal := ⟨fun w hw g => conj_mem_omegaG_pOne hQT
    (fun p hp => CFSG.pCore_normal.conj_mem p hp g)
    (fun p hp => by
      have := CFSG.pCore_normal.conj_mem p hp g⁻¹
      rwa [inv_inv] at this) hw⟩
  have hWQ : W ≤ Q := (omegaG_le _).trans (pOne_le _ Q)
  have hle2 : (centralizer ({t} : Set G)).relIndex W ≤ 2 :=
    relIndex_centralizer_le_two hQT hA hAQ htA
  obtain ⟨d, hdB, hd1, htd⟩ := exists_inv_mod_of_mul_self_mem T B hB9 hTB hBc hB3 (hA.1 htA)
    htQ (by rw [hA.2.1.2 t htA]; exact Q.one_mem)
  have h8 := eight_le_relIndex_centralizer hQ2 hBc hB3 hB9 htr hdB hd1 htd W hWn hWQ
    (isElemTwo_omegaG _).1 (isElemTwo_omegaG _).2 hXnc
  omega

include hCQ in
theorem relIndex_ne_four (hEnn : ¬ (omegaG (jG (T : Subgroup G) 1)).Normal) {A : Subgroup G}
    (hA : A ∈ famG (T : Subgroup G) 0) : (CFSG.pCore 2 G).relIndex A ≠ 4 := by
  intro h4
  set Q := CFSG.pCore 2 G with hQdef
  have hQ2 : IsPGroup 2 Q := pCore_two_isPGroup
  have hQT : Q ≤ (T : Subgroup G) := pCore_two_le_sylow T
  have hQn : Q.Normal := CFSG.pCore_normal
  have hr : 2 ≤ CFSG.pRank 2 (T : Subgroup G) := by
    by_contra h
    push Not at h
    apply hEnn
    rw [omegaG_jG_one_eq_bot_of_pRank_le (by omega)]
    exact Subgroup.normal_bot
  obtain ⟨⟨z, hzA, hz⟩, y, hyB, hy1, hpm, ⟨s, hsA, hsy⟩, ⟨c, hcA, hcQ, hcy⟩⟩ :=
    exists_of_relIndex_eq_four T B hB9 hTB hBc hB3 hA.1 hA.2.1.2 hA.2.1.1 h4
  set π := QuotientGroup.mk' Q with hπ
  have hπQ : ∀ q ∈ Q, π q = 1 := fun q hq => (QuotientGroup.eq_one_iff q).mpr hq
  have hcomm_iff : ∀ g : G, g * y * g⁻¹ * y⁻¹ ∈ Q ↔ π g * π y = π y * π g := fun g => by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_mul, map_mul, map_mul,
      map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  have hinv_iff : ∀ g : G, g * y * g⁻¹ * y ∈ Q ↔ π g * π y * (π g)⁻¹ = (π y)⁻¹ := fun g => by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_mul, map_mul, map_mul,
      map_inv, mul_eq_one_iff_eq_inv]
  have hπy1 : π y ≠ 1 := fun h => hy1 (by
    have h' : y ∈ (B : Subgroup G) ⊓ CFSG.pCore 2 G := ⟨hyB, (QuotientGroup.eq_one_iff y).mp h⟩
    rwa [inf_pCore_two_eq_bot B hB9, Subgroup.mem_bot] at h')
  have hπy3 : π y ^ 3 = 1 := by rw [← map_pow, hB3 y hyB, map_one]
  have hπyinv : (π y)⁻¹ ≠ π y := fun h => hπy1 (by
    have h2 : π y * π y = 1 := by
      calc π y * π y = π y * (π y)⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel _
    calc π y = π y ^ 3 * (π y * π y)⁻¹ := by group
      _ = 1 := by rw [hπy3, h2, inv_one, one_mul])
  set Cy : Subgroup G := (centralizer ({π y} : Set (G ⧸ Q))).comap π with hCydef
  have hmemCy : ∀ g, g ∈ Cy ↔ g * y * g⁻¹ * y⁻¹ ∈ Q := fun g => by
    rw [hCydef, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, hcomm_iff]
  have hQCy : Q ≤ Cy := fun q hq => by
    rw [hmemCy, hcomm_iff, hπQ q hq, one_mul, mul_one]
  set A₀ := A ⊓ Cy with hA₀def
  set P := Q ⊔ A₀ with hPdef
  set X := Subgroup.zpowers y with hXdef
  set H := (X ⊔ Q) ⊔ A with hHdef
  have hPT : P ≤ (T : Subgroup G) := sup_le hQT (inf_le_left.trans hA.1)
  have hP2 : IsPGroup 2 P := T.isPGroup'.to_le hPT
  have hAP : A ⊓ P = A₀ := by
    apply le_antisymm
    · rintro x ⟨hxA, hxP⟩
      obtain ⟨q, hq, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxP
      exact ⟨hxA, Cy.mul_mem (hQCy hq) ha.2⟩
    · exact le_inf inf_le_left le_sup_right
  have hsCy : s ∉ Cy := fun h => hπyinv (by
    have h1 := (hcomm_iff s).mp ((hmemCy s).mp h)
    have h2 := (hinv_iff s).mp hsy
    rw [← h2, h1, mul_inv_cancel_right])
  have hrel2 : Cy.relIndex A = 2 := by
    have hdvd : Cy.relIndex A ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff']
      refine ⟨s, hsA, fun b hb => ?_⟩
      rcases hpm b hb with hcen | hinv
      · exact Or.inr ((hmemCy b).mpr hcen)
      · left
        rw [hmemCy, hcomm_iff]
        have h1 := (hinv_iff s).mp hsy
        have h2 := (hinv_iff b).mp hinv
        have h3 : π (s * b) * π y * (π (s * b))⁻¹ = π y := by
          calc π (s * b) * π y * (π (s * b))⁻¹
              = π s * (π b * π y * (π b)⁻¹) * (π s)⁻¹ := by rw [map_mul]; group
            _ = π s * (π y)⁻¹ * (π s)⁻¹ := by rw [h2]
            _ = (π s * π y * (π s)⁻¹)⁻¹ := by group
            _ = π y := by rw [h1, inv_inv]
        calc π (s * b) * π y = π (s * b) * π y * (π (s * b))⁻¹ * π (s * b) := by group
          _ = π y * π (s * b) := by rw [h3]
    have hne1 : Cy.relIndex A ≠ 1 := fun h => hsCy (Subgroup.relIndex_eq_one.mp h hsA)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hA₀ : A₀ ∈ famG (T : Subgroup G) 1 := by
    refine ⟨inf_le_left.trans hA.1, ⟨fun a ha b hb => hA.2.1.1 a ha.1 b hb.1,
      fun a ha => hA.2.1.2 a ha.1⟩, ?_⟩
    have h := Subgroup.relIndex_mul_card (H := Cy) (K := A)
    rw [hrel2, hA.2.2, inf_comm] at h
    have h' : 2 ^ (CFSG.pRank 2 (T : Subgroup G) - 0) =
        2 * 2 ^ (CFSG.pRank 2 (T : Subgroup G) - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h'] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hAP' : A ⊓ P ∈ famG (T : Subgroup G) 1 := by rw [hAP]; exact hA₀
  have hPQ : Q.relIndex P ≤ 2 := by
    rw [hPdef, Subgroup.relIndex_sup_left]
    exact relIndex_le_two_of_centralizes T B hB9 hTB hBc hB3 (inf_le_left.trans hA.1) hyB hy1
      (fun a ha => (hmemCy a).mp ha.2)
  have hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P := by
    intro p hp
    obtain ⟨q, hq, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hp
    have ha' : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ ∈ Q := (hmemCy _).mp (Cy.inv_mem ha.2)
    have : y * (q * a) * y⁻¹ = (y * q * y⁻¹) * a * (a⁻¹ * y * a⁻¹⁻¹ * y⁻¹) := by group
    rw [this]
    exact P.mul_mem (P.mul_mem (Subgroup.mem_sup_left (hQn.conj_mem q hq y))
      (Subgroup.mem_sup_right ha)) (Subgroup.mem_sup_left ha')
  have hAPn : ∀ a ∈ A, ∀ p ∈ P, a * p * a⁻¹ ∈ P := by
    intro a ha p hp
    obtain ⟨q, hq, a', ha', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hp
    have : a * (q * a') * a⁻¹ = (a * q * a⁻¹) * a' := by
      rw [show a * (q * a') * a⁻¹ = (a * q * a⁻¹) * (a * a' * a⁻¹) by group,
        hA.2.1.1 a ha a' ha'.1, mul_inv_cancel_right]
    rw [this]
    exact P.mul_mem (Subgroup.mem_sup_left (hQn.conj_mem q hq a)) (Subgroup.mem_sup_right ha')
  have hHN : H ≤ normalizer (P : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_mem hyP)
    · intro q hq
      exact mem_normalizer_of_conj_mem fun p hp =>
        P.mul_mem (P.mul_mem (Subgroup.mem_sup_left hq) hp) (P.inv_mem (Subgroup.mem_sup_left hq))
    · intro a ha
      exact mem_normalizer_of_conj_mem (hAPn a ha)
  have hHP : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P := fun h hh p hp =>
    (Subgroup.mem_normalizer_iff.mp (hHN hh) p).mp hp
  have hAXQ : A ≤ normalizer ((X ⊔ Q : Subgroup G) : Set G) := by
    intro a ha
    apply mem_normalizer_of_conj_mem
    intro u hu
    obtain ⟨x, hx, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hay : a * y * a⁻¹ ∈ X ⊔ Q := by
      rcases hpm a ha with hcen | hinv
      · have : a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y := by group
        rw [this]
        exact (X ⊔ Q).mul_mem (Subgroup.mem_sup_right hcen)
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
      · have : a * y * a⁻¹ = (a * y * a⁻¹ * y) * y⁻¹ := by group
        rw [this]
        exact (X ⊔ Q).mul_mem (Subgroup.mem_sup_right hinv)
          (Subgroup.mem_sup_left (X.inv_mem (Subgroup.mem_zpowers y)))
    have : a * (y ^ m * q) * a⁻¹ = (a * y * a⁻¹) ^ m * (a * q * a⁻¹) := by
      rw [conj_zpow]; group
    rw [this]
    exact (X ⊔ Q).mul_mem ((X ⊔ Q).zpow_mem hay m)
      (Subgroup.mem_sup_right (hQn.conj_mem q hq a))
  have hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
      IsPGroup 2 K → K ≤ P := by
    intro K hKH hKn hK2 k hk
    have hdec : (H : Set G) = (A : Set G) * ((X ⊔ Q : Subgroup G) : Set G) := by
      rw [hHdef, sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right A (X ⊔ Q) hAXQ]
    have hk' : k ∈ (A : Set G) * ((X ⊔ Q : Subgroup G) : Set G) := by
      rw [← hdec]; exact hKH hk
    obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_mul.mp hk'
    obtain ⟨x, hx, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hπk : π (a * (y ^ m * q)) = π a * π y ^ m := by
      rw [map_mul, map_mul, hπQ q hq, mul_one, map_zpow]
    have hc : a * (y ^ m * q) * y * (a * (y ^ m * q))⁻¹ * y⁻¹ ∈ K := by
      have h1 : y * (a * (y ^ m * q))⁻¹ * y⁻¹ ∈ K :=
        hKn y (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))) _
          (K.inv_mem hk)
      have : a * (y ^ m * q) * y * (a * (y ^ m * q))⁻¹ * y⁻¹ =
          (a * (y ^ m * q)) * (y * (a * (y ^ m * q))⁻¹ * y⁻¹) := by group
      rw [this]
      exact K.mul_mem hk h1
    have hπc : π (a * (y ^ m * q) * y * (a * (y ^ m * q))⁻¹ * y⁻¹) =
        π a * π y * (π a)⁻¹ * (π y)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπk]
      group
    have haCy : a ∈ Cy := by
      rcases hpm a ha with hcen | hinv
      · exact (hmemCy a).mpr hcen
      · exfalso
        have h1 := (hinv_iff a).mp hinv
        have hval : π a * π y * (π a)⁻¹ * (π y)⁻¹ = π y := by
          rw [h1]
          calc (π y)⁻¹ * (π y)⁻¹ = (π y)⁻¹ * (π y)⁻¹ * π y ^ 3 := by rw [hπy3, mul_one]
            _ = π y := by group
        obtain ⟨j, hj⟩ := hK2 ⟨_, hc⟩
        have hj' : π y ^ 2 ^ j = 1 := by
          have := congrArg (fun x : K => π (x : G)) hj
          simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] at this
          rwa [hπc, hval] at this
        have hdvd : orderOf (π y) ∣ Nat.gcd 3 (2 ^ j) :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hπy3) (orderOf_dvd_of_pow_eq_one hj')
        rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right j (by norm_num)), Nat.dvd_one,
          orderOf_eq_one_iff] at hdvd
        exact hπy1 hdvd
    have hπaπy : Commute (π a) (π y) := (hcomm_iff a).mp ((hmemCy a).mp haCy)
    have hπaym : Commute (π a) (π y ^ m) := hπaπy.zpow_right m
    have hπa2 : π a * π a = 1 := by rw [← map_mul, hA.2.1.2 a ha, map_one]
    obtain ⟨j, hj⟩ := hK2 ⟨_, hk⟩
    have hπkj : (π a * π y ^ m) ^ 2 ^ (j + 1) = 1 := by
      have := congrArg (fun x : K => π (x : G)) hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] at this
      rw [hπk] at this
      rw [pow_succ, pow_mul, this, one_pow]
    have hπan : π a ^ 2 ^ (j + 1) = 1 := by
      rw [pow_succ', pow_mul, pow_two, hπa2, one_pow]
    have hym : (π y ^ m) ^ 2 ^ (j + 1) = 1 := by
      have := hπaym.mul_pow (2 ^ (j + 1))
      rw [hπkj, hπan, one_mul] at this
      exact this.symm
    have hym3 : (π y ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hπy3, one_zpow]
    have hdvd : orderOf (π y ^ m) ∣ Nat.gcd 3 (2 ^ (j + 1)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hym3) (orderOf_dvd_of_pow_eq_one hym)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right (j + 1) (by norm_num)), Nat.dvd_one,
      orderOf_eq_one_iff, ← map_zpow] at hdvd
    have hymQ : y ^ m ∈ Q := (QuotientGroup.eq_one_iff _).mp hdvd
    have : a * (y ^ m * q) = (a * (y ^ m * q) * a⁻¹) * a := by group
    rw [this]
    exact P.mul_mem (Subgroup.mem_sup_left (hQn.conj_mem _ (Q.mul_mem hymQ hq) a))
      (Subgroup.mem_sup_right ⟨ha, haCy⟩)
  have hgen : ∀ N : Subgroup G, (∀ t ∈ (T : Subgroup G), ∀ n ∈ N, t * n * t⁻¹ ∈ N) →
      (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N.Normal := by
    intro N hNT hNX
    have hNB : ∀ b ∈ (B : Subgroup G), ∀ n ∈ N, b * n * b⁻¹ ∈ N := by
      intro b hb n hn
      by_cases hb1 : b = 1
      · rw [hb1, one_mul, inv_one, mul_one]; exact hn
      obtain ⟨g, hgT, -, hgy⟩ :=
        exists_conj_eq_of_quaternion T B hB9 hBc hB3 hQ8 hyB hb hy1 hb1
      have h1 : g⁻¹ * n * g⁻¹⁻¹ ∈ N := hNT _ ((T : Subgroup G).inv_mem hgT) n hn
      have h2 := hNX y (Subgroup.mem_zpowers y) _ h1
      have h3 := hNT g hgT _ h2
      rw [← hgy, show g * y * g⁻¹ * n * (g * y * g⁻¹)⁻¹ =
        g * (y * (g⁻¹ * n * g⁻¹⁻¹) * y⁻¹) * g⁻¹ by group]
      exact h3
    constructor
    intro n hn g
    obtain ⟨t, ht, b, hb, rfl⟩ := hTB g
    have := hNT t ht _ (hNB b hb n hn)
    rw [show t * b * n * (t * b)⁻¹ = t * (b * n * b⁻¹) * t⁻¹ by group]
    exact this
  have hEH : omegaG (jG (T : Subgroup G) 1) ≤ H := by
    intro e he
    have heT : e ∈ (T : Subgroup G) := jG_le _ _ (omegaG_le _ he)
    rcases forall_mod_of_normal_elem T B hB9 hTB hBc hB3 hQ8
        (F := omegaG (jG (T : Subgroup G) 1)) (fun t ht f hf => conj_mem_omegaG_jG ht hf)
        (fun f hf => hf.2.2) (fun f hf g hg => (isElemTwo_omegaG _).1 f hf g hg) he with
      hcen | hinv
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (mem_of_forall_commute_mod T B hB9 hTB hBc hB3 heT hcen))
    · have hez : e * z⁻¹ ∈ Q :=
        mem_of_forall_commute_mod T B hB9 hTB hBc hB3
          ((T : Subgroup G).mul_mem heT ((T : Subgroup G).inv_mem (hA.1 hzA)))
          (fun b hb => mul_inv_conj_mem_of_inv hQn (hinv b hb) (hz b hb))
      have : e = (e * z⁻¹) * z := by group
      rw [this]
      exact H.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right hez))
        (Subgroup.mem_sup_right hzA)
  have hEn : ∀ t ∈ (T : Subgroup G), ∀ e ∈ omegaG (jG (T : Subgroup G) 1),
      t * e * t⁻¹ ∈ omegaG (jG (T : Subgroup G) 1) := fun t ht e he => conj_mem_omegaG_jG ht he
  have hXnc := not_centralizes_omegaG_pOne (T := (T : Subgroup G)) (Q := Q) (H := H) (P := P)
    (X := X) (A₁ := A ⊓ P) le_sup_left hPT hP2 hQ2 hCQ hHP hO2 hEH hEn hr hAP' inf_le_right
    hgen hEnn
  have hWH : ∀ h ∈ H, ∀ w ∈ omegaG (pOne (T : Subgroup G) P),
      h * w * h⁻¹ ∈ omegaG (pOne (T : Subgroup G) P) := fun h hh w hw =>
    conj_mem_omegaG_pOne hPT (hHP h hh) (fun p hp => by
      have := hHP h⁻¹ (H.inv_mem hh) p hp
      rwa [inv_inv] at this) hw
  have htX : ∀ x ∈ X, s * x * s⁻¹ * x ∈ Q := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 := (hinv_iff s).mp hsy
    rw [← QuotientGroup.eq_one_iff]
    change π (s * y ^ m * s⁻¹ * y ^ m) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, ← conj_zpow, h1, inv_zpow,
      inv_mul_cancel]
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hB3 y hyB, one_zpow]
  have hA' := sup_mem_famG hPT hQ2 hA hAP' hsA htX hX3
    (fun x hx => hWH x (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)))
    (fun q hq => hWH q (Subgroup.mem_sup_left (Subgroup.mem_sup_right hq))) hXnc
  have hA'P : (A ⊓ P) ⊔ omegaG (pOne (T : Subgroup G) P) ≤ P :=
    sup_le inf_le_right ((omegaG_le _).trans (pOne_le _ P))
  have hcA' : c ∈ (A ⊓ P) ⊔ omegaG (pOne (T : Subgroup G) P) :=
    Subgroup.mem_sup_left ⟨hcA, Subgroup.mem_sup_right ⟨hcA, (hmemCy c).mpr hcy⟩⟩
  have hrel : Q.relIndex ((A ⊓ P) ⊔ omegaG (pOne (T : Subgroup G) P)) = 2 := by
    have hle := (Subgroup.relIndex_le_of_le_right hA'P (relIndex_ne_zero_of_finite Q P)).trans
      hPQ
    have hne1 : Q.relIndex ((A ⊓ P) ⊔ omegaG (pOne (T : Subgroup G) P)) ≠ 1 := fun h =>
      hcQ (Subgroup.relIndex_eq_one.mp h hcA')
    have hne0 := relIndex_ne_zero_of_finite Q ((A ⊓ P) ⊔ omegaG (pOne (T : Subgroup G) P))
    omega
  exact relIndex_ne_two T B hB9 hTB hBc hB3 hCQ hQ8 hEnn hA' hrel

end Main

theorem rank3II_3_17 (T : Sylow 2 G) (B : Sylow 3 G)
    (hTB : ((T : Subgroup G) : Set G) * ((B : Subgroup G) : Set G) = Set.univ)
    (hB : CFSG.Assembly.IsElemAbelian 3 (B : Subgroup G)) (hB9 : Nat.card (B : Subgroup G) = 9)
    (hF : CFSG.generalizedFitting G = CFSG.pCore 2 G)
    (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
      K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
        (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2)) :
    let Z := (CFSG.omegaOneCenter (⊤ : Subgroup (T : Subgroup G))).map (T : Subgroup G).subtype
    let J := (CFSG.higherElemThompson (T : Subgroup G) 0).map (T : Subgroup G).subtype
    let E := (CFSG.higherElemThompsonOmega (T : Subgroup G) 1).map (T : Subgroup G).subtype
    (Z.Normal ∧ J.Normal) ∨ (Z.Normal ∧ E.Normal) ∨ (J.Normal ∧ E.Normal) := by
  intro Z J E
  have hZ : Z = omegaG (T : Subgroup G) := by
    show (CFSG.omegaOneCenter (⊤ : Subgroup (T : Subgroup G))).map (T : Subgroup G).subtype = _
    rw [map_omegaOneCenter, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hJ : J = jG (T : Subgroup G) 0 := map_higherElemThompson _ 0
  have hE : E = omegaG (jG (T : Subgroup G) 1) := by
    show (CFSG.omegaOneCenter (CFSG.higherElemThompson (T : Subgroup G) 1)).map
      (T : Subgroup G).subtype = _
    rw [map_omegaOneCenter, map_higherElemThompson]
  rw [hZ, hJ, hE]
  have hTB' : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b := by
    intro g
    have hg : g ∈ ((T : Subgroup G) : Set G) * ((B : Subgroup G) : Set G) := by
      rw [hTB]; exact Set.mem_univ g
    obtain ⟨t, ht, b, hb, h⟩ := Set.mem_mul.mp hg
    exact ⟨t, ht, b, hb, h.symm⟩
  have hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1 := hB.2
  have hCQ : centralizer (CFSG.pCore 2 G : Set G) ≤ CFSG.pCore 2 G := by
    rw [← hF]; exact CFSG.centralizer_generalizedFitting_le G
  have hTn : ∀ t ∈ (T : Subgroup G), ∀ x ∈ (T : Subgroup G), t * x * t⁻¹ ∈ (T : Subgroup G) :=
    fun t ht x hx =>
      (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hx) ((T : Subgroup G).inv_mem ht)
  by_cases hV : ∃ b ∈ (B : Subgroup G), ∃ v ∈ omegaG (CFSG.pCore 2 G), b * v * b⁻¹ ≠ v
  ·
    have hall : ∀ i ≤ 1, ∀ g : G, ∀ A ∈ famG (T : Subgroup G) i, ∀ a ∈ A,
        g * a * g⁻¹ ∈ (T : Subgroup G) := fun i hi g A hA a ha =>
      pCore_two_le_sylow T (CFSG.pCore_normal.conj_mem a
        (le_pCore_of_mem_famG T B hB9 hTB' hBc hB3 hQ8 hV hi hA ha) g)
    exact Or.inr (Or.inr ⟨jG_normal (hall 0 (Nat.zero_le 1)),
      omegaG_normal (jG_normal (hall 1 le_rfl))⟩)
  ·
    push Not at hV
    have hZQ : omegaG (T : Subgroup G) ≤ omegaG (CFSG.pCore 2 G) := by
      intro z hz
      have hzQ : z ∈ CFSG.pCore 2 G := hCQ (Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (hz.2.1 q (pCore_two_le_sylow T hq)).symm)
      exact ⟨hzQ, fun x hx => hz.2.1 x (pCore_two_le_sylow T hx), hz.2.2⟩
    have hZn : (omegaG (T : Subgroup G)).Normal := by
      constructor
      intro z hz g
      obtain ⟨t, ht, b, hb, rfl⟩ := hTB' g
      rw [show t * b * z * (t * b)⁻¹ = t * (b * z * b⁻¹) * t⁻¹ by group, hV b hb z (hZQ hz)]
      exact conj_mem_omegaG (hTn t ht) (fun x hx => by
        have := hTn t⁻¹ ((T : Subgroup G).inv_mem ht) x hx
        rwa [inv_inv] at this) hz
    by_cases hJn : (jG (T : Subgroup G) 0).Normal
    · exact Or.inl ⟨hZn, hJn⟩
    · refine Or.inr (Or.inl ⟨hZn, ?_⟩)
      by_contra hEnn
      apply hJn
      apply jG_normal
      intro g A hA a ha
      have hAQ : A ≤ CFSG.pCore 2 G := by
        have hk4 := relIndex_le_four T B hB9 hTB' hBc hB3 hA.1 hA.2.1.2 hA.2.1.1
        have hkdvd : (CFSG.pCore 2 G).relIndex A ∣ 2 ^ (CFSG.pRank 2 (T : Subgroup G) - 0) :=
          hA.2.2 ▸ Subgroup.relIndex_dvd_card (CFSG.pCore 2 G) A
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hkdvd
        have hjle : j ≤ 2 := by
          rw [hj] at hk4
          exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk4.trans (by norm_num))
        interval_cases j
        · rw [pow_zero] at hj
          exact Subgroup.relIndex_eq_one.mp hj
        · exact (relIndex_ne_two T B hB9 hTB' hBc hB3 hCQ hQ8 hEnn hA (by simpa using hj)).elim
        · exact (relIndex_ne_four T B hB9 hTB' hBc hB3 hCQ hQ8 hEnn hA (by simpa using hj)).elim
      exact pCore_two_le_sylow T (CFSG.pCore_normal.conj_mem a (hAQ ha) g)

end CFSG.RankThree.PartTwo.Sec3

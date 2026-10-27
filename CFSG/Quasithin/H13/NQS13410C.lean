module

public import CFSG.Quasithin.H13.NQS1342
public import CFSG.Quasithin.H13.U3S1344A
public import CFSG.Quasithin.H13.A6Set14

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem mem_L_of_orderOf_three (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hx3 : orderOf x = 3) : x ∈ L := by
  obtain ⟨h5, -, -, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  have hyp := U3.hyp1223_of h1332 S.h13 S.irr
  have hLV : L ≤ normalizer (V : Set G) := S.irr.2.2.1
  have hO := pCoreOf_L_le_centralizer_V S
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rcases h1228 G T L V hyp with h | h | ⟨-, h⟩
  · rw [← h]
    exact subset_closure ⟨hx, 1, by rw [pow_one, ← hx3, pow_orderOf_eq_one]⟩
  · exfalso
    have hcase := U3.a6_or_hatA6_of_isA6On hLV hO h5 (U3.s134_isA6On S)
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨
        Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
      rcases hcase with he | ⟨-, hz, ⟨e⟩⟩
      · left
        obtain ⟨e⟩ := he
        rw [Nat.card_congr e.toEquiv, h360]
      · right
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (center (↥L ⧸ CFSG.pCore 2 ↥L))
        rw [Nat.card_congr e.toEquiv, h360, hz] at h1
        rw [h1]
    rcases h with he5 | h32
    · obtain ⟨e5⟩ := he5
      have := Nat.card_congr e5.toEquiv
      rw [h60] at this
      omega
    · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
      have := Nat.card_congr e3.toEquiv
      rw [HSType.card_SL_three_two] at this
      omega
  · rw [h]
    exact subset_closure ⟨hx, hx3⟩

theorem mem_L_of_pow_three (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {x : G}
    (hx : x ∈ normalizer (L : Set G)) {k : ℕ} (hxk : x ^ 3 ^ k = 1) : x ∈ L := by
  have hyp := U3.hyp1223_of h1332 S.h13 S.irr
  have hcen : center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inr he))
  rcases h1228 G T L V hyp with h | h | ⟨⟨n, -, -, hz, -⟩, -⟩
  · rw [← h]
    exact subset_closure ⟨hx, k, hxk⟩
  · exfalso
    obtain ⟨e⟩ := he
    have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by rw [Nat.card_congr e.toEquiv, h360]
    rcases h with he5 | h32
    · obtain ⟨e5⟩ := he5
      have := Nat.card_congr e5.toEquiv
      rw [h60] at this
      omega
    · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
      have := Nat.card_congr e3.toEquiv
      rw [HSType.card_SL_three_two] at this
      omega
  · exfalso
    rw [hcen, Subgroup.card_bot] at hz
    omega

theorem mem_L1_of_pow_three (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {x : G}
    (hxZ : x ∈ centralizer (quasithinOmegaOneCenter T : Set G)) {k : ℕ} (hxk : x ^ 3 ^ k = 1) :
    x ∈ L₁Of L (fsuV1 T V) := by
  have hZV : V ⊓ centralizer (L : Set G) ≤ quasithinOmegaOneCenter T :=
    S.ZV_le_ZL.trans inf_le_left
  have hxM : x ∈ normalizer (L : Set G) :=
    S.centralizer_ZV_le (centralizer_le (SetLike.coe_subset_coe.mpr hZV) hxZ)
  have hxL := mem_L_of_pow_three h1332 h1228 S he hxM hxk
  have hxN : x ∈ normalizer (fsuV1 T V : Set G) :=
    centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.mpr
      (inf_le_right : fsuV1 T V ≤ quasithinOmegaOneCenter T)) hxZ)
  exact U3.mem_oTwoRes_of_odd (mem_inf.2 ⟨hxL, hxN⟩) (Odd.pow (by decide : Odd 3)) hxk

theorem mem_L1_of_orderOf_three (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V) {x : G}
    (hxZ : x ∈ centralizer (quasithinOmegaOneCenter T : Set G)) (hx3 : orderOf x = 3) :
    x ∈ L₁Of L (fsuV1 T V) := by
  have hZV : V ⊓ centralizer (L : Set G) ≤ quasithinOmegaOneCenter T :=
    S.ZV_le_ZL.trans inf_le_left
  have hxM : x ∈ normalizer (L : Set G) :=
    S.centralizer_ZV_le (centralizer_le (SetLike.coe_subset_coe.mpr hZV) hxZ)
  have hxL := mem_L_of_orderOf_three h1332 h1228 S hxM hx3
  have hxN : x ∈ normalizer (fsuV1 T V : Set G) :=
    centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.mpr
      (inf_le_right : fsuV1 T V ≤ quasithinOmegaOneCenter T)) hxZ)
  exact U3.mem_oTwoRes_of_odd (mem_inf.2 ⟨hxL, hxN⟩) (by decide : Odd 3)
    (by rw [← hx3, pow_orderOf_eq_one])

theorem isPGroup_inf_centralizer_of_a6 (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := by
  have h1 : L ⊓ centralizer (V : Set G) ≤ pCoreOf 2 L :=
    (U3.centralizer_le_o2Z_of_isA6On S.frame.L_le (pCoreOf_L_le_centralizer_V S)
      S.fsu.quasisimple (U3.s134_isA6On S)).trans (U3.o2Z_le_pCoreOf_of_a6 he)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le h1

theorem mem_C3_of_inA4 : ∀ a : Perm (Fin 6), U3.InA4 a → a ^ 3 = 1 → a ∈ S14.C3 := by
  decide +kernel

theorem c3_conj_pow : ∀ a ∈ S14.C3, a ≠ 1 → ∀ τ ∈ S14.C3, ∃ c ∈ S14.C3, ∃ i : Fin 3,
    τ = (c * a * c⁻¹) ^ (i : ℕ) := by
  decide +kernel

omit [Finite G] in
theorem mem_of_pow_odd_mem {Y : Subgroup G} {n : G} {s m : ℕ} (hs : n ^ 2 ^ s = 1)
    (hm : Odd m) (hnm : n ^ m ∈ Y) : n ∈ Y := by
  have hcop : Nat.Coprime m (2 ^ s) := Nat.Coprime.pow_right s (Nat.coprime_two_right.2 hm)
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp only [pow_zero, pow_one] at hs
    rw [hs]
    exact one_mem _
  have h1 : 1 < 2 ^ s := Nat.one_lt_two_pow hs0.ne'
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
  have key : n ^ (m * u) = n := by
    rw [← Nat.mod_add_div (m * u) (2 ^ s), hu, pow_add, pow_mul, hs, one_pow, mul_one, pow_one]
  rw [← key, pow_mul]
  exact pow_mem hnm u

theorem L1_le_of_mem (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {X : Subgroup G}
    (hX : L₁Of L (fsuV1 T V) ≤ normalizer (X : Set G)) {y : G} (hyX : y ∈ X)
    (hyL1 : y ∈ L₁Of L (fsuV1 T V)) (hy1 : y ≠ 1) {my : ℕ} (hmy : Odd my) (hym : y ^ my = 1) :
    L₁Of L (fsuV1 T V) ≤ X := by
  set L₁ := L₁Of L (fsuV1 T V) with hL₁def
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1N : L₁ ≤ normalizer (V : Set G) := hL1L.trans S.frame.L_le
  have hP := isPGroup_inf_centralizer_of_a6 S he
  set Y := X ⊓ L₁ with hYdef
  have hYN : ∀ l ∈ L₁, ∀ w ∈ Y, l * w * l⁻¹ ∈ Y := by
    intro l hl w hw
    obtain ⟨hwX, hwL⟩ := Subgroup.mem_inf.1 hw
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.mp (hX hl) w).mp hwX,
      mul_mem (mul_mem hl hwL) (inv_mem hl)⟩
  have hyN := hL1N hyL1
  set a := S.frame.ρ ⟨y, hyN⟩ with ha
  have haA4 : U3.InA4 a := U3.s134_rho_L1 S hyN hyL1
  have hym' : (⟨y, hyN⟩ : ↥(normalizer (V : Set G))) ^ my = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, hym])
  have ha45 : a ^ 45 = 1 := U3.pow_45_of_odd' hmy (by rw [ha, ← map_pow, hym', map_one])
  have ha3 : a ^ 3 = 1 := U3.cube_of_inA4 a haA4 ha45
  have ha1 : a ≠ 1 := by
    intro h
    have hyC := (U3.s134_rho_eq_one_iff S ⟨y, hyN⟩).1 h
    obtain ⟨k, hk⟩ := hP ⟨y, ⟨hL1L hyL1, hyC⟩⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : y ∈ (⊥ : Subgroup G) := mem_of_pow_odd_mem hk' hmy (by rw [hym]; exact one_mem _)
    exact hy1 (mem_bot.1 h1)
  have haC3 : a ∈ S14.C3 := mem_C3_of_inA4 a haA4 ha3
  have hlift : ∀ τ ∈ S14.C3, ∃ w ∈ Y, ∃ hw : w ∈ normalizer (V : Set G),
      S.frame.ρ ⟨w, hw⟩ = τ := by
    intro τ hτ
    obtain ⟨c, hc, i, rfl⟩ := c3_conj_pow a haC3 ha1 τ hτ
    obtain ⟨hc4, hc5, hcs, hc3⟩ := S14.c3_facts c hc
    obtain ⟨lc, hlc, hlcN, hρc⟩ :=
      U3.s134_exists_mem_L1 S (Perm.mem_alternatingGroup.2 hcs) hc3 ⟨hc4, hc5, hcs⟩
    have hwN : lc * y * lc⁻¹ ∈ normalizer (V : Set G) :=
      mul_mem (mul_mem hlcN hyN) (inv_mem hlcN)
    refine ⟨(lc * y * lc⁻¹) ^ (i : ℕ), pow_mem (hYN lc hlc y (Subgroup.mem_inf.2 ⟨hyX, hyL1⟩)) _,
      pow_mem hwN _, ?_⟩
    have e : (⟨(lc * y * lc⁻¹) ^ (i : ℕ), pow_mem hwN _⟩ : ↥(normalizer (V : Set G))) =
        (⟨lc, hlcN⟩ * ⟨y, hyN⟩ * ⟨lc, hlcN⟩⁻¹) ^ (i : ℕ) := rfl
    rw [e, map_pow, map_mul, map_mul, map_inv, hρc]
  have hcov : ∀ l ∈ L₁, ∃ w ∈ Y, w⁻¹ * l ∈ L ⊓ centralizer (V : Set G) := by
    intro l hl
    have hb := U3.s134_rho_L1 S (hL1N hl) hl
    obtain ⟨τ₁, hτ₁, τ₂, hτ₂, hb'⟩ := S14.alt4_prod _ hb.1 hb.2.1 hb.2.2
    obtain ⟨w₁, hw₁, hw₁N, hρ₁⟩ := hlift τ₁ hτ₁
    obtain ⟨w₂, hw₂, hw₂N, hρ₂⟩ := hlift τ₂ hτ₂
    refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (mul_mem
      (hL1L (Subgroup.mem_inf.1 hw₁).2) (hL1L (Subgroup.mem_inf.1 hw₂).2))) (hL1L hl), ?_⟩⟩
    have hgN : (w₁ * w₂)⁻¹ * l ∈ normalizer (V : Set G) :=
      mul_mem (inv_mem (mul_mem hw₁N hw₂N)) (hL1N hl)
    refine (U3.s134_rho_eq_one_iff S ⟨_, hgN⟩).1 ?_
    have e : (⟨(w₁ * w₂)⁻¹ * l, hgN⟩ : ↥(normalizer (V : Set G))) =
        (⟨w₁, hw₁N⟩ * ⟨w₂, hw₂N⟩)⁻¹ * ⟨l, hL1N hl⟩ := rfl
    rw [e, map_mul, map_inv, map_mul, hρ₁, hρ₂, ← hb', inv_mul_cancel]
  have hodd : ∀ g ∈ L₁, ∀ m : ℕ, Odd m → g ^ m = 1 → g ∈ Y := by
    intro g hg m hm hgm
    obtain ⟨w, hw, hwl⟩ := hcov g hg
    set n := w⁻¹ * g with hn
    have hnL1 : n ∈ L₁ := mul_mem (inv_mem (Subgroup.mem_inf.1 hw).2) hg
    have hgwn : g = w * n := by rw [hn]; group
    have hpow : ∀ k : ℕ, ∃ w' ∈ Y, g ^ k = w' * n ^ k := by
      intro k
      induction k with
      | zero => exact ⟨1, one_mem _, by simp⟩
      | succ k ih =>
        obtain ⟨w', hw', hk⟩ := ih
        refine ⟨w' * (n ^ k * w * (n ^ k)⁻¹), mul_mem hw' (hYN _ (pow_mem hnL1 k) w hw), ?_⟩
        rw [pow_succ, hk, hgwn]
        group
    obtain ⟨w', hw', hm'⟩ := hpow m
    rw [hgm] at hm'
    have hnm : n ^ m ∈ Y := by
      have : n ^ m = w'⁻¹ := eq_inv_of_mul_eq_one_right hm'.symm
      rw [this]
      exact inv_mem hw'
    obtain ⟨s, hs⟩ := hP ⟨n, hwl⟩
    have hs' : n ^ 2 ^ s = 1 := by simpa using congrArg Subtype.val hs
    rw [hgwn]
    exact mul_mem hw (mem_of_pow_odd_mem hs' hm hnm)
  have hL1eq : oTwoRes L₁ = L₁ := S14.oTwoRes_idem _
  intro g hg
  rw [← hL1eq] at hg
  have hle : oTwoRes L₁ ≤ Y := by
    rw [oTwoRes, closure_le]
    rintro x ⟨hx, m, hm, hxm⟩
    exact hodd x hx m hm hxm
  exact (Subgroup.mem_inf.1 (hle hg)).1

theorem L1_le_of_pow_three (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {X : Subgroup G}
    (hX : L₁Of L (fsuV1 T V) ≤ normalizer (X : Set G)) {y : G} (hyX : y ∈ X)
    (hyZ : y ∈ centralizer (quasithinOmegaOneCenter T : Set G)) (hy1 : y ≠ 1) {k : ℕ}
    (hyk : y ^ 3 ^ k = 1) : L₁Of L (fsuV1 T V) ≤ X :=
  L1_le_of_mem S he hX hyX (mem_L1_of_pow_three h1332 h1228 S he hyZ hyk) hy1
    (Odd.pow (by decide : Odd 3)) hyk

end CFSG.Quasithin.H13.NQS134

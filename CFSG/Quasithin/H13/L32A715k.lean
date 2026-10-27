module

public import CFSG.Quasithin.H13.L32A715j
public import CFSG.Quasithin.H13.L32A715g

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E

theorem exists_c : ∃ c ∈ modO2Image (hz T V) (l1 T L V), c ≠ 1 ∧ c ^ 3 = 1 ∧
    Subgroup.zpowers c = modO2Image (hz T V) (l1 T L V) := by
  obtain ⟨-, -, hcard3, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hne : modO2Image (hz T V) (l1 T L V) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcard3
    norm_num at hcard3
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hc1' : c ≠ 1 := fun e => hc1 (Subtype.ext e)
  have hc3 : c ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(modO2Image (hz T V) (l1 T L V))) (x := ⟨c, hc⟩)
    rw [hcard3] at this
    simpa using congrArg Subtype.val this
  refine ⟨c, hc, hc1', hc3, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hc) ?_
  rw [hcard3, Nat.card_zpowers, orderOf_eq_prime hc3 hc1']

include hF in
theorem fpf_c {c : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hc3 : c ^ 3 = 1) (hcL : Subgroup.zpowers c = modO2Image (hz T V) (l1 T L V)) :
    ∀ w : UMod hF.toHypF91, rhoDot hF.toHypF91 c w = w → w = 1 := by
  obtain ⟨-, -, -, -, -, -, hUL1⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hL1hz : l1 T L V ≤ hz T V := (le_sup_left.trans E.S.hz.1.1).trans E.le_hz
  refine fpf_of_commutator hF.toHypF91 hL1hz hc3 (fun y hy => ?_) hUL1
  have hmem : QuotientGroup.mk (⟨y, hL1hz hy⟩ : ↥(hz T V)) ∈ Subgroup.zpowers c := by
    rw [hcL]
    exact mem_modO2Image_iff.mpr ⟨_, hy, rfl⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  obtain ⟨k, -, hk⟩ := Heis.exists_pow_lt_three_of_zpow hc3 n
  exact ⟨k, by rw [← hk, hn]⟩

omit E in
include hF in
theorem umod_nontrivial : ∃ w : UMod hF.toHypF91, w ≠ 1 := by
  obtain ⟨v, hvV, hvV1⟩ := IsConcreteLE.exists_of_lt hF.V₁_lt_Vp
  have hvU : v ∈ conjClosure V (hz T V) := le_conjClosure V _ hvV
  exact ⟨clsU hF.toHypF91 hvU, fun e => hvV1 ((clsU_eq_one_iff _ hvU).mp e)⟩

include hF in
theorem card_commV_y {y : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (huniq : ∀ r ∈ modO2Image (hz T V) T,
      r ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) →
      r ^ 2 = 1 → r ≠ 1 → r = y ^ 2) :
    Nat.card (commV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2)))) ≤ 4 := by
  obtain ⟨s, hsR, hsQ, hss, hidx⟩ := E.exists_s hF
  obtain ⟨-, -, -, -, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  set sd : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V) :=
    QuotientGroup.mk (⟨s, E.r1_le_hz hsR⟩ : ↥(hz T V)) with hsd
  have hsdm : sd ∈ modO2Image (hz T V) T ⊓ Subgroup.centralizer ((modO2Image (hz T V)
      (l1 T L V) : Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) := by
    rw [← hR1C]
    exact mem_modO2Image_iff.mpr ⟨_, hsR, rfl⟩
  have hss' : (⟨s, E.r1_le_hz hsR⟩ : ↥(hz T V)) * ⟨s, E.r1_le_hz hsR⟩ = 1 := Subtype.ext hss
  have hsd2 : sd ^ 2 = 1 := by
    rw [hsd, sq, ← QuotientGroup.mk_mul, hss', QuotientGroup.mk_one]
  have hsd1 : sd ≠ 1 := by
    intro e
    apply hsQ
    rw [hsd, QuotientGroup.eq_one_iff] at e
    exact ⟨_, e, rfl⟩
  have hsy : sd = y ^ 2 := huniq sd hsdm.1 hsdm.2 hsd2 hsd1
  have hρ : rhoDot hF.toHypF91 (y ^ 2) = C1Pack.rhoH hF.toHypF91 ⟨s, E.r1_le_hz hsR⟩ := by
    rw [← hsy, hsd, rhoDot_mk]
  have ht2 : C1Pack.rhoH hF.toHypF91 ⟨s, E.r1_le_hz hsR⟩ *
      C1Pack.rhoH hF.toHypF91 ⟨s, E.r1_le_hz hsR⟩ = 1 := by
    rw [← map_mul, hss', map_one]
  rw [hρ]
  exact (card_commV_le hF.toHypF91 ⟨s, E.r1_le_hz hsR⟩ ht2).trans hidx

include hF in
theorem mem_kdot_of_pow {x : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)} {m : ℕ} (hx : x ^ 3 ^ m = 1) :
    x ∈ modO2Image (hz T V) (oTwoUpper H) := by
  set h := hF.toHypF91 with hh
  set ρ := rhoDot h with hρdef
  have := E.kdot_normal
  have hK := E.isPOnePlusTwo_kdot
  obtain ⟨hcen, y, -, hyC, -, hy4, huniq, hinv⟩ := E.exists_y
  obtain ⟨c, hcL, hc1, hc3, hcz⟩ := E.exists_c
  have hcZ : c ∈ (Subgroup.center ↥(modO2Image (hz T V) (oTwoUpper H))).map
      (modO2Image (hz T V) (oTwoUpper H)).subtype := hcen ▸ hcL
  have hfpf := E.fpf_c hF hc3 hcz
  have hne := umod_nontrivial hF
  have hcommV := E.card_commV_y hF huniq
  have hW2 := umod_sq h
  have hmul : ∀ g g' : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V), g * g' = g' * g →
      ρ g * ρ g' = ρ g' * ρ g := fun g g' e => by rw [← map_mul, e, map_mul]
  have hcent : ∀ a ∈ modO2Image (hz T V) (oTwoUpper H), a * c = c * a := by
    intro a ha
    obtain ⟨c', hc', hcc⟩ := hcZ
    rw [← hcc]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨a, ha⟩)
  have hKpow : ∀ a ∈ modO2Image (hz T V) (oTwoUpper H), a ^ 3 = 1 := fun a ha => by
    simpa using congrArg Subtype.val (Heis.pow_three_eq hK ⟨a, ha⟩)
  have hρc3 : ρ c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hy22 : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact hy4
  have ht2 : ρ (y ^ 2) * ρ (y ^ 2) = 1 := by rw [← map_mul, hy22, map_one]
  have hyc : y ^ 2 * c = c * y ^ 2 :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hyC 2) c hcL).symm
  refine mem_of_pow_three_pow hK E.pRank_le hW2 ρ (rhoDot_injective h) hcZ hc1 hfpf ?_ hx
  intro a haK haZ j hj
  have haZ' : (⟨a, haK⟩ : ↥(modO2Image (hz T V) (oTwoUpper H))) ∉ Subgroup.center _ :=
    fun e => haZ ⟨_, e, rfl⟩
  obtain ⟨b', hb'⟩ := Heis.exists_comm_ne_one_of_not_mem haZ'
  set b : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V) := b'.1 with hbdef
  have hbK : b ∈ modO2Image (hz T V) (oTwoUpper H) := b'.2
  set ζ := a⁻¹ * b⁻¹ * a * b with hζ
  have hζZ : ζ ∈ Subgroup.zpowers c := by
    rw [hcz, ← hcen]
    refine ⟨⁅(⟨a, haK⟩ : ↥(modO2Image (hz T V) (oTwoUpper H)))⁻¹, b'⁻¹⁆,
      Heis.comm_mem_center hK _ _, ?_⟩
    simp [commutatorElement_def, hζ, hbdef]
  have hζ1 : ζ ≠ 1 := by
    intro e
    apply hb'
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    have e' : a * b = b * a := by
      calc a * b = b * a * ζ := by rw [hζ]; group
        _ = b * a := by rw [e, mul_one]
    calc a * b * a⁻¹ * b⁻¹ = (a * b) * a⁻¹ * b⁻¹ := rfl
      _ = 1 := by rw [e']; group
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hζZ
  obtain ⟨s, hs3, hs⟩ := Heis.exists_pow_lt_three_of_zpow hc3 n
  have hs0 : s % 3 ≠ 0 := by
    rw [Nat.mod_eq_of_lt hs3]
    intro e
    apply hζ1
    rw [← hn, hs, e, pow_zero]
  have hab : ρ a * ρ b = ρ b * ρ a * ρ c ^ s := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, ← hs, hn, hζ]
    congr 1
    group
  have hinva := hinv a haK
  rw [← hcz] at hinva
  obtain ⟨n', hn'⟩ := Subgroup.mem_zpowers_iff.mp hinva
  obtain ⟨k, -, hk⟩ := Heis.exists_pow_lt_three_of_zpow hc3 n'
  have hyinv : (y ^ 2)⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right hy22
  have hck : c ^ k * a⁻¹ = a⁻¹ * c ^ k := by
    have h1 := ((show Commute a c from hcent a haK).pow_right k).eq
    calc c ^ k * a⁻¹ = a⁻¹ * (a * c ^ k) * a⁻¹ := by group
      _ = a⁻¹ * (c ^ k * a) * a⁻¹ := by rw [h1]
      _ = a⁻¹ * c ^ k := by group
  have hta : ρ (y ^ 2) * ρ a * ρ (y ^ 2) = (ρ a)⁻¹ * ρ c ^ k := by
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    have e1 : y ^ 2 * a * (y ^ 2)⁻¹ * a = c ^ k := by rw [← hk, hn']
    rw [hyinv] at e1
    calc y ^ 2 * a * y ^ 2 = (y ^ 2 * a * y ^ 2 * a) * a⁻¹ := by group
      _ = c ^ k * a⁻¹ := by rw [e1]
      _ = a⁻¹ * c ^ k := hck
  have hρa3 : ρ a ^ 3 = 1 := by rw [← map_pow, hKpow a haK, map_one]
  exact (HeisMod.card_eq_sixtyfour hW2 hρc3 hfpf hρa3 (hmul _ _ (hcent a haK))
    (hmul _ _ (hcent b hbK)) hab hs0 ht2 (hmul _ _ hyc) hta hne hcommV).2.1 j hj

end Ctx7153

end CFSG.Quasithin.H13.L32A

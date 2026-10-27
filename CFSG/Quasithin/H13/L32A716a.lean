module

public import CFSG.Quasithin.H13.L32A715k

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem exists_frame : ∃ a b c y : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V),
    a ∈ modO2Image (hz T V) (oTwoUpper H) ∧ b ∈ modO2Image (hz T V) (oTwoUpper H) ∧
    c ∈ modO2Image (hz T V) (l1 T L V) ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧
    Subgroup.zpowers c = modO2Image (hz T V) (l1 T L V) ∧
    (Subgroup.center ↥(modO2Image (hz T V) (oTwoUpper H))).map
        (modO2Image (hz T V) (oTwoUpper H)).subtype = modO2Image (hz T V) (l1 T L V) ∧
    y ∈ modO2Image (hz T V) T ∧
    y ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
      Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) ∧
    y ^ 2 ≠ 1 ∧ y ^ 4 = 1 ∧
    (∀ r ∈ modO2Image (hz T V) T,
      r ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) →
      r ^ 2 = 1 → r ≠ 1 → r = y ^ 2) ∧
    (∀ x ∈ modO2Image (hz T V) (oTwoUpper H),
      y ^ 2 * x * (y ^ 2)⁻¹ * x ∈ modO2Image (hz T V) (l1 T L V)) ∧
    (∀ w : UMod hF.toHypF91, rhoDot hF.toHypF91 c w = w → w = 1) ∧
    (∃ s : ℕ, s % 3 ≠ 0 ∧ rhoDot hF.toHypF91 a * rhoDot hF.toHypF91 b =
      rhoDot hF.toHypF91 b * rhoDot hF.toHypF91 a * rhoDot hF.toHypF91 c ^ s) ∧
    (∃ k : ℕ, rhoDot hF.toHypF91 (y ^ 2) * rhoDot hF.toHypF91 a * rhoDot hF.toHypF91 (y ^ 2) =
      (rhoDot hF.toHypF91 a)⁻¹ * rhoDot hF.toHypF91 c ^ k) ∧
    Nat.card (UMod hF.toHypF91) = 64 ∧
    (∀ j, j < 3 → Nat.card (HeisMod.wt (rhoDot hF.toHypF91 a) (rhoDot hF.toHypF91 c) j) = 4) ∧
    Nat.card (commV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2)))) = 4 := by
  set h := hF.toHypF91 with hh
  set ρ := rhoDot h with hρdef
  have := E.kdot_normal
  have hK := E.isPOnePlusTwo_kdot
  obtain ⟨hcen, y, hyT, hyC, hy2, hy4, huniq, hinv⟩ := E.exists_y
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
  obtain ⟨a', ha'⟩ : ∃ a' : ↥(modO2Image (hz T V) (oTwoUpper H)), a' ∉ Subgroup.center _ := by
    by_contra hno
    push Not at hno
    exact Heis.center_ne_top hK (eq_top_iff.mpr fun x _ => hno x)
  set a : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V) := a'.1 with hadef
  have haK : a ∈ modO2Image (hz T V) (oTwoUpper H) := a'.2
  obtain ⟨b', hb'⟩ := Heis.exists_comm_ne_one_of_not_mem ha'
  set b : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V) := b'.1 with hbdef
  have hbK : b ∈ modO2Image (hz T V) (oTwoUpper H) := b'.2
  set ζ := a⁻¹ * b⁻¹ * a * b with hζ
  have hζZ : ζ ∈ Subgroup.zpowers c := by
    rw [hcz, ← hcen]
    refine ⟨⁅a'⁻¹, b'⁻¹⁆, Heis.comm_mem_center hK _ _, ?_⟩
    simp [commutatorElement_def, hζ, hbdef, hadef]
  have hζ1 : ζ ≠ 1 := by
    intro e
    apply hb'
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    have e' : a * b = b * a := by
      calc a * b = b * a * ζ := by rw [hζ]; group
        _ = b * a := by rw [e, mul_one]
    calc (a' : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) * b' * (a' : _)⁻¹ * (b' : _)⁻¹ =
        (a * b) * a⁻¹ * b⁻¹ := rfl
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
  obtain ⟨h64, h4, h4c⟩ := HeisMod.card_eq_sixtyfour hW2 hρc3 hfpf hρa3 (hmul _ _ (hcent a haK))
    (hmul _ _ (hcent b hbK)) hab hs0 ht2 (hmul _ _ hyc) hta hne hcommV
  exact ⟨a, b, c, y, haK, hbK, hcL, hc1, hc3, hcz, hcen, hyT, hyC, hy2, hy4, huniq, hinv, hfpf,
    ⟨s, hs0, hab⟩, ⟨k, hta⟩, h64, h4, h4c⟩

theorem card_umod : Nat.card (UMod hF.toHypF91) = 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h64, -⟩ := E.exists_frame hF
  exact h64

theorem irreducible (W' : Subgroup (UMod hF.toHypF91))
    (hW' : ∀ g ∈ modO2Image (hz T V) (oTwoUpper H), ∀ w ∈ W', rhoDot hF.toHypF91 g w ∈ W') :
    W' = ⊥ ∨ W' = ⊤ := by
  obtain ⟨a, b, c, -, haK, hbK, hcL, -, hc3, -, hcen, -, -, -, -, -, -, hfpf, ⟨s, hs0, hab⟩, -,
    -, h4, -⟩ := E.exists_frame hF
  have hK := E.isPOnePlusTwo_kdot
  have hcK : c ∈ modO2Image (hz T V) (oTwoUpper H) := by
    rw [← hcen] at hcL
    obtain ⟨c', -, rfl⟩ := hcL
    exact c'.2
  have hcZ : c ∈ (Subgroup.center ↥(modO2Image (hz T V) (oTwoUpper H))).map
      (modO2Image (hz T V) (oTwoUpper H)).subtype := hcen ▸ hcL
  have hcent : ∀ x ∈ modO2Image (hz T V) (oTwoUpper H), x * c = c * x := by
    intro x hx
    obtain ⟨c', hc', hcc⟩ := hcZ
    rw [← hcc]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨x, hx⟩)
  have hKpow : ∀ x ∈ modO2Image (hz T V) (oTwoUpper H), x ^ 3 = 1 := fun x hx => by
    simpa using congrArg Subtype.val (Heis.pow_three_eq hK ⟨x, hx⟩)
  have hmul : ∀ g g' : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V), g * g' = g' * g →
      rhoDot hF.toHypF91 g * rhoDot hF.toHypF91 g' =
        rhoDot hF.toHypF91 g' * rhoDot hF.toHypF91 g :=
    fun g g' e => by rw [← map_mul, e, map_mul]
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  right
  exact HeisMod.eq_top_of_invariant (umod_sq _) (by rw [← map_pow, hc3, map_one]) hfpf
    (by rw [← map_pow, hKpow a haK, map_one]) (hmul _ _ (hcent a haK)) (hmul _ _ (hcent b hbK))
    hab hs0 h4 (hW' a haK) (hW' b hbK) (hW' c hcK) hbot

end Ctx7153

end CFSG.Quasithin.H13.L32A

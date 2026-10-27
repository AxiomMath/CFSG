module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
public import CFSG.SignalizerFunctorTheorem.MinimalAction.CyclicThree

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers
open CFSG.SignalizerFunctorTheorem.Glauberman
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

variable {G : Type*} [Group G] [Finite G]

structure EightSetting (P : Subgroup G) (d : G) (W : Subgroup G) : Prop where
  normal : P.Normal
  pgroup : IsPGroup 2 P
  selfCentralizing : ∀ g : G, (∀ h ∈ P, h * g = g * h) → g ∈ P
  rank : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 4
  three : IsPGroup 3 (Subgroup.zpowers d)
  ne_one : d ≠ 1
  ne_bot : W ≠ ⊥
  elem : IsElemAbelian 2 W
  normalizes : d ∈ Subgroup.normalizer (W : Set G)
  free : ∀ w ∈ W, d * w * d⁻¹ = w → w = 1

namespace EightSetting

variable {P : Subgroup G} {d : G} {W : Subgroup G}

omit [Finite G] in
private theorem mem_omegaCenter_iff {q : ℕ} {T : Subgroup G} {z : G} :
    z ∈ omegaCenter q T ↔ z ∈ T ∧ (∀ t ∈ T, z * t = t * z) ∧ z ^ q = 1 :=
  Iff.rfl

omit [Finite G] in
private theorem normal_omegaCenter {T : Subgroup G} (hT : T.Normal) :
    (omegaCenter 2 T).Normal where
  conj_mem z hz g := by
    obtain ⟨hzT, hzc, hz2⟩ := mem_omegaCenter_iff.1 hz
    refine mem_omegaCenter_iff.2 ⟨hT.conj_mem z hzT g, fun t ht => ?_, ?_⟩
    · have hc := hzc (g⁻¹ * t * g) (by simpa using hT.conj_mem t ht g⁻¹)
      calc g * z * g⁻¹ * t = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * t * g * z) * g⁻¹ := by rw [hc]
        _ = t * (g * z * g⁻¹) := by group
    · rw [conj_pow, hz2, mul_one, mul_inv_cancel]

omit [Finite G] in
private theorem isElemAbelian_omegaCenter (T : Subgroup G) :
    IsElemAbelian 2 (omegaCenter 2 T) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => (mem_omegaCenter_iff.1 hx).2.2⟩
  exact (mem_omegaCenter_iff.1 a.2).2.1 b (mem_omegaCenter_iff.1 b.2).1

omit [Finite G] in
private theorem mem_normalizer_of_normal {N : Subgroup G} (hN : N.Normal) (g : G) :
    g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.normalizer_eq_top_iff.2 hN]
  exact Subgroup.mem_top g

omit [Finite G] in
private theorem mem_centralizer_zpowers {y z : G} (hyz : y * z = z * y) :
    z ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact (Commute.zpow_left (show Commute y z from hyz) k).eq

private theorem two_dvd_natCard_of_ne_bot {H : Subgroup G} (hH : IsPGroup 2 H) (hne : H ≠ ⊥) :
    2 ∣ Nat.card H := by
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rcases n with _ | n
  · exact absurd (Subgroup.card_eq_one.1 (hn.trans (pow_zero 2))) hne
  · rw [hn]
    exact dvd_pow_self 2 n.succ_ne_zero

private theorem exists_mem_orderOf_eq_two {H : Subgroup G} (hH : 2 ∣ Nat.card H) :
    ∃ x ∈ H, orderOf x = 2 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hH
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

private theorem exists_pow_orderOf_eq_two {H : Subgroup G} (hH : IsPGroup 2 H) {g : G}
    (hg : g ∈ H) (hg1 : g ≠ 1) : ∃ n : ℕ, orderOf (g ^ n) = 2 := by
  have h2 : 2 ∣ orderOf g := by
    have := hH.dvd_orderOf (g := ⟨g, hg⟩) fun h1 => hg1 (congrArg Subtype.val h1)
    rwa [Subgroup.orderOf_mk] at this
  exact ⟨orderOf g / 2, orderOf_pow_orderOf_div (orderOf_pos g).ne' h2⟩

omit [Finite G] in
private theorem P_ne_bot (h : EightSetting P d W) : P ≠ ⊥ := by
  intro hP
  refine h.ne_one ?_
  have hd : d ∈ P := h.selfCentralizing d fun x hx => by
    rw [hP, Subgroup.mem_bot] at hx
    rw [hx, one_mul, mul_one]
  rwa [hP, Subgroup.mem_bot] at hd

private theorem omegaCenter_ne_bot (h : EightSetting P d W) : omegaCenter 2 P ≠ ⊥ := by
  have hmod := centralizer_card_modEq 2 Nat.prime_two P P h.pgroup Subgroup.le_normalizer
  obtain ⟨x, hx, hx2⟩ := exists_mem_orderOf_eq_two
    ((hmod.dvd_iff dvd_rfl).1 (two_dvd_natCard_of_ne_bot h.pgroup (P_ne_bot h)))
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxZ : x ∈ omegaCenter 2 P := by
    refine mem_omegaCenter_iff.2
      ⟨hxP, fun t ht => (Subgroup.mem_centralizer_iff.1 hxC t ht).symm, ?_⟩
    have := pow_orderOf_eq_one x
    rwa [hx2] at this
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hxZ
  rw [hxZ, orderOf_one] at hx2
  omega

private theorem normalizes_inf (h : EightSetting P d W) :
    d ∈ Subgroup.normalizer
      ((omegaCenter 2 P ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  have hZ := normal_omegaCenter h.normal
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.1
    (show x ∈ omegaCenter 2 P ⊓ Subgroup.centralizer (W : Set G) from hx)
  show d * x * d⁻¹ ∈ omegaCenter 2 P ⊓ Subgroup.centralizer (W : Set G)
  refine Subgroup.mem_inf.2 ⟨hZ.conj_mem x hxZ d, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
  have hw' : d⁻¹ * w * d ∈ W := by
    simpa using (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (W : Set G)).inv_mem h.normalizes) w).1 hw
  have hc := Subgroup.mem_centralizer_iff.1 hxC _ hw'
  calc w * (d * x * d⁻¹) = d * (d⁻¹ * w * d * x) * d⁻¹ := by group
    _ = d * (x * (d⁻¹ * w * d)) * d⁻¹ := by rw [hc]
    _ = d * x * d⁻¹ * w := by group

private theorem card_modEq_one (h : EightSetting P d W) {U : Subgroup G} (hUW : U ≤ W)
    (hdU : d ∈ Subgroup.normalizer (U : Set G)) : Nat.card U ≡ 1 [MOD 3] := by
  have hmod := centralizer_card_modEq 3 Nat.prime_three (Subgroup.zpowers d) U h.three
    (Subgroup.zpowers_le.2 hdU)
  have hfix : U ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun u hu => ?_
    obtain ⟨huU, huC⟩ := Subgroup.mem_inf.1 hu
    have hc := Subgroup.mem_centralizer_iff.1 huC d (Subgroup.mem_zpowers d)
    rw [Subgroup.mem_bot]
    exact h.free u (hUW huU) (by rw [hc, mul_inv_cancel_right])
  rwa [hfix, Subgroup.card_bot] at hmod

theorem card_eq_four (h : EightSetting P d W) : Nat.card W = 4 := by
  have hmod := card_modEq_one h le_rfl h.normalizes
  have hle := h.rank W h.elem
  have hpos : 0 < Nat.card W := Nat.card_pos
  have hne : Nat.card W ≠ 1 := fun h1 => h.ne_bot (Subgroup.card_eq_one.1 h1)
  unfold Nat.ModEq at hmod
  omega

private theorem le_omegaCenter_aux (h : EightSetting P d W) {U : Subgroup G}
    (hUZ : U ≤ omegaCenter 2 P) (hUC : U ≤ Subgroup.centralizer (W : Set G))
    (hdU : d ∈ Subgroup.normalizer (U : Set G)) (h2U : 2 ∣ Nat.card U) :
    W ≤ omegaCenter 2 P := by
  have hUe : IsElemAbelian 2 U := elementary_abelian_of_le 2 (isElemAbelian_omegaCenter P) hUZ
  have hUW : U ≤ W := by
    have hsup : IsElemAbelian 2 (W ⊔ U) := isElemAbelian_sup h.elem hUe fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 (hUC hb) a ha
    have hW : W = W ⊔ U := Subgroup.eq_of_le_of_card_ge le_sup_left
      (by rw [card_eq_four h]; exact h.rank _ hsup)
    exact le_sup_right.trans hW.ge
  have hmod := card_modEq_one h hUW hdU
  have hle := Subgroup.card_le_of_le hUW
  have hW4 := card_eq_four h
  have hpos : 0 < Nat.card U := Nat.card_pos
  unfold Nat.ModEq at hmod
  have hUeq : U = W := Subgroup.eq_of_le_of_card_ge hUW (by omega)
  rw [← hUeq]
  exact hUZ

theorem eq_omegaCenter (h : EightSetting P d W) : W = omegaCenter 2 P := by
  have hZ := normal_omegaCenter h.normal
  have hZe := isElemAbelian_omegaCenter P
  have hmod := centralizer_card_modEq 2 Nat.prime_two W (omegaCenter 2 P)
    (elementary_abelian_isPGroup 2 W h.elem) fun w _ => mem_normalizer_of_normal hZ w
  have h2Z : 2 ∣ Nat.card (omegaCenter 2 P) :=
    two_dvd_natCard_of_ne_bot (elementary_abelian_isPGroup 2 _ hZe) (omegaCenter_ne_bot h)
  have hWZ : W ≤ omegaCenter 2 P :=
    le_omegaCenter_aux (U := omegaCenter 2 P ⊓ Subgroup.centralizer (W : Set G)) h inf_le_left
      inf_le_right (normalizes_inf h) ((hmod.dvd_iff dvd_rfl).1 h2Z)
  exact Subgroup.eq_of_le_of_card_ge hWZ (by rw [card_eq_four h]; exact h.rank _ hZe)

theorem normal_left (h : EightSetting P d W) : W.Normal := by
  rw [h.eq_omegaCenter]
  exact normal_omegaCenter h.normal

private theorem eq_one_of_commute (h : EightSetting P d W) {y : G}
    (hy : IsPGroup 3 (Subgroup.zpowers y)) (hyN : y ∈ Subgroup.normalizer (W : Set G))
    (hyW : ∃ z ∈ W, y * z ≠ z * y) : ∀ z ∈ W, y * z = z * y → z = 1 := by
  have hW4 := card_eq_four h
  have hmod := centralizer_card_modEq 3 Nat.prime_three (Subgroup.zpowers y) W hy
    (Subgroup.zpowers_le.2 hyN)
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = W ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
    ⟨_, rfl⟩
  rw [← hC] at hmod
  have hmem : ∀ z, z ∈ C ↔ z ∈ W ∧ y * z = z * y := fun z => by
    rw [hC, Subgroup.mem_inf]
    exact and_congr_right fun _ =>
      ⟨fun hz => Subgroup.mem_centralizer_iff.1 hz y (Subgroup.mem_zpowers y),
        mem_centralizer_zpowers⟩
  have hCW : C ≤ W := fun z hz => ((hmem z).1 hz).1
  have hle := Subgroup.card_le_of_le hCW
  have hpos : 0 < Nat.card C := Nat.card_pos
  unfold Nat.ModEq at hmod
  have hne4 : Nat.card C ≠ 4 := by
    intro h4
    obtain ⟨z, hz, hyz⟩ := hyW
    have hCeq : C = W := Subgroup.eq_of_le_of_card_ge hCW (by omega)
    have hzC : z ∈ C := by rw [hCeq]; exact hz
    exact hyz ((hmem z).1 hzC).2
  have hC1 : Nat.card C = 1 := by omega
  intro z hz hyz
  have hzC : z ∈ C := (hmem z).2 ⟨hz, hyz⟩
  rw [Subgroup.card_eq_one.1 hC1, Subgroup.mem_bot] at hzC
  exact hzC

theorem star (h : EightSetting P d W) {y : G} (hy : IsPGroup 3 (Subgroup.zpowers y))
    (hyW : ∃ z ∈ W, y * z ≠ z * y) :
    (∀ z ∈ W, y * z = z * y → z = 1) ∧ (∀ g ∈ P, y * g = g * y → g = 1) ∧ y ^ 3 = 1 := by
  have hWZ := eq_omegaCenter h
  have hWn : W.Normal := h.normal_left
  have hW1 := eq_one_of_commute h hy (mem_normalizer_of_normal hWn y) hyW
  have hP1 : ∀ g ∈ P, y * g = g * y → g = 1 := by
    intro g hgP hyg
    by_contra hg1
    obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two h.pgroup hgP hg1
    have ht2 : (g ^ n) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (g ^ n)
      rwa [hn] at this
    have htP : g ^ n ∈ P := pow_mem hgP n
    have hyt : y * g ^ n = g ^ n * y := (Commute.pow_right (show Commute y g from hyg) n).eq
    have htW : g ^ n ∉ W := fun htW => by
      rw [hW1 _ htW hyt, orderOf_one] at hn
      omega
    have hcomm : ∀ a ∈ W, ∀ b ∈ Subgroup.zpowers (g ^ n), a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have ha' : a ∈ omegaCenter 2 P := by rwa [← hWZ]
      exact (Commute.zpow_right
        (show Commute a (g ^ n) from (mem_omegaCenter_iff.1 ha').2.1 _ htP) k).eq
    have hE := isElemAbelian_sup h.elem (isElemAbelian_zpowers ht2) hcomm
    have hEW : W = W ⊔ Subgroup.zpowers (g ^ n) := Subgroup.eq_of_le_of_card_ge le_sup_left
      (by rw [card_eq_four h]; exact h.rank _ hE)
    exact htW (by rw [hEW]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  refine ⟨hW1, hP1, ?_⟩
  have hcube := cube_centralizes h.pgroup (mem_normalizer_of_normal h.normal y) hy hP1
    fun E _ hE => h.rank E hE
  have hy3 : y ^ 3 ∈ P := h.selfCentralizing _ fun g hg => (hcube g hg).symm
  obtain ⟨a, ha⟩ := h.pgroup.exists_orderOf_dvd_pow ⟨y ^ 3, hy3⟩
  obtain ⟨b, hb⟩ := hy.exists_orderOf_dvd_pow ⟨y ^ 3, pow_mem (Subgroup.mem_zpowers y) 3⟩
  rw [Subgroup.orderOf_mk] at ha hb
  exact orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow a b (by norm_num)) ha hb)

end EightSetting

end CFSG.SignalizerFunctorTheorem.MinimalAction

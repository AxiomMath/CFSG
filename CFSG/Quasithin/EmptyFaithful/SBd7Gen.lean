module

import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Natural
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf
public import CFSG.Quasithin.EmptyFaithful.SBd6Gen
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace SBd7

section Generic

variable {G : Type} [Group G]

theorem odd_fixes_of_card_four {V : Subgroup G} (hV4 : Nat.card V = 4)
    (hsq : ∀ a ∈ V, a * a = 1)
    {y b : G} (hy : y ∈ Subgroup.normalizer (V : Set G)) (hodd : Odd (orderOf y))
    (hb : b ∈ V) (hb1 : b ≠ 1) (hyb : y * b * y⁻¹ = b) :
    ∀ c ∈ V, y * c * y⁻¹ = c := by
  classical
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  have : Fintype V := Fintype.ofFinite V
  intro c hc
  by_contra hne
  have hyV : ∀ x ∈ V, y * x * y⁻¹ ∈ V := fun x hx => (Subgroup.mem_normalizer_iff.mp hy x).mp hx
  have hdV : y * c * y⁻¹ ∈ V := hyV c hc
  have hc1 : c ≠ 1 := by
    intro h; apply hne; rw [h]; group
  have hcb : c ≠ b := by
    intro h; apply hne; rw [h, hyb]
  have hd1 : y * c * y⁻¹ ≠ 1 := by
    intro h
    apply hc1
    have h2 : c = y⁻¹ * (y * c * y⁻¹) * y := by group
    rw [h2, h]; group
  have hdb : y * c * y⁻¹ ≠ b := by
    intro h
    apply hcb
    have h2 : c = y⁻¹ * (y * c * y⁻¹) * y := by group
    have h3 : y⁻¹ * b * y = b := by
      have : b = y⁻¹ * (y * b * y⁻¹) * y := by group
      rw [hyb] at this
      exact this.symm
    rw [h2, h]; exact h3
  have hbc : b * c ∈ V := V.mul_mem hb hc
  have hbb : b * b = 1 := hsq b hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hbcne1 : b * c ≠ 1 := by
    intro h
    apply hcb
    have : c = b⁻¹ * (b * c) := by group
    rw [this, h, hbinv]; group
  have hbcneb : b * c ≠ b := by
    intro h; apply hc1
    have : c = b⁻¹ * (b * c) := by group
    rw [this, h]; group
  have hbcnec : b * c ≠ c := by
    intro h; apply hb1
    have : b = (b * c) * c⁻¹ := by group
    rw [this, h]; group
  have hdc : y * c * y⁻¹ ≠ c := hne
  let s : Finset V := {1, ⟨b, hb⟩, ⟨c, hc⟩, ⟨y * c * y⁻¹, hdV⟩}
  have hs : s.card = 4 := by
    have h1 : (1 : V) ≠ ⟨b, hb⟩ := fun h => hb1 (congrArg Subtype.val h).symm
    have h2 : (1 : V) ≠ ⟨c, hc⟩ := fun h => hc1 (congrArg Subtype.val h).symm
    have h3 : (1 : V) ≠ ⟨y * c * y⁻¹, hdV⟩ := fun h => hd1 (congrArg Subtype.val h).symm
    have h4 : (⟨b, hb⟩ : V) ≠ ⟨c, hc⟩ := fun h => hcb (congrArg Subtype.val h).symm
    have h5 : (⟨b, hb⟩ : V) ≠ ⟨y * c * y⁻¹, hdV⟩ := fun h => hdb (congrArg Subtype.val h).symm
    have h6 : (⟨c, hc⟩ : V) ≠ ⟨y * c * y⁻¹, hdV⟩ := fun h => hdc (congrArg Subtype.val h).symm
    simp [s, h1, h2, h3, h4, h5, h6]
  have hall : s = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hs]
    have := Nat.card_eq_fintype_card (α := V)
    omega
  have hmem : (⟨b * c, hbc⟩ : V) ∈ s := by rw [hall]; exact Finset.mem_univ _
  simp only [s, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact hbcne1 (congrArg Subtype.val h)
  · exact hbcneb (congrArg Subtype.val h)
  · exact hbcnec (congrArg Subtype.val h)
  · have hbcd : b * c = y * c * y⁻¹ := congrArg Subtype.val h
    have h2 : y * (y * c * y⁻¹) * y⁻¹ = c := by
      have e : y * (y * c * y⁻¹) * y⁻¹ = (y * b * y⁻¹) * (y * c * y⁻¹) := by
        calc y * (y * c * y⁻¹) * y⁻¹ = y * (b * c) * y⁻¹ := by rw [hbcd]
          _ = (y * b * y⁻¹) * (y * c * y⁻¹) := by group
      rw [e, hyb, ← hbcd, ← mul_assoc, hbb, one_mul]
    have hcomm : Commute (y * y) c := by
      show y * y * c = c * (y * y)
      have : y * y * c * y⁻¹ * y⁻¹ = c := by
        calc y * y * c * y⁻¹ * y⁻¹ = y * (y * c * y⁻¹) * y⁻¹ := by group
          _ = c := h2
      calc y * y * c = (y * y * c * y⁻¹ * y⁻¹) * (y * y) := by group
        _ = c * (y * y) := by rw [this]
    obtain ⟨k, hk⟩ := hodd
    have hyy : (y * y) ^ (k + 1) = y := by
      have h1 : y ^ (orderOf y) = 1 := pow_orderOf_eq_one y
      rw [hk] at h1
      calc (y * y) ^ (k + 1) = y ^ (2 * k + 1) * y := by
            rw [← pow_two, ← pow_mul]; group
        _ = y := by rw [h1, one_mul]
    have hcy : Commute y c := by
      have := hcomm.pow_left (k + 1)
      rwa [hyy] at this
    apply hne
    have : y * c = c * y := hcy
    calc y * c * y⁻¹ = c * y * y⁻¹ := by rw [this]
      _ = c := by group

theorem exists_central_of_normal [Finite G] {S X : Subgroup G}
    (hS : IsPGroup 2 S) (hX : X ≤ S) (hN : S ≤ Subgroup.normalizer (X : Set G)) (hX1 : X ≠ ⊥) :
    ∃ n ∈ X, n ≠ 1 ∧ ∀ s ∈ S, s * n * s⁻¹ = n := by
  have hnil : Group.IsNilpotent ↥S := hS.isNilpotent
  have hnorm : (X.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hX).mpr hN
  have hne : X.subgroupOf S ≠ ⊥ := by
    intro h
    apply hX1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hX hx⟩ : S) ∈ X.subgroupOf S := hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have h2 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨x, hxS⟩, hx, hx1⟩ : ∃ z ∈ (X.subgroupOf S ⊓ Subgroup.center ↥S), z ≠ 1 := by
    by_contra h
    push Not at h
    apply h2
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact h z hz
  obtain ⟨hxX, hxc⟩ := hx
  refine ⟨x, hxX, fun h => hx1 (Subtype.ext h), fun s hs => ?_⟩
  have := Subgroup.mem_center_iff.mp hxc ⟨s, hs⟩
  have h3 : s * x = x * s := congrArg Subtype.val this
  calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [h3]
    _ = x := by group

theorem le_of_central_mul {Q H Z : Subgroup G} (hHQ : H ≤ Q) (hZQ : Z ≤ Q)
    (hcent : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hprod : ∀ q ∈ Q, ∃ h ∈ H, ∃ z ∈ Z, q = h * z)
    (hZc : Z ≤ ⁅Q, Q⁆) : Q ≤ H := by
  have hcomm : ⁅Q, Q⁆ ≤ H := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := hprod a ha
    obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := hprod b hb
    have e1 : ⁅h₁ * z₁, h₂ * z₂⁆ = ⁅h₁ * z₁, h₂⁆ := by
      have hz : z₂ * (h₁ * z₁)⁻¹ = (h₁ * z₁)⁻¹ * z₂ := by
        have := hcent z₂ hz₂ (h₁ * z₁)⁻¹ (Q.inv_mem (Q.mul_mem (hHQ hh₁) (hZQ hz₁)))
        exact this
      have hz' : z₂ * (h₁ * z₁)⁻¹ * z₂⁻¹ = (h₁ * z₁)⁻¹ := by
        rw [hz]; group
      simp only [commutatorElement_def]
      calc h₁ * z₁ * (h₂ * z₂) * (h₁ * z₁)⁻¹ * (h₂ * z₂)⁻¹
          = h₁ * z₁ * h₂ * (z₂ * (h₁ * z₁)⁻¹ * z₂⁻¹) * h₂⁻¹ := by group
        _ = h₁ * z₁ * h₂ * (h₁ * z₁)⁻¹ * h₂⁻¹ := by rw [hz']
    have e2 : ⁅h₁ * z₁, h₂⁆ = ⁅h₁, h₂⁆ := by
      have hz : z₁ * h₂ = h₂ * z₁ := hcent z₁ hz₁ h₂ (hHQ hh₂)
      have hz' : z₁ * h₂ * z₁⁻¹ = h₂ := by rw [hz]; group
      simp only [commutatorElement_def]
      calc h₁ * z₁ * h₂ * (h₁ * z₁)⁻¹ * h₂⁻¹ = h₁ * (z₁ * h₂ * z₁⁻¹) * h₁⁻¹ * h₂⁻¹ := by group
        _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by rw [hz']
    rw [e1, e2, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
  intro q hq
  obtain ⟨h, hh, z, hz, rfl⟩ := hprod q hq
  exact H.mul_mem hh (hcomm (hZc hz))

theorem pow_mem_of_mul_pgroup {H L S : Subgroup G} (hLH : L ≤ H) (hN : H ≤ Subgroup.normalizer (L : Set G))
    (hprod : (H : Set G) = (L : Set G) * (S : Set G)) (hSH : S ≤ H) (hS : IsPGroup 2 ↥S) :
    ∀ x ∈ H, ∃ n : ℕ, x ^ 2 ^ n ∈ L := by
  intro x hx
  have hLn : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hN
  have hx' : x ∈ ((L : Set G) * (S : Set G)) := hprod ▸ hx
  obtain ⟨l, hl, s, hs, rfl⟩ := hx'
  obtain ⟨n, hn⟩ := hS ⟨s, hs⟩
  refine ⟨n, ?_⟩
  let π := QuotientGroup.mk' (L.subgroupOf H)
  have hlG : l ∈ H := hLH hl
  have hsG : s ∈ H := hSH hs
  have hlt : l * s ∈ H := H.mul_mem hlG hsG
  have hπ : π (⟨l * s, hlt⟩ : ↥H) = π ⟨s, hsG⟩ := by
    have : (⟨l * s, hlt⟩ : ↥H) = ⟨l, hlG⟩ * ⟨s, hsG⟩ := rfl
    rw [this, map_mul]
    have hl1 : π ⟨l, hlG⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hl)
    rw [hl1, one_mul]
  have h1 : (⟨s, hsG⟩ : ↥H) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    exact Subtype.ext (by simpa using this)
  have hpow : π ((⟨l * s, hlt⟩ : ↥H) ^ 2 ^ n) = 1 := by
    rw [map_pow, hπ, ← map_pow, h1, map_one]
  have hmem := (QuotientGroup.eq_one_iff _).mp hpow
  rw [Subgroup.mem_subgroupOf] at hmem
  exact hmem

variable [Finite G]

theorem charTwo_sup_of_normalizing {L S : Subgroup G} (hL : CharTwo L) (hS : IsPGroup 2 ↥S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) : CharTwo (L ⊔ S) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hL hS hSL

theorem commutator_pCoreOf_sup_eq {L X : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) :
    ⁅pCoreOf 2 (L ⊔ X), L⁆ = ⁅pCoreOf 2 L, L⁆ := by
  have hHN : L ⊔ X ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) hXL
  have hOLH : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ X) := by
    have hnorm : L ⊔ X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun g hg =>
      normalizer_le_normalizer_pCoreOf 2 L (hHN hg)
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) hnorm
      (pCoreOf_isPGroup 2 L)
  apply le_antisymm
  · set A : Subgroup G := pCoreOf 2 (L ⊔ X) with hA
    have hAH : A ≤ L ⊔ X := pCoreOf_le 2 _
    have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAH.trans hHN
    have hLA : L ≤ Subgroup.normalizer (A : Set G) := fun l hl =>
      le_normalizer_pCoreOf 2 (L ⊔ X) (Subgroup.mem_sup_left hl)
    have h1 : ⁅A, L⁆ ≤ pCoreOf 2 L := by
      have hle : ⁅A, L⁆ ≤ A ⊓ L := by
        refine Subgroup.commutator_le.mpr fun a ha l hl => ⟨?_, ?_⟩
        · have h1 : l * a⁻¹ * l⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hLA hl) _).mp (A.inv_mem ha)
          have e : a * l * a⁻¹ * l⁻¹ = a * (l * a⁻¹ * l⁻¹) := by group
          rw [commutatorElement_def, e]
          exact A.mul_mem ha h1
        · have h1 : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAL ha) _).mp hl
          rw [commutatorElement_def]
          exact L.mul_mem h1 (L.inv_mem hl)
      refine hle.trans ?_
      have hnorm : L ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := fun l hl =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hLA hl, Subgroup.le_normalizer hl⟩
      exact le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
        ((pCoreOf_isPGroup 2 (L ⊔ X)).to_le inf_le_left)
    have hAN : A ≤ Subgroup.normalizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G) := fun a ha =>
      SBd5.mem_normalizer_commutator_of (normalizer_le_normalizer_pCoreOf 2 L (hAL ha)) (hAL ha)
    have hLN : L ≤ Subgroup.normalizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G) := fun l hl =>
      SBd5.mem_normalizer_commutator_of (le_normalizer_pCoreOf 2 L hl) (Subgroup.le_normalizer hl)
    exact SBd6.commutator_le_of_double_le hperf hAN hLN (Subgroup.commutator_mono h1 le_rfl)
  · exact Subgroup.commutator_mono hOLH le_rfl

end Generic

end SBd7

end CFSG.Quasithin

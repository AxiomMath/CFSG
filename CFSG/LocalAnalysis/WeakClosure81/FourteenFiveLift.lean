module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveFix
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G} [((KOf M V g).subgroupOf (LOf V g)).Normal]

private theorem isPGroup_subgroupOf_LOf (h : Hyp65 n M V₀ V g) :
    IsPGroup 2 ↥((KOf M V g).subgroupOf (LOf V g)) := by
  intro k
  refine ⟨2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  have hNleV : NOf M V g ≤ V := fun _ hx => (Subgroup.mem_inf.1 (h.N_le_U hx)).1
  have hkV : ((k : ↥(LOf V g)) : G) * ((k : ↥(LOf V g)) : G) ∈ V :=
    hNleV (h.sq_K_mem_N ((k : ↥(LOf V g)) : G) (Subgroup.mem_subgroupOf.1 k.2))
  have h4 : ((k : ↥(LOf V g)) : G) ^ (2 : ℕ) ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, show (4 : ℕ) = 2 + 2 by norm_num,
      pow_add, pow_two]
    exact IsElemAbelian.mul_self_eq_one h.elemAbelian hkV
  exact h4

private theorem card_imgK_eq_two_pow_mQuot (h : Hyp65 n M V₀ V g) :
    Nat.card (imgK M V g V) = 2 ^ E3.mQuot V (conjSubgroup M g) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (imgK_isElemAbelian M V g h.elemAbelian).isPGroup
  have hcard : Nat.card (imgK M V g V) = (conjSubgroup M g).relIndex V := h.card_imgK
  have hrel : (conjSubgroup M g).relIndex V = 2 ^ k := by rw [← hcard, hk]
  have hmq : E3.mQuot V (conjSubgroup M g) = k := by
    change padicValNat 2 ((conjSubgroup M g).relIndex V) = k
    rw [hrel, padicValNat.prime_pow]
  rw [hcard, hmq, hrel]

theorem mem_N_of_mk_eq_mul (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    {l : G} (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l) {x : ↥(LOf V g)}
    {c s₁ s₂ : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)}
    (hs₁ : s₁ ∈ conjSubgroup (imgK M V g V) c)
    (hs₂ : s₂ ∈ conjSubgroup (conjSubgroup (imgK M V g V)
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨l, hlL⟩)) c)
    (hs₁1 : s₁ ≠ 1) (hs₂1 : s₂ ≠ 1)
    (hx : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) x = s₁ * s₂) {k : G}
    (hk : k ∈ KOf M V g) (hxk : (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ NOf M V g) :
    k ∈ NOf M V g := by
  unfold imgK at hs₁ hs₂
  obtain ⟨w, hwπ⟩ := QuotientGroup.mk'_surjective ((KOf M V g).subgroupOf (LOf V g)) c
  have hconjA : conjSubgroup ((V.subgroupOf (LOf V g)).map
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))))
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) w) =
      ((conjSubgroup V (w : G)).subgroupOf (LOf V g)).map
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) := by
    rw [map_conjSubgroup_of_hom, conjSubgroup_subgroupOf]
  have hs₁'' : s₁ ∈ ((conjSubgroup V (w : G)).subgroupOf (LOf V g)).map
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) := by
    rw [← hwπ] at hs₁
    rwa [hconjA] at hs₁
  obtain ⟨t₁, ht₁, ht₁π⟩ := Subgroup.mem_map.1 hs₁''
  have hs₂'' : s₂ ∈ ((conjSubgroup (conjSubgroup V g) (w : G)).subgroupOf (LOf V g)).map
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) := by
    rw [← hwπ] at hs₂
    rw [← map_subgroupOf_conjSubgroup_eq (K := KOf M V g) hlL hlV] at hs₂
    rw [map_conjSubgroup_of_hom, conjSubgroup_subgroupOf] at hs₂
    exact hs₂
  obtain ⟨t₂, ht₂, ht₂π⟩ := Subgroup.mem_map.1 hs₂''
  have ht₁V : (w : G) * (t₁ : G) * (w : G)⁻¹ ∈ V :=
    (mem_conjSubgroup_iff).1 (Subgroup.mem_subgroupOf.1 ht₁)
  have ht₂Vg : (w : G) * (t₂ : G) * (w : G)⁻¹ ∈ conjSubgroup V g :=
    (mem_conjSubgroup_iff).1 (Subgroup.mem_subgroupOf.1 ht₂)
  set t₁' : G := (w : G) * (t₁ : G) * (w : G)⁻¹ with ht₁'def
  set t₂' : G := (w : G) * (t₂ : G) * (w : G)⁻¹ with ht₂'def
  set y' : G := (w : G) * (x : G) * (w : G)⁻¹ with hy'def
  set k' : G := (w : G) * k * (w : G)⁻¹ with hk'def
  have ht₁'V : t₁' ∈ V := by simpa [ht₁'def] using ht₁V
  have ht₂'Vg : t₂' ∈ conjSubgroup V g := by simpa [ht₂'def] using ht₂Vg
  have ht₁'U : t₁' ∉ UOf M V g := by
    intro hU
    have ht₁K : (t₁ : G) ∈ KOf M V g := by
      have h₁ := (Subgroup.mem_normalizer_iff.1
        (h.L_le_normalizer_K ((LOf V g).inv_mem w.2)) t₁').1
        (show t₁' ∈ KOf M V g from
          Subgroup.mem_sup_left (by simpa [ht₁'def] using hU))
      convert h₁ using 1
      rw [ht₁'def]
      group
    have hπ1 : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) t₁ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff t₁, Subgroup.mem_subgroupOf]
      exact ht₁K
    rw [ht₁π] at hπ1
    exact hs₁1 hπ1
  have ht₂'B : t₂' ∉ BOf M V g := by
    intro hB
    have ht₂K : (t₂ : G) ∈ KOf M V g := by
      have h₁ := (Subgroup.mem_normalizer_iff.1
        (h.L_le_normalizer_K ((LOf V g).inv_mem w.2)) t₂').1
        (show t₂' ∈ KOf M V g from
          Subgroup.mem_sup_right (by simpa [ht₂'def] using hB))
      convert h₁ using 1
      rw [ht₂'def]
      group
    have hπ2 : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) t₂ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff t₂, Subgroup.mem_subgroupOf]
      exact ht₂K
    rw [ht₂π] at hπ2
    exact hs₂1 hπ2
  have hπ12 : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ((t₁ * t₂)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, map_mul, ht₁π, ht₂π, hx]
    group
  have hmemL : (t₁ * t₂)⁻¹ * x ∈ (KOf M V g).subgroupOf (LOf V g) := by
    rw [← QuotientGroup.eq_one_iff ((t₁ * t₂)⁻¹ * x)]
    exact hπ12
  have hmemK : ((t₁ : G) * (t₂ : G))⁻¹ * (x : G) ∈ KOf M V g := by
    simpa using Subgroup.mem_subgroupOf.1 hmemL
  have hconj12 : (t₁' * t₂')⁻¹ * y' ∈ KOf M V g := by
    have h₁ := (Subgroup.mem_normalizer_iff.1 (h.L_le_normalizer_K w.2)
      (((t₁ : G) * (t₂ : G))⁻¹ * (x : G))).1 hmemK
    convert h₁ using 1
    rw [ht₁'def, ht₂'def, hy'def]
    group
  have hk'K : k' ∈ KOf M V g := by
    have h₁ := (Subgroup.mem_normalizer_iff.1 (h.L_le_normalizer_K w.2) k).1 hk
    simpa [hk'def] using h₁
  have hE : y' * k' * y'⁻¹ * k'⁻¹ ∈ NOf M V g := by
    have h₁ : (w : G) * ((x : G) * k * (x : G)⁻¹ * k⁻¹) * (w : G)⁻¹ ∈ NOf M V g := by
      have hmem : (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ conjSubgroup (NOf M V g) (w : G) := by
        rw [h.conjSubgroup_N_eq w.2]
        exact hxk
      exact (mem_conjSubgroup_iff).1 hmem
    convert h₁ using 1
    rw [hy'def, hk'def]
    group
  have hk' : k' ∈ NOf M V g :=
    mem_N_of_conj_mul_inv_mem h hgen ⟨l, hlL, hlV⟩ ht₁'V ht₁'U ht₂'Vg ht₂'B hconj12 hk'K hE
  have hkconj : k ∈ conjSubgroup (NOf M V g) (w : G) := by
    rw [mem_conjSubgroup_iff]
    exact hk'
  rwa [h.conjSubgroup_N_eq w.2] at hkconj

private theorem mem_N_of_torusData (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    {l : G} (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l)
    {T : Subgroup (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g))}
    (hT : TorusData (imgK M V g V)
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨l, hlL⟩) T)
    {Y' : Subgroup ↥(LOf V g)} (hY' : Y'.map
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) = T)
    (hodd : Odd (Nat.card Y')) {y : G} (hy : y ∈ Y'.map (LOf V g).subtype) (hy1 : y ≠ 1)
    {v : G} (hv : v ∈ V) (hyv : y * v * y⁻¹ = v) : v ∈ NOf M V g := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ (KOf M V g).subgroupOf L) :=
    QuotientGroup.mk' ((KOf M V g).subgroupOf L)
  rw [Subgroup.mem_map] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hy'1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hπyT : π y' ∈ T := hY' ▸ Subgroup.mem_map_of_mem π hy'
  have hπy1 : π y' ≠ 1 :=
    mk_ne_one_of_odd_card ((KOf M V g).subgroupOf L) (isPGroup_subgroupOf_LOf h) hodd
      hy' hy'1
  by_cases hvU : v ∈ UOf M V g
  · obtain ⟨c, s₁, hs₁, s₂, hs₂, hs₁1, hs₂1, hπ⟩ := hT.2.2.2.2.2.2 (π y') hπyT hπy1
    refine mem_N_of_mk_eq_mul h hgen hlL hlV hs₁ hs₂ hs₁1 hs₂1 hπ
      (show v ∈ KOf M V g from Subgroup.mem_sup_left hvU) ?_
    rw [show (y' : G) * v * (y' : G)⁻¹ = v from hyv, mul_inv_cancel]
    exact (NOf M V g).one_mem
  · let v' : ↥L := ⟨v, Subgroup.mem_sup_left hv⟩
    have hv'A : π v' ∈ imgK M V g V := by
      unfold imgK
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hv)
    have hv'1 : π v' ≠ 1 := fun hπ =>
      hvU (by
        rw [← h.V_inf_K]
        exact ⟨hv, (mk_eq_one_iff_mem_K M V g v').1 hπ⟩)
    have hfixL : y' * v' * y'⁻¹ = v' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hyv
    have hfixπ : π y' * π v' * (π y')⁻¹ = π v' := by
      simpa only [map_mul, map_inv] using congrArg π hfixL
    exact absurd (hT.2.2.2.2.2.1 (π y') hπyT (π v') hv'A hv'1 hfixπ) hπy1

theorem exists_torus_of_torusData (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    {l : G} (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l)
    {T : Subgroup (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g))}
    (hT : TorusData (imgK M V g V)
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨l, hlL⟩) T) :
    ∃ Y : Subgroup G, Y ≤ LOf V g ⊓ M ∧
      Nat.card Y = 2 ^ E3.mQuot V (conjSubgroup M g) - 1 ∧
      ∀ y ∈ Y, y ≠ 1 → ∀ v ∈ V, y * v * y⁻¹ = v → v ∈ NOf M V g := by
  have hcardA := card_imgK_eq_two_pow_mQuot h
  have hTcard : Nat.card T = 2 ^ E3.mQuot V (conjSubgroup M g) - 1 := by
    rw [hT.2.1, hcardA]
  have hAne : imgK M V g V ≠ ⊥ := h.imgK_V_ne_bot
  have h1lt : 1 < Nat.card (imgK M V g V) := (Subgroup.one_lt_card_iff_ne_bot _).2 hAne
  have h2 : 1 < 2 ^ E3.mQuot V (conjSubgroup M g) := by rw [← hcardA]; exact h1lt
  have hmq0 : E3.mQuot V (conjSubgroup M g) ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at h2
    exact lt_irrefl 1 h2
  have hTodd : Odd (Nat.card T) := by
    rw [hTcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.2 ⟨even_two, hmq0⟩) odd_one
  obtain ⟨Y', -, hY'card, hY'⟩ :=
    exists_isCyclic_map_eq_of_isPGroup ((KOf M V g).subgroupOf (LOf V g))
      (isPGroup_subgroupOf_LOf h) hT.1 hTodd
  have hYle : Y'.map (LOf V g).subtype ≤ LOf V g ⊓ M := by
    rintro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hπT : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y' ∈ T :=
      hY' ▸ Subgroup.mem_map_of_mem _ hy'
    exact ⟨y'.2, h.mem_M_of_image_mem_normalizer (hT.2.2.1 hπT)⟩
  have hcardY : Nat.card (Y'.map (LOf V g).subtype) =
      2 ^ E3.mQuot V (conjSubgroup M g) - 1 := by
    rw [Subgroup.card_map_of_injective (LOf V g).subtype_injective, hY'card, hTcard]
  have hoddY' : Odd (Nat.card Y') := by rw [hY'card]; exact hTodd
  refine ⟨Y'.map (LOf V g).subtype, hYle, hcardY, ?_⟩
  intro y hy hy1 v hv hyv
  exact mem_N_of_torusData h hgen hlL hlV hT hY' hoddY' hy hy1 hv hyv

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4F
public import CFSG.Quasithin.Vol2.Ch11SecO11H
public import CFSG.Quasithin.H13.J4TypeDefs
public import CFSG.Quasithin.Vol2.Ch11SecOE5F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4U

open CFSG.Open CFSG.Blueprint QuasithinUnique
open CFSG.Quasithin.H13.J4 (IsTypeJ4Centralizer IsAutTripleM22)

theorem isHat_of {D : Type} [Group D] (hperf : Group.IsPerfect D)
    (ψ : D →* CFSG.Quasithin.H13.J4.M22) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = Subgroup.center D) (hZc : Nat.card (Subgroup.center D) = 3) :
    IsHat D (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  let e : D ⧸ Subgroup.center D ≃* CFSG.Quasithin.H13.J4.M22 :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  obtain ⟨-, -, hsimple⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  have hsD : IsSimpleGroup (D ⧸ Subgroup.center D) := e.isSimpleGroup
  refine ⟨⟨hperf, hsD, ?_⟩, hZc, ⟨e⟩⟩
  by_contra hall
  push Not at hall
  have hper : Group.IsPerfect (D ⧸ Subgroup.center D) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center D))
      (QuotientGroup.mk'_surjective _)
  have hbot : commutator (D ⧸ Subgroup.center D) = ⊥ := by
    rw [eq_bot_iff]
    show ⁅(⊤ : Subgroup (D ⧸ Subgroup.center D)), (⊤ : Subgroup (D ⧸ Subgroup.center D))⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, hall a b]
    group
  have htop := hper.commutator_eq_top
  rw [hbot] at htop
  have h1 : Nat.card (D ⧸ Subgroup.center D) = 1 := by
    rw [← Subgroup.card_top, ← htop, Subgroup.card_bot]
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M22] at h1
  norm_num at h1

variable {G : Type} [Group G]

theorem isPGroup_subgroupOf {p : ℕ} {H K : Subgroup G} (hH : IsPGroup p H) :
    IsPGroup p ↥(H.subgroupOf K) :=
  hH.comap_of_injective K.subtype K.subtype_injective

variable [Finite G]

theorem card_map_mk {C : Type} [Group C] [Finite C] {N Y : Subgroup C} [N.Normal] (hNY : N ≤ Y)
    {a : ℕ} (hY : Nat.card Y = a * Nat.card N) : Nat.card (Y.map (QuotientGroup.mk' N)) = a := by
  have hker : (QuotientGroup.mk' N).ker ≤ Y := by rw [QuotientGroup.ker_mk']; exact hNY
  have hidx := Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N) hker
  have h1 := Subgroup.card_mul_index (Y.map (QuotientGroup.mk' N))
  have h2 := Subgroup.card_mul_index Y
  have h3 := Subgroup.card_mul_index N
  rw [hidx] at h1
  rw [hY] at h2
  have hN0 : 0 < Nat.card N := Nat.card_pos
  have hYi : 0 < Y.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (C ⧸ N) * Nat.card N = a * Y.index * Nat.card N := by
    rw [show Nat.card (C ⧸ N) = N.index from rfl, mul_comm N.index, h3, ← h2]
    ring
  have h5 : Nat.card (C ⧸ N) = a * Y.index := Nat.eq_of_mul_eq_mul_right hN0 h4
  rw [h5] at h1
  exact Nat.eq_of_mul_eq_mul_right hYi h1

theorem eq_of_le_centralizer
    {z : G} (hT : IsTypeJ4Centralizer G z) {S : Subgroup G}
    (hS : IsSylowTwoOf S ⊤) (hSz : S ≤ Subgroup.centralizer ({z} : Set G))
    {B₁ B₂ : Subgroup G} (h₁ : IsL24Sub S B₁) (h₂ : IsL24Sub S B₂)
    (hB₁ : B₁ ≤ Subgroup.centralizer ({z} : Set G))
    (hB₂ : B₂ ≤ Subgroup.centralizer ({z} : Set G)) : B₁ = B₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, -, hcore, hquot, -⟩ := hT
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set Q₀ := CFSG.pCore 2 ↥C with hQ₀
  set π := QuotientGroup.mk' Q₀ with hπ
  set S' := S.subgroupOf C with hS'
  have hQ₀c : Nat.card Q₀ = 2 ^ 13 := hcore.2.2.1
  have hQ₀2 : IsPGroup 2 Q₀ := CFSG.pCore_isPGroup
  have hS'2 : IsPGroup 2 S' := isPGroup_subgroupOf hS.2.1
  have hS'syl : IsSylowTwoOf S' ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hS'2, fun h => ?_⟩
    apply hS.2.2
    show 2 ∣ S.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.trans (Subgroup.relIndex_dvd_index_of_le hSz)
  have hQS : Q₀ ≤ S' := OE5.le_of_isPGroup hS'syl hQ₀2
    (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal).ge)
  have hS'c : Nat.card S' = 2 ^ 21 := by
    obtain ⟨k, hk⟩ := hS'2.exists_card_eq
    have h1 := Subgroup.card_mul_index S'
    rw [hk, hcard] at h1
    have hodd : S'.index % 2 = 1 := by
      have h := hS'syl.2.2
      rw [show (S'.subgroupOf ⊤).index = S'.index from Subgroup.relIndex_top_right S'] at h
      omega
    have h2 : S'.index * 2 ^ k = 10395 * 2 ^ 21 := by rw [mul_comm S'.index, h1]; norm_num
    have h3 := O11.odd_mul_two_pow_eq hodd (by norm_num) h2
    rw [h3] at h2
    have h4 : 2 ^ k = 2 ^ 21 := Nat.eq_of_mul_eq_mul_left (by norm_num) h2
    rw [hk, h4]
  have hk : ∀ {B : Subgroup G}, IsPGroup 2 ↥(π.ker.subgroupOf (B.subgroupOf C)) := fun {B} => by
    rw [hπ, QuotientGroup.ker_mk']
    exact isPGroup_subgroupOf hQ₀2
  have e₁ := isL24Sub_map_of_isPGroup (isL24Sub_subgroupOf h₁ hB₁) π hk
  have e₂ := isL24Sub_map_of_isPGroup (isL24Sub_subgroupOf h₂ hB₂) π hk
  set X := ↥C ⧸ Q₀ with hX
  have hXc : Nat.card X = 2661120 := by
    have h1 := Subgroup.card_mul_index Q₀
    rw [hQ₀c, hcard] at h1
    have h2 : 2 ^ 13 * Q₀.index = 2 ^ 13 * 2661120 := by rw [h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  set Sb := S'.map π with hSb
  have hSbc : Nat.card Sb = 2 ^ 8 :=
    card_map_mk hQS (by rw [hS'c, hQ₀c]; norm_num)
  obtain ⟨Z, -, hZc, hidx, hperf, hcen, -, hψ⟩ := hquot
  set D := Subgroup.centralizer (Z : Set X) with hD
  obtain ⟨ψ, -, hψs, hψk, -⟩ := hψ
  have hcenD : Subgroup.center ↥D = ψ.ker := by
    rw [hψk, ← hcen, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  have hZc' : Nat.card (Subgroup.center ↥D) = 3 := by
    rw [← hZc, ← hcen]
    exact (Subgroup.card_map_of_injective D.subtype_injective).symm
  have : D.Normal := Subgroup.normal_of_index_eq_two hidx
  have hD₁ : (B₁.subgroupOf C).map π ≤ D := le_of_perfect_of_index_two hidx e₁.2.1
  have hD₂ : (B₂.subgroupOf C).map π ≤ D := le_of_perfect_of_index_two hidx e₂.2.1
  have f₁ := isL24Sub_subgroupOf e₁ hD₁
  have f₂ := isL24Sub_subgroupOf e₂ hD₂
  have hDc : Nat.card D = 1330560 := by
    have h1 := Subgroup.card_mul_index D
    rw [hidx, hXc] at h1
    omega
  have hSD : Nat.card ↥(D ⊓ Sb) = 2 ^ 7 := by
    have h1 := Subgroup.relIndex_mul_card (H := D) (K := Sb)
    have h2 : D.relIndex Sb ∣ 2 := by
      have h := Subgroup.relIndex_dvd_index_of_normal D Sb
      rwa [hidx] at h
    rw [hSbc] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exfalso
      rw [Subgroup.relIndex_eq_one] at h
      have h3 : Nat.card Sb ∣ Nat.card D := Subgroup.card_dvd_of_le h
      rw [hSbc, hDc] at h3
      norm_num at h3
    · rw [h] at h1
      have h3 : 2 * Nat.card ↥(D ⊓ Sb) = 2 * 2 ^ 7 := by rw [h1]; norm_num
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
  have hSD' : Nat.card ↥(Sb.subgroupOf D) = 2 ^ 7 := by
    rw [← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Sb ⊓ D ≤ D)).toEquiv, inf_comm,
      hSD]
  have hSyl : IsSylowTwoOf (Sb.subgroupOf D) ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨isPGroup_subgroupOf (hS'2.map π), fun h => ?_⟩
    have h1 := Subgroup.card_mul_index (Sb.subgroupOf D)
    rw [hSD', hDc] at h1
    norm_num at h1
    have h2 : (Sb.subgroupOf D).index = 10395 := by omega
    rw [h2] at h
    norm_num at h
  have hHat := isHat_of hperf ψ hψs hcenD.symm hZc'
  have hU := O11.l24Unique_hatM22 hHat hSyl
  have hEq : (B₁.subgroupOf C).map π = (B₂.subgroupOf C).map π := by
    have h := hU _ _ f₁ f₂
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hD₁, inf_eq_left.mpr hD₂] at h
    exact h
  have hlift : ∀ {B : Subgroup G},
      ((B.subgroupOf C).map π ⊔ Sb).comap π = B.subgroupOf C ⊔ S' := fun {B} => by
    rw [hSb, hπ, ← Subgroup.map_sup, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr (hQS.trans le_sup_right)]
  have hsup : B₁.subgroupOf C ⊔ S' = B₂.subgroupOf C ⊔ S' := by
    rw [← hlift, ← hlift, hEq]
  have h12 := O11.eq_of_sup_eq hS'2 (isL24Sub_subgroupOf h₁ hB₁) (isL24Sub_subgroupOf h₂ hB₂)
    hsup
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hB₁, inf_eq_left.mpr hB₂] at h12
  exact h12

end CFSG.Quasithin.Vol2.Ch11.SecS.J4U

module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.L3YC

namespace Row18

section Sylow

variable {K : Type*} [Group K] [Finite K]

theorem card_eq_pow_of_isSylowTwoOf {N S : Subgroup K} (hS : IsSylowTwoOf S N) {k m : ℕ}
    (hN : Nat.card N = 2 ^ k * m) (hm : ¬ 2 ∣ m) : Nat.card S = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := hS.2.1
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hSp
  have h1 := Subgroup.card_mul_index (S.subgroupOf N)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hj, hN] at h1
  have ho : ¬ 2 ∣ (S.subgroupOf N).index := hS.2.2
  set o := (S.subgroupOf N).index with ho'
  rw [hj]
  rcases lt_trichotomy j k with h | h | h
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    have h2 : 2 ^ j * o = 2 ^ j * (2 ^ (d + 1) * m) := by
      rw [h1, pow_add, pow_succ]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    exact ho ⟨2 ^ d * m, by rw [h3]; ring⟩
  · rw [h]
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    have h2 : 2 ^ k * (2 ^ (d + 1) * o) = 2 ^ k * m := by
      rw [← h1, pow_add, pow_succ]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    exact hm ⟨2 ^ d * o, by rw [← h3]; ring⟩

theorem le_of_normalizes_of_card_dvd {N Lb S₀ : Subgroup K} (hS : IsSylowTwoOf S₀ N)
    (hLN : Lb ≤ N) (hnorm : S₀ ≤ Subgroup.normalizer (Lb : Set K))
    (hdvd : Nat.card S₀ ∣ Nat.card Lb) : S₀ ≤ Lb := by
  have h1 : Lb.relIndex (S₀ ⊔ Lb) = Lb.relIndex S₀ := B6.relIndex_sup_eq_of_le_normalizer hnorm
  obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hS.2.1 Lb
  have hW : S₀ ⊔ Lb ≤ N := sup_le hS.1 hLN
  have e1 : Lb.relIndex (S₀ ⊔ Lb) * Nat.card ↥(Lb ⊓ (S₀ ⊔ Lb)) = Nat.card ↥(S₀ ⊔ Lb) :=
    Subgroup.relIndex_mul_card Lb (S₀ ⊔ Lb)
  rw [inf_eq_left.mpr le_sup_right, h1, hn] at e1
  have hWN : Nat.card ↥(S₀ ⊔ Lb) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hW
  have hN := Subgroup.card_mul_index (S₀.subgroupOf N)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv] at hN
  have ho : ¬ 2 ∣ (S₀.subgroupOf N).index := hS.2.2
  obtain ⟨d, hd⟩ := hdvd
  rw [← e1, ← hN, hd] at hWN
  have hpos : 0 < Nat.card ↥S₀ := Nat.card_pos
  have hdiv : 2 ^ n * d ∣ (S₀.subgroupOf N).index := by
    have : Nat.card ↥S₀ * (2 ^ n * d) ∣ Nat.card ↥S₀ * (S₀.subgroupOf N).index := by
      convert hWN using 1
      ring
    exact (Nat.mul_dvd_mul_iff_left hpos).mp this
  have hn0 : n = 0 := by
    by_contra hne
    exact ho (((dvd_pow_self 2 hne).trans (dvd_mul_right _ _)).trans hdiv)
  have : Lb.relIndex (S₀ ⊔ Lb) = 1 := by rw [h1, hn, hn0, pow_zero]
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp this)

end Sylow

section Outer

open CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type*} [Group K] [Finite K]

theorem three_conj_inner_of_outer_le_two {N : Subgroup K} [N.Normal]
    (hout : Nat.card (Outer ↥N) ≤ 2) :
    ∀ g : K, (∃ m : ℕ, g ^ 3 ^ m = 1) →
      ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹ := by
  rintro g ⟨m, hg⟩
  have hfin : Finite (Outer ↥N) := inferInstance
  have hpos : 0 < Nat.card (Outer ↥N) := Nat.card_pos
  set α : MulAut ↥N := MulAut.conjNormal g with hα
  have hα3 : α ^ 3 ^ m = 1 := by
    rw [hα, ← map_pow, hg, map_one]
  have hsq : α ^ 2 ∈ inner ↥N := by
    have h2 : (QuotientGroup.mk α : Outer ↥N) ^ 2 = 1 := by
      have hc : Nat.card (Outer ↥N) = 1 ∨ Nat.card (Outer ↥N) = 2 := by omega
      rcases hc with hc | hc
      · have : Subsingleton (Outer ↥N) := (Nat.card_eq_one_iff_unique.mp hc).1
        exact Subsingleton.elim _ _
      · rw [← hc]
        exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow] at h2
    exact (QuotientGroup.eq_one_iff _).mp h2
  obtain ⟨k, hk⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ m))
  have h1 : (α ^ 2) ^ k * α = 1 := by
    rw [← pow_mul, ← pow_succ, ← hk]
    exact hα3
  have h2 : α = ((α ^ 2) ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hin : α ∈ inner ↥N := by
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq k)
  obtain ⟨n, hn⟩ := hin
  refine ⟨n.1, n.2, fun a ha => ?_⟩
  have := congrArg (fun τ : MulAut ↥N => (τ ⟨a, ha⟩ : _).1) hn
  simpa [hα, MulAut.conjNormal_apply, MulAut.conj_apply] using this.symm

end Outer

section Center

theorem eq_one_of_central_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) {z : X} (hz : ∀ a, z * a = a * z) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · have : z ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun g => (hz g).symm
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

theorem exists_noncomm_of_simple_not_prime {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hp : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup X := { ‹Group X› with mul_comm := fun a b => h a b }
  exact hp (IsSimpleGroup.prime_card (α := X))

end Center

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_mk_eq_three {H : Subgroup G} {x : G} (hx : x ∈ H) (hx3 : orderOf x = 3) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hx⟩) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨x, hx⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3')
    rw [this, map_one]
  · intro h
    have hmem : (⟨x, hx⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥H) (p := 2)) ⟨_, hmem⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => (z : ↥H).1) hk
      simpa using this
    have h3 : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem bar_le_normalizer {H L S : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
      Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  rintro _ ⟨⟨s, hsH⟩, hs, rfl⟩
  have hs' : s ∈ S := hs
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  obtain ⟨⟨l, hlH⟩, hl, rfl⟩ := ha
  have hl' : l ∈ L := hl
  have hc : s * l * s⁻¹ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hSL hs') l).mp hl'
    exact this
  refine ⟨⟨s * l * s⁻¹, H.mul_mem (H.mul_mem hsH hlH) (H.inv_mem hsH)⟩, hc, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem exists_bar_overgroup {H L S : Subgroup G} {t' x : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hSH : S ≤ H) (hS2 : IsPGroup 2 S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hL5 : ¬ p ∣ Nat.card L) (hxL : x ∈ L) (hx₂H : t'⁻¹ * x * t' ∈ H)
    (hconj : ∀ s ∈ S, t' * s * t'⁻¹ ∈ S) :
    ∃ Y : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), ¬ p ∣ Nat.card Y ∧
      (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤ Y ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t'⁻¹ * x * t', hx₂H⟩ ∈ Y := by
  set X₂ : Subgroup G := Subgroup.closure ((S : Set G) ∪ {t'⁻¹ * x * t'}) with hX₂
  have hSX : S ≤ X₂ := fun s hs => Subgroup.subset_closure (Or.inl hs)
  have hxX : t'⁻¹ * x * t' ∈ X₂ := Subgroup.subset_closure (Or.inr rfl)
  have hX₂H : X₂ ≤ H := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | hy)
    · exact hSH hy
    · rw [Set.mem_singleton_iff.mp hy]; exact hx₂H
  have hX₂c : X₂ ≤ B6.conjSub t'⁻¹ (L ⊔ S) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | hy)
    · refine B6.mem_conjSub.mpr ?_
      rw [inv_inv]
      exact (le_sup_right : S ≤ L ⊔ S) (hconj y hy)
    · rw [Set.mem_singleton_iff.mp hy]
      refine B6.mem_conjSub.mpr ?_
      rw [inv_inv]
      have : t' * (t'⁻¹ * x * t') * t'⁻¹ = x := by group
      rw [this]
      exact (le_sup_left : L ≤ L ⊔ S) hxL
  have hcardSup : Nat.card ↥(L ⊔ S) = 2 ^ (Classical.choose
      (B6.exists_relIndex_eq_two_pow_of_isPGroup hS2 L)) * Nat.card L := by
    have h1 : L.relIndex (S ⊔ L) = L.relIndex S := B6.relIndex_sup_eq_of_le_normalizer hSL
    have e1 : L.relIndex (S ⊔ L) * Nat.card ↥(L ⊓ (S ⊔ L)) = Nat.card ↥(S ⊔ L) :=
      Subgroup.relIndex_mul_card L (S ⊔ L)
    rw [inf_eq_left.mpr le_sup_right, h1,
      Classical.choose_spec (B6.exists_relIndex_eq_two_pow_of_isPGroup hS2 L)] at e1
    rw [sup_comm, ← e1]
  have h5 : ¬ p ∣ Nat.card ↥(L ⊔ S) := by
    rw [hcardSup]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      exact hp2 this
    · exact hL5 h
  have hcardConj : Nat.card ↥(B6.conjSub t'⁻¹ (L ⊔ S)) = Nat.card ↥(L ⊔ S) :=
    Subgroup.card_map_of_injective (MulAut.conj t'⁻¹).injective
  have hX5 : ¬ p ∣ Nat.card ↥X₂ := fun h =>
    h5 (hcardConj ▸ h.trans (Subgroup.card_dvd_of_le hX₂c))
  refine ⟨(X₂.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)), ?_, ?_, ?_⟩
  · intro h
    refine hX5 (h.trans ((Subgroup.card_map_dvd _ _).trans ?_))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₂H).toEquiv]
  · exact Subgroup.map_mono (fun y hy => hSX hy)
  · exact ⟨⟨t'⁻¹ * x * t', hx₂H⟩, hxX, rfl⟩

end Bar

end Row18

end Stellmacher.L3YC

end CFSG.Quasithin

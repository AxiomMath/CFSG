module

public import CFSG.Quasithin.Background.GoldschmidtS146RQuot

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Quot

variable {G : Type} [Group G] {H J : Subgroup G} [(J.subgroupOf H).Normal]

theorem card_imgJ_mul {Y : Subgroup G} (hJY : J ≤ Y) (hYH : Y ≤ H) :
    Nat.card ↥(imgJ H J Y) * Nat.card ↥J = Nat.card ↥Y := by
  let f : ↥Y →* ↥H ⧸ J.subgroupOf H :=
    (QuotientGroup.mk' (J.subgroupOf H)).comp (Subgroup.inclusion hYH)
  have hker : f.ker = J.subgroupOf Y := by
    ext x
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hrange : f.range = imgJ H J Y := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_imgJ.mpr ⟨Subgroup.inclusion hYH x, x.2, rfl⟩
    · intro hq
      obtain ⟨h, hh, rfl⟩ := mem_imgJ.mp hq
      exact ⟨⟨h, hh⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  have h2 : Nat.card ↥f.range = Nat.card ↥(imgJ H J Y) := by rw [hrange]
  have h3 : Nat.card ↥f.ker = Nat.card ↥J := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJY).toEquiv
  rw [← h2, ← h3]
  exact h1.symm

theorem card_imgJ_mul_inf {X : Subgroup G} (hXH : X ≤ H) :
    Nat.card ↥(imgJ H J X) * Nat.card ↥(X ⊓ J : Subgroup G) = Nat.card ↥X := by
  let f : ↥X →* ↥H ⧸ J.subgroupOf H :=
    (QuotientGroup.mk' (J.subgroupOf H)).comp (Subgroup.inclusion hXH)
  have hker : f.ker = J.subgroupOf X := by
    ext x
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hrange : f.range = imgJ H J X := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_imgJ.mpr ⟨Subgroup.inclusion hXH x, x.2, rfl⟩
    · intro hq
      obtain ⟨h, hh, rfl⟩ := mem_imgJ.mp hq
      exact ⟨⟨h, hh⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  have h2 : Nat.card ↥f.range = Nat.card ↥(imgJ H J X) := by rw [hrange]
  have h3 : Nat.card ↥f.ker = Nat.card ↥(X ⊓ J : Subgroup G) := by
    rw [hker]
    have : (J.subgroupOf X) = (X ⊓ J).subgroupOf X := by
      rw [Subgroup.inf_subgroupOf_left]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h2, ← h3]
  exact h1.symm

theorem imgJ_eq_top_iff {Y : Subgroup G} (hJY : J ≤ Y) (hYH : Y ≤ H) :
    imgJ H J Y = ⊤ ↔ Y = H := by
  constructor
  · intro h
    refine le_antisymm hYH fun x hx => ?_
    have h1 : ((⟨x, hx⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∈ imgJ H J Y := by rw [h]; trivial
    have := (mk_mem_imgJ hYH (hJY.trans hYH) ⟨x, hx⟩).mp h1
    simpa [sup_eq_left.mpr hJY] using this
  · rintro rfl
    exact imgJ_self

theorem le_normalizer_of_imgJ {S Y : Subgroup G} (hJS : J ≤ S) (hSY : S ≤ Y) (hYH : Y ≤ H)
    (h : imgJ H J Y ≤ Subgroup.normalizer ((imgJ H J S : Subgroup (↥H ⧸ J.subgroupOf H)) :
      Set (↥H ⧸ J.subgroupOf H))) :
    Y ≤ Subgroup.normalizer (S : Set G) := by
  have hSH : S ≤ H := hSY.trans hYH
  have hJH : J ≤ H := hJS.trans hSH
  have key : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have hy' : ((⟨y, hYH hy⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∈ imgJ H J Y :=
      mem_imgJ.mpr ⟨⟨y, hYH hy⟩, hy, rfl⟩
    have hs' : ((⟨s, hSH hs⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∈ imgJ H J S :=
      mem_imgJ.mpr ⟨⟨s, hSH hs⟩, hs, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (h hy') _).mp hs'
    have h2 : (((⟨y, hYH hy⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) * ((⟨s, hSH hs⟩ : ↥H) : ↥H ⧸
        J.subgroupOf H) * ((⟨y, hYH hy⟩ : ↥H) : ↥H ⧸ J.subgroupOf H)⁻¹) =
        ((⟨y * s * y⁻¹, H.mul_mem (H.mul_mem (hYH hy) (hSH hs)) (H.inv_mem (hYH hy))⟩ : ↥H) :
          ↥H ⧸ J.subgroupOf H) := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    rw [h2] at h1
    have := (mk_mem_imgJ hSH hJH _).mp h1
    simpa [sup_eq_left.mpr hJS] using this
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact fun hs => key y hy s hs
  · intro hs
    have := key y⁻¹ (Y.inv_mem hy) _ hs
    simpa [mul_assoc] using this

end Quot

section Perfect

variable {G : Type} [Group G] [Finite G]

theorem eq_of_normal_of_le_sup {K H N : Subgroup G} (hHK : H ≤ K) (hNK : N ≤ K)
    (hperf : ⁅K, K⁆ = K) (hN2 : IsPGroup 2 N) (hnorm : (H.subgroupOf K).Normal)
    (hKHN : K ≤ H ⊔ N) : H = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKnorm : K ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hnorm
  let f : ↥(N.subgroupOf K) →* ↥K ⧸ H.subgroupOf K :=
    (QuotientGroup.mk' (H.subgroupOf K)).comp (N.subgroupOf K).subtype
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (x : G) ∈ ((H ⊔ N : Subgroup G) : Set G) := hKHN x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H N (hNK.trans hKnorm)] at hx
    obtain ⟨h, hh, n, hn, hxhn⟩ := hx
    have hx1 : (x : ↥K) = ⟨h, hHK hh⟩ * ⟨n, hNK hn⟩ := Subtype.ext hxhn.symm
    refine ⟨⟨⟨n, hNK hn⟩, by simpa [Subgroup.mem_subgroupOf] using hn⟩, ?_⟩
    show (QuotientGroup.mk (⟨n, hNK hn⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) = QuotientGroup.mk x
    rw [hx1, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (⟨h, hHK hh⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by simpa [Subgroup.mem_subgroupOf] using hh)
    rw [this, one_mul]
  have hN' : IsPGroup 2 ↥(N.subgroupOf K) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have hQ2 : IsPGroup 2 (↥K ⧸ H.subgroupOf K) := hN'.of_surjective f hsurj
  have hQsolv : Group.IsSolvable (↥K ⧸ H.subgroupOf K) := by
    have := hQ2.isNilpotent
    infer_instance
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have hQperf : Group.IsPerfect (↥K ⧸ H.subgroupOf K) := inferInstance
  have hsub : Subsingleton (↥K ⧸ H.subgroupOf K) := by
    by_contra hns
    have : Nontrivial (↥K ⧸ H.subgroupOf K) := not_subsingleton_iff_nontrivial.mp hns
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K ⧸ H.subgroupOf K)).ne
      (Group.isPerfect_def.mp hQperf)
  refine le_antisymm hHK fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) = 1 := Subsingleton.elim _ _
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  simpa [Subgroup.mem_subgroupOf] using h2

theorem eq_of_subnormal_of_le_sup {A L N : Subgroup G} (hNL : N ≤ L) (hperf : ⁅L, L⁆ = L)
    (hN2 : IsPGroup 2 N) (hA : IsSubnormal A L) (hLAN : L ≤ A ⊔ N) : A = L := by
  induction hA with
  | refl => rfl
  | @step A M K hAM hnorm hMK ih =>
    have hMK' : M = K := ih hNL hperf (hLAN.trans (sup_le_sup_right hAM N))
    subst hMK'
    exact eq_of_normal_of_le_sup hAM hNL hperf hN2 hnorm hLAN

omit [Finite G] in
theorem subnormal_image_bot_or_top {A C : Subgroup G} (h : IsSubnormal A C) {S : Type*} [Group S]
    (hS : IsSimpleGroup S) (ρ : ↥C →* S) (hρ : Function.Surjective ρ) :
    (A.subgroupOf C).map ρ = ⊥ ∨ (A.subgroupOf C).map ρ = ⊤ := by
  induction h with
  | refl =>
    refine Or.inr ?_
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hρ
  | @step A M C hAM hn _ ih =>
    rcases ih ρ hρ with h | h
    · refine Or.inl (eq_bot_iff.mpr (le_trans ?_ h.le))
      exact Subgroup.map_mono fun x hx => hAM hx
    · rw [Subgroup.normal_subgroupOf_iff hAM] at hn
      have hN : ((A.subgroupOf C).map ρ).Normal := by
        refine ⟨?_⟩
        rintro _ ⟨x, hx, rfl⟩ s
        obtain ⟨y, hy, rfl⟩ : s ∈ (M.subgroupOf C).map ρ := h ▸ Subgroup.mem_top s
        refine ⟨y * x * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
        simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx hy ⊢
        simpa using hn _ _ hx hy
      exact hS.eq_bot_or_eq_top_of_normal _

end Perfect

end CFSG.Quasithin.GoldS146R

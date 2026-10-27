module

public import CFSG.RankThree.PartOne.S13K.N135Fit
public import CFSG.RankThree.PartOne.S12.Sec136
import CFSG.RankThree.PartOne.S12.Sec127
public import CFSG.RankThree.PartOne.S12.Sec138Trans
public import CFSG.RankThree.PartOne.S12.ZStarStep

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne

theorem node135_rank4 :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
      ¬ Outcome152Five p E A (lieGenerated p E) → Nat.card E = p ^ 4 →
      ∀ t ∈ reflectionSet p E, ∀ K : Subgroup G, IsKt p E t K → K ≤ L →
      ∀ u : ↥(torusWeyl E), (u : MulAut E) ∈ torusImage E L → u * u = 1 →
        (∀ b : E, (b : G) ∈ L → (u : MulAut E) b = b⁻¹) →
        (∀ g ∈ torusImage E L, g * (u : MulAut E) = (u : MulAut E) * g) →
        autFixedInG E (u : MulAut E) = Subgroup.zpowers c →
        ∀ N : Subgroup ↥(torusWeyl E), N.Normal → Odd (Nat.card N) → ∀ n ∈ N, n * u = u * n := by
  intro G _ _ p A c L E h hF hF13 _hT hcard t _ht K _hK _hKL u huΓ hu2 _hinv hucomm hfix N hN
    hNodd n hn
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  let _ : CommGroup ↥E := commGroupOf hEc
  have : IsElementaryAbelian p ↥E := h.E_elem
  have hexp : ∀ v : ↥E, v ^ p = 1 := fun v =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) v
  let c' : ↥E := ⟨c, hcE⟩
  have hc1 : c' ≠ 1 := fun h1 => h.c_ne_one (congrArg Subtype.val h1)
  let u₀ : MulAut ↥E := (u : MulAut E)
  have hfixE : ∀ e : ↥E, u₀ e = e ↔ e ∈ Subgroup.zpowers c' := by
    intro e
    rw [← mem_autFixedInG_iff_apply, hfix]
    constructor
    · intro he
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 he
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · intro he
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 he
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
  have hΛc : ∀ g ∈ torusImage E L, g c' = c' := fun g hg => apply_c_of_mem_torusImage h hcE hg
  have hfour : ∃ B₀ : Subgroup ↥E, ∀ S : Subgroup ↥E,
      (∀ g ∈ torusImage E L, ∀ s ∈ S, g s ∈ S) → S ≠ ⊥ → S ≠ ⊤ →
      S = Subgroup.zpowers c' ∨ S = B₀ := by
    refine ⟨(⁅E, L ⊓ torusNormalizer E⁆).comap E.subtype, fun S hS hSbot hStop => ?_⟩
    have hle : S.map E.subtype ≤ E := Subgroup.map_subtype_le S
    have hinv : torusInvariant E L (S.map E.subtype) := by
      rintro w ⟨hwL, hwN⟩ b hb
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hb
      have hwN' : w ∈ Subgroup.normalizer (E : Set G) := hwN
      have := hS _ (Sec138Trans.conjAut_mem_torusImage hwN' hwL) s hs
      exact Subgroup.mem_map.2 ⟨_, this, Equivariance.coe_conjAut hwN' s⟩
    have hne : S.map E.subtype ≠ ⊥ := fun h0 =>
      hSbot ((Subgroup.map_eq_bot_iff_of_injective S E.subtype_injective).1 h0)
    have hne' : S.map E.subtype ≠ E := by
      intro h0
      apply hStop
      have : S.map E.subtype = (⊤ : Subgroup ↥E).map E.subtype := by
        rw [h0, Subgroup.map_top, Subgroup.range_subtype]
      exact Subgroup.map_injective E.subtype_injective this
    rcases hF.four.1 _ hle hinv hne hne' with h1 | h1
    · left
      have : S.map E.subtype = (Subgroup.zpowers c').map E.subtype := by
        rw [h1, MonoidHom.map_zpowers]; rfl
      exact Subgroup.map_injective E.subtype_injective this
    · right
      have : S = (S.map E.subtype).comap E.subtype :=
        (Subgroup.comap_map_eq_self_of_injective E.subtype_injective S).symm
      rw [this, h1]
  have hirr : ∀ S : Subgroup ↥E, (∀ w ∈ torusWeyl E, ∀ s ∈ S, w s ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hle : S.map E.subtype ≤ E := Subgroup.map_subtype_le S
    have hinv : torusInvariant E ⊤ (S.map E.subtype) := by
      rintro w ⟨-, hwN⟩ b hb
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hb
      have hwN' : w ∈ Subgroup.normalizer (E : Set G) := hwN
      have hmem : conjAut E w hwN' ∈ torusWeyl E := ⟨⟨w, hwN'⟩, rfl⟩
      exact Subgroup.mem_map.2 ⟨_, hS _ hmem s hs, Equivariance.coe_conjAut hwN' s⟩
    rcases hF13.irreducible _ hle hinv with h1 | h1
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective S E.subtype_injective).1 h1
    · right
      have : S.map E.subtype = (⊤ : Subgroup ↥E).map E.subtype := by
        rw [h1, Subgroup.map_top, Subgroup.range_subtype]
      exact Subgroup.map_injective E.subtype_injective this
  have hΛW : torusImage E L ≤ torusWeyl E := Sec127.torusImage_le_torusWeyl E L
  let N' : Subgroup (MulAut ↥E) := N.map (torusWeyl E).subtype
  have hN'n : ∀ w ∈ torusWeyl E, ∀ m ∈ N', w * m * w⁻¹ ∈ N' := by
    intro w hw m hm
    obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.1 hm
    exact Subgroup.mem_map.2 ⟨⟨w, hw⟩ * m₀ * ⟨w, hw⟩⁻¹, hN.conj_mem m₀ hm₀ ⟨w, hw⟩, rfl⟩
  have hN'odd : Odd (Nat.card N') := by
    have : Nat.card N' = Nat.card N := Subgroup.card_map_of_injective (torusWeyl E).subtype_injective
    rw [this]
    exact hNodd
  have hu2' : u₀ * u₀ = 1 := congrArg Subtype.val hu2
  have hres := N135.commute_of_normal_odd hp2 hexp hcard hΛW hirr hu2' huΓ hucomm hc1 hΛc hfixE
    hfour hN'n hN'odd
  exact Subtype.ext (hres (n : MulAut ↥E) ⟨n, hn, rfl⟩)

end CFSG.RankThree.PartOne.S13K

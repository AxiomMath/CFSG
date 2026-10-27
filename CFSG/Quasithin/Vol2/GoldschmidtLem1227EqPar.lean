module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqBasic
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqA6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Lem1227Eq

variable {G : Type} [Group G]

theorem le_normalizer_inf_normalizer {T K W : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTW : T ≤ Subgroup.normalizer (W : Set G)) :
    T ≤ Subgroup.normalizer ((K ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hN : t ∈ Subgroup.normalizer (Subgroup.normalizer (W : Set G) : Set G) :=
    Subgroup.le_normalizer (hTW ht)
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hTK ht) x).1 hx1,
      (Subgroup.mem_normalizer_iff.1 hN x).1 hx2⟩
  · rintro ⟨hx1, hx2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hTK ht) x).2 hx1,
      (Subgroup.mem_normalizer_iff.1 hN x).2 hx2⟩

theorem le_normalizer_inf_self {T K : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨T.mul_mem (T.mul_mem ht hx1) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.1 (hTK ht) x).1 hx2⟩
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.1 (hTK ht) x).2 hx2⟩
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) hx1) ht
    simpa [mul_assoc] using this

variable [Finite G] {T K H M₀ W : Subgroup G}

theorem not_isDiagramNontrivial_of_stable_subgroup (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hiso : Nonempty (↥(E2.star M₀ H K) ≃* Alt6))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hJW : K ⊓ kerIn M₀ H ≤ Subgroup.normalizer (W : Set G))
    (hKW : ¬ K ≤ Subgroup.normalizer (W : Set G))
    (hidx : (K ⊓ Subgroup.normalizer (W : Set G)).relIndex K ≤ 44) :
    ¬ E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)) := by
  obtain ⟨-, hSyl⟩ := isSylowTwoOf_star hKH hHK hmin
  obtain ⟨e⟩ := hiso
  set Ks := E2.star M₀ H K with hKs
  set TKs := E2.star M₀ H (T ⊓ K) with hTKs
  set Pt : Subgroup G := K ⊓ Subgroup.normalizer (W : Set G) with hPt
  set P := E2.star M₀ H Pt with hP
  have hPK : P ≤ Ks := star_mono inf_le_left
  have hTP : TKs ≤ P := star_mono fun x hx => ⟨hx.2, hTW hx.1⟩
  have hTsN : E2.star M₀ H T ≤ Subgroup.normalizer (P : Set (E2.StarQuot M₀ H)) :=
    star_le_normalizer_star (le_normalizer_inf_normalizer hTK hTW)
  have hPne : P ≠ Ks := by
    intro hPK'
    apply hKW
    intro k hk
    have hmem : starMk M₀ H (Subgroup.inclusion hKH ⟨k, hk⟩) ∈ P := by
      rw [hPK']
      exact mem_star_iff.2 ⟨Subgroup.inclusion hKH ⟨k, hk⟩, hk, rfl⟩
    obtain ⟨h, hh, hhk⟩ := mem_star_iff.1 hmem
    have hj : (h : G)⁻¹ * k ∈ kerIn M₀ H := by
      have := (QuotientGroup.eq (s := (kerIn M₀ H).subgroupOf H)).1 hhk
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hjK : (h : G)⁻¹ * k ∈ K := K.mul_mem (K.inv_mem hh.1) hk
    have hjN := hJW ⟨hjK, hj⟩
    have hkN : (h : G) * ((h : G)⁻¹ * k) ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ hh.2 hjN
    simpa using hkN
  have hS' : IsSylowTwoOf (TKs.subgroupOf Ks) ⊤ := by
    rw [isSylowTwoOf_top_iff']
    exact ⟨hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm, hSyl.2.2⟩
  have hA6 := A6Syl.of_sylow e hS'
  have hKcard : Nat.card ↥Ks = 360 := by
    rw [Nat.card_congr e.toEquiv, card_Alt6]
  set P' : Subgroup ↥Ks := P.subgroupOf Ks with hP'
  have hP'idx : P'.index ≤ 44 := by
    have h1 : (Pt.subgroupOf K).index ≤ 44 := hidx
    have h2 : ((Pt.subgroupOf K).map (starHom M₀ hKH)).index ∣ (Pt.subgroupOf K).index :=
      Subgroup.index_map_dvd (Pt.subgroupOf K) (starHom_surjective M₀ hKH)
    have h3 : (Pt.subgroupOf K).map (starHom M₀ hKH) ≤ P' := by
      rintro _ ⟨k, hk, rfl⟩
      rw [hP', Subgroup.mem_subgroupOf]
      exact mem_star_iff.2 ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.1 hk, rfl⟩
    have h4 : P'.index ∣ ((Pt.subgroupOf K).map (starHom M₀ hKH)).index :=
      Subgroup.index_dvd_of_le h3
    have hpos : 0 < (Pt.subgroupOf K).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd hpos (h4.trans h2)).trans h1
  have hP'card : 8 < Nat.card P' := by
    have h := P'.index_mul_card
    rw [hKcard] at h
    by_contra hle
    push Not at hle
    have : P'.index * Nat.card P' ≤ 44 * 8 := Nat.mul_le_mul hP'idx hle
    omega
  have hSP' : TKs.subgroupOf Ks ≤ P' := Subgroup.subgroupOf_mono Ks hTP
  have hP'ne : P' ≠ ⊤ := by
    intro h
    exact hPne (le_antisymm hPK (Subgroup.subgroupOf_eq_top.1 h))
  obtain ⟨-, hmax⟩ := hA6.maximal_of_card_gt hSP' hP'ne hP'card
  refine not_isDiagramNontrivial_of_stable hSyl hPK hPne (fun R hRK hPR => ?_) ?_ hTsN
  · rcases hmax (R.subgroupOf Ks) (Subgroup.subgroupOf_mono Ks hPR) with h | h
    · left
      have := Subgroup.subgroupOf_inj.1 h
      rwa [inf_of_le_left hRK, inf_of_le_left hPK] at this
    · right
      exact le_antisymm hRK (Subgroup.subgroupOf_eq_top.1 h)
  · intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥Ks) ∈
        Subgroup.normalizer ((TKs.subgroupOf Ks : Subgroup ↥Ks) : Set ↥Ks) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have := Subgroup.mem_normalizer_iff.1 hx.2 y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using (this.trans (by simp))
    have := hA6.normalizer hxN
    exact hTP (Subgroup.mem_subgroupOf.1 this)

end Lem1227Eq

end CFSG.Quasithin.H13

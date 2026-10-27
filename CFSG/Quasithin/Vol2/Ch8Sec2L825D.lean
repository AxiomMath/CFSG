module

public import CFSG.Quasithin.H13.KGFact22TorusFacts
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

section L825D

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_star_82 {M I : Subgroup G} (hK : IsPGroup 2 ↥(kerIn (M ⊓ I) I))
    {Y : Subgroup (E2.StarQuot (M ⊓ I) I)} (hY : Y ≤ E2.star (M ⊓ I) I (M ⊓ I))
    (hYodd : Odd (Nat.card ↥Y)) :
    ∃ X : Subgroup G, X ≤ M ⊓ I ∧ E2.star (M ⊓ I) I X = Y ∧ Nat.card ↥X = Nat.card ↥Y ∧
      X ⊓ kerIn (M ⊓ I) I = ⊥ := by
  classical
  set K' := (kerIn (M ⊓ I) I).subgroupOf I with hK'
  set π := QuotientGroup.mk' K' with hπ
  set W : Subgroup ↥I := (M ⊓ I).subgroupOf I ⊓ Y.comap π with hW
  have hKMI : kerIn (M ⊓ I) I ≤ M ⊓ I := kerIn_le
  have hK'W : K' ≤ W := by
    intro x hx
    refine ⟨hKMI hx, ?_⟩
    show π x ∈ Y
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Y.one_mem
  have hWY : W.map π = Y := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · intro y hy
      obtain ⟨m, hm, hmy⟩ := hY hy
      refine ⟨m, ⟨hm, ?_⟩, hmy⟩
      show π m ∈ Y
      rw [hmy]
      exact hy
  set N := K'.subgroupOf W with hN
  have : N.Normal := Subgroup.Normal.subgroupOf inferInstance W
  have hNcard : Nat.card ↥N = Nat.card ↥K' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'W).toEquiv
  have hK'card : Nat.card ↥K' = Nat.card ↥(kerIn (M ⊓ I) I) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (kerIn_le.trans inf_le_right)).toEquiv
  set φ : ↥W →* E2.StarQuot (M ⊓ I) I := π.comp W.subtype with hφ
  have hker : φ.ker = N := by
    ext w
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    rfl
  have hrange : φ.range = Y := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hWY]
  have hidx : N.index = Nat.card ↥Y := by
    rw [Subgroup.index_eq_card, ← hker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange]
  have hcop : Nat.Coprime (Nat.card ↥N) N.index := by
    rw [hidx, hNcard, hK'card]
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hK
    rw [ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hYodd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHN : H ⊓ N = ⊥ := disjoint_iff.mp hH.disjoint.symm
  have hHcard : Nat.card ↥H = Nat.card ↥Y := by
    have h1 := hH.card_mul_card
    have h2 := N.card_mul_index
    rw [hidx] at h2
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    have h3 : Nat.card ↥N * Nat.card ↥H = Nat.card ↥N * Nat.card ↥Y := by rw [h1, h2]
    exact Nat.eq_of_mul_eq_mul_left hpos h3
  have hφH : Function.Injective (φ.comp H.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have hxN : (x : ↥W) ∈ N := by rw [← hker]; exact hx
    have : (x : ↥W) ∈ H ⊓ N := ⟨x.2, hxN⟩
    rw [hHN, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hHmap : H.map φ = Y := by
    have hle : H.map φ ≤ Y := by
      rw [← hrange]
      exact Subgroup.map_le_range φ H
    have hcard : Nat.card ↥(H.map φ) = Nat.card ↥H := by
      have h1 : H.map φ = (φ.comp H.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [h1]
      exact (Nat.card_congr (MonoidHom.ofInjective hφH).toEquiv).symm
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hHcard])
  refine ⟨(H.map W.subtype).map I.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨h, -, rfl⟩, rfl⟩
    exact (h : ↥W).2.1
  · show (((H.map W.subtype).map I.subtype).subgroupOf I).map π = Y
    have h1 : ((H.map W.subtype).map I.subtype).subgroupOf I = H.map W.subtype :=
      Subgroup.comap_map_eq_self_of_injective I.subtype_injective _
    rw [h1, Subgroup.map_map]
    exact hHmap
  · rw [Subgroup.card_map_of_injective I.subtype_injective,
      Subgroup.card_map_of_injective W.subtype_injective, hHcard]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨_, ⟨h, hh, rfl⟩, rfl⟩, hk⟩
    have hhN : h ∈ N := by
      show ((h : ↥W) : ↥I) ∈ K'
      exact hk
    have : h ∈ H ⊓ N := ⟨hh, hhN⟩
    rw [hHN, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _

omit [Finite G] in
theorem isSylowTwoOf_star_82 {T M I : Subgroup G} (hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ I) I) :
    QuasithinUnique.IsSylowTwoOf (E2.star (M ⊓ I) I (T ⊓ I)) ⊤ := by
  obtain ⟨hTI, hp, hidx⟩ := hSyl
  set P := (T ⊓ I).subgroupOf I with hP
  have hPp : IsPGroup 2 ↥P := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hTI).symm
  refine ⟨le_top, hPp.map _, ?_⟩
  intro h2
  apply hidx
  have h1 : (E2.star (M ⊓ I) I (T ⊓ I)).index ∣ P.index :=
    Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
  have h3 : ((E2.star (M ⊓ I) I (T ⊓ I)).subgroupOf ⊤).index =
      (E2.star (M ⊓ I) I (T ⊓ I)).index :=
    Subgroup.relIndex_top_right _
  rw [h3] at h2
  exact h2.trans h1

theorem exists_cartan_82 {T M I : Subgroup G} {k : ℕ} (hK : IsPGroup 2 ↥(kerIn (M ⊓ I) I))
    (hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ I) I)
    (hB : E2.star (M ⊓ I) I (M ⊓ I) =
      Subgroup.normalizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (hk : 2 ≤ k)
    (hI : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) :
    ∃ X : Subgroup G, X ≤ M ⊓ I ∧ IsCyclic ↥X ∧ Nat.card ↥X = 2 ^ k - 1 ∧
      X ⊓ kerIn (M ⊓ I) I = ⊥ := by
  have hBen : E2.IsBenderOf k (E2.StarQuot (M ⊓ I) I) := by
    refine ⟨hk, ?_⟩
    rcases hI with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨Y, -, -, hYN, -, -, hYcyc, -, hYcard, -⟩ :=
    e22TorusFacts_holds (E2.StarQuot (M ⊓ I) I) k hk (Or.inl hBen) _ (isSylowTwoOf_star_82 hSyl)
  have hYodd : Odd (Nat.card ↥Y) := by
    rw [hYcard]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  obtain ⟨X, hXMI, hXY, hXc, hXK⟩ := exists_lift_star_82 hK (hYN.trans hB.symm.le) hYodd
  refine ⟨X, hXMI, ?_, hXc.trans hYcard, hXK⟩
  have hXI : X ≤ I := hXMI.trans inf_le_right
  let f : ↥X →* E2.StarQuot (M ⊓ I) I :=
    (QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I)).comp (Subgroup.inclusion hXI)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    have : (x : G) ∈ X ⊓ kerIn (M ⊓ I) I := ⟨x.2, hx⟩
    rw [hXK, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hfr : f.range = Y := by
    rw [← hXY]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hXI x.2⟩, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have : IsCyclic ↥f.range := by rw [hfr]; exact hYcyc
  exact isCyclic_of_surjective (MonoidHom.ofInjective hf).symm.toMonoidHom
    (MonoidHom.ofInjective hf).symm.surjective

end L825D

end CFSG.Quasithin.H13

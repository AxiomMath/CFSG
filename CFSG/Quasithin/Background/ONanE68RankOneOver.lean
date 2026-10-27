module

public import CFSG.Quasithin.Background.ONanE68RankOneModel
import CFSG.Holt.Bender
import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences

public section

namespace CFSG.Quasithin.E6.E68Proof

namespace RankOne

open CFSG.Open CFSG.Holt

variable {S : Type} [Group S] [Finite S]

theorem exists_fourGroup_le {q k : ℕ} (hB : fusionBenderBorel S q k) (P : Sylow 2 S)
    (hq : 4 ∣ q) : ∃ V : Subgroup S, V ≤ (P : Subgroup S) ∧ Nat.card V = 4 ∧
      ∀ v ∈ V, v ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Subgroup.center (P : Subgroup S))
    2 (n := 2) (by rw [(hB P).2.2.2.1]; exact hq)
  let V : Subgroup S := (K.map (Subgroup.center (P : Subgroup S)).subtype).map
    (P : Subgroup S).subtype
  refine ⟨V, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · change Nat.card ((K.map (Subgroup.center (P : Subgroup S)).subtype).map
      (P : Subgroup S).subtype) = 4
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
    norm_num
  · rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    have h := congrArg Subtype.val ((hB P).2.2.1 z z.2)
    simpa using h

theorem eq_one_of_orderOf_two_pow {G : Type*} [Group G] {x : G} {m n : ℕ}
    (hx : orderOf x = 2 ^ m) (hn : Odd n) (hd : orderOf x ∣ n) : x = 1 := by
  rw [← orderOf_eq_one_iff]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [hx, h0, pow_zero]
  · have h2 : 2 ∣ n := (dvd_pow_self 2 hpos.ne').trans (hx ▸ hd)
    exact absurd h2 (Nat.not_even_iff_odd.mpr hn ∘ even_iff_two_dvd.mpr)

omit [Finite S] in
theorem fusionStronglyEmbedded_subgroupOf {M Y P : Subgroup S} (hSE : fusionStronglyEmbedded M)
    (hYM : ¬ Y ≤ M) (hPM : P ≤ M) (hPY : P ≤ Y) (hP2 : 2 ∣ Nat.card P) :
    fusionStronglyEmbedded (M.subgroupOf Y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hYM
    intro y hy
    have : (⟨y, hy⟩ : Y) ∈ M.subgroupOf Y := htop ▸ Subgroup.mem_top _
    exact this
  · have hle : P.subgroupOf Y ≤ M.subgroupOf Y := fun x hx => hPM hx
    have h1 : Nat.card (P.subgroupOf Y) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv
    exact even_iff_two_dvd.mpr (h1 ▸ hP2 |>.trans (Subgroup.card_dvd_of_le hle))
  · intro g hg
    have hgM : (g : S) ∉ M := hg
    refine Odd.of_dvd_nat (hSE.2.2 (g : S) hgM) ?_
    rw [← Subgroup.card_map_of_injective (f := Y.subtype) (Subgroup.subtype_injective Y)]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨x, ⟨hxH, hxH'⟩, rfl⟩
    refine ⟨hxH, ?_⟩
    obtain ⟨h, hh, hhx⟩ := hxH'
    exact ⟨(h : S), hh, by simpa using congrArg Subtype.val hhx⟩

theorem normal_odd_eq_bot {Y : Subgroup S} (P : Sylow 2 S) (hPY : (P : Subgroup S) ≤ Y)
    (hH : fusionStronglyEmbedded
      ((Subgroup.normalizer ((P : Subgroup S) : Set S)).subgroupOf Y))
    {V : Subgroup S} (hVP : V ≤ (P : Subgroup S)) (hV4 : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hcent : ∀ y : S, (∀ p ∈ (P : Subgroup S), y * p = p * y) → y ∈ (P : Subgroup S))
    (R : Subgroup Y) (hR : R.Normal) (hRodd : Odd (Nat.card R)) : R = ⊥ := by
  have hVY : V ≤ Y := hVP.trans hPY
  have hV'H : V.subgroupOf Y ≤ (Subgroup.normalizer ((P : Subgroup S) : Set S)).subgroupOf Y :=
    fun v hv => Subgroup.le_normalizer (hVP hv)
  have hV'4 : Nat.card (V.subgroupOf Y) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv
  have hRH : R ≤ (Subgroup.normalizer ((P : Subgroup S) : Set S)).subgroupOf Y :=
    CFSG.BenderSuzuki.fourGroup_odd_subgroup_le_stronglyEmbedded
      (CFSG.ShultStronglyClosedTI.native_strong_embedding_of_order_conditions hH) hV'H hV'4
      (fun u => Subtype.ext (Subtype.ext (hV2 ((u : Y) : S) u.2)))
      (Subgroup.le_normalizer_of_normal) hRodd
  have key : ∀ x : Y, x ∈ R → (x : S) ∈ (P : Subgroup S) → x = 1 := by
    intro x hxR hxP
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨(x : S), hxP⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hm
    have hd : orderOf x ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨x, hxR⟩ : R)
      rwa [Subgroup.orderOf_mk] at this
    exact eq_one_of_orderOf_two_pow hm hRodd hd
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hrN : (r : S) ∈ Subgroup.normalizer ((P : Subgroup S) : Set S) := hRH hr
  have hcomm : ∀ p ∈ (P : Subgroup S), (r : S) * p = p * (r : S) := by
    intro p hp
    let g : Y := ⟨p, hPY hp⟩
    have hc'R : r * (g * r⁻¹ * g⁻¹) ∈ R := R.mul_mem hr (hR.conj_mem r⁻¹ (R.inv_mem hr) g)
    have hc'P : ((r * (g * r⁻¹ * g⁻¹) : Y) : S) ∈ (P : Subgroup S) := by
      have h1 : (r : S) * p * (r : S)⁻¹ ∈ (P : Subgroup S) :=
        (Subgroup.mem_normalizer_iff.mp hrN p).mp hp
      have h2 : ((r * (g * r⁻¹ * g⁻¹) : Y) : S) = (r : S) * p * (r : S)⁻¹ * p⁻¹ := by
        simp [g, mul_assoc]
      rw [h2]
      exact (P : Subgroup S).mul_mem h1 ((P : Subgroup S).inv_mem hp)
    have h3 := key _ hc'R hc'P
    have h4 := congrArg Subtype.val h3
    have h2 : ((r * (g * r⁻¹ * g⁻¹) : Y) : S) = (r : S) * p * (r : S)⁻¹ * p⁻¹ := by
      simp [g, mul_assoc]
    rw [h2] at h4
    simp only [Subgroup.coe_one] at h4
    calc (r : S) * p = (r : S) * p * (r : S)⁻¹ * p⁻¹ * p * (r : S) := by group
      _ = p * (r : S) := by rw [h4]; group
  exact key r hr (hcent r hcomm)

theorem normalizer_of_proper_overgroup
    {q k : ℕ} (hM : ModelOf S q k) (P : Sylow 2 S)
    (hcent : ∀ y : S, (∀ p ∈ (P : Subgroup S), y * p = p * y) → y ∈ (P : Subgroup S))
    {Y : Subgroup S} (hPY : (P : Subgroup S) ≤ Y) (hY : Y ≠ ⊤) :
    Y ≤ Subgroup.normalizer ((P : Subgroup S) : Set S) := by
  by_contra hYM
  have hB := hM.fusionBenderBorel
  obtain ⟨hq4, hq4', hk1, hk3⟩ := hM.params
  have hPM : (P : Subgroup S) ≤ Subgroup.normalizer ((P : Subgroup S) : Set S) :=
    Subgroup.le_normalizer
  have hP2 : 2 ∣ Nat.card (P : Subgroup S) := by
    rw [(hB P).2.2.2.2]
    exact ((Dvd.dvd.trans (by norm_num : 2 ∣ 4) hq4')).trans (dvd_pow_self q (by omega))
  have hH := fusionStronglyEmbedded_subgroupOf (hB P).1 hYM hPM hPY hP2
  obtain ⟨V, hVP, hV4, hV2⟩ := exists_fourGroup_le hB P hq4'
  have hO : ∀ R : Subgroup Y, R.Normal → Odd (Nat.card R) → R = ⊥ := fun R hR hRodd =>
    normal_odd_eq_bot P hPY hH hVP hV4 hV2 hcent R hR hRodd
  have hVY : V ≤ Y := hVP.trans hPY
  have hV'4 : Nat.card (V.subgroupOf Y) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv
  obtain ⟨N, q', i', hN⟩ := exists_isBenderNormal_quotient hH hO hV'4
    (fun v hv => Subtype.ext (hV2 (v : S) hv))
  have hcard := hN.card_sylow (P.subtype hPY)
  have hcen := hN.card_center_sylow (P.subtype hPY)
  rw [Sylow.coe_subtype] at hcard hcen
  have e1 : Nat.card ((P : Subgroup S).subgroupOf Y) = Nat.card (P : Subgroup S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv
  have e2 : Nat.card (Subgroup.center ((P : Subgroup S).subgroupOf Y)) =
      Nat.card (Subgroup.center (P : Subgroup S)) :=
    Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hPY)).toEquiv
  rw [e1, (hB P).2.2.2.2] at hcard
  rw [e2, (hB P).2.2.2.1] at hcen
  subst hcen
  have hik : i' = k := (Nat.pow_right_injective (by omega : 2 ≤ q) hcard).symm
  subst hik
  have hNmodel : ModelOf N q i' := hN.model
  obtain ⟨e⟩ := hNmodel.nonempty_mulEquiv hM
  have h1 : Nat.card N = Nat.card S := Nat.card_congr e.toEquiv
  have h2 : Nat.card N ≤ Nat.card Y := Subgroup.card_le_card_group N
  apply hY
  rw [← Subgroup.card_eq_iff_eq_top]
  exact le_antisymm (Subgroup.card_le_card_group Y) (h1 ▸ h2)

end RankOne

end CFSG.Quasithin.E6.E68Proof

module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

section Ranks

variable {G : Type} [Group G] [Finite G]

theorem le_card_of_card_eq_pow {p k : ℕ} (hp : 2 ≤ p) (E : Subgroup G)
    (hE : Nat.card E = p ^ k) : k ≤ Nat.card G := by
  have h1 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  have h2 : k < p ^ k := Nat.lt_pow_self (by omega)
  exact h2.le.trans (hE ▸ h1)

theorem bddAbove_pRank_set (p : ℕ) (hp : 2 ≤ p) (H : Subgroup G) :
    BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k} :=
  ⟨Nat.card G, fun _ ⟨E, _, _, hE⟩ => le_card_of_card_eq_pow hp E hE⟩

theorem pRank_le_card (p : ℕ) (hp : 2 ≤ p) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ Nat.card G := by
  unfold CFSG.Open.pRank
  refine csSup_le' fun _ hk => ?_
  obtain ⟨E, _, _, hE⟩ := hk
  exact le_card_of_card_eq_pow hp E hE

theorem pRank_mono (p : ℕ) (hp : 2 ≤ p) {H K : Subgroup G} (hHK : H ≤ K) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p K := by
  unfold CFSG.Open.pRank
  refine csSup_le' fun k hk => ?_
  obtain ⟨E, hEH, hE, hk'⟩ := hk
  exact le_csSup (bddAbove_pRank_set p hp K) ⟨E, hEH.trans hHK, hE, hk'⟩

theorem pRank_le_map {X : Type} [Group X] [Finite X] (p : ℕ) (hp : 2 ≤ p) (f : X →* G)
    (hf : Function.Injective f) (K : Subgroup X) :
    CFSG.Open.pRank p K ≤ CFSG.Open.pRank p (K.map f) := by
  unfold CFSG.Open.pRank
  refine csSup_le' fun k hk => ?_
  obtain ⟨E, hEK, hE, hk'⟩ := hk
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have himg : CFSG.Open.IsElemAbelian p (E.map f) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hax, ← hby, ← map_mul, ← map_mul, hEc a ha b hb]
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hE.2 a ha, map_one]
  have hcard : Nat.card (E.map f) = p ^ k := by
    rw [Subgroup.card_map_of_injective hf, hk']
  exact le_csSup (bddAbove_pRank_set p hp (K.map f)) ⟨E.map f, Subgroup.map_mono hEK, himg, hcard⟩

theorem pRank_le_evenRank {p : ℕ} {N : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : CFSG.Open.IsTwoLocal N) : CFSG.Open.pRank p N ≤ CFSG.Open.evenRank G := by
  unfold CFSG.Open.evenRank
  refine le_csSup ⟨Nat.card G, fun k hk => ?_⟩
    ⟨p, N, hp, hp2, hN, rfl⟩
  obtain ⟨p', H, hp', -, -, hk'⟩ := hk
  rw [← hk']
  exact pRank_le_card p' hp'.two_le H

theorem pRank_le_two_of_normalizer (hG : CFSG.Open.evenRank G ≤ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K P : Subgroup G} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P)
    (hK : K ≤ Subgroup.normalizer (P : Set G)) : CFSG.Open.pRank p K ≤ 2 :=
  calc CFSG.Open.pRank p K ≤ CFSG.Open.pRank p (Subgroup.normalizer (P : Set G)) :=
        pRank_mono p hp.two_le hK
    _ ≤ CFSG.Open.evenRank G := pRank_le_evenRank hp hp2 ⟨P, hP, hP2, rfl⟩
    _ ≤ 2 := hG

theorem pRank_le_two_centralizer (hG : CFSG.Open.evenRank G ≤ 2) {u : G} (hu : u * u = 1)
    (hu1 : u ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (Subgroup.centralizer ({u} : Set G)) ≤ 2 := by
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
  have hP : Subgroup.zpowers u ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hu1
  have hP2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  refine pRank_le_two_of_normalizer hG hp hp2 hP hP2 ?_
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hgu : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgu' : g * u * g⁻¹ = u := by
    rw [hgu, mul_inv_cancel_right]
  rw [← conj_zpow, hgu']
  exact Subgroup.zpow_mem_zpowers u k

theorem isQuasithin_of_injective (hG : CFSG.Open.evenRank G ≤ 2) {X : Type} [Group X]
    [Finite X] (f : X →* G) (hf : Function.Injective f) : CFSG.Quasithin.IsQuasithin X := by
  unfold CFSG.Quasithin.IsQuasithin CFSG.Open.evenRank
  refine csSup_le' fun k hk => ?_
  obtain ⟨p, N, hp, hp2, ⟨P, hP, hP2, hN⟩, hk'⟩ := hk
  rw [← hk']
  have hPf : P.map f ≠ ⊥ := by
    intro h
    apply hP
    rw [eq_bot_iff]
    intro x hx
    have hfx : f x ∈ P.map f := Subgroup.mem_map_of_mem f hx
    rw [h, Subgroup.mem_bot] at hfx
    exact Subgroup.mem_bot.mpr (hf (by rw [hfx, map_one]))
  have hPf2 : IsPGroup 2 (P.map f) := hP2.map f
  have hNf : (Subgroup.normalizer (P : Set X)).map f ≤
      Subgroup.normalizer ((P.map f : Subgroup G) : Set G) := by
    rintro _ ⟨h, hh, rfl⟩
    have hPc : ∀ y : X, y ∈ P ↔ h * y * h⁻¹ ∈ P := fun y => Subgroup.mem_normalizer_iff.mp hh y
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have e : f h * f y * (f h)⁻¹ = f (h * y * h⁻¹) := by simp only [map_mul, map_inv]
      rw [e]
      exact Subgroup.mem_map_of_mem f ((hPc y).mp hy)
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨h⁻¹ * z * h, ?_, ?_⟩
      · exact (hPc _).mpr (by simpa [mul_assoc] using hz)
      · simp only [map_mul, map_inv]
        rw [hzx]
        group
  have hNN : N = Subgroup.normalizer (P : Set X) := hN
  rw [hNN]
  calc CFSG.Open.pRank p (Subgroup.normalizer (P : Set X))
      ≤ CFSG.Open.pRank p ((Subgroup.normalizer (P : Set X)).map f) :=
        pRank_le_map p hp.two_le f hf _
    _ ≤ 2 := pRank_le_two_of_normalizer hG hp hp2 hPf hPf2 hNf

theorem isKGroupCat_of_proper {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {H : Subgroup G} (hH : H ≠ ⊤) :
    CFSG.SectionRank.IsKGroupCat ↥H :=
  CFSG.KCore.KProperNonab.kGroupAllSimple CFSG.SectionRank.catalog_isoInvariant
    CFSG.SectionRank.catalog_containsAbelianSimple hK H hH

end Ranks

end CFSG.Quasithin.H13.Ch4.J4KX

end

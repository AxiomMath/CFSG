module

public import CFSG.Quasithin.H13.GoldschmidtU43EExcl
public import CFSG.Quasithin.H13.GoldschmidtU43DA6
public import CFSG.Quasithin.H13.GoldschmidtU43EA6Sylow
public import CFSG.Quasithin.H13.GoldschmidtU43EFrat
public import CFSG.Quasithin.H13.GoldschmidtU43EOrder

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)
include S

theorem inj_on_PK {φ : ↥S.K1 →* Equiv.Perm (Fin 6)} (hker : φ.ker = S.E1.subgroupOf S.K1)
    (PK : Sylow 3 ↥S.K1) : ∀ p ∈ (PK : Subgroup ↥S.K1), φ p = 1 → p = 1 := by
  intro p hp hφ
  have hpE : (p : G) ∈ S.E1 := by
    have : p ∈ φ.ker := MonoidHom.mem_ker.mpr hφ
    rw [hker] at this
    exact this
  set T' : Subgroup G := (PK : Subgroup ↥S.K1).map S.K1.subtype with hT'
  have hpT : (p : G) ∈ T' := ⟨p, hp, rfl⟩
  have hT'card : Nat.card T' = 9 := by
    rw [hT', Subgroup.card_map_of_injective S.K1.subtype_injective]
    exact S.card_PK PK
  have h1 : Nat.card ↥(T' ⊓ S.E1) ∣ 9 := hT'card ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(T' ⊓ S.E1) ∣ 16 := S.card_E1 ▸ Subgroup.card_dvd_of_le inf_le_right
  have h3 : Nat.card ↥(T' ⊓ S.E1) = 1 := by
    have := Nat.dvd_gcd h1 h2
    have e : Nat.gcd 9 16 = 1 := by norm_num
    rw [e] at this
    exact Nat.dvd_one.mp this
  have hbot : T' ⊓ S.E1 = ⊥ := Subgroup.card_eq_one.mp h3
  have : (p : G) ∈ T' ⊓ S.E1 := ⟨hpT, hpE⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem card_Mg_ne_nine : Nat.card S.Mg ≠ 9 := by
  intro h9
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hker, hrange⟩ := S.e.swap.exists_hom_A6 S.e.ha
  obtain ⟨PK⟩ : Nonempty (Sylow 3 ↥S.K1) := Sylow.nonempty
  obtain ⟨g, hg⟩ := S.exists_conj_Tg h9 PK
  set Sbar : Subgroup (Equiv.Perm (Fin 6)) := (PK : Subgroup ↥S.K1).map φ with hSbar
  have hinj := S.inj_on_PK hker PK
  have hScard : Nat.card Sbar = 9 := by
    rw [hSbar, card_map_of_trivial_ker φ _ hinj]
    exact S.card_PK PK
  obtain ⟨hcent, nbar, hsign, hnorm, hsq⟩ := A6Sylow.S6_sylow3 Sbar hScard
  have hnbar : nbar ∈ φ.range := by
    rw [hrange]
    exact Equiv.Perm.mem_alternatingGroup.mpr hsign
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp hnbar
  have hnormS : φ g' ∈ Subgroup.normalizer (Sbar : Set (Equiv.Perm (Fin 6))) := by
    rw [hg']
    exact Subgroup.mem_normalizer_iff.mpr hnorm
  obtain ⟨m, hmN, s₁, hs₁, hm⟩ := exists_normalizer_lift φ PK hnormS
  have hA : φ (m * m) ∉ Sbar := by
    intro hin
    apply hsq
    have e : φ (m * m) = nbar * s₁ * (nbar * s₁) := by rw [map_mul, hm, hg']
    have hconj : nbar⁻¹ * s₁ * nbar ∈ Sbar := by
      rw [hnorm (nbar⁻¹ * s₁ * nbar)]
      have : nbar * (nbar⁻¹ * s₁ * nbar) * nbar⁻¹ = s₁ := by group
      rw [this]
      exact hs₁
    have : nbar * nbar = φ (m * m) * (((nbar⁻¹ * s₁ * nbar) * s₁)⁻¹) := by
      rw [e]
      group
    rw [this]
    exact mul_mem hin (inv_mem (mul_mem hconj hs₁))
  set T' : Subgroup G := (PK : Subgroup ↥S.K1).map S.K1.subtype with hT'
  have hm' : ∀ x : G, x ∈ T' ↔ (m : G) * x * (m : G)⁻¹ ∈ T' := by
    intro x
    have hmem := Subgroup.mem_normalizer_iff.mp hmN
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨m * p * m⁻¹, (hmem p).1 hp, rfl⟩
    · rintro ⟨q, hq, hqx⟩
      have hq' : m⁻¹ * q * m⁻¹⁻¹ ∈ (PK : Subgroup ↥S.K1) :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hmN) q).1 hq
      refine ⟨m⁻¹ * q * m, ?_, ?_⟩
      · simp only [inv_inv] at hq'
        exact hq'
      · have : (q : G) = (m : G) * x * (m : G)⁻¹ := hqx
        show ((m : G)⁻¹ * q * m) = x
        rw [this]
        group
  set n' : G := g⁻¹ * (m : G) * g with hn'
  have hn'N : n' ∈ Subgroup.normalizer (S.Tg : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have e1 : x ∈ S.Tg ↔ g * x * g⁻¹ ∈ T' := by
      rw [hg]
      have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [this]
    have e2 : g * x * g⁻¹ ∈ T' ↔ (m : G) * (g * x * g⁻¹) * (m : G)⁻¹ ∈ T' := hm' _
    have e3 : (m : G) * (g * x * g⁻¹) * (m : G)⁻¹ ∈ T' ↔ n' * x * n'⁻¹ ∈ S.Tg := by
      rw [hg]
      have : g⁻¹ * ((m : G) * (g * x * g⁻¹) * (m : G)⁻¹) * g = n' * x * n'⁻¹ := by
        rw [hn']
        group
      rw [this]
    rw [e1, e2, e3]
  have hn'H : n' ∈ Hz z := S.normalizer_Tg_le_Hz h9 hn'N
  have hsqC : n' * n' ∈ S.Cg := S.sq_mem_Cg hn'N hn'H
  have hcomm : ∀ p ∈ (PK : Subgroup ↥S.K1),
      ((m : G) * m) * (p : G) = (p : G) * ((m : G) * m) := by
    intro p hp
    have hpT : (p : G) ∈ T' := ⟨p, hp, rfl⟩
    have ht : g⁻¹ * (p : G) * g ∈ S.Tg := (hg _).1 hpT
    have hc := (S.mem_Cg).1 hsqC _ ht
    have e : n' * n' = g⁻¹ * ((m : G) * m) * g := by
      rw [hn']
      group
    rw [e] at hc
    have h2 : g⁻¹ * ((p : G) * ((m : G) * m)) * g = g⁻¹ * (((m : G) * m) * (p : G)) * g := by
      calc g⁻¹ * ((p : G) * ((m : G) * m)) * g
          = (g⁻¹ * (p : G) * g) * (g⁻¹ * ((m : G) * m) * g) := by group
        _ = (g⁻¹ * ((m : G) * m) * g) * (g⁻¹ * (p : G) * g) := hc
        _ = g⁻¹ * (((m : G) * m) * (p : G)) * g := by group
    have h3 := mul_left_cancel (mul_right_cancel h2)
    exact h3.symm
  have hB : φ (m * m) ∈ Sbar := by
    apply hcent
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hs
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm p hp)
  exact hA hB

theorem card_Mg_eq_81 : Nat.card S.Mg = 81 := by
  rcases S.card_Mg_cases with h | h
  · exact absurd h S.card_Mg_ne_nine
  · exact h

end JWSetup

end CFSG.Quasithin.H13.U43

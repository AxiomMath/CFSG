module

public import CFSG.Sporadic.Fi24.Involutions
public import CFSG.Sporadic.FischerOddCore.Fi23Cent
public import CFSG.Sporadic.FischerOddCore.AlmostSimple

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.Sporadic.Fi24 (R J M MR JR tR D24 jR)

section Generic

variable {G : Type*} [Group G]

theorem oddCore_eq_bot_of_map_le [Finite G] {L K : Subgroup G}
    (hKL : K ≤ L) (hN : (CFSG.oddCore ↥L).map L.subtype ≤ K)
    (hK : CFSG.oddCore ↥K = ⊥) : CFSG.oddCore ↥L = ⊥ := by
  set N := (CFSG.oddCore ↥L).map L.subtype
  have hnormal : (N.subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨n', hn', hnn⟩ := hn
    refine ⟨⟨k, hKL k.2⟩ * n' * ⟨k, hKL k.2⟩⁻¹,
      (CFSG.oddCore_normal (G := L)).conj_mem n' hn' _, ?_⟩
    rw [map_mul, map_mul, map_inv, hnn]
    rfl
  have hodd : Odd (Nat.card (N.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv,
      Nat.card_congr ((CFSG.oddCore ↥L).equivMapOfInjective _ L.subtype_injective).toEquiv.symm]
    exact odd_card_oddCore
  have hle := le_oddCore_of_normal hnormal hodd
  rw [hK, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  have hbot : N = ⊥ := disjoint_self.1 (hle.mono_right hN)
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hbot

theorem mem_of_odd_of_mem_or_mul_mem {K : Subgroup G} {T n : G} (hT : T * T = 1)
    (hTK : T ∉ K) (hK : ∀ m ∈ K, m * T = T * m) (h : n ∈ K ∨ n * T ∈ K)
    (ho : Odd (orderOf n)) : n ∈ K := by
  rcases h with h | h
  · exact h
  · exfalso
    set m₁ := n * T with hm₁
    have hm₁T : Commute m₁ T := hK m₁ h
    have hn' : n = m₁ * T := by rw [hm₁, mul_assoc, hT, mul_one]
    obtain ⟨k, hk⟩ := ho
    have h1 : n ^ orderOf n = 1 := pow_orderOf_eq_one n
    rw [hk, hn', hm₁T.mul_pow, pow_succ T, pow_mul, sq, hT, one_pow, one_mul] at h1
    apply hTK
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ h _)

theorem oddCore_inf_centralizer_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : Even (Nat.card Q))
    (hinv : ∀ u : Q, orderOf u = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({u} : Set Q)) = ⊥)
    (K : Subgroup G) (φ : K ≃* Q) {m : G} (hm : m ∈ K) (hm2 : m * m = 1) :
    CFSG.oddCore ↥(K ⊓ Subgroup.centralizer {m}) = ⊥ := by
  have e1 := infCentralizerEquiv K hm
  have e2 := centralizerMulEquiv φ ⟨m, hm⟩
  refine oddCore_eq_bot_of_mulEquiv (e1.trans e2).symm ?_
  by_cases h1 : m = 1
  · subst h1
    have htop : Subgroup.centralizer ({φ ⟨1, hm⟩} : Set Q) = ⊤ := by
      rw [show (⟨1, hm⟩ : K) = 1 from rfl, map_one, eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul]
    rw [htop]
    exact oddCore_eq_bot_of_mulEquiv Subgroup.topEquiv.symm (oddCore_eq_bot_of_isSimpleGroup hQ)
  · apply hinv
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hm2) h1

theorem oddCore_centralizer_inf_of_involution [Finite G] {K : Subgroup G} {T : G}
    (hT : T * T = 1) (hTK : T ∉ K) (hK : ∀ m ∈ K, m * T = T * m)
    (hKT : ∀ c : G, c * T = T * c → c ∈ K ∨ c * T ∈ K)
    (hKm : ∀ m ∈ K, m * m = 1 → CFSG.oddCore ↥(K ⊓ Subgroup.centralizer {m}) = ⊥)
    {t : G} (ht : t * t = 1) (htT : t * T = T * t) :
    CFSG.oddCore ↥(Subgroup.centralizer {t} ⊓ Subgroup.centralizer {T}) = ⊥ := by
  obtain ⟨m, hm, hmt⟩ : ∃ m ∈ K, t = m ∨ t = m * T := by
    rcases hKT t htT with h | h
    · exact ⟨t, h, Or.inl rfl⟩
    · exact ⟨t * T, h, Or.inr (by rw [mul_assoc, hT, mul_one])⟩
  have hmT := hK m hm
  have hm2 : m * m = 1 := by
    rcases hmt with rfl | rfl
    · exact ht
    · have : m * T * (m * T) = m * m * (T * T) :=
        calc m * T * (m * T) = m * (T * m) * T := by group
          _ = m * (m * T) * T := by rw [← hmT]
          _ = m * m * (T * T) := by group
      rw [this, hT, mul_one] at ht
      exact ht
  have hsub : K ⊓ Subgroup.centralizer {m} ≤
      Subgroup.centralizer {t} ⊓ Subgroup.centralizer {T} := by
    intro k hk
    obtain ⟨hkK, hkm⟩ := Subgroup.mem_inf.1 hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hkm
    have hkT := hK k hkK
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 hkT⟩
    rcases hmt with rfl | rfl
    · exact hkm
    · calc k * (m * T) = k * m * T := by group
        _ = m * k * T := by rw [hkm]
        _ = m * (k * T) := by group
        _ = m * (T * k) := by rw [hkT]
        _ = m * T * k := by group
  refine oddCore_eq_bot_of_map_le hsub ?_ (hKm m hm hm2)
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨hnt, hnT⟩ := Subgroup.mem_inf.1 n.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hnt hnT
  have hodd : Odd (orderOf (n : G)) := by
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_mem_oddCore hn
  have hnK := mem_of_odd_of_mem_or_mul_mem hT hTK hK (hKT _ hnT) hodd
  refine Subgroup.mem_inf.2 ⟨hnK, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hnTc := hK _ hnK
  rcases hmt with rfl | rfl
  · exact hnt
  · have h' : (n : G) * m * T = m * (n : G) * T :=
      calc (n : G) * m * T = (n : G) * (m * T) := by group
        _ = m * T * n := hnt
        _ = m * (T * n) := by group
        _ = m * (n * T) := by rw [← hnTc]
        _ = m * n * T := by group
    exact mul_right_cancel h'

theorem oddCore_inf_centralizer_of_conj {c t x T : G} (hx : c * x * c⁻¹ = T)
    (h : CFSG.oddCore ↥(Subgroup.centralizer {c * t * c⁻¹} ⊓ Subgroup.centralizer {T}) = ⊥) :
    CFSG.oddCore ↥(Subgroup.centralizer {t} ⊓ Subgroup.centralizer {x}) = ⊥ := by
  rw [← hx] at h
  have h' := oddCore_inf_centralizer_conj c⁻¹ _ _ h
  rwa [show c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ = t by group,
    show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h'

end Generic

theorem mem_MR_of_odd
    {n : R} (hn : n * tR = tR * n) (ho : Odd (orderOf n)) : n ∈ MR :=
  @mem_of_odd_of_mem_or_mul_mem R inferInstance MR tR n Fi24.tR_mul_tR Fi24.tR_not_mem_MR
    (fun _ hm => Fi24.commute_tR_of_mem_MR hm)
    (Fi24.mem_MR_or_of_commute (Subgroup.mem_centralizer_singleton_iff.2 hn)) ho

theorem oddCore_MR_inf_centralizer
    {m : R} (hm : m ∈ MR) (hm2 : m * m = 1) :
    CFSG.oddCore ↥(MR ⊓ Subgroup.centralizer {m}) = ⊥ :=
  @oddCore_inf_centralizer_of_simple R inferInstance CFSG.Sporadic.Fi23.J inferInstance
    inferInstance CFSG.Sporadic.Fi23.isSimpleGroup_J
    (by rw [CFSG.Sporadic.Fi23.card_J]; decide) oddCore_centralizer_J MR Fi24.fi23EquivJMR m hm
    hm2

theorem oddCore_centralizer_inf_tR
    {t : R} (ht : t * t = 1) (htT : t * tR = tR * t) :
    CFSG.oddCore ↥(Subgroup.centralizer {t} ⊓ Subgroup.centralizer {tR}) = ⊥ :=
  @oddCore_centralizer_inf_of_involution R inferInstance inferInstance MR tR Fi24.tR_mul_tR
    Fi24.tR_not_mem_MR (fun _ hm => Fi24.commute_tR_of_mem_MR hm)
    (fun _ hc => Fi24.mem_MR_or_of_commute (Subgroup.mem_centralizer_singleton_iff.2 hc))
    (fun _ hm hm2 => oddCore_MR_inf_centralizer hm hm2) t ht htT

theorem CTUC_Fi24_involution_point_stabilizers_odd_core_trivial :
    ∀ t : R, orderOf t = 2 → ∀ x ∈ D24, t * x * t⁻¹ = x →
      CFSG.oddCore ↥(Subgroup.centralizer {t} ⊓ Subgroup.centralizer {x}) = ⊥ := by
  intro t ht x hx htx
  obtain ⟨g, hg⟩ := Fi24.exists_conj_eq_tR hx
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htx' : t * x = x * t := by
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [htx]
  have hc2 : jR g * t * (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) = 1 := by
    rw [show jR g * t * (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) = jR g * (t * t) * (jR g)⁻¹ by group,
      ht2, mul_one, mul_inv_cancel]
  have hcT : jR g * t * (jR g)⁻¹ * tR = tR * (jR g * t * (jR g)⁻¹) := by
    rw [← hg]
    calc jR g * t * (jR g)⁻¹ * (jR g * x * (jR g)⁻¹) = jR g * (t * x) * (jR g)⁻¹ := by group
      _ = jR g * (x * t) * (jR g)⁻¹ := by rw [htx']
      _ = jR g * x * (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) := by group
  exact @oddCore_inf_centralizer_of_conj R inferInstance (jR g) t x tR hg
    (oddCore_centralizer_inf_tR hc2 hcT)

end CFSG.Sporadic.FischerOddCore

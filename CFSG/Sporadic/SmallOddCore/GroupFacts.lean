module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFourGroup
public import CFSG.GroupTheory.LocalCores.PrimeSetCoreIsomorphism

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup

variable {M : Type*} [Group M]

@[expose] def conjClass (H : Subgroup M) (t : M) : Set M := {x | ∃ g ∈ H, x = g * t * g⁻¹}

theorem mem_conjClass {H : Subgroup M} {t x : M} : x ∈ conjClass H t ↔ ∃ g ∈ H, x = g * t * g⁻¹ :=
  Iff.rfl

theorem self_mem_conjClass (H : Subgroup M) (t : M) : t ∈ conjClass H t :=
  ⟨1, H.one_mem, by simp⟩

theorem ncard_conjClass_mul_card (H : Subgroup M) [Finite H] (t : M) :
    (conjClass H t).ncard * Nat.card ↥(H ⊓ centralizer ({t} : Set M)) = Nat.card H := by
  let _ : MulAction H M := MulAction.compHom M ((MulAut.conj : M →* MulAut M).comp H.subtype)
  have hsmul : ∀ (g : H) (x : M), g • x = (g : M) * x * (g : M)⁻¹ := fun _ _ => rfl
  have horbit : MulAction.orbit H t = conjClass H t := by
    ext x
    simp only [MulAction.mem_orbit_iff, hsmul, mem_conjClass]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hstab : MulAction.stabilizer H t = (centralizer ({t} : Set M)).subgroupOf H := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (g : M) * t = (g : M) * t * (g : M)⁻¹ * g := by group
        _ = t * g := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have h1 := (MulAction.stabilizer H t).card_mul_index
  rw [MulAction.index_stabilizer, horbit, hstab] at h1
  have h2 : Nat.card ((centralizer ({t} : Set M)).subgroupOf H) =
      Nat.card ↥(H ⊓ centralizer ({t} : Set M)) := by
    rw [← inf_subgroupOf_left (centralizer ({t} : Set M)) H]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h1, ← h2, mul_comm]

theorem inf_centralizer_conj (H : Subgroup M) {g : M} (hg : g ∈ H) (t : M) :
    H ⊓ centralizer ({g * t * g⁻¹} : Set M) =
      (H ⊓ centralizer ({t} : Set M)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨g⁻¹ * x * g, ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩, by group⟩
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxt]
      _ = t * (g⁻¹ * x * g) := by group
  · rintro ⟨y, ⟨hy, hyt⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg), ?_⟩
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hyt]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group

theorem oddCore_inf_centralizer_conj (H : Subgroup M) [Finite M] {g : M} (hg : g ∈ H) {t : M}
    (ht : CFSG.oddCore ↥(H ⊓ centralizer ({t} : Set M)) = ⊥) :
    CFSG.oddCore ↥(H ⊓ centralizer ({g * t * g⁻¹} : Set M)) = ⊥ := by
  rw [inf_centralizer_conj H hg t]
  let e : ↥(H ⊓ centralizer ({t} : Set M)) ≃* ↥((H ⊓ centralizer ({t} : Set M)).map
      (MulAut.conj g).toMonoidHom) :=
    (H ⊓ centralizer ({t} : Set M)).equivMapOfInjective _ (MulAut.conj g).injective
  rw [CFSG.oddCore_eq_piCore] at ht ⊢
  rw [← CFSG.LocalCores.prime_set_core_isomorphism e, ht, Subgroup.map_bot]

section IndexTwo

variable {P : Subgroup M} {u : M}

theorem mem_sup_zpowers_iff (hu : u ^ 2 = 1) (hn : ∀ p ∈ P, u * p * u⁻¹ ∈ P) {x : M} :
    x ∈ P ⊔ zpowers u ↔ x ∈ P ∨ x * u ∈ P := by
  have huu : u * u = 1 := by rw [← sq, hu]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  let K : Subgroup M :=
    { carrier := {x | x ∈ P ∨ x * u ∈ P}
      one_mem' := Or.inl P.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (P.mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact P.mul_mem hx hy)
        · right
          have h1 : u * y * u⁻¹ ∈ P := hn y hy
          have : x * y * u = (x * u) * (u * y * u⁻¹) := by
            rw [huinv, show x * u * (u * y * u) = x * (u * u) * y * u by group, huu, mul_one]
          rw [this]
          exact P.mul_mem hx h1
        · left
          have h1 : u * (y * u) * u⁻¹ ∈ P := hn _ hy
          have : x * y = (x * u) * (u * (y * u) * u⁻¹) := by
            rw [huinv]
            calc x * y = x * (u * u) * y * (u * u) := by rw [huu]; group
              _ = x * u * (u * (y * u) * u) := by group
          rw [this]
          exact P.mul_mem hx h1
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (P.inv_mem hx)
        · right
          have h1 := hn _ (P.inv_mem hx)
          have : x⁻¹ * u = u * (x * u)⁻¹ * u⁻¹ := by rw [huinv]; group
          rw [this]
          exact h1 }
  have hK : P ⊔ zpowers u = K := by
    apply le_antisymm
    · refine sup_le (fun x hx => Or.inl hx) ?_
      rw [zpowers_le]
      right
      rw [huu]
      exact P.one_mem
    · rintro x (hx | hx)
      · exact mem_sup_left hx
      · have : x = (x * u) * u := by rw [mul_assoc, huu, mul_one]
        rw [this]
        exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers u))
  rw [hK]
  rfl

theorem card_sup_zpowers [Finite M] (hu : u ^ 2 = 1) (hn : ∀ p ∈ P, u * p * u⁻¹ ∈ P)
    (huP : u ∉ P) : Nat.card ↥(P ⊔ zpowers u) = 2 * Nat.card P := by
  classical
  have : Fintype M := Fintype.ofFinite M
  have huu : u * u = 1 := by rw [← sq, hu]
  have hdisj : Disjoint (P : Set M) ((fun x => x * u) '' (P : Set M)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, rfl⟩
    have : u = y⁻¹ * (y * u) := by group
    exact huP (this ▸ P.mul_mem (P.inv_mem hy) hx)
  have hunion : ((P ⊔ zpowers u : Subgroup M) : Set M) =
      (P : Set M) ∪ (fun x => x * u) '' (P : Set M) := by
    ext x
    rw [SetLike.mem_coe, mem_sup_zpowers_iff hu hn, Set.mem_union, SetLike.mem_coe]
    refine or_congr Iff.rfl ⟨fun h => ⟨x * u, h, by
      show x * u * u = x
      rw [mul_assoc, huu, mul_one]⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    show y * u * u ∈ P
    rw [mul_assoc, huu, mul_one]
    exact hy
  have hinj : Set.InjOn (fun x => x * u) (P : Set M) := fun x _ y _ h => mul_right_cancel h
  have h1 : Nat.card ↥(P ⊔ zpowers u) = ((P ⊔ zpowers u : Subgroup M) : Set M).ncard :=
    Nat.card_coe_set_eq _
  have h2 : Nat.card ↥P = (P : Set M).ncard := Nat.card_coe_set_eq _
  rw [h1, hunion, Set.ncard_union_eq hdisj, hinj.ncard_image, h2]
  ring

end IndexTwo

theorem exists_conj_mem_of_card [Finite M] {R S : Subgroup M} (hSR : S ≤ R)
    (hS : Nat.card S = 2 ^ (Nat.card R).factorization 2) {t : M} (ht : t ∈ R)
    (ht2 : orderOf t = 2) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 R := Sylow.ofCard (S.subgroupOf R) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv)
  have htR2 : IsPGroup 2 (zpowers (⟨t, ht⟩ : R)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one]
  obtain ⟨T, hT⟩ := htR2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq R S' T
  refine ⟨x, x.2, ?_⟩
  have htT : (⟨t, ht⟩ : R) ∈ (T : Subgroup R) := hT (mem_zpowers _)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htT
  obtain ⟨s, hs, hst⟩ := htT
  have hsS : (s : M) ∈ S := by
    have : s ∈ S.subgroupOf R := by
      rwa [show ((S' : Subgroup R)) = S.subgroupOf R from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨t, ht⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem oddCore_eq_bot_of_witnesses (K : Subgroup M) [Finite K] (xs : List M)
    (hcover : ∀ y ∈ K, (orderOf y).Prime → orderOf y ≠ 2 → ∃ x ∈ xs, ∃ c ∈ K, y = c * x * c⁻¹)
    (hwit : ∀ x ∈ xs, ∀ N : Subgroup M, N ≤ K → (∀ c ∈ K, ∀ y ∈ N, c * y * c⁻¹ ∈ N) → x ∈ N →
      ∃ z ∈ N, 2 ∣ orderOf z) :
    CFSG.oddCore ↥K = ⊥ := by
  set N₀ := CFSG.oddCore ↥K
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.SmallLocal.odd_card_oddCore
  set N := N₀.map K.subtype
  have hNodd : Odd (Nat.card N) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hN₀odd
  have hNK : N ≤ K := map_subtype_le _
  have hNn : ∀ c ∈ K, ∀ y ∈ N, c * y * c⁻¹ ∈ N := by
    intro c hc y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    refine mem_map.mpr ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹,
      (CFSG.oddCore_normal (G := K)).conj_mem _ hy' _, ?_⟩
    simp
  by_contra hne
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card N₀) (by
    intro h1
    exact hne ((Subgroup.card_eq_one).mp h1))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N₀) q hqdvd
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hN₀odd) (even_iff_two_dvd.mpr hqdvd)
  have hyq : orderOf ((y : K) : M) = q := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  obtain ⟨x, hx, c, hc, hyc⟩ := hcover _ (y : K).2 (hyq ▸ hq) (hyq ▸ hq2)
  have hyN : ((y : K) : M) ∈ N := mem_map.mpr ⟨y, y.2, rfl⟩
  have hxN : x ∈ N := by
    have := hNn c⁻¹ (K.inv_mem hc) _ hyN
    rwa [hyc, show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
  obtain ⟨z, hz, hz2⟩ := hwit x hx N hNK hNn hxN
  have : orderOf (⟨z, hz⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at this
  exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr (hz2.trans this))

end CFSG.Sporadic.SmallOddCore


module

public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

def powCols (C : Array ℕ) (m : ℕ) : Array ℕ :=
  if m = 0 then idRows 11 else
    if m % 2 = 1 then comp11 C (powCols (comp11 C C) (m / 2)) else powCols (comp11 C C) (m / 2)
termination_by m
decreasing_by all_goals omega

def fixCount (C : Array ℕ) : ℕ := ((Finset.range 2048).filter fun a => app11 C a = a).card

section Generic

variable {G : Type*} [Group G]

theorem commute_iff_of_zpowers_eq {n k k' : G}
    (h : Subgroup.zpowers k = Subgroup.zpowers k') : Commute n k ↔ Commute n k' := by
  have hk : k ∈ Subgroup.zpowers k' := h ▸ Subgroup.mem_zpowers k
  have hk' : k' ∈ Subgroup.zpowers k := h.symm ▸ Subgroup.mem_zpowers k'
  obtain ⟨i, rfl⟩ := hk
  obtain ⟨j, hj⟩ := hk'
  constructor
  · intro hc
    rw [← hj]
    exact hc.zpow_right j
  · intro hc
    exact hc.zpow_right i

theorem exists_conj_zpowers_of_factorization [Finite G] {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hfac : (Nat.card K).factorization p = 1) {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K)
    (ok : orderOf k = p) (ok' : orderOf k' = p) :
    ∃ g ∈ K, Subgroup.zpowers k = Subgroup.zpowers (g * k' * g⁻¹) := by
  have okK : orderOf (⟨k, hk⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact ok
  have okK' : orderOf (⟨k', hk'⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact ok'
  let P : Sylow p K := Sylow.ofCard (Subgroup.zpowers ⟨k, hk⟩) (by
    rw [Nat.card_zpowers, okK, hfac, pow_one])
  let P' : Sylow p K := Sylow.ofCard (Subgroup.zpowers ⟨k', hk'⟩) (by
    rw [Nat.card_zpowers, okK', hfac, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P' P
  have hPP : Subgroup.zpowers (⟨k, hk⟩ : K) =
      (Subgroup.zpowers (⟨k', hk'⟩ : K)).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun Q : Sylow p K => (Q : Subgroup K)) hg
    simp only [Sylow.coe_subgroup_smul, P, P', Sylow.coe_ofCard] at this
    rw [← this]
    rfl
  refine ⟨g, g.2, ?_⟩
  have h1 := congrArg (Subgroup.map K.subtype) hPP
  rw [Subgroup.map_map, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h1
  exact h1

theorem card_centralizer_inf_eq [Finite G] {K N : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hfac : (Nat.card K).factorization p = 1) (hKN : ∀ g ∈ K, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) (ok : orderOf k = p) (ok' : orderOf k' = p) :
    Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup G) =
      Nat.card (Subgroup.centralizer {k'} ⊓ N : Subgroup G) := by
  obtain ⟨g, hgK, hzp⟩ := exists_conj_zpowers_of_factorization hfac hk hk' ok ok'
  have hgN : ∀ n ∈ N, g⁻¹ * n * g ∈ N := fun n hn => by
    have := hKN _ (K.inv_mem hgK) n hn
    rwa [inv_inv] at this
  have hgN' : ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun n hn => hKN g hgK n hn
  refine Nat.card_congr
    { toFun := fun n => ⟨g⁻¹ * n * g, Subgroup.mem_inf.2 ⟨?_, hgN _ (Subgroup.mem_inf.1 n.2).2⟩⟩
      invFun := fun n => ⟨g * n * g⁻¹, Subgroup.mem_inf.2 ⟨?_, hgN' _ (Subgroup.mem_inf.1 n.2).2⟩⟩
      left_inv := fun n => Subtype.ext (by dsimp only; group)
      right_inv := fun n => Subtype.ext (by dsimp only; group) }
  · have h1 : Commute (n : G) (g * k' * g⁻¹) := (commute_iff_of_zpowers_eq hzp).1
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 n.2).1)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * n * g * k' = g⁻¹ * (n * (g * k' * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * k' * g⁻¹) * n) * g := by rw [h1.eq]
      _ = k' * (g⁻¹ * n * g) := by group
  · have h1 : (n : G) * k' = k' * n :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 n.2).1
    have h2 : Commute (g * n * g⁻¹) (g * k' * g⁻¹) := by
      show g * n * g⁻¹ * (g * k' * g⁻¹) = g * k' * g⁻¹ * (g * n * g⁻¹)
      calc g * n * g⁻¹ * (g * k' * g⁻¹) = g * (n * k') * g⁻¹ := by group
        _ = g * (k' * n) * g⁻¹ := by rw [h1]
        _ = g * k' * g⁻¹ * (g * n * g⁻¹) := by group
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((commute_iff_of_zpowers_eq hzp).2 h2).eq

end Generic

theorem exists_conj_zpowers {p : ℕ} [Fact p.Prime] (hfac : (Nat.card K).factorization p = 1)
    {k k' : J} (hk : k ∈ K) (hk' : k' ∈ K) (ok : orderOf k = p) (ok' : orderOf k' = p) :
    ∃ g ∈ K, Subgroup.zpowers k = Subgroup.zpowers (g * k' * g⁻¹) := by
  have h := exists_conj_zpowers_of_factorization hfac hk hk' ok ok'
  exact h

end CFSG.Sporadic.J4Schreier

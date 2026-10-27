
module

public import CFSG.Sporadic.Schreier.J4SLocalNodesBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SCommGenInputs
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2.Native MulAction

section Generic

variable {G : Type*} [Group G]

theorem commutator_le_of_relIndex_eq_two {N L B : Subgroup G} (hB : B.relIndex N = 2)
    (hNL : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) (hinv : ∀ l ∈ L, ∀ b ∈ B, l * b * l⁻¹ ∈ B) :
    ⁅N, L⁆ ≤ B := by
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_eq_two_iff.1 hB
  have key : ∀ n ∈ N, n ∉ B → n * a ∈ B := fun n hn hnB => by
    rcases ((xor_iff_or_and_not_and _ _).1 (ha n hn)).1 with h | h
    · exact h
    · exact absurd h hnB
  rw [Subgroup.commutator_le]
  intro n hn l hl
  have hm : l * n * l⁻¹ ∈ N := hNL l hl n hn
  rw [commutatorElement_def, show n * l * n⁻¹ * l⁻¹ = n * (l * n * l⁻¹)⁻¹ by group]
  by_cases hnB : n ∈ B
  · exact B.mul_mem hnB (B.inv_mem (hinv l hl n hnB))
  · have hmB : l * n * l⁻¹ ∉ B := fun h => hnB (by
      have h1 := hinv l⁻¹ (L.inv_mem hl) _ h
      rwa [show l⁻¹ * (l * n * l⁻¹) * l⁻¹⁻¹ = n by group] at h1)
    rw [show n * (l * n * l⁻¹)⁻¹ = (n * a) * (l * n * l⁻¹ * a)⁻¹ by group]
    exact B.mul_mem (key n hn hnB) (B.inv_mem (key _ hm hmB))

theorem map_conj_eq_self {N : Subgroup G} {c : G} (h1 : ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, c⁻¹ * n * c ∈ N) : N.map (MulAut.conj c).toMonoidHom = N := by
  ext m
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h1 n hn
  · intro hm
    refine ⟨c⁻¹ * m * c, h2 m hm, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_inf_centralizer {K : Subgroup G} {c g : G} (hc : c ∈ K) :
    (K ⊓ Subgroup.centralizer {g}).map (MulAut.conj c).toMonoidHom =
      K ⊓ Subgroup.centralizer {c * g * c⁻¹} := by
  ext m
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hk
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨K.mul_mem (K.mul_mem hc hk.1) (K.inv_mem hc), ?_⟩
    calc c * k * c⁻¹ * (c * g * c⁻¹) = c * (k * g) * c⁻¹ := by group
      _ = c * (g * k) * c⁻¹ := by rw [hk.2]
      _ = c * g * c⁻¹ * (c * k * c⁻¹) := by group
  · rintro ⟨hm, hmc⟩
    refine ⟨c⁻¹ * m * c, Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem (K.inv_mem hc) hm) hc, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc c⁻¹ * m * c * g = c⁻¹ * (m * (c * g * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * g * c⁻¹) * m) * c := by rw [hmc]
        _ = g * (c⁻¹ * m * c) := by group
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem commutator_eq_of_map {N L M : Subgroup G} {c : G}
    (hN : N.map (MulAut.conj c).toMonoidHom = N) (hM : L.map (MulAut.conj c).toMonoidHom = M)
    (h : ⁅N, L⁆ = N) : ⁅N, M⁆ = N := by
  rw [← hM, ← hN, ← Subgroup.map_commutator, h]

end Generic

theorem conj_eq_of_mem_centralizer {k g : J} (h : k ∈ Subgroup.centralizer {g}) :
    k * g * k⁻¹ = g := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  rw [h, mul_inv_cancel_right]

theorem mem_centralizer_of_conj_eq {k g : J} (h : k * g * k⁻¹ = g) :
    k ∈ Subgroup.centralizer {g} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc k * g = k * g * k⁻¹ * k := by group
    _ = g * k := by rw [h]

theorem commPicks_lt : ∀ p ∈ commPicks, p.2 < 8 := by decide

end CFSG.Sporadic.J4Schreier

module

public import CFSG.Quasithin.Vol2.Ch10SecDGroup
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open

variable {G : Type} [Group G]

theorem commutator_subgroupOf_eq {L N : Subgroup G} (hLN : L ≤ N) (hperf : ⁅L, L⁆ = L) :
    ⁅L.subgroupOf N, L.subgroupOf N⁆ = L.subgroupOf N := by
  apply Subgroup.map_injective (Subgroup.subtype_injective N)
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLN, hperf]

theorem le_centralizer_of_perfect [Finite G] {L W : Subgroup G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hperf : ⁅L, L⁆ = L) (hW : Nat.card W ≤ 4) :
    L ≤ Subgroup.centralizer (W : Set G) := by
  set φ : Subgroup.normalizer (W : Set G) →* Equiv.Perm ↥W := (MulAut.toPerm ↥W).comp (conjAct W)
  set Q := (L.subgroupOf (Subgroup.normalizer (W : Set G))).map φ with hQ
  have hQperf : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← Subgroup.map_commutator, commutator_subgroupOf_eq hLW hperf]
  have hder : ∀ n, Q ≤ derivedSeries (Equiv.Perm ↥W) n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hQperf]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := (Group.isSolvable_def (G := Equiv.Perm ↥W)).mp (Equiv.Perm.isSolvable hW)
  have hQ1 : Q = ⊥ := le_bot_iff.mp (hn ▸ hder n)
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hlN := hLW hl
  have hφ : φ ⟨l, hlN⟩ = 1 := by
    have : φ ⟨l, hlN⟩ ∈ Q := ⟨⟨l, hlN⟩, by simpa [Subgroup.mem_subgroupOf] using hl, rfl⟩
    rwa [hQ1, Subgroup.mem_bot] at this
  have h1 : conjAct W ⟨l, hlN⟩ = 1 :=
    MulEquiv.ext fun x => congrArg (fun σ : Equiv.Perm ↥W => σ x) hφ
  have hC := (conjAct_eq_one_iff ⟨l, hlN⟩).mp h1
  exact ((Subgroup.mem_centralizer_iff.mp hC) w hw)

theorem commutator_le_left_of_le_normalizer {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
  rw [commutatorElement_def]
  simpa [mul_assoc] using V.mul_mem hv h

theorem conj_mem_commutator {V L : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {l : G} (hl : l ∈ L) {x : G} (hx : x ∈ ⁅V, L⁆) : l * x * l⁻¹ ∈ ⁅V, L⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, l', hl', rfl⟩ := hy
    refine Subgroup.subset_closure ⟨l * v * l⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hLV hl) v).mp hv,
      l * l' * l⁻¹, L.mul_mem (L.mul_mem hl hl') (L.inv_mem hl), ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul y z _ _ hy hz =>
    have := Subgroup.mul_mem _ hy hz
    simpa [mul_assoc] using this
  | inv y _ hy =>
    have := Subgroup.inv_mem _ hy
    simpa [mul_assoc] using this

theorem le_normalizer_commutator {V L : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_commutator hLV hl, fun hx => ?_⟩
  have := conj_mem_commutator hLV (L.inv_mem hl) hx
  simpa [mul_assoc] using this

theorem commutator_commutator_ne_bot {V L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hne : ⁅V, L⁆ ≠ ⊥) : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by
  intro h
  apply hne
  have h1 : ⁅⁅L, V⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L V]; exact h
  have h2 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h
  rw [hperf, Subgroup.commutator_comm] at h2
  exact h2

theorem three_le_mQuot_commutator [Finite G] {V L : Subgroup G} (hV : IsPGroup 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hperf : ⁅L, L⁆ = L) (hne : ⁅V, L⁆ ≠ ⊥) :
    3 ≤ E3.mQuot ⁅V, L⁆ ⊥ := by
  have hle := commutator_le_left_of_le_normalizer hLV
  have hW : IsPGroup 2 ↥(⁅V, L⁆ : Subgroup G) := hV.to_le hle
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hW
  have hmQ : E3.mQuot ⁅V, L⁆ ⊥ = m := by
    rw [E3.mQuot, Subgroup.relIndex_bot_left, hm, padicValNat.prime_pow]
  rw [hmQ]
  by_contra hlt
  have hcard : Nat.card ↥(⁅V, L⁆ : Subgroup G) ≤ 4 := by
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right two_pos (by omega)
      _ = 4 := by norm_num
  have hC := le_centralizer_of_perfect (le_normalizer_commutator hLV) hperf hcard
  apply commutator_commutator_ne_bot hperf hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mp hC

end CFSG.Quasithin.Vol2.Ch10.SecD

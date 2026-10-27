module

public import CFSG.Quasithin.MS93.S36SpBase
public import CFSG.Quasithin.MS93.S36SpRed

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36SP
open scoped commutatorElement

variable {G : Type} [Group G]

section Closure

theorem conj_mem {A M : Subgroup G} (h : M ≤ Subgroup.normalizer (A : Set G)) {m : G}
    (hm : m ∈ M) {a : G} (ha : a ∈ A) : m * a * m⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.1 (h hm) a).1 ha

theorem conj_inv_mem {A M : Subgroup G} (h : M ≤ Subgroup.normalizer (A : Set G)) {m : G}
    (hm : m ∈ M) {a : G} (ha : a ∈ A) : m⁻¹ * a * m ∈ A := by
  simpa using conj_mem h (M.inv_mem hm) ha

theorem le_normalizer_normalClosureIn (M Y : Subgroup G) :
    M ≤ Subgroup.normalizer (normalClosureIn M Y : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosureIn_le M Y)).1
    (normalClosureIn_normal M Y)

theorem normalClosureIn_le_of_le {M Y N : Subgroup G} (hNM : N ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hYN : Y ≤ N) : normalClosureIn M Y ≤ N :=
  normalClosureIn_le_of hNM ((Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hMN)
    (inf_le_left.trans hYN)

@[expose] def cenMod (M Q K : Subgroup G) (hMK : M ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup G where
  carrier := {x | x ∈ M ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ K}
  one_mem' := ⟨M.one_mem, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
    refine ⟨M.mul_mem hxM hyM, fun q hq => ?_⟩
    have e : ⁅x * y, q⁆ = (x * ⁅y, q⁆ * x⁻¹) * ⁅x, q⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact K.mul_mem (conj_mem hMK hxM (hy q hq)) (hx q hq)
  inv_mem' := by
    rintro x ⟨hxM, hx⟩
    refine ⟨M.inv_mem hxM, fun q hq => ?_⟩
    have e : ⁅x⁻¹, q⁆ = x⁻¹ * ⁅x, q⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_inv_mem hMK hxM (K.inv_mem (hx q hq))

theorem le_normalizer_cenMod {M Q K : Subgroup G} (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) :
    M ≤ Subgroup.normalizer (cenMod M Q K hMK : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ cenMod M Q K hMK, m * x * m⁻¹ ∈ cenMod M Q K hMK := by
    rintro m hm x ⟨hxM, hx⟩
    refine ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), fun q hq => ?_⟩
    have e : ⁅m * x * m⁻¹, q⁆ = m * ⁅x, m⁻¹ * q * m⁆ * m⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem hMK hm (hx _ (conj_inv_mem hMQ hm hq))
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun hx => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using this

theorem commutator_normalClosureIn_le {M Y Q K : Subgroup G} (hYM : Y ≤ M)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (h : ⁅Y, Q⁆ ≤ K) : ⁅normalClosureIn M Y, Q⁆ ≤ K := by
  have hle : normalClosureIn M Y ≤ cenMod M Q K hMK :=
    normalClosureIn_le_of_le (fun _ hx => hx.1) (le_normalizer_cenMod hMQ hMK)
      fun y hy => ⟨hYM hy, fun q hq => h (Subgroup.commutator_mem_commutator hy hq)⟩
  rw [Subgroup.commutator_le]
  intro x hx q hq
  exact (hle hx).2 q hq

theorem sq_mem_normalClosureIn {M Y K : Subgroup G} (hYM : Y ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) (hY2 : ∀ y ∈ Y, y ^ 2 = 1)
    (hRR : ⁅normalClosureIn M Y, normalClosureIn M Y⁆ ≤ K) :
    ∀ r ∈ normalClosureIn M Y, r ^ 2 ∈ K := by
  set R := normalClosureIn M Y with hR
  have hRn : M ≤ Subgroup.normalizer (R : Set G) := le_normalizer_normalClosureIn M Y
  let H : Subgroup G :=
    { carrier := {r | r ∈ R ∧ r ^ 2 ∈ K}
      one_mem' := ⟨R.one_mem, by simp⟩
      mul_mem' := by
        rintro r s ⟨hr, hr2⟩ ⟨hs, hs2⟩
        refine ⟨R.mul_mem hr hs, ?_⟩
        have e : (r * s) ^ 2 = r ^ 2 * ⁅r⁻¹, s⁆ * s ^ 2 := by
          simp only [commutatorElement_def, pow_two]
          group
        rw [e]
        exact K.mul_mem (K.mul_mem hr2
          (hRR (Subgroup.commutator_mem_commutator (R.inv_mem hr) hs))) hs2
      inv_mem' := by
        rintro r ⟨hr, hr2⟩
        refine ⟨R.inv_mem hr, ?_⟩
        rw [inv_pow]
        exact K.inv_mem hr2 }
  have hHn : M ≤ Subgroup.normalizer (H : Set G) := by
    have key : ∀ m ∈ M, ∀ r ∈ H, m * r * m⁻¹ ∈ H := by
      rintro m hm r ⟨hr, hr2⟩
      refine ⟨conj_mem hRn hm hr, ?_⟩
      have e : (m * r * m⁻¹) ^ 2 = m * r ^ 2 * m⁻¹ := by
        simp only [pow_two]
        group
      rw [e]
      exact conj_mem hMK hm hr2
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key m hm x, fun hx => ?_⟩
    have := key m⁻¹ (M.inv_mem hm) _ hx
    simpa [mul_assoc] using this
  have hRH : R ≤ H := normalClosureIn_le_of_le (fun _ hx => normalClosureIn_le M Y hx.1) hHn
    fun y hy => ⟨le_normalClosureIn hYM hy, by rw [hY2 y hy]; exact K.one_mem⟩
  exact fun r hr => (hRH hr).2

end Closure

section Faithful

variable [Finite G] {M T L : Subgroup G}

theorem le_pCoreOf_of_commutator_le (h : PUHyp M T L) {A B : Subgroup G}
    (hA : M ≤ Subgroup.normalizer (A : Set G)) (hB : M ≤ Subgroup.normalizer (B : Set G))
    (hAL : ¬ ⁅A, L⁆ ≤ B) {Y : Subgroup G} (hYT : Y ≤ T) (hAY : ⁅A, Y⁆ ≤ B) :
    Y ≤ pCoreOf 2 M := by
  by_contra hYQ
  exact hAL (comm_le_of_comm_le h hYT hYQ hA hB hAY)

end Faithful

end CFSG.Quasithin.MS93.S36E

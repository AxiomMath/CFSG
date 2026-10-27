module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.H23P4

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_mem_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G))
    {x : G} (hx : x ∈ ⁅A, B⁆) : g * x * g⁻¹ ∈ ⁅A, B⁆ := by
  have h : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    have h1 : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hA a).mp ha
    have h2 : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hB b).mp hb
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    show g * ⁅a, b⁆ * g⁻¹ ∈ ⁅A, B⁆
    rw [e]
    exact Subgroup.commutator_mem_commutator h1 h2
  exact h hx

theorem commutator_mem_of_normalizer {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) {l : G} (hl : l ∈ L) : ⁅l, y⁆ ∈ L := by
  have h : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hy l⁻¹).mp (inv_mem hl)
  have e : ⁅l, y⁆ = l * (y * l⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hl h

theorem commutator_mem_of_perfect {L N M : Subgroup G} {y : G}
    (hperf : ⁅L, L⁆ = L) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hM : ∀ g ∈ L, ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (hNM : ∀ n ∈ N, ∀ g ∈ L, ⁅n, g⁆ ∈ M)
    (hN : ∀ l ∈ L, ⁅l, y⁆ ∈ N) : ∀ l ∈ L, ⁅l, y⁆ ∈ M := by
  classical
  let M' : Subgroup L := M.subgroupOf L
  have hMn : M'.Normal := ⟨fun n hn g => by
    have h := hM g g.2 n (Subgroup.mem_subgroupOf.mp hn)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using h)⟩
  let π : L →* L ⧸ M' := QuotientGroup.mk' M'
  let c : L → L := fun g => ⟨⁅(g : G), y⁆, commutator_mem_of_normalizer hy g.2⟩
  have hc : ∀ g h : L, c (g * h) = g * c h * g⁻¹ * c g := by
    intro g h
    apply Subtype.ext
    simp only [c, Subgroup.coe_mul, InvMemClass.coe_inv, commutatorElement_def]
    group
  have hcomm : ∀ g h : L, Commute (π (c g)) (π h) := by
    intro g h
    have h1 : ((⁅c g, h⁆ : L) : G) ∈ M := by
      have := hNM (c g) (hN g g.2) h h.2
      simpa [commutatorElement_def] using this
    have h2 : π ⁅c g, h⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.mpr h1)
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  let δ : L →* L ⧸ M' := MonoidHom.mk' (fun g => π (c g)) (by
    intro g h
    calc π (c (g * h)) = π g * π (c h) * (π g)⁻¹ * π (c g) := by
          rw [hc]; simp only [map_mul, map_inv]
      _ = π (c h) * π (c g) := by rw [(hcomm h g).symm.eq, mul_inv_cancel_right]
      _ = π (c g) * π (c h) := (hcomm h (c g)).eq)
  have hker : commutator L ≤ δ.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm a (c b)).eq
  have hperfL : commutator L = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
  intro l hl
  have h1 : δ ⟨l, hl⟩ = 1 := by
    have : (⟨l, hl⟩ : L) ∈ δ.ker := hker (hperfL ▸ Subgroup.mem_top _)
    exact this
  have h2 : c ⟨l, hl⟩ ∈ M' := (QuotientGroup.eq_one_iff _).1 h1
  exact Subgroup.mem_subgroupOf.mp h2

theorem eq_one_of_conj_step {y l c : G} (hc : y * c * y⁻¹ = c) (h2 : c ^ 2 = 1) {m : ℕ}
    (hm : Odd m) (hy : y ^ m = 1) (h : y * l * y⁻¹ = c * l) : c = 1 := by
  have hcj : ∀ j : ℕ, y * c ^ j * y⁻¹ = c ^ j := fun j => by rw [← conj_pow, hc]
  have key : ∀ j : ℕ, y ^ j * l * (y ^ j)⁻¹ = c ^ j * l := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (j + 1) * l * (y ^ (j + 1))⁻¹ = y * (y ^ j * l * (y ^ j)⁻¹) * y⁻¹ := by group
        _ = (y * c ^ j * y⁻¹) * (y * l * y⁻¹) := by rw [ih]; group
        _ = c ^ (j + 1) * l := by rw [h, hcj, pow_succ, mul_assoc]
  have h1 := key m
  rw [hy] at h1
  simp only [one_mul, inv_one, mul_one] at h1
  have h3 : c ^ m = 1 := right_eq_mul.mp h1
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h3
  exact h3

end CFSG.Quasithin.H23P4

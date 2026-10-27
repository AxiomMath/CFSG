module

public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.LocalAnalysis.WeakClosure81.FiveSylow
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_of_isPGroup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V V₀ E Z Q : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀V : V₀ ≤ V) (hEV : E ≤ V)
    (hEV₀ : E ⊓ V₀ = ⊥) (hQ : IsPGroup p Q) (hQV : Q ≤ normalizer (V : Set G))
    (hQV₀ : Q ≤ normalizer (V₀ : Set G)) (hZQ : Z ≤ Q)
    (hZ : V ⊓ centralizer (Z : Set G) = E)
    (hQE : ∀ q ∈ Q, ∀ e ∈ E, q * e * q⁻¹ * e⁻¹ ∈ V₀) :
    V ⊓ centralizer (Q : Set G) = E := by
  have hle : V ⊓ centralizer (Q : Set G) ≤ E :=
    hZ ▸ inf_le_inf_left V (centralizer_le hZQ)
  refine le_antisymm hle fun e he => ?_
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVN : V ≤ normalizer (V₀ : Set G) := by
    intro v hv
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [hV.comm hv (hV₀V hw), mul_inv_cancel_right]
      exact hw
    · intro hw
      have := hV.comm hv (hV₀V hw)
      have hw' : w = v * w * v⁻¹ := by
        calc w = v⁻¹ * (v * w * v⁻¹) * v := by group
          _ = v⁻¹ * (v * (v * w * v⁻¹)) * v⁻¹ * v := by rw [this]; group
          _ = v * w * v⁻¹ := by group
      rw [hw']
      exact hw
  have hsolv : Group.IsSolvable V := isSolvable_of_comm fun a b => Subtype.ext (hV.comm a.2 b.2)
  have hcop := IsPGroup.coprime_card_of_ne p 2 hp2 Q V hQ hV.isPGroup
  obtain ⟨c, hc, n, hn, hcn⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_mem_inf_centralizer_mul_of_coprime hV₀V hVN hQV hQV₀
      hsolv hcop (hEV he) fun s hs => by
        have hse : s * e * s⁻¹ ∈ V := (mem_normalizer_iff.1 (hQV hs) e).1 (hEV he)
        rw [hV.comm (V.inv_mem (hEV he)) hse]
        exact hQE s hs e he
  have hcE : c ∈ E := hle hc
  have hnE : n ∈ E := by
    have : n = c⁻¹ * e := by rw [hcn]; group
    rw [this]; exact E.mul_mem (E.inv_mem hcE) he
  have hn1 : n = 1 := by
    have : n ∈ E ⊓ V₀ := ⟨hnE, hn⟩
    rwa [hEV₀, mem_bot] at this
  rw [hcn, hn1, mul_one]
  exact hc

theorem exists_inv_mul_mem_normalizer_of_isSylowIn {p : ℕ} [Fact p.Prime]
    {X Z C Q : Subgroup G} (hZC : Z ≤ normalizer (C : Set G))
    (hXZC : X ≤ normalizer ((Z ⊔ C : Subgroup G) : Set G)) (hZQ : Z ≤ Q)
    (hQ : IsSylowIn p Q (Z ⊔ C)) :
    ∀ x ∈ X, ∃ c ∈ C, c⁻¹ * x ∈ normalizer (Q : Set G) := by
  intro x hx
  obtain ⟨y, hy, m, -, hm, rfl⟩ :=
    frattini_isSylowIn le_normalizer normal_in_normalizer hQ x (hXZC hx)
  have hy' : y ∈ ((C ⊔ Z : Subgroup G) : Set G) := by rw [sup_comm]; exact hy
  rw [coe_mul_of_right_le_normalizer_left C Z hZC] at hy'
  obtain ⟨c, hc, z, hz, rfl⟩ := Set.mem_mul.1 hy'
  refine ⟨c, hc, ?_⟩
  have : c⁻¹ * (c * z * m) = z * m := by group
  rw [this]
  exact mul_mem (le_normalizer (hZQ hz)) hm

theorem isSylowIn_of_forall_inv_mul_mem {p : ℕ} [Fact p.Prime] {X C N S R : Subgroup G}
    (hCX : C ≤ X) (hXC : X ≤ normalizer (C : Set G)) (hNX : N ≤ X)
    (hX : ∀ x ∈ X, ∃ c ∈ C, c⁻¹ * x ∈ N) (hS : IsSylowIn p S C) (hSN : S ≤ N)
    (hR : IsSylowIn p R N) : IsSylowIn p R X := by
  refine ⟨hR.le.trans hNX, hR.isPGroup, fun hdvd => ?_⟩
  have hNC : N ≤ normalizer (C : Set G) := hNX.trans hXC
  have hXeq : X = N ⊔ C := by
    refine le_antisymm (fun x hx => ?_) (sup_le hNX hCX)
    obtain ⟨c, hc, hcx⟩ := hX x hx
    have : x = c * (c⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mem_sup_right hc) (mem_sup_left hcx)
  have h1 := relIndex_mul_relIndex (N ⊓ C) N X inf_le_left hNX
  have h2 := relIndex_mul_relIndex (N ⊓ C) C X inf_le_right hCX
  have h3 := CFSG.QuasithinUnique.C5.relIndex_inf_eq_of_le_normalizer hNC
  rw [← hXeq] at h3
  have hne : (N ⊓ C).relIndex N ≠ 0 := by
    haveI := isFiniteRelIndex_of_finiteIndex (H := N ⊓ C) (K := N)
    exact relIndex_ne_zero
  have h4 : N.relIndex X = (N ⊓ C).relIndex C := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
    rw [h1, ← h2, h3, mul_comm]
  have h5 := relIndex_mul_relIndex S (N ⊓ C) C (le_inf hSN hS.le) inf_le_right
  have h6 : ¬ p ∣ N.relIndex X := by
    rw [h4]
    intro hd
    exact hS.not_dvd_relIndex (h5 ▸ dvd_mul_of_dvd_right hd _)
  rw [← relIndex_mul_relIndex R N X hR.le hNX] at hdvd
  rcases (Nat.Prime.dvd_mul Fact.out).1 hdvd with h | h
  · exact hR.not_dvd_relIndex h
  · exact h6 h

theorem mem_normalizer_inf_centralizer_of_mem_normalizer {V Q : Subgroup G} {w : G}
    (hwV : w ∈ normalizer (V : Set G)) (hwQ : w ∈ normalizer (Q : Set G)) :
    w ∈ normalizer ((V ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have hQ : normalizer (Q : Set G) ≤ normalizer (centralizer (Q : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).1 inferInstance
  exact inf_normalizer_le_normalizer_inf ⟨hwV, hQ hwQ⟩

end CFSG.LocalAnalysis.WeakClosure81

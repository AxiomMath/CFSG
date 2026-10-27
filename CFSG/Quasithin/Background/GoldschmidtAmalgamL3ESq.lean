module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EF3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace Ctx

theorem le_zpowers_of_normal (c : Ctx A B z V) {N : Subgroup D} (hNV : N ≤ V)
    (hN : ∀ x ∈ B, ∀ n ∈ N, x * n * x⁻¹ ∈ N) : N ≤ Subgroup.zpowers z := by
  intro n hn
  by_contra hnz
  have hn1 : n ≠ 1 := fun h => hnz (h ▸ Subgroup.one_mem _)
  have hnz' : n ≠ z := fun h => hnz (h ▸ Subgroup.mem_zpowers z)
  obtain ⟨x, hxB, hx3⟩ := c.hyp.gold.vertex_right.exists_order_three
  have hxN := c.hyp.not_mem_normalizer_of_orderOf_three hxB hx3
  obtain ⟨a₀, -, -, -, -, hcases⟩ := c.exists_basis
  have hzz := c.z_sq
  have hV : ∀ v ∈ V, v = 1 ∨ v = z ∨ v = n ∨ v = z * n := by
    intro v hv
    rcases hcases n (hNV hn) with e | e | e | e
    · exact absurd e hn1
    · exact absurd e hnz'
    · rcases hcases v hv with e' | e' | e' | e'
      · exact Or.inl e'
      · exact Or.inr (Or.inl e')
      · exact Or.inr (Or.inr (Or.inl (e'.trans e.symm)))
      · exact Or.inr (Or.inr (Or.inr (by rw [e'] ; rw [e])))
    · rcases hcases v hv with e' | e' | e' | e'
      · exact Or.inl e'
      · exact Or.inr (Or.inl e')
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [e', e, ← mul_assoc, hzz, one_mul]
      · exact Or.inr (Or.inr (Or.inl (e'.trans e.symm)))
  have hzx : x * z * x⁻¹ = z := c.hyp.central x hxB
  have hle : conjSub x V ≤ V := by
    intro y hy
    rw [mem_conjSub] at hy
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    rcases hV _ hy with h | h | h | h <;> rw [h]
    · simp
    · rw [hzx]; exact c.z_mem_V
    · exact hNV (hN x hxB n hn)
    · have : x * (z * n) * x⁻¹ = z * (x * n * x⁻¹) := by
        calc x * (z * n) * x⁻¹ = (x * z * x⁻¹) * (x * n * x⁻¹) := by group
          _ = z * (x * n * x⁻¹) := by rw [hzx]
      rw [this]
      exact V.mul_mem c.z_mem_V (hNV (hN x hxB n hn))
  have heq : conjSub x V = V :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  exact hxN (mem_normalizer_of_conjSub_eq heq)

theorem centerQ_le_K (c : Ctx A B z V) {ζ : D} (hζ : ζ ∈ centerOf (pCoreOf 2 A)) :
    ζ ∈ Ksub A B :=
  (c.mem_K_iff).mpr ⟨hζ.1, fun u hu => Subgroup.mem_centralizer_iff.mp hζ.2 u (c.U_le_Q hu)⟩

omit [Finite D] in
theorem centerQ_conj (_c : Ctx A B z V) {x ζ : D} (hx : x ∈ A)
    (hζ : ζ ∈ centerOf (pCoreOf 2 A)) : x * ζ * x⁻¹ ∈ centerOf (pCoreOf 2 A) := by
  refine ⟨pCoreOf_conj_mem hx hζ.1, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
  have hp' : x⁻¹ * p * x⁻¹⁻¹ ∈ pCoreOf 2 A := pCoreOf_conj_mem (A.inv_mem hx) hp
  have h := Subgroup.mem_centralizer_iff.mp hζ.2 _ hp'
  calc p * (x * ζ * x⁻¹) = x * ((x⁻¹ * p * x⁻¹⁻¹) * ζ) * x⁻¹ := by group
    _ = x * (ζ * (x⁻¹ * p * x⁻¹⁻¹)) * x⁻¹ := by rw [h]
    _ = (x * ζ * x⁻¹) * p := by group

@[expose] def K2sub (A B : Subgroup D) : Subgroup D :=
  Subgroup.closure {x | ∃ k ∈ Ksub A B, x = k * k}

omit [Finite D] in
theorem K2_normal (c : Ctx A B z V) {x n : D} (hx : x ∈ B) (hn : n ∈ K2sub A B) :
    x * n * x⁻¹ ∈ K2sub A B := by
  unfold K2sub at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    exact Subgroup.subset_closure ⟨x * k * x⁻¹, c.K_normal hx hk, by group⟩
  | one => simp
  | mul y y' _ _ ih ih' =>
    have e : x * (y * y') * x⁻¹ = (x * y * x⁻¹) * (x * y' * x⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ ih ih'
  | inv y _ ih =>
    have e : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ ih

theorem K2_le_M (c : Ctx A B z V) : K2sub A B ≤ Msub A B V := by
  unfold K2sub
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact c.sq_Q_M (c.K_le_Q hk)

end Ctx

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

include g in
theorem U_inf_M_le_V {n : D} (hnU : n ∈ conjClosure V B) (hnM : n ∈ Msub A B V) : n ∈ V := by
  obtain ⟨v, hv, e | e⟩ := g.U_form hnU
  · rw [e]; exact hv
  · exfalso
    have hu₀M : g.u₀ ∈ Msub A B V := by
      have : g.u₀ = v⁻¹ * n := by rw [e]; group
      rw [this]
      exact (Msub A B V).mul_mem ((Msub A B V).inv_mem (c.V_le_M hv)) hnM
    have h := c.comm_W_M g.u₁_mem_W hu₀M
    rw [g.comm10] at h
    exact g.z₂_ne_one h

include g in
theorem sq_mem_zpowers {ζ : D} (hζ : ζ ∈ centerOf (pCoreOf 2 A)) (h : ζ * ζ ∈ V) :
    ζ * ζ ∈ Subgroup.zpowers z := by
  have hζK : ζ ∈ Ksub A B := c.centerQ_le_K hζ
  let N : Subgroup D := conjClosure V B ⊓ Ctx.K2sub A B
  have hNV : N ≤ V := fun n hn => g.U_inf_M_le_V hn.1 (c.K2_le_M hn.2)
  have hNn : ∀ x ∈ B, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn =>
    ⟨conjClosure_conj_mem hx hn.1, c.K2_normal hx hn.2⟩
  have hmem : ζ * ζ ∈ N := ⟨le_conjClosure V B h, Subgroup.subset_closure ⟨ζ, hζK, rfl⟩⟩
  exact c.le_zpowers_of_normal hNV hNn hmem

include g in
theorem sq_eq_one {ζ : D} (hζ : ζ ∈ centerOf (pCoreOf 2 A)) (h : ζ * ζ ∈ V) : ζ * ζ = 1 := by
  have h1 := g.sq_mem_zpowers hζ h
  have hζ' := c.centerQ_conj g.a_mem hζ
  have e : (g.a * ζ * g.a⁻¹) * (g.a * ζ * g.a⁻¹) = g.a * (ζ * ζ) * g.a⁻¹ := by group
  have h2 : (g.a * ζ * g.a⁻¹) * (g.a * ζ * g.a⁻¹) ∈ V := by
    rw [e]; exact c.V_normal g.a_mem h
  have h3 := g.sq_mem_zpowers hζ' h2
  rw [e] at h3
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  rcases zpow_eq_one_or_self c.hyp.natural.z_sq k with h4 | h4
  · rw [← hk]; exact h4
  · exfalso
    rw [← hk, h4] at h3
    obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp h3
    rcases zpow_eq_one_or_self c.hyp.natural.z_sq k' with h5 | h5
    · rw [h5] at hk'; exact g.z₁_ne_one hk'.symm
    · rw [h5] at hk'; exact g.z₁_ne_z hk'.symm

end Gen

end GoldAmL3E

end F6

end CFSG.Quasithin

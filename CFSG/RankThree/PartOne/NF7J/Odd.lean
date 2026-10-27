module

public import CFSG.RankThree.PartOne.NF7J.Model4

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS
open scoped commutatorElement

@[expose] def octSq : Fin 8 → M32 :=
  ![mk32 84, mk32 84, mk32 84 * mk32 167 * mk32 84, mk32 84 * mk32 167 * mk32 84,
    mk32 167 * mk32 84 * mk32 167, mk32 167 * mk32 84 * mk32 167, mk32 167, mk32 167]

theorem oct_sq : ∀ i : Fin 8, oct i * oct i = octSq i := by decide +kernel

@[expose] noncomputable def xoct (i : Fin 8) : GL (Fin 3) (ZMod 2) :=
  matUnit' (oct i) (oct_isOrd4 i).1

theorem xoct_val (i : Fin 8) : ((xoct i : GL (Fin 3) (ZMod 2)) : M32) = oct i :=
  matUnit'_val _ _

theorem xoct_ord4 (i : Fin 8) : IsOrd4 ((xoct i : GL (Fin 3) (ZMod 2)) : M32) := by
  rw [xoct_val]
  exact oct_isOrd4 i

theorem xoct_sq (i : Fin 8) : (((xoct i * xoct i : GL (Fin 3) (ZMod 2))) : M32) = octSq i := by
  rw [Units.val_mul, xoct_val, oct_sq]

theorem xoct_inv (i : Fin 8) : xoct (octInv i) = (xoct i)⁻¹ := by
  have h3 : xoct i ^ 3 = (xoct i)⁻¹ := by
    have h := (isOrd4_iff (xoct i)).1 (xoct_ord4 i)
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact h.1
  rw [← h3]
  apply Units.ext
  rw [xoct_val, Units.val_pow_eq_pow_val, xoct_val, oct_inv]

theorem mod4_cases : ∀ a b : Fin 8, (a : ℕ) % 4 = (b : ℕ) % 4 → a ≠ b → b = a + 4 := by decide

theorem ν_triple {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} (D : Datum p E)
    (a b : MulAut E) : D.ν * ((D.ν * a) * (D.ν * b) * (D.ν * a)) = a * b * a := by
  rw [D.νmul_νmul]
  have h := D.ν_comm (a * b)
  calc D.ν * (a * b * (D.ν * a)) = D.ν * (a * b * D.ν * a) := by simp only [mul_assoc]
    _ = D.ν * (D.ν * (a * b) * a) := by rw [h]
    _ = D.ν * (D.ν * (a * b * a)) := by simp only [mul_assoc]
    _ = a * b * a := D.ν_mul_ν_mul _

section Odd

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] {F : RFrame G p c L E f K} {D : Datum p E}
  (B : Base F D) (X : EFacts G p c E) (N : Norm F D)

theorem r₀_inv (F : RFrame G p c L E f K) : F.r₀⁻¹ = F.r₀ :=
  inv_eq_of_mul_eq_one_right (RFrame.r₀_sq F)

theorem r₁_inv (F : RFrame G p c L E f K) : F.r₁⁻¹ = F.r₁ :=
  inv_eq_of_mul_eq_one_right (RFrame.r₁_sq F)

include X N in
theorem pos_cls0 {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32))
    (hxx : ((x * x : GL (Fin 3) (ZMod 2)) : M32) = mk32 84) :
    ∃ j : Fin 8, (j : ℕ) % 4 = 0 ∧ iotaU B x = F.rg j := by
  have h5 := X.five_le
  have hn := iotaU_node B X N hx
  have e1 : x * x = D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ := Units.ext (by rw [hxx, N.h1])
  rw [e1, MulEquiv.symm_apply_apply] at hn
  have hn' : D.ν * ((⟨D.ν * F.r₀, a₁_mem F D⟩ : ↥D.H) : MulAut E) = F.r₀ := D.ν_mul_ν_mul _
  rw [hn', F.rootGp_r₀ h5] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with h | h
  · exact ⟨0, rfl, h⟩
  · exact ⟨4, rfl, h⟩

include X N in
theorem pos_cls3 {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32))
    (hxx : ((x * x : GL (Fin 3) (ZMod 2)) : M32) = mk32 167) :
    ∃ j : Fin 8, (j : ℕ) % 4 = 3 ∧ iotaU B x = F.rg j := by
  have h5 := X.five_le
  have hn := iotaU_node B X N hx
  have e1 : x * x = D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ := Units.ext (by rw [hxx, N.h2])
  rw [e1, MulEquiv.symm_apply_apply] at hn
  have hn' : D.ν * ((⟨D.ν * F.r₁, a₂_mem F D⟩ : ↥D.H) : MulAut E) = F.r₁ := D.ν_mul_ν_mul _
  rw [hn', F.rootGp_r₁ h5] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with h | h
  · exact ⟨7, rfl, h⟩
  · exact ⟨3, rfl, h⟩

include X N in
theorem pos_cls1 {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32))
    (hxx : ((x * x : GL (Fin 3) (ZMod 2)) : M32) = mk32 84 * mk32 167 * mk32 84) :
    ∃ j : Fin 8, (j : ℕ) % 4 = 1 ∧ iotaU B x = F.rg j := by
  have hp := X.prime
  have h5 := X.five_le
  have hn := iotaU_node B X N hx
  have e1 : x * x = D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ * D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ *
      D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ := Units.ext (by
    rw [hxx, Units.val_mul, Units.val_mul, N.h1, N.h2])
  have hsy : ((D.e.symm (D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ * D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ *
      D.e ⟨D.ν * F.r₀, a₁_mem F D⟩) : ↥D.H) : MulAut E) =
      (D.ν * F.r₀) * (D.ν * F.r₁) * (D.ν * F.r₀) := by
    simp only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
  rw [e1, hsy, ν_triple] at hn
  have hn2 : F.r₀ * F.r₁ * F.r₀ = F.r₀ * F.r₁ * F.r₀⁻¹ := by rw [r₀_inv]
  rw [hn2, F.rootGp_n₁ hp h5 X.comm] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with h | h
  · exact ⟨5, rfl, h⟩
  · exact ⟨1, rfl, h⟩

include X N in
theorem pos_cls2 {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32))
    (hxx : ((x * x : GL (Fin 3) (ZMod 2)) : M32) = mk32 167 * mk32 84 * mk32 167) :
    ∃ j : Fin 8, (j : ℕ) % 4 = 2 ∧ iotaU B x = F.rg j := by
  have hp := X.prime
  have h5 := X.five_le
  have hn := iotaU_node B X N hx
  have e1 : x * x = D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ * D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ *
      D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ := Units.ext (by
    rw [hxx, Units.val_mul, Units.val_mul, N.h1, N.h2])
  have hsy : ((D.e.symm (D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ * D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ *
      D.e ⟨D.ν * F.r₁, a₂_mem F D⟩) : ↥D.H) : MulAut E) =
      (D.ν * F.r₁) * (D.ν * F.r₀) * (D.ν * F.r₁) := by
    simp only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
  rw [e1, hsy, ν_triple] at hn
  have hn2 : F.r₁ * F.r₀ * F.r₁ = F.r₁ * F.r₀ * F.r₁⁻¹ := by rw [r₁_inv]
  rw [hn2, F.rootGp_n₂ hp h5 X.comm] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with h | h
  · exact ⟨2, rfl, h⟩
  · exact ⟨6, rfl, h⟩

include X N in
theorem pos_oct (i : Fin 8) : ∃ j : Fin 8, (j : ℕ) % 4 = octCls i ∧ iotaU B (xoct i) = F.rg j := by
  fin_cases i
  · exact pos_cls0 B X N (xoct_ord4 0) (xoct_sq 0)
  · exact pos_cls0 B X N (xoct_ord4 1) (xoct_sq 1)
  · exact pos_cls1 B X N (xoct_ord4 2) (xoct_sq 2)
  · exact pos_cls1 B X N (xoct_ord4 3) (xoct_sq 3)
  · exact pos_cls2 B X N (xoct_ord4 4) (xoct_sq 4)
  · exact pos_cls2 B X N (xoct_ord4 5) (xoct_sq 5)
  · exact pos_cls3 B X N (xoct_ord4 6) (xoct_sq 6)
  · exact pos_cls3 B X N (xoct_ord4 7) (xoct_sq 7)

@[expose] noncomputable def pidx (i : Fin 8) : Fin 8 := Classical.choose (pos_oct B X N i)

theorem pidx_spec (i : Fin 8) :
    ((pidx B X N i : Fin 8) : ℕ) % 4 = octCls i ∧ iotaU B (xoct i) = F.rg (pidx B X N i) :=
  Classical.choose_spec (pos_oct B X N i)

theorem Nrel_oct (i j : Fin 8) :
    Nrel B (oct i) (oct j) ↔ ¬ ∀ a ∈ iotaU B (xoct i), ∀ b ∈ iotaU B (xoct j), a * b = b * a := by
  rw [← xoct_val i, ← xoct_val j, Nrel_unit]

theorem Nrel_unit_oct (u : GL (Fin 3) (ZMod 2)) (i : Fin 8) :
    Nrel B (u : M32) (oct i) ↔ ¬ ∀ a ∈ iotaU B u, ∀ b ∈ iotaU B (xoct i), a * b = b * a := by
  rw [← xoct_val i, Nrel_unit]

theorem zeta_ne (F : RFrame G p c L E f K) (h5 : 5 ≤ p) :
    (F.ζ : K) ≠ 0 ∧ (F.ζ : K) ≠ 1 :=
  ⟨Units.ne_zero F.ζ, fun h => F.hζ.ne_one (by omega) (Units.ext h)⟩

include X N in
theorem octHyp (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2)
    (hy : ∃ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)), conjAut E y hy = D.ν) :
    OctHyp (Nrel B) (pidx B X N) := by
  obtain ⟨y, hy', hye⟩ := hy
  have h5 := X.five_le
  have hspec := fun i => pidx_spec B X N i
  refine ⟨fun i => (hspec i).1, ?_, ?_, ?_⟩
  · intro i
    have h1 : iotaU B (xoct (octInv i)) ≠ iotaU B (xoct i) := by
      rw [xoct_inv]
      exact iotaU_inv_ne B X N hdvd hodd (xoct_ord4 i) hy' hye
    rw [(hspec (octInv i)).2, (hspec i).2] at h1
    have h2 : pidx B X N (octInv i) ≠ pidx B X N i := fun h => h1 (by rw [h])
    have h3 : ((pidx B X N i : Fin 8) : ℕ) % 4 = ((pidx B X N (octInv i) : Fin 8) : ℕ) % 4 := by
      rw [(hspec i).1, (hspec (octInv i)).1, octCls_inv]
    exact mod4_cases _ _ h3 h2.symm
  · intro i j
    rw [Nrel_oct, (hspec i).2, (hspec j).2]
    constructor
    · intro h
      by_contra hnc
      exact h (fun a ha b hb => F.rg_comm hnc a ha b hb)
    · intro hnc H
      obtain ⟨a, ha, b, hb, hab⟩ := F.rg_ncomm hnc
      exact hab (H a ha b hb)
  · intro i j k hj hk h hh hNi hNj
    obtain ⟨u, rfl⟩ := exists_unit_of_det hh.1
    rw [Nrel_unit_oct, not_not, (hspec i).2] at hNi
    rw [Nrel_unit_oct, not_not, (hspec j).2, hj] at hNj
    rw [Nrel_unit_oct, not_not, (hspec k).2]
    obtain ⟨hz0, hz1⟩ := zeta_ne F h5
    obtain ⟨hA, hB'⟩ := F.rg_gen (pidx B X N i) hz0 hz1
    have hcomm : ⁅F.rg (pidx B X N i), F.rg (pidx B X N i + 3)⁆ ≤
        Subgroup.centralizer ((iotaU B u : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have c1 : Commute a g₁ := hNi a ha g₁ hg₁
      have c2 : Commute a g₂ := hNj a ha g₂ hg₂
      have c3 : Commute a (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) :=
        ((c1.mul_right c2).mul_right c1.inv_right).mul_right c2.inv_right
      rw [commutatorElement_def]
      exact c3.eq
    intro a ha b hb
    have hmem : b ∈ ⁅F.rg (pidx B X N i), F.rg (pidx B X N i + 3)⁆ := by
      rcases hk with hk | hk
      · rw [hk] at hb
        exact hA hb
      · rw [hk] at hb
        exact hB' hb
    have := hcomm hmem
    rw [Subgroup.mem_centralizer_iff] at this
    exact this a ha

theorem node_mem_reflectionSet (D : Datum p E) {u : GL (Fin 3) (ZMod 2)} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : D.ν * ((D.e.symm u : ↥D.H) : MulAut E) ∈ reflectionSet p E := by
  apply D.hD' _ (D.e.symm u).2
  · have h : D.e.symm u * D.e.symm u = 1 := by rw [← map_mul, hu2, map_one]
    simpa using congrArg Subtype.val h
  · intro h
    apply hu1
    have h' : D.e.symm u = 1 := Subtype.ext h
    have := congrArg D.e h'
    simpa using this

theorem ord3_aux (v : GL (Fin 3) (ZMod 2)) (hv : (v : M32) = mk32 84 * mk32 161) :
    orderOf v = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hv]
    decide +kernel
  · intro h
    have := congrArg (fun u : GL (Fin 3) (ZMod 2) => (u : M32)) h
    rw [hv] at this
    revert this
    decide +kernel

@[expose] def LinesComm (p : ℕ) (E : Subgroup G) (f : ℕ) : Prop :=
  ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, orderOf (s * t) = 3 →
    ∀ T ∈ RootGp p E f s, ∃ S ∈ RootGp p E f t, ∀ a ∈ T, ∀ b ∈ S, a * b = b * a

include X N in
theorem hF2_of_lines (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2)
    (hy : ∃ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)), conjAut E y hy = D.ν)
    (hlines : LinesComm p E f) :
    ¬ Nrel B (mk32 254) (mk32 239) ∨ ¬ Nrel B (mk32 254) (mk32 351) := by
  obtain ⟨y, hy', hye⟩ := hy
  have h239 : det3 (mk32 239) = 1 := by decide +kernel
  have h351 : det3 (mk32 351) = 1 := by decide +kernel
  have hx239v : ((matUnit' (mk32 239) h239 : GL (Fin 3) (ZMod 2)) : M32) = mk32 239 :=
    matUnit'_val _ _
  have hx351v : ((matUnit' (mk32 351) h351 : GL (Fin 3) (ZMod 2)) : M32) = mk32 351 :=
    matUnit'_val _ _
  generalize matUnit' (mk32 239) h239 = x239 at hx239v
  generalize matUnit' (mk32 351) h351 = x351 at hx351v
  have hinv : x351 = x239⁻¹ := by
    have h1 : x239 * x351 = 1 := Units.ext (by
      rw [Units.val_mul, hx239v, hx351v]
      decide +kernel)
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hord239 : IsOrd4 (x239 : M32) := by
    rw [hx239v]
    decide +kernel
  have hord254 := xoct_ord4 0
  have sq0 : ((xoct 0 * xoct 0 : GL (Fin 3) (ZMod 2)) : M32) = mk32 84 := xoct_sq 0
  have sq1 : ((x239 * x239 : GL (Fin 3) (ZMod 2)) : M32) = mk32 161 := by
    rw [Units.val_mul, hx239v]
    decide +kernel
  have u0sq : (xoct 0 * xoct 0) * (xoct 0 * xoct 0) = 1 := Units.ext (by
    rw [Units.val_mul, sq0]
    decide +kernel)
  have u0ne : xoct 0 * xoct 0 ≠ 1 := fun h => by
    have := congrArg (fun u : GL (Fin 3) (ZMod 2) => (u : M32)) h
    rw [sq0] at this
    revert this
    decide +kernel
  have u1sq : (x239 * x239) * (x239 * x239) = 1 := Units.ext (by
    rw [Units.val_mul, sq1]
    decide +kernel)
  have u1ne : x239 * x239 ≠ 1 := fun h => by
    have := congrArg (fun u : GL (Fin 3) (ZMod 2) => (u : M32)) h
    rw [sq1] at this
    revert this
    decide +kernel
  have hs := node_mem_reflectionSet D u0sq u0ne
  have ht := node_mem_reflectionSet D u1sq u1ne
  have hst : orderOf ((D.ν * ((D.e.symm (xoct 0 * xoct 0) : ↥D.H) : MulAut E)) *
      (D.ν * ((D.e.symm (x239 * x239) : ↥D.H) : MulAut E))) = 3 := by
    rw [D.νmul_νmul, ← Subgroup.coe_mul, ← map_mul, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    apply ord3_aux
    rw [Units.val_mul, sq0, sq1]
  have hT := iotaU_node B X N hord254
  obtain ⟨S, hS, hcomm⟩ := hlines _ hs _ ht hst _ hT
  have e254 : mk32 254 = ((xoct 0 : GL (Fin 3) (ZMod 2)) : M32) := (xoct_val 0).symm
  rcases iotaU_rootGp B X N hdvd hodd hord239 hy' hye S hS with h | h
  · left
    rw [e254, ← hx239v, Nrel_unit, not_not]
    rw [h] at hcomm
    exact hcomm
  · right
    rw [e254, ← hx351v, hinv, Nrel_unit, not_not]
    rw [h] at hcomm
    exact hcomm

include X N in
theorem odd_false (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) (hlines : LinesComm p E f) : False := by
  obtain ⟨B⟩ := exists_Base F D X
  have hy : ∃ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)), conjAut E y hy = D.ν :=
    exists_y (F := F)
  exact core_false (Nrel B)
    (fun g g' _ _ h => Nrel_symm B g g' h)
    (fun h g g' g₁ g₁' hh hg hg' e1 e2 => Nrel_conj B X N hdvd hodd hh hg hg' e1 e2)
    (fun g g' hg hg' => Nrel_inv B X N hdvd hodd hy hg hg')
    (pidx B X N) (octHyp B X N hdvd hodd hy) (hF2_of_lines B X N hdvd hodd hy hlines)

end Odd

end CFSG.RankThree.PartOne.NF7J

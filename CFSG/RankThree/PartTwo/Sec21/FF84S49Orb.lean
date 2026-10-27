module

public import CFSG.RankThree.PartTwo.Sec21.FF84S49Two
public import CFSG.RankThree.PartTwo.Sec21.FF84S49OrbGen
public import CFSG.RankThree.PartTwo.Sec21.FF84S49Coord
public import CFSG.RankThree.PartTwo.Sec21.FF84S49ASix

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

attribute [local instance] Classical.propDecidable



@[expose] noncomputable def NcompC (b b₁ b₂ x : G) : ℕ :=
  (if x ∈ Cen b then 0 else 1) + (if x ∈ Cen b₁ then 0 else 1) + (if x ∈ Cen b₂ then 0 else 1)

theorem conj_mem_cen_iff (g x z : G) : g * z * g⁻¹ ∈ Cen (g * x * g⁻¹) ↔ z ∈ Cen x := by
  rw [cen_conjBy, mem_conjBy_iff]
  have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
  rw [e]

theorem mem_cenS_of_subset {s : Set G} {x : G} (h : ∀ u ∈ s, x ∈ Cen u) :
    x ∈ CenS (Subgroup.closure s) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have : Subgroup.closure s ≤ Cen x := by
    refine (Subgroup.closure_le _).2 fun u hu => ?_
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 (h u hu)).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (this hw)

theorem op2_cen_of_reach {S : Subgroup G} {g x s : G} (hg : g ∈ Nor S) (hgx : g * x * g⁻¹ = s)
    (hs : Op 2 (Cen s) = S) : Op 2 (Cen x) = S := by
  have h1 : Op 2 (Cen s) = conjBy g (Op 2 (Cen x)) := by
    rw [← hgx, cen_conjBy, op2_conjBy]
  rw [hs] at h1
  have h2 : conjBy g S = S := mem_nor_iff_conjBy.1 hg
  apply conjBy_inj (y := g)
  rw [← h1, h2]

theorem mem_nor_of_cen {H : Subgroup G} {y : G} (hy : ∀ z ∈ H, z * y = y * z) : y ∈ Nor H := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : y * h * y⁻¹ = h := by
      have := hy h hh
      calc y * h * y⁻¹ = (y * h) * y⁻¹ := rfl
        _ = (h * y) * y⁻¹ := by rw [this]
        _ = h := by group
    rw [e]; exact hh
  · intro hh
    have h1 := hy _ hh
    have e1 : y * h * y⁻¹ * y = y * h := by group
    rw [e1] at h1
    have e : y * h * y⁻¹ = h := (mul_left_cancel h1).symm
    rw [e] at hh
    exact hh

theorem pat_disjoint {S : Subgroup G} {b b₁ b₂ : G} {e₀ e₁ e₂ f₀ f₁ f₂ : Prop}
    (h : ¬ (e₀ ↔ f₀) ∨ ¬ (e₁ ↔ f₁) ∨ ¬ (e₂ ↔ f₂)) :
    Disjoint (PatSet S b b₁ b₂ e₀ e₁ e₂) (PatSet S b b₁ b₂ f₀ f₁ f₂) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h0, h1, h2⟩ ⟨-, g0, g1, g2⟩
  rcases h with h | h | h
  · exact h (h0.symm.trans g0)
  · exact h (h1.symm.trans g1)
  · exact h (h2.symm.trans g2)

theorem pat_ne_one {S : Subgroup G} {b b₁ b₂ : G} {e₀ e₁ e₂ : Prop} {x : G}
    (hx : x ∈ PatSet S b b₁ b₂ e₀ e₁ e₂) (h : ¬ (e₀ ∧ e₁ ∧ e₂)) : x ≠ 1 := by
  rintro rfl
  obtain ⟨-, h0, h1, h2⟩ := hx
  apply h
  exact ⟨h0.1 (Subgroup.mem_centralizer_singleton_iff.2 (by simp)),
    h1.1 (Subgroup.mem_centralizer_singleton_iff.2 (by simp)),
    h2.1 (Subgroup.mem_centralizer_singleton_iff.2 (by simp))⟩

namespace S48Ctx

variable (c : S48Ctx b L B K b₁ b₂) {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2)

include c hU

theorem coordHyp : CoordHyp (Op 2 (Nor U)) b b₁ b₂ := by
  obtain ⟨hEA6, -⟩ := c.S48_elemab hU
  obtain ⟨hb2, hb1, hC⟩ := c.S48_b2 hU
  have hiso := c.S_iso hU
  have hBgen := c.sec.mono.2.1
  exact
  { ea := c.S_ea2 hU
    card := by rw [hEA6.2]; norm_num
    nor₀ := c.B_le_nor_S hU (mem_b c.sec)
    nor₁ := c.B_le_nor_S hU (mem_b₁ c.sec)
    nor₂ := c.B_le_nor_S hU (mem_b₂ c.sec)
    ord₀ := c.ord_b
    ord₁ := c.ord_b₁
    ord₂ := c.ord_b₂
    c₀₁ := c.hBcomm b (mem_b c.sec) b₁ (mem_b₁ c.sec)
    c₀₂ := c.hBcomm b (mem_b c.sec) b₂ (mem_b₂ c.sec)
    c₁₂ := c.hBcomm b₁ (mem_b₁ c.sec) b₂ (mem_b₂ c.sec)
    f₀ := by rw [c.S48_CSb hU]; exact c.piU_card hU
    f₁ := hb1
    f₂ := hb2
    fix := by rw [← hBgen]; exact hC
    k₀ := hiso.1
    k₁ := hiso.2.1
    k₂ := hiso.2.2.1
    join := hiso.2.2.2.1
    z₀ := hiso.2.2.2.2.1
    z₁ := hiso.2.2.2.2.2.1
    z₂ := hiso.2.2.2.2.2.2 }

theorem closure3_le_nor : Subgroup.closure ({b, b₁, b₂} : Set G) ≤ Nor (Op 2 (Nor U)) := by
  refine (Subgroup.closure_le _).2 ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact c.B_le_nor_S hU (mem_b c.sec)
  · exact c.B_le_nor_S hU (mem_b₁ c.sec)
  · exact c.B_le_nor_S hU (mem_b₂ c.sec)

theorem shift_mem {n : G} (hnS : n ∈ Nor (Op 2 (Nor U))) (h1 : n * b * n⁻¹ = b₁)
    (h2 : n * b₁ * n⁻¹ = b₂) (h3 : n * b₂ * n⁻¹ = b) {e₀ e₁ e₂ : Prop} {x : G}
    (hx : x ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ e₀ e₁ e₂) :
    n * x * n⁻¹ ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ e₂ e₀ e₁ := by
  obtain ⟨hxS, g0, g1, g2⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.1 hnS x).1 hxS, ?_, ?_, ?_⟩
  · rw [← h3, conj_mem_cen_iff]; exact g2
  · rw [← h1, conj_mem_cen_iff]; exact g0
  · rw [← h2, conj_mem_cen_iff]; exact g1

theorem reach_same (e₀ e₁ e₂ : Prop) {x y : G}
    (hx : x ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ e₀ e₁ e₂)
    (hy : y ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ e₀ e₁ e₂) :
    ∃ g ∈ Nor (Op 2 (Nor U)), g * x * g⁻¹ = y := by
  obtain ⟨-, htr⟩ := coord_orbits (c.coordHyp hU) e₀ e₁ e₂
  obtain ⟨β, hβ, hβy⟩ := htr x hx y hy
  exact ⟨β, c.closure3_le_nor hU hβ, hβy⟩

theorem reach_shift {n : G} (hnS : n ∈ Nor (Op 2 (Nor U))) (h1 : n * b * n⁻¹ = b₁)
    (h2 : n * b₁ * n⁻¹ = b₂) (h3 : n * b₂ * n⁻¹ = b) (e₀ e₁ e₂ : Prop) {x y : G}
    (hx : x ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ e₀ e₁ e₂)
    (hy : y ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ e₂ e₀ e₁) :
    ∃ g ∈ Nor (Op 2 (Nor U)), g * x * g⁻¹ = y := by
  obtain ⟨β, hβ, hβy⟩ := c.reach_same hU e₂ e₀ e₁ (c.shift_mem hU hnS h1 h2 h3 hx) hy
  refine ⟨β * n, mul_mem hβ hnS, ?_⟩
  rw [← hβy]
  group

theorem reach_shift2 {n : G} (hnS : n ∈ Nor (Op 2 (Nor U))) (h1 : n * b * n⁻¹ = b₁)
    (h2 : n * b₁ * n⁻¹ = b₂) (h3 : n * b₂ * n⁻¹ = b) (e₀ e₁ e₂ : Prop) {x y : G}
    (hx : x ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ e₀ e₁ e₂)
    (hy : y ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ e₁ e₂ e₀) :
    ∃ g ∈ Nor (Op 2 (Nor U)), g * x * g⁻¹ = y := by
  have hx2 := c.shift_mem hU hnS h1 h2 h3 (c.shift_mem hU hnS h1 h2 h3 hx)
  obtain ⟨β, hβ, hβy⟩ := c.reach_same hU e₁ e₂ e₀ hx2 hy
  refine ⟨β * (n * n), mul_mem hβ (mul_mem hnS hnS), ?_⟩
  rw [← hβy]
  group

theorem no_triple {w : G} (hwS : w ∈ Op 2 (Nor U)) (h0 : w ∈ Cen b) (h1 : w ∈ Cen b₁)
    (h2 : w ∈ Cen b₂) : w = 1 := by
  have hmem : w ∈ Op 2 (Nor U) ⊓ CenS (Subgroup.closure ({b, b₁, b₂} : Set G)) := by
    refine ⟨hwS, mem_cenS_of_subset ?_⟩
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  rw [(c.coordHyp hU).fix] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem cen_pair {w u v : G} (hw : w ∈ CenS (Subgroup.closure ({u, v} : Set G))) :
    w ∈ Cen u ∧ w ∈ Cen v := by
  have h := Subgroup.mem_centralizer_iff.1 hw
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (h u (Subgroup.subset_closure (by simp))).symm,
    Subgroup.mem_centralizer_singleton_iff.2 (h v (Subgroup.subset_closure (by simp))).symm⟩

theorem pat1₀ {x : G} (hx : x ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ False True True) :
    x ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ ∧ x ≠ 1 := by
  have hCH := c.coordHyp hU
  have hiso := c.S_iso hU
  set W := ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ with hW
  have hsub : (↑W : Set G) \ {1} ⊆ PatSet (Op 2 (Nor U)) b b₁ b₂ False True True := by
    rintro w ⟨hw, hw1⟩
    have hwS := c.comm_le_S hU (mem_b c.sec) hw
    obtain ⟨hc1, hc2⟩ := c.cen_pair hU (hiso.2.2.2.2.1 hw)
    refine ⟨hwS, ⟨fun hc0 => hw1 (c.no_triple hU hwS hc0 hc1 hc2), fun h => h.elim⟩,
      ⟨fun _ => trivial, fun _ => hc1⟩, ⟨fun _ => trivial, fun _ => hc2⟩⟩
  have hc : (PatSet (Op 2 (Nor U)) b b₁ b₂ False True True).ncard = 3 := by
    have := (coord_orbits hCH False True True).1
    simpa using this
  have hW3 : ((↑W : Set G) \ {1}).ncard = 3 := by
    rw [Set.ncard_diff_singleton_of_mem (one_mem W), ← Nat.card_coe_set_eq]
    have : Nat.card ↥(↑W : Set G) = 4 := hiso.1
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  have hxm : x ∈ (↑W : Set G) \ {1} := by rw [heq]; exact hx
  exact ⟨hxm.1, hxm.2⟩

theorem op2_pat1₀ (h180 : Nat.card ↥(L ⊓ Cen b₁) = 180) {x : G}
    (hx : x ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ False True True) : Op 2 (Cen x) = Op 2 (Nor U) := by
  obtain ⟨h1, h2⟩ := c.pat1₀ hU hx
  exact c.S49_one_comp₀ hU h180 h1 h2

theorem not_cen_le_nor_pat2₀ (hA : A8Model L) (hP : A_PiStar_stmt)
    (hT : A_transv_stmt) {x : G} (hx : x ∈ PatSet (Op 2 (Nor U)) b b₁ b₂ True False False) :
    ¬ Cen x ≤ Nor (Op 2 (Nor U)) := by
  have hiso := c.S_iso hU
  obtain ⟨hxS, g0, g1, g2⟩ := hx
  have hb : x ∈ Cen b := g0.2 trivial
  have hnb₁ : x ∉ Cen b₁ := fun h => g1.1 h
  have hnb₂ : x ∉ Cen b₂ := fun h => g2.1 h
  have hxU : x ∈ U := by
    rw [← c.S48_CSb hU]; exact ⟨hxS, hb⟩
  refine c.S49_two_comp hU hA hP hT hxU ?_ ?_ ?_
  · intro hm
    exact hnb₂ (c.cen_pair hU (hiso.2.2.2.2.2.1 hm)).2
  · intro hm
    exact hnb₁ (c.cen_pair hU (hiso.2.2.2.2.2.2 hm)).2
  · intro h1
    apply hnb₁
    rw [h1]
    exact Subgroup.mem_centralizer_singleton_iff.2 (by simp)

theorem ncomp_pat {S : Subgroup G} {e₀ e₁ e₂ : Prop} {x : G}
    (hx : x ∈ PatSet S b b₁ b₂ e₀ e₁ e₂) :
    NcompC b b₁ b₂ x = (if e₀ then 0 else 1) + (if e₁ then 0 else 1) + (if e₂ then 0 else 1) := by
  obtain ⟨-, g0, g1, g2⟩ := hx
  unfold NcompC
  rw [if_congr g0 rfl rfl, if_congr g1 rfl rfl, if_congr g2 rfl rfl]

theorem S49_S6 (hA : A8Model L) (hodd : A_cent_A5_odd_stmt) {s₀ : G}
    (hs : s₀ ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b⁆) (hs1 : s₀ ≠ 1) :
    ∃ H : Subgroup G, H ≤ Cen s₀ ∧ Nonempty (↥H ≃* Equiv.Perm (Fin 6)) ∧
      H ⊓ Op 2 (Nor U) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h180 := card_L_cen_b₁ hA c.post
  have hS : Op 2 (Cen s₀) = Op 2 (Nor U) := c.S49_one_comp₀ hU h180 hs hs1
  have hs₀S : s₀ ∈ Op 2 (Nor U) := c.comm_le_S hU (mem_b c.sec) hs
  have ord2 : orderOf s₀ = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using (c.S_ea2 hU).2 s₀ hs₀S) hs1
  have hxc : s₀ ∈ CenS (Subgroup.closure ({b₁, b₂} : Set G)) := (c.S_iso hU).2.2.2.2.1 hs
  obtain ⟨H, hHc, ⟨e⟩⟩ := P4_S6_cen hA hodd c.post ord2 hxc
  refine ⟨H, hHc, ⟨e⟩, ?_⟩
  have hCenN : Cen s₀ ≤ Nor (Op 2 (Nor U)) := by
    have := le_nor_op2 (Cen s₀)
    rwa [hS] at this
  have hHN : H ≤ Nor (H ⊓ Op 2 (Nor U)) := fun g hg =>
    nor_inf (Subgroup.le_normalizer hg) (hCenN (hHc hg))
  exact normal_two_of_S6 e inf_le_left hHN ((op2_isPGroup _).to_le inf_le_right)

theorem S49_orbits (hA : A8Model L) (hP : A_PiStar_stmt)
    (hT : A_transv_stmt) (hodd : A_cent_A5_odd_stmt) :
    ∃ Δ₁ Δ₂ : Set G, Δ₁ ∪ Δ₂ = (Op 2 (Nor U) : Set G) \ {1} ∧ Disjoint Δ₁ Δ₂ ∧
      Δ₁.ncard = 36 ∧ Δ₂.ncard = 27 ∧
      (∀ x ∈ Δ₁, ∀ y ∈ Δ₁, ∃ n ∈ Nor (Op 2 (Nor U)), n * x * n⁻¹ = y) ∧
      (∀ x ∈ Δ₂, ∀ y ∈ Δ₂, ∃ n ∈ Nor (Op 2 (Nor U)), n * x * n⁻¹ = y) ∧
      (∀ x ∈ Δ₁, ∀ n ∈ Nor (Op 2 (Nor U)), n * x * n⁻¹ ∈ Δ₁) ∧
      (∀ x ∈ Δ₁, Op 2 (Cen x) = Op 2 (Nor U)) ∧ (∀ x ∈ Δ₂, Op 2 (Cen x) ≠ Op 2 (Nor U)) ∧
      (∀ x ∈ Op 2 (Nor U), x ≠ 1 → (x ∈ Δ₁ ↔ NcompC b b₁ b₂ x % 2 = 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h180 := card_L_cen_b₁ hA c.post
  have hCH := c.coordHyp hU
  obtain ⟨n, hnH, hn1, hn2, hn3⟩ := c.cycle hU
  have hnS : n ∈ Nor (Op 2 (Nor U)) := hnH.1
  set Q3 := PatSet (Op 2 (Nor U)) b b₁ b₂ False False False with hQ3
  set A0 := PatSet (Op 2 (Nor U)) b b₁ b₂ False True True with hA0
  set A1 := PatSet (Op 2 (Nor U)) b b₁ b₂ True False True with hA1
  set A2 := PatSet (Op 2 (Nor U)) b b₁ b₂ True True False with hA2
  set D0 := PatSet (Op 2 (Nor U)) b b₁ b₂ True False False with hD0
  set D1 := PatSet (Op 2 (Nor U)) b b₁ b₂ False True False with hD1
  set D2 := PatSet (Op 2 (Nor U)) b b₁ b₂ False False True with hD2
  have cQ3 : Q3.ncard = 27 := by
    have := (coord_orbits hCH False False False).1; simpa using this
  have cA0 : A0.ncard = 3 := by
    have := (coord_orbits hCH False True True).1; simpa using this
  have cA1 : A1.ncard = 3 := by
    have := (coord_orbits hCH True False True).1; simpa using this
  have cA2 : A2.ncard = 3 := by
    have := (coord_orbits hCH True True False).1; simpa using this
  have cD0 : D0.ncard = 9 := by
    have := (coord_orbits hCH True False False).1; simpa using this
  have cD1 : D1.ncard = 9 := by
    have := (coord_orbits hCH False True False).1; simpa using this
  have cD2 : D2.ncard = 9 := by
    have := (coord_orbits hCH False False True).1; simpa using this
  have cO₁ : (A0 ∪ A1 ∪ A2).ncard = 9 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨pat_disjoint (by simp), pat_disjoint (by simp)⟩),
      Set.ncard_union_eq (pat_disjoint (by simp)), cA0, cA1, cA2]
  have cΔ₁ : (Q3 ∪ (A0 ∪ A1 ∪ A2)).ncard = 36 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_right.2 ⟨Set.disjoint_union_right.2
      ⟨pat_disjoint (by simp), pat_disjoint (by simp)⟩, pat_disjoint (by simp)⟩), cQ3, cO₁]
  have cΔ₂ : (D0 ∪ D1 ∪ D2).ncard = 27 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨pat_disjoint (by simp), pat_disjoint (by simp)⟩),
      Set.ncard_union_eq (pat_disjoint (by simp)), cD0, cD1, cD2]
  have hsplit : ∀ x ∈ Op 2 (Nor U), x ≠ 1 →
      x ∈ Q3 ∪ (A0 ∪ A1 ∪ A2) ∨ x ∈ D0 ∪ D1 ∪ D2 := by
    intro x hxS hx1
    by_cases hb : x ∈ Cen b <;> by_cases hb₁ : x ∈ Cen b₁ <;> by_cases hb₂ : x ∈ Cen b₂
    · exact absurd (c.no_triple hU hxS hb hb₁ hb₂) hx1
    · exact Or.inl (Or.inr (Or.inr ⟨hxS, iff_true_intro hb, iff_true_intro hb₁, iff_false_intro hb₂⟩))
    · exact Or.inl (Or.inr (Or.inl (Or.inr ⟨hxS, iff_true_intro hb, iff_false_intro hb₁,
        iff_true_intro hb₂⟩)))
    · exact Or.inr (Or.inl (Or.inl ⟨hxS, iff_true_intro hb, iff_false_intro hb₁, iff_false_intro hb₂⟩))
    · exact Or.inl (Or.inr (Or.inl (Or.inl ⟨hxS, iff_false_intro hb, iff_true_intro hb₁,
        iff_true_intro hb₂⟩)))
    · exact Or.inr (Or.inl (Or.inr ⟨hxS, iff_false_intro hb, iff_true_intro hb₁, iff_false_intro hb₂⟩))
    · exact Or.inr (Or.inr ⟨hxS, iff_false_intro hb, iff_false_intro hb₁, iff_true_intro hb₂⟩)
    · exact Or.inl (Or.inl ⟨hxS, iff_false_intro hb, iff_false_intro hb₁, iff_false_intro hb₂⟩)
  have hΔ₁S : ∀ x ∈ Q3 ∪ (A0 ∪ A1 ∪ A2), x ∈ Op 2 (Nor U) ∧ x ≠ 1 := by
    intro x hx
    rcases hx with hx | (hx | hx) | hx
    · exact ⟨hx.1, pat_ne_one hx (by simp)⟩
    · exact ⟨hx.1, pat_ne_one hx (by simp)⟩
    · exact ⟨hx.1, pat_ne_one hx (by simp)⟩
    · exact ⟨hx.1, pat_ne_one hx (by simp)⟩
  have hΔ₂S : ∀ x ∈ D0 ∪ D1 ∪ D2, x ∈ Op 2 (Nor U) ∧ x ≠ 1 := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact ⟨hx.1, pat_ne_one hx (by simp)⟩
    · exact ⟨hx.1, pat_ne_one hx (by simp)⟩
    · exact ⟨hx.1, pat_ne_one hx (by simp)⟩
  have hodd1 : ∀ x ∈ Q3 ∪ (A0 ∪ A1 ∪ A2), NcompC b b₁ b₂ x % 2 = 1 := by
    intro x hx
    rcases hx with hx | (hx | hx) | hx
    · rw [c.ncomp_pat hU hx]; simp
    · rw [c.ncomp_pat hU hx]; simp
    · rw [c.ncomp_pat hU hx]; simp
    · rw [c.ncomp_pat hU hx]; simp
  have heven2 : ∀ x ∈ D0 ∪ D1 ∪ D2, NcompC b b₁ b₂ x % 2 = 0 := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · rw [c.ncomp_pat hU hx]; simp
    · rw [c.ncomp_pat hU hx]; simp
    · rw [c.ncomp_pat hU hx]; simp
  obtain ⟨s₀, hs₀A⟩ : A0.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [cA0]; norm_num)
  obtain ⟨x₀, hx₀D⟩ : D0.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [cD0]; norm_num)
  have hs₀ : Op 2 (Cen s₀) = Op 2 (Nor U) := c.op2_pat1₀ hU h180 hs₀A
  have hx₀ : ¬ Cen x₀ ≤ Nor (Op 2 (Nor U)) := c.not_cen_le_nor_pat2₀ hU hA hP hT hx₀D
  have reachD : ∀ x ∈ D0 ∪ D1 ∪ D2, ∃ g ∈ Nor (Op 2 (Nor U)), g * x * g⁻¹ = x₀ := by
    rintro x ((hx | hx) | hx)
    · exact c.reach_same hU True False False hx hx₀D
    · exact c.reach_shift2 hU hnS hn1 hn2 hn3 False True False hx hx₀D
    · exact c.reach_shift hU hnS hn1 hn2 hn3 False False True hx hx₀D
  have hΔ₂cen : ∀ x ∈ D0 ∪ D1 ∪ D2, ¬ Cen x ≤ Nor (Op 2 (Nor U)) := by
    intro x hx hle
    obtain ⟨g, hg, hgx⟩ := reachD x hx
    have := cen_le_nor_conj hg x
    rw [hgx] at this
    exact hx₀ (this.2 hle)
  have reachA : ∀ x ∈ A0 ∪ A1 ∪ A2, ∃ g ∈ Nor (Op 2 (Nor U)), g * x * g⁻¹ = s₀ := by
    rintro x ((hx | hx) | hx)
    · exact c.reach_same hU False True True hx hs₀A
    · exact c.reach_shift2 hU hnS hn1 hn2 hn3 True False True hx hs₀A
    · exact c.reach_shift hU hnS hn1 hn2 hn3 True True False hx hs₀A
  have hOpA : ∀ x ∈ A0 ∪ A1 ∪ A2, Op 2 (Cen x) = Op 2 (Nor U) := by
    intro x hx
    obtain ⟨g, hg, hgx⟩ := reachA x hx
    exact op2_cen_of_reach hg hgx hs₀
  have hCenA : ∀ x ∈ A0 ∪ A1 ∪ A2, Cen x ≤ Nor (Op 2 (Nor U)) := by
    intro x hx
    have := le_nor_op2 (Cen x)
    rwa [hOpA x hx] at this
  have hs₀' := c.pat1₀ hU hs₀A
  have hs₀S : s₀ ∈ Op 2 (Nor U) := hs₀A.1
  have ord2 : orderOf s₀ = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using (c.S_ea2 hU).2 s₀ hs₀S) hs₀'.2
  have hxc : s₀ ∈ CenS (Subgroup.closure ({b₁, b₂} : Set G)) := by
    refine mem_cenS_of_subset ?_
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hs₀A.2.2.1.2 trivial
    · exact hs₀A.2.2.2.2 trivial
  obtain ⟨H, hHc, ⟨e⟩⟩ := P4_S6_cen hA hodd c.post ord2 hxc
  have hCenN : Cen s₀ ≤ Nor (Op 2 (Nor U)) := by
    have := le_nor_op2 (Cen s₀)
    rwa [hs₀] at this
  have h5 : 5 ∣ Nat.card ↥H := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hy : orderOf (y₀ : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hy₀
  have hyn : (y₀ : G) ∈ Nor (Op 2 (Nor U)) := hCenN (hHc y₀.2)
  have hnc : ¬ Op 2 (Nor U) ≤ Cen (y₀ : G) := by
    intro hSc
    have hyU : (y₀ : G) ∈ Nor U :=
      mem_nor_of_cen fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hSc (c.U_le_S hU hh))
    have hyC : (y₀ : G) ∈ CenS (Op 2 (Nor U)) :=
      Subgroup.mem_centralizer_iff.2 fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hSc hh)
    have hyS : (y₀ : G) ∈ Op 2 (Nor U) := c.S48_charTwo hU ⟨hyU, hyC⟩
    have h2 : (y₀ : G) ^ 2 = 1 := by simpa [pow_two] using (c.S_ea2 hU).2 _ hyS
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy] at this
    omega
  obtain ⟨u, huA, hu⟩ := order5_move (c.S48_elemab hU).1 hy hyn hnc
    (X := A0 ∪ A1 ∪ A2) (fun x hx => (hΔ₁S x (Or.inr hx)).1) cO₁
    (fun h1 => (hΔ₁S 1 (Or.inr h1)).2 rfl)
  have huS : u ∈ Op 2 (Nor U) := (hΔ₁S u (Or.inr huA)).1
  have hu1 : u ≠ 1 := (hΔ₁S u (Or.inr huA)).2
  set y : G := (y₀ : G) with hydef
  have hwS : y * u * y⁻¹ ∈ Op 2 (Nor U) := (Subgroup.mem_normalizer_iff.1 hyn u).1 huS
  have hw1 : y * u * y⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have : u = y⁻¹ * (y * u * y⁻¹) * y := by group
    rw [this, h]; group
  have hwQ : y * u * y⁻¹ ∈ Q3 := by
    rcases hsplit _ hwS hw1 with (hw | hw) | hw
    · exact hw
    · exact absurd hw hu
    · exfalso
      refine hΔ₂cen _ hw ?_
      exact (cen_le_nor_conj hyn u).2 (hCenA u huA)
  have reachΔ₁ : ∀ x ∈ Q3 ∪ (A0 ∪ A1 ∪ A2), ∃ g ∈ Nor (Op 2 (Nor U)), g * x * g⁻¹ = s₀ := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨β, hβ, hβx⟩ := c.reach_same hU False False False hx hwQ
      obtain ⟨gu, hgu, hguu⟩ := reachA u huA
      refine ⟨gu * y⁻¹ * β, mul_mem (mul_mem hgu (inv_mem hyn)) hβ, ?_⟩
      calc (gu * y⁻¹ * β) * x * (gu * y⁻¹ * β)⁻¹
          = gu * y⁻¹ * (β * x * β⁻¹) * (gu * y⁻¹)⁻¹ := by group
        _ = gu * y⁻¹ * (y * u * y⁻¹) * (gu * y⁻¹)⁻¹ := by rw [hβx]
        _ = gu * u * gu⁻¹ := by group
        _ = s₀ := hguu
    · exact reachA x hx
  have hOpΔ₁ : ∀ x ∈ Q3 ∪ (A0 ∪ A1 ∪ A2), Op 2 (Cen x) = Op 2 (Nor U) := by
    intro x hx
    obtain ⟨g, hg, hgx⟩ := reachΔ₁ x hx
    exact op2_cen_of_reach hg hgx hs₀
  have hCenΔ₁ : ∀ x ∈ Q3 ∪ (A0 ∪ A1 ∪ A2), Cen x ≤ Nor (Op 2 (Nor U)) := by
    intro x hx
    have := le_nor_op2 (Cen x)
    rwa [hOpΔ₁ x hx] at this
  refine ⟨Q3 ∪ (A0 ∪ A1 ∪ A2), D0 ∪ D1 ∪ D2, ?_, ?_, cΔ₁, cΔ₂, ?_, ?_, ?_, hOpΔ₁, ?_, ?_⟩
  · ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨(hΔ₁S x hx).1, fun h => (hΔ₁S x hx).2 h⟩
      · exact ⟨(hΔ₂S x hx).1, fun h => (hΔ₂S x hx).2 h⟩
    · rintro ⟨hxS, hx1⟩
      exact hsplit x hxS hx1
  · rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 := hodd1 x hx1
    have h2 := heven2 x hx2
    omega
  · intro x hx y hy
    obtain ⟨g, hg, hgx⟩ := reachΔ₁ x hx
    obtain ⟨g', hg', hgy⟩ := reachΔ₁ y hy
    refine ⟨g'⁻¹ * g, mul_mem (inv_mem hg') hg, ?_⟩
    calc g'⁻¹ * g * x * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * x * g⁻¹) * g' := by group
      _ = g'⁻¹ * (g' * y * g'⁻¹) * g' := by rw [hgx, hgy]
      _ = y := by group
  · intro x hx y hy
    obtain ⟨g, hg, hgx⟩ := reachD x hx
    obtain ⟨g', hg', hgy⟩ := reachD y hy
    refine ⟨g'⁻¹ * g, mul_mem (inv_mem hg') hg, ?_⟩
    calc g'⁻¹ * g * x * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * x * g⁻¹) * g' := by group
      _ = g'⁻¹ * (g' * y * g'⁻¹) * g' := by rw [hgx, hgy]
      _ = y := by group
  · intro x hx m hm
    have hxS := hΔ₁S x hx
    have hwS : m * x * m⁻¹ ∈ Op 2 (Nor U) := (Subgroup.mem_normalizer_iff.1 hm x).1 hxS.1
    have hw1 : m * x * m⁻¹ ≠ 1 := by
      intro h
      apply hxS.2
      have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [this, h]; group
    rcases hsplit _ hwS hw1 with hw | hw
    · exact hw
    · exfalso
      exact hΔ₂cen _ hw ((cen_le_nor_conj hm x).2 (hCenΔ₁ x hx))
  · intro x hx h
    refine hΔ₂cen x hx ?_
    have := le_nor_op2 (Cen x)
    rwa [h] at this
  · intro x hxS hx1
    constructor
    · intro hx
      exact hodd1 x hx
    · intro hodd'
      rcases hsplit x hxS hx1 with hs | hs
      · exact hs
      · have := heven2 x hs
        omega

end S48Ctx

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

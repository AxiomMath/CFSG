module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiSeven

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv CFSG.Open CFSG.ClassicalInvolution.Solomon73

@[expose] def sgn2 (σ : Perm (Fin 6)) : ZMod 2 := if Perm.sign σ = 1 then 0 else 1

theorem sgn2_mul (σ τ : Perm (Fin 6)) : sgn2 (σ * τ) = sgn2 σ + sgn2 τ := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  unfold sgn2
  rw [Perm.sign_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;>
    rcases Int.units_eq_one_or (Perm.sign τ) with h' | h' <;> simp [h, h', hne] <;> decide

theorem sgn2_one : sgn2 1 = 0 := by simp [sgn2]

set_option maxRecDepth 100000 in
theorem sgn2_swapsOf : ∀ d : Fin 3 → ZMod 2, sgn2 (swapsOf d) = d 0 + d 1 + d 2 := by
  decide +kernel

@[expose] def twistW (a : Wr 6) : Wr 6 := ⟨a.vec + fun _ => sgn2 a.perm, a.perm⟩

theorem twistW_mul (a b : Wr 6) : twistW (a * b) = twistW a * twistW b := by
  obtain ⟨u, σ⟩ := a
  obtain ⟨v, τ⟩ := b
  refine Wr.ext (funext fun i => ?_) rfl
  show u i + v (σ.symm i) + sgn2 (σ * τ) = u i + sgn2 σ + (v (σ.symm i) + sgn2 τ)
  rw [sgn2_mul]
  ring

theorem twistW_twistW (a : Wr 6) : twistW (twistW a) = a := by
  obtain ⟨u, σ⟩ := a
  refine Wr.ext (funext fun i => ?_) rfl
  show u i + sgn2 σ + sgn2 σ = u i
  rw [add_assoc, zmod2_add_self, add_zero]

theorem wsum_twistW (a : Wr 6) : wsum (twistW a) = wsum a := by
  obtain ⟨u, σ⟩ := a
  show ∑ i, (u i + sgn2 σ) = ∑ i, u i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h6 : ((6 : ℕ) : ZMod 2) = 0 := by decide
  rw [h6, zero_mul, add_zero]

theorem twistW_mem_Wsub {a : Wr 6} (ha : a ∈ Wsub) : twistW a ∈ Wsub := by
  show wsum (twistW a) = 0
  rw [wsum_twistW]
  exact ha

@[expose] def twistWsub : ↥Wsub ≃* ↥Wsub where
  toFun a := ⟨twistW a, twistW_mem_Wsub a.2⟩
  invFun a := ⟨twistW a, twistW_mem_Wsub a.2⟩
  left_inv a := Subtype.ext (twistW_twistW a)
  right_inv a := Subtype.ext (twistW_twistW a)
  map_mul' a b := Subtype.ext (twistW_mul a b)

theorem twistW_allOnes : twistW (Wr.allOnes 6) = Wr.allOnes 6 := by
  refine Wr.ext (funext fun i => ?_) rfl
  show (1 : ZMod 2) + sgn2 1 = 1
  rw [sgn2_one, add_zero]

@[expose] def twC (x : SC) : SC := (x.1 + fun _ => x.2 0 + x.2 1 + x.2 2, x.2)

theorem twistW_cSp (x : SC) : twistW (cSp x) = cSp (twC x) := by
  refine Wr.ext (funext fun i => ?_) rfl
  show x.1 (blk i) + sgn2 (swapsOf x.2) = x.1 (blk i) + (x.2 0 + x.2 1 + x.2 2)
  rw [sgn2_swapsOf]

theorem twC_twC : ∀ x : SC, twC (twC x) = x := by decide

theorem twistW_wPi3 : twistW wPi3 = wPi3 := by
  refine Wr.ext (funext fun i => ?_) rfl
  show wPi3.vec i + sgn2 1 = wPi3.vec i
  rw [sgn2_one, add_zero]

theorem twistW_wPi12 : twistW wPi12 = wPi12 := by
  refine Wr.ext (funext fun i => ?_) rfl
  show wPi12.vec i + sgn2 1 = wPi12.vec i
  rw [sgn2_one, add_zero]

theorem twistW_mem_SW_iff (a : Wr 6) : twistW a ∈ SW ↔ a ∈ SW := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := mem_SW_iff.mp h
    rw [← twistW_twistW a, hx, twistW_cSp]
    exact cSp_mem_SW _
  · intro h
    obtain ⟨x, rfl⟩ := mem_SW_iff.mp h
    rw [twistW_cSp]
    exact cSp_mem_SW _

theorem twistW_mem_DW_iff (a : Wr 6) : twistW a ∈ DW ↔ a ∈ DW := by
  rw [mem_DW, mem_DW, wsum_twistW]
  rfl

theorem image_twC : (scOrb 0 ∪ scOrb 2).image twC = scOrb 0 ∪ scOrb 6 := by decide

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

@[expose] noncomputable def twist : YData z where
  ϑ := Y.ϑ.trans twistWsub
  ϑ_z := by
    show twistW (Y.ϑ ⟨z, mem_centralizer_self' z⟩ : Wr 6) = Wr.allOnes 6
    rw [Y.ϑ_z, twistW_allOnes]

theorem twist_ϑ (x : ↥(Subgroup.centralizer ({z} : Set G))) :
    (Y.twist.ϑ x : Wr 6) = twistW (Y.ϑ x) := rfl

theorem twist_ι (a : ↥Wsub) : Y.twist.ι a = Y.ι (twistWsub a) := rfl

theorem twist_mem_lift {X : Subgroup (Wr 6)} (hX : ∀ a, twistW a ∈ X ↔ a ∈ X) (x : G) :
    x ∈ Y.twist.lift X ↔ x ∈ Y.lift X := by
  rw [Y.twist.mem_lift, Y.mem_lift]
  refine exists_congr fun hx => ?_
  rw [twist_ϑ]
  exact hX _

theorem twist_A : Y.twist.A = Y.A := by
  ext x
  exact Y.twist_mem_lift twistW_mem_SW_iff x

theorem twist_T : Y.twist.T = Y.T := by
  ext x
  exact Y.twist_mem_lift twistW_mem_DW_iff x

theorem twist_σA (c : SC) : Y.twist.σA c = Y.σA (twC c) := by
  rw [σA, twist_ι, σA]
  congr 1
  exact Subtype.ext (twistW_cSp c)

theorem twist_π3 : Y.twist.π3 = Y.π3 := by
  rw [π3, twist_ι, π3]
  congr 1
  exact Subtype.ext twistW_wPi3

theorem twist_π12 : Y.twist.π12 = Y.π12 := by
  rw [π12, twist_ι, π12]
  congr 1
  exact Subtype.ext twistW_wPi12

theorem twist_coord (X : Set G) : Y.twist.coord X = (Y.coord X).image twC := by
  ext c
  rw [Y.twist.mem_coord, twist_σA, Finset.mem_image]
  constructor
  · intro h
    exact ⟨twC c, Y.mem_coord.mpr h, twC_twC c⟩
  · rintro ⟨c', hc', rfl⟩
    rw [twC_twC]
    exact Y.mem_coord.mp hc'

theorem exists_std (hchar : IsCharTwoType G) (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T)
    (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3) (h12 : ¬ IsConj z Y.π12)
    (h312 : ¬ IsConj Y.π3 Y.π12) (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    (hiso : ∃ a ∈ Y.A, a ≠ z ∧ IsConj z a) :
    ∃ Y' : YData z, Y'.A = Y.A ∧ Y'.T = Y.T ∧ Y'.π3 = Y.π3 ∧ Y'.π12 = Y.π12 ∧
      Y'.coord (conjSet Y'.NA z) = scOrb 0 ∪ scOrb 6 := by
  rcases Y.coord_conj_z hchar P hP hz h3 h12 h312 hE hiso with h | h
  · refine ⟨Y.twist, Y.twist_A, Y.twist_T, Y.twist_π3, Y.twist_π12, ?_⟩
    rw [twist_coord, show Y.twist.NA = Y.NA by rw [NA, NA, twist_A], h, image_twC]
  · exact ⟨Y, rfl, rfl, rfl, rfl, h⟩

end YData

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

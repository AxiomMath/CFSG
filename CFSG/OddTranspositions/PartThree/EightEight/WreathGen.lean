module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.Ten.SetupQ
import CFSG.GroupTheory.SmallSymmetric

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki Equiv SemidirectProduct
open scoped commutatorElement

theorem swp_eq_inl_mul_inr {f m : ℕ} (a : PSL2Model f) (i j : Fin m) :
    WreathEndgame.swp a i j =
      (SemidirectProduct.inl (Pi.mulSingle i a * Pi.mulSingle j a⁻¹) : L2Wreath f m) *
        SemidirectProduct.inr (swap i j) := by
  refine SemidirectProduct.ext ?_ ?_
  · funext p
    simp [WreathEndgame.swp]
  · simp [WreathEndgame.swp]

theorem inl_mulSingle_mul_inv_eq_swp_mul_swp_one_inv {f m : ℕ}
    (a : PSL2Model f) (i j : Fin m) :
    (SemidirectProduct.inl (Pi.mulSingle i a * Pi.mulSingle j a⁻¹) : L2Wreath f m) =
      WreathEndgame.swp a i j * (WreathEndgame.swp (1 : PSL2Model f) i j)⁻¹ := by
  rw [swp_eq_inl_mul_inr, WreathEndgame.swp_one_eq_inr]
  simp

theorem mulSingle_mul_inv_mul_eq_inl_commutator {f m : ℕ} (c d : PSL2Model f)
    (i j : Fin m) (hij : i ≠ j) :
    (SemidirectProduct.inl (Pi.mulSingle i c * Pi.mulSingle j c⁻¹) : L2Wreath f m) *
        (SemidirectProduct.inl (Pi.mulSingle i d * Pi.mulSingle j d⁻¹) : L2Wreath f m) *
        ((SemidirectProduct.inl (Pi.mulSingle i (c * d) * Pi.mulSingle j (c * d)⁻¹) :
          L2Wreath f m))⁻¹ =
      SemidirectProduct.inl (Pi.mulSingle j ⁅c⁻¹, d⁻¹⁆) := by
  rw [← map_mul, ← map_inv, ← map_mul]
  congr 1
  funext p
  by_cases hp : p = i
  · subst hp
    simp [Pi.mulSingle_eq_of_ne hij]
  · by_cases hpj : p = j
    · subst hpj
      simp [Pi.mulSingle_eq_of_ne hij.symm, commutatorElement_def]
      group
    · simp [Pi.mulSingle_eq_of_ne hp, Pi.mulSingle_eq_of_ne hpj]

theorem range_inl_le_of_forall_mulSingle_mem {f n : ℕ} {S : Subgroup (L2Wreath f n)}
    (h : ∀ (p : Fin n) (a : PSL2Model f),
      (SemidirectProduct.inl (Pi.mulSingle p a) : L2Wreath f n) ∈ S) :
    (SemidirectProduct.inl.range : Subgroup (L2Wreath f n)) ≤ S := by
  rintro x ⟨y, rfl⟩
  exact Subgroup.mem_comap.mp
    (Subgroup.pi_mem_of_mulSingle_mem (H := S.comap SemidirectProduct.inl) y fun p => h p (y p))

theorem inl_mulSingle_mem_closure_sameSwaps {f m : ℕ} (hf : 2 ≤ f) {i j : Fin m} (hij : i ≠ j)
    (a : CFSG.Theory.Comparator.PSL2Model f) :
    SemidirectProduct.inl (Pi.mulSingle i a) ∈
      Subgroup.closure (WreathEndgame.sameSwaps f m (swap i j)) := by
  let S := Subgroup.closure (WreathEndgame.sameSwaps f m (swap i j))
  let u : PSL2Model f → L2Wreath f m :=
    fun c => SemidirectProduct.inl (Pi.mulSingle i c * Pi.mulSingle j c⁻¹)
  have hswp : ∀ c, WreathEndgame.swp c i j ∈ S := fun c =>
    Subgroup.subset_closure ⟨WreathEndgame.swp_mem hij, rfl⟩
  have hu : ∀ c, u c ∈ S := by
    intro c
    change (SemidirectProduct.inl (Pi.mulSingle i c * Pi.mulSingle j c⁻¹) :
      L2Wreath f m) ∈ S
    rw [inl_mulSingle_mul_inv_eq_swp_mul_swp_one_inv]
    exact Subgroup.mul_mem _ (hswp c) (Subgroup.inv_mem _ (hswp 1))
  let K : Subgroup (PSL2Model f) :=
    S.comap ((SemidirectProduct.inl : (Fin m → PSL2Model f) →* L2Wreath f m).comp
      (MonoidHom.mulSingle (fun _ : Fin m => PSL2Model f) j))
  have hK : commutator (PSL2Model f) ≤ K := by
    change ⁅(⊤ : Subgroup (PSL2Model f)), (⊤ : Subgroup (PSL2Model f))⁆ ≤ K
    rw [Subgroup.commutator_le]
    intro g1 _ g2 _
    have h := mulSingle_mul_inv_mul_eq_inl_commutator g1⁻¹ g2⁻¹ i j hij
    have hmem : u g1⁻¹ * u g2⁻¹ * (u (g1⁻¹ * g2⁻¹))⁻¹ ∈ S :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hu _) (hu _)) (Subgroup.inv_mem _ (hu _))
    rw [h] at hmem
    change (SemidirectProduct.inl (Pi.mulSingle j ⁅g1, g2⁆) : L2Wreath f m) ∈ S
    simpa only [inv_inv] using hmem
  have hperf : commutator (PSL2Model f) = ⊤ :=
    (Group.isPerfect_def (G := PSL2Model f)).mp (SetupQ.isPerfect_psl2Model hf)
  have hKtop : K = ⊤ := top_le_iff.mp (hperf ▸ hK)
  have hcoord : ∀ c, (SemidirectProduct.inl (Pi.mulSingle j c) : L2Wreath f m) ∈ S := by
    intro c
    have hc : c ∈ K := by rw [hKtop]; trivial
    simpa [K] using hc
  have hcancel : u a * (SemidirectProduct.inl (Pi.mulSingle j a) : L2Wreath f m) =
      SemidirectProduct.inl (Pi.mulSingle i a) := by
    rw [← map_mul]
    congr 1
    funext p
    by_cases hp : p = i
    · subst hp
      simp [Pi.mulSingle_eq_of_ne hij]
    · by_cases hpj : p = j
      · subst hpj
        simp [Pi.mulSingle_eq_of_ne hij.symm]
      · simp [Pi.mulSingle_eq_of_ne hp, Pi.mulSingle_eq_of_ne hpj]
  have hmem : u a * (SemidirectProduct.inl (Pi.mulSingle j a) : L2Wreath f m) ∈ S :=
    Subgroup.mul_mem _ (hu a) (hcoord a)
  rwa [hcancel] at hmem

theorem inl_mulSingle_mem_closure_four {f : ℕ} (hf : 2 ≤ f) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (p : Fin 4) (a : PSL2Model f) :
    (SemidirectProduct.inl (Pi.mulSingle p a) : L2Wreath f 4) ∈
      Subgroup.closure (WreathEndgame.sameSwaps f 4 (swap i j) ∪
        WreathEndgame.sameSwaps f 4 (swap k l)) := by
  have hcard : ({i, j, k, l} : Finset (Fin 4)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [hij, hik, hil, hjk, hjl, hkl]
  have huniv : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hcard)
  have hp : p = i ∨ p = j ∨ p = k ∨ p = l := by
    have h := huniv ▸ Finset.mem_univ p
    simpa [Finset.mem_insert, Finset.mem_singleton] using h
  have hS12 : Subgroup.closure (WreathEndgame.sameSwaps f 4 (swap i j)) ≤
      Subgroup.closure (WreathEndgame.sameSwaps f 4 (swap i j) ∪
        WreathEndgame.sameSwaps f 4 (swap k l)) :=
    Subgroup.closure_mono Set.subset_union_left
  have hS34 : Subgroup.closure (WreathEndgame.sameSwaps f 4 (swap k l)) ≤
      Subgroup.closure (WreathEndgame.sameSwaps f 4 (swap i j) ∪
        WreathEndgame.sameSwaps f 4 (swap k l)) :=
    Subgroup.closure_mono Set.subset_union_right
  rcases hp with rfl | rfl | rfl | rfl
  · exact hS12 (inl_mulSingle_mem_closure_sameSwaps (m := 4) hf hij a)
  · refine hS12 ?_
    have h := inl_mulSingle_mem_closure_sameSwaps (m := 4) hf hij.symm a
    simpa [swap_comm] using h
  · exact hS34 (inl_mulSingle_mem_closure_sameSwaps (m := 4) hf hkl a)
  · refine hS34 ?_
    have h := inl_mulSingle_mem_closure_sameSwaps (m := 4) hf hkl.symm a
    simpa [swap_comm] using h

theorem range_inl_le_closure_sameSwaps_union {f : ℕ} (hf : 2 ≤ f) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (SemidirectProduct.inl.range : Subgroup (L2Wreath f 4)) ≤
      Subgroup.closure (WreathEndgame.sameSwaps f 4 (swap i j) ∪
        WreathEndgame.sameSwaps f 4 (swap k l)) :=
  range_inl_le_of_forall_mulSingle_mem
    (fun p a => inl_mulSingle_mem_closure_four hf hij hik hil hjk hjl hkl p a)

end CFSG.OddTranspositions.PartThree.EightEight

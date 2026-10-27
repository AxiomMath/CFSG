module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectN2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise
open CFSG.Quasithin.H13.Direct523Semi CFSG.Quasithin.H13.Direct523Count
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL)

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

theorem unipSL_mulVec {F : Type} [Field F] (b : F) (w : Fin 2 → F) :
    (unipSL b : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec w = uB b w := by
  funext i
  fin_cases i <;> simp [unipSL, uB_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem coord_z_eq (s : Setup521 G T M L V H B D D₃ Z₁ n) {N : Subgroup G} {m : ℕ}
    (D : NatL2Data L N m) (hroot : D.SylowAdapted (T ⊓ L))
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) {z : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) (hzN : z ∈ N) :
    ∃ a₀ : D.K, a₀ ≠ 0 ∧ coordN D z hzN = a₀ • Direct523Semi.e₁ := by
  unfold NatL2Data.SylowAdapted at hroot
  obtain ⟨-, h2⟩ := hroot
  obtain ⟨g, hgL, hgS, hg⟩ := h2 1
  have hgT : g ∈ T := (inf_le_left : T ⊓ L ≤ T) hgS
  have hgN : g ∈ Subgroup.normalizer (N : Set G) := hTN hgT
  have hgz : g * z = z * g :=
    (Subgroup.mem_centralizer_iff.mp (T_le_centralizer_Z₁ s hgT) z hz).symm
  have key : D.conj ⟨g, hgN⟩ (coordN D z hzN) =
      (unipSL (1 : D.K) : Matrix.SpecialLinearGroup (Fin 2) D.K).1.mulVec (coordN D z hzN) :=
    hg _
  rw [conj_fix_of_centralizes D hgN hgz, unipSL_mulVec] at key
  have hw1 : coordN D z hzN 1 = 0 := by simpa [uB_apply] using congrFun key 0
  have hw0 : coordN D z hzN 0 ≠ 0 := by
    intro h0
    apply hz1
    have hz0 : coordN D z hzN = 0 := funext fun i => by fin_cases i <;> simp [h0, hw1]
    have h1 : coordN D (1 : G) N.one_mem = 0 := by unfold coordN; simp
    exact coordN_injective D hzN N.one_mem (hz0.trans h1.symm)
  refine ⟨coordN D z hzN 0, hw0, ?_⟩
  funext i
  fin_cases i <;> simp [Direct523Semi.e₁, hw1]

theorem conj_mul_eq {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {u v : G}
    (hu : u ∈ Subgroup.normalizer (N : Set G)) (hv : v ∈ Subgroup.normalizer (N : Set G)) :
    D.conj ⟨u * v, mul_mem hu hv⟩ = (D.conj ⟨v, hv⟩).trans (D.conj ⟨u, hu⟩) := by
  refine AddEquiv.ext fun w => ?_
  rw [AddEquiv.trans_apply]
  exact NatL2Data.conj_mul D ⟨u, hu⟩ ⟨v, hv⟩ w

theorem conj_Z₁_trivial (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact) {N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {z : G} (hz : z ∈ Z₁)
    (hz1 : z ≠ 1) (hzN : z ∈ N) {c : G} (hc : c ∈ Z₁) {hc' : c ∈ Subgroup.normalizer (N : Set G)}
    (w : Fin 2 → D.K) : D.conj ⟨c, hc'⟩ w = w := by
  apply conj_Z₁_eq_id D (fun a ha b hb => D.mem_comm ha hb) hzN _ w
  rcases s.eq_one_or_eq hz hz1 hc with h | h
  · exact Or.inl h
  · exact Or.inr h

end CFSG.Quasithin.H13

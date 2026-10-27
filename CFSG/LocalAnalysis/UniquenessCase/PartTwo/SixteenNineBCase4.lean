module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case4_not_quasisimple {M : Type} [Group M] {K : Subgroup M}
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) : ¬ CFSG.Open.IsQuasisimple ↥K := by
  rintro ⟨-, hs⟩
  have hc : Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hK y y.2 x x.2)
  have h1 : Nat.card (↥K ⧸ Subgroup.center ↥K) = 1 := by
    rw [← Subgroup.index, Subgroup.index_eq_one]
    exact hc
  haveI := hs.toNontrivial
  haveI : Finite (↥K ⧸ Subgroup.center ↥K) := Nat.finite_of_card_ne_zero (by omega)
  have h2 : Subsingleton (↥K ⧸ Subgroup.center ↥K) := Finite.card_le_one_iff_subsingleton.1 h1.le
  exact not_nontrivial_iff_subsingleton.2 h2 ‹_›

theorem s16n9b_case4_pcore (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {p r : ℕ} (hp : p.Prime) (hr : 1 < r)
    (hL : IsElemAbelianOfRank p r ↥(lBar V₀ V hV L)) :
    lBar V₀ V hV L ≤ pCoreOf p (Mbar D.M V₀ V hV) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hL
  have hcomm : ∀ x ∈ lBar V₀ V hV L, ∀ y ∈ lBar V₀ V hV L, x * y = y * x := by
    intro x hx y hy
    have h := mul_comm (e ⟨x, hx⟩) (e ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (e.injective h)
  obtain ⟨t, -, -, -, -, -, -, h⟩ := hc.conc
  rcases h with h133 | ⟨K, hK, g, -, -, hLK, -⟩ | ⟨hcomp, -⟩ | ⟨-, -, hcomp, -⟩
  · obtain ⟨p', hp', hLp, -⟩ := h133
    let i0 : Fin r := ⟨0, by omega⟩
    let x : ↥(lBar V₀ V hV L) := e.symm (Multiplicative.ofAdd (Pi.single i0 (1 : ZMod p)))
    have hx1 : x ≠ 1 := by
      intro h
      have h' : Multiplicative.ofAdd (Pi.single i0 (1 : ZMod p)) =
          (1 : Multiplicative (Fin r → ZMod p)) := by
        have := congrArg e h
        simpa [x] using this
      have h'' := congrFun (Multiplicative.ofAdd.injective h') i0
      simp at h''
    have hxp : x ^ p = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      simp only [x, MulEquiv.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      ext i
      simp
    have hord : orderOf x = p := orderOf_eq_prime hxp hx1
    have hxmem : (x : MulAut (Vtil V₀ V hV)) ∈ pCoreOf p' (Mbar D.M V₀ V hV) := hLp x.2
    haveI : Fact p'.Prime := ⟨hp'⟩
    have hpg : IsPGroup p' ↥(pCoreOf p' (Mbar D.M V₀ V hV)) :=
      (CFSG.pCore_isPGroup (p := p') (G := ↥(Mbar D.M V₀ V hV))).map (Mbar D.M V₀ V hV).subtype
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hpg) ⟨x, hxmem⟩
    have hk' : orderOf (x : MulAut (Vtil V₀ V hV)) = p' ^ k :=
      (Subgroup.orderOf_coe (⟨x.1, hxmem⟩ : ↥(pCoreOf p' (Mbar D.M V₀ V hV)))).trans hk
    have hord' : orderOf (x : MulAut (Vtil V₀ V hV)) = p :=
      (Subgroup.orderOf_coe x).trans hord
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk'
      have : p = 1 := by rw [← hord', hk']
      exact hp.ne_one this
    have hdvd : p' ∣ p := by
      rw [← hord', hk']
      exact dvd_pow_self p' hk0
    have hpp' : p' = p := (Nat.prime_dvd_prime_iff_eq hp' hp).1 hdvd
    subst hpp'
    exact hLp
  · refine (s16n9b_case4_not_quasisimple (K := K) (fun a ha b hb => hcomm a ?_ b ?_) hK.2.2).elim
    · rw [hLK]
      exact Subgroup.mem_sup_left ha
    · rw [hLK]
      exact Subgroup.mem_sup_left hb
  · exact (s16n9b_case4_not_quasisimple hcomm hcomp.2.2).elim
  · exact (s16n9b_case4_not_quasisimple hcomm hcomp.2.2).elim

theorem s16n9b_case4_good (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 1 < r)
    (h4 : Case168_4At D V₀ V hV L p r)
    (hge : 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV)) (hk : D.k < dParam p) :
    s16n9bGood (Mbar D.M V₀ V hV) p D.k (D.k + 2) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  exact s16n9b_case4_core (s15_Infra_vtil_sq_eq_one V₀ V hV) hp hr h4.1
    (s16n9b_case4_pcore D hV hc hpp hr h4.1) h4.2.1 hge hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

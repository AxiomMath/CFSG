module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s13_outAbelian_of_isU3_even {X : Type} [Group X] [Finite X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (hU : IsU3 X n) (heven : Even n) :
    ∀ σ τ : MulAut X, ∃ y : X, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y := by
  obtain ⟨N, hNn, hInn, hcyc, -, hev⟩ := UCK.u3OutShape X n (uc22p22d_isSU3_of_isU3 hq hU)
  haveI : N.Normal := hNn
  haveI : IsCyclic (MulAut X ⧸ N) := hcyc
  have hNeq : N = (MulAut.conj : X →* MulAut X).range := le_antisymm (hev heven) hInn
  intro σ τ
  have hmem : σ * τ * σ⁻¹ * τ⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply, ← commutatorElement_def,
      map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative (MulAut X ⧸ N)) _ _)
  rw [hNeq] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy.symm⟩

theorem s13_mem_Lp_sup_Sp_of_inner {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hns : s13_NormalSimple (Bar2 M)) {x : G} (hxM : x ∈ M) (hx : ∃ k : ℕ, x ^ p ^ k = 1)
    (hinner : ∀ J : Subgroup (Bar2 M), CFSG.IsComponent J →
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ : Bar2 M) ∈
        J ⊔ Subgroup.centralizer (J : Set (Bar2 M))) :
    x ∈ F13.Lp M p ⊔ F13.Sp M p := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨e, he, c, hc, hec⟩ := s13_exists_mul_of_inner hns hinner
  obtain ⟨a', ha', b', hb', hab⟩ :=
    s13_exists_pPart_mul hp (A := CFSG.layer (Bar2 M))
      (B := Subgroup.centralizer (CFSG.layer (Bar2 M) : Set (Bar2 M))) (hAB := le_rfl)
      (hx := ⟨k, s13_Thirteen2_pow_bar hxM hk⟩) he hc hec
  have ha'E : a' ∈ barImage M (F13.Lp M p) := by
    rw [s13_barImage_Lp M hp]
    exact ha'
  have hb'S : b' ∈ barImage M (F13.Sp M p) := by
    rw [s13_barImage_Sp M hp]
    exact s13_Thirteen2_pElementSubgroup_mono
      (Subgroup.centralizer_le (s13_Thirteen2_pElementSubgroup_le p (CFSG.layer (Bar2 M)))) hb'
  have hbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ : Bar2 M) ∈
      barImage M (F13.Lp M p ⊔ F13.Sp M p) := by
    rw [s13_barImage_sup (s13_Lp_le M p) (s13_Sp_le M p), hab]
    exact Subgroup.mul_mem_sup ha'E hb'S
  haveI : ((F13.Lp M p).subgroupOf M).Normal := s13_Lp_normal M p
  haveI : ((F13.Sp M p).subgroupOf M).Normal := s13_Sp_normal M p
  have hnormal : ((F13.Lp M p ⊔ F13.Sp M p).subgroupOf M).Normal := by
    rw [Subgroup.subgroupOf_sup (s13_Lp_le M p) (s13_Sp_le M p)]
    infer_instance
  exact s13_mem_of_barImage_of_pPart (sup_le (s13_Lp_le M p) (s13_Sp_le M p)) hnormal
    hp hp2 hxM ⟨k, hk⟩ hbar

theorem opp_eq_Lp_sup_Sp_of_inner {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hns : s13_NormalSimple (Bar2 M))
    (hinner : ∀ x : G, ∀ hxM : x ∈ M, (∃ k : ℕ, x ^ p ^ k = 1) →
      ∀ J : Subgroup (Bar2 M), CFSG.IsComponent J →
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ : Bar2 M) ∈
          J ⊔ Subgroup.centralizer (J : Set (Bar2 M))) :
    Opp p M = F13.Lp M p ⊔ F13.Sp M p := by
  refine le_antisymm ?_ (s13_Lp_sup_Sp_le_opp M p)
  change Subgroup.closure {x : G | x ∈ M ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤ F13.Lp M p ⊔ F13.Sp M p
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hxM, k, hk⟩
  have hx : ∃ k : ℕ, x ^ p ^ k = 1 := ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩
  exact s13_mem_Lp_sup_Sp_of_inner hp hp2 hns hxM hx (hinner x hxM hx)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

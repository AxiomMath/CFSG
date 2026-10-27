module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux4
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216

public section

open CFSG.Open
open scoped commutatorElement Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] {p : ℕ}

theorem isGreatest_scalJoin
    [Finite Γ] {A X : Subgroup Γ} (h : NearAsolvAction p A X) :
    IsGreatest {Z : Subgroup Γ | Z ≤ X ∧ Admits (cenIn X (A : Set Γ) ⊔ A) Z ∧ Group.IsSolvable Z}
      (scalJoin X A (cenIn X (A : Set Γ))) := by
  have hDA : cenIn X (A : Set Γ) ⊔ A ≤ Subgroup.normalizer (X : Set Γ) :=
    sup_le (inf_le_left.trans Subgroup.le_normalizer) h.admits
  refine ⟨⟨Thm211.scalJoin_le_left _ _ _, Thm211.sup_le_normalizer_scalJoin inf_le_right
    (inf_le_left.trans Subgroup.le_normalizer) h.admits,
    (thm211b h le_rfl hDA).2⟩, fun Z hZ => ?_⟩
  obtain ⟨hZX, hZadm, hZs⟩ := hZ
  exact Thm211.le_scalJoin ⟨hZX, (sup_le_sup_right inf_le_right A).trans hZadm, hZs⟩

namespace Setup

variable [Finite Γ] {A X D D₂ N L R X₁ X₂ W : Subgroup Γ} [(D₂.subgroupOf D).Normal]
  (S : Setup p A X D D₂ N L R X₁ X₂ W)

include S

theorem scalJoin_inf_kOf :
    scalJoin X A (cenIn X (A : Set Γ)) ⊓ kOf X = mOf A (kOf X) := by
  have hss := S.lemma213Hyp.semisimpleAction
  have hXK : kOf X ≤ X := kOf_le X
  have hAK : Admits (cenIn X (A : Set Γ) ⊔ A) (kOf X) := by
    rw [S.cen]
    exact S.admits_K
  have h1 := (thm211b S.hyp.near hXK hAK).1
  rw [Thm211.scalJoin_cenIn_eq hXK] at h1
  have h2 := (thm211a hss.toNearAsolvAction hss.semisimple).1
  rw [← h1]
  exact h2

theorem concl_of_k1_eq_bot
    (hk1 : k1 X W = ⊥) : Concl A D D₂ R := by
  have HW := S.lemma213Hyp
  have hss := HW.semisimpleAction
  have H := S.hyp
  have hD₂ : D₂ = ⊥ := S.D₂_eq_bot hk1
  have hPle : R ⊓ kOf X ≤ fProd A (kOf X) := by
    refine hss.le_fProd_iff.mpr ⟨inf_le_right, fun J hJ => ?_⟩
    have hJ2 : J ∈ Lemma213.tTwo X W := by
      rw [S.tTwo_eq_lcal hk1]
      exact hJ
    exact (S.projIn_le_fProd hJ2).trans ((hss.le_fProd_iff.mp le_rfl).2 J hJ)
  have hRadm : Admits (cenIn X (A : Set Γ) ⊔ A) R := by
    rw [S.cen]
    exact (sup_le (D_le_H R D A) (A_le_H R D A)).trans H.H_le_R
  have hRK : R ≤ kOf X := by
    have hGr := isGreatest_scalJoin H.near
    have hZK : R ⊓ kOf X ≤ s1 X (scalJoin X A (cenIn X (A : Set Γ))) := by
      unfold s1 s0
      rw [S.scalJoin_inf_kOf, hss.mOf_eq_kProd, hss.fittingSubgroupOf_kProd]
      exact hPle
    have hc := lemma216c H.near S.sol_eq S.ne_bot hGr H.hR hRadm hZK
    exact hc.trans (inf_le_left.trans inf_le_right)
  have hRle : R ≤ fProd A (kOf X) := fun x hx =>
    hPle (Subgroup.mem_inf.mpr ⟨hx, hRK hx⟩)
  have := hss.isMulCommutative_fProd
  have hcomm : IsMulCommutative ↥R := Thm210.isMulCommutative_of_le hRle
  have hAp : IsPGroup p A := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A
    H.near.elemAbelian
  have hcop : Nat.Coprime p (Nat.card R) :=
    H.near.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le H.hR)
  have hAR : A ≤ Subgroup.normalizer (R : Set Γ) := (A_le_H R D A).trans H.H_le_R
  have hDR : D ≤ Subgroup.normalizer (R : Set Γ) := (D_le_H R D A).trans H.H_le_R
  have hDA : D ≤ Subgroup.normalizer (A : Set Γ) := fun d hd => by
    have hd' : d ∈ cenIn X (A : Set Γ) := by rw [S.cen]; exact hd
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hd').2
  have hRB := CFSG.SignalizerFunctor.Helpers.normalized_commutator_target_normalizes A R hAR
  have hAB := CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A R hAR
  have hDB : D ≤ Subgroup.normalizer ((⁅R, A⁆ : Subgroup Γ) : Set Γ) := fun d hd => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDR hd),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDA hd)]
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization p
    H.near.prime A R hAp hAR hcop
  have hbot := commutator_inf_centralizer_eq_bot H.near.prime hAp hAR hcop
  refine ⟨⁅R, A⁆, CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing R A hAR,
    ⟨(CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing R A hAR).trans
      (R_le_H R D A), sup_le (sup_le hRB hDB) hAB⟩, ?_, ?_⟩
  · rw [hD₂]
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxB, hxD⟩ := Subgroup.mem_inf.mp hx
    have hxD' : x ∈ cenIn X (A : Set Γ) := by rw [S.cen]; exact hxD
    have : x ∈ ⁅R, A⁆ ⊓ Subgroup.centralizer (A : Set Γ) :=
      Subgroup.mem_inf.mpr ⟨hxB, (Subgroup.mem_inf.mp hxD').2⟩
    rwa [hbot] at this
  · rw [← H.RD]
    have h1 : R ⊓ D = R ⊓ Subgroup.centralizer (A : Set Γ) := by
      rw [← S.cen]
      unfold cenIn
      rw [← inf_assoc, inf_eq_left.mpr H.hR]
    rw [h1, hfac]

end Setup

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35

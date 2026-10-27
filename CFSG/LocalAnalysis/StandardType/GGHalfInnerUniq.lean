module

public import CFSG.LocalAnalysis.StandardType.GGHalfEndNodes
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

theorem pComponent_conj_eq_of_perfect_common {G : Type} [Group G] [Finite G] {y' r : G}
    {K' J P : Subgroup G}
    (hK' : LargeEvenPComponent 3 (Subgroup.centralizer ({y'} : Set G)) K') (hJ : J ≤ K')
    (hr : r ∈ Subgroup.normalizer (Subgroup.zpowers y' : Set G))
    (hP : P ≤ J ⊓ J.map (MulAut.conj r).toMonoidHom) (hperf : ⁅P, P⁆ = P) (h3 : 3 ∣ Nat.card P) :
    K'.map (MulAut.conj r).toMonoidHom = K' := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hzw : Subgroup.zpowers (r * y' * r⁻¹) = Subgroup.zpowers y' :=
    (MonoidHom.map_zpowers (MulAut.conj r).toMonoidHom y').symm.trans
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hr)
  have hcomp : LargeEvenPComponent 3 (Subgroup.centralizer ({y'} : Set G))
      (K'.map (MulAut.conj r).toMonoidHom) := by
    have h := largeEvenPComponent_conj_centralizer_singleton hK' r
    rwa [centralizer_singleton_eq_of_zpowers_eq hzw] at h
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3
  have hgordG : orderOf ((g : ↥P) : G) = 3 :=
    (orderOf_injective P.subtype Subtype.coe_injective (g : ↥P)).trans hgord
  have hgp : ((g : ↥P) : G) ^ 3 = 1 := by
    rw [← hgordG]
    exact pow_orderOf_eq_one _
  have hg1 : ((g : ↥P) : G) ≠ 1 := by
    intro h
    have h1 : orderOf ((g : ↥P) : G) = 1 := by rw [h, orderOf_one]
    rw [hgordG] at h1
    exact (by omega : (3 : ℕ) ≠ 1) h1
  have hPK' : P ≤ K' := (hP.trans inf_le_left).trans hJ
  have hPK'r : P ≤ K'.map (MulAut.conj r).toMonoidHom :=
    (hP.trans inf_le_right).trans (Subgroup.map_mono hJ)
  exact (eq_of_pComponents_of_perfect_common (A := K')
    (A' := K'.map (MulAut.conj r).toMonoidHom) hK' hcomp hPK' hPK'r
    (le_of_eq hperf.symm) g.2 hg1 hgp).symm

namespace GGHalfCtx

theorem nbr_eq_of_zpowers_eq {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hLB : GGLBalanceInput) {y' : G}
    {K' : Subgroup G} (hnbr : GGNbr p B x D J y' K')
    (hy : Subgroup.zpowers y' = Subgroup.zpowers y) : K' = K := by
  obtain ⟨hI, hBs, hDJ⟩ := h.cfg
  obtain ⟨-, hp3, -, -, hnbrY, -, -⟩ := h.nbr
  subst hp3
  have hinj : Function.Injective (φ₁.comp (slLower2Hom m)) :=
    h.coords.inj₁.comp (slLower2Hom_injective m)
  have hcardJ : Nat.card J = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) := by
    rw [← h.coords.rangeJ]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hm : 1 ≤ m := by
    have := h.nbr.2.2.1
    omega
  have hpJ : 3 ∣ Nat.card J := by
    rw [hcardJ]
    exact three_dvd_card_sl m hm
  exact (ggNbr_unique hLB hI hDJ hpJ hnbrY hnbr hy.symm).symm

end GGHalfCtx

end CFSG.StandardType

end

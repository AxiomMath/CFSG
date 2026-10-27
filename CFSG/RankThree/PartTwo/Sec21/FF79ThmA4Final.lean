module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3Mk
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L5Final
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKNoInv
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKL34Holds

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G] [Finite G]

theorem ff79_3_final4 (hNo : FF79KNoInvA5) (hL34 : FF79KL34) {b : G} {J B A : Subgroup G}
    (h3 : FF79Sec3 b J) (hyp : FF79Hyp 4 b J) (helem : IsElemAb 3 4 A)
    (hodd : Odd (Nat.card (CenS B))) (hJ : J = OUpp 2 (Cen b))
    (hBgen : Subgroup.zpowers b ⊔ (B ⊓ J) = B) (h35 : FF79Concl35 b A) : False := by
  obtain ⟨U₁, U₂, hU1, hU2, hsup, -, hbU₁, hbU₂, hU₁L, hU₂L, hm₁, hm₂, hK₁, hK₂⟩ := h35
  have hb3 : b ^ 3 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hyp.ord] at this
  have hc1 : Nat.card U₁ = 9 := by have := hU1.2; norm_num at this; exact this
  have hc2 : Nat.card U₂ = 9 := by have := hU2.2; norm_num at this; exact this
  have hodd2 : Odd (Nat.card (Opp 3 (CenS U₂))) :=
    ff79_opp3_cenS_odd helem ((le_sup_right : U₂ ≤ U₁ ⊔ U₂).trans hsup.le) h3.rank3
  have hmodel₁ : StatedClassicalModel (LayerQ (CenS U₁)) .PSL 3 2 2 :=
    model_of_mulEquiv Subgroup.topEquiv.symm hm₁
  have hmodel₂ : StatedClassicalModel (LayerQ (CenS U₂)) .PSL 3 2 2 :=
    model_of_mulEquiv Subgroup.topEquiv.symm hm₂
  obtain ⟨p, hpL, hpU₁, hp4, hp2, hpb⟩ :=
    exists_fixed_square hL34.1 hb3 hc1 hbU₁ hbU₂ hU₁L hmodel₂ hK₂ hodd2
  have hpU₂ : p ∈ CenS U₂ := OppE_le _ hpL
  have hcomm := sq_centralizes hL34.2 hc2 hU₂L hmodel₁ hK₁ hpU₁ hpU₂ hp4 hpb
  have hζc : p ^ 2 ∈ Cen b := by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    exact mul_inv_eq_iff_eq_mul.mp hpb
  have hζ2 : (p ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hp4
  have hζJ : p ^ 2 ∈ J := by
    rw [hJ]
    exact mem_OUpp_of_pow (p := 2) (k := 1) hζc (by rw [pow_one]; exact hζ2)
  have hord : orderOf (p ^ 2) = 2 := orderOf_eq_prime hζ2 hp2
  have hKJ : OUpp 2 (OppE 3 (CenS U₁) ⊓ Cen b) ≤ J := by
    rw [hJ]
    exact OUpp_mono 2 inf_le_right
  have hJb : J ≤ Cen b := hyp.std.1
  refine false_of_commuting_involution hNo (Or.inl rfl) hyp.model hKJ hK₁ ?_ hζJ hord hcomm
  intro t ht hto hcen
  have htb : t * b = b * t := by
    have := Subgroup.mem_centralizer_iff.mp (hJb ht) b (Set.mem_singleton b)
    exact this.symm
  have hBle : B ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [← hBgen]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]; exact htb
    · intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact hcen x hx.2
  have htC : t ∈ CenS B := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hBle hx) t (Set.mem_singleton t)).symm
  have hdvd : orderOf t ∣ Nat.card (CenS B) := by
    have := orderOf_dvd_natCard (⟨t, htC⟩ : CenS B)
    rwa [Subgroup.orderOf_mk] at this
  rw [hto] at hdvd
  obtain ⟨m, hm⟩ := hodd
  omega

theorem ff79TheoremA_simpleK4_core
    (hO : FF79KLemmaOP) (hAS : FF79AStarExists4) :
    ∀ (G : Type) [Group G] [Finite G] (b : G) (J : Subgroup G),
      IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) → KProper InCatalog G →
        FF79Hyp 4 b J → ConjInto b J := by
  intro G _ _ b J hs hna hK hyp
  by_contra hc
  have hFtop := generalizedFitting_eq_top_of_simple' hs hna
  have hsF : IsSimpleGroup (generalizedFitting G) := by
    rw [hFtop]
    exact Subgroup.topEquiv.isSimpleGroup
  obtain ⟨B, A, P, D, hpre⟩ := S3.exists_sec34Pre4 hs hna hyp hc
  have h3 : FF79Sec3 b J :=
    ⟨hsF, Or.inl hyp, hyp.rank.trans (pRank_cen_eq_three hpre.sylB hpre.elemB), hc⟩
  have hin := hpre.toIn (hAS G b J B A P D hs hna hK h3 hpre)
  have h35 := ff79_3_5_of_in_holds hO hs hna hK h3 hin
  exact ff79_3_final4 ff79KNoInvA5_holds ff79KL34_holds h3 hyp hpre.elemA hpre.oddCB hpre.hJ
    hpre.supB h35

end CFSG.RankThree.PartTwo.Sec21.FF79.H4

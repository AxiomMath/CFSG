module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxMark
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxModel

public section

namespace CFSG.StandardType.QTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.StandardType CFSG.Blueprint CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qTwoNbrRec_core
    {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig 3 B Bs x L D J)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) {y : G} {K : Subgroup G}
    (hnbr : GGNbr 3 B x D J y K) (hJK : J ≤ K)
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G))) {d : ℕ} (hd : 5 ≤ d)
    (hmark : GGInnerDiagOnLabel ggRowP_ESU 3 Bs K)
    (hK : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU d 2 1) :
    Nonempty (QTwoNbrModel 3 B Bs x L D J y K) := by
  classical
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hmark' := qTwoNbrRec_marking hd hmark hK
  obtain ⟨F, hFf, hFfin, θ, hF, hperf, hN, hind⟩ := qTwoNbrRec_unpack hd hmark'
  letI : Field F := hFf
  letI : Finite F := hFfin
  have hFd : UnitaryFieldData 2 1 F := TableBU.unitaryFieldData_of_card hF le_rfl
  haveI : CharP F 2 := hFd.charP
  have hBsel : CFSG.Open.IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hrank : 3 ^ (d / 3 + 2) ≤ Nat.card (ggGamma K hN).range := by
    by_cases hd6 : d = 6
    · subst hd6
      exact qTwoNbrRec_rank_six hLB hPJ hcfg hnbr hN hmark'
    · exact qTwoNbrRec_rank_ne_six hcfg hnbr hN hd hd6 hF hperf θ
  obtain ⟨Q, hQ, q, hq_surj, hq_ker⟩ := qTwoNbrRec_exists_quot hN
  obtain ⟨ψ, hψker, hψrange, hψdiag⟩ :=
    qTwoNbrRec_model_psi hN hBsel hF hd θ hperf hind hrank q hq_ker
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  exact ⟨{
    hJK := hJK
    hcomp := hcomp
    hKperf := hperf
    hxBs := hxBs
    hBsN := hN
    Delta := qTwoNbrRec_Delta K
    hDelta_le_K := qTwoNbrRec_Delta_le K
    hDelta_central := fun _ hd' k hk => qTwoNbrRec_Delta_central hd' k hk
    hDelta_pgroup := qTwoNbrRec_Delta_isPGroup K
    Q := Q
    groupQ := hQ
    q := q
    hq_surj := hq_surj
    hq_ker := hq_ker
    F0 := F
    hcardF0 := hF4
    d := d
    hd := hd
    ψ := ψ
    hψ_ker := hψker
    Kbar := qTwoNbrRec_Kb q
    hKbar := rfl
    As := (q.comp (Subgroup.inclusion (le_sup_right : Bs ≤ K ⊔ Bs))).range
    hAs := rfl
    hψ_range := hψrange
    hdiag := hψdiag
    Jbar := ((q.comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Bs))).comp
      (Subgroup.inclusion hJK)).range
    hJbar := rfl
    xbar := q ⟨x, (le_sup_right : Bs ≤ K ⊔ Bs) hxBs⟩
    hxbar := rfl
    CKbar := (q.comp (Subgroup.inclusion
      (show K ⊓ Subgroup.centralizer ({x} : Set G) ≤ K ⊔ Bs from
        le_trans inf_le_left le_sup_left))).range
    hCKbar := rfl }⟩

end CFSG.StandardType.QTwo

end

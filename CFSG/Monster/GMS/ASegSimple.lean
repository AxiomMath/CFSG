module

public import CFSG.Monster.GMS.ASegAmalgamAssemble
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10042
public import Certificates.Certificate10043
public import Certificates.Certificate10044
public import Certificates.Certificate10045
public import Certificates.Certificate10064
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import Certificates.Certificate10077
public import Certificates.Certificate8955

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog CFSG.Monster.GMS.S4Family
  CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Generic

variable {V' : Type*} {Γ' : SimpleGraph V'} {X X' : Type*} [Group X] [Group X'] [MulAction X' V']
  {ι : Type*}

theorem nonempty_mulEquiv_of_amalgam_simple (D' : TitsData Γ' X' ι) (hX' : IsSimpleGroup X')
    [Nontrivial X] (Xv Xe : Subgroup X) (Xt : ι → Subgroup X) (hgen : Xv ⊔ Xe = ⊤)
    (σv : Xv ≃* D'.Xv) (σe : Xe ≃* D'.Xe) (σt : ∀ j, Xt j ≃* D'.Xt j)
    (hve' : ∀ a (ha : a ∈ D'.Xv) (hb : a ∈ D'.Xe), (σv.symm ⟨a, ha⟩ : X) = σe.symm ⟨a, hb⟩)
    (hvt' : ∀ j a (ha : a ∈ D'.Xv) (hb : a ∈ D'.Xt j),
      (σv.symm ⟨a, ha⟩ : X) = (σt j).symm ⟨a, hb⟩)
    (het' : ∀ j a (ha : a ∈ D'.Xe) (hb : a ∈ D'.Xt j),
      (σe.symm ⟨a, ha⟩ : X) = (σt j).symm ⟨a, hb⟩) :
    Nonempty (X ≃* X') := by
  obtain ⟨Ψ, ⟨hΨv, hΨe, -⟩, -⟩ := D'.existsUnique_hom
    (Xv.subtype.comp σv.symm.toMonoidHom) (Xe.subtype.comp σe.symm.toMonoidHom)
    (fun j => (Xt j).subtype.comp (σt j).symm.toMonoidHom) hve' hvt' het'
  have hv : ∀ x : Xv, (x : X) ∈ Ψ.range := fun x => ⟨σv x, by simpa using hΨv (σv x)⟩
  have he : ∀ x : Xe, (x : X) ∈ Ψ.range := fun x => ⟨σe x, by simpa using hΨe (σe x)⟩
  have hrange : Ψ.range = ⊤ := by
    rw [eq_top_iff, ← hgen, sup_le_iff]
    exact ⟨fun x hx => hv ⟨x, hx⟩, fun x hx => he ⟨x, hx⟩⟩
  have hsurj : Function.Surjective Ψ := MonoidHom.range_eq_top.mp hrange
  have hker : Ψ.ker = ⊥ := by
    rcases hX'.eq_bot_or_eq_top_of_normal Ψ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : X)
      obtain ⟨x', rfl⟩ := hsurj x
      exact hx (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x'))
  have hinj : Function.Injective Ψ := (MonoidHom.ker_eq_bot_iff Ψ).mp hker
  exact ⟨(MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm⟩

end Generic

section Functions

variable {V' : Type*} {Γ' : SimpleGraph V'} {X X' : Type*} [Group X] [Group X'] [MulAction X' V']
  {ι : Type*}

theorem nonempty_mulEquiv_of_amalgam_isIsoOn_simple (D' : TitsData Γ' X' ι)
    (hX' : IsSimpleGroup X') [Nontrivial X] (Xv Xe : Subgroup X) (Xt : ι → Subgroup X)
    (hgen : Xv ⊔ Xe = ⊤) (fv fe : X → X') (ft : ι → X → X') (hv : IsIsoOn fv Xv D'.Xv)
    (he : IsIsoOn fe Xe D'.Xe) (ht : ∀ j, IsIsoOn (ft j) (Xt j) (D'.Xt j))
    (hve : ∀ g ∈ Xv ⊓ Xe, fv g = fe g) (hvt : ∀ j, ∀ g ∈ Xv ⊓ Xt j, fv g = ft j g)
    (het : ∀ j, ∀ g ∈ Xe ⊓ Xt j, fe g = ft j g)
    (hve' : ∀ g ∈ Xv, fv g ∈ D'.Xe → g ∈ Xe)
    (hvt' : ∀ j, ∀ g ∈ Xv, fv g ∈ D'.Xt j → g ∈ Xt j)
    (het' : ∀ j, ∀ g ∈ Xe, fe g ∈ D'.Xt j → g ∈ Xt j) : Nonempty (X ≃* X') :=
  nonempty_mulEquiv_of_amalgam_simple D' hX' Xv Xe Xt hgen (isoEquiv hv) (isoEquiv he)
    (fun j => isoEquiv (ht j))
    (fun g' hg' hb' => symm_compat_of_isIsoOn hv he hve hve' g' hg' hb')
    (fun j g' hg' hb' => symm_compat_of_isIsoOn hv (ht j) (hvt j) (hvt' j) g' hg' hb')
    (fun j g' hg' hb' => symm_compat_of_isIsoOn he (ht j) (het j) (het' j) g' hg' hb')

end Functions

section Monster

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {d₀ d₀' : B}
  {a z₀ y z : G} {a' z₀' y' z' : G'} {A Z : G → G'}

theorem centralizer_sup_edgeStab_eq_top
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) (hconn : (twoAGraph a).Preconnected) :
    C[a] ⊔ edgeStab (vertA a) (vertY D) = ⊤ :=
  sup_eq_top_of_preconnected (fun g _ _ h => twoAGraph_adj_smul g h) hconn
    (fun w hw => harc_twoAGraph I hG (vertA a) (vertY D) (vertA a) w (aseg_adj hG D) hw)
    (harc_twoAGraph I hG (vertA a) (vertY D) (vertY D) (vertA a) (aseg_adj hG D)
      (aseg_adj hG D).symm)
    (fun g => (smul_eq_self_iff g (vertA a)).symm) (fun _ => mem_edgeStab)

theorem nonempty_mulEquiv_of_amalgamData_simple
    (I : GMSInterfaces d₀ G)
    (I' : GMSInterfaces d₀' G') (hG : GMSF1Type d₀ a z₀) (hG' : GMSF1Type d₀' a' z₀')
    (D : ASegData a z₀ y z) (D' : ASegData a' z₀' y' z') (Q : AmalgamData a y z a' y' z' A Z)
    (hconn : (twoAGraph a).Preconnected) (hconn' : (twoAGraph a').Preconnected)
    (hΓ' : Triangulable (twoAGraph a')) (hsimple : IsSimpleGroup G') :
    Nonempty (G ≃* G') := by
  have M := amalgamIsos_of hG D D' Q
  have : Nontrivial G := ⟨⟨a, 1, fun h => by
    have h2 := hG.1.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)⟩⟩
  exact nonempty_mulEquiv_of_amalgam_isIsoOn_simple (asegTitsData I' hG' D' hconn' hΓ') hsimple
    C[a] (edgeStab (vertA a) (vertY D)) (XtB a y z)
    (centralizer_sup_edgeStab_eq_top I hG D hconn) A (asegTheta A Z a y z)
    (fun j => cond j Z (asegTheta A Z a y z)) M.hv M.he M.ht M.hve M.hvt M.het M.hve' M.hvt'
    M.het'

theorem nonempty_mulEquiv_of_triangulable_simple
    (I : GMSInterfaces d₀ G)
    (I' : GMSInterfaces d₀' G') (hG : GMSF1Type d₀ a z₀) (hG' : GMSF1Type d₀' a' z₀')
    (hTB : TwoBabyUnique) (hDC : Co1DoubleCoverTwoB)
    (hconn : (twoAGraph a).Preconnected) (hconn' : (twoAGraph a').Preconnected)
    (hΓ' : Triangulable (twoAGraph a')) (hsimple : IsSimpleGroup G')
    (hKR : KAutRigid a z₀) (hCB : CentInvAutInnerTwoAB a z₀) :
    Nonempty (G ≃* G') := by
  obtain ⟨y, z, D⟩ := exists_asegData I hG
  have hCB' : CentInvAutInnerAt a z := hCB a z (IsConj.refl a) ⟨D.isConj_z, D.isConj_az⟩
  obtain ⟨A, Z, y', z', D', P⟩ := exists_alpha_zeta I I' hG hG' hTB hDC hCB' D
  have Q : AmalgamData a y z a' y' z' A Z :=
    { alphaZeta := P
      comm3 := D.comm3 hG
      comm3' := D'.comm3 hG'
      dec := fun _ hg => D.exists_mul_of_mem_Xt0 (eightGroupLines_of I hG) hG hg
      dec' := fun _ hg => D'.exists_mul_of_mem_Xt0 (eightGroupLines_of I' hG') hG' hg
      key := key_identity I hG (hKR y z D) D P }
  exact nonempty_mulEquiv_of_amalgamData_simple I I' hG hG' D D' Q hconn hconn' hΓ' hsimple

end Monster

end CFSG.Monster.GMS

module

public import CFSG.Monster.B.TwoA.Amalgam.Kernels
public import CFSG.Monster.B.TwoA.Unitary.Coinv
public import CFSG.Monster.B.TwoA.Sp8.Par1Center
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate16016
public import Certificates.Certificate16022
public import Certificates.Certificate16040
public import Certificates.Certificate16951
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0)
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem not_exists_retraction_of {z : G} (hz1 : z ≠ 1) (hzc : z ∈ commutator G) :
    ¬ ∃ φ : G →* Subgroup.zpowers z, φ z = ⟨z, Subgroup.mem_zpowers _⟩ := by
  rintro ⟨φ, hφ⟩
  have hab : ∀ a b : Subgroup.zpowers z, a * b = b * a := fun a b => by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hk, ← zpow_add, ← zpow_add, add_comm]
  have hker : commutator G ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hab (φ a) (φ b),
      mul_inv_cancel_right, mul_inv_cancel]
  have h1 := hker hzc
  rw [MonoidHom.mem_ker, hφ] at h1
  exact hz1 (congrArg Subtype.val h1)

theorem mul_section_aux (g h tg th : G) (hc : ∀ x, h * th⁻¹ * x = x * (h * th⁻¹)) :
    g * h * (th⁻¹ * tg⁻¹) = g * tg⁻¹ * (h * th⁻¹) := by
  calc g * h * (th⁻¹ * tg⁻¹) = g * (h * th⁻¹) * tg⁻¹ := by group
    _ = h * th⁻¹ * g * tg⁻¹ := by rw [← hc g]
    _ = h * th⁻¹ * (g * tg⁻¹) := by group
    _ = g * tg⁻¹ * (h * th⁻¹) := hc _

theorem not_exists_section_of {z : G} (hzZ : z ∈ Subgroup.center G) (hz1 : z ≠ 1)
    (hzc : z ∈ commutator G) [(Subgroup.zpowers z).Normal] :
    ¬ ∃ s : G ⧸ Subgroup.zpowers z →* G,
      ∀ q, (QuotientGroup.mk (s q) : G ⧸ Subgroup.zpowers z) = q := by
  rintro ⟨s, hs⟩
  apply not_exists_retraction_of hz1 hzc
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ x : G, w * x = x * w := fun w hw x =>
    (Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hzZ hw) x).symm
  have hmem : ∀ g : G, g * (s (QuotientGroup.mk g))⁻¹ ∈ Subgroup.zpowers z := fun g => by
    have h := hs (QuotientGroup.mk g)
    rw [QuotientGroup.eq] at h
    have hc := hcent _ h (s (QuotientGroup.mk g))
    have e : g * (s (QuotientGroup.mk g))⁻¹ = (s (QuotientGroup.mk g))⁻¹ * g := by
      calc g * (s (QuotientGroup.mk g))⁻¹ = s (QuotientGroup.mk g) *
            ((s (QuotientGroup.mk g))⁻¹ * g) * (s (QuotientGroup.mk g))⁻¹ := by group
        _ = (s (QuotientGroup.mk g))⁻¹ * g * s (QuotientGroup.mk g) *
            (s (QuotientGroup.mk g))⁻¹ := by rw [hc]
        _ = (s (QuotientGroup.mk g))⁻¹ * g := by group
    rw [e]
    exact h
  refine ⟨{ toFun := fun g => ⟨g * (s (QuotientGroup.mk g))⁻¹, hmem g⟩
            map_one' := by
              apply Subtype.ext
              show (1 : G) * (s (QuotientGroup.mk 1))⁻¹ = 1
              rw [QuotientGroup.mk_one, map_one, inv_one, mul_one]
            map_mul' := fun g h => by
              apply Subtype.ext
              show g * h * (s (QuotientGroup.mk (g * h)))⁻¹ =
                g * (s (QuotientGroup.mk g))⁻¹ * (h * (s (QuotientGroup.mk h))⁻¹)
              rw [QuotientGroup.mk_mul, map_mul, mul_inv_rev]
              exact mul_section_aux g h (s (QuotientGroup.mk g)) (s (QuotientGroup.mk h))
                (hcent _ (hmem h)) }, ?_⟩
  apply Subtype.ext
  show z * (s (QuotientGroup.mk z))⁻¹ = z
  rw [(QuotientGroup.eq_one_iff z).2 (Subgroup.mem_zpowers _), map_one, inv_one, mul_one]

theorem not_isComplement_of {z : G} (hzZ : z ∈ Subgroup.center G) (hz1 : z ≠ 1)
    (hzc : z ∈ commutator G) [(Subgroup.zpowers z).Normal] :
    ¬ ∃ H : Subgroup G, Subgroup.IsComplement' H (Subgroup.zpowers z) := by
  rintro ⟨H, hH⟩
  exact not_exists_section_of hzZ hz1 hzc ⟨H.subtype.comp hH.QuotientMulEquiv.toMonoidHom,
    fun q => Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hH q⟩

end Generic

theorem mem_orthogonal_sigLine_iff
    (x : Wv v0) :
    x ∈ bV.orthogonal sigLine ↔ x ∈ Unitary.sigmaPerp := by
  change _ ↔ Unitary.bW Unitary.sigmaW x = 0
  constructor
  · intro h
    exact h _ sigmaW_mem_sigLine
  · intro h y hy
    rcases mem_sigLine.1 hy with rfl | rfl
    · exact LinearMap.map_zero₂ _ _
    · exact h

theorem psiW_mem_sigmaPerp
    {d : Dfull} (hd : d ∈ N1) :
    psiW ⟨d, hd.1⟩ ∈ Unitary.sigmaPerp := by
  have h := hd
  rw [N1_eq_EU] at h
  obtain ⟨_, hU⟩ := mem_EU.1 h
  exact (mem_orthogonal_sigLine_iff _).1 hU

theorem mem_N1_of_psiW
    {e : Ehat} (he : psiW e ∈ Unitary.sigmaPerp) : (e : Dfull) ∈ N1 := by
  rw [N1_eq_EU]
  exact mem_EU_of ((mem_orthogonal_sigLine_iff _).2 he)

theorem conj_mem_N1 {p n : Dfull} (hp : p ∈ P1) (hn : n ∈ N1) : p * n * p⁻¹ ∈ N1 := by
  have hpc : p * cQ = cQ * p := Subgroup.mem_centralizer_singleton_iff.1 hp.2
  have hnc : n * cQ = cQ * n := Subgroup.mem_centralizer_singleton_iff.1 hn.2
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  · have h := conj_mem_Ehat (P1.inv_mem hp).1 hn.1
    rwa [inv_inv] at h
  · have hpc' : p⁻¹ * cQ = cQ * p⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hpc, mul_inv_cancel_right]
    calc p * n * p⁻¹ * cQ = p * n * (p⁻¹ * cQ) := by group
      _ = p * (n * cQ) * p⁻¹ := by rw [hpc']; group
      _ = (p * cQ) * n * p⁻¹ := by rw [hnc]; group
      _ = cQ * (p * n * p⁻¹) := by rw [hpc]; group

theorem commutator_N1_P1_le : ⁅N1, P1⁆ ≤ N1 := by
  rw [Subgroup.commutator_le]
  intro n hn p hp
  rw [commutatorElement_def, show n * p * n⁻¹ * p⁻¹ = n * (p * n⁻¹ * p⁻¹) by group]
  exact N1.mul_mem hn (conj_mem_N1 hp (N1.inv_mem hn))

@[expose] def commImage : Submodule (ZMod 2) (Wv v0) where
  carrier := {w | ∃ e : Ehat, (e : Dfull) ∈ ⁅N1, P1⁆ ∧ psiW e = w}
  add_mem' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    exact ⟨e * e', Subgroup.mul_mem _ he he', psiW_mul _ _⟩
  zero_mem' := ⟨1, Subgroup.one_mem _, psiW_one⟩
  smul_mem' := by
    intro t w hw
    rcases zmod2_cases t with rfl | rfl
    · rw [zero_smul]
      exact ⟨1, Subgroup.one_mem _, psiW_one⟩
    · rwa [one_smul]

theorem commImage_eq :
    commImage = Unitary.sigmaPerp := by
  apply Unitary.native_unitary_hyperplane_zero_coinvariants.2 commImage
  · rintro _ ⟨e, he, rfl⟩
    exact psiW_mem_sigmaPerp (commutator_N1_P1_le he)
  · intro v hv g hg
    obtain ⟨e, rfl⟩ := psiW_surjective v
    have hn : (e : Dfull) ∈ N1 := mem_N1_of_psiW hv
    obtain ⟨p, hp⟩ := p1Proj_surjective ⟨g, hg⟩
    have hpg : jhatToKv0 ⟨p, P1_le_Jhat p.2⟩ = g := by
      have h := congrArg Subtype.val hp
      rwa [coe_p1Proj] at h
    have hpJ : (p : Dfull) ∈ Jhat := P1_le_Jhat p.2
    refine ⟨⟨(p : Dfull)⁻¹ * e * p, conj_mem_Ehat hpJ e.2⟩ * e⁻¹, ?_, ?_⟩
    · have h : ⁅(p : Dfull)⁻¹, (e : Dfull)⁆ ∈ ⁅P1, N1⁆ :=
        Subgroup.commutator_mem_commutator (P1.inv_mem p.2) hn
      rw [Subgroup.commutator_comm, commutatorElement_def, inv_inv] at h
      exact h
    · rw [psiW_mul, psiW_conj hpJ e.2, psiW_inv, ZModModule.neg_eq_self, hpg]

theorem commutator_N1_P1 :
    ⁅N1, P1⁆ = N1 := by
  apply le_antisymm commutator_N1_P1_le
  intro n hn
  have hx : xhat ∈ ⁅N1, P1⁆ := by
    have h1 : (⟨xhat, xhat_mem_N1⟩ : N1) ∈ commutator N1 := by
      rw [commutator_N1, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_zpowers _
    have h2 : xhat ∈ (commutator N1).map N1.subtype := ⟨_, h1, rfl⟩
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2
    exact Subgroup.commutator_mono le_rfl N1_le_P1 h2
  have hv : psiW ⟨n, hn.1⟩ ∈ commImage := commImage_eq ▸ psiW_mem_sigmaPerp hn
  obtain ⟨d, hd, e⟩ := hv
  have h0 : psiW (d⁻¹ * ⟨n, hn.1⟩) = 0 := by
    rw [psiW_mul, psiW_inv, e, neg_add_cancel]
  rcases (psiW_eq_zero_iff _).1 h0 with h | h
  · have e' : (d : Dfull)⁻¹ * n = 1 := congrArg Subtype.val h
    rw [inv_mul_eq_one] at e'
    rw [← e']
    exact hd
  · have e' : (d : Dfull)⁻¹ * n = xhat := congrArg Subtype.val h
    rw [inv_mul_eq_iff_eq_mul] at e'
    rw [e']
    exact Subgroup.mul_mem _ hd hx

theorem cQ_mem_N1 : cQ ∈ N1 :=
  ⟨cQ_mem_Ehat, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem cQ_mem_Eam :
    cQ ∈ Eam := Pc_le_Eam 0 (N1_le_P1 cQ_mem_N1)

theorem N1_le_commutator_P1 :
    N1 ≤ ⁅P1, P1⁆ := by
  rw [← commutator_N1_P1]
  exact Subgroup.commutator_mono N1_le_P1 le_rfl

theorem commutator_P1_le_Eam :
    ⁅P1, P1⁆ ≤ ⁅Eam, Eam⁆ :=
  Subgroup.commutator_mono (Pc_le_Eam 0) (Pc_le_Eam 0)

theorem cQ_mem_commutator_Eam :
    cQ ∈ ⁅Eam, Eam⁆ :=
  commutator_P1_le_Eam (N1_le_commutator_P1 cQ_mem_N1)

@[expose] def cE' :
    Eam := ⟨cQ, cQ_mem_Eam⟩

theorem cE'_mem_center :
    cE' ∈ Subgroup.center Eam := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer g.2)

theorem cE'_ne_one :
    cE' ≠ 1 := fun h => cQ_ne_one (congrArg Subtype.val h)

instance zpowers_cE'_normal :
    (Subgroup.zpowers cE').Normal :=
  ⟨fun n hn g => by
    have hc : n ∈ Subgroup.center Eam := Subgroup.zpowers_le.2 cE'_mem_center hn
    rw [Subgroup.mem_center_iff.1 hc g, mul_inv_cancel_right]
    exact hn⟩

theorem cE'_mem_commutator :
    cE' ∈ commutator Eam := by
  have h : cQ ∈ (commutator Eam).map Eam.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact cQ_mem_commutator_Eam
  obtain ⟨g, hg, e⟩ := h
  have : g = cE' := Subtype.ext e
  rwa [this] at hg

theorem short_F4_central_extension_nonsplit :
    ⁅Nc 0, Pc 0⁆ = Nc 0 ∧ Nc 0 ≤ ⁅Pc 0, Pc 0⁆ ∧ ⁅Pc 0, Pc 0⁆ ≤ ⁅Eam, Eam⁆ ∧
    cQ ∈ ⁅Eam, Eam⁆ ∧ cE' ∈ Subgroup.center Eam ∧ orderOf cE' = 2 ∧
    (¬ ∃ s : Eam ⧸ Subgroup.zpowers cE' →* Eam,
      ∀ q, (QuotientGroup.mk (s q) : Eam ⧸ Subgroup.zpowers cE') = q) ∧
    ¬ ∃ H : Subgroup Eam, Subgroup.IsComplement' H (Subgroup.zpowers cE') := by
  have h0 : Nc 0 = N1 := Nc_zero
  refine ⟨?_, ?_, commutator_P1_le_Eam, cQ_mem_commutator_Eam, cE'_mem_center, ?_,
    not_exists_section_of cE'_mem_center cE'_ne_one cE'_mem_commutator,
    not_isComplement_of cE'_mem_center cE'_ne_one cE'_mem_commutator⟩
  · rw [h0]
    exact commutator_N1_P1
  · rw [h0]
    exact N1_le_commutator_P1
  · apply orderOf_eq_prime
    · apply Subtype.ext
      show cQ ^ 2 = 1
      rw [sq]
      exact cQ_mul_self
    · exact cE'_ne_one

end CFSG.Monster.B.TwoA.Amalgam

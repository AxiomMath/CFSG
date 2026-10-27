module

public import CFSG.Monster.Existence.TwoPoint.LeechStab
public import CFSG.Monster.Existence.TwoPointTwoB

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Generated CFSG.Monster.B.Short CFSG.Monster.B Subgroup

theorem leech_phi0_ne_zero {r : Q} (h : IsShortCoord (coordOf r)) :
    phi0 (coordOf r) ≠ 0 :=
  h.elim fun _ hu => fun h0 => classOf_ne_zero_of_mem_minVecs hu.1 (hu.2.trans h0)

theorem leech_qL_phi0_eq_zero {r : Q} (h : IsShortCoord (coordOf r)) :
    qL (phi0 (coordOf r)) = 0 :=
  h.elim fun _ hu => hu.2 ▸ qL_classOf_minVecs hu.1

theorem leechPre_mono {S S' : Submodule (ZMod 2) L2} (h : S ≤ S') : leechPre S ≤ leechPre S' :=
  fun _ hq => h hq

theorem leech_mul_self_mem_center_of_sq {G : Type*} [Group G] {c : Subgroup G} {a : G}
    (h : a ^ 2 ∈ c) : a * a ∈ c := by
  rwa [pow_two] at h

theorem leech_mul_self_mem_center_Q (a : Q) : a * a ∈ center Q :=
  leech_mul_self_mem_center_of_sq (sq_mem_center_of_extraspecial isExtraspecialPGroup_Q center_Q a)

theorem leechPre_mul_self_mem_center (S : Submodule (ZMod 2) L2) (a : leechPre S) :
    a * a ∈ center (leechPre S) :=
  mem_center_iff.2 fun d => Subtype.ext (mem_center_iff.1 (leech_mul_self_mem_center_Q a.1) d.1)

theorem orderOf_zQ_leechPre (S : Submodule (ZMod 2) L2) :
    orderOf (⟨zQ, zQ_mem_leechPre S⟩ : leechPre S) = 2 :=
  (Subgroup.orderOf_coe (⟨zQ, zQ_mem_leechPre S⟩ : leechPre S)).symm.trans orderOf_zQ

theorem zQ_mem_center_leechPre (S : Submodule (ZMod 2) L2) :
    (⟨zQ, zQ_mem_leechPre S⟩ : leechPre S) ∈ center (leechPre S) :=
  mem_center_iff.2 fun d => Subtype.ext (mem_center_iff.1 Short.zQ_mem_center d.1)

theorem center_leechPre_perp {u v : L2} (h1 : bL u v = 1) :
    center (leechPre (leechPerp u v)) =
      zpowers (⟨zQ, zQ_mem_leechPre _⟩ : leechPre (leechPerp u v)) := by
  refine le_antisymm (fun c hc => ?_) (zpowers_le.2 (zQ_mem_center_leechPre _))
  have h0 : phi0 (coordOf c.1) = 0 := phi0_eq_zero_of_forall_commute h1 c.2 fun d hd =>
    congrArg Subtype.val (mem_center_iff.1 hc ⟨d, hd⟩)
  rw [mem_zpowers_iff_of_orderOf_eq_two (orderOf_zQ_leechPre _)]
  exact ((phi0_coordOf_eq_zero_iff c.1).1 h0).elim (fun h => Or.inl (Subtype.ext h))
    (fun h => Or.inr (Subtype.ext h))

theorem natCard_center_leechPre_perp {u v : L2} (h1 : bL u v = 1) :
    Nat.card (center (leechPre (leechPerp u v))) = 2 :=
  (congrArg (fun H : Subgroup (leechPre (leechPerp u v)) => Nat.card H)
    (center_leechPre_perp h1)).trans ((Nat.card_zpowers _).trans (orderOf_zQ_leechPre _))

theorem center_leechPre_perp_ne_top {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h1 : bL u v = 1) : center (leechPre (leechPerp u v)) ≠ ⊤ := fun htop => by
  have h2 : Nat.card (center (leechPre (leechPerp u v))) =
      Nat.card (⊤ : Subgroup (leechPre (leechPerp u v))) :=
    congrArg (fun H : Subgroup (leechPre (leechPerp u v)) => Nat.card H) htop
  have h3 : (2 : ℕ) = 2 ^ 23 :=
    (natCard_center_leechPre_perp h1).symm.trans
      (h2.trans (Subgroup.card_top.trans (natCard_leechPre_perp hu hv huv)))
  exact absurd h3 (by norm_num)

theorem isExtraspecialPGroup_leechPre_perp {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h1 : bL u v = 1) : IsExtraspecialPGroup 2 (leechPre (leechPerp u v)) := by
  have : Finite (leechPre (leechPerp u v)) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_leechPre_perp hu hv huv]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsExtraspecial 2 (leechPre (leechPerp u v)) :=
    ⟨natCard_center_leechPre_perp h1,
      isElementaryAbelian_two_quotient (N := leechPre (leechPerp u v)) _
        (leechPre_mul_self_mem_center _),
      not_subsingleton_iff_nontrivial.1 fun hs => center_leechPre_perp_ne_top hu hv huv h1
        (QuotientGroup.subsingleton_iff.1 hs)⟩
  exact IsExtraspecial.isExtraspecialPGroup

abbrev leechN (r₁ r₂ : Q) : Subgroup (leechJ r₁ r₂) :=
  ((leechC r₁ r₂).map Short.rhoHom).subgroupOf (leechJ r₁ r₂)

instance normal_leechN (r₁ r₂ : Q) : (leechN r₁ r₂).Normal := normal_ker_leechC r₁ r₂

@[expose] def leechNEquivPerp (r₁ r₂ : Q) :
    leechN r₁ r₂ ≃* leechPre (leechPerp (phi0 (coordOf r₁)) (phi0 (coordOf r₂))) :=
  (leechNEquiv r₁ r₂).trans (MulEquiv.subgroupCongr (centralizer_inf_eq_leechPre r₁ r₂))

theorem natCard_leechN {r₁ r₂ : Q} (h₁ : phi0 (coordOf r₁) ≠ 0) (h₂ : phi0 (coordOf r₂) ≠ 0)
    (h₁₂ : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂)) : Nat.card (leechN r₁ r₂) = 2 ^ 23 :=
  (Nat.card_congr (leechNEquivPerp r₁ r₂).toEquiv).trans (natCard_leechPre_perp h₁ h₂ h₁₂)

theorem leechJ_extraspecial_shape
    {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (h12 : bL (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) = 1) :
    ∃ (N : Subgroup (leechJ r₁ r₂)) (_ : N.Normal), IsExtraspecialPGroup 2 N ∧
      Nat.card N = 2 ^ 23 ∧ Nonempty (leechJ r₁ r₂ ⧸ N ≃*
        ↥(Kstab (phi0 (coordOf r₁)) ⊓ Kstab (phi0 (coordOf r₂)))) := by
  have h₁ := leech_phi0_ne_zero hr₁
  have h₂ := leech_phi0_ne_zero hr₂
  have hne : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂) := fun h => by
    rw [h, bL_self] at h12
    exact zero_ne_one h12
  exact ⟨leechN r₁ r₂, normal_leechN r₁ r₂,
    IsExtraspecialPGroup.of_mulEquiv
      (G := leechPre (leechPerp (phi0 (coordOf r₁)) (phi0 (coordOf r₂)))) (H := leechN r₁ r₂)
      (leechNEquivPerp r₁ r₂).symm (isExtraspecialPGroup_leechPre_perp h₁ h₂ hne h12),
    natCard_leechN h₁ h₂ hne, ⟨leechQuotEquiv h₁ h₂ hne⟩⟩

abbrev leechT (v₁ v₂ : L2) : Subgroup Q :=
  leechPre (Submodule.span (ZMod 2) ({v₁, v₂} : Set L2))

theorem leechT_le_leechPerp {u v : L2} (h : bL u v = 0) :
    leechT u v ≤ leechPre (leechPerp u v) := leechPre_mono (span_pair_le_leechPerp h)

theorem zQ_mem_leechT (v₁ v₂ : L2) : zQ ∈ leechT v₁ v₂ := zQ_mem_leechPre _

theorem mul_self_mem_leechT (v₁ v₂ : L2) (q : Q) : q * q ∈ leechT v₁ v₂ :=
  (zpowers_le.2 (zQ_mem_leechT v₁ v₂)) (center_Q.le (leech_mul_self_mem_center_Q q))

theorem natCard_leechT {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Nat.card (leechT u v) = 2 ^ 3 := by
  rw [leechT, natCard_leechPre, leech_natCard_span_pair hu hv huv]
  norm_num

theorem isElementaryAbelian_leechT {u v : L2} (hu : qL u = 0) (hv : qL v = 0) (h : bL u v = 0) :
    IsElementaryAbelian 2 (leechT u v) :=
  isElementaryAbelian_two_of_mul_self (K := leechT u v) fun a => Subtype.ext
    ((mul_self_eq_one_iff_qL a.1).2 (qL_eq_zero_of_mem_span_pair hu hv h a.2))

theorem conjQ_mem_leechT {r₁ r₂ : Q} {p : Pvis} (hp : thetaEquiv p ∈ leechJ r₁ r₂) {t : Q}
    (ht : t ∈ leechT (phi0 (coordOf r₁)) (phi0 (coordOf r₂))) :
    conjQ p t ∈ leechT (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) := by
  obtain ⟨hc1, hc2⟩ := conjQ_eq_of_thetaEquiv_mem_leechJ hp
  have hf₁ : modTwoEnd p.1.2 (phi0 (coordOf r₁)) = phi0 (coordOf r₁) :=
    (phi0_conjQ p r₁).symm.trans (congrArg (fun r => phi0 (coordOf r)) hc1)
  have hf₂ : modTwoEnd p.1.2 (phi0 (coordOf r₂)) = phi0 (coordOf r₂) :=
    (phi0_conjQ p r₂).symm.trans (congrArg (fun r => phi0 (coordOf r)) hc2)
  have key : ∀ w ∈ Submodule.span (ZMod 2) ({phi0 (coordOf r₁), phi0 (coordOf r₂)} : Set L2),
      modTwoEnd p.1.2 w = w := fun w hw =>
    (Submodule.mem_span_pair.1 hw).elim fun a hab => hab.elim fun b hb => by
      rw [← hb, map_add, map_smul, map_smul, hf₁, hf₂]
  refine mem_leechPre.2 ?_
  rw [phi0_conjQ p t, key _ ht]
  exact ht

abbrev leechN₀ (r₁ r₂ : Q) : Subgroup (leechJ r₁ r₂) :=
  ((leechT (phi0 (coordOf r₁)) (phi0 (coordOf r₂))).map Short.rhoHom).subgroupOf (leechJ r₁ r₂)

theorem leechT_le_leechC {r₁ r₂ : Q} (h : bL (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) = 0) :
    leechT (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) ≤ leechC r₁ r₂ :=
  (leechT_le_leechPerp h).trans (centralizer_inf_eq_leechPre r₁ r₂).symm.le

instance normal_leechN₀ (r₁ r₂ : Q) : (leechN₀ r₁ r₂).Normal :=
  normal_leechRho fun _ hp _ ht => conjQ_mem_leechT hp ht

theorem leechJ_layered_shape
    {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (hne : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂))
    (h12 : bL (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) = 0) :
    HasLayeredTwoShape (leechJ r₁ r₂) 3 20 fun X _ =>
      Nonempty (X ≃* ↥(Kstab (phi0 (coordOf r₁)) ⊓ Kstab (phi0 (coordOf r₂)))) := by
  have h₁ := leech_phi0_ne_zero hr₁
  have h₂ := leech_phi0_ne_zero hr₂
  have hTS := leechT_le_leechC h12
  have : IsElementaryAbelian 2 (leechT (phi0 (coordOf r₁)) (phi0 (coordOf r₂))) :=
    isElementaryAbelian_leechT (leech_qL_phi0_eq_zero hr₁)
      (leech_qL_phi0_eq_zero hr₂) h12
  have hsq : ∀ a : leechN r₁ r₂, a * a ∈ (leechN₀ r₁ r₂).subgroupOf (leechN r₁ r₂) := fun a =>
    (show ((a : leechJ r₁ r₂) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ (leechC r₁ r₂).map Short.rhoHom from
      a.2).elim fun q hq => ⟨q * q, mul_self_mem_leechT _ _ q,
        (map_mul Short.rhoHom q q).trans (congrArg₂ (· * ·) hq.2 hq.2)⟩
  exact ⟨leechN r₁ r₂, normal_leechN r₁ r₂, leechN₀ r₁ r₂, normal_leechN₀ r₁ r₂,
    fun x hx => Subgroup.map_mono hTS hx,
    isElementaryAbelian_of_mulEquiv
      (K := leechT (phi0 (coordOf r₁)) (phi0 (coordOf r₂))) (K' := leechN₀ r₁ r₂)
      (leechRhoEquiv hTS).symm,
    (Nat.card_congr (leechRhoEquiv hTS).toEquiv).trans (natCard_leechT h₁ h₂ hne),
    isElementaryAbelian_two_quotient (N := leechN r₁ r₂) _ hsq, natCard_leechN h₁ h₂ hne,
    ⟨leechQuotEquiv h₁ h₂ hne⟩⟩

end CFSG.Monster.Existence

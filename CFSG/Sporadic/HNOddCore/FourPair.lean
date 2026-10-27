
module

public import CFSG.Sporadic.HNOddCore.FourPairBase

public import CFSG.Sporadic.HNOddCore.FourPairB
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

instance Qbar_normal_inst :
    (Qbar.subgroupOf rho4.range).Normal := Qbar_normal

abbrev Qr :
    Subgroup rho4.range := Qbar.subgroupOf rho4.range

@[expose] def qrEquiv :
    Fin 256 ≃ Qr :=
  qbEquiv.trans (Subgroup.subgroupOfEquivOfLe Qbar_le_range).symm.toEquiv

theorem qrEquiv_val
    (m : Fin 256) : ((qrEquiv m : rho4.range) : Perm (Fin 800)) = qb m := rfl

@[expose] def psiQ :
    MulAut Qr →* Perm (Fin 256) :=
  (Equiv.permCongrHom qrEquiv.symm).toMonoidHom.comp (MulAut.toPerm Qr)

@[expose] def kappa :
    rho4.range →* Perm (Fin 256) := psiQ.comp (MulAut.conjNormal (H := Qr))

theorem kappa_apply
    (x : rho4.range) (m : Fin 256) :
    kappa x m = qrEquiv.symm (MulAut.conjNormal (H := Qr) x (qrEquiv m)) := rfl

theorem kappa_injective_aut :
    Function.Injective psiQ := by
  intro f g h
  have h1 := (Equiv.permCongrHom qrEquiv.symm).injective h
  exact MulEquiv.toEquiv_injective h1

@[expose] def rhoGenR
    (g : Fin 11) : rho4.range := ⟨rhoGen g, rhoGen_mem g.2⟩

theorem closure_rhoGenR :
    Subgroup.closure (Set.range rhoGenR) = ⊤ :=
  closure_preimage_eq_top (fun g : Fin 11 => rhoGen_mem g.2) range_eq_closure_rhoGen

theorem kappa_gen_inv
    (g : Fin 11) : kappa (rhoGenR g)⁻¹ = pk g := by
  apply Equiv.ext
  intro m
  apply Fin.ext
  rw [← prep_pk g.2 m, kappa_apply]
  have hlt := colPerm_lt g.2 m.2
  have e : MulAut.conjNormal (rhoGenR g)⁻¹ (qrEquiv m) = qrEquiv ⟨_, hlt⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_mul, inv_inv, InvMemClass.coe_inv,
      qrEquiv_val, qrEquiv_val, mul_assoc]
    exact colPerm_spec g.2 m.2
  rw [e, Equiv.symm_apply_apply]

theorem kappa_gen
    (g : Fin 11) : kappa (rhoGenR g) = (pk g)⁻¹ := by
  rw [← kappa_gen_inv, map_inv, inv_inv]

theorem card_kappa_range :
    Nat.card kappa.range = 14400 := by
  rw [range_eq_closure kappa closure_rhoGenR]
  have e : Subgroup.closure (Set.range fun g => kappa (rhoGenR g)) =
      Subgroup.closure (Set.range fun g : Fin 11 => pk g) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      show kappa (rhoGenR g) ∈ _
      rw [kappa_gen]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨g, rfl⟩)
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      show pk g ∈ _
      rw [← inv_inv (pk g), ← kappa_gen]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨g, rfl⟩)
  have hO : ∀ k < colPerms.size, PRep 256 colPerms[k]! (pk k) := fun k hk =>
    prep_pk (by rw [← q_parts.2.2.2.1]; exact hk)
  have e2 : Subgroup.closure (Set.range fun g : Fin 11 => pk g) = arrGen 256 colPerms := by
    rw [arrGen_eq hO]
    congr 1
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, by rw [q_parts.2.2.2.1]; exact g.2⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨⟨k, by rw [← q_parts.2.2.2.1]; exact hk⟩, rfl⟩
  rw [e, e2,
    card_arrGen_of_chainCheck (by norm_num) (by decide) q_parts.2.2.2.2.2.2.2.2.2.2.2]
  decide

theorem card_conj_range :
    Nat.card (MulAut.conjNormal (G := rho4.range) (H := Qr)).range = 14400 := by
  rw [← card_kappa_range, kappa, MonoidHom.range_comp,
    Subgroup.card_map_of_injective kappa_injective_aut]

theorem card_Qr :
    Nat.card Qr = 256 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Qbar_le_range).toEquiv, card_Qbar]

theorem Qr_le_ker :
    Qr ≤ (MulAut.conjNormal (G := rho4.range) (H := Qr)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.one_apply]
  apply Subtype.ext
  show (x : Perm (Fin 800)) * ((h : rho4.range) : Perm (Fin 800)) * (x : Perm (Fin 800))⁻¹ =
    ((h : rho4.range) : Perm (Fin 800))
  rw [Qbar_comm (x := (x : Perm (Fin 800))) (y := ((h : rho4.range) : Perm (Fin 800))) hx h.2,
    mul_assoc, mul_inv_cancel, mul_one]

theorem ker_conj :
    (MulAut.conjNormal (G := rho4.range) (H := Qr)).ker = Qr := by
  have h1 := (MulAut.conjNormal (G := rho4.range) (H := Qr)).ker.card_mul_index
  rw [Subgroup.index_ker, card_conj_range, card_rho4_range] at h1
  refine (Subgroup.eq_of_le_of_card_ge Qr_le_ker ?_).symm
  rw [card_Qr]
  omega

theorem centralizer_Qbar :
    Subgroup.centralizer (Qbar : Set (Perm (Fin 800))) ⊓ rho4.range = Qbar := by
  apply le_antisymm
  · rintro x ⟨hc, hr⟩
    have hx : (⟨x, hr⟩ : rho4.range) ∈ Qr := by
      rw [← ker_conj, MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro h
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      apply Subtype.ext
      show x * ((h : rho4.range) : Perm (Fin 800)) * x⁻¹ = ((h : rho4.range) : Perm (Fin 800))
      rw [(Subgroup.mem_centralizer_iff.1 hc ((h : rho4.range) : Perm (Fin 800)) h.2).symm,
        mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  · intro x hx
    refine ⟨Subgroup.mem_centralizer_iff.2 fun y hy => Qbar_comm hy hx, Qbar_le_range hx⟩

abbrev Q4 :
    Subgroup C4 := Qr.comap rho4.rangeRestrict

theorem Q4_normal :
    Q4.Normal := Subgroup.Normal.comap Qbar_normal _

theorem mem_Q4
    {x : C4} : x ∈ Q4 ↔ rho4 x ∈ Qbar := Iff.rfl

theorem card_Q4 :
    Nat.card Q4 = 512 := by
  have hK : rho4.rangeRestrict.ker ≤ Q4 := Subgroup.ker_le_comap _ _
  have h := card_ker_mul_card_map rho4.rangeRestrict hK
  rw [Subgroup.map_comap_eq_self_of_surjective rho4.rangeRestrict_surjective, card_Qr,
    MonoidHom.ker_rangeRestrict, ker_rho4, Nat.card_zpowers, orderOf_t4C] at h
  omega

theorem Q4_isPGroup :
    IsPGroup 2 Q4 := IsPGroup.of_card (n := 9) (by rw [card_Q4]; norm_num)

theorem centralizer_Q4_le :
    Subgroup.centralizer (Q4 : Set C4) ≤ Q4 := by
  intro x hx
  rw [mem_Q4, ← centralizer_Qbar]
  refine ⟨Subgroup.mem_centralizer_iff.2 fun q hq => ?_, ⟨x, rfl⟩⟩
  obtain ⟨y, hy⟩ := Qbar_le_range hq
  have hyQ : y ∈ Q4 := by
    rw [mem_Q4, hy]
    exact hq
  have := Subgroup.mem_centralizer_iff.1 hx y hyQ
  rw [← hy, ← map_mul, ← map_mul, this]

@[expose] def fixPt4
    (k : Fin 800) : X := hF4.pt ((finCongr f4_size).symm k)

theorem fixPt4_injective :
    Function.Injective fixPt4 := fun _ _ h =>
  (finCongr f4_size).symm.injective (hF4.pt_injective h)

theorem fix_t4_iff
    (y : X) : jR t4J • y = y ↔ ∃ k : Fin 800, fixPt4 k = y := by
  rw [fix_t4]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨finCongr f4_size k, by rw [fixPt4, Equiv.symm_apply_apply]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, rfl⟩

theorem ctuc_hn_four_pair_self_centralizing_two_subgroup :
    Function.Injective fixPt4 ∧ (∀ y : X, jR t4J • y = y ↔ ∃ k : Fin 800, fixPt4 k = y) ∧
    (∀ (x : C4) (k : Fin 800), fixPt4 (rho4 x k) = (x : RH) • fixPt4 k) ∧
    rho4.ker = Subgroup.zpowers t4C ∧ Nat.card rho4.range = 3686400 ∧
    (∀ i < 8, qbar i ∈ rho4.range) ∧ Qbar ≤ rho4.range ∧ (Qbar.subgroupOf rho4.range).Normal ∧
    (∀ x ∈ Qbar, ∀ y ∈ Qbar, x * y = y * x) ∧ (∀ x ∈ Qbar, x ^ 2 = 1) ∧ Nat.card Qbar = 256 ∧
    Nat.card (MulAut.conjNormal (G := rho4.range) (H := Qbar.subgroupOf rho4.range)).range =
      14400 ∧
    Subgroup.centralizer (Qbar : Set (Perm (Fin 800))) ⊓ rho4.range = Qbar ∧
    Q4.Normal ∧ Nat.card Q4 = 512 ∧ IsPGroup 2 Q4 ∧ Subgroup.centralizer (Q4 : Set C4) ≤ Q4 :=
  ⟨fixPt4_injective, fix_t4_iff, pt_rho4, ker_rho4, card_rho4_range,
    fun _ hi => qbar_mem_range hi, Qbar_le_range, Qbar_normal, fun _ hx _ hy => Qbar_comm hx hy,
    fun _ hx => Qbar_sq hx, card_Qbar, card_conj_range, centralizer_Qbar, Q4_normal, card_Q4,
    Q4_isPGroup, centralizer_Q4_le⟩

end CFSG.Sporadic.HNOddCore

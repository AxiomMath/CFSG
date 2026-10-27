
module

public import CFSG.Monster.B.TwoA.Base.FourNormBase
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

@[expose] def wvEquiv {a b : L2} (h : a = b) : Wv a ≃ₗ[ZMod 2] Wv b := by
  subst h
  exact LinearEquiv.refl _ _

theorem wvEquiv_mk {a b : L2} (h : a = b) (x : vPerpL a) :
    wvEquiv h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(x : L2), by subst h; exact x.2⟩ := by
  subst h
  rfl

theorem wvEquiv_wAct {a b : L2} (h : a = b) (k : Kstab a) (x : Wv a) :
    wvEquiv h (wAct a k x) = wAct b ⟨k, by subst h; exact k.2⟩ (wvEquiv h x) := by
  subst h
  rfl

theorem qW_wvEquiv {a b : L2} (h : a = b) (ha : qL a = 0) (hb : qL b = 0) (x : Wv a) :
    qW b hb (wvEquiv h x) = qW a ha x := by
  subst h
  rfl

theorem polar_wvEquiv {a b : L2} (h : a = b) (ha : qL a = 0) (hb : qL b = 0) (x y : Wv a) :
    QuadraticMap.polarBilin (qW b hb) (wvEquiv h x) (wvEquiv h y) =
      QuadraticMap.polarBilin (qW a ha) x y := by
  subst h
  rfl

theorem hv0 : phi0 (coordOf rStar) = v0 := phi0_coordOf_rStar

theorem qL_v0 : qL v0 = 0 := Griess.qL_classOf_minVecs vMinus_zero_one_mem

noncomputable abbrev qV : QuadraticForm (ZMod 2) (Wv v0) := qW v0 qL_v0

noncomputable abbrev bV : LinearMap.BilinForm (ZMod 2) (Wv v0) := QuadraticMap.polarBilin qV

theorem bV_nondegenerate : bV.Nondegenerate := polarBilin_qW_nondegenerate v0_ne_zero qL_v0

theorem bV_comm (x y : Wv v0) : bV x y = bV y x := QuadraticMap.polar_comm _ x y

theorem bV_self
    (x : Wv v0) : bV x x = 0 := by
  change QuadraticMap.polar qV x x = 0
  rw [QuadraticMap.polar_self]
  exact (by decide : ∀ t : ZMod 2, 2 • t = 0) _

theorem qV_add (x y : Wv v0) : qV (x + y) = qV x + qV y + bV x y := by
  change qV (x + y) = qV x + qV y + QuadraticMap.polar qV x y
  rw [QuadraticMap.polar]
  ring

@[expose] def jhatToKv0 : Jhat →* Kstab v0 :=
  (MulEquiv.subgroupCongr Kstab_rStar_eq).toMonoidHom.comp jhatToKv

theorem coe_jhatToKv0 (g : Jhat) : ((jhatToKv0 g : Kstab v0) : OLq) = (jhatToKv g : OLq) := rfl

theorem jhatToKv0_surjective :
    Function.Surjective jhatToKv0 := by
  rw [jhatToKv0, MonoidHom.coe_comp]
  exact (MulEquiv.surjective _).comp jhatToKv_surjective

theorem jhatToKv0_eq_one_iff (g : Jhat) : jhatToKv0 g = 1 ↔ jhatToKv g = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    have h1 : ((jhatToKv0 g : Kstab v0) : OLq) = 1 := congrArg Subtype.val h
    exact h1
  · intro h
    apply Subtype.ext
    have h1 : ((jhatToKv g : Kstab (phi0 (coordOf rStar))) : OLq) = 1 := congrArg Subtype.val h
    exact h1

theorem ker_jhatToKv0 : jhatToKv0.ker = Ehat.subgroupOf Jhat := by
  ext g
  rw [MonoidHom.mem_ker, jhatToKv0_eq_one_iff, ← MonoidHom.mem_ker, ker_jhatToKv]

theorem jhatToKv0_jhatEquiv (g : Jbar) :
    ((jhatToKv0 (jhatEquiv g) : Kstab v0) : OLq) = (jbarToKv g : OLq) := by
  rw [coe_jhatToKv0, jhatToKv_jhatEquiv]

theorem jhatToKv0_eq_one_of_mem_Ehat {g : Dfull} (hg : g ∈ Jhat) (he : g ∈ Ehat) :
    jhatToKv0 ⟨g, hg⟩ = 1 := by
  rw [← MonoidHom.mem_ker, ker_jhatToKv0, Subgroup.mem_subgroupOf]
  exact he

@[expose] def ehatEquiv : Ebar ≃* Ehat := Ebar.equivMapOfInjective iotaD iotaD_injective

theorem coe_ehatEquiv (e : Ebar) : (ehatEquiv e : Dfull) = iotaD e := rfl

@[expose] def psiE : Ehat →* Multiplicative (Wv v0) :=
  (AddEquiv.toMultiplicative (wvEquiv hv0).toAddEquiv).toMonoidHom.comp
    (psiBar.comp ehatEquiv.symm.toMonoidHom)

@[expose] def psiW (e : Ehat) : Wv v0 := Multiplicative.toAdd (psiE e)

theorem psiW_ehatEquiv (e : Ebar) :
    psiW (ehatEquiv e) = wvEquiv hv0 (Multiplicative.toAdd (psiBar e)) := by
  change wvEquiv hv0 (Multiplicative.toAdd (psiBar (ehatEquiv.symm (ehatEquiv e)))) = _
  rw [MulEquiv.symm_apply_apply]

theorem psiW_mul (e e' : Ehat) : psiW (e * e') = psiW e + psiW e' := by
  rw [psiW, map_mul, toAdd_mul]
  rfl

theorem psiW_one : psiW 1 = 0 := by
  rw [psiW, map_one, toAdd_one]

theorem psiW_inv (e : Ehat) : psiW e⁻¹ = -psiW e := by
  rw [psiW, map_inv, toAdd_inv]
  rfl

theorem psiE_surjective : Function.Surjective psiE := by
  rw [psiE, MonoidHom.coe_comp, MonoidHom.coe_comp]
  exact (MulEquiv.surjective _).comp (psiBar_surjective.comp ehatEquiv.symm.surjective)

theorem psiW_surjective : Function.Surjective psiW := fun x => by
  obtain ⟨e, he⟩ := psiE_surjective (Multiplicative.ofAdd x)
  exact ⟨e, by rw [psiW, he, toAdd_ofAdd]⟩

theorem xhat_mem_Ehat : xhat ∈ Ehat := ⟨xbar, xbar_mem_Ebar, rfl⟩

@[expose] def xhatE : Ehat := ⟨xhat, xhat_mem_Ehat⟩

theorem xhatE_eq : xhatE = ehatEquiv ⟨xbar, xbar_mem_Ebar⟩ := rfl

theorem psiW_eq_zero_iff (e : Ehat) : psiW e = 0 ↔ e = 1 ∨ e = xhatE := by
  obtain ⟨e₀, rfl⟩ := ehatEquiv.surjective e
  rw [psiW_ehatEquiv, LinearEquiv.map_eq_zero_iff, toAdd_eq_zero, psiBar_eq_one_iff, xhatE_eq,
    EmbeddingLike.map_eq_one_iff, (EquivLike.injective ehatEquiv).eq_iff]

theorem psiW_xhatE : psiW xhatE = 0 := (psiW_eq_zero_iff _).2 (.inr rfl)

theorem orderOf_xhatE : orderOf xhatE = 2 := by
  rw [← orderOf_injective Ehat.subtype Subtype.coe_injective xhatE]
  exact orderOf_xhat

theorem ker_psiE : psiE.ker = Subgroup.zpowers xhatE := by
  ext e
  rw [MonoidHom.mem_ker, Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xhatE,
    ← psiW_eq_zero_iff, psiW, toAdd_eq_zero]

theorem natCard_ker_psiE : Nat.card psiE.ker = 2 := by
  rw [ker_psiE, Nat.card_zpowers, orderOf_xhatE]

theorem psiW_conj {g e : Dfull} (hg : g ∈ Jhat) (he : e ∈ Ehat) :
    psiW ⟨g⁻¹ * e * g, conj_mem_Ehat hg he⟩ = wAct v0 (jhatToKv0 ⟨g, hg⟩) (psiW ⟨e, he⟩) := by
  have hg' := hg
  rw [Jhat_eq_map] at hg'
  obtain ⟨g₀, hg₀, rfl⟩ := hg'
  obtain ⟨e₀, he₀, rfl⟩ := he
  have h1 : (⟨(iotaD g₀)⁻¹ * iotaD e₀ * iotaD g₀, conj_mem_Ehat hg ⟨e₀, he₀, rfl⟩⟩ : Ehat) =
      ehatEquiv ⟨g₀⁻¹ * e₀ * g₀, conj_mem_Ebar hg₀ he₀⟩ :=
    Subtype.ext (by rw [coe_ehatEquiv, map_mul, map_mul, map_inv])
  have h2 : (⟨iotaD e₀, ⟨e₀, he₀, rfl⟩⟩ : Ehat) = ehatEquiv ⟨e₀, he₀⟩ := rfl
  have h3 : (⟨iotaD g₀, hg⟩ : Jhat) = jhatEquiv ⟨g₀, hg₀⟩ := rfl
  rw [h1, h2, h3, psiW_ehatEquiv, psiW_ehatEquiv, psiBar_conj hg₀ he₀, toAdd_ofAdd, wvEquiv_wAct]
  congr 2
  exact Subtype.ext (jhatToKv0_jhatEquiv ⟨g₀, hg₀⟩).symm

theorem iotaD_xbar_pow (n : ℕ) : iotaD (xbar ^ n) = xhat ^ n := by
  rw [map_pow, iotaD_xbar]

theorem Ehat_comm (e e' : Ehat) :
    (e : Dfull) * e' = e' * e * xhat ^ (bV (psiW e) (psiW e')).val := by
  obtain ⟨e₀, rfl⟩ := ehatEquiv.surjective e
  obtain ⟨e₀', rfl⟩ := ehatEquiv.surjective e'
  have hb : bV (psiW (ehatEquiv e₀)) (psiW (ehatEquiv e₀')) =
      bW (Multiplicative.toAdd (psiBar e₀)) (Multiplicative.toAdd (psiBar e₀')) := by
    rw [psiW_ehatEquiv, psiW_ehatEquiv]
    exact polar_wvEquiv hv0 qL_phi0_coordOf_rStar qL_v0 _ _
  have h := congrArg iotaD (Ebar_mul_eq_mul_xbar_pow e₀ e₀')
  rw [map_mul, map_mul, map_mul, iotaD_xbar_pow] at h
  rw [hb]
  exact h

theorem Ehat_mul_self (e : Ehat) (h : qV (psiW e) = 0) : (e : Dfull) * e = 1 := by
  obtain ⟨e₀, rfl⟩ := ehatEquiv.surjective e
  obtain ⟨q, hq, rfl⟩ := exists_rep_Ebar e₀
  rw [psiW_ehatEquiv, qW_wvEquiv hv0 qL_phi0_coordOf_rStar qL_v0, psiBar_kappa_rho hq,
    toAdd_ofAdd, qW_mk] at h
  have hqq : q * q = 1 := (mul_self_eq_one_iff_qL q).2 h
  have e2 : (⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ : Cgen) * ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ =
      1 := Subtype.ext (by
        rw [Subgroup.coe_mul, ← rhoEquiv_mul, hqq, OneMemClass.coe_one, rhoEquiv_one'])
  change iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) *
    iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) = 1
  rw [← map_mul, ← map_mul, e2, map_one, map_one]

theorem yhat_mem_Ehat :
    yhat ∈ Ehat := ⟨zbar, zbar_mem_Ebar, rfl⟩

@[expose] def yhatE :
    Ehat := ⟨yhat, yhat_mem_Ehat⟩

theorem psiW_yhat :
    psiW yhatE = wFr := by
  have e : yhatE = ehatEquiv ⟨zbar, zbar_mem_Ebar⟩ := rfl
  rw [e, psiW_ehatEquiv, psiBar_zbar, toAdd_ofAdd, wvEquiv_mk, wFr, fPerp]

@[expose] def dbar (i j : Fin 24) : Cbar :=
  kappa ⟨rhoEquiv (rMinus i j), rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩

theorem dbar_mem_Ebar (i j : Fin 24) : dbar i j ∈ Ebar :=
  kappa_rho_mem_Ebar (DQ_mem_centralizer _)

@[expose] def dhat (i j : Fin 24) : Dfull := iotaD (dbar i j)

theorem dhat_mem_Ehat (i j : Fin 24) : dhat i j ∈ Ehat := ⟨dbar i j, dbar_mem_Ebar i j, rfl⟩

@[expose] def dhatE (i j : Fin 24) : Ehat := ⟨dhat i j, dhat_mem_Ehat i j⟩

theorem psiW_dhat
    {i j : Fin 24} (hij : i < j) (h : OffPair i j) :
    psiW (dhatE i j) = pairW i j h 0 := by
  have e : dhatE i j = ehatEquiv ⟨dbar i j, dbar_mem_Ebar i j⟩ := rfl
  rw [e, psiW_ehatEquiv]
  have e2 := psiBar_kappa_rho (DQ_mem_centralizer (deltaPair i j))
  change wvEquiv hv0 (Multiplicative.toAdd (psiBar ⟨kappa ⟨rhoEquiv (DQ (deltaPair i j)),
    rhoEquiv_mem_Cgen (DQ_mem_centralizer (deltaPair i j))⟩,
    kappa_rho_mem_Ebar (DQ_mem_centralizer (deltaPair i j))⟩)) = _
  rw [e2, toAdd_ofAdd, wvEquiv_mk, pairW]
  congr 1
  apply Subtype.ext
  change phi0 (coordOf (rMinus i j)) = pairCls i j 0
  rw [phi0_coordOf_rMinus hij, pairCls, pairVec_zero]

theorem tauhat_mul_dhat (i j : Fin 24) : tauhat * dhat i j = dhat i j * tauhat := by
  rw [tauhat, dhat, dbar, taubar, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  change tauB * rhoEquiv (DQ (deltaPair i j)) = rhoEquiv (DQ (deltaPair i j)) * tauB
  exact (hCocode_mul_tauB_even (CFSG.Monster.B.pair_ΩC_deltaPair i j)).symm

theorem xhat_comm_of_mem_Jhat
    {g : Dfull} (hg : g ∈ Jhat) : g * xhat = xhat * g := by
  rw [← centralizer_xhat] at hg
  exact Subgroup.mem_centralizer_singleton_iff.1 hg

theorem xhat_mul_self : xhat * xhat = 1 := by
  rw [← iotaD_xbar, ← map_mul, xbar_mul_self, map_one]

end CFSG.Monster.B.TwoA

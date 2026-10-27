module

public import CFSG.Quasithin.H13.A6S1372SixteenThree
public import CFSG.Quasithin.H13.A6S1372SixteenC1

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6Real

variable {V W : Type} [CommGroup V] [CommGroup W] {p : V →* W} {X : Subgroup (MulAut V)}
  {Y : Subgroup (MulAut W)}

theorem eq_of_corr (hfX : ∀ x ∈ X, (∀ v, p (x v) = p v) → x = 1) {x x' : MulAut V}
    (hx : x ∈ X) (hx' : x' ∈ X) {y : MulAut W} (h : ∀ v, p (x v) = y (p v))
    (h' : ∀ v, p (x' v) = y (p v)) : x = x' := by
  have hinv : ∀ v, p (x'⁻¹ v) = y⁻¹ (p v) := by
    intro v
    have h1 := h' (x'⁻¹ v)
    rw [MulAut.apply_inv_self] at h1
    rw [h1, MulAut.inv_apply_self]
  have h1 : x'⁻¹ * x = 1 := hfX _ (X.mul_mem (X.inv_mem hx') hx) fun v => by
    rw [MulAut.mul_apply, hinv, h, MulAut.inv_apply_self]
  calc x = x' * (x'⁻¹ * x) := by group
    _ = x' := by rw [h1, mul_one]

theorem exists_hom (hXY : ∀ x ∈ X, ∃ y ∈ Y, ∀ v, p (x v) = y (p v))
    (hYX : ∀ y ∈ Y, ∃ x ∈ X, ∀ v, p (x v) = y (p v))
    (hfX : ∀ x ∈ X, (∀ v, p (x v) = p v) → x = 1) :
    ∃ φ : ↥Y →* ↥X, Function.Surjective φ ∧
      ∀ (y : ↥Y) (v : V), p ((φ y : MulAut V) v) = (y : MulAut W) (p v) := by
  classical
  choose f hf hfc using hYX
  refine ⟨{ toFun := fun y => ⟨f y y.2, hf y y.2⟩, map_one' := ?_, map_mul' := ?_ }, ?_,
    fun y v => hfc y y.2 v⟩
  · apply Subtype.ext
    exact eq_of_corr hfX (hf 1 _) X.one_mem (hfc 1 _) fun _ => rfl
  · intro a b
    apply Subtype.ext
    refine eq_of_corr hfX (hf _ _) (X.mul_mem (hf a a.2) (hf b b.2)) (hfc _ _) fun v => ?_
    show p (f a a.2 (f b b.2 v)) = (a : MulAut W) ((b : MulAut W) (p v))
    rw [hfc a a.2, hfc b b.2]
  · intro x
    obtain ⟨y, hy, hxy⟩ := hXY x x.2
    exact ⟨⟨y, hy⟩, Subtype.ext (eq_of_corr hfX (hf y hy) x.2 (hfc y hy) hxy)⟩

theorem apply_mem_commV {x : MulAut V} (hx : x ∈ X) {u : V} (hu : u ∈ commV X) :
    x u ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_mem hx hu

theorem realizesVia_of_map [Group.IsPerfect ↥X] (hp : Function.Surjective p)
    (hXY : ∀ x ∈ X, ∃ y ∈ Y, ∀ v, p (x v) = y (p v)) (hker : ∀ x ∈ X, ∀ v, p v = 1 → x v = v)
    {φ : ↥Y →* ↥X} (hφs : Function.Surjective φ)
    (hφ : ∀ (y : ↥Y) (v : V), p ((φ y : MulAut V) v) = (y : MulAut W) (p v))
    {D : FFModel} {π : D.Gam →* ↥Y} (h : D.RealizesVia Y (commV Y) (fixV Y ⊓ commV Y) π) :
    D.RealizesVia X (commV X) (fixV X ⊓ commV X) (φ.comp π) := by
  obtain ⟨hπ, -, hkersec, -, -, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  have hYX : ∀ y ∈ Y, ∃ x ∈ X, ∀ v, p (x v) = y (p v) := fun y hy =>
    ⟨_, (φ ⟨y, hy⟩).2, hφ ⟨y, hy⟩⟩
  have hmap := A6Three.map_commV hp hXY hYX
  have hpU : ∀ u ∈ commV X, p u ∈ commV Y := fun u hu => by
    rw [← hmap]
    exact ⟨u, hu, rfl⟩
  let q : ↥(commV X) →* ↥(commV Y) :=
    (p.comp (commV X).subtype).codRestrict (commV Y) fun u => hpU u u.2
  have hq : ∀ u : ↥(commV X), ((q u : ↥(commV Y)) : W) = p u := fun _ => rfl
  refine ⟨hφs.comp hπ, inf_le_right, hkersec, fun x u hu => apply_mem_commV x.2 hu,
    fun x z hz => ?_, hsec, hkerinv, β.comp q, ?_, ?_, ?_⟩
  · rw [hz.1 x x.2]
    exact hz
  · intro t
    obtain ⟨w, rfl⟩ := hβs t
    have hw : (w : W) ∈ (commV X).map p := by rw [hmap]; exact w.2
    obtain ⟨u, hu, hpu⟩ := hw
    exact ⟨⟨u, hu⟩, by rw [MonoidHom.comp_apply]; exact congrArg β (Subtype.ext hpu)⟩
  · intro u
    rw [MonoidHom.comp_apply, hβk, hq]
    constructor
    · intro hu
      exact ⟨A6Three.mem_fixV_of_map hXY hker hu.1, u.2⟩
    · intro hu
      refine ⟨fun y hy => ?_, hpU _ u.2⟩
      obtain ⟨x, hx, hxy⟩ := hYX y hy
      rw [← hxy, hu.1 x hx]
  · intro γ u m hu hm hum
    have hu' : ((π γ : ↥Y) : MulAut W) ((q u : ↥(commV Y)) : W) ∈ commV Y := by
      rw [hq, ← hφ]
      exact hpU _ hu
    have h1 := hβe γ (q u) m hu' hm hum
    rw [MonoidHom.comp_apply, ← h1]
    congr 1
    apply Subtype.ext
    rw [hq]
    exact hφ (π γ) u

theorem realizes_of_map [Group.IsPerfect ↥X] (hp : Function.Surjective p)
    (hXY : ∀ x ∈ X, ∃ y ∈ Y, ∀ v, p (x v) = y (p v))
    (hYX : ∀ y ∈ Y, ∃ x ∈ X, ∀ v, p (x v) = y (p v)) (hker : ∀ x ∈ X, ∀ v, p v = 1 → x v = v)
    (hfX : ∀ x ∈ X, (∀ v, p (x v) = p v) → x = 1) {D : FFModel}
    (h : D.Realizes Y (commV Y) (fixV Y ⊓ commV Y)) :
    D.Realizes X (commV X) (fixV X ⊓ commV X) := by
  obtain ⟨φ, hφs, hφ⟩ := exists_hom hXY hYX hfX
  obtain ⟨π, hπ⟩ := h
  exact ⟨_, realizesVia_of_map hp hXY hker hφs hφ hπ⟩

end A6Real

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section KTilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

omit hab in
theorem KData.realizes_tilde_of_plus (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) (hLem : Lem1374One) (h1352 : Stmt13_5_2) (h51 : AsB51)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K) {D : FFModel}
    (hD : D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))) :
    D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hHV := S.le_normalizer_UV1 hH
  have hKU := hK.le_centralizer_U0 hNS h13315 h1356two hH hhat hNU hna h13314 hLem h1352 h51 hab
  have hV1C : (fsuV1 T V).subgroupOf (conjClosure S.V3 H) ≤
      (Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H) :=
    fun x hx => S.V1_le_centralizer_QH hNS h13315 h1356two hH hx
  set p := QuotientGroup.map
    (((fsuV1 T V).subgroupOf (conjClosure S.V3 H)).subgroupOf ⊤)
    (((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)).subgroupOf ⊤)
    (MonoidHom.id _) (fun x hx => hV1C hx) with hp
  have hpmk : ∀ u : ↥(conjClosure S.V3 H),
      p (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))
            u := fun _ => rfl
  have hpeq : ∀ (h : ↥H)
      (x : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      p (A6Mod.secAct hHU hHV h x) = A6Mod.secAct hHU hHC h (p x) := by
    intro h x
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ x
    rfl
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ y
    exact ⟨_, hpmk u⟩
  have hperf : Group.IsPerfect ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    (hK.isQuasisimple_tilde hNS h13315 h1356two hH hab hhat hNU hLem).1
  refine A6Real.realizes_of_map hpsurj ?_ ?_ ?_ ?_ hD
  · intro x hx
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    exact ⟨_, (A6Mod.mem_autSec_iff hHU hHC hKH).2 ⟨k, hkK, rfl⟩, hpeq k⟩
  · intro y hy
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hKH).1 hy
    exact ⟨_, (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨k, hkK, rfl⟩, hpeq k⟩
  ·
    intro x hx v hv
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ v
    rw [hpmk, A6Mod.secMk_eq_one_iff] at hv
    rw [A6Mod.secAct_secMk]
    congr 1
    apply Subtype.ext
    rw [Setup.rho_apply_coe]
    have hc := Subgroup.mem_centralizer_iff.mp (hKU hkK) (u : G) ⟨u.2, hv⟩
    rw [← hc, mul_inv_cancel_right]
  ·
    intro x hx hfix
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    have h1 : A6Mod.secAct hHU hHC k = 1 := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := hpsurj y
      rw [← hpeq, hfix]
      rfl
    rw [← MonoidHom.mem_ker, S.ker_secAct_plus hNS h13315 h1356two hH hab hNU hhat hLem] at h1
    rw [← MonoidHom.mem_ker, S.ker_secAct_tilde hNS h13315 h1356two hH]
    exact h1

end Conf

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6

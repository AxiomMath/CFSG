module

public import CFSG.RankThree.CentralLiftU.UnitaryLift

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.CentralExt (sl2Lift comp_sl2Lift_of_exists)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W sl2ConjDiag
  coe_sl2Diag coe_sl2W coe_sl2ConjDiag sl2W_mul_sl2W sl2ConjDiag_inv_sl2W
  sl2ConjDiag_neg_one_sl2W)
open CFSG.RankThree.CentralLift.LinearRoots (swapSL sl2ConjDiag_sl2Diag swapSL_sl2Diag
  sl2ConjDiag_one)
open CFSG.LieType.Steinberg (perfectLift comp_perfectLift_of_exists)
open scoped Matrix

section Unique

variable {E G : Type*} [Group E] [Group G] {π : E →* G}

theorem comp_sl2Lift_of_unique {k : Type*} [Field k] {α : SpecialLinearGroup (Fin 2) k →* G}
    (hα : ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α) : π.comp (sl2Lift π α) = α :=
  comp_sl2Lift_of_exists hα.exists

theorem map_sl2Lift_of_unique {k : Type*} [Field k] {α : SpecialLinearGroup (Fin 2) k →* G}
    (hα : ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α)
    (g : SpecialLinearGroup (Fin 2) k) : π (sl2Lift π α g) = α g :=
  DFunLike.congr_fun (comp_sl2Lift_of_unique hα) g

theorem eq_sl2Lift_of_unique {k : Type*} [Field k] {α : SpecialLinearGroup (Fin 2) k →* G}
    (hα : ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α)
    {β : SpecialLinearGroup (Fin 2) k →* E} (hβ : π.comp β = α) : β = sl2Lift π α :=
  hα.unique hβ (comp_sl2Lift_of_unique hα)

theorem conj_sl2Lift_of_unique {k : Type*} [Field k]
    (hk : ∀ α : SpecialLinearGroup (Fin 2) k →* G,
      ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α)
    (α : SpecialLinearGroup (Fin 2) k →* G) (e : E) (g : SpecialLinearGroup (Fin 2) k) :
    e * sl2Lift π α g * e⁻¹ = sl2Lift π ((MulAut.conj (π e)).toMonoidHom.comp α) g := by
  have h1 := eq_sl2Lift_of_unique (hk ((MulAut.conj (π e)).toMonoidHom.comp α))
    (β := (MulAut.conj e).toMonoidHom.comp (sl2Lift π α)) (by
      ext x
      change π (e * sl2Lift π α x * e⁻¹) = π e * α x * (π e)⁻¹
      rw [map_mul, map_mul, map_inv, map_sl2Lift_of_unique (hk α)])
  exact DFunLike.congr_fun h1 g

theorem sl2Lift_comp_of_unique {k k' : Type*} [Field k] [Field k']
    (hk : ∀ α : SpecialLinearGroup (Fin 2) k →* G,
      ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α)
    (hk' : ∀ α : SpecialLinearGroup (Fin 2) k' →* G,
      ∃! β : SpecialLinearGroup (Fin 2) k' →* E, π.comp β = α)
    (α : SpecialLinearGroup (Fin 2) k →* G)
    (β : SpecialLinearGroup (Fin 2) k' →* SpecialLinearGroup (Fin 2) k) :
    (sl2Lift π α).comp β = sl2Lift π (α.comp β) :=
  eq_sl2Lift_of_unique (hk' _) (by rw [← MonoidHom.comp_assoc, comp_sl2Lift_of_unique (hk α)])

theorem commute_sl2Lift_of_unique {k k' : Type*} [Field k] [Field k']
    (hk : ∀ α : SpecialLinearGroup (Fin 2) k →* G,
      ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α)
    (hk' : ∀ α : SpecialLinearGroup (Fin 2) k' →* G,
      ∃! β : SpecialLinearGroup (Fin 2) k' →* E, π.comp β = α)
    (α : SpecialLinearGroup (Fin 2) k →* G) (α' : SpecialLinearGroup (Fin 2) k' →* G)
    (hαα' : ∀ g g', Commute (α g) (α' g')) (g : SpecialLinearGroup (Fin 2) k)
    (g' : SpecialLinearGroup (Fin 2) k') : Commute (sl2Lift π α g) (sl2Lift π α' g') := by
  have hc : (MulAut.conj (π (sl2Lift π α g))).toMonoidHom.comp α' = α' := by
    ext x
    change π (sl2Lift π α g) * α' x * (π (sl2Lift π α g))⁻¹ = α' x
    rw [map_sl2Lift_of_unique (hk α), (hαα' g x).eq, mul_inv_cancel_right]
  have h1 := conj_sl2Lift_of_unique hk' α' (sl2Lift π α g) g'
  rw [hc] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

variable {H : Type*} [Group H]

theorem comp_perfectLift_of_unique {α : H →* G} (hα : ∃! β : H →* E, π.comp β = α) :
    π.comp (perfectLift π α) = α :=
  comp_perfectLift_of_exists hα.exists

theorem map_perfectLift_of_unique {α : H →* G} (hα : ∃! β : H →* E, π.comp β = α) (x : H) :
    π (perfectLift π α x) = α x :=
  DFunLike.congr_fun (comp_perfectLift_of_unique hα) x

theorem eq_perfectLift_of_unique {α : H →* G} (hα : ∃! β : H →* E, π.comp β = α)
    {β : H →* E} (hβ : π.comp β = α) : β = perfectLift π α :=
  hα.unique hβ (comp_perfectLift_of_unique hα)

theorem conj_perfectLift_of_unique (hH : ∀ α : H →* G, ∃! β : H →* E, π.comp β = α)
    (α : H →* G) (e : E) (x : H) :
    e * perfectLift π α x * e⁻¹ = perfectLift π ((MulAut.conj (π e)).toMonoidHom.comp α) x := by
  have h1 := eq_perfectLift_of_unique (hH ((MulAut.conj (π e)).toMonoidHom.comp α))
    (β := (MulAut.conj e).toMonoidHom.comp (perfectLift π α)) (by
      ext y
      change π (e * perfectLift π α y * e⁻¹) = π e * α y * (π e)⁻¹
      rw [map_mul, map_mul, map_inv, map_perfectLift_of_unique (hH α)])
  exact DFunLike.congr_fun h1 x

end Unique

namespace Gen

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r ε : ℕ}

structure LiftHyp {R : Type*} [Group R] (π : R →* hypSU h r ε) : Prop where
  sl2K : ∀ α : SpecialLinearGroup (Fin 2) K →* hypSU h r ε,
    ∃! β : SpecialLinearGroup (Fin 2) K →* R, π.comp β = α
  sl2F : ∀ α : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h r ε,
    ∃! β : SpecialLinearGroup (Fin 2) h.fixedField →* R, π.comp β = α
  su3 : ∀ α : gramSU h (gramJ3 K) →* hypSU h r ε,
    ∃! β : gramSU h (gramJ3 K) →* R, π.comp β = α

section Basic

variable {R : Type*} [Group R] {π : R →* hypSU h r ε} (hS : LiftHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem pi_rhoLift {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) K) :
    π (rhoLift h π hij g) = rhoU h hij g := by
  exact map_sl2Lift_of_unique (hS.sl2K _) g

theorem pi_iotaLift (k : Fin r) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    π (iotaLift h π hc hc0 k g) = iotaU h hc hc0 k g := by
  exact map_sl2Lift_of_unique (hS.sl2F _) g

theorem pi_vRho {i j : Fin r} (hij : i ≠ j) : π (vRho h π hij) = rhoU h hij sl2W :=
  pi_rhoLift h hS hij sl2W

theorem pi_vIota (k : Fin r) : π (vIota h π hc hc0 k) = iotaU h hc hc0 k sl2W :=
  pi_iotaLift h hS hc hc0 k sl2W

theorem coe_pi_hRho {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    ((π (hRho h π hij t) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (rhoDiag h i j t) := by
  rw [hRho, MonoidHom.comp_apply, pi_rhoLift h hS]
  exact coe_rhoU_sl2Diag h hij t

theorem coe_pi_hIota (k : Fin r) (b : h.fixedFieldˣ) :
    ((π (hIota h π hc hc0 k b) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal (iotaDiag h k b) := by
  rw [hIota, MonoidHom.comp_apply, pi_iotaLift h hS]
  exact coe_iotaU_sl2Diag h hc hc0 k b

theorem conj_rhoLift_of {e : R} {k l k' l' : Fin r} (hkl : k ≠ l) (hkl' : k' ≠ l')
    {γ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K}
    (hγ : (MulAut.conj (π e)).toMonoidHom.comp (rhoU h hkl) = (rhoU h hkl').comp γ)
    (g : SpecialLinearGroup (Fin 2) K) :
    e * rhoLift h π hkl g * e⁻¹ = rhoLift h π hkl' (γ g) := by
  rw [rhoLift, conj_sl2Lift_of_unique hS.sl2K, hγ, ← sl2Lift_comp_of_unique hS.sl2K hS.sl2K]
  rfl

theorem conj_iotaLift_of {e : R} {k k' : Fin r}
    {γ : SpecialLinearGroup (Fin 2) h.fixedField →* SpecialLinearGroup (Fin 2) h.fixedField}
    (hγ : (MulAut.conj (π e)).toMonoidHom.comp (iotaU h hc hc0 k) =
      (iotaU h hc hc0 k').comp γ) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    e * iotaLift h π hc hc0 k g * e⁻¹ = iotaLift h π hc hc0 k' (γ g) := by
  rw [iotaLift, conj_sl2Lift_of_unique hS.sl2F, hγ, ← sl2Lift_comp_of_unique hS.sl2F hS.sl2F]
  rfl

theorem commute_rhoLift_rhoLift {i j k l : Fin r} (hij : i ≠ j) (hkl : k ≠ l)
    (hcomm : ∀ g g', Commute (rhoU (ε := ε) h hij g) (rhoU h hkl g'))
    (g g' : SpecialLinearGroup (Fin 2) K) :
    Commute (rhoLift h π hij g) (rhoLift h π hkl g') := by
  exact commute_sl2Lift_of_unique hS.sl2K hS.sl2K _ _ hcomm g g'

theorem commute_rhoLift_iotaLift {i j : Fin r} (hij : i ≠ j) (k : Fin r)
    (hcomm : ∀ g g', Commute (rhoU (ε := ε) h hij g) (iotaU h hc hc0 k g'))
    (g : SpecialLinearGroup (Fin 2) K) (g' : SpecialLinearGroup (Fin 2) h.fixedField) :
    Commute (rhoLift h π hij g) (iotaLift h π hc hc0 k g') := by
  exact commute_sl2Lift_of_unique hS.sl2K hS.sl2F _ _ hcomm g g'

theorem commute_iotaLift_iotaLift (k l : Fin r)
    (hcomm : ∀ g g', Commute (iotaU (ε := ε) h hc hc0 k g) (iotaU h hc hc0 l g'))
    (g g' : SpecialLinearGroup (Fin 2) h.fixedField) :
    Commute (iotaLift h π hc hc0 k g) (iotaLift h π hc hc0 l g') := by
  exact commute_sl2Lift_of_unique hS.sl2F hS.sl2F _ _ hcomm g g'

theorem rhoLift_swap {i j : Fin r} (hij : i ≠ j) :
    rhoLift h π hij.symm = (rhoLift h π hij).comp swapSL := by
  rw [rhoLift, rhoLift, rhoU_swap, sl2Lift_comp_of_unique hS.sl2K hS.sl2K]

theorem hRho_swap {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    hRho h π hij.symm t = hRho h π hij t⁻¹ := by
  rw [hRho, hRho, MonoidHom.comp_apply, MonoidHom.comp_apply, rhoLift_swap h hS hij,
    MonoidHom.comp_apply, swapSL_sl2Diag]

end Basic

section Diag

variable {R : Type*} [Group R] {π : R →* hypSU h r ε} (hS : LiftHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem conj_rhoLift_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) K) :
    x * rhoLift h π hij g * x⁻¹ = rhoLift h π hij (sl2ConjDiag (Units.mk0 (q (.inl j) / q (.inl i))
      (div_ne_zero (diag_entry_ne_zero h hx _) (diag_entry_ne_zero h hx _))) g) := by
  refine conj_rhoLift_of h hS hij hij ?_ g
  refine MonoidHom.ext fun g' => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_diag_rhoU h hx hij g'

theorem conj_iotaLift_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    x * iotaLift h π hc hc0 k g * x⁻¹ =
      iotaLift h π hc hc0 k (sl2ConjDiag (diagRatio h hx k) g) := by
  refine conj_iotaLift_of h hS hc hc0 ?_ g
  refine MonoidHom.ext fun g' => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_diag_iotaU h hc hc0 hx k g'

theorem conj_hRho_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    {i j : Fin r} (hij : i ≠ j) (t : Kˣ) : x * hRho h π hij t * x⁻¹ = hRho h π hij t := by
  rw [hRho, MonoidHom.comp_apply, conj_rhoLift_of_diag h hS hx hij, sl2ConjDiag_sl2Diag]

theorem conj_hIota_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) (b : h.fixedFieldˣ) :
    x * hIota h π hc hc0 k b * x⁻¹ = hIota h π hc hc0 k b := by
  rw [hIota, MonoidHom.comp_apply, conj_iotaLift_of_diag h hS hc hc0 hx, sl2ConjDiag_sl2Diag]

theorem vRho_conj_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    {i j : Fin r} (hij : i ≠ j) :
    vRho h π hij * x * (vRho h π hij)⁻¹ = hRho h π hij (Units.mk0 (q (.inl j) / q (.inl i))
      (div_ne_zero (diag_entry_ne_zero h hx _) (diag_entry_ne_zero h hx _))) * x := by
  set u : Kˣ := Units.mk0 (q (.inl j) / q (.inl i))
    (div_ne_zero (diag_entry_ne_zero h hx _) (diag_entry_ne_zero h hx _))
  have E : x * vRho h π hij * x⁻¹ = hRho h π hij u⁻¹ * vRho h π hij := by
    rw [vRho, conj_rhoLift_of_diag h hS hx hij, sl2ConjDiag_sl2W, map_mul]
    rfl
  calc vRho h π hij * x * (vRho h π hij)⁻¹
      = (hRho h π hij u⁻¹)⁻¹ * (hRho h π hij u⁻¹ * vRho h π hij) * x * (vRho h π hij)⁻¹ := by
        group
    _ = (hRho h π hij u⁻¹)⁻¹ * (x * vRho h π hij * x⁻¹) * x * (vRho h π hij)⁻¹ := by rw [E]
    _ = hRho h π hij u * x := by rw [map_inv, inv_inv]; group

theorem vIota_conj_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) :
    vIota h π hc hc0 k * x * (vIota h π hc hc0 k)⁻¹ =
      hIota h π hc hc0 k (diagRatio h hx k) * x := by
  set u := diagRatio h hx k
  have E : x * vIota h π hc hc0 k * x⁻¹ = hIota h π hc hc0 k u⁻¹ * vIota h π hc hc0 k := by
    rw [vIota, conj_iotaLift_of_diag h hS hc hc0 hx, sl2ConjDiag_sl2W, map_mul]
    rfl
  calc vIota h π hc hc0 k * x * (vIota h π hc hc0 k)⁻¹
      = (hIota h π hc hc0 k u⁻¹)⁻¹ * (hIota h π hc hc0 k u⁻¹ * vIota h π hc hc0 k) * x *
          (vIota h π hc hc0 k)⁻¹ := by group
    _ = (hIota h π hc hc0 k u⁻¹)⁻¹ * (x * vIota h π hc hc0 k * x⁻¹) * x *
          (vIota h π hc hc0 k)⁻¹ := by rw [E]
    _ = hIota h π hc hc0 k u * x := by rw [map_inv, inv_inv]; group

end Diag

section Weyl

variable {R : Type*} [Group R] {π : R →* hypSU h r ε} (hS : LiftHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem vRho_conj_rhoLift {i j : Fin r} (hij : i ≠ j) {k l : Fin r} (hkl : k ≠ l)
    (g : SpecialLinearGroup (Fin 2) K) :
    vRho h π hij * rhoLift h π hkl g * (vRho h π hij)⁻¹ =
      rhoLift h π ((Equiv.swap i j).injective.ne hkl)
        (sl2ConjDiag (Units.mk0 (lineSign j l / lineSign j k)
          (div_ne_zero (lineSign_ne_zero j l) (lineSign_ne_zero j k))) g) := by
  refine conj_rhoLift_of h hS hkl _ (MonoidHom.ext fun g' => ?_) g
  rw [pi_vRho h hS hij]
  exact conj_rhoU_sl2W_rhoU h hij hkl g'

theorem vRho_conj_iotaLift {i j : Fin r} (hij : i ≠ j) (k : Fin r)
    (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    vRho h π hij * iotaLift h π hc hc0 k g * (vRho h π hij)⁻¹ =
      iotaLift h π hc hc0 (Equiv.swap i j k) g := by
  refine conj_iotaLift_of h hS hc hc0 (γ := MonoidHom.id _) (MonoidHom.ext fun g' => ?_) g
  rw [pi_vRho h hS hij]
  exact conj_rhoU_sl2W_iotaU h hij hc hc0 k g'

theorem vRho_conj_vIota {i j : Fin r} (hij : i ≠ j) :
    vRho h π hij * vIota h π hc hc0 j * (vRho h π hij)⁻¹ = vIota h π hc hc0 i := by
  have e := vRho_conj_iotaLift h hS hc hc0 hij j sl2W
  rwa [Equiv.swap_apply_right] at e

theorem hRho_trans {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t : Kˣ) :
    hRho h π hik t = hRho h π hij t * hRho h π hjk t := by
  have e1 := vRho_conj_of_diag h hS (coe_pi_hRho h hS hjk t) hij
  have e2 := vRho_conj_rhoLift h hS hij hjk (sl2Diag t)
  rw [sl2ConjDiag_sl2Diag, rhoLift_congr h π _ hik (Equiv.swap_apply_right i j)
    (Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm)] at e2
  have hu : Units.mk0 (rhoDiag h j k t (.inl j) / rhoDiag h j k t (.inl i))
      (div_ne_zero (diag_entry_ne_zero h (coe_pi_hRho h hS hjk t) _)
        (diag_entry_ne_zero h (coe_pi_hRho h hS hjk t) _)) = t := by
    ext
    simp [rhoDiag, hij, hik]
  rw [hu] at e1
  change vRho h π hij * hRho h π hjk t * (vRho h π hij)⁻¹ = hRho h π hik t at e2
  rw [← e2, e1]

theorem hIota_eq_hRho_mul {i j : Fin r} (hij : i ≠ j) (b : h.fixedFieldˣ) :
    hIota h π hc hc0 i b = hRho h π hij (fcoe h b) * hIota h π hc hc0 j b := by
  have e1 := vRho_conj_of_diag h hS (coe_pi_hIota h hS hc hc0 j b) hij
  have e2 := vRho_conj_iotaLift h hS hc hc0 hij j (sl2Diag b)
  rw [Equiv.swap_apply_right] at e2
  have hu : Units.mk0 (iotaDiag h j b (.inl j) / iotaDiag h j b (.inl i))
      (div_ne_zero (diag_entry_ne_zero h (coe_pi_hIota h hS hc hc0 j b) _)
        (diag_entry_ne_zero h (coe_pi_hIota h hS hc hc0 j b) _)) = fcoe h b := by
    ext
    simp [iotaDiag, hij, coe_fcoe]
  rw [hu] at e1
  change vRho h π hij * hIota h π hc hc0 j b * (vRho h π hij)⁻¹ = hIota h π hc hc0 i b at e2
  rw [← e2, e1]

theorem vRho_conj_vRho_left {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    vRho h π hij * vRho h π hjl * (vRho h π hij)⁻¹ = (vRho h π hil)⁻¹ := by
  have e := vRho_conj_rhoLift h hS hij hjl sl2W
  have hu : Units.mk0 (lineSign (K := K) j l / lineSign j j)
      (div_ne_zero (lineSign_ne_zero j l) (lineSign_ne_zero j j)) = -1 := by
    ext
    simp [lineSign, hjl.symm]
  rw [hu, sl2ConjDiag_neg_one_sl2W, map_inv, rhoLift_congr h π _ hil
    (Equiv.swap_apply_right i j) (Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm)] at e
  exact e

theorem vRho_conj_vRho_right {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    vRho h π hjl * vRho h π hij * (vRho h π hjl)⁻¹ = vRho h π hil := by
  have e := vRho_conj_rhoLift h hS hjl hij sl2W
  have hu : Units.mk0 (lineSign (K := K) l j / lineSign l i)
      (div_ne_zero (lineSign_ne_zero l j) (lineSign_ne_zero l i)) = 1 := by
    ext
    simp [lineSign, hjl, hil]
  rw [hu, sl2ConjDiag_one, rhoLift_congr h π _ hil (Equiv.swap_apply_of_ne_of_ne hij hil)
    (Equiv.swap_apply_left j l)] at e
  exact e

theorem commute_vRho_vRho {i j k l : Fin r} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) : Commute (vRho h π hij) (vRho h π hkl) :=
  commute_rhoLift_rhoLift h hS hij hkl (commute_rhoU_rhoU h hij hkl hik hil hjk hjl) sl2W sl2W

theorem commute_vRho_vIota {i j k : Fin r} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Commute (vRho h π hij) (vIota h π hc hc0 k) :=
  commute_rhoLift_iotaLift h hS hc hc0 hij k (commute_rhoU_iotaU h hij hc hc0 hik hjk) sl2W sl2W

theorem commute_vIota_vIota {k l : Fin r} (hkl : k ≠ l) :
    Commute (vIota h π hc hc0 k) (vIota h π hc hc0 l) :=
  commute_iotaLift_iotaLift h hS hc hc0 k l (commute_iotaU_iotaU h hc hc0 hkl) sl2W sl2W

end Weyl


section Odd

variable {R : Type*} [Group R] {π : R →* hypSU h r 1} (hS : LiftHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem pi_kappaLift (k : Fin r) (X : gramSU h (gramJ3 K)) :
    π (kappaLift h π k X) = kappaU h k X :=
  map_perfectLift_of_unique (hS.su3 _) X

theorem coe_pi_hKappa (k : Fin r) (a : Kˣ) :
    ((π (hKappa h π k a) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      diagonal (kappaDiag h k a) := by
  rw [hKappa, MonoidHom.comp_apply, pi_kappaLift h hS]
  exact coe_kappaU_dkHom h k a

theorem kappaLift_comp (k : Fin r) (γ : gramSU h (gramJ3 K) →* gramSU h (gramJ3 K)) :
    (kappaLift h π k).comp γ = perfectLift π ((kappaU h k).comp γ) := by
  refine eq_perfectLift_of_unique (hS.su3 _) ?_
  rw [← MonoidHom.comp_assoc]
  exact congrArg (fun α => α.comp γ)
    (comp_perfectLift_of_unique (hS.su3 (kappaU h k)))

theorem conj_kappaLift_of {e : R} {k k' : Fin r}
    {γ : gramSU h (gramJ3 K) →* gramSU h (gramJ3 K)}
    (hγ : (MulAut.conj (π e)).toMonoidHom.comp (kappaU h k) = (kappaU h k').comp γ)
    (X : gramSU h (gramJ3 K)) :
    e * kappaLift h π k X * e⁻¹ = kappaLift h π k' (γ X) := by
  have h1 := conj_perfectLift_of_unique hS.su3 (kappaU h k) e X
  rw [hγ, ← kappaLift_comp h hS] at h1
  exact h1

theorem conj_kappaLift_of_diag {x : R} {q : HypIndex r 1 → K}
    (hx : ((π x : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal q)
    (k : Fin r) (X : gramSU h (gramJ3 K)) :
    x * kappaLift h π k X * x⁻¹ = kappaLift h π k (conjDiagJ3 h (diag_trip_ne_zero h hx k)
      (diag_trip_02 h hx k) (diag_trip_11 h hx k) X) := by
  refine conj_kappaLift_of h hS ?_ X
  refine MonoidHom.ext fun X' => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_diag_kappaU h hx k X'

theorem conj_hKappa_of_diag {x : R} {q : HypIndex r 1 → K}
    (hx : ((π x : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal q)
    (k : Fin r) (a : Kˣ) : x * hKappa h π k a * x⁻¹ = hKappa h π k a := by
  rw [hKappa, MonoidHom.comp_apply, conj_kappaLift_of_diag h hS hx, conjDiagJ3_dkHom]

theorem vRho_conj_hKappa {i j : Fin r} (hij : i ≠ j) (k : Fin r) (a : Kˣ) :
    vRho h π hij * hKappa h π k a * (vRho h π hij)⁻¹ = hKappa h π (Equiv.swap i j k) a := by
  have e := conj_kappaLift_of h hS (e := vRho h π hij) (k := k) (k' := Equiv.swap i j k)
    (γ := conjDiagJ3 h (u := ![lineSign j k, 1, lineSign j k])
      (fun x => by fin_cases x <;> simp [lineSign_ne_zero])
      (lineSign_isometry_J3 h j k).1 (lineSign_isometry_J3 h j k).2)
    (MonoidHom.ext fun X' => by
      rw [pi_vRho h hS hij]
      exact conj_rhoU_sl2W_kappaU h hij k X') (dkHom h a)
  rw [conjDiagJ3_dkHom] at e
  exact e

theorem hKappa_eq_hRho_mul {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    hKappa h π i a = hRho h π hij a * hKappa h π j a := by
  have e1 := vRho_conj_of_diag h hS (coe_pi_hKappa h hS j a) hij
  have e2 := vRho_conj_hKappa h hS hij j a
  rw [Equiv.swap_apply_right] at e2
  have hu : Units.mk0 (kappaDiag h j a (.inl j) / kappaDiag h j a (.inl i))
      (div_ne_zero (diag_entry_ne_zero h (coe_pi_hKappa h hS j a) _)
        (diag_entry_ne_zero h (coe_pi_hKappa h hS j a) _)) = a := by
    ext
    simp [kappaDiag, hij]
  rw [hu] at e1
  rw [← e2, e1]

theorem iotaLift_eq_kappaLift_comp (k : Fin r) :
    iotaLift h π hc hc0 k = (kappaLift h π k).comp (iota3 h hc hc0) := by
  symm
  refine eq_sl2Lift_of_unique (hS.sl2F _) ?_
  rw [← MonoidHom.comp_assoc, iotaU_eq_kappaU_comp h hc hc0 k]
  exact congrArg (fun α => α.comp (iota3 h hc hc0))
    (comp_perfectLift_of_unique (hS.su3 (kappaU h k)))

theorem hIota_eq_hKappa (k : Fin r) (b : h.fixedFieldˣ) :
    hIota h π hc hc0 k b = hKappa h π k (fcoe h b) := by
  rw [hIota, MonoidHom.comp_apply, iotaLift_eq_kappaLift_comp h hS hc hc0, MonoidHom.comp_apply,
    iota3_sl2Diag h hc hc0]
  rfl

end Odd

end Gen

end CFSG.RankThree.CentralLiftU

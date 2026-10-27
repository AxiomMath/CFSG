module

public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsBridge

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary

theorem conj_mem_conjOrbit {M : Type*} [Group M] {H : Subgroup M} {x y γ : M} (hγ : γ ∈ H)
    (hy : y ∈ conjOrbit H x) : γ * y * γ⁻¹ ∈ conjOrbit H x := by
  obtain ⟨c, hc, rfl⟩ := hy
  exact ⟨γ * c, H.mul_mem hγ hc, by group⟩

theorem conjOrbit_mono {M : Type*} [Group M] {H H' : Subgroup M} (h : H ≤ H') (x : M) :
    conjOrbit H x ⊆ conjOrbit H' x := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, h hc, rfl⟩

theorem conjOrbit_subset_fibOrbit
    {d : Fin 5} {H : Subgroup GStar} (hH : H ≤ parStar firstJ)
    {x : GStar} (hx : x ∈ fibOrbit d) : conjOrbit H x ⊆ fibOrbit d := by
  rintro _ ⟨c, hc, rfl⟩
  exact conj_mem_conjOrbit (hH hc) hx

@[expose] def quotSp (d : Fin 5) : Submodule F4 V6 := if d = 2 then Rsp else Tsp

@[expose] def quotDim (d : Fin 5) : ℕ := if d = 2 then 1 else 3

theorem uIso_quotSp (d : Fin 5) : UIso (quotDim d) (quotSp d) := by
  unfold quotSp quotDim
  split_ifs
  · exact uIso_Rsp
  · exact uIso_Tsp

theorem exists_actP1_quotSp
    {d : Fin 5} {S : Submodule F4 V6} (hS : UIso (quotDim d) S) :
    ∃ g : Pc 0, actP1 g (quotSp d) = S := by
  unfold quotSp quotDim at *
  split_ifs at *
  · exact exists_actP1_Rsp hS
  · exact exists_actP1_Tsp hS

theorem actP1_inv_eq_sigmaAct
    (q : Pc 0) (S : Submodule F4 V6) :
    actP1 q⁻¹ S = sigmaAct S (rhoP1 q) := by
  rw [actP1, map_inv, inv_inv]

open _root_.Classical in
@[expose] def nquot
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (d : Fin 5) (x : GStar) :
    Submodule F4 V6 :=
  if h : ∃ p : Pc 0, rho1 θ p * SemidirectProduct.inl (fibT d) * (rho1 θ p)⁻¹ = x
  then actP1 h.choose (quotSp d) else ⊥

section Quotient

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)

include hadj hfeq hfB in
theorem actP1_quotSp_iff
    {d : Fin 5} (hd : IsMid d) (g : Pc 0) :
    actP1 g (quotSp d) = quotSp d ↔ rho1 θ g ∈ parIStar d := by
  rcases hd with rfl | rfl | rfl
  · exact (actP1_Tsp_iff g).trans (mem_Pc_one_iff_rho1 hadj hfeq hfB g)
  · exact (actP1_Rsp_iff g).trans (mem_Pc_three_iff_rho1 hadj hfeq hfB g)
  · exact (actP1_Tsp_iff g).trans (mem_Pc_one_iff_rho1 hadj hfeq hfB g)

include hadj hfeq hfB in
theorem actP1_quotSp_eq_iff
    {d : Fin 5} (hd : IsMid d) (p p' : Pc 0) :
    actP1 p (quotSp d) = actP1 p' (quotSp d) ↔ (rho1 θ p)⁻¹ * rho1 θ p' ∈ parIStar d := by
  rw [← map_inv, ← map_mul, ← actP1_quotSp_iff hadj hfeq hfB hd]
  constructor
  · intro h
    rw [actP1_mul, ← h, actP1_inv_actP1]
  · intro h
    calc actP1 p (quotSp d) = actP1 p (actP1 (p⁻¹ * p') (quotSp d)) := by rw [h]
      _ = actP1 p' (quotSp d) := by rw [← actP1_mul, mul_inv_cancel_left]

include hadj hfeq hfB in
theorem nquot_conj
    {d : Fin 5} (hd : IsMid d) (p : Pc 0) :
    nquot θ d (rho1 θ p * SemidirectProduct.inl (fibT d) * (rho1 θ p)⁻¹) = actP1 p (quotSp d) := by
  have hex : ∃ p' : Pc 0, rho1 θ p' * SemidirectProduct.inl (fibT d) * (rho1 θ p')⁻¹ =
      rho1 θ p * SemidirectProduct.inl (fibT d) * (rho1 θ p)⁻¹ := ⟨p, rfl⟩
  rw [nquot, dite_eq_left hex]
  refine ((actP1_quotSp_eq_iff hadj hfeq hfB hd p hex.choose).2 ?_).symm
  apply fibCent_le_parIStar d
  refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (rho1_mem_parStar hadj hfeq hfB p))
    (rho1_mem_parStar hadj hfeq hfB _), Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have h := hex.choose_spec
  set a := rho1 θ hex.choose
  set b := rho1 θ p
  set t : GStar := SemidirectProduct.inl (fibT d)
  calc b⁻¹ * a * t = b⁻¹ * (a * t * a⁻¹) * a := by group
    _ = b⁻¹ * (b * t * b⁻¹) * a := by rw [h]
    _ = t * (b⁻¹ * a) := by group

include hadj hfeq hfB in
theorem exists_rho1_conj
    {d : Fin 5} {x : GStar} (hx : x ∈ fibOrbit d) :
    ∃ p : Pc 0, rho1 θ p * SemidirectProduct.inl (fibT d) * (rho1 θ p)⁻¹ = x := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := exists_rho1_eq hadj hfeq hfB hγ
  exact ⟨p, rfl⟩

include hadj hfeq hfB in
theorem nquot_eq_iff
    {d : Fin 5} (hd : IsMid d) {x y : GStar} (hx : x ∈ fibOrbit d)
    (hy : y ∈ fibOrbit d) : nquot θ d x = nquot θ d y ↔ y ∈ conjOrbit radStar x := by
  obtain ⟨p, rfl⟩ := exists_rho1_conj hadj hfeq hfB hx
  obtain ⟨p', rfl⟩ := exists_rho1_conj hadj hfeq hfB hy
  rw [nquot_conj hadj hfeq hfB hd, nquot_conj hadj hfeq hfB hd,
    actP1_quotSp_eq_iff hadj hfeq hfB hd,
    mem_conjOrbit_radStar_iff (rho1_mem_parStar hadj hfeq hfB p)
      (rho1_mem_parStar hadj hfeq hfB p')]

include hadj hfeq hfB in
theorem nquot_conj_inv
    {d : Fin 5} (hd : IsMid d) {x : GStar} (hx : x ∈ fibOrbit d) (q : Pc 0) :
    nquot θ d ((rho1 θ q)⁻¹ * x * rho1 θ q) = sigmaAct (nquot θ d x) (rhoP1 q) := by
  obtain ⟨p, rfl⟩ := exists_rho1_conj hadj hfeq hfB hx
  have e : (rho1 θ q)⁻¹ * (rho1 θ p * SemidirectProduct.inl (fibT d) * (rho1 θ p)⁻¹) *
      rho1 θ q = rho1 θ (q⁻¹ * p) * SemidirectProduct.inl (fibT d) * (rho1 θ (q⁻¹ * p))⁻¹ := by
    rw [map_mul, map_inv]
    group
  rw [e, nquot_conj hadj hfeq hfB hd, nquot_conj hadj hfeq hfB hd, actP1_mul]
  exact actP1_inv_eq_sigmaAct q _

include hadj hfeq hfB in
theorem image_nquot
    {d : Fin 5} (hd : IsMid d) :
    nquot θ d '' fibOrbit d = {S | UIso (quotDim d) S} := by
  ext S
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, rfl⟩ := exists_rho1_conj hadj hfeq hfB hx
    rw [nquot_conj hadj hfeq hfB hd]
    exact (uIso_quotSp d).actP1 p
  · intro hS
    obtain ⟨g, rfl⟩ := exists_actP1_quotSp hS
    exact ⟨_, ⟨rho1 θ g, rho1_mem_parStar hadj hfeq hfB g, rfl⟩, nquot_conj hadj hfeq hfB hd g⟩

include hadj hfeq hfB in
theorem uIso_nquot
    {d : Fin 5} (hd : IsMid d) {x : GStar} (hx : x ∈ fibOrbit d) :
    UIso (quotDim d) (nquot θ d x) := by
  have h : nquot θ d x ∈ nquot θ d '' fibOrbit d := ⟨x, hx, rfl⟩
  rwa [image_nquot hadj hfeq hfB hd] at h

variable {Q : Subgroup (Pc 0)} (hU : radStar ≤ Q.map (rho1 θ))

include hadj hfeq hfB hU in
theorem conjOrbit_eq_of_mid
    {d : Fin 5} (hd : IsMid d) {x : GStar} (hx : x ∈ fibOrbit d) :
    conjOrbit (Q.map (rho1 θ)) x =
      {y | y ∈ fibOrbit d ∧ ∃ q ∈ Q, sigmaAct (nquot θ d x) (rhoP1 q) = nquot θ d y} := by
  ext y
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨conj_mem_conjOrbit (rho1_mem_parStar hadj hfeq hfB q) hx, q⁻¹, Q.inv_mem hq, ?_⟩
    have h := nquot_conj_inv hadj hfeq hfB hd hx q⁻¹
    rw [map_inv (rho1 θ) q, inv_inv] at h
    exact h.symm
  · rintro ⟨hy, q, hq, hqy⟩
    have hy' : (rho1 θ q)⁻¹ * x * rho1 θ q ∈ fibOrbit d := by
      have h := conj_mem_conjOrbit (rho1_mem_parStar hadj hfeq hfB q⁻¹) hx
      rwa [map_inv (rho1 θ) q, inv_inv] at h
    have hfib : nquot θ d ((rho1 θ q)⁻¹ * x * rho1 θ q) = nquot θ d y := by
      rw [nquot_conj_inv hadj hfeq hfB hd hx q, hqy]
    obtain ⟨u, hu, rfl⟩ := (nquot_eq_iff hadj hfeq hfB hd hy' hy).1 hfib
    obtain ⟨q', hq', hq'u⟩ := hU hu
    refine ⟨u * (rho1 θ q)⁻¹, Q.map (rho1 θ) |>.mul_mem ⟨q', hq', hq'u⟩
      ⟨q⁻¹, Q.inv_mem hq, map_inv _ _⟩, by group⟩

include hadj hfeq hfB hU in
theorem conjOrbit_eq_of_JJ
    {d : Fin 5} (hd : d = 0 ∨ d = 4) {x : GStar} (hx : x ∈ fibOrbit d) :
    conjOrbit (Q.map (rho1 θ)) x = fibOrbit d := by
  refine Set.Subset.antisymm (conjOrbit_subset_fibOrbit (map_le_parStar hadj hfeq hfB Q) hx)
    fun y hy => ?_
  exact conjOrbit_mono hU x (mem_conjOrbit_radStar_of_JJ hd hx hy)

include hadj hfeq hfB in
theorem ncard_nquot_fibre
    {d : Fin 5} (hd : IsMid d) {S : Submodule F4 V6}
    (hS : UIso (quotDim d) S) :
    {y : fibOrbit d | nquot θ d y = S}.ncard = fibUSize d := by
  have hS' : S ∈ nquot θ d '' fibOrbit d := by
    rw [image_nquot hadj hfeq hfB hd]
    exact hS
  obtain ⟨x, hx, rfl⟩ := hS'
  have e : {y : fibOrbit d | nquot θ d y = nquot θ d x} =
      Subtype.val ⁻¹' conjOrbit radStar x := by
    ext y
    exact (eq_comm.trans (nquot_eq_iff hadj hfeq hfB hd hx y.2))
  have hsub : conjOrbit radStar x ⊆ fibOrbit d := fun _ hy =>
    conjOrbit_subset_fibOrbit radStar_le_parStar hx hy
  rw [e, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
    (by rw [Subtype.range_coe]; exact hsub), ncard_conjOrbit_radStar hx]

include hadj hfeq hfB hU in
theorem ncard_conjOrbit_of_mid
    {d : Fin 5} (hd : IsMid d) {x : GStar} (hx : x ∈ fibOrbit d) :
    (conjOrbit (Q.map (rho1 θ)) x).ncard =
      fibUSize d * {S | ∃ q ∈ Q, sigmaAct (nquot θ d x) (rhoP1 q) = S}.ncard := by
  set ψ : fibOrbit d → {S : Submodule F4 V6 // UIso (quotDim d) S} :=
    fun y => ⟨nquot θ d y, uIso_nquot hadj hfeq hfB hd y.2⟩ with hψ
  have : Finite (Submodule F4 V6) :=
    Finite.of_injective (fun S : Submodule F4 V6 => (S : Set V6)) SetLike.coe_injective
  set A : Set {S : Submodule F4 V6 // UIso (quotDim d) S} :=
    {S | ∃ q ∈ Q, sigmaAct (nquot θ d x) (rhoP1 q) = (S : Submodule F4 V6)} with hA
  have hfib : ∀ S, (ψ ⁻¹' {S}).ncard = fibUSize d := by
    intro S
    have e : ψ ⁻¹' {S} = {y : fibOrbit d | nquot θ d y = S} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, hψ]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e]
    exact ncard_nquot_fibre hadj hfeq hfB hd S.2
  have h1 := ncard_preimage_of_fiber hfib A
  have e1 : conjOrbit (Q.map (rho1 θ)) x = Subtype.val '' (ψ ⁻¹' A) := by
    rw [conjOrbit_eq_of_mid hadj hfeq hfB hU hd hx]
    ext y
    constructor
    · rintro ⟨hy, q, hq, hqy⟩
      exact ⟨⟨y, hy⟩, ⟨q, hq, hqy⟩, rfl⟩
    · rintro ⟨y, ⟨q, hq, hqy⟩, rfl⟩
      exact ⟨y.2, q, hq, hqy⟩
  have e2 : {S | ∃ q ∈ Q, sigmaAct (nquot θ d x) (rhoP1 q) = S} =
      Subtype.val '' A := by
    ext S
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨_, (uIso_nquot hadj hfeq hfB hd hx).sigmaAct _⟩, ⟨q, hq, rfl⟩, rfl⟩
    · rintro ⟨S, ⟨q, hq, hqS⟩, rfl⟩
      exact ⟨q, hq, hqS⟩
  rw [e1, e2, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_image_of_injective _ Subtype.val_injective, h1]

end Quotient

end CFSG.Monster.B.TwoA.Amalgam

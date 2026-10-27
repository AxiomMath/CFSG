module

public import CFSG.LieType.Steinberg.TwistedE6.Unipotent

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6

namespace TwE6Lang

theorem prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (ζ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ζ ^ f i = ζ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem cartan_E6_symm (a c : Fin (Tag.rank .E6)) : Tag.cartan .E6 a c = Tag.cartan .E6 c a := by
  fin_cases a <;> fin_cases c <;> decide

theorem twReflectHom_twReflectHom (i : Fin (Tag.rank .F4)) (v : Fin (Tag.rank .E6) → ℤ) :
    twReflectHom i (twReflectHom i v) = v := by
  have h : (twReflectHom i).comp (twReflectHom i) = AddMonoidHom.id _ :=
    addMonoidHom_ext_single fun l => by
      revert i l
      decide
  exact DFunLike.congr_fun h v

variable {k : Type*} [Field k]

@[expose] noncomputable def torusPow (ζ : kˣ) (v : Fin (Tag.rank .E6) → ℤ) :
    e6Data_valid.minGroup k :=
  torusHom k fun a => ζ ^ v a

theorem torusHom_commute (u u' : Fin (Tag.rank .E6) → kˣ) :
    Commute (torusHom k u) (torusHom k u') := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

theorem hm_commute_torusHom (a : Fin (Tag.rank .E6)) (t : kˣ) (u : Fin (Tag.rank .E6) → kˣ) :
    Commute (e6Data_valid.hm k a t) (torusHom k u) := by
  rw [← torusHom_mulSingle]
  exact torusHom_commute _ _

theorem chiHom_zpow (ζ : kˣ) (c : Fin (Tag.rank .E6)) (v : Fin (Tag.rank .E6) → ℤ) :
    chiHom c (fun a => ζ ^ v a) = ζ ^ (-∑ a, Tag.cartan .E6 a c * v a) := by
  rw [chiHom_apply]
  simp_rw [← zpow_mul]
  rw [prod_zpow_eq_zpow_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem nm_conj_torusPow (ζ : kˣ) (c : Fin (Tag.rank .E6)) (v : Fin (Tag.rank .E6) → ℤ) :
    e6Data_valid.nm k c * torusPow ζ v * (e6Data_valid.nm k c)⁻¹ =
      torusPow ζ (reflect .E6 c v) := by
  rw [torusPow, nm_conj_torusHom, torusPow, chiHom_zpow]
  congr 1
  funext b
  by_cases hb : b = c
  · subst hb
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same, reflect, Pi.sub_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one, ← zpow_add]
    congr 1
    simp_rw [cartan_E6_symm _ b]
    ring
  · simp [Pi.mulSingle_eq_of_ne hb, reflect, Pi.single_eq_of_ne hb]

theorem nHatE_conj_torusPow (ζ : kˣ) (i : Fin (Tag.rank .F4)) (v : Fin (Tag.rank .E6) → ℤ) :
    nHatE k i * torusPow ζ v * (nHatE k i)⁻¹ = torusPow ζ (twReflectHom i v) := by
  have two : ∀ a b : Fin (Tag.rank .E6), e6Data_valid.nm k a * e6Data_valid.nm k b *
      torusPow ζ v * (e6Data_valid.nm k a * e6Data_valid.nm k b)⁻¹ =
        torusPow ζ (reflect .E6 a (reflect .E6 b v)) := fun a b => by
    rw [← nm_conj_torusPow, ← nm_conj_torusPow]
    group
  fin_cases i
  · exact nm_conj_torusPow ζ (nd 1) v
  · exact nm_conj_torusPow ζ (nd 3) v
  · exact two (nd 2) (nd 4)
  · exact two (nd 0) (nd 5)

theorem nHatE_inv_conj_torusPow (ζ : kˣ) (i : Fin (Tag.rank .F4)) (v : Fin (Tag.rank .E6) → ℤ) :
    (nHatE k i)⁻¹ * torusPow ζ v * nHatE k i = torusPow ζ (twReflectHom i v) := by
  have h := nHatE_conj_torusPow ζ i (twReflectHom i v)
  rw [twReflectHom_twReflectHom] at h
  rw [← h]
  group

variable (k) in
@[expose] noncomputable def nWord (L : List (Fin (Tag.rank .F4))) : e6Data_valid.minGroup k :=
  (L.map (nHatE k)).prod

@[expose] def wAct :
    List (Fin (Tag.rank .F4)) → (Fin (Tag.rank .E6) → ℤ) →+ (Fin (Tag.rank .E6) → ℤ)
  | [] => AddMonoidHom.id _
  | i :: L => (twReflectHom i).comp (wAct L)

@[expose] def wActInv :
    List (Fin (Tag.rank .F4)) → (Fin (Tag.rank .E6) → ℤ) →+ (Fin (Tag.rank .E6) → ℤ)
  | [] => AddMonoidHom.id _
  | i :: L => (wActInv L).comp (twReflectHom i)

theorem nWord_nil : nWord k [] = 1 := rfl

theorem nWord_cons (i : Fin (Tag.rank .F4)) (L : List (Fin (Tag.rank .F4))) :
    nWord k (i :: L) = nHatE k i * nWord k L := by
  rw [nWord, List.map_cons, List.prod_cons, nWord]

theorem nWord_conj_torusPow (ζ : kˣ) (L : List (Fin (Tag.rank .F4)))
    (v : Fin (Tag.rank .E6) → ℤ) :
    nWord k L * torusPow ζ v * (nWord k L)⁻¹ = torusPow ζ (wAct L v) := by
  induction L with
  | nil => simp [nWord_nil, wAct]
  | cons i L ih =>
    rw [nWord_cons, show nHatE k i * nWord k L * torusPow ζ v * (nHatE k i * nWord k L)⁻¹ =
      nHatE k i * (nWord k L * torusPow ζ v * (nWord k L)⁻¹) * (nHatE k i)⁻¹ by group, ih,
      nHatE_conj_torusPow]
    rfl

theorem nWord_inv_conj_torusPow (ζ : kˣ) (L : List (Fin (Tag.rank .F4)))
    (v : Fin (Tag.rank .E6) → ℤ) :
    (nWord k L)⁻¹ * torusPow ζ v * nWord k L = torusPow ζ (wActInv L v) := by
  induction L generalizing v with
  | nil => simp [nWord_nil, wActInv]
  | cons i L ih =>
    rw [nWord_cons, show (nHatE k i * nWord k L)⁻¹ * torusPow ζ v * (nHatE k i * nWord k L) =
      (nWord k L)⁻¹ * ((nHatE k i)⁻¹ * torusPow ζ v * nHatE k i) * nWord k L by group,
      nHatE_inv_conj_torusPow, ih]
    rfl

theorem sigma_nWord (θ : k →+* k) (L : List (Fin (Tag.rank .F4))) :
    sigma k θ (nWord k L) = nWord k L := by
  induction L with
  | nil => rw [nWord_nil, map_one]
  | cons i L ih => rw [nWord_cons, map_mul, sigma_nHatE, ih]

theorem isRoot_wAct (L : List (Fin (Tag.rank .F4))) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) : IsRoot .E6 (wAct L γ) := by
  induction L with
  | nil => exact hγ
  | cons i L ih => exact isRoot_twReflect i ih

theorem nWord_conj_mem_rootGroup (L : List (Fin (Tag.rank .F4))) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) {x : e6Data_valid.minGroup k} (hx : x ∈ e6Data_valid.rootGroup k γ) :
    nWord k L * x * (nWord k L)⁻¹ ∈ e6Data_valid.rootGroup k (wAct L γ) := by
  induction L with
  | nil => simpa [nWord_nil, wAct] using hx
  | cons i L ih =>
    rw [nWord_cons, show nHatE k i * nWord k L * x * (nHatE k i * nWord k L)⁻¹ =
      nHatE k i * (nWord k L * x * (nWord k L)⁻¹) * (nHatE k i)⁻¹ by group]
    exact nHatE_conj_mem (isRoot_wAct L hγ) i ih

theorem sigma_torusHom (θ : k →+* k) (u : Fin (Tag.rank .E6) → kˣ) :
    sigma k θ (torusHom k u) =
      torusHom k fun b => Units.map (θ : k →* k) (u (rhoPerm.symm b)) := by
  let f : (Fin (Tag.rank .E6) → kˣ) →* (Fin (Tag.rank .E6) → kˣ) :=
    { toFun := fun u b => Units.map (θ : k →* k) (u (rhoPerm.symm b))
      map_one' := by
        funext b
        simp
      map_mul' := fun u w => by
        funext b
        simp }
  have h : (sigma k θ).comp (torusHom k) = (torusHom k).comp f := by
    refine MonoidHom.pi_ext fun a t => ?_
    simp only [MonoidHom.comp_apply, torusHom_mulSingle, sigma_hm]
    rw [← torusHom_mulSingle]
    congr 1
    funext b
    change (Pi.mulSingle (rhoPerm a) (Units.map (θ : k →* k) t) : Fin (Tag.rank .E6) → kˣ) b =
      Units.map (θ : k →* k) ((Pi.mulSingle a t : Fin (Tag.rank .E6) → kˣ) (rhoPerm.symm b))
    by_cases hb : b = rhoPerm a
    · subst hb
      simp
    · have hb' : rhoPerm.symm b ≠ a := fun h => hb (by rw [← h, Equiv.apply_symm_apply])
      rw [Pi.mulSingle_eq_of_ne hb, Pi.mulSingle_eq_of_ne hb', map_one]
  exact DFunLike.congr_fun h u

theorem sigma_torusPow (θ : k →+* k) {ζ : kˣ} {m : ℤ}
    (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (v : Fin (Tag.rank .E6) → ℤ) :
    sigma k θ (torusPow ζ v) = torusPow ζ (m • rho v) := by
  rw [torusPow, sigma_torusHom, torusPow]
  congr 1
  funext b
  rw [map_zpow, hζ, ← zpow_mul]
  congr 1

theorem torusHom_injective : Function.Injective (torusHom k) := by
  intro u u' h
  have he := congrArg (e6Data_valid.endo k) h
  rw [endo_torusHom, endo_torusHom, diagHom_apply, diagHom_apply] at he
  have hval : ∀ x : Fin e6Data.d, MinData.Valid.charHom k u (e6Data.wt x) =
      MinData.Valid.charHom k u' (e6Data.wt x) := fun x =>
    Additive.toMul.injective (Units.ext (congrFun (diagOp_injective he) x))
  funext a
  exact e6Data_valid.charHom_eq_of_wt k hval a

end TwE6Lang

end CFSG.StandardType

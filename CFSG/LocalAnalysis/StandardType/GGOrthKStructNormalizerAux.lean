module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType

open CFSG.StandardType.GGHalf
open CFSG.StandardType.SpJoin
open CFSG.StandardType.SpCoord
open CFSG.LieType.Universal.SpecialLinear
open scoped BigOperators
open Multiplicative

@[expose] noncomputable def okNorm_wt {k : ℕ} (a : Fin k → Multiplicative (ZMod 3)) : ℕ :=
  (Finset.univ.filter fun j => a j ≠ 1).card

theorem okNorm_wt_mulSingle {k : ℕ} {j : Fin k} {g : Multiplicative (ZMod 3)} (hg : g ≠ 1) :
    okNorm_wt (Pi.mulSingle j g : Fin k → Multiplicative (ZMod 3)) = 1 := by
  rw [okNorm_wt]
  have hfilter :
      (Finset.univ.filter fun i => (Pi.mulSingle j g : Fin k → Multiplicative (ZMod 3)) i ≠ 1) =
        {j} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hij
      exact h.2 (by rw [Pi.mulSingle_apply, if_neg hij])
    · intro hij
      subst hij
      simpa [Pi.mulSingle_apply] using hg
  rw [hfilter, Finset.card_singleton]

theorem okNorm_weight_one {k : ℕ} {a : Fin k → Multiplicative (ZMod 3)}
    (h : okNorm_wt a = 1) :
    ∃ j : Fin k, a j ≠ 1 ∧ a = Pi.mulSingle j (a j) := by
  rw [okNorm_wt] at h
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
  have hjmem : j ∈ Finset.univ.filter (fun i => a i ≠ 1) := by
    rw [hj]
    exact Finset.mem_singleton.mpr rfl
  have haj : a j ≠ 1 := (Finset.mem_filter.mp hjmem).2
  refine ⟨j, haj, ?_⟩
  funext i
  rw [Pi.mulSingle_apply]
  by_cases hi : i = j
  · subst hi
    simp
  · rw [if_neg hi]
    by_contra hne
    have himem : i ∈ Finset.univ.filter (fun l => a l ≠ 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
    rw [hj] at himem
    exact hi (Finset.mem_singleton.mp himem)

theorem okNorm_wt_mulSingle_le_one {k : ℕ} (i : Fin k) (c : Multiplicative (ZMod 3)) :
    okNorm_wt (Pi.mulSingle i c : Fin k → Multiplicative (ZMod 3)) ≤ 1 := by
  rw [okNorm_wt]
  have hsub : (Finset.univ.filter fun t =>
      (Pi.mulSingle i c : Fin k → Multiplicative (ZMod 3)) t ≠ 1) ⊆ {i} := by
    intro t ht
    rw [Finset.mem_singleton]
    by_contra hti
    exact (Finset.mem_filter.mp ht).2 (by rw [Pi.mulSingle_apply, if_neg hti])
  calc (Finset.univ.filter fun t =>
        (Pi.mulSingle i c : Fin k → Multiplicative (ZMod 3)) t ≠ 1).card
      ≤ ({i} : Finset (Fin k)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton i

theorem okNorm_zmod3_ne_zero {x : ZMod 3} (h : x ≠ 0) : x = 1 ∨ x = -1 := by
  have hval := ZMod.val_lt x
  have hne : x.val ≠ 0 := by
    intro h0
    apply h
    rw [← ZMod.natCast_zmod_val x, h0]
    norm_num
  have hcases : x.val = 1 ∨ x.val = 2 := by omega
  rcases hcases with h1 | h2
  · left
    rw [← ZMod.natCast_zmod_val x, h1]
    norm_num
  · right
    rw [← ZMod.natCast_zmod_val x, h2]
    decide

theorem okNorm_finrank_ker_conj {N : ℕ}
    (e : (Fin N → F2) ≃ₗ[F2] (Fin N → F2))
    (f : (Fin N → F2) →ₗ[F2] (Fin N → F2)) :
    Module.finrank F2 (LinearMap.ker (e.conj f)) =
      Module.finrank F2 (LinearMap.ker f) := by
  have hker : LinearMap.ker (e.conj f) =
      Submodule.map (e : (Fin N → F2) →ₗ[F2] (Fin N → F2)) (LinearMap.ker f) := by
    apply Submodule.ext
    intro x
    rw [LinearMap.mem_ker, Submodule.mem_map]
    constructor
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [LinearMap.mem_ker]
      rw [LinearEquiv.conj_apply] at hx
      simp only [LinearMap.comp_apply] at hx
      have hx' : e (f (e.symm x)) = e 0 := by simpa using hx
      exact e.injective hx'
    · rintro ⟨y, hy, rfl⟩
      rw [LinearEquiv.conj_apply]
      simp only [LinearMap.comp_apply]
      change e (f (e.symm (e y))) = 0
      rw [e.symm_apply_apply, LinearMap.mem_ker.mp hy, map_zero]
  rw [hker]
  exact LinearEquiv.finrank_map_eq e (LinearMap.ker f)

theorem okNorm_sgnAut_toEquiv {k : ℕ} (i : Fin k) :
    (SpCoord.sgnAut (p := 3) (k := k) i).toEquiv = coordInv k 3 i := by
  ext v t
  change (SpCoord.sgnAut (p := 3) (k := k) i) v t = coordInv k 3 i v t
  rw [SpCoord.sgnAut_apply, coordInv_apply, Function.update_apply]

theorem okNorm_permAut_toEquiv {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (SpCoord.permAut (p := 3) (k := k) σ).toEquiv = coordPerm k 3 σ := by
  ext v t
  rfl

@[expose] noncomputable def okNorm_flipAut {k : ℕ} (S : Finset (Fin k)) :
    MulAut (Fin k → Multiplicative (ZMod 3)) where
  toFun v := fun t => if t ∈ S then (v t)⁻¹ else v t
  invFun v := fun t => if t ∈ S then (v t)⁻¹ else v t
  left_inv v := by
    funext t
    show (if t ∈ S then (if t ∈ S then (v t)⁻¹ else v t)⁻¹
      else (if t ∈ S then (v t)⁻¹ else v t)) = v t
    by_cases h : t ∈ S
    · rw [if_pos h, if_pos h]
      exact inv_inv (v t)
    · rw [if_neg h, if_neg h]
  right_inv v := by
    funext t
    show (if t ∈ S then (if t ∈ S then (v t)⁻¹ else v t)⁻¹
      else (if t ∈ S then (v t)⁻¹ else v t)) = v t
    by_cases h : t ∈ S
    · rw [if_pos h, if_pos h]
      exact inv_inv (v t)
    · rw [if_neg h, if_neg h]
  map_mul' v w := by
    funext t
    show (if t ∈ S then ((v * w) t)⁻¹ else (v * w) t) =
      (if t ∈ S then (v t)⁻¹ else v t) * (if t ∈ S then (w t)⁻¹ else w t)
    by_cases h : t ∈ S
    · rw [if_pos h, if_pos h, if_pos h, Pi.mul_apply]
      exact mul_inv (v t) (w t)
    · rw [if_neg h, if_neg h, if_neg h, Pi.mul_apply]

@[simp] theorem okNorm_flipAut_apply {k : ℕ} (S : Finset (Fin k))
    (v : Fin k → Multiplicative (ZMod 3)) (t : Fin k) :
    okNorm_flipAut S v t = if t ∈ S then (v t)⁻¹ else v t := rfl

theorem okNorm_flipAut_mulSingle {k : ℕ} (S : Finset (Fin k)) (i : Fin k)
    (c : Multiplicative (ZMod 3)) :
    okNorm_flipAut S (Pi.mulSingle i c : Fin k → Multiplicative (ZMod 3)) =
      Pi.mulSingle i (if i ∈ S then c⁻¹ else c) := by
  funext t
  simp only [okNorm_flipAut_apply, Pi.mulSingle_apply]
  by_cases ht : t = i
  · rw [ht]
    by_cases hi : i ∈ S <;> simp [hi]
  · simp only [ht, if_false, if_true]
    by_cases htS : t ∈ S
    · rw [if_pos htS]
      decide
    · rw [if_neg htS]

theorem okNorm_flipAut_mem {k : ℕ} (S : Finset (Fin k)) :
    (okNorm_flipAut S).toEquiv ∈ spSignedGroup k 3 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have h1 : okNorm_flipAut (∅ : Finset (Fin k)) = 1 := by
        ext v t
        simp [okNorm_flipAut_apply]
      rw [h1]
      exact Subgroup.one_mem _
  | insert a T ha ih =>
      have hstep : okNorm_flipAut (insert a T) =
          SpCoord.sgnAut (p := 3) (k := k) a * okNorm_flipAut T := by
        apply MulEquiv.ext
        intro v
        funext t
        simp only [okNorm_flipAut_apply, MulAut.mul_apply, SpCoord.sgnAut_apply,
          Function.update_apply]
        by_cases ht : t = a
        · rw [ht, if_pos (Finset.mem_insert_self a T), if_pos rfl, if_neg ha]
          rfl
        · rw [if_neg ht]
          by_cases htT : t ∈ T
          · rw [if_pos (Finset.mem_insert_of_mem htT), if_pos htT]
          · rw [if_neg (fun h => htT (Finset.mem_insert.mp h |>.elim (fun h' => absurd h' ht) id)),
              if_neg htT]
      rw [hstep]
      rw [show (SpCoord.sgnAut (p := 3) (k := k) a * okNorm_flipAut T).toEquiv =
          (SpCoord.sgnAut (p := 3) (k := k) a).toEquiv * (okNorm_flipAut T).toEquiv from rfl]
      rw [okNorm_sgnAut_toEquiv]
      exact Subgroup.mul_mem _ (coordInv_mem_spSignedGroup a) ih

theorem okNorm_mem_spSignedGroup_of_weight {k : ℕ}
    (α : MulAut (Fin k → Multiplicative (ZMod 3)))
    (hwt : ∀ a, okNorm_wt (α a) = okNorm_wt a) :
    MulEquiv.toEquiv α ∈ spSignedGroup k 3 := by
  classical
  let g : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1
  have hg : g ≠ 1 := by
    change Multiplicative.ofAdd (1 : ZMod 3) ≠ 1
    intro h
    exact one_ne_zero ((ofAdd_eq_one).mp h)
  have hginv : g⁻¹ ≠ 1 := fun h => hg (inv_eq_one.mp h)
  have hbasis_wt (j : Fin k) :
      okNorm_wt (α (Pi.mulSingle j g : Fin k → Multiplicative (ZMod 3))) = 1 := by
    rw [hwt, okNorm_wt_mulSingle hg]
  choose m hm using fun j => okNorm_weight_one (hbasis_wt j)
  let ε : Fin k → Multiplicative (ZMod 3) :=
    fun j => α (Pi.mulSingle j g : Fin k → Multiplicative (ZMod 3)) (m j)
  have hε_eq (j : Fin k) :
      α (Pi.mulSingle j g : Fin k → Multiplicative (ZMod 3)) = Pi.mulSingle (m j) (ε j) :=
    (hm j).2
  have hε_ne (j : Fin k) : ε j ≠ 1 := (hm j).1
  let s : Fin k → ZMod 3 := fun j => Multiplicative.toAdd (ε j)
  have hs_cases (j : Fin k) : s j = 1 ∨ s j = -1 := by
    apply okNorm_zmod3_ne_zero
    intro h
    exact hε_ne j ((toAdd_eq_zero).mp h)
  have hε_ofadd (j : Fin k) : ε j = Multiplicative.ofAdd (s j) := (ofAdd_toAdd (x := ε j)).symm
  have hneg : Multiplicative.ofAdd (-1 : ZMod 3) = g⁻¹ := by
    have h1 : g * Multiplicative.ofAdd (-1 : ZMod 3) = 1 := by
      rw [show g = Multiplicative.ofAdd (1 : ZMod 3) from rfl, ← ofAdd_add]
      decide
    exact (inv_eq_of_mul_eq_one_right h1).symm
  let S : Finset (Fin k) := Finset.univ.filter (fun j => s j = -1)
  have hmemS (j : Fin k) : j ∈ S ↔ s j = -1 := by
    change j ∈ Finset.univ.filter (fun l => s l = -1) ↔ s j = -1
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ j, h⟩⟩
  have hε_sign (i : Fin k) : ε i = if i ∈ S then g⁻¹ else g := by
    rw [hε_ofadd i]
    rcases hs_cases i with h1 | h1
    · rw [h1, if_neg (by rw [hmemS, h1]; decide)]
    · rw [h1, hneg, if_pos ((hmemS i).mpr h1)]
  have hm_inj : Function.Injective m := by
    intro i j hij
    by_contra hne
    have hsupp : 2 ≤ okNorm_wt
        (Pi.mulSingle i g * Pi.mulSingle j g : Fin k → Multiplicative (ZMod 3)) := by
      rw [okNorm_wt]
      have hsub : ({i, j} : Finset (Fin k)) ⊆ Finset.univ.filter (fun t =>
          (Pi.mulSingle i g * Pi.mulSingle j g : Fin k → Multiplicative (ZMod 3)) t ≠ 1) := by
        intro t ht
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ t, ?_⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with h | h
        · rw [h, Pi.mul_apply, Pi.mulSingle_apply, if_pos rfl, Pi.mulSingle_apply, if_neg hne,
            mul_one]
          exact hg
        · rw [h, Pi.mul_apply, Pi.mulSingle_apply, if_neg (fun hh : j = i => hne hh.symm),
            Pi.mulSingle_apply, if_pos rfl, one_mul]
          exact hg
      calc 2 = ({i, j} : Finset (Fin k)).card := (Finset.card_pair hne).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hprod_eq : α (Pi.mulSingle i g * Pi.mulSingle j g :
          Fin k → Multiplicative (ZMod 3)) = Pi.mulSingle (m i) (ε i * ε j) := by
      rw [map_mul, hε_eq i, hε_eq j, hij, ← Pi.mulSingle_mul]
    have hle : okNorm_wt (α (Pi.mulSingle i g * Pi.mulSingle j g :
        Fin k → Multiplicative (ZMod 3))) ≤ 1 := by
      rw [hprod_eq]
      exact okNorm_wt_mulSingle_le_one (m i) (ε i * ε j)
    have hge : 2 ≤ okNorm_wt (α (Pi.mulSingle i g * Pi.mulSingle j g :
        Fin k → Multiplicative (ZMod 3))) := by
      rw [hwt]
      exact hsupp
    omega
  let π : Equiv.Perm (Fin k) := Equiv.ofBijective m (Finite.injective_iff_bijective.mp hm_inj)
  let β : MulAut (Fin k → Multiplicative (ZMod 3)) :=
    SpCoord.permAut (p := 3) (k := k) π * okNorm_flipAut S
  have hπi (i : Fin k) : π i = m i := rfl
  have hbasis (i : Fin k) : α (Pi.mulSingle i g : Fin k → Multiplicative (ZMod 3)) =
      β (Pi.mulSingle i g : Fin k → Multiplicative (ZMod 3)) := by
    rw [hε_eq i, hε_sign i]
    change Pi.mulSingle (m i) (if i ∈ S then g⁻¹ else g) =
      (SpCoord.permAut (p := 3) (k := k) π * okNorm_flipAut S)
        (Pi.mulSingle i g : Fin k → Multiplicative (ZMod 3))
    rw [MulAut.mul_apply, okNorm_flipAut_mulSingle, SpCoord.permAut_mulSingle, hπi]
  have hαβ : α = β := by
    have hhom : MulEquiv.toMonoidHom α = MulEquiv.toMonoidHom β := by
      refine SpCoord.hom_ext_mulSingle (p := 3) (k := k)
        (F₁ := MulEquiv.toMonoidHom α) (F₂ := MulEquiv.toMonoidHom β) ?_
      intro i
      simpa using hbasis i
    apply MulEquiv.ext
    intro a
    have := congrArg (fun f : (Fin k → Multiplicative (ZMod 3)) →* _ => f a) hhom
    simpa using this
  have hmemβ : MulEquiv.toEquiv β ∈ spSignedGroup k 3 := by
    rw [show MulEquiv.toEquiv β =
        (SpCoord.permAut (p := 3) (k := k) π).toEquiv * (okNorm_flipAut S).toEquiv from rfl]
    rw [okNorm_permAut_toEquiv]
    exact Subgroup.mul_mem _ (coordPerm_mem_spSignedGroup π) (okNorm_flipAut_mem S)
  rw [← hαβ] at hmemβ
  exact hmemβ

end CFSG.StandardType

end

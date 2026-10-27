module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameChange
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

variable {n p : ℕ}

private def axisVec (i0 : Fin n) : Fin n → Multiplicative (ZMod p) :=
  Pi.mulSingle i0 (ofAdd (1 : ZMod p))

private theorem axisVec_self (i0 : Fin n) :
    axisVec (p := p) i0 i0 = ofAdd (1 : ZMod p) := by
  rw [axisVec, Pi.mulSingle_eq_same]

private theorem axisVec_of_ne {i0 k : Fin n} (h : k ≠ i0) : axisVec (p := p) i0 k = 1 := by
  rw [axisVec, Pi.mulSingle_eq_of_ne h]

private theorem mem_bCoordinateBlock_fix {i0 : Fin n}
    (hp : p.Prime) (hp2 : p ≠ 2) {r : MulAut (Fin n → Multiplicative (ZMod p))}
    (hr : r ∈ bCoordinateBlock n p i0) {f : Fin n → Multiplicative (ZMod p)}
    (hf : ∀ k, k ≠ i0 → f k = 1) : r f = f :=
  (forall_bCoordinateBlock_fix_iff hp hp2 i0 f).mpr hf r hr

private theorem exists_ne_three {n : ℕ} (hn : 4 ≤ n) (a b c : Fin n) :
    ∃ d : Fin n, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := by
    intro d _
    by_cases hda : d = a
    · simp [hda]
    · by_cases hdb : d = b
      · simp [hdb]
      · have hdc : d = c := h d hda hdb
        simp [hdc]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({a, b, c} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
  omega

private theorem map_conj_inv_le {V : Type*} [Group V] [Finite V]
    {W : Subgroup (MulAut V)} {u : MulAut V}
    (hu : ∀ w ∈ W, u * w * u⁻¹ ∈ W) : ∀ w ∈ W, u⁻¹ * w * u ∈ W := by
  have hmap : W.map (MulAut.conj u).toMonoidHom ≤ W := by
    rintro x hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using hu v hv
  have hcard : Nat.card (W.map (MulAut.conj u).toMonoidHom) = Nat.card W :=
    Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hEq : W.map (MulAut.conj u).toMonoidHom = W :=
    Subgroup.eq_of_le_of_card_ge hmap (le_of_eq hcard.symm)
  intro w hw
  have hw' : w ∈ W.map (MulAut.conj u).toMonoidHom := by rw [hEq]; exact hw
  obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw'
  have h1 : u⁻¹ * w * u = v := by
    have h2 : w = u * v * u⁻¹ := by rw [← hvw]; rfl
    rw [h2]
    group
  rw [h1]
  exact hv

private theorem exists_mulSingle_of_normalizes_bCoordinateBlock {i0 : Fin n}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : ∀ w ∈ bCoordinateBlock n p i0, u * w * u⁻¹ ∈ bCoordinateBlock n p i0)
    (hu' : ∀ w ∈ bCoordinateBlock n p i0, u⁻¹ * w * u ∈ bCoordinateBlock n p i0)
    {i : Fin n} (hi : i ≠ i0) :
    ∃ (j : Fin n) (c : ZMod p), j ≠ i0 ∧ c ≠ 0 ∧
      u (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle j (ofAdd c) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set r : MulAut (Fin n → Multiplicative (ZMod p)) := u * sgnAut i * u⁻¹ with hrdef
  have hrW : r ∈ bCoordinateBlock n p i0 :=
    hu _ (Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩))
  have hsp : IsSignedPerm ⇑r := by
    have h := bCoordinateBlock_le_bSignedFull (p := p) i0 hrW
    rwa [bSignedFull_eq_signedPermSubgroup] at h
  obtain ⟨π, ε, hsign, hr⟩ := hsp
  have haxis : r (axisVec (p := p) i0) = axisVec (p := p) i0 :=
    mem_bCoordinateBlock_fix hp hp2 hrW (fun k hk => axisVec_of_ne hk)
  have hπi0 : π i0 = i0 := by
    by_contra h0
    have h := congrArg (fun g => toAdd (g (π i0))) haxis
    rw [hr (axisVec (p := p) i0) i0, axisVec_self, toAdd_ofAdd, mul_one,
      axisVec_of_ne h0, toAdd_one] at h
    exact coord_sign_ne_zero hp (hsign i0) h
  have hεi0 : ε i0 = 1 := by
    have h := congrArg (fun g => toAdd (g (π i0))) haxis
    rw [hr (axisVec (p := p) i0) i0, hπi0, axisVec_self, toAdd_ofAdd, mul_one] at h
    exact h
  set U : Fin n → Multiplicative (ZMod p) := u (Pi.mulSingle i (ofAdd 1)) with hU
  have hu1 : U ≠ 1 := by
    rw [hU, Ne, ← map_one u]
    intro h
    have h1 : Pi.mulSingle i (ofAdd (1 : ZMod p)) = 1 := u.injective h
    have h2 := congrArg (fun f => toAdd (f i)) h1
    simp only [toAdd_mulSingle, ↓reduceIte, Pi.one_apply, toAdd_one] at h2
    exact coord_zero_ne_one hp h2.symm
  have hF1 : r U = U⁻¹ := by
    rw [hrdef, hU, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self,
      sgnAut_mulSingle_self, map_inv]
  have hF2 : ∀ g : Fin n → Multiplicative (ZMod p), ∃ e : ℕ, r g * g⁻¹ = U ^ e := by
    intro g
    obtain ⟨h, rfl⟩ := u.surjective g
    refine ⟨(-(2 * toAdd (h i))).val, ?_⟩
    have h1 : sgnAut i h * h⁻¹ = Pi.mulSingle i (ofAdd 1) ^ (-(2 * toAdd (h i))).val := by
      rw [mulSingle_ofAdd_pow, ZMod.natCast_zmod_val, mul_one]
      refine eq_of_toAdd_eq fun j => ?_
      rw [toAdd_mul_apply, toAdd_inv_apply, sgnAut_apply, toAdd_mulSingle]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, toAdd_inv, ite_eq_left rfl]
        ring
      · rw [Function.update_of_ne hj, ite_eq_right hj, add_neg_cancel]
    rw [hrdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, ← map_inv, ← map_mul,
      h1, map_pow]
  have hrδ : ∀ l j, toAdd ((r (Pi.mulSingle l (ofAdd 1)) *
      (Pi.mulSingle l (ofAdd 1))⁻¹ :
      Fin n → Multiplicative (ZMod p)) j) =
      (if j = π l then ε l else 0) - (if j = l then 1 else 0) := by
    intro l j
    rw [toAdd_mul_apply, toAdd_inv_apply, IsSignedPerm.apply_mulSingle hr, toAdd_mulSingle,
      toAdd_mulSingle, mul_one, sub_eq_add_neg]
  by_cases hπ : ∃ a, π a ≠ a
  · exfalso
    obtain ⟨a, ha⟩ := hπ
    have hai0 : a ≠ i0 := by
      rintro rfl
      exact ha (by rw [hπi0])
    have hπai0 : π a ≠ i0 := by
      intro h
      have h2 : a = i0 := π.injective (by rw [h, hπi0])
      exact hai0 h2
    obtain ⟨c, hca, hcπa, hci0⟩ := exists_ne_three hn a (π a) i0
    obtain ⟨e, he⟩ := hF2 (Pi.mulSingle a (ofAdd 1))
    have hea := congrArg (fun f => toAdd (f a)) he
    have hec := congrArg (fun f => toAdd (f c)) he
    rw [hrδ, toAdd_pow_apply, ite_eq_right (Ne.symm ha), ite_eq_left rfl, zero_sub] at hea
    rw [hrδ, toAdd_pow_apply, ite_eq_right hcπa, ite_eq_right hca, sub_zero] at hec
    have he0 : (e : ZMod p) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, neg_eq_zero] at hea
      exact coord_zero_ne_one hp hea.symm
    have huc : toAdd (U c) = 0 := (coord_mul_eq_zero hp hec.symm).resolve_left he0
    obtain ⟨e', he'⟩ := hF2 (Pi.mulSingle c (ofAdd 1))
    have hec' := congrArg (fun f => toAdd (f c)) he'
    rw [hrδ, toAdd_pow_apply, huc, mul_zero, ite_eq_left rfl] at hec'
    have hπc : π c = c := by
      by_contra h
      rw [ite_eq_right (Ne.symm h), zero_sub, neg_eq_zero] at hec'
      exact coord_zero_ne_one hp hec'.symm
    rw [ite_eq_left hπc.symm, sub_eq_zero] at hec'
    have hrc : ∀ x : ZMod p, r (Pi.mulSingle c (ofAdd x)) = Pi.mulSingle c (ofAdd x) := by
      intro x
      rw [IsSignedPerm.apply_mulSingle hr, hπc, hec', one_mul]
    set w : MulAut (Fin n → Multiplicative (ZMod p)) := permAut (Equiv.swap (π a) c) with hw
    have hwW : w ∈ bCoordinateBlock n p i0 :=
      Subgroup.subset_closure (Or.inr ⟨π a, c, hcπa.symm, hπai0, hci0, rfl⟩)
    have hw'B : u⁻¹ * w * u ∈ bCoordinateBlock n p i0 := hu' w hwW
    have hw'sp : IsSignedPerm ⇑(u⁻¹ * w * u) := by
      have h := bCoordinateBlock_le_bSignedFull (p := p) i0 hw'B
      rwa [bSignedFull_eq_signedPermSubgroup] at h
    obtain ⟨π', ε', -, hw'⟩ := hw'sp
    have hcomm := IsSignedPerm.mul_sgnAut hw' i
    have hwr : w * r * w⁻¹ = u * sgnAut (π' i) * u⁻¹ := by
      have e1 : w * r * w⁻¹ =
          u * ((u⁻¹ * w * u) * sgnAut i) * (u⁻¹ * w * u)⁻¹ * u⁻¹ := by
        rw [hrdef]
        group
      rw [e1, hcomm]
      group
    have hF3 : r * (w * r * w⁻¹) = (w * r * w⁻¹) * r := by
      rw [hwr, hrdef]
      calc u * sgnAut i * u⁻¹ * (u * sgnAut (π' i) * u⁻¹) =
            u * (sgnAut i * sgnAut (π' i)) * u⁻¹ := by group
        _ = u * (sgnAut (π' i) * sgnAut i) * u⁻¹ := by rw [sgnAut_mul_comm]
        _ = u * sgnAut (π' i) * u⁻¹ * (u * sgnAut i * u⁻¹) := by group
    have hεa : ε a ≠ 0 := coord_sign_ne_zero hp (hsign a)
    have hwa : w⁻¹ (Pi.mulSingle a (ofAdd 1)) = Pi.mulSingle a (ofAdd 1) := by
      rw [hw, permAut_inv_mulSingle, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne ha.symm hca.symm]
    have hra : r (Pi.mulSingle a (ofAdd 1)) = Pi.mulSingle (π a) (ofAdd (ε a)) := by
      rw [IsSignedPerm.apply_mulSingle hr, mul_one]
    have hwb : ∀ x, w (Pi.mulSingle (π a) x) = Pi.mulSingle c x := fun x => by
      rw [hw, permAut_mulSingle, Equiv.swap_apply_left]
    have hwc : ∀ x, w (Pi.mulSingle c x) = Pi.mulSingle (π a) x := fun x => by
      rw [hw, permAut_mulSingle, Equiv.swap_apply_right]
    have hwb' : ∀ x, w⁻¹ (Pi.mulSingle (π a) x) = Pi.mulSingle c x := fun x => by
      rw [hw, permAut_inv_mulSingle, Equiv.swap_inv, Equiv.swap_apply_left]
    have h1 := congrArg (fun g : MulAut (Fin n → Multiplicative (ZMod p)) =>
      g (Pi.mulSingle a (ofAdd 1))) hF3
    simp only [MulAut.mul_apply] at h1
    rw [hwa, hra, hwb, hrc, hwb', hrc, hwc] at h1
    exact hcπa (mulSingle_ofAdd_eq_iff hεa h1).1
  · push Not at hπ
    have hdiag : ∀ f l, toAdd (r f l) = ε l * toAdd (f l) := fun f l => by
      have := hr f l
      rwa [hπ l] at this
    have hsupp : ∀ l, toAdd (U l) ≠ 0 → ε l = -1 := by
      intro l hl
      have h1 := hdiag U l
      rw [hF1, toAdd_inv_apply] at h1
      rcases hsign l with h | h
      · rw [h, one_mul] at h1
        exact absurd (coord_eq_zero_of_eq_neg hp hp2 h1.symm) hl
      · exact h
    obtain ⟨l₀, hl₀⟩ : ∃ l₀, toAdd (U l₀) ≠ 0 := by
      by_contra h
      push Not at h
      exact hu1 (funext fun l => toAdd.injective (by rw [h l, Pi.one_apply, toAdd_one]))
    have hl₀i0 : l₀ ≠ i0 := by
      intro h0
      have h1 : ε l₀ = -1 := hsupp l₀ hl₀
      rw [h0, hεi0] at h1
      have h2 : (2 : ZMod p) = 0 := by linear_combination h1
      exact coord_two_ne_zero hp hp2 h2
    refine ⟨l₀, toAdd (U l₀), hl₀i0, hl₀, ?_⟩
    refine eq_of_toAdd_eq fun l => ?_
    rw [toAdd_mulSingle]
    by_cases hl : l = l₀
    · rw [hl, if_pos rfl]
    · rw [if_neg hl]
      by_contra hul
      obtain ⟨e, he⟩ := hF2 (Pi.mulSingle l₀ (ofAdd 1))
      have hel₀ := congrArg (fun f => toAdd (f l₀)) he
      have hel := congrArg (fun f => toAdd (f l)) he
      rw [hrδ, toAdd_pow_apply, hπ, ite_eq_left rfl, if_pos rfl, hsupp l₀ hl₀] at hel₀
      rw [hrδ, toAdd_pow_apply, hπ, ite_eq_right hl, ite_eq_right hl, sub_zero] at hel
      have he0 : (e : ZMod p) = 0 := (coord_mul_eq_zero hp hel.symm).resolve_right hul
      rw [he0, zero_mul] at hel₀
      exact coord_two_ne_zero hp hp2 (by linear_combination -hel₀)


private theorem exists_mulSingle_axisVec_of_normalizes {i0 : Fin n}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : ∀ w ∈ bCoordinateBlock n p i0, u * w * u⁻¹ ∈ bCoordinateBlock n p i0)
    (hu' : ∀ w ∈ bCoordinateBlock n p i0, u⁻¹ * w * u ∈ bCoordinateBlock n p i0) :
    ∃ c : ZMod p, c ≠ 0 ∧
      u (axisVec (p := p) i0) = Pi.mulSingle i0 (ofAdd c) := by
  have hfix : ∀ k, k ≠ i0 → u (axisVec (p := p) i0) k = 1 := by
    intro k hk
    have hf : ∀ w ∈ bCoordinateBlock n p i0,
        w (u (axisVec (p := p) i0)) = u (axisVec (p := p) i0) := by
      intro w hw
      have h1 : (u⁻¹ * w * u) (axisVec (p := p) i0) = axisVec (p := p) i0 :=
        mem_bCoordinateBlock_fix hp hp2 (hu' w hw) (fun m hm => axisVec_of_ne hm)
      calc w (u (axisVec (p := p) i0))
          = u (u⁻¹ (w (u (axisVec (p := p) i0)))) :=
              (MulAut.apply_inv_self (M := Fin n → Multiplicative (ZMod p)) u _).symm
        _ = u ((u⁻¹ * w * u) (axisVec (p := p) i0)) := by
              rw [MulAut.mul_apply, MulAut.mul_apply]
        _ = u (axisVec (p := p) i0) := by rw [h1]
    exact (forall_bCoordinateBlock_fix_iff hp hp2 i0 _).mp hf k hk
  have hne : u (axisVec (p := p) i0) ≠ 1 := by
    rw [Ne, ← map_one u]
    intro h
    have h1 : axisVec (p := p) i0 = 1 := u.injective h
    have h2 := congrArg (fun f => toAdd (f i0)) h1
    rw [axisVec_self, Pi.one_apply] at h2
    exact coord_zero_ne_one hp (by simpa using h2.symm)
  refine ⟨toAdd (u (axisVec (p := p) i0) i0), ?_, ?_⟩
  · intro h0
    exact hne (eq_of_toAdd_eq fun k => by
      by_cases hk : k = i0
      · rw [hk, h0, Pi.one_apply, toAdd_one]
      · rw [hfix k hk, Pi.one_apply, toAdd_one])
  · refine eq_of_toAdd_eq fun k => ?_
    by_cases hk : k = i0
    · rw [hk, Pi.mulSingle_eq_same, toAdd_ofAdd]
    · rw [hfix k hk, Pi.mulSingle_eq_of_ne hk, toAdd_one]

private theorem exists_sign_mul_of_normalizes {i0 : Fin n}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : ∀ w ∈ bCoordinateBlock n p i0, u * w * u⁻¹ ∈ bCoordinateBlock n p i0)
    {i i' : Fin n} (hi : i ≠ i0) (hi' : i' ≠ i0) (hii' : i ≠ i')
    {j j' : Fin n} {c c' : ZMod p}
    (hc : u (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle j (ofAdd c))
    (hc' : u (Pi.mulSingle i' (ofAdd 1)) = Pi.mulSingle j' (ofAdd c'))
    (hcc : c ≠ 0) :
    ∃ s : ZMod p, (s = 1 ∨ s = -1) ∧ c' = s * c := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have ht : permAut (Equiv.swap i i') ∈ bCoordinateBlock n p i0 :=
    Subgroup.subset_closure (Or.inr ⟨i, i', hii', hi, hi', rfl⟩)
  have hvW : u * permAut (Equiv.swap i i') * u⁻¹ ∈ bCoordinateBlock n p i0 := hu _ ht
  set v : MulAut (Fin n → Multiplicative (ZMod p)) := u * permAut (Equiv.swap i i') * u⁻¹
    with hvdef
  have hvsp : IsSignedPerm ⇑v := by
    have h := bCoordinateBlock_le_bSignedFull (p := p) i0 hvW
    rwa [bSignedFull_eq_signedPermSubgroup] at h
  obtain ⟨π, ε, hsign, hπ⟩ := hvsp
  have h1 : v (u (Pi.mulSingle i (ofAdd 1))) = u (Pi.mulSingle i' (ofAdd 1)) := by
    rw [hvdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, permAut_mulSingle,
      Equiv.swap_apply_left]
  rw [hc, hc', IsSignedPerm.apply_mulSingle hπ] at h1
  obtain ⟨-, hval⟩ := mulSingle_ofAdd_eq_iff (x := ε j * c) (y := c')
    (coord_mul_ne_zero hp (coord_sign_ne_zero hp (hsign j)) hcc) h1
  exact ⟨ε j, hsign j, hval.symm⟩

private theorem diagAut_mem_bCoordinateBlock_of_fix {i0 : Fin n} {ε : Fin n → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hε0 : ε i0 = 1) :
    diagAut ε (fun i => coord_sign_mul_self (hε i)) ∈ bCoordinateBlock n p i0 := by
  classical
  have key : ∀ (s : Finset (Fin n)), (∀ i ∈ s, i ≠ i0) →
      ∀ (u : MulAut (Fin n → Multiplicative (ZMod p))) (ε' : Fin n → ZMod p),
        (∀ i, ε' i = 1 ∨ ε' i = -1) → (∀ i, i ∉ s → ε' i = 1) →
        (∀ f i, toAdd (u f i) = ε' i * toAdd (f i)) → u ∈ bCoordinateBlock n p i0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _hs u ε' _ hS hu
        have h1 : u = 1 := by
          refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
          rw [hu, hS i (Finset.notMem_empty i), one_mul]
          rfl
        rw [h1]
        exact Subgroup.one_mem _
    | insert a s ha ih =>
        intro hs u ε' hε' hS hu
        have haj : a ≠ i0 := hs a (Finset.mem_insert_self a s)
        have hs' : ∀ i ∈ s, i ≠ i0 := fun i hi => hs i (Finset.mem_insert_of_mem hi)
        rcases hε' a with hεa | hεa
        · refine ih hs' u ε' hε' (fun i hi => ?_) hu
          by_cases hia : i = a
          · rw [hia, hεa]
          · exact hS i (by simp [hia, hi])
        · have h1 : u * sgnAut a ∈ bCoordinateBlock n p i0 := by
            refine ih hs' _ (Function.update ε' a 1) (fun i => ?_) (fun i hi => ?_)
              (fun f i => ?_)
            · by_cases hia : i = a
              · subst hia
                simp
              · rw [Function.update_of_ne hia]
                exact hε' i
            · by_cases hia : i = a
              · subst hia
                simp
              · rw [Function.update_of_ne hia]
                exact hS i (by simp [hia, hi])
            · rw [MulAut.mul_apply, hu, sgnAut_apply]
              by_cases hia : i = a
              · subst hia
                simp [hεa]
              · rw [Function.update_of_ne hia, Function.update_of_ne hia]
          have h2 := Subgroup.mul_mem _ h1
            (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl ⟨a, haj, rfl⟩)))
          rwa [mul_inv_cancel_right] at h2
  refine key (Finset.univ.erase i0) (fun i hi => (Finset.mem_erase.mp hi).1) _ ε hε
    (fun i hi => ?_) (fun f i => by rw [diagAut_apply, toAdd_ofAdd])
  have h : i = i0 := by simpa using hi
  rw [h]
  exact hε0

private theorem permAut_mem_bCoordinateBlock_of_fix {i0 : Fin n} {π : Equiv.Perm (Fin n)}
    (hπ : π i0 = i0) : permAut π ∈ bCoordinateBlock n p i0 := by
  classical
  have hmem : ∀ i : Fin n, i ≠ i0 ↔ π i ≠ i0 := by
    intro i
    constructor
    · intro hi h
      exact hi (π.injective (by rw [h, hπ]))
    · intro hi h
      rw [h] at hi
      exact hi hπ
  set σ : Equiv.Perm {j : Fin n // j ≠ i0} := π.subtypePerm (fun i => (hmem i).symm) with hσ
  have hπeq : Equiv.Perm.ofSubtype σ = π := by
    rw [hσ]
    refine Equiv.Perm.ofSubtype_subtypePerm (fun i => (hmem i).symm) (fun x hx => ?_)
    rintro rfl
    exact hx hπ
  have hswap : ∀ x y : {j : Fin n // j ≠ i0},
      (Equiv.Perm.ofSubtype (Equiv.swap x y) : Equiv.Perm (Fin n)) =
        Equiv.swap (x : Fin n) (y : Fin n) := by
    intro x y
    refine Equiv.ext fun i => ?_
    by_cases hi0 : i = i0
    · rw [hi0, Equiv.Perm.ofSubtype_apply_of_not_mem (a := i0) (Equiv.swap x y) (by simp)]
      exact (Equiv.swap_apply_of_ne_of_ne x.2.symm y.2.symm).symm
    · rw [show (Equiv.Perm.ofSubtype (Equiv.swap x y)) i
            = (Equiv.Perm.ofSubtype (Equiv.swap x y))
              (⟨i, hi0⟩ : {j : Fin n // j ≠ i0}) from rfl,
        Equiv.Perm.ofSubtype_apply_coe, Equiv.swap_apply_def, Equiv.swap_apply_def,
        apply_ite Subtype.val, apply_ite Subtype.val]
      by_cases hx : i = (x : Fin n)
      · rw [if_pos (show (⟨i, hi0⟩ : {j : Fin n // j ≠ i0}) = x from Subtype.ext hx), if_pos hx]
      · rw [if_neg (fun h => hx (congrArg Subtype.val h)), if_neg hx]
        by_cases hy : i = (y : Fin n)
        · rw [if_pos (show (⟨i, hi0⟩ : {j : Fin n // j ≠ i0}) = y from Subtype.ext hy),
            if_pos hy]
        · rw [if_neg (fun h => hy (congrArg Subtype.val h)), if_neg hy]
  have key : ∀ τ : Equiv.Perm {j : Fin n // j ≠ i0},
      permAut (Equiv.Perm.ofSubtype τ) ∈ bCoordinateBlock n p i0 := by
    intro τ
    induction τ using Equiv.Perm.swap_induction_on with
    | one =>
        have h1 : (Equiv.Perm.ofSubtype (1 : Equiv.Perm {j : Fin n // j ≠ i0}) :
            Equiv.Perm (Fin n)) = 1 := by rw [map_one]
        rw [h1]
        have h2 : (permAut (1 : Equiv.Perm (Fin n)) :
            MulAut (Fin n → Multiplicative (ZMod p))) = 1 :=
          map_one (TypeBDatum.permAutHom n p)
        rw [h2]
        exact Subgroup.one_mem _
    | swap_mul τ x y hxy ih =>
        change (TypeBDatum.permAutHom n p) (Equiv.Perm.ofSubtype (Equiv.swap x y * τ)) ∈
          bCoordinateBlock n p i0
        rw [map_mul, map_mul]
        refine Subgroup.mul_mem _ ?_ ih
        rw [hswap x y]
        refine Subgroup.subset_closure (Or.inr ⟨x.1, y.1, ?_, x.2, y.2, rfl⟩)
        intro h
        exact hxy (Subtype.ext h)
  rw [← hπeq]
  exact key σ

private def scaleHom (γ : ZMod p) :
    (Fin n → Multiplicative (ZMod p)) →* (Fin n → Multiplicative (ZMod p)) where
  toFun f i := ofAdd (γ * toAdd (f i))
  map_one' := by
    funext i
    simp
  map_mul' f g := by
    funext i
    rw [Pi.mul_apply, Pi.mul_apply, toAdd_mul, mul_add, ofAdd_add]

private theorem scaleHom_apply (γ : ZMod p) (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    scaleHom (p := p) γ f i = ofAdd (γ * toAdd (f i)) :=
  rfl

private theorem scaleHom_mulSingle (γ : ZMod p) (j : Fin n) (c : ZMod p) :
    scaleHom (p := p) γ (Pi.mulSingle j (ofAdd c)) = Pi.mulSingle j (ofAdd (γ * c)) := by
  refine eq_of_toAdd_eq fun m => ?_
  rw [scaleHom_apply, toAdd_ofAdd, toAdd_mulSingle, toAdd_mulSingle]
  by_cases hm : m = j
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, mul_zero]

private theorem scaleHom_comp_pow (γ : ZMod p) (w : MulAut (Fin n → Multiplicative (ZMod p)))
    (a : Fin n → Multiplicative (ZMod p)) (k : ℕ) :
    scaleHom (p := p) γ (w (a ^ k)) = (scaleHom (p := p) γ (w a)) ^ k := by
  rw [map_pow, map_pow]

private theorem exists_perm_extend {i0 : Fin n}
    {σ : {i : Fin n // i ≠ i0} → {j : Fin n // j ≠ i0}} (hσinj : Function.Injective σ) :
    ∃ π : Equiv.Perm (Fin n), π i0 = i0 ∧
      ∀ (i : Fin n) (hi : i ≠ i0), π i = (σ ⟨i, hi⟩ : Fin n) := by
  set πf : Fin n → Fin n := fun i => if h : i = i0 then i0 else (σ ⟨i, h⟩ : Fin n) with hπfdef
  have hπf_i0 : πf i0 = i0 := by rw [hπfdef]; simp
  have hπf_apply : ∀ (i : Fin n) (hi : i ≠ i0), πf i = (σ ⟨i, hi⟩ : Fin n) := by
    intro i hi
    rw [hπfdef]
    simp only [dif_neg hi]
  have hπf_ne : ∀ (i : Fin n) (hi : i ≠ i0), πf i ≠ i0 := by
    intro i hi
    rw [hπf_apply i hi]
    exact (σ ⟨i, hi⟩).2
  have hπf_inj : Function.Injective πf := by
    intro i j hij
    by_cases hi : i = i0
    · have h1 : πf j = i0 := by rw [← hij, hi, hπf_i0]
      have hj : j = i0 := by
        by_contra hj
        exact hπf_ne j hj h1
      rw [hi, hj]
    · by_cases hj : j = i0
      · have h1 : πf i = i0 := by rw [hij, hj, hπf_i0]
        have hi' : i = i0 := by
          by_contra hi'
          exact hπf_ne i hi' h1
        exact absurd hi' hi
      · have h1 : (σ ⟨i, hi⟩ : Fin n) = (σ ⟨j, hj⟩ : Fin n) := by
          rw [← hπf_apply i hi, ← hπf_apply j hj, hij]
        exact Subtype.ext_iff.mp (hσinj (Subtype.ext h1))
  let π : Equiv.Perm (Fin n) :=
    Equiv.ofBijective πf ⟨hπf_inj, Finite.surjective_of_injective hπf_inj⟩
  have hπapply : ∀ i, π i = πf i := fun i => rfl
  refine ⟨π, ?_, ?_⟩
  · rw [hπapply, hπf_i0]
  · intro i hi
    rw [hπapply, hπf_apply i hi]

private theorem exists_signs_of_ratio {i0 : Fin n} {γ : ZMod p} (hγ : γ ≠ 0)
    {d : {i : Fin n // i ≠ i0} → ZMod p} {j0 : {i : Fin n // i ≠ i0}} (hbase : γ = d j0)
    (hratio : ∀ x y : {i : Fin n // i ≠ i0}, x ≠ y →
      ∃ s : ZMod p, (s = 1 ∨ s = -1) ∧ d y = s * d x) :
    ∃ ε : Fin n → ZMod p, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ε i0 = 1 ∧
      ∀ (i : Fin n) (hi : i ≠ i0), d ⟨i, hi⟩ = γ * ε i := by
  classical
  set ε : Fin n → ZMod p :=
    fun i => if h : i = i0 then 1 else if d ⟨i, h⟩ = γ then 1 else -1 with hεdef
  have hεi0 : ε i0 = 1 := by rw [hεdef]; simp
  have hεval : ∀ (i : Fin n) (hi : i ≠ i0),
      ε i = if d ⟨i, hi⟩ = γ then 1 else -1 := by
    intro i hi
    rw [hεdef]
    simp only [dif_neg hi]
  have hεsign : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    by_cases hi : i = i0
    · exact Or.inl (by rw [hi, hεi0])
    · rw [hεval i hi]
      split_ifs with h
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hεd : ∀ (i : Fin n) (hi : i ≠ i0), d ⟨i, hi⟩ = γ * ε i := by
    intro i hi
    rw [hεval i hi]
    by_cases heq : d ⟨i, hi⟩ = γ
    · rw [if_pos heq, mul_one]
      exact heq
    · rw [if_neg heq]
      by_cases heqi : (⟨i, hi⟩ : {j : Fin n // j ≠ i0}) = j0
      · exfalso
        exact heq (by rw [hbase, heqi])
      · obtain ⟨s, hs, hsd⟩ := hratio ⟨i, hi⟩ j0 heqi
        rcases hs with rfl | rfl
        · exfalso
          exact heq (by rw [hbase, hsd, one_mul])
        · rw [hbase, hsd]
          ring
  exact ⟨ε, hεsign, hεi0, hεd⟩

private theorem smul_of_basis_data [NeZero p] {i0 : Fin n}
    {u w : MulAut (Fin n → Multiplicative (ZMod p))} {γ : ZMod p}
    {ε : Fin n → ZMod p} {π : Equiv.Perm (Fin n)}
    {σ : {i : Fin n // i ≠ i0} → {j : Fin n // j ≠ i0}} {d : {i : Fin n // i ≠ i0} → ZMod p}
    (hσ : ∀ i : {i : Fin n // i ≠ i0},
      u (Pi.mulSingle (i : Fin n) (ofAdd 1)) =
        Pi.mulSingle (σ i : Fin n) (ofAdd (d i)))
    (hεd : ∀ (i : Fin n) (hi : i ≠ i0), d ⟨i, hi⟩ = γ * ε i)
    (hεi0 : ε i0 = 1) (hπi0 : π i0 = i0)
    (hπ_off : ∀ (i : Fin n) (hi : i ≠ i0), π i = (σ ⟨i, hi⟩ : Fin n))
    (hw_gen : ∀ i : Fin n,
      w (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle (π i) (ofAdd (ε i)))
    (d0 : ZMod p) (haxis : u (Pi.mulSingle i0 (ofAdd 1)) = Pi.mulSingle i0 (ofAdd d0)) :
    ∀ (f : Fin n → Multiplicative (ZMod p)) (k : Fin n), k ≠ i0 →
      toAdd (u f k) = γ * toAdd (w f k) := by
  have hD_gen : ∀ i : Fin n, scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))) =
      scaleHom (p := p) γ (Pi.mulSingle (π i) (ofAdd (ε i))) := by
    intro i
    rw [hw_gen]
  have hΦgen : ∀ i : Fin n, ∀ m, m ≠ i0 →
      (u (Pi.mulSingle i (ofAdd 1)) *
        (scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))))⁻¹) m = 1 := by
    intro i m hm
    rw [Pi.mul_apply, Pi.inv_apply]
    by_cases hi : i = i0
    · rw [hi, show u (Pi.mulSingle i0 (ofAdd 1)) = Pi.mulSingle i0 (ofAdd d0) from haxis]
      have hD0 : scaleHom (p := p) γ (w (Pi.mulSingle i0 (ofAdd 1))) =
          Pi.mulSingle i0 (ofAdd γ) := by
        rw [hD_gen, hπi0, hεi0, scaleHom_mulSingle]
        simp
      rw [hD0, Pi.mulSingle_eq_of_ne hm, Pi.mulSingle_eq_of_ne hm]
      exact mul_inv_cancel 1
    · have hD0 : scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))) =
          Pi.mulSingle (σ ⟨i, hi⟩ : Fin n) (ofAdd (γ * ε i)) := by
        rw [hD_gen, hπ_off i hi, scaleHom_mulSingle]
      rw [hD0, show u (Pi.mulSingle i (ofAdd 1)) =
          Pi.mulSingle (σ ⟨i, hi⟩ : Fin n) (ofAdd (d ⟨i, hi⟩)) from hσ ⟨i, hi⟩]
      by_cases hmj : m = (σ ⟨i, hi⟩ : Fin n)
      · rw [hmj, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, ← hεd i hi]
        exact mul_inv_cancel _
      · rw [Pi.mulSingle_eq_of_ne hmj, Pi.mulSingle_eq_of_ne hmj]
        exact mul_inv_cancel 1
  have hpt : ∀ (i m : Fin n), m ≠ i0 →
      u (Pi.mulSingle i (ofAdd 1)) m *
        (scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))) m)⁻¹ = 1 := by
    intro i m hm
    have h := hΦgen i m hm
    rwa [Pi.mul_apply, Pi.inv_apply] at h
  intro f k hk
  have hΦf : ∀ m, m ≠ i0 → (u f * (scaleHom (p := p) γ (w f))⁻¹) m = 1 := by
    intro m hm
    have hf : f = ∏ i, Pi.mulSingle i (f i) := (Finset.univ_prod_mulSingle f).symm
    have hpow : ∀ i : Fin n, Pi.mulSingle i (f i) =
        (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod p)) ^
          (toAdd (f i)).val := by
      intro i
      conv_lhs => rw [← ofAdd_toAdd (f i)]
      rw [mulSingle_ofAdd_eq_pow]
    have h1 : (u f) m = ∏ i, ((u (Pi.mulSingle i (ofAdd 1))) m) ^ (toAdd (f i)).val := by
      conv_lhs => rw [hf]
      rw [map_prod, Finset.prod_apply]
      exact Finset.prod_congr rfl fun i _ => by rw [hpow i, map_pow, Pi.pow_apply]
    have h2 : (scaleHom (p := p) γ (w f)) m =
        ∏ i, ((scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1)))) m) ^
          (toAdd (f i)).val := by
      have hwf : w f = ∏ i, w (Pi.mulSingle i (f i)) := by
        conv_lhs => rw [hf]
        rw [map_prod]
      conv_lhs => rw [hwf]
      rw [map_prod, Finset.prod_apply]
      exact Finset.prod_congr rfl fun i _ => by
        rw [hpow i, scaleHom_comp_pow, Pi.pow_apply]
    have h3 : ∏ i, ((u (Pi.mulSingle i (ofAdd 1))) m) ^ (toAdd (f i)).val =
        ∏ i, ((scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1)))) m) ^
          (toAdd (f i)).val := by
      refine Finset.prod_congr rfl fun i _ => ?_
      have h := hpt i m hm
      have hab : u (Pi.mulSingle i (ofAdd 1)) m =
          scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))) m := by
        calc u (Pi.mulSingle i (ofAdd 1)) m
            = u (Pi.mulSingle i (ofAdd 1)) m *
                (scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))) m)⁻¹ *
                scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))) m := by
              rw [mul_assoc, inv_mul_cancel, mul_one]
          _ = 1 * scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))) m := by rw [h]
          _ = scaleHom (p := p) γ (w (Pi.mulSingle i (ofAdd 1))) m := one_mul _
      rw [hab]
    rw [Pi.mul_apply, Pi.inv_apply, h1, h2, h3]
    exact mul_inv_cancel _
  have hk' : u f k = scaleHom (p := p) γ (w f) k := by
    have h1 := hΦf k hk
    rw [Pi.mul_apply, Pi.inv_apply] at h1
    calc u f k
        = u f k * (scaleHom (p := p) γ (w f) k)⁻¹ * scaleHom (p := p) γ (w f) k := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = 1 * scaleHom (p := p) γ (w f) k := by rw [h1]
      _ = scaleHom (p := p) γ (w f) k := one_mul _
  rw [hk', scaleHom_apply, toAdd_ofAdd]

theorem exists_smul_mem_bCoordinateBlock_of_normalizes {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (i0 : Fin n) {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : ∀ w ∈ bCoordinateBlock n p i0, u * w * u⁻¹ ∈ bCoordinateBlock n p i0) :
    ∃ (γ : ZMod p) (w : MulAut (Fin n → Multiplicative (ZMod p))),
      w ∈ bCoordinateBlock n p i0 ∧
        ∀ (f : Fin n → Multiplicative (ZMod p)) (k : Fin n), k ≠ i0 →
          toAdd (u f k) = γ * toAdd (w f k) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hu' : ∀ w ∈ bCoordinateBlock n p i0, u⁻¹ * w * u ∈ bCoordinateBlock n p i0 :=
    map_conj_inv_le hu
  have hsub : ∀ i : {i : Fin n // i ≠ i0}, ∃ j : {j : Fin n // j ≠ i0}, ∃ c : ZMod p,
      c ≠ 0 ∧ u (Pi.mulSingle (i : Fin n) (ofAdd 1)) = Pi.mulSingle (j : Fin n) (ofAdd c) := by
    intro i
    obtain ⟨j, c, hj, hc, he⟩ :=
      exists_mulSingle_of_normalizes_bCoordinateBlock hp hp2 hn hu hu' i.2
    exact ⟨⟨j, hj⟩, c, hc, he⟩
  choose σ d hd hσ using hsub
  obtain ⟨d0, hd0, haxis⟩ := exists_mulSingle_axisVec_of_normalizes hp hp2 hu hu'
  have hσinj : Function.Injective σ := by
    intro x y hxy
    by_contra hne
    have hdx : d x ≠ 0 := hd x
    obtain ⟨t, ht⟩ := exists_natCast_mul_eq hp hdx (d y)
    have htne : (t : ZMod p) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at ht
      exact hd y ht.symm
    have h1 : u ((Pi.mulSingle (x : Fin n) (ofAdd 1)) ^ t)
        = u (Pi.mulSingle (y : Fin n) (ofAdd 1)) := by
      rw [map_pow, hσ x, hσ y, mulSingle_ofAdd_pow, ht, hxy]
    have h2 := u.injective h1
    rw [mulSingle_ofAdd_pow, mul_one] at h2
    exact hne (Subtype.ext (mulSingle_ofAdd_eq_iff (a := (x : Fin n)) (b := (y : Fin n))
      htne h2).1)
  obtain ⟨c0, hc0, -, -⟩ := exists_ne_three hn i0 i0 i0
  let j0 : {i : Fin n // i ≠ i0} := ⟨c0, hc0⟩
  set γ : ZMod p := d j0 with hγdef
  have hγ : γ ≠ 0 := hd j0
  have hratio : ∀ x y : {i : Fin n // i ≠ i0}, x ≠ y →
      ∃ s : ZMod p, (s = 1 ∨ s = -1) ∧ d y = s * d x := by
    intro x y hxy
    exact exists_sign_mul_of_normalizes hp hp2 hu x.2 y.2
      (fun h => hxy (Subtype.ext h)) (hσ x) (hσ y) (hd x)
  obtain ⟨ε, hεsign, hεi0, hεd⟩ := exists_signs_of_ratio hγ hγdef hratio
  obtain ⟨π, hπi0, hπ_off⟩ := exists_perm_extend hσinj
  set w : MulAut (Fin n → Multiplicative (ZMod p)) :=
    permAut π * diagAut ε (fun i => coord_sign_mul_self (hεsign i)) with hwdef
  have hw_mem : w ∈ bCoordinateBlock n p i0 := by
    rw [hwdef]
    exact Subgroup.mul_mem _ (permAut_mem_bCoordinateBlock_of_fix hπi0)
      (diagAut_mem_bCoordinateBlock_of_fix hεsign hεi0)
  have hw_gen : ∀ i : Fin n,
      w (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle (π i) (ofAdd (ε i)) := by
    intro i
    rw [hwdef, MulAut.mul_apply, diagAut_mulSingle, permAut_mulSingle, mul_one]
  refine ⟨γ, w, hw_mem, ?_⟩
  intro f k hk
  exact smul_of_basis_data hσ hεd hεi0 hπi0 hπ_off hw_gen d0 haxis f k hk

theorem exists_eq_sgnAut_of_mem_bCoordinateBlock_of_commute_conj
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {i0 : Fin n} {t : MulAut (Fin n → Multiplicative (ZMod p))}
    (ht : t ∈ bCoordinateBlock n p i0)
    (hrefl : t ^ 2 = 1 ∧
      Nat.card {f : Fin n → Multiplicative (ZMod p) // t f = f} * p =
        Nat.card (Fin n → Multiplicative (ZMod p)))
    (hcomm : ∀ w ∈ bCoordinateBlock n p i0, Commute (w * t * w⁻¹) t) :
    ∃ i : Fin n, i ≠ i0 ∧ t = SpCoord.sgnAut i := by
  classical
  have haxis : t (axisVec (p := p) i0) = axisVec (p := p) i0 :=
    mem_bCoordinateBlock_fix hp hp2 ht (fun k hk => axisVec_of_ne hk)
  rcases eq_sgnAut_or_swap_of_isRefl hp hp2 (bCoordinateBlock_le_bSignedFull i0 ht)
    hrefl.1 hrefl.2 with ⟨i, hi⟩ | ⟨a, b, hab, hi | hi⟩
  · refine ⟨i, ?_, hi⟩
    intro hii0
    have hmem : SpCoord.sgnAut i ∈ bCoordinateBlock n p i := by
      rw [← hi, hii0]
      exact ht
    exact sgnAut_not_mem_bCoordinateBlock hp hp2 i hmem
  · exfalso
    have hb0 : b ≠ i0 := by
      intro hbi0
      subst hbi0
      have h := congrArg (fun f : Fin n → Multiplicative (ZMod p) => toAdd (f a)) haxis
      rw [hi, permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left,
        axisVec, Pi.mulSingle_eq_same, toAdd_ofAdd, Pi.mulSingle_eq_of_ne hab,
        toAdd_one] at h
      exact coord_zero_ne_one hp h.symm
    obtain ⟨c, hca, hcb, hci0⟩ := exists_ne_three hn a b i0
    have hbc : b ≠ c := hcb.symm
    set w : MulAut (Fin n → Multiplicative (ZMod p)) := permAut (Equiv.swap b c) with hwdef
    have hw : w ∈ bCoordinateBlock n p i0 :=
      Subgroup.subset_closure (Or.inr ⟨b, c, hbc, hb0, hci0, rfl⟩)
    have hw_a : w⁻¹ (Pi.mulSingle a (ofAdd 1)) = Pi.mulSingle a (ofAdd 1) := by
      rw [hwdef, permAut_inv_mulSingle, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne hab hca.symm]
    have hw_b : w⁻¹ (Pi.mulSingle b (ofAdd 1)) = Pi.mulSingle c (ofAdd 1) := by
      rw [hwdef, permAut_inv_mulSingle, Equiv.swap_inv, Equiv.swap_apply_left]
    have hw_b' : w (Pi.mulSingle b (ofAdd 1)) = Pi.mulSingle c (ofAdd 1) := by
      rw [hwdef, permAut_mulSingle, Equiv.swap_apply_left]
    have hw_c : w (Pi.mulSingle c (ofAdd 1)) = Pi.mulSingle b (ofAdd 1) := by
      rw [hwdef, permAut_mulSingle, Equiv.swap_apply_right]
    have ht_a : t (Pi.mulSingle a (ofAdd 1)) = Pi.mulSingle b (ofAdd 1) := by
      rw [hi, permAut_mulSingle, Equiv.swap_apply_left]
    have ht_c : t (Pi.mulSingle c (ofAdd 1)) = Pi.mulSingle c (ofAdd 1) := by
      rw [hi, permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hca hcb]
    have hwt_a : (w * t * w⁻¹) (Pi.mulSingle a (ofAdd 1)) =
        Pi.mulSingle c (ofAdd 1) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hw_a, ht_a, hw_b']
    have hwt_b : (w * t * w⁻¹) (Pi.mulSingle b (ofAdd 1)) =
        Pi.mulSingle b (ofAdd 1) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hw_b, ht_c, hw_c]
    have hL : (((w * t * w⁻¹) * t) (Pi.mulSingle a (ofAdd 1))) =
        Pi.mulSingle b (ofAdd 1) := by
      rw [MulAut.mul_apply, ht_a, hwt_b]
    have hR : ((t * (w * t * w⁻¹)) (Pi.mulSingle a (ofAdd 1))) =
        Pi.mulSingle c (ofAdd 1) := by
      rw [MulAut.mul_apply, hwt_a, ht_c]
    have he := congrArg
      (fun u : MulAut (Fin n → Multiplicative (ZMod p)) => u (Pi.mulSingle a (ofAdd 1)))
      (hcomm w hw).eq
    rw [hL, hR] at he
    have h := congrArg (fun f : Fin n → Multiplicative (ZMod p) => toAdd (f b)) he
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hcb.symm, toAdd_ofAdd,
      toAdd_one] at h
    exact coord_zero_ne_one hp h.symm
  · exfalso
    have hsinv : (SpCoord.sgnAut a : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ =
        SpCoord.sgnAut a :=
      inv_eq_of_mul_eq_one_left (by simpa [sq] using SpCoord.sgnAut_sq a)
    have hb0 : b ≠ i0 := by
      intro hbi0
      subst hbi0
      have h := congrArg (fun f : Fin n → Multiplicative (ZMod p) => toAdd (f a)) haxis
      rw [hi, hsinv, MulAut.mul_apply, MulAut.mul_apply, axisVec,
        sgnAut_mulSingle_of_ne (Ne.symm hab), permAut_mulSingle, Equiv.swap_apply_right,
        sgnAut_mulSingle_self, ← Pi.mulSingle_inv, ← ofAdd_neg, Pi.mulSingle_eq_same,
        toAdd_ofAdd, Pi.mulSingle_eq_of_ne hab, toAdd_one] at h
      have h0 : (0 : ZMod p) = 1 := by linear_combination h
      exact coord_zero_ne_one hp h0
    obtain ⟨c, hca, hcb, hci0⟩ := exists_ne_three hn a b i0
    have hbc : b ≠ c := hcb.symm
    set w : MulAut (Fin n → Multiplicative (ZMod p)) := permAut (Equiv.swap b c) with hwdef
    have hw : w ∈ bCoordinateBlock n p i0 :=
      Subgroup.subset_closure (Or.inr ⟨b, c, hbc, hb0, hci0, rfl⟩)
    have hw_a : w⁻¹ (Pi.mulSingle a (ofAdd 1)) = Pi.mulSingle a (ofAdd 1) := by
      rw [hwdef, permAut_inv_mulSingle, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne hab hca.symm]
    have hw_b : w⁻¹ (Pi.mulSingle b (ofAdd 1)) = Pi.mulSingle c (ofAdd 1) := by
      rw [hwdef, permAut_inv_mulSingle, Equiv.swap_inv, Equiv.swap_apply_left]
    have hw_b' : w (Pi.mulSingle b (ofAdd 1)) = Pi.mulSingle c (ofAdd 1) := by
      rw [hwdef, permAut_mulSingle, Equiv.swap_apply_left]
    have hw_c : w (Pi.mulSingle c (ofAdd 1)) = Pi.mulSingle b (ofAdd 1) := by
      rw [hwdef, permAut_mulSingle, Equiv.swap_apply_right]
    have ht_a : t (Pi.mulSingle a (ofAdd 1)) = (Pi.mulSingle b (ofAdd 1))⁻¹ := by
      rw [hi, hsinv, MulAut.mul_apply, MulAut.mul_apply, sgnAut_mulSingle_self, map_inv,
        permAut_mulSingle, Equiv.swap_apply_left, map_inv, sgnAut_mulSingle_of_ne (Ne.symm hab)]
    have ht_c : t (Pi.mulSingle c (ofAdd 1)) = Pi.mulSingle c (ofAdd 1) := by
      rw [hi, hsinv, MulAut.mul_apply, MulAut.mul_apply, sgnAut_mulSingle_of_ne hca,
        permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hca hcb, sgnAut_mulSingle_of_ne hca]
    have hwt_a : (w * t * w⁻¹) (Pi.mulSingle a (ofAdd 1)) =
        (Pi.mulSingle c (ofAdd 1))⁻¹ := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hw_a, ht_a, map_inv, hw_b']
    have hwt_b : (w * t * w⁻¹) (Pi.mulSingle b (ofAdd 1)) =
        Pi.mulSingle b (ofAdd 1) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hw_b, ht_c, hw_c]
    have hL : (((w * t * w⁻¹) * t) (Pi.mulSingle a (ofAdd 1))) =
        (Pi.mulSingle b (ofAdd 1))⁻¹ := by
      rw [MulAut.mul_apply, ht_a, map_inv, hwt_b]
    have hR : ((t * (w * t * w⁻¹)) (Pi.mulSingle a (ofAdd 1))) =
        (Pi.mulSingle c (ofAdd 1))⁻¹ := by
      rw [MulAut.mul_apply, hwt_a, map_inv, ht_c]
    have he := congrArg
      (fun u : MulAut (Fin n → Multiplicative (ZMod p)) => u (Pi.mulSingle a (ofAdd 1)))
      (hcomm w hw).eq
    rw [hL, hR] at he
    have h := congrArg (fun f : Fin n → Multiplicative (ZMod p) => toAdd (f b)) he
    rw [← Pi.mulSingle_inv, ← Pi.mulSingle_inv, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne hcb.symm, toAdd_inv, toAdd_ofAdd, toAdd_one] at h
    have h0 : (1 : ZMod p) = 0 := by linear_combination -h
    exact coord_zero_ne_one hp h0.symm

theorem exists_sgnAut_eq_congr_liftBs {G : Type} [Group G] {Bs : Subgroup G} {n p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {W₀ : Type} [Group W₀]
    (Θ : ((Fin r → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (a : Fin r) :
    ∃ i : Fin n, i ≠ i0 ∧
      MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut a)) = SpCoord.sgnAut i := by
  classical
  set L : MulAut (Fin r → Multiplicative (ZMod p)) →*
      MulAut (Fin n → Multiplicative (ZMod p)) :=
    (MulAut.congr eta).toMonoidHom.comp (TypeBDatum.liftBs Θ) with hLdef
  have hsign : SpCoord.sgnAut a ∈ TypeBDatum.signedAut r p := by
    change SpCoord.sgnAut a ∈ TypeBDatum.signedSupportedAut r p Finset.univ
    exact Subgroup.subset_closure (Or.inl ⟨a, Finset.mem_univ a, rfl⟩)
  have ht : L (SpCoord.sgnAut a) ∈ bCoordinateBlock n p i0 := by
    rw [← hcoord]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hsign)
  have hrefl : L (SpCoord.sgnAut a) ^ 2 = 1 ∧
      Nat.card {f : Fin n → Multiplicative (ZMod p) // L (SpCoord.sgnAut a) f = f} * p =
        Nat.card (Fin n → Multiplicative (ZMod p)) := by
    obtain ⟨h2, hcard⟩ := ggIsReflection_liftBs (p := p) hp hp2 Θ
      (SpCoord.sgnAut_sq a) (SpCoord.card_fix_sgnAut hp hp2 a)
    refine ⟨?_, ?_⟩
    · rw [hLdef, MonoidHom.comp_apply]
      change MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut a)) ^ 2 = 1
      rw [← map_pow, h2, map_one]
    · rw [hLdef, MonoidHom.comp_apply]
      change Nat.card {f : Fin n → Multiplicative (ZMod p) //
          MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut a)) f = f} * p =
        Nat.card (Fin n → Multiplicative (ZMod p))
      rw [card_fixed_congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut a)), hcard,
        Nat.card_congr eta.toEquiv]
  have hcomm : ∀ w ∈ bCoordinateBlock n p i0,
      Commute (w * L (SpCoord.sgnAut a) * w⁻¹) (L (SpCoord.sgnAut a)) := by
    intro w hw
    have hw' : w ∈ ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
        (MulAut.congr eta).toMonoidHom := by
      rw [hcoord]
      exact hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    have hsp : IsSignedPerm ⇑u := by
      rw [TypeBDatum.signedAut_eq_bSignedFull r p] at hu
      rw [bSignedFull_eq_signedPermSubgroup r p] at hu
      change IsSignedPerm ⇑u at hu
      exact hu
    obtain ⟨π, ε, -, hu'⟩ := hsp
    have hconj : u * SpCoord.sgnAut a * u⁻¹ = SpCoord.sgnAut (π a) := by
      rw [IsSignedPerm.mul_sgnAut hu' a]
      group
    have hLconj : L u * L (SpCoord.sgnAut a) * (L u)⁻¹ =
        L (SpCoord.sgnAut (π a)) := by
      rw [← map_inv, ← map_mul, ← map_mul, hconj]
    change Commute (L u * L (SpCoord.sgnAut a) * (L u)⁻¹) (L (SpCoord.sgnAut a))
    rw [commute_iff_eq, hLconj]
    calc L (SpCoord.sgnAut (π a)) * L (SpCoord.sgnAut a)
        = L (SpCoord.sgnAut (π a) * SpCoord.sgnAut a) := (map_mul L _ _).symm
      _ = L (SpCoord.sgnAut a * SpCoord.sgnAut (π a)) := by rw [sgnAut_mul_comm]
      _ = L (SpCoord.sgnAut a) * L (SpCoord.sgnAut (π a)) := map_mul L _ _
  obtain ⟨i, hi0, hi⟩ :=
    exists_eq_sgnAut_of_mem_bCoordinateBlock_of_commute_conj hp hp2 hn ht hrefl hcomm
  exact ⟨i, hi0, by simpa [hLdef] using hi⟩

private theorem eq_one_of_sgnAut_fix {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i : Fin n} {v : Fin n → Multiplicative (ZMod p)}
    (h : SpCoord.sgnAut i v = v) : v i = 1 := by
  have h1 := congrArg (fun g : Fin n → Multiplicative (ZMod p) => toAdd (g i)) h
  rw [SpCoord.sgnAut_apply, Function.update_self, toAdd_inv] at h1
  have hz : toAdd (v i) = 0 := SpCoord.coord_eq_zero_of_eq_neg hp hp2 h1.symm
  exact toAdd.injective (by simpa using hz)

theorem exists_axisEquiv_coord_eq_one_of_bCoordinateBlock_eq
    {G : Type} [Group G] {Bs : Subgroup G} {n p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n) (hrn : r + 1 = n)
    {W₀ : Type} [Group W₀]
    (Θ : ((Fin r → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∃ ι : Fin r ≃ {i : Fin n // i ≠ i0},
      ∀ (b : ↥Bs) (a : Fin r),
        (Θ.symm b).1 a = 1 ↔ eta b (ι a).val = 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  choose idx hidx0 hidx using fun a : Fin r =>
    exists_sgnAut_eq_congr_liftBs hp hp2 hn Θ eta i0 hcoord a

  have hfix {m : ℕ} (i : Fin m)
      (v : Fin m → Multiplicative (ZMod p)) :
      SpCoord.sgnAut i v = v ↔ v i = 1 := by
    constructor
    · exact eq_one_of_sgnAut_fix hp hp2
    · intro hv
      funext j
      rw [SpCoord.sgnAut_apply]
      by_cases hji : j = i
      · subst j
        rw [Function.update_self, hv]
        exact inv_one
      · rw [Function.update_of_ne hji]

  have hzero : ∀ (b : ↥Bs) (a : Fin r),
      (Θ.symm b).1 a = 1 ↔ eta b (idx a) = 1 := by
    intro b a
    obtain ⟨⟨v, c⟩, rfl⟩ := Θ.surjective b
    rw [Θ.symm_apply_apply]
    change v a = 1 ↔ eta (Θ (v, c)) (idx a) = 1
    have hlift : SpCoord.sgnAut a v = v ↔
        TypeBDatum.liftBs Θ (SpCoord.sgnAut a) (Θ (v, c)) = Θ (v, c) := by
      rw [TypeBDatum.liftBs_apply]
      constructor
      · intro h
        rw [h]
      · intro h
        exact congrArg Prod.fst (Θ.injective h)
    calc
      v a = 1 ↔ SpCoord.sgnAut a v = v := (hfix a v).symm
      _ ↔ TypeBDatum.liftBs Θ (SpCoord.sgnAut a) (Θ (v, c)) = Θ (v, c) := hlift
      _ ↔ eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut a) (Θ (v, c))) =
          eta (Θ (v, c)) := ⟨fun h => congrArg eta h, fun h => eta.injective h⟩
      _ ↔ SpCoord.sgnAut (idx a) (eta (Θ (v, c))) = eta (Θ (v, c)) := by
        rw [← hidx a, congr_apply_tau]
      _ ↔ eta (Θ (v, c)) (idx a) = 1 := hfix (idx a) (eta (Θ (v, c)))

  let idx' : Fin r → {i : Fin n // i ≠ i0} := fun a => ⟨idx a, hidx0 a⟩
  have hinj : Function.Injective idx' := by
    intro a a' h
    by_contra haa'
    have hi : idx a = idx a' := congrArg Subtype.val h
    let v : Fin r → Multiplicative (ZMod p) := Pi.mulSingle a (ofAdd (1 : ZMod p))
    let b : ↥Bs := Θ (v, 1)
    have hon : (Θ.symm b).1 a ≠ 1 := by
      intro h1
      have h10 : (1 : ZMod p) = 0 := by
        simpa [b, v] using congrArg Multiplicative.toAdd h1
      exact one_ne_zero h10
    have hoff : (Θ.symm b).1 a' = 1 := by
      simp [b, v, Ne.symm haa']
    apply hon
    apply (hzero b a).mpr
    rw [hi]
    exact (hzero b a').mp hoff

  have hcard : Fintype.card (Fin r) = Fintype.card {i : Fin n // i ≠ i0} := by
    rw [Fintype.card_subtype_compl (fun i : Fin n => i = i0)]
    simp only [Fintype.card_fin, Fintype.card_subtype_eq]
    omega
  have hbij : Function.Bijective idx' :=
    (Fintype.bijective_iff_injective_and_card idx').mpr ⟨hinj, hcard⟩
  refine ⟨Equiv.ofBijective idx' hbij, ?_⟩
  intro b a
  exact hzero b a

theorem exists_one_active_of_bCoordinateBlock_eq {G : Type} [Group G] {Bs : Subgroup G}
    {p n r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {C : Type} [Group C]
    (Θ : ((Fin r → Multiplicative (ZMod p)) × C) ≃* ↥Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (y : ↥Bs) {j : Fin n} (hj : j ≠ i0)
    (hyj : eta y j ≠ 1)
    (hyoff : ∀ i, i ≠ i0 → i ≠ j → eta y i = 1) :
    ∃ a : Fin r, (Θ.symm y).1 a ≠ 1 ∧
      ∀ b, b ≠ a → (Θ.symm y).1 b = 1 := by
  classical
  let f : Fin r → Multiplicative (ZMod p) := (Θ.symm y).1
  let c : C := (Θ.symm y).2
  have hy : Θ (f, c) = y := by
    change Θ (Θ.symm y) = y
    exact Θ.apply_symm_apply y
  have hf_ne : f ≠ 1 := by
    intro hf
    have hfixall : ∀ w ∈ bCoordinateBlock n p i0, w (eta y) = eta y := by
      intro w hw
      have hw' : w ∈ ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
          (MulAut.congr eta).toMonoidHom := by
        rw [hcoord]
        exact hw
      obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw'
      obtain ⟨u, hu, hvu⟩ := Subgroup.mem_map.mp hv
      have hfix_native : TypeBDatum.liftBs Θ u y = y := by
        rw [← hy, TypeBDatum.liftBs_apply, hf, map_one]
      have hfix_img : (MulAut.congr eta).toMonoidHom (TypeBDatum.liftBs Θ u) (eta y) =
          eta y := by
        change MulAut.congr eta (TypeBDatum.liftBs Θ u) (eta y) = eta y
        rw [congr_apply_tau, hfix_native]
      rw [← hvw, ← hvu]
      exact hfix_img
    exact hyj ((forall_bCoordinateBlock_fix_iff hp hp2 i0 (eta y)).mp hfixall j hj)
  obtain ⟨a0, ha0⟩ : ∃ a0 : Fin r, f a0 ≠ 1 := by
    by_contra h
    push Not at h
    exact hf_ne (funext fun a => h a)
  have hsign_eq_j : ∀ a : Fin r, f a ≠ 1 →
      MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut a)) = SpCoord.sgnAut j := by
    intro a ha
    obtain ⟨i, hi0, hi⟩ := exists_sgnAut_eq_congr_liftBs hp hp2 hn Θ eta i0 hcoord a
    have hij : i = j := by
      by_contra hij
      have hyd : eta y i = 1 := hyoff i hi0 hij
      have hfix_i : SpCoord.sgnAut i (eta y) = eta y := by
        funext k
        rw [SpCoord.sgnAut_apply]
        by_cases hk : k = i
        · subst hk
          rw [Function.update_self, hyd, inv_one]
        · rw [Function.update_of_ne hk]
      rw [← hi] at hfix_i
      rw [congr_apply_tau] at hfix_i
      have hlift : TypeBDatum.liftBs Θ (SpCoord.sgnAut a) y = y := eta.injective hfix_i
      rw [← hy] at hlift
      rw [TypeBDatum.liftBs_apply] at hlift
      have hnative : SpCoord.sgnAut a f = f :=
        congrArg Prod.fst (Θ.injective hlift)
      exact ha (eq_one_of_sgnAut_fix hp hp2 hnative)
    simpa [hij] using hi
  refine ⟨a0, ?_, ?_⟩
  · simpa [f] using ha0
  · intro b hb
    by_contra hb1
    have hb1' : f b ≠ 1 := by simpa [f] using hb1
    have hsign_b := hsign_eq_j b hb1'
    have hsign_a0 := hsign_eq_j a0 ha0
    have hlift_eq : TypeBDatum.liftBs Θ (SpCoord.sgnAut b) =
        TypeBDatum.liftBs Θ (SpCoord.sgnAut a0) := by
      apply (MulAut.congr eta).injective
      rw [hsign_b, hsign_a0]
    have hnat : SpCoord.sgnAut b f = SpCoord.sgnAut a0 f := by
      have h1 : TypeBDatum.liftBs Θ (SpCoord.sgnAut b) y =
          TypeBDatum.liftBs Θ (SpCoord.sgnAut a0) y := by rw [hlift_eq]
      rw [← hy] at h1
      rw [TypeBDatum.liftBs_apply, TypeBDatum.liftBs_apply] at h1
      exact congrArg Prod.fst (Θ.injective h1)
    have h0 : f a0 = (f a0)⁻¹ := by
      have h1 := congrArg (fun g : Fin r → Multiplicative (ZMod p) => g a0) hnat
      rw [SpCoord.sgnAut_apply, SpCoord.sgnAut_apply] at h1
      rw [Function.update_of_ne hb.symm, Function.update_self] at h1
      exact h1
    have hto : toAdd (f a0) = -toAdd (f a0) := by
      have h1 := congrArg (fun x : Multiplicative (ZMod p) => toAdd x) h0
      rw [toAdd_inv] at h1
      exact h1
    have hz : toAdd (f a0) = 0 := SpCoord.coord_eq_zero_of_eq_neg hp hp2 hto
    exact ha0 (toAdd.injective (by simpa using hz))

end CFSG.StandardType

end

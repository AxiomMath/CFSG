module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType

namespace SpCoord

open Multiplicative

variable {p k : ℕ}

@[expose] def commMod (H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))) :
    Subgroup (Fin k → Multiplicative (ZMod p)) :=
  Subgroup.closure {c | ∃ g ∈ H, ∃ f, c = f⁻¹ * g f}

theorem displacement_mem_commMod {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    {g : MulAut (Fin k → Multiplicative (ZMod p))} (hg : g ∈ H)
    (f : Fin k → Multiplicative (ZMod p)) : f⁻¹ * g f ∈ commMod H :=
  Subgroup.subset_closure ⟨g, hg, f, rfl⟩

theorem apply_mem_commMod {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    {g : MulAut (Fin k → Multiplicative (ZMod p))} (hg : g ∈ H)
    {w : Fin k → Multiplicative (ZMod p)} (hw : w ∈ commMod H) : g w ∈ commMod H := by
  induction hw using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨h, hh, f, rfl⟩ := hc
    have hmem : g * h * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)
    have heq : g (f⁻¹ * h f) = (g f)⁻¹ * (g * h * g⁻¹) (g f) := by
      rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [heq]
    exact displacement_mem_commMod hmem (g f)
  | one => rw [map_one]; exact (commMod H).one_mem
  | mul a b _ _ ha hb => rw [map_mul]; exact (commMod H).mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact (commMod H).inv_mem ha

local notation "δ" i => (Pi.mulSingle i (ofAdd (1 : ZMod p)) : Fin k → Multiplicative (ZMod p))

@[expose] def IsFixedCoord (H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))))
    (i : Fin k) : Prop :=
  ∀ g ∈ H, ∀ f : Fin k → Multiplicative (ZMod p), g f i = f i

theorem commMod_apply_of_isFixedCoord {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    {i : Fin k} (hi : IsFixedCoord H i) {w : Fin k → Multiplicative (ZMod p)}
    (hw : w ∈ commMod H) : w i = 1 := by
  induction hw using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨g, hg, f, rfl⟩ := hc
    rw [Pi.mul_apply, Pi.inv_apply, hi g hg f, inv_mul_cancel]
  | one => rfl
  | mul a b _ _ ha hb => rw [Pi.mul_apply, ha, hb, mul_one]
  | inv a _ ha => rw [Pi.inv_apply, ha, inv_one]

theorem apply_coord_eq_of_apply_mulSingle (hp : p.Prime)
    {g : MulAut (Fin k → Multiplicative (ZMod p))} (hg : IsSignedPerm ⇑g) {i : Fin k}
    (hgi : g (δ i) = δ i) (f : Fin k → Multiplicative (ZMod p)) : g f i = f i := by
  obtain ⟨π, ε, hε, hπ⟩ := hg
  have h1 : (Pi.mulSingle (π i) (ofAdd (ε i)) : Fin k → Multiplicative (ZMod p)) =
      Pi.mulSingle i (ofAdd 1) := by
    rw [← hgi, IsSignedPerm.apply_mulSingle hπ i 1, mul_one]
  obtain ⟨hπi, hεi⟩ := mulSingle_ofAdd_eq_iff (coord_sign_ne_zero hp (hε i)) h1
  have h2 := hπ f i
  rw [hπi, hεi, one_mul] at h2
  exact toAdd.injective h2

theorem exists_even_support_of_irreducible (hp : p.Prime)
    {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hH : ∀ g ∈ H, IsSignedPerm ⇑g)
    (hirr : ∀ W : Subgroup (Fin k → Multiplicative (ZMod p)), W ≤ commMod H →
      (∀ g ∈ H, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = commMod H)
    (hcard : Nat.card (commMod H) * p ^ 2 ≤ p ^ k) :
    ∃ T : Finset (Fin k), Even T.card ∧ ∀ w ∈ commMod H, ∀ i ∉ T, w i = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases hfix : ∃ t, IsFixedCoord H t
  · obtain ⟨t, ht⟩ := hfix
    set T0 := Finset.univ.filter (fun i => ¬ IsFixedCoord H i) with hT0
    have htT0 : t ∉ T0 := by simp [hT0, ht]
    have hsupp : ∀ T : Finset (Fin k), T0 ⊆ T → ∀ w ∈ commMod H, ∀ i ∉ T, w i = 1 := by
      intro T hT w hw i hi
      have hfi : IsFixedCoord H i := by
        by_contra h
        exact hi (hT (by simp [hT0, h]))
      exact commMod_apply_of_isFixedCoord hfi hw
    by_cases hev : Even T0.card
    · exact ⟨T0, hev, hsupp T0 subset_rfl⟩
    · refine ⟨insert t T0, ?_, hsupp _ (Finset.subset_insert _ _)⟩
      rw [Finset.card_insert_of_notMem htT0]
      exact (Nat.not_even_iff_odd.mp hev).add_one
  · exfalso
    push Not at hfix
    have hc1 : 1 ≤ Nat.card (commMod H) := Nat.card_pos
    have hp2 : 2 ≤ p := hp.two_le
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        rw [pow_zero] at hcard
        nlinarith
      · exact hk0
    set i₀ : Fin k := ⟨0, hk⟩
    set M : Subgroup (Fin k → Multiplicative (ZMod p)) :=
      Subgroup.zpowers (δ i₀) ⊔ commMod H with hM
    have hCM : commMod H ≤ M := le_sup_right
    have hi₀M : (δ i₀) ∈ M := (le_sup_left : Subgroup.zpowers (δ i₀) ≤ M)
      (Subgroup.mem_zpowers _)
    have hkey : ∀ g ∈ H, ∀ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) → (∀ f i, toAdd (g f (π i)) = ε i * toAdd (f i)) →
        ∀ i, ((δ i) ∈ M ↔ (δ (π i)) ∈ M) := by
      intro g hg π ε hε hπ i
      have hd : (δ i)⁻¹ * g (δ i) ∈ M := hCM (displacement_mem_commMod hg _)
      have h1 : (δ i) ∈ M ↔ g (δ i) ∈ M := by
        constructor
        · intro h
          have h' := M.mul_mem h hd
          rwa [mul_inv_cancel_left] at h'
        · intro h
          have h' := M.mul_mem h (M.inv_mem hd)
          rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h'
      rw [h1, IsSignedPerm.apply_mulSingle hπ i 1, mul_one]
      rcases hε i with h | h
      · rw [h]
      · rw [h, ofAdd_neg, Pi.mulSingle_inv, inv_mem_iff]
    let VO : Subgroup (Fin k → Multiplicative (ZMod p)) :=
      { carrier := {f | ∀ i, (δ i) ∉ M → f i = 1}
        mul_mem' := fun {a b} ha hb i hi => by
          rw [Pi.mul_apply, ha i hi, hb i hi, mul_one]
        one_mem' := fun _ _ => rfl
        inv_mem' := fun {a} ha i hi => by rw [Pi.inv_apply, ha i hi, inv_one] }
    let VOc : Subgroup (Fin k → Multiplicative (ZMod p)) :=
      { carrier := {f | ∀ i, (δ i) ∈ M → f i = 1}
        mul_mem' := fun {a b} ha hb i hi => by
          rw [Pi.mul_apply, ha i hi, hb i hi, mul_one]
        one_mem' := fun _ _ => rfl
        inv_mem' := fun {a} ha i hi => by rw [Pi.inv_apply, ha i hi, inv_one] }
    have hVO : ∀ g ∈ H, ∀ f ∈ VO, g f ∈ VO := by
      intro g hg f hf i hi
      obtain ⟨π, ε, hε, hπ⟩ := hH g hg
      have hf' : ∀ j, (δ j) ∉ M → f j = 1 := hf
      have hj : (δ (π.symm i)) ∉ M := by
        rw [hkey g hg π ε hε hπ, Equiv.apply_symm_apply]
        exact hi
      have h1 := hπ f (π.symm i)
      rw [Equiv.apply_symm_apply, hf' _ hj, toAdd_one, mul_zero] at h1
      exact toAdd.injective (h1.trans toAdd_one.symm)
    have hVOc : ∀ g ∈ H, ∀ f ∈ VOc, g f ∈ VOc := by
      intro g hg f hf i hi
      obtain ⟨π, ε, hε, hπ⟩ := hH g hg
      have hf' : ∀ j, (δ j) ∈ M → f j = 1 := hf
      have hj : (δ (π.symm i)) ∈ M := by
        rw [hkey g hg π ε hε hπ, Equiv.apply_symm_apply]
        exact hi
      have h1 := hπ f (π.symm i)
      rw [Equiv.apply_symm_apply, hf' _ hj, toAdd_one, mul_zero] at h1
      exact toAdd.injective (h1.trans toAdd_one.symm)
    have hW1 : commMod H ⊓ VO ≤ commMod H := inf_le_left
    have hW1s : ∀ g ∈ H, ∀ w ∈ commMod H ⊓ VO, g w ∈ commMod H ⊓ VO :=
      fun g hg w hw => ⟨apply_mem_commMod hg hw.1, hVO g hg w hw.2⟩
    rcases hirr _ hW1 hW1s with hbot | htop
    ·
      apply hfix i₀
      intro g hg
      have hδ : (δ i₀) ∈ VO := by
        intro i hi
        have hne : i ≠ i₀ := fun h => hi (h ▸ hi₀M)
        exact Pi.mulSingle_eq_of_ne hne _
      have hd : (δ i₀)⁻¹ * g (δ i₀) ∈ commMod H ⊓ VO :=
        ⟨displacement_mem_commMod hg _, VO.mul_mem (VO.inv_mem hδ) (hVO g hg _ hδ)⟩
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hd
      exact apply_coord_eq_of_apply_mulSingle hp (hH g hg) hd.symm
    ·
      have hall : ∀ i, (δ i) ∈ M := by
        intro i
        by_contra hi
        apply hfix i
        intro g hg
        have hδ : (δ i) ∈ VOc := by
          intro j hj
          have hne : j ≠ i := fun h => hi (h ▸ hj)
          exact Pi.mulSingle_eq_of_ne hne _
        have hdC : (δ i)⁻¹ * g (δ i) ∈ commMod H := displacement_mem_commMod hg _
        have hdO : (δ i)⁻¹ * g (δ i) ∈ VO := by
          rw [← htop] at hdC
          exact hdC.2
        have hdOc : (δ i)⁻¹ * g (δ i) ∈ VOc :=
          VOc.mul_mem (VOc.inv_mem hδ) (hVOc g hg _ hδ)
        have hd1 : (δ i)⁻¹ * g (δ i) = 1 := by
          funext j
          by_cases hj : (δ j) ∈ M
          · exact hdOc j hj
          · exact hdO j hj
        rw [inv_mul_eq_one] at hd1
        exact apply_coord_eq_of_apply_mulSingle hp (hH g hg) hd1.symm
      have htopM : ∀ f : Fin k → Multiplicative (ZMod p), f ∈ M := by
        intro f
        rw [← Finset.univ_prod_mulSingle f]
        refine Subgroup.prod_mem _ fun i _ => ?_
        rw [← ofAdd_toAdd (f i), mulSingle_ofAdd_eq_pow]
        exact M.pow_mem (hall i) _
      have hsurj : Function.Surjective
          (fun a : ↥(Subgroup.zpowers (δ i₀)) × ↥(commMod H) =>
            ((a.1 : Fin k → Multiplicative (ZMod p)) * a.2)) := by
        intro f
        obtain ⟨y, z, hyz⟩ := Subgroup.mem_sup'.mp (htopM f)
        exact ⟨(y, z), hyz⟩
      have hle := Nat.card_le_card_of_surjective _ hsurj
      have hcoord : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
        congr 1
        exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
      rw [Nat.card_prod, hcoord, Nat.card_zpowers] at hle
      have hord : orderOf (δ i₀) ≤ p := by
        refine orderOf_le_of_pow_eq_one hp.pos ?_
        rw [mulSingle_ofAdd_pow, ZMod.natCast_self, zero_mul, ofAdd_zero, Pi.mulSingle_one]
      have h3 : p ^ k ≤ p * Nat.card (commMod H) :=
        hle.trans (Nat.mul_le_mul_right _ hord)
      have h4 : Nat.card (commMod H) * p ^ 2 ≤ p * Nat.card (commMod H) := hcard.trans h3
      have h5 : Nat.card (commMod H) * p ^ 2 = Nat.card (commMod H) * p * p := by ring
      rw [h5, mul_comm p] at h4
      have h6 : Nat.card (commMod H) * p * 2 ≤ Nat.card (commMod H) * p * p :=
        Nat.mul_le_mul_left _ hp2
      have h7 : 0 < Nat.card (commMod H) * p := Nat.mul_pos hc1 hp.pos
      linarith


@[expose] def sgnSetAut (T : Finset (Fin k)) : MulAut (Fin k → Multiplicative (ZMod p)) where
  toFun f i := if i ∈ T then (f i)⁻¹ else f i
  invFun f i := if i ∈ T then (f i)⁻¹ else f i
  left_inv f := by
    funext i
    by_cases h : i ∈ T <;> simp [h]
  right_inv f := by
    funext i
    by_cases h : i ∈ T <;> simp [h]
  map_mul' f g := by
    funext i
    by_cases h : i ∈ T <;> simp [h, mul_comm]

theorem sgnSetAut_apply (T : Finset (Fin k)) (f : Fin k → Multiplicative (ZMod p)) (i : Fin k) :
    sgnSetAut T f i = if i ∈ T then (f i)⁻¹ else f i :=
  rfl

theorem sgnSetAut_apply_of_support {T : Finset (Fin k)} {f : Fin k → Multiplicative (ZMod p)}
    (hf : ∀ i ∉ T, f i = 1) : sgnSetAut T f = f⁻¹ := by
  funext i
  rw [sgnSetAut_apply, Pi.inv_apply]
  by_cases h : i ∈ T
  · rw [if_pos h]
  · rw [if_neg h, hf i h, inv_one]

theorem sgnSetAut_empty : (sgnSetAut ∅ : MulAut (Fin k → Multiplicative (ZMod p))) = 1 := by
  ext f i
  simp [sgnSetAut_apply]

theorem sgnSetAut_eq_mul_erase {T : Finset (Fin k)} {a b : Fin k} (ha : a ∈ T) (hb : b ∈ T)
    (hab : a ≠ b) :
    (sgnSetAut T : MulAut (Fin k → Multiplicative (ZMod p))) =
      sgnAut a * sgnAut b * sgnSetAut ((T.erase a).erase b) := by
  ext f i
  rw [MulAut.mul_apply, MulAut.mul_apply, sgnSetAut_apply, sgnAut_apply, sgnAut_apply]
  by_cases hia : i = a
  · subst hia
    rw [if_pos ha, Function.update_self, Function.update_of_ne hab, sgnSetAut_apply,
      if_neg (by simp)]
  · rw [Function.update_of_ne hia]
    by_cases hib : i = b
    · subst hib
      rw [if_pos hb, Function.update_self, sgnSetAut_apply, if_neg (by simp)]
    · rw [Function.update_of_ne hib, sgnSetAut_apply]
      by_cases hiT : i ∈ T
      · rw [if_pos hiT, if_pos (by simp [hiT, hia, hib])]
      · rw [if_neg hiT, if_neg (by simp [hiT])]

theorem sgnSetAut_mem_of_even {S : Set (MulAut (Fin k → Multiplicative (ZMod p)))}
    (h1 : (1 : MulAut (Fin k → Multiplicative (ZMod p))) ∈ S)
    (hmul : ∀ α ∈ S, ∀ β ∈ S, α * β ∈ S)
    (hpair : ∀ a b : Fin k, a ≠ b → sgnAut a * sgnAut b ∈ S) :
    ∀ T : Finset (Fin k), Even T.card → sgnSetAut T ∈ S := by
  classical
  intro T hT
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    rcases T.eq_empty_or_nonempty with hTe | ⟨a, ha⟩
    · rw [hTe, sgnSetAut_empty]
      exact h1
    · have hcard1 : 1 ≤ (T.erase a).card := by
        have h := Finset.card_erase_add_one ha
        obtain ⟨m, hm⟩ := hT
        omega
      obtain ⟨b, hb⟩ := Finset.card_pos.mp hcard1
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have hbT : b ∈ T := Finset.mem_of_mem_erase hb
      have hcard2 : ((T.erase a).erase b).card + 2 = T.card := by
        rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
        have : 2 ≤ T.card := by
          have h := Finset.card_erase_add_one ha
          omega
        omega
      rw [sgnSetAut_eq_mul_erase ha hbT (Ne.symm hba)]
      refine hmul _ (hpair a b (Ne.symm hba)) _ (ih _ (by omega) _ ?_ rfl)
      obtain ⟨m, hm⟩ := hT
      exact ⟨m - 1, by omega⟩

end SpCoord

end CFSG.StandardType

end

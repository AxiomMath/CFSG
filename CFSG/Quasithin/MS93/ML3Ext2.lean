module

public import CFSG.Quasithin.MS93.ML3Ext
public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.Quasithin.MS93

open Matrix CFSG.Quasithin

variable {F : Type} [Field F]

theorem cyc_inv_conj_rootElt12 (a : F) :
    cyc⁻¹ * rootElt 1 2 a * cyc⁻¹⁻¹ = rootElt 0 1 a := by
  have h := cyc_conj_rootElt (F := F) 0 1 a
  rw [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl] at h
  rw [← h]
  group

theorem rootElt21_comm_rootElt01 (a : F) :
    rootElt 2 1 (1 : F) * rootElt 0 1 a = rootElt 0 1 a * rootElt 2 1 1 :=
  (rootElt_commute (by decide) (by decide) 1 a).eq

theorem rootElt21_mulVec (x : Fin 3 → F) :
    ((rootElt 2 1 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = ![x 0, x 1, x 2 + x 1] := by
  rw [rootElt_mulVec (by decide)]
  funext k
  fin_cases k <;> simp

variable [CharP F 2]

theorem rootElt21_conj_tLn :
    rootElt 2 1 (1 : F) * tLn 1 0 * (rootElt 2 1 1)⁻¹ = rootElt 0 1 1 * tLn 1 0 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change ((rootElt 2 1 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((tLn 1 0 : SL3 F) :
      Matrix _ _ F) = ((rootElt 0 1 (1 : F) : SL3 F) : Matrix _ _ F) * ((tLn 1 0 : SL3 F) :
      Matrix _ _ F) * ((rootElt 2 1 (1 : F) : SL3 F) : Matrix _ _ F)
  rw [tLn_zero_right, coe_rootElt (by decide), coe_rootElt (by decide),
    coe_rootElt (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem mem_of_invariant (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ (g : SL3 F) (x : Fin 3 → F), x ∈ S → ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S)
    {x : Fin 3 → F} (hx : x ∈ S) (hx0 : x ≠ 0) (z : Fin 3 → F) : z ∈ S := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  have hsingle : ∀ i, i ≠ j → ∀ c : F, Pi.single i c ∈ S := fun i hij c => by
    have h := S.sub_mem (hS (rootElt i j (c / x j)) x hx) hx
    rwa [rootElt_mulVec hij, add_sub_cancel_left, div_mul_cancel₀ c hj] at h
  have hall : ∀ k (c : F), Pi.single k c ∈ S := fun k c => by
    by_cases hk : k = j
    · subst hk
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ k := ⟨k + 1, by fin_cases k <;> decide⟩
      have h := S.sub_mem (hS (rootElt k i c) _ (hsingle i hi 1)) (hsingle i hi 1)
      rwa [rootElt_mulVec hi.symm, add_sub_cancel_left, Pi.single_eq_same, mul_one] at h
    · exact hsingle k hk c
  have hz : z = Pi.single 0 (z 0) + Pi.single 1 (z 1) + Pi.single 2 (z 2) := by
    funext k
    fin_cases k <;> simp
  rw [hz]
  exact S.add_mem (S.add_mem (hall 0 _) (hall 1 _)) (hall 2 _)

omit [CharP F 2] in
theorem sStar_mulVec_e0 {s : SL3 F} (hs : s ∈ (sStar : Subgroup (SL3 F))) :
    ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  let P : Subgroup (SL3 F) :=
    { carrier := {g | ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]}
      mul_mem' := fun {a b} ha hb => by
        show ((a * b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]
        rw [coe_mul_SL3, ← Matrix.mulVec_mulVec]
        rw [show ((b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] from hb]
        exact ha
      one_mem' := by
        show ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]
        simp
      inv_mem' := fun {a} ha => by
        show ((a⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]
        have ha' : ((a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := ha
        conv_lhs => rw [← ha']
        rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel]
        simp }
  have hX : ∀ i j : Fin 3, j ≠ 0 → i ≠ j → rootGroup i j ≤ P := by
    rintro i j hj hij _ ⟨c, rfl⟩
    show ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]
    rw [rootElt_mulVec hij]
    fin_cases j
    · exact absurd rfl hj
    all_goals simp
  have hle : (sStar : Subgroup (SL3 F)) ≤ P := by
    rw [sStar]
    exact sup_le (sup_le (hX 0 1 (by decide) (by decide)) (hX 0 2 (by decide) (by decide)))
      (hX 1 2 (by decide) (by decide))
  exact hle hs

omit [Field F] [CharP F 2] in
theorem card_natMod [Finite F] :
    Nat.card (Multiplicative (Fin 3 → F)) = Nat.card F ^ 3 := by
  rw [show Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (Fin 3 → F) from rfl, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

omit [CharP F 2] in
theorem eq_zero_of_fixed {x : Fin 3 → F}
    (h : ∀ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) : x = 0 := by
  have h01 := h (rootElt 0 1 1)
  have h12 := h (rootElt 1 2 1)
  have h10 := h (rootElt 1 0 1)
  rw [rootElt_mulVec (by decide)] at h01 h12 h10
  have e1 := congrFun h01 0
  have e2 := congrFun h12 1
  have e0 := congrFun h10 1
  simp at e1 e2 e0
  funext k
  fin_cases k
  · exact e0
  · exact e1
  · exact e2

section Module

variable {V : Type*} [CommGroup V] {ρ : SL3 F →* MulAut V}

namespace NatNatExt

variable (E : NatNatExt ρ) (hV : ∀ v : V, v ^ 2 = 1)
include E hV

theorem dc_dc_rootElt01 [Finite F] (a c : F) (v : V) :
    dc ρ (rootElt 0 1 a) (dc ρ (rootElt 0 1 c) v) = 1 := by
  rw [← cyc_inv_conj_rootElt12 a, ← cyc_inv_conj_rootElt12 c, dc_dc_conj, ← tLn_zero_left,
    ← tLn_zero_left, E.dc_dc_tLn_right hV, map_one]

omit [CharP F 2] hV in
theorem exists_β_eq_e2 : ∃ v₂ : V, Multiplicative.toAdd (E.β v₂) = ![0, 0, 1] :=
  E.β_surjective (Multiplicative.ofAdd ![0, 0, 1])

theorem exists_dc_tLn10_eq [Finite F] {u : V} (hu : E.InL0 u) :
    ∃ z : F, dc ρ (tLn 1 0) u = E.ι (Multiplicative.ofAdd ![z, 0, 0]) := by
  obtain ⟨v₂, hv₂⟩ := E.exists_β_eq_e2
  set x := Multiplicative.toAdd (E.β u) with hx
  have hu2 : x 2 = 0 := hu
  set c := dc ρ (tLn (x 0) (x 1)) v₂ with hc
  have hβc : E.β (u * c⁻¹) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hc, E.toAdd_β_dc_tLn, hv₂, ← hx]
    funext k
    fin_cases k <;> simp [hu2]
  obtain ⟨z, hz⟩ := E.exists_ι_eq hβc
  have hu' : u = E.ι (Multiplicative.ofAdd z) * c := by rw [hz, inv_mul_cancel_right]
  refine ⟨z 2, ?_⟩
  rw [hu', dc_mul_right, hc, E.dc_dc_qLn hV (tLn_mem_qLn _ _) (tLn_mem_qLn _ _), mul_one,
    E.dc_tLn_ι]
  congr 2
  funext k
  fin_cases k <;> simp

omit [CharP F 2] hV in
theorem dc_rootElt01_ι (a z : F) :
    dc ρ (rootElt 0 1 a) (E.ι (Multiplicative.ofAdd ![z, 0, 0])) = 1 := by
  rw [E.dc_ι, rootElt_mulVec (by decide)]
  have : (![z, 0, 0] : Fin 3 → F) + Pi.single 0 (a * (![z, 0, 0] : Fin 3 → F) 1) -
      ![z, 0, 0] = 0 := by
    funext k
    fin_cases k <;> simp
  rw [this, ofAdd_zero, map_one]

theorem dc_rootElt01_dc_tLn_of_inL0 [Finite F] {u : V} (hu : E.InL0 u) (a : F) :
    dc ρ (rootElt 0 1 a) (dc ρ (tLn 1 0) u) = 1 := by
  obtain ⟨z, hz⟩ := E.exists_dc_tLn10_eq hV hu
  rw [hz, E.dc_rootElt01_ι]

theorem act_rootElt21_dc_dc [Finite F] (a : F) (w : V) :
    ρ (rootElt 2 1 1) (dc ρ (rootElt 0 1 a) (dc ρ (tLn 1 0) w)) =
      dc ρ (rootElt 0 1 a) (dc ρ (tLn 1 0) (ρ (rootElt 2 1 1) w)) := by
  rw [act_dc_of_commute (rootElt21_comm_rootElt01 a), act_dc_eq, rootElt21_conj_tLn, dc_mul,
    dc_mul_right, dc_mul_right, E.dc_dc_rootElt01 hV, E.dc_dc_rootElt01 hV, one_mul, one_mul]

theorem dc_rootElt01_dc_tLn [Finite F] (a : F) (v : V) :
    dc ρ (rootElt 0 1 a) (dc ρ (tLn 1 0) v) = 1 := by
  set x := Multiplicative.toAdd (E.β v) with hx
  obtain ⟨u₂, hu₂⟩ := E.β_surjective (Multiplicative.ofAdd ![0, x 2, 0])
  have hu₂' : E.InL0 u₂ := by
    show Multiplicative.toAdd (E.β u₂) 2 = 0
    rw [hu₂]
    rfl
  set u₁ := v * (ρ (rootElt 2 1 1) u₂)⁻¹ with hu₁
  have hu₁' : E.InL0 u₁ := by
    show Multiplicative.toAdd (E.β u₁) 2 = 0
    rw [hu₁, map_mul, map_inv, toAdd_mul, toAdd_inv, E.β_equiv, rootElt21_mulVec, hu₂, ← hx]
    simp
  have hv : v = u₁ * ρ (rootElt 2 1 1) u₂ := by rw [hu₁, inv_mul_cancel_right]
  rw [hv, dc_mul_right, dc_mul_right, E.dc_rootElt01_dc_tLn_of_inL0 hV hu₁', one_mul,
    ← E.act_rootElt21_dc_dc hV, E.dc_rootElt01_dc_tLn_of_inL0 hV hu₂', map_one]

omit [CharP F 2] hV in
theorem ρ_injective : Function.Injective ρ := by
  intro g h hgh
  have key : ∀ x : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
      ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x := fun x => by
    have e1 := E.ι_equiv g x
    rw [hgh, E.ι_equiv h x] at e1
    exact (E.ι_ofAdd_inj e1).symm
  apply Subtype.ext
  exact Matrix.ext_of_mulVec_single fun i => key _

theorem exists_mem_fixV_sStar [Finite F] :
    ∃ w ∈ fixV (sStar.map ρ), Multiplicative.toAdd (E.β w) = ![1, 0, 0] := by
  obtain ⟨v₂, hv₂⟩ := E.exists_β_eq_e2
  refine ⟨dc ρ (tLn 1 0) v₂, ?_, ?_⟩
  · set w := dc ρ (tLn 1 0) v₂ with hw
    let S : Subgroup (SL3 F) :=
      { carrier := {g | ρ g w = w}
        mul_mem' := fun {a b} ha hb => by
          show ρ (a * b) w = w
          rw [map_mul, MulAut.mul_apply, show ρ b w = w from hb, show ρ a w = w from ha]
        one_mem' := by
          show ρ 1 w = w
          simp
        inv_mem' := fun {a} ha => by
          show ρ a⁻¹ w = w
          have ha' : ρ a w = w := ha
          conv_lhs => rw [← ha']
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] }
    have hle : (sStar : Subgroup (SL3 F)) ≤ S := by
      rw [sStar]
      refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨a, rfl⟩
        show ρ (rootElt 0 1 a) w = w
        rw [← dc_eq_one_iff]
        exact E.dc_rootElt01_dc_tLn hV a v₂
      · rintro _ ⟨c, rfl⟩
        show ρ (rootElt 0 2 c) w = w
        rw [← dc_eq_one_iff, ← tLn_zero_right]
        exact E.dc_dc_qLn hV (tLn_mem_qLn _ _) (tLn_mem_qLn _ _) v₂
      · rintro _ ⟨c, rfl⟩
        show ρ (rootElt 1 2 c) w = w
        rw [← dc_eq_one_iff, ← tLn_zero_left]
        exact E.dc_dc_qLn hV (tLn_mem_qLn _ _) (tLn_mem_qLn _ _) v₂
    rw [mem_fixV]
    rintro x ⟨g, hg, rfl⟩
    exact hle hg
  · rw [E.toAdd_β_dc_tLn, hv₂]
    funext k
    fin_cases k <;> simp

omit [CharP F 2] hV in
theorem card_eq [Finite F] : Nat.card V = Nat.card F ^ 6 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup E.β.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective E.β E.β_surjective).toEquiv,
    E.ker_β, ← Nat.card_congr (MonoidHom.ofInjective E.ι_injective).toEquiv, card_natMod]
  ring

theorem ms18_card_le [Finite F] :
    Nat.card V ≤ Nat.card ↥(qLn.map ρ) * Nat.card ↥(fixV (qLn.map ρ)) := by
  have := Fintype.ofFinite F
  have : Finite V :=
    Nat.finite_of_card_ne_zero (by rw [E.card_eq]; exact pow_ne_zero _ Nat.card_pos.ne')
  obtain ⟨v₂, hv₂⟩ := E.exists_β_eq_e2
  let f : F × F → ↥(qLn.map ρ) := fun p => ⟨ρ (tLn p.1 p.2), tLn p.1 p.2, tLn_mem_qLn _ _, rfl⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : tLn a b = tLn a' b' := E.ρ_injective (congrArg Subtype.val h)
    have h2 := congrArg (fun g : SL3 F => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1])
      h1
    simp only [tLn_mulVec] at h2
    have h3 := congrFun h2 0
    have h4 := congrFun h2 1
    simp at h3 h4
    rw [h3, h4]
  let g : F × F × F × F → ↥(fixV (qLn.map ρ)) := fun p =>
    ⟨E.ι (Multiplicative.ofAdd ![p.1, p.2.1, 0]) * dc ρ (tLn p.2.2.1 p.2.2.2) v₂, by
      rw [mem_fixV]
      rintro x ⟨t, ht, rfl⟩
      obtain ⟨a', b', rfl⟩ := mem_qLn_iff_tLn.mp ht
      rw [map_mul, (dc_eq_one_iff ρ _ _).mp (E.dc_tLn_ι_of_two (y := ![p.1, p.2.1, 0]) rfl a' b'),
        (dc_eq_one_iff ρ _ _).mp (E.dc_dc_qLn hV (tLn_mem_qLn a' b') (tLn_mem_qLn _ _) v₂)]⟩
  have hg : Function.Injective g := by
    rintro ⟨y0, y1, a, b⟩ ⟨y0', y1', a', b'⟩ h
    have h1 := congrArg (fun u : ↥(fixV (qLn.map ρ)) => Multiplicative.toAdd (E.β u)) h
    simp only [g, map_mul, toAdd_mul, E.toAdd_β_dc_tLn, hv₂] at h1
    have hβι : ∀ y : Fin 3 → F, E.β (E.ι (Multiplicative.ofAdd y)) = 1 := fun y =>
      (E.mem_range_ι_iff _).mp ⟨_, rfl⟩
    rw [hβι, hβι, toAdd_one, zero_add, zero_add] at h1
    have ha := congrFun h1 0
    have hb := congrFun h1 1
    simp at ha hb
    subst ha hb
    have h2 := congrArg Subtype.val h
    simp only [g, mul_left_inj] at h2
    have h3 := E.ι_ofAdd_inj h2
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp at h30 h31
    rw [h30, h31]
  have hcf := Nat.card_le_card_of_injective f hf
  have hcg := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod] at hcf
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod] at hcg
  rw [E.card_eq]
  calc Nat.card F ^ 6 = (Nat.card F * Nat.card F) * (Nat.card F * (Nat.card F *
        (Nat.card F * Nat.card F))) := by ring
    _ ≤ _ := Nat.mul_le_mul hcf hcg

omit [CharP F 2] hV in
theorem ms18_fixV : fixV ρ.range = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_fixV] at hv
  have hfix : ∀ g : SL3 F, ρ g v = v := fun g => hv _ ⟨g, rfl⟩
  have hβ : E.β v = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    apply eq_zero_of_fixed
    intro g
    rw [← E.β_equiv, hfix]
  obtain ⟨y, rfl⟩ := E.exists_ι_eq hβ
  have hy : y = 0 := by
    apply eq_zero_of_fixed
    intro g
    have := hfix g
    rw [E.ι_equiv] at this
    exact E.ι_ofAdd_inj this
  rw [hy, ofAdd_zero, map_one]
  exact Subgroup.one_mem _

theorem ms18_gen [Finite F] : G6.submoduleClosure ρ.range (fixV (sStar.map ρ)) = ⊤ := by
  set T := fixV (sStar.map ρ) with hT
  let W : Subgroup V := Subgroup.closure {v | ∃ (g : SL3 F) (u : V), u ∈ T ∧ ρ g u = v}
  have hWle : W ≤ G6.submoduleClosure ρ.range T := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, u, hu, rfl⟩
    exact (le_iSup₂ (f := fun (x : MulAut V) (_ : x ∈ ρ.range) => T.map x.toMonoidHom) (ρ g)
      ⟨g, rfl⟩) ⟨u, hu, rfl⟩
  have hTW : ∀ u ∈ T, u ∈ W := fun u hu =>
    Subgroup.subset_closure ⟨1, u, hu, by simp⟩
  have hWinv : ∀ (h : SL3 F) (v : V), v ∈ W → ρ h v ∈ W := by
    intro h v hv
    have : W.map (ρ h).toMonoidHom ≤ W := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨g, u, hu, rfl⟩, rfl⟩
      exact Subgroup.subset_closure ⟨h * g, u, hu, by simp [MulAut.mul_apply]⟩
    exact this ⟨v, hv, rfl⟩
  let S₀ : AddSubgroup (Fin 3 → F) :=
    { carrier := {y | E.ι (Multiplicative.ofAdd y) ∈ W}
      zero_mem' := by
        show E.ι (Multiplicative.ofAdd 0) ∈ W
        rw [ofAdd_zero, map_one]
        exact W.one_mem
      add_mem' := fun {y y'} hy hy' => by
        show E.ι (Multiplicative.ofAdd (y + y')) ∈ W
        rw [ofAdd_add, map_mul]
        exact W.mul_mem hy hy'
      neg_mem' := fun {y} hy => by
        show E.ι (Multiplicative.ofAdd (-y)) ∈ W
        rw [ofAdd_neg, map_inv]
        exact W.inv_mem hy }
  have hS₀ : ∀ (g : SL3 F) (y : Fin 3 → F), y ∈ S₀ →
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S₀ := fun g y hy => by
    show E.ι (Multiplicative.ofAdd _) ∈ W
    rw [← E.ι_equiv]
    exact hWinv g _ hy
  have he0 : (![1, 0, 0] : Fin 3 → F) ∈ S₀ := by
    show E.ι (Multiplicative.ofAdd ![1, 0, 0]) ∈ W
    apply hTW
    rw [hT, mem_fixV]
    rintro x ⟨s, hs, rfl⟩
    rw [E.ι_equiv, sStar_mulVec_e0 hs]
  have hne : (![1, 0, 0] : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hV₀ : ∀ y : Fin 3 → F, E.ι (Multiplicative.ofAdd y) ∈ W := fun y =>
    mem_of_invariant S₀ hS₀ he0 hne y
  obtain ⟨w, hw, hβw⟩ := E.exists_mem_fixV_sStar hV
  let S₁ : AddSubgroup (Fin 3 → F) :=
    { carrier := {x | ∃ u ∈ W, Multiplicative.toAdd (E.β u) = x}
      zero_mem' := ⟨1, W.one_mem, by simp⟩
      add_mem' := fun {x x'} ⟨u, hu, hux⟩ ⟨u', hu', hux'⟩ =>
        ⟨u * u', W.mul_mem hu hu', by rw [map_mul, toAdd_mul, hux, hux']⟩
      neg_mem' := fun {x} ⟨u, hu, hux⟩ => ⟨u⁻¹, W.inv_mem hu, by rw [map_inv, toAdd_inv, hux]⟩ }
  have hS₁ : ∀ (g : SL3 F) (x : Fin 3 → F), x ∈ S₁ →
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S₁ := fun g x ⟨u, hu, hux⟩ =>
    ⟨ρ g u, hWinv g u hu, by rw [E.β_equiv, hux]⟩
  have hβ1 : (![1, 0, 0] : Fin 3 → F) ∈ S₁ := ⟨w, hTW w hw, hβw⟩
  have hW : W = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hmem := mem_of_invariant S₁ hS₁ hβ1 hne (Multiplicative.toAdd (E.β v))
    obtain ⟨u, hu, hux⟩ := hmem
    have hker : E.β (v * u⁻¹) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hux, add_neg_cancel, toAdd_one]
    obtain ⟨y, hy⟩ := E.exists_ι_eq hker
    have hv : v = E.ι (Multiplicative.ofAdd y) * u := by rw [hy, inv_mul_cancel_right]
    rw [hv]
    exact W.mul_mem (hV₀ y) hu
  exact eq_top_iff.mpr (hW ▸ hWle)

end NatNatExt

end Module

end CFSG.Quasithin.MS93

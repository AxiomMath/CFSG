module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiW

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv

@[expose] def pairInv : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5

@[expose] def InP16 (σ : Perm (Fin 6)) : Prop :=
  σ * pairInv = pairInv * σ ∧ pact σ (v6 [4, 5]) = v6 [4, 5]

instance (σ : Perm (Fin 6)) : Decidable (InP16 σ) := by unfold InP16; infer_instance

@[expose] def DW : Subgroup (Wr 6) where
  carrier := {a | wsum a = 0 ∧ InP16 a.perm}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_, ?_⟩
    · rw [wsum_mul, ha.1, hb.1, add_zero]
    · show a.perm * b.perm * pairInv = pairInv * (a.perm * b.perm)
      rw [mul_assoc, hb.2.1, ← mul_assoc, ha.2.1, mul_assoc]
    · show pact (a.perm * b.perm) (v6 [4, 5]) = v6 [4, 5]
      rw [pact_mul, hb.2.2, ha.2.2]
  one_mem' := ⟨wsum_one, by rw [Wr.one_perm, one_mul, mul_one], pact_one _⟩
  inv_mem' {a} ha := by
    refine ⟨by rw [wsum_inv]; exact ha.1, ?_, ?_⟩
    · show a.perm⁻¹ * pairInv = pairInv * a.perm⁻¹
      exact (Commute.inv_left (show Commute a.perm pairInv from ha.2.1)).eq
    · show pact a.perm⁻¹ (v6 [4, 5]) = v6 [4, 5]
      conv_lhs => rw [← ha.2.2]
      rw [← pact_mul, inv_mul_cancel, pact_one]

theorem mem_DW {a : Wr 6} : a ∈ DW ↔ wsum a = 0 ∧ InP16 a.perm := Iff.rfl

theorem DW_le_Wsub : DW ≤ Wsub := fun _ ha => ha.1

theorem inP16_swapsOf : ∀ d, InP16 (swapsOf d) := by decide

theorem SW_le_DW : SW ≤ DW := fun a ha => by
  obtain ⟨x, rfl⟩ := mem_SW_iff.mp ha
  exact ⟨cS_mem_Wsub x.1 x.2, inP16_swapsOf x.2⟩

theorem card_P16 : Fintype.card {σ : Perm (Fin 6) // InP16 σ} = 16 := by decide +kernel

theorem card_DW : Nat.card DW = 512 := by
  have h1 : Nat.card DW = Nat.card ({v : Fin 6 → ZMod 2 // ∑ i, v i = 0} ×
      {σ : Perm (Fin 6) // InP16 σ}) :=
    Nat.card_congr
      { toFun := fun a => (⟨(a : Wr 6).vec, a.2.1⟩, ⟨(a : Wr 6).perm, a.2.2⟩)
        invFun := fun p => ⟨⟨p.1.1, p.2.1⟩, p.1.2, p.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : Nat.card {v : Fin 6 → ZMod 2 // ∑ i, v i = 0} = 32 := by
    rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [h1, Nat.card_prod, h2, Nat.card_eq_fintype_card, card_P16]

theorem inS_conj_wp_of_commute : ∀ π : Perm (Fin 6), π * pairInv = pairInv * π →
    ∀ x : SC, InS (wp π * cSp x * (wp π)⁻¹) := by decide +kernel

theorem pairConst_conj_vec : ∀ (u : Fin 6 → ZMod 2) (d : Fin 3 → ZMod 2) (i : Fin 6),
    (u + pact (swapsOf d) u) (partner i) = (u + pact (swapsOf d) u) i := by decide

theorem inS_conj_vec (u : Fin 6 → ZMod 2) {a : Wr 6} (ha : InS a) :
    InS ((⟨u, 1⟩ : Wr 6) * a * (⟨u, 1⟩ : Wr 6)⁻¹) := by
  obtain ⟨x, rfl⟩ := exists_cSp_of_inS ha
  have hx := inS_cSp x
  rw [show cSp x = ⟨bv x.1, swapsOf x.2⟩ from rfl, conj_mkVec]
  refine ⟨fun i => ?_, (inS_cSp x).2⟩
  have h1 := pairConst_conj_vec u x.2 i
  have h2 : bv x.1 (partner i) = bv x.1 i := hx.1 i
  calc (u + bv x.1 + pact (swapsOf x.2) u) (partner i)
      = bv x.1 (partner i) + (u + pact (swapsOf x.2) u) (partner i) := by
        simp only [Pi.add_apply]; ring
    _ = bv x.1 i + (u + pact (swapsOf x.2) u) i := by rw [h1, h2]
    _ = (u + bv x.1 + pact (swapsOf x.2) u) i := by simp only [Pi.add_apply]; ring

@[expose] def X0W : Subgroup (Wr 6) where
  carrier := {a | wsum a = 0 ∧ a.perm * pairInv = pairInv * a.perm}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [wsum_mul, ha.1, hb.1, add_zero]
    · show a.perm * b.perm * pairInv = pairInv * (a.perm * b.perm)
      rw [mul_assoc, hb.2, ← mul_assoc, ha.2, mul_assoc]
  one_mem' := ⟨wsum_one, by rw [Wr.one_perm, one_mul, mul_one]⟩
  inv_mem' {a} ha := by
    refine ⟨by rw [wsum_inv]; exact ha.1, ?_⟩
    show a.perm⁻¹ * pairInv = pairInv * a.perm⁻¹
    exact (Commute.inv_left (show Commute a.perm pairInv from ha.2)).eq

theorem conj_mem_SW_of_mem_X0W {a b : Wr 6} (ha : a ∈ X0W) (hb : b ∈ SW) : a * b * a⁻¹ ∈ SW := by
  obtain ⟨x, rfl⟩ := mem_SW_iff.mp hb
  obtain ⟨u, π⟩ := a
  have hsplit : (⟨u, π⟩ : Wr 6) = ⟨u, 1⟩ * wp π := Wr.ext (funext fun i => by
    show u i = u i + (0 : Fin 6 → ZMod 2) ((1 : Perm (Fin 6)).symm i)
    simp) (by simp [wp, Wr.mul_perm])
  rw [hsplit, mul_inv_rev, show ∀ p q r s : Wr 6, p * q * r * (s * p⁻¹) = p * (q * r * s) * p⁻¹ by
    intros; group]
  exact inS_conj_vec u (inS_conj_wp_of_commute π ha.2 x)

theorem mk_eq_vec_mul_wp (v : Fin 6 → ZMod 2) (σ : Perm (Fin 6)) :
    (⟨v, σ⟩ : Wr 6) = ⟨v, 1⟩ * wp σ :=
  Wr.ext (funext fun i => by
    show v i = v i + (0 : Fin 6 → ZMod 2) ((1 : Perm (Fin 6)).symm i)
    simp) (by simp [wp, Wr.mul_perm])

@[expose] def m5Perms : List (Perm (Fin 6)) :=
  [1, swap 1 2, swap 1 3 * swap 1 2, swap 3 4, swap 3 5 * swap 3 4,
    swap 1 4 * swap 1 2 * swap 3 5, swap 1 5 * swap 1 3 * swap 1 4 * swap 1 2]

@[expose] def p16List : List (Perm (Fin 6)) :=
  [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2,
    swap 0 2 * swap 1 3 * swap 0 1, swap 0 2 * swap 1 3 * swap 2 3]
    |>.flatMap fun σ => [σ, σ * swap 4 5]

set_option maxRecDepth 100000 in
theorem mem_p16List : ∀ σ : Perm (Fin 6), InP16 σ → σ ∈ p16List := by decide +kernel

set_option maxRecDepth 100000 in
theorem exists_perm_conj_inS' : ∀ σ ∈ p16List, σ * σ = 1 →
    ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → v + pact σ v = 0 →
      ∃ π ∈ m5Perms, InS ⟨pact π v, π * σ * π⁻¹⟩ := by decide +kernel

theorem exists_perm_conj_inS (σ : Perm (Fin 6)) (hσ : InP16 σ) (h2 : σ * σ = 1)
    (v : Fin 6 → ZMod 2) (hv : ∑ i, v i = 0) (hvv : v + pact σ v = 0) :
    ∃ π : Perm (Fin 6), InS ⟨pact π v, π * σ * π⁻¹⟩ := by
  obtain ⟨π, -, hπ⟩ := exists_perm_conj_inS' σ (mem_p16List σ hσ) h2 v hv hvv
  exact ⟨π, hπ⟩

theorem wp_mem_Wsub (π : Perm (Fin 6)) : wp π ∈ Wsub := by
  show ∑ i, (0 : Fin 6 → ZMod 2) i = 0
  simp

theorem exists_conj_mem_SW {a : Wr 6} (ha : a ∈ DW) (h2 : a * a = 1) :
    ∃ g ∈ Wsub, g * a * g⁻¹ ∈ SW := by
  obtain ⟨v, σ⟩ := a
  obtain ⟨π, hπ⟩ := exists_perm_conj_inS σ ha.2 (congrArg Wr.perm h2) v ha.1
    (congrArg Wr.vec h2)
  exact ⟨wp π, wp_mem_Wsub π, by rw [conj_wp]; exact hπ⟩

theorem pact_P16_center : ∀ σ : Perm (Fin 6), InP16 σ →
    pact σ (fun _ => 1) = (fun _ => 1) ∧ pact σ (v6 [4, 5]) = v6 [4, 5] ∧
      pact σ (v6 [0, 1, 2, 3]) = v6 [0, 1, 2, 3] := by
  intro σ hσ
  have h := mem_p16List σ hσ
  revert h
  revert σ
  decide +kernel

theorem vec_commute_of_pact {w : Fin 6 → ZMod 2} {a : Wr 6} (h : pact a.perm w = w) :
    a * ⟨w, 1⟩ = ⟨w, 1⟩ * a := by
  obtain ⟨v, σ⟩ := a
  refine Wr.ext ?_ (by simp [Wr.mul_perm])
  show v + pact σ w = w + pact 1 v
  rw [h, pact_one, add_comm]

theorem commute_wPi3_of_mem_DW {a : Wr 6} (ha : a ∈ DW) : a * wPi3 = wPi3 * a :=
  vec_commute_of_pact (pact_P16_center a.perm ha.2).2.1

theorem commute_wPi12_of_mem_DW {a : Wr 6} (ha : a ∈ DW) : a * wPi12 = wPi12 * a :=
  vec_commute_of_pact (pact_P16_center a.perm ha.2).2.2

@[expose] def tauP : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def uVecs : List (Fin 6 → ZMod 2) := [0, v6 [0, 2], v6 [0, 4], v6 [2, 4]]

theorem uVecs_add : ∀ v ∈ uVecs, ∀ w ∈ uVecs, v + w ∈ uVecs := by decide

theorem uVecs_pact : ∀ w ∈ uVecs, pact tauP w ∈ uVecs := by decide

theorem uVecs_pact_inv : ∀ w ∈ uVecs, pact tauP⁻¹ w ∈ uVecs := by decide

theorem tauP_mul_self : tauP * tauP = 1 := by decide

theorem tauP_inv : tauP⁻¹ = tauP := by decide

@[expose] def InU (a : Wr 6) : Prop := (a.perm = 1 ∨ a.perm = tauP) ∧ a.vec ∈ uVecs

theorem pact_mem_uVecs {σ : Perm (Fin 6)} (hσ : σ = 1 ∨ σ = tauP) {w : Fin 6 → ZMod 2}
    (hw : w ∈ uVecs) : pact σ w ∈ uVecs := by
  rcases hσ with rfl | rfl
  · exact hw
  · exact uVecs_pact w hw

@[expose] def UW : Subgroup (Wr 6) where
  carrier := {a | InU a}
  mul_mem' {a b} ha hb := by
    obtain ⟨v, σ⟩ := a
    obtain ⟨w, τ⟩ := b
    refine ⟨?_, uVecs_add _ ha.2 _ (pact_mem_uVecs ha.1 hb.2)⟩
    show σ * τ = 1 ∨ σ * τ = tauP
    rcases ha.1 with h1 | h1 <;> rcases hb.1 with h2 | h2 <;> subst h1 <;> subst h2
    · left; rfl
    · right; exact one_mul _
    · right; exact mul_one _
    · left; exact tauP_mul_self
  one_mem' := ⟨Or.inl rfl, by decide⟩
  inv_mem' {a} ha := by
    obtain ⟨v, σ⟩ := a
    rw [mk_inv]
    refine ⟨?_, ?_⟩
    · rcases ha.1 with h | h <;> subst h
      · left; rfl
      · right; exact tauP_inv
    · rcases ha.1 with h | h <;> subst h
      · exact ha.2
      · exact uVecs_pact_inv v ha.2

theorem uVecs_sum : ∀ w ∈ uVecs, ∑ i, w i = 0 := by decide

theorem inP16_one : InP16 1 := by decide

theorem inP16_tauP : InP16 tauP := by decide

theorem UW_le_DW : UW ≤ DW := fun a ha =>
  ⟨uVecs_sum _ ha.2, by rcases ha.1 with h | h <;> rw [h]; exacts [inP16_one, inP16_tauP]⟩

theorem uVecs_pairConst : ∀ w ∈ uVecs, (∀ i, w (partner i) = w i) → w = 0 := by decide

theorem tauP_not_pair : ¬ (∀ i, tauP i = i ∨ tauP i = partner i) := by decide

theorem UW_inf_SW : UW ⊓ SW = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun a ha => ?_
  obtain ⟨⟨hp, hv⟩, hS⟩ := ha
  have hp1 : a.perm = 1 := hp.resolve_right fun h => tauP_not_pair (h ▸ hS.2)
  have hv0 : a.vec = 0 := uVecs_pairConst _ hv hS.1
  exact Wr.ext hv0 hp1

theorem card_UW : Nat.card UW = 8 := by
  classical
  have h : Nat.card UW = Nat.card ({σ : Perm (Fin 6) // σ = 1 ∨ σ = tauP} ×
      {v : Fin 6 → ZMod 2 // v ∈ uVecs}) :=
    Nat.card_congr
      { toFun := fun a => (⟨(a : Wr 6).perm, a.2.1⟩, ⟨(a : Wr 6).vec, a.2.2⟩)
        invFun := fun p => ⟨⟨p.2.1, p.1.1⟩, p.1.2, p.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h, Nat.card_prod]
  have h1 : Nat.card {σ : Perm (Fin 6) // σ = 1 ∨ σ = tauP} = 2 := by
    have : Nat.card {σ : Perm (Fin 6) // σ = 1 ∨ σ = tauP} =
        ({1, tauP} : Set (Perm (Fin 6))).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [this, Set.ncard_pair (by decide)]
  have h2 : Nat.card {v : Fin 6 → ZMod 2 // v ∈ uVecs} = 4 := by
    have : Nat.card {v : Fin 6 → ZMod 2 // v ∈ uVecs} =
        ((uVecs.toFinset : Finset (Fin 6 → ZMod 2)) : Set (Fin 6 → ZMod 2)).ncard := by
      rw [← Nat.card_coe_set_eq]
      congr 1
    rw [this, Set.ncard_coe_finset]
    decide
  rw [h1, h2]

theorem card_SW : Nat.card SW = 64 := by
  have h : Nat.card SW = Nat.card SC := Nat.card_congr
    { toFun := fun a => (exists_cSp_of_inS a.2).choose
      invFun := fun x => ⟨cSp x, cSp_mem_SW x⟩
      left_inv := fun a => Subtype.ext (exists_cSp_of_inS a.2).choose_spec.symm
      right_inv := fun x => by
        have h1 := (exists_cSp_of_inS (cSp_mem_SW x)).choose_spec
        have h2 := cS_injective h1
        exact Prod.ext h2.1.symm h2.2.symm }
  rw [h, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  norm_num

theorem UW_sup_SW : UW ⊔ SW = DW := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le UW_le_DW SW_le_DW) ?_
  rw [card_DW]
  have hinj : Function.Injective (fun p : ↥UW × ↥SW => ((p.1 : Wr 6) * p.2 : Wr 6)) := by
    rintro ⟨u, s⟩ ⟨u', s'⟩ h
    have h1 : (u' : Wr 6)⁻¹ * u = s' * (s : Wr 6)⁻¹ := by
      have := congrArg (fun x => (u' : Wr 6)⁻¹ * x * (s : Wr 6)⁻¹) h
      simpa [mul_assoc] using this
    have hU : (u' : Wr 6)⁻¹ * u ∈ UW := UW.mul_mem (UW.inv_mem u'.2) u.2
    have hS : s' * (s : Wr 6)⁻¹ ∈ SW := SW.mul_mem s'.2 (SW.inv_mem s.2)
    have h2 : (u' : Wr 6)⁻¹ * u = 1 := by
      have : (u' : Wr 6)⁻¹ * u ∈ UW ⊓ SW := ⟨hU, h1 ▸ hS⟩
      rw [UW_inf_SW] at this
      exact this
    have hu : u = u' := Subtype.ext (inv_mul_eq_one.mp h2).symm
    subst hu
    have hs : (s : Wr 6) = s' := mul_left_cancel h
    exact Prod.ext rfl (Subtype.ext hs)
  have hle : Nat.card (↥UW × ↥SW) ≤ Nat.card ↥(UW ⊔ SW) :=
    Nat.card_le_card_of_injective
      (fun p => ⟨(p.1 : Wr 6) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
        (Subgroup.mem_sup_right p.2.2)⟩)
      (fun p q h => hinj (congrArg Subtype.val h))
  rw [Nat.card_prod, card_UW, card_SW] at hle
  exact hle

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

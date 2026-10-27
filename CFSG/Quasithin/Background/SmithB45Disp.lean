module

public import CFSG.Quasithin.Background.SmithB42Disp
public import CFSG.Quasithin.Background.SmithB45Families

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

namespace B45Disp

open CFSG.QuasithinUnique.Setup.X5 CFSG.ComponentClassification B42Disp

section Offender

variable {V : Type*} [CommGroup V]

@[expose] def Is2FStar (X A : Subgroup (MulAut V)) : Prop :=
  A ≤ X ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
    ∀ B : Subgroup (MulAut V), B ≤ A →
      Nat.card B ^ 2 * Nat.card (fixV B) ≤ Nat.card A ^ 2 * Nat.card (fixV A)

variable [Finite V]

omit [Finite V] in
theorem card_bot_sq_mul_card_fixV :
    Nat.card (⊥ : Subgroup (MulAut V)) ^ 2 * Nat.card (fixV (⊥ : Subgroup (MulAut V))) =
      Nat.card V := by
  rw [Subgroup.card_bot, one_pow, one_mul, B1.fixV_bot, Subgroup.card_top]

omit [Finite V] in
theorem Is2FStar.card_le {X A : Subgroup (MulAut V)} (h : Is2FStar X A) :
    Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A) := by
  have h1 := h.2.2.2 ⊥ bot_le
  rwa [card_bot_sq_mul_card_fixV] at h1

theorem exists_is2FStar {X A : Subgroup (MulAut V)} (hA : IsA2 X A)
    (hoff : Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A)) : ∃ B ≤ A, Is2FStar X B := by
  have : Finite (MulAut V) := finite_mulAut
  have : Finite (Subgroup (MulAut V)) :=
    Finite.of_injective (fun H : Subgroup (MulAut V) => (H : Set (MulAut V)))
      SetLike.coe_injective
  set S : Set (Subgroup (MulAut V)) := {B | B ≤ A ∧ B ≠ ⊥} with hS
  obtain ⟨B, ⟨hBA, hB1⟩, hmax⟩ := Set.exists_max_image S
    (fun B => Nat.card B ^ 2 * Nat.card (fixV B)) (Set.toFinite S) ⟨A, le_rfl, hA.2.1⟩
  refine ⟨B, hBA, hBA.trans hA.1, hB1, ⟨fun a ha b hb => hA.2.2.1 a (hBA ha) b (hBA hb),
    fun a ha => hA.2.2.2 a (hBA ha)⟩, fun C hC => ?_⟩
  by_cases hC1 : C = ⊥
  · subst hC1
    rw [card_bot_sq_mul_card_fixV]
    exact hoff.trans (hmax A ⟨le_rfl, hA.2.1⟩)
  · exact hmax C ⟨hC.trans hBA, hC1⟩

theorem index_fixV_le_card_sq_of_le {E : Subgroup (MulAut V)}
    (hoff : Nat.card V ≤ Nat.card E ^ 2 * Nat.card (fixV E)) :
    (fixV E).index ≤ Nat.card E ^ 2 := by
  have h2 := (fixV E).card_mul_index
  have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  rw [h2, mul_comm]
  exact hoff

theorem index_fixV_le_card_sq {E : Subgroup (MulAut V)}
    (hoff : Nat.card V ≤ Nat.card E ^ 2 * Nat.card (fixV E)) {x : MulAut V} (hx : x ∈ E) :
    (fixV (Subgroup.zpowers x)).index ≤ Nat.card E ^ 2 :=
  (index_fixV_antitone ((Subgroup.zpowers_le).2 hx)).trans (index_fixV_le_card_sq_of_le hoff)

omit [Finite V] in
theorem Is2FStar.conjAut {X A : Subgroup (MulAut V)} (h : Is2FStar X A) {g : MulAut V}
    (hg : g ∈ X) : Is2FStar X (B1.conjAut g A) := by
  refine ⟨B1.conjAut_le hg h.1, B1.conjAut_ne_bot h.2.1, B1.isElemAbelian2_conjAut h.2.2.1,
    fun B hB => ?_⟩
  have hB' : B1.conjAut g⁻¹ B ≤ A := by
    have := (B1.conjAut_le_iff (g := g⁻¹)).2 hB
    rwa [B1.conjAut_inv_conjAut] at this
  have e1 : Nat.card B = Nat.card (B1.conjAut g⁻¹ B) := by
    conv_lhs => rw [← B1.conjAut_conjAut_inv g B]
    exact B1.card_conjAut g _
  have e2 : Nat.card (fixV B) = Nat.card (fixV (B1.conjAut g⁻¹ B)) := by
    conv_lhs => rw [← B1.conjAut_conjAut_inv g B]
    exact B1.card_fixV_conjAut g _
  rw [B1.card_conjAut, B1.card_fixV_conjAut, e1, e2]
  exact h.2.2.2 _ hB'

theorem weight2_le_weight2_sup {X B Λ : Subgroup (MulAut V)} (hB : Is2FStar X B)
    (hc : ∀ x ∈ Λ, ∀ b ∈ B, x * b = b * x) :
    Nat.card Λ ^ 2 * Nat.card (fixV Λ) ≤ Nat.card (Λ ⊔ B : Subgroup (MulAut V)) ^ 2 *
      Nat.card (fixV (Λ ⊔ B)) := by
  have : Finite (MulAut V) := finite_mulAut
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Λ B hc
  obtain ⟨h2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixV Λ) (fixV B)
    (fun x _ y _ => mul_comm x y)
  have hle : fixV Λ ⊔ fixV B ≤ fixV (Λ ⊓ B) :=
    sup_le (fixV_antitone inf_le_left) (fixV_antitone inf_le_right)
  have h3 := Subgroup.card_le_of_le hle
  have h4 := hB.2.2.2 (Λ ⊓ B) inf_le_right
  rw [fixV_sup]
  have hpos1 : 0 < Nat.card (Λ ⊓ B : Subgroup (MulAut V)) := Nat.card_pos
  have hpos2 : 0 < Nat.card (fixV Λ ⊔ fixV B : Subgroup V) := Nat.card_pos
  have hbd : Nat.card (Λ ⊓ B : Subgroup (MulAut V)) ^ 2 *
      Nat.card (fixV Λ ⊔ fixV B : Subgroup V) ≤ Nat.card B ^ 2 * Nat.card (fixV B) :=
    (Nat.mul_le_mul_left _ h3).trans h4
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos (pow_pos hpos1 2) hpos2)
  calc Nat.card Λ ^ 2 * Nat.card (fixV Λ) * (Nat.card (Λ ⊓ B : Subgroup (MulAut V)) ^ 2 *
        Nat.card (fixV Λ ⊔ fixV B : Subgroup V))
      ≤ Nat.card Λ ^ 2 * Nat.card (fixV Λ) * (Nat.card B ^ 2 * Nat.card (fixV B)) :=
        Nat.mul_le_mul_left _ hbd
    _ = (Nat.card (Λ ⊔ B : Subgroup (MulAut V)) * Nat.card (Λ ⊓ B : Subgroup (MulAut V))) ^ 2 *
        (Nat.card (fixV Λ ⊔ fixV B : Subgroup V) * Nat.card (fixV Λ ⊓ fixV B : Subgroup V)) := by
        rw [h1, h2]
        ring
    _ = Nat.card (Λ ⊔ B : Subgroup (MulAut V)) ^ 2 * Nat.card (fixV Λ ⊓ fixV B : Subgroup V) *
        (Nat.card (Λ ⊓ B : Subgroup (MulAut V)) ^ 2 *
          Nat.card (fixV Λ ⊔ fixV B : Subgroup V)) := by
        ring

theorem card_le_weight2_closure_conj {X A : Subgroup (MulAut V)} (hA : Is2FStar X A)
    (ks : List (MulAut V)) (hks : ∀ k ∈ ks, k ∈ X)
    (hcomm : ∀ k ∈ ks, ∀ k' ∈ ks, ∀ a ∈ A, ∀ b ∈ A,
      k * a * k⁻¹ * (k' * b * k'⁻¹) = k' * b * k'⁻¹ * (k * a * k⁻¹)) :
    Nat.card V ≤ Nat.card (Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹}) ^ 2 *
      Nat.card (fixV (Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹})) := by
  induction ks with
  | nil =>
    have h : {y : MulAut V | ∃ k ∈ ([] : List (MulAut V)), ∃ a ∈ A, y = k * a * k⁻¹} = ∅ := by
      ext y
      simp
    rw [h, Subgroup.closure_empty, card_bot_sq_mul_card_fixV]
  | cons k ks ih =>
    have ih' := ih (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      (fun k₁ h₁ k₂ h₂ => hcomm k₁ (List.mem_cons_of_mem _ h₁) k₂ (List.mem_cons_of_mem _ h₂))
    set Λ := Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} with hΛ
    have hset : {y | ∃ k' ∈ k :: ks, ∃ a ∈ A, y = k' * a * k'⁻¹} =
        {y | ∃ k' ∈ ks, ∃ a ∈ A, y = k' * a * k'⁻¹} ∪ (B1.conjAut k A : Set (MulAut V)) := by
      ext y
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union, SetLike.mem_coe,
        B1.mem_conjAut]
      constructor
      · rintro ⟨k', hk' | hk', a, ha, rfl⟩
        · subst hk'
          right
          simpa [mul_assoc] using ha
        · exact Or.inl ⟨k', hk', a, ha, rfl⟩
      · rintro (⟨k', hk', a, ha, rfl⟩ | h)
        · exact ⟨k', Or.inr hk', a, ha, rfl⟩
        · exact ⟨k, Or.inl rfl, k⁻¹ * y * k, h, by group⟩
    have hcl : Subgroup.closure {y | ∃ k' ∈ k :: ks, ∃ a ∈ A, y = k' * a * k'⁻¹} =
        Λ ⊔ B1.conjAut k A := by
      rw [hset, Subgroup.closure_union, Subgroup.closure_eq]
    rw [hcl]
    have hc : ∀ x ∈ Λ, ∀ b ∈ B1.conjAut k A, x * b = b * x := by
      intro x hx b hb
      have hle : Λ ≤ Subgroup.centralizer (B1.conjAut k A : Set (MulAut V)) := by
        rw [hΛ, Subgroup.closure_le]
        rintro _ ⟨k', hk', a, ha, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro b' hb'
        have hb'' := B1.mem_conjAut.1 hb'
        have := hcomm k (List.mem_cons_self ..) k' (List.mem_cons_of_mem _ hk') _ hb'' a ha
        calc b' * (k' * a * k'⁻¹) = k * (k⁻¹ * b' * k) * k⁻¹ * (k' * a * k'⁻¹) := by group
          _ = k' * a * k'⁻¹ * (k * (k⁻¹ * b' * k) * k⁻¹) := this
          _ = k' * a * k'⁻¹ * b' := by group
      exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) b hb).symm
    exact ih'.trans (weight2_le_weight2_sup (hA.conjAut (hks k (List.mem_cons_self ..))) hc)

end Offender

@[expose] def DispAtOut (M : Type*) [Group M] (Q : ℕ → Prop) (α : MulAut M) (n : ℕ) : Prop :=
  ∃ (ℓ : ℕ) (c m : M), Q ℓ ∧ ℓ.Prime ∧ ℓ ≠ 2 ∧ α ∉ (MulAut.conj : M →* MulAut M).range ∧
    α c = c⁻¹ ∧ ℓ ∣ orderOf c ∧ m * α m = 1 ∧ m * α c * m⁻¹ = c ∧
    n ^ 2 < 2 ^ orderOf (2 : ZMod ℓ)

section Double

variable {V : Type*} [CommGroup V]

@[expose] def DoubleDispOut (L : Subgroup (MulAut V)) (Q : ℕ → Prop) : Prop :=
  ∀ ℓ : ℕ, Q ℓ → ℓ.Prime → ℓ ≠ 2 → ∀ g : MulAut V, g ∈ L → ℓ ∣ orderOf g →
    (∃ δ ∈ Subgroup.normalizer (L : Set (MulAut V)), δ * δ = 1 ∧ δ ∉ L ∧ δ * g = g * δ) →
    2 ^ (2 * orderOf (2 : ZMod ℓ)) ≤ (fixV (Subgroup.zpowers g)).index

variable [Finite V]

theorem doubleDispOut_of_orderOf_eq {L : Subgroup (MulAut V)} {Q : ℕ → Prop}
    (h : ∀ ℓ : ℕ, Q ℓ → ℓ.Prime → ℓ ≠ 2 → ∀ g : MulAut V, g ∈ L → orderOf g = ℓ →
      (∃ δ ∈ Subgroup.normalizer (L : Set (MulAut V)), δ * δ = 1 ∧ δ ∉ L ∧ δ * g = g * δ) →
      2 ^ (2 * orderOf (2 : ZMod ℓ)) ≤ (fixV (Subgroup.zpowers g)).index) :
    DoubleDispOut L Q := by
  rintro ℓ hQ hℓ hℓ2 g hg hdvd ⟨δ, hδN, hδ2, hδL, hδg⟩
  have : Finite (MulAut V) := finite_mulAut
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hord := orderOf_pow_orderOf_div hpos hdvd
  have hcomm : δ * g ^ (orderOf g / ℓ) = g ^ (orderOf g / ℓ) * δ :=
    ((show Commute δ g from hδg).pow_right _).eq
  refine (h ℓ hQ hℓ hℓ2 _ (L.pow_mem hg _) hord ⟨δ, hδN, hδ2, hδL, hcomm⟩).trans ?_
  exact index_fixV_antitone ((Subgroup.zpowers_le).2
    (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _))

theorem sq_lt_index_of_dispAtOut (L : Subgroup (MulAut V)) (hperf : Group.IsPerfect L)
    (hZL : Subgroup.center L = ⊥) {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M)
    {Q : ℕ → Prop} (hDQ : DoubleDispOut L Q) (x : Subgroup.normalizer (L : Set (MulAut V)))
    (hx2 : (x : MulAut V) * x = 1) {n : ℕ} (h : DispAtOut M Q (modelAct L e x) n) :
    n ^ 2 < (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  have := hperf
  obtain ⟨ℓ, c, m, hQ, hℓ, hℓ2, hαo, hαc, hdvd, hm, hmc, hlt⟩ := h
  set α := modelAct L e x with hαdef
  set π := modelProj L e with hπ
  have hxi : (x : MulAut V)⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hconj : ∀ l : L, π (conjOn L x l) = α (π l) := fun l => by
    rw [hπ, modelProj_apply, modelProj_apply, hαdef, modelAct_apply_mk]
  obtain ⟨l, hl⟩ := exists_lift L e c⁻¹
  obtain ⟨l', hl'⟩ := exists_lift L e m
  have hπl : π l = c⁻¹ := by rw [hπ, modelProj_apply, hl]
  have hπl' : π l' = m := by rw [hπ, modelProj_apply, hl']
  set g : L := conjOn L x l * l⁻¹ with hg
  have hgV : (g : MulAut V) = x * ((l : MulAut V) * x * (l : MulAut V)⁻¹) := by
    rw [hg, Subgroup.coe_mul, coe_conjOn, Subgroup.coe_inv]
    calc (x : MulAut V) * l * (x : MulAut V)⁻¹ * (l : MulAut V)⁻¹ =
        (x : MulAut V) * l * x * (l : MulAut V)⁻¹ := by rw [hxi]
      _ = _ := by group
  have hπg : π g = c ^ 2 := by
    rw [hg, map_mul, map_inv, hconj, hπl, map_inv, hαc, inv_inv, sq]
  have hdvdg : ℓ ∣ orderOf (g : MulAut V) := by
    rw [Subgroup.orderOf_coe]
    have h1 : ℓ ∣ orderOf (c ^ 2) := dvd_orderOf_sq hℓ hℓ2 hdvd
    rw [← hπg] at h1
    exact h1.trans (orderOf_map_dvd _ _)
  set δ : MulAut V := (l' : MulAut V) * x with hδ
  have hδN : δ ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    mul_mem (Subgroup.le_normalizer l'.2) x.2
  have hδL : δ ∉ L := by
    intro hδ'
    have hxL : (x : MulAut V) ∈ L := by
      have e1 : (x : MulAut V) = (l' : MulAut V)⁻¹ * δ := by rw [hδ]; group
      rw [e1]
      exact mul_mem (inv_mem l'.2) hδ'
    exact hαo ⟨e (QuotientGroup.mk ⟨x, hxL⟩), (modelAct_of_mem L e hxL).symm⟩
  have hδ2 : δ * δ = 1 := by
    have hmem : l' * conjOn L x l' ∈ Subgroup.center L := by
      apply mem_center_of_modelProj_eq_one L e
      rw [← hπ, map_mul, hconj, hπl', hm]
    rw [hZL, Subgroup.mem_bot] at hmem
    have h1 := congrArg Subtype.val hmem
    rw [Subgroup.coe_mul, coe_conjOn, OneMemClass.coe_one] at h1
    calc δ * δ = (l' : MulAut V) * ((x : MulAut V) * l' * (x : MulAut V)⁻¹) := by
          rw [hδ, hxi]; group
      _ = 1 := h1
  have hδg : δ * (g : MulAut V) = g * δ := by
    have hmem : l' * conjOn L x g * l'⁻¹ * g⁻¹ ∈ Subgroup.center L := by
      apply mem_center_of_modelProj_eq_one L e
      rw [← hπ, map_mul, map_mul, map_mul, map_inv, map_inv, hconj, hπl', hπg]
      have e1 : m * α (c ^ 2) * m⁻¹ = c ^ 2 := by
        rw [map_pow, sq, sq]
        calc m * (α c * α c) * m⁻¹ = (m * α c * m⁻¹) * (m * α c * m⁻¹) := by group
          _ = c * c := by rw [hmc]
      rw [e1, mul_inv_cancel]
    rw [hZL, Subgroup.mem_bot] at hmem
    have h1 := congrArg Subtype.val hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn, OneMemClass.coe_one] at h1
    have h2 : (l' : MulAut V) * ((x : MulAut V) * g * (x : MulAut V)⁻¹) * (l' : MulAut V)⁻¹ =
        g := mul_inv_eq_one.1 h1
    calc δ * (g : MulAut V) =
        (l' : MulAut V) * ((x : MulAut V) * g * (x : MulAut V)⁻¹) * (l' : MulAut V)⁻¹ * δ := by
          rw [hδ]; group
      _ = g * δ := by rw [h2]
  have h1 := hDQ ℓ hQ hℓ hℓ2 (g : MulAut V) g.2 hdvdg ⟨δ, hδN, hδ2, hδL, hδg⟩
  have h2 : (fixV (Subgroup.zpowers (g : MulAut V))).index ≤
      (fixV (Subgroup.zpowers (x : MulAut V))).index ^ 2 := by
    rw [hgV, sq]
    refine (index_fixV_mul_le _ _).trans ?_
    rw [index_fixV_conj]
  have h5 : (n ^ 2) ^ 2 < 2 ^ (2 * orderOf (2 : ZMod ℓ)) := by
    calc (n ^ 2) ^ 2 < (2 ^ orderOf (2 : ZMod ℓ)) ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
      _ = 2 ^ (2 * orderOf (2 : ZMod ℓ)) := by ring
  by_contra hle
  push Not at hle
  have h4 := Nat.pow_le_pow_left hle 2
  omega

end Double

theorem b4Hyp_data {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) :
    Nontrivial V ∧ Group.IsPerfect ↥L ∧
      (∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      L ≤ G ∧ G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  obtain ⟨-, hLeq, hq, hirr⟩ := hHyp
  refine ⟨?_, hq.1, Bridge.TypeList.irr_of_isIrrSec hirr, ?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hirr.1
    exact ⟨⟨x, 1, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _)⟩⟩
  · rw [hLeq]
    exact quasithinGenFitting_le G
  · rw [hLeq]
    exact le_normalizer_quasithinGenFitting G

theorem odd_card_center_of_isIrrSec {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) : Odd (Nat.card (Subgroup.center ↥L)) := by
  have : Nontrivial V := by
    obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hirr.1
    exact ⟨⟨x, 1, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _)⟩⟩
  exact odd_card_center L (centralizer_odd (fun v => by rw [← pow_two]; exact hV v) L
    (Bridge.TypeList.irr_of_isIrrSec hirr))


end B45Disp

theorem AsB45No2FFor.or {P Q : ∀ (X : Type) [Group X], Prop} (hP : AsB45No2FFor P)
    (hQ : AsB45No2FFor Q) : AsB45No2FFor (fun (X : Type) [Group X] => P X ∨ Q X) := by
  intro V _ _ hV G L hHyp hPQ
  rcases hPQ with h | h
  · exact hP V hV G L hHyp h
  · exact hQ V hV G L hHyp h

end CFSG.Quasithin

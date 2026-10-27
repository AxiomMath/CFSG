module

public import CFSG.Quasithin.H13.VolIAltCoverEightVec
public import CFSG.Quasithin.H13.VolIAltCoverUniversal
public import CFSG.Quasithin.H13.VolIAltCoverSeven
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

structure AltCover8 (V : Type*) [CommGroup V] where
  ρ : ↥(alternatingGroup (Fin 8)) →* MulAut V
  β : V →* DnQuot 8
  surj : Function.Surjective β
  fix : ∀ σ v, β v = 1 → ρ σ v = v
  equiv : ∀ σ v (m : ↥(coreMod 8)), β v = QuotientGroup.mk m →
    β (ρ σ v) = QuotientGroup.mk (coreAct 8 (σ : Perm (Fin 8)) m)
  gen : ∀ v : V, v ∈ closure {x | ∃ σ w, x = ρ σ w * w⁻¹}

@[expose] def ModelCover.toAltCover8 {V : Type*} [CommGroup V]
    (C : ModelCover (FFModel.altDn 8) V) : AltCover8 V where
  ρ := C.ρ
  β := C.β
  surj := C.surj
  fix := C.fix
  equiv σ v m h := C.equiv σ v m (permAct_mem_coreMod _ m.2) h
  gen := C.gen

namespace AltCover8

variable {V : Type*} [CommGroup V] (C : AltCover8 V)

theorem β_act8 (σ : ↥(alternatingGroup (Fin 8))) {v : V} {m : ↥(coreMod 8)}
    (h : C.β v = QuotientGroup.mk m) :
    C.β (C.ρ σ v) = QuotientGroup.mk (coreAct 8 (σ : Perm (Fin 8)) m) :=
  C.equiv σ v m h

theorem β_comm8 (σ : ↥(alternatingGroup (Fin 8))) {v : V} {m : ↥(coreMod 8)}
    (h : C.β v = QuotientGroup.mk m) :
    C.β (C.ρ σ v * v⁻¹) = QuotientGroup.mk (coreAct 8 (σ : Perm (Fin 8)) m * m⁻¹) := by
  rw [map_mul, map_inv, C.β_act8 σ h, h, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem β_comm3 (σ τ υ : ↥(alternatingGroup (Fin 8))) {a b c : PermMod 8} (ha : a ∈ coreMod 8)
    (hb : b ∈ coreMod 8) (hc : c ∈ coreMod 8) {u v w : V}
    (hu : C.β u = QuotientGroup.mk ⟨a, ha⟩) (hv : C.β v = QuotientGroup.mk ⟨b, hb⟩)
    (hw : C.β w = QuotientGroup.mk ⟨c, hc⟩) :
    C.β (C.ρ σ u * u⁻¹ * (C.ρ τ v * v⁻¹) * (C.ρ υ w * w⁻¹)) =
      QuotientGroup.mk ⟨comm3 σ τ υ a b c, comm3_mem σ τ υ ha hb hc⟩ := by
  rw [map_mul, map_mul, C.β_comm8 σ hu, C.β_comm8 τ hv, C.β_comm8 υ hw,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem comm_mul8 {M : Subgroup V} {a b : ↥(alternatingGroup (Fin 8))}
    (ha : ∀ v, C.ρ a v * v⁻¹ ∈ M) (hb : ∀ v, C.ρ b v * v⁻¹ ∈ M) (v : V) :
    C.ρ (a * b) v * v⁻¹ ∈ M := by
  have e : C.ρ (a * b) v * v⁻¹ = (C.ρ a (C.ρ b v) * (C.ρ b v)⁻¹) * (C.ρ b v * v⁻¹) := by
    rw [map_mul, MulAut.mul_apply]
    group
  rw [e]
  exact mul_mem (ha _) (hb v)

@[expose] def Y8 : Subgroup V :=
  ((commMap (C.ρ a8c123)).range ⊔ (commMap (C.ρ a8c345)).range) ⊔ (commMap (C.ρ a8c567)).range

theorem comm_mem_Y8 {σ : ↥(alternatingGroup (Fin 8))} (hσ : (σ : Perm (Fin 8)) 0 = 0) (v : V) :
    C.ρ σ v * v⁻¹ ∈ C.Y8 := by
  obtain ⟨σ', rfl⟩ := liftAlt_surj σ hσ
  refine alt7_induction (fun σ' => ∀ v, C.ρ (liftAlt σ') v * v⁻¹ ∈ C.Y8) (fun v => ?_)
    (fun a b ha hb v => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_) σ' v
  · rw [map_one, map_one, MulAut.one_apply, mul_inv_cancel]
    exact one_mem _
  · rw [map_mul]
    exact C.comm_mul8 ha hb v
  · rw [liftAlt_a7c012]
    exact mem_sup_left (mem_sup_left ⟨v, rfl⟩)
  · rw [liftAlt_a7c234]
    exact mem_sup_left (mem_sup_right ⟨v, rfl⟩)
  · rw [liftAlt_a7c456]
    exact mem_sup_right ⟨v, rfl⟩

theorem card_Y8_le [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) : Nat.card C.Y8 ≤ 64 := by
  have hβk : ∀ v, C.β v = 1 ↔ v ∈ C.β.ker := fun v => MonoidHom.mem_ker.symm
  have hc : ∀ t : ↥(alternatingGroup (Fin 8)), t ^ 3 = 1 → ∀ T : Finset (PermMod 8),
      (∀ m : PermMod 8, permAct 8 (t : Perm (Fin 8)) m * m⁻¹ ∈ T) →
      Nat.card (commMap (C.ρ t)).range ≤ T.card := fun t ht T hT =>
    card_commMap_range_le (n := 8) (β := C.β) (t := C.ρ t) (γ := (t : Perm (Fin 8))) hV2 hβk
      (by rw [← map_pow, ht, map_one]) (fun z hz => C.fix t z (MonoidHom.mem_ker.1 hz))
      (fun _ _ h => C.β_act8 t h) T hT
  have h₁ := hc a8c123 a8c123_pow _ comm_mem_evenOn_eight_123
  have h₂ := hc a8c345 a8c345_pow _ comm_mem_evenOn_eight_345
  have h₃ := hc a8c567 a8c567_pow _ comm_mem_evenOn_eight_567
  rw [evenOn_eight_123_card] at h₁
  rw [evenOn_eight_345_card] at h₂
  rw [evenOn_eight_567_card] at h₃
  calc Nat.card C.Y8 ≤
        Nat.card ↥((commMap (C.ρ a8c123)).range ⊔ (commMap (C.ρ a8c345)).range) *
          Nat.card (commMap (C.ρ a8c567)).range := card_sup_le_mul _ _
    _ ≤ (Nat.card (commMap (C.ρ a8c123)).range * Nat.card (commMap (C.ρ a8c345)).range) *
          Nat.card (commMap (C.ρ a8c567)).range :=
        Nat.mul_le_mul_right _ (card_sup_le_mul _ _)
    _ ≤ (4 * 4) * 4 := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃

theorem exists_mem_Y8 (q : DnQuot 8) : ∃ y ∈ C.Y8, C.β y = q := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, b, hb, c, hc, hm⟩ := coreMod_eight_eq m m.2
  obtain ⟨u, hu⟩ := C.surj (QuotientGroup.mk ⟨a, lifts123Eight_mem a ha⟩)
  obtain ⟨v, hv⟩ := C.surj (QuotientGroup.mk ⟨b, lifts345_mem b hb⟩)
  obtain ⟨w, hw⟩ := C.surj (QuotientGroup.mk ⟨c, lifts567_mem c hc⟩)
  refine ⟨C.ρ a8c123 u * u⁻¹ * (C.ρ a8c345 v * v⁻¹) * (C.ρ a8c567 w * w⁻¹),
    mul_mem (mul_mem (mem_sup_left (mem_sup_left ⟨u, rfl⟩))
      (mem_sup_left (mem_sup_right ⟨v, rfl⟩))) (mem_sup_right ⟨w, rfl⟩), ?_⟩
  rw [C.β_comm3 a8c123 a8c345 a8c567 _ _ _ hu hv hw]
  exact mk_eq_mk_iff_eight.2 hm

theorem bijective_Y8 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) :
    Function.Bijective (C.β.comp C.Y8.subtype) := by
  refine Function.Surjective.bijective_of_nat_card_le (fun q => ?_)
    ((C.card_Y8_le hV2).trans card_dnQuot_eight.symm.le)
  obtain ⟨y, hy, rfl⟩ := C.exists_mem_Y8 q
  exact ⟨⟨y, hy⟩, rfl⟩

theorem card_Y8 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) : Nat.card C.Y8 = 64 := by
  rw [Nat.card_congr (Equiv.ofBijective _ (C.bijective_Y8 hV2))]
  exact card_dnQuot_eight

@[expose] def sY8 : Subgroup V := C.Y8.map (C.ρ a8h).toMonoidHom

theorem ρ_h_h (v : V) : C.ρ a8h (C.ρ a8h v) = v := by
  rw [← MulAut.mul_apply, ← map_mul, a8h_mul_self, map_one, MulAut.one_apply]

theorem conj_h_zero {κ : ↥(alternatingGroup (Fin 8))} (hκ : (κ : Perm (Fin 8)) 7 = 7) :
    ((a8h * κ * a8h : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) 0 = 0 := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Perm.mul_apply, Perm.mul_apply, a8h_zero, hκ,
    a8h_seven]

theorem comm_mem_sY8 {κ : ↥(alternatingGroup (Fin 8))} (hκ : (κ : Perm (Fin 8)) 7 = 7)
    (v : V) : C.ρ κ v * v⁻¹ ∈ C.sY8 := by
  refine mem_map.2 ⟨C.ρ (a8h * κ * a8h) (C.ρ a8h v) * (C.ρ a8h v)⁻¹,
    C.comm_mem_Y8 (conj_h_zero hκ) _, ?_⟩
  show C.ρ a8h (C.ρ (a8h * κ * a8h) (C.ρ a8h v) * (C.ρ a8h v)⁻¹) = C.ρ κ v * v⁻¹
  simp only [map_mul, map_inv, MulAut.mul_apply, C.ρ_h_h]

theorem sup_eq_top8 : C.Y8 ⊔ C.sY8 = ⊤ := by
  have hP : ∀ σ : ↥(alternatingGroup (Fin 8)), ∀ v, C.ρ σ v * v⁻¹ ∈ C.Y8 ⊔ C.sY8 := by
    intro σ
    by_cases h0 : (σ : Perm (Fin 8)) 0 = 0
    · exact fun v => mem_sup_left (C.comm_mem_Y8 h0 v)
    · have hr := rep8_spec ((σ : Perm (Fin 8)) 0) h0
      have hk : (((rep8 ((σ : Perm (Fin 8)) 0) * a8c012)⁻¹ * σ :
          ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) 0 = 0 := by
        rw [Subgroup.coe_mul, Perm.mul_apply, Subgroup.coe_inv, Perm.inv_eq_iff_eq,
          Subgroup.coe_mul, Perm.mul_apply, a8c012_zero, hr.2]
      have e : σ = rep8 ((σ : Perm (Fin 8)) 0) * a8c012 *
          ((rep8 ((σ : Perm (Fin 8)) 0) * a8c012)⁻¹ * σ) := by group
      have hg : ∀ v, C.ρ a8c012 v * v⁻¹ ∈ C.Y8 ⊔ C.sY8 := fun v =>
        mem_sup_right (C.comm_mem_sY8 a8_fix.2.2.2.2.2.2 v)
      rw [e]
      exact C.comm_mul8 (C.comm_mul8 (fun v => mem_sup_left (C.comm_mem_Y8 hr.1 v)) hg)
        (fun v => mem_sup_left (C.comm_mem_Y8 hk v))
  rw [eq_top_iff]
  intro v _
  refine (closure_le _).2 ?_ (C.gen v)
  rintro _ ⟨σ, w, rfl⟩
  exact hP σ w

theorem card_inf_ge8 [Finite V] : 32 ≤ Nat.card ↥(C.Y8 ⊓ C.sY8) := by
  obtain ⟨f123, f345, f456, s123, s345, s456, -⟩ := a8_fix
  have hmem : ∀ x (hx : x ∈ evenP8), ∃ u ∈ C.Y8 ⊓ C.sY8,
      C.β u = QuotientGroup.mk ⟨x, mem_coreMod_of_mem_evenP8 hx⟩ := by
    intro x hx
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := evenP8_eq x hx
    obtain ⟨u, hu⟩ := C.surj (QuotientGroup.mk ⟨a, lifts123Eight_mem a ha⟩)
    obtain ⟨v, hv⟩ := C.surj (QuotientGroup.mk ⟨b, lifts345_mem b hb⟩)
    obtain ⟨w, hw⟩ := C.surj (QuotientGroup.mk ⟨c, lifts456_mem c hc⟩)
    exact ⟨_, mem_inf.2 ⟨mul_mem (mul_mem (C.comm_mem_Y8 f123 u) (C.comm_mem_Y8 f345 v))
      (C.comm_mem_Y8 f456 w), mul_mem (mul_mem (C.comm_mem_sY8 s123 u) (C.comm_mem_sY8 s345 v))
      (C.comm_mem_sY8 s456 w)⟩, C.β_comm3 a8c123 a8c345 a8c456 _ _ _ hu hv hw⟩
  let f : ↥evenP8 → ↥((C.Y8 ⊓ C.sY8).map C.β) := fun x =>
    ⟨QuotientGroup.mk ⟨x, mem_coreMod_of_mem_evenP8 x.2⟩, by
      obtain ⟨u, hu, he⟩ := hmem x x.2
      exact mem_map.2 ⟨u, hu, he⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have h' : (QuotientGroup.mk ⟨x, mem_coreMod_of_mem_evenP8 hx⟩ : DnQuot 8) =
        QuotientGroup.mk ⟨y, mem_coreMod_of_mem_evenP8 hy⟩ := congrArg Subtype.val h
    rcases mk_eq_mk_iff_eight.1 h' with h'' | h''
    · exact Subtype.ext h''.symm
    · exact absurd h''.symm (evenP8_allOnes x hx y hy)
  calc 32 = Nat.card ↥evenP8 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, evenP8_card]
    _ ≤ Nat.card ↥((C.Y8 ⊓ C.sY8).map C.β) := Nat.card_le_card_of_injective f hf
    _ ≤ Nat.card ↥(C.Y8 ⊓ C.sY8) :=
        Nat.card_le_card_of_surjective _ (C.β.subgroupMap_surjective _)

include C in
theorem card_le8 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) : Nat.card V ≤ 128 := by
  have hN : C.Y8 ≤ normalizer (C.sY8 : Set V) := by
    rw [normalizer_eq_top]
    exact le_top
  have h := card_sup_mul_card_inf hN
  have hsY : Nat.card C.sY8 = 64 := by
    show Nat.card ↥(C.Y8.map (C.ρ a8h).toMonoidHom) = 64
    rw [card_map_of_injective (f := (C.ρ a8h).toMonoidHom) (C.ρ a8h).injective, C.card_Y8 hV2]
  rw [C.sup_eq_top8, card_top, C.card_Y8 hV2, hsY] at h
  have h32 := C.card_inf_ge8
  have : Nat.card V * 32 ≤ 64 * 64 :=
    calc Nat.card V * 32 ≤ Nat.card V * Nat.card ↥(C.Y8 ⊓ C.sY8) := Nat.mul_le_mul_left _ h32
      _ = 64 * 64 := h
  omega

theorem card_ker_le8 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) : Nat.card C.β.ker ≤ 2 := by
  have h1 := card_ker_mul_card_range C.β
  rw [MonoidHom.range_eq_top.2 C.surj, card_top, card_dnQuot_eight] at h1
  have h2 := C.card_le8 hV2
  omega

end AltCover8

theorem cover8_bound : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ C : ModelCover (FFModel.altDn 8) W, Nat.card C.β.ker ≤ 2 :=
  fun _ _ _ hW2 C => C.toAltCover8.card_ker_le8 hW2

@[expose] def act8 : ↥(alternatingGroup (Fin 8)) →* MulAut ↥(coreMod 8) :=
  (coreAct 8).comp (alternatingGroup (Fin 8)).subtype

theorem act8_ker (σ : ↥(alternatingGroup (Fin 8))) (m : ↥(coreMod 8))
    (hm : (m : PermMod 8) ∈ zpowers (allOnes 8) ⊓ coreMod 8) : act8 σ m = m := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_inf.1 hm).1
  apply Subtype.ext
  show permAct 8 (σ : Perm (Fin 8)) m = m
  rw [← hk, map_zpow]
  rfl

@[expose] def a8d1 : ↥(alternatingGroup (Fin 8)) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a8d2 : ↥(alternatingGroup (Fin 8)) :=
  ⟨swap 4 5 * swap 6 7, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem allOnes_eight_eq : allOnes 8 = permAct 8 (a8d1 : Perm (Fin 8)) (ev8 0 2) * (ev8 0 2)⁻¹ *
    (permAct 8 (a8d2 : Perm (Fin 8)) (ev8 4 6) * (ev8 4 6)⁻¹) := by
  decide

theorem coreMod_eight_gen (m : ↥(coreMod 8)) :
    m ∈ Subgroup.closure {x | ∃ σ y, x = act8 σ y * y⁻¹} := by
  have hg : ∀ σ (y : ↥(coreMod 8)),
      act8 σ y * y⁻¹ ∈ Subgroup.closure {x | ∃ σ y, x = act8 σ y * y⁻¹} :=
    fun σ y => Subgroup.subset_closure ⟨σ, y, rfl⟩
  have h02 : ev8 0 2 ∈ coreMod 8 := by
    rw [mem_coreMod]
    decide
  have h46 : ev8 4 6 ∈ coreMod 8 := by
    rw [mem_coreMod]
    decide
  have h1 : (⟨allOnes 8, allOnes_eight_mem⟩ : ↥(coreMod 8)) ∈
      Subgroup.closure {x | ∃ σ y, x = act8 σ y * y⁻¹} := by
    have e : (⟨allOnes 8, allOnes_eight_mem⟩ : ↥(coreMod 8)) =
        act8 a8d1 ⟨ev8 0 2, h02⟩ * (⟨ev8 0 2, h02⟩ : ↥(coreMod 8))⁻¹ *
          (act8 a8d2 ⟨ev8 4 6, h46⟩ * (⟨ev8 4 6, h46⟩ : ↥(coreMod 8))⁻¹) :=
      Subtype.ext allOnes_eight_eq
    rw [e]
    exact mul_mem (hg _ _) (hg _ _)
  obtain ⟨a, ha, b, hb, c, hc, hm⟩ := coreMod_eight_eq m m.2
  let c3 : ↥(coreMod 8) := ⟨comm3 a8c123 a8c345 a8c567 a b c,
    comm3_mem _ _ _ (lifts123Eight_mem a ha) (lifts345_mem b hb) (lifts567_mem c hc)⟩
  have h3 : c3 ∈ Subgroup.closure {x | ∃ σ y, x = act8 σ y * y⁻¹} := by
    have e : c3 =
        act8 a8c123 ⟨a, lifts123Eight_mem a ha⟩ * (⟨a, lifts123Eight_mem a ha⟩ : ↥(coreMod 8))⁻¹ *
          (act8 a8c345 ⟨b, lifts345_mem b hb⟩ * (⟨b, lifts345_mem b hb⟩ : ↥(coreMod 8))⁻¹) *
          (act8 a8c567 ⟨c, lifts567_mem c hc⟩ * (⟨c, lifts567_mem c hc⟩ : ↥(coreMod 8))⁻¹) :=
      rfl
    rw [e]
    exact mul_mem (mul_mem (hg _ _) (hg _ _)) (hg _ _)
  rcases hm with hm | hm
  · rwa [show m = c3 from Subtype.ext hm]
  · rw [show m = c3 * ⟨allOnes 8, allOnes_eight_mem⟩ from Subtype.ext hm]
    exact mul_mem h3 h1

theorem card_ker_eight :
    Nat.card ↥((FFModel.altDn 8).ker.subgroupOf (FFModel.altDn 8).sec) = 2 := by
  have hle : zpowers (allOnes 8) ≤ coreMod 8 := zpowers_le.2 allOnes_eight_mem
  show Nat.card ↥((zpowers (allOnes 8) ⊓ coreMod 8).subgroupOf (coreMod 8)) = 2
  rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, inf_eq_left.2 hle,
    Nat.card_zpowers, orderOf_allOnes_eight]

theorem permMod_sq {n : ℕ} (x : PermMod n) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, two_nsmul, Pi.zero_apply]
  exact zmod2_add_self _

theorem altNaturalCoverEight_holds :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut V)) (Z : Subgroup V), Z ≤ fixV H → commV H = ⊤ →
        AlternatingNatural H ⊤ Z 8 →
          Z = ⊥ ∨ (Nat.card Z = 2 ∧ Nat.card V = 2 ^ 7 ∧
            FFModel.Realizes (altCoreModel 8) H ⊤ ⊥) := by
  intro V _ _ hV2 H Z hZ hcomm h
  obtain ⟨C, π, hπs, hρ, hβk⟩ := ModelCover.exists_of_realizes hZ hcomm h
  have hker : C.β.ker = Z := by
    ext v
    exact MonoidHom.mem_ker.trans (hβk v)
  have hle := cover8_bound V hV2 C
  rw [hker] at hle
  have hpos : 0 < Nat.card Z := Nat.card_pos
  rcases (by omega : Nat.card Z = 1 ∨ Nat.card Z = 2) with h1 | h2
  · exact Or.inl (Subgroup.eq_bot_of_card_eq Z h1)
  · right
    have h64 : Nat.card (FFModel.altDn 8).Sec = 64 := card_dnQuot_eight
    have hV : Nat.card V = 2 ^ 7 := by
      rw [C.card_eq, hker, h2, h64]
      norm_num
    refine ⟨h2, hV, ?_⟩
    have : Finite ↥(FFModel.altDn 8).sec := (inferInstance : Finite ↥(coreMod 8))
    obtain ⟨Φ, hΦ⟩ := ModelCover.exists_mulEquiv (D := FFModel.altDn 8) act8 (fun _ _ => rfl)
      act8_ker card_ker_eight
      coreMod_eight_gen (fun m => Subtype.ext (permMod_sq _)) cover8_bound hV2 C
      (by rw [hker, h2])
    exact realizes_of_mulEquiv (E := altCoreModel 8) rfl π hπs Φ fun γ v =>
      (congrArg (fun w => (Φ w).val)
        (congrArg (fun f : MulAut V => f v) (hρ γ))).symm.trans (congrArg Subtype.val (hΦ γ v))

end CFSG.Quasithin.H13.VolI

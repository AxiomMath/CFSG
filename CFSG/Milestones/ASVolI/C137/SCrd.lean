module

public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Quasithin.L3

variable {G : Type} [Group G]

section Nat

variable {A V : Subgroup G} {α : ↥A →* Γ} {β : ↥V →* Multiplicative Vec}

theorem burnsideC137_natVia_inj (h : IsNatVia A V ⊥ α β) : Function.Injective β := by
  rw [← MonoidHom.ker_eq_bot_iff, h.2.1]
  exact Subgroup.bot_subgroupOf _

@[expose] noncomputable def burnsideC137_natE (h : IsNatVia A V ⊥ α β) :
    ↥V ≃* Multiplicative Vec :=
  MulEquiv.ofBijective β ⟨burnsideC137_natVia_inj h, h.1⟩

theorem burnsideC137_natE_apply (h : IsNatVia A V ⊥ α β) (v : ↥V) :
    burnsideC137_natE h v = β v := rfl

theorem burnsideC137_natE_symm_conj (h : IsNatVia A V ⊥ α β)
    (hAV : A ≤ normalizer (V : Set G)) (a : ↥A) (x : Vec) :
    (((burnsideC137_natE h).symm (Multiplicative.ofAdd (act (α a) x)) : ↥V) : G) =
      (a : G) * ((burnsideC137_natE h).symm (Multiplicative.ofAdd x) : G) * (a : G)⁻¹ := by
  set u := (burnsideC137_natE h).symm (Multiplicative.ofAdd x) with hu
  have hw : (a : G) * (u : G) * (a : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 (hAV a.2) u).1 u.2
  have hbu : β u = Multiplicative.ofAdd x := by
    rw [← burnsideC137_natE_apply h, hu, MulEquiv.apply_symm_apply]
  have key : β ⟨_, hw⟩ = Multiplicative.ofAdd (act (α a) x) := by
    have h1 := h.2.2 a u ⟨_, hw⟩ rfl
    rw [hbu] at h1
    exact h1
  have h2 : (burnsideC137_natE h).symm (Multiplicative.ofAdd (act (α a) x)) = ⟨_, hw⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact key.symm
  rw [h2]

theorem burnsideC137_natVia_ker (h : IsNatVia A V ⊥ α β) (hAV : A ≤ normalizer (V : Set G))
    (a : ↥A) (ha : (a : G) ∈ centralizer (V : Set G)) : α a = 1 := by
  apply act_injective
  intro x
  have h1 := burnsideC137_natE_symm_conj h hAV a x
  have h2 : (a : G) * ((burnsideC137_natE h).symm (Multiplicative.ofAdd x) : G) * (a : G)⁻¹ =
      ((burnsideC137_natE h).symm (Multiplicative.ofAdd x) : G) := by
    have := Subgroup.mem_centralizer_iff.1 ha _ ((burnsideC137_natE h).symm
      (Multiplicative.ofAdd x)).2
    rw [← this, mul_inv_cancel_right]
  rw [h2] at h1
  have h3 := (burnsideC137_natE h).symm.injective (Subtype.ext h1)
  exact h3

theorem burnsideC137_natVia_cent (h : IsNatVia A V ⊥ α β) (hAV : A ≤ normalizer (V : Set G))
    (a : ↥A) (ha : α a = 1) : (a : G) ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨x, hx⟩ := (burnsideC137_natE h).symm.surjective ⟨v, hv⟩
  have h1 := burnsideC137_natE_symm_conj h hAV a (Multiplicative.toAdd x)
  rw [ha, act_one] at h1
  have h2 : ((burnsideC137_natE h).symm x : G) = v := congrArg Subtype.val hx
  simp only [ofAdd_toAdd, h2] at h1
  calc v * a = ((a : G) * v * (a : G)⁻¹) * a := by rw [← h1]
    _ = a * v := by group

end Nat

section Coords

variable [Finite G] {L U U₁ U₂ : Subgroup G} {α : ↥L →* Γ} {β₁ : ↥U₁ →* Multiplicative Vec}
  {β₂ : ↥U₂ →* Multiplicative Vec}

@[expose] def burnsideC137_ι {U W : Subgroup G} (hU : IsElemAbelian 2 U) (h : W ≤ U) :
    ↥W →* IntMod U hU where
  toFun w := IntMod.mk hU ⟨w, h w.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem burnsideC137_ι_val {U W : Subgroup G} (hU : IsElemAbelian 2 U) (h : W ≤ U) (w : ↥W) :
    (burnsideC137_ι hU h w).val = w := rfl

variable (hs : SumOfTwoNat L U α U₁ U₂ β₁ β₂)
include hs

theorem burnsideC137_LN : L ≤ normalizer (U : Set G) := by
  intro l hl
  rw [← hs.join]
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  have key : ∀ g : G, g ∈ normalizer (U₁ : Set G) → g ∈ normalizer (U₂ : Set G) →
      ∀ y ∈ U₁ ⊔ U₂, g * y * g⁻¹ ∈ U₁ ⊔ U₂ := by
    intro g hg1 hg2 y hy
    have hle : U₁ ⊔ U₂ ≤ (U₁ ⊔ U₂).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · exact (le_sup_left : U₁ ≤ U₁ ⊔ U₂) ((Subgroup.mem_normalizer_iff.1 hg1 u).1 hu)
      · exact (le_sup_right : U₂ ≤ U₁ ⊔ U₂) ((Subgroup.mem_normalizer_iff.1 hg2 u).1 hu)
    exact hle hy
  constructor
  · exact key l (hs.norm₁ hl) (hs.norm₂ hl) x
  · intro hx
    have := key l⁻¹ (Subgroup.inv_mem _ (hs.norm₁ hl)) (Subgroup.inv_mem _ (hs.norm₂ hl)) _ hx
    simpa [mul_assoc] using this

variable (hU : IsElemAbelian 2 U)
include hU

@[expose] noncomputable def burnsideC137_Φ :
    Multiplicative Vec × Multiplicative Vec →* IntMod U hU :=
  MonoidHom.coprod ((burnsideC137_ι hU hs.le₁).comp (burnsideC137_natE hs.nat₁).symm.toMonoidHom)
    ((burnsideC137_ι hU hs.le₂).comp (burnsideC137_natE hs.nat₂).symm.toMonoidHom)

theorem burnsideC137_Φ_val (p : Multiplicative Vec × Multiplicative Vec) :
    (burnsideC137_Φ hs hU p).val =
      ((burnsideC137_natE hs.nat₁).symm p.1 : G) * ((burnsideC137_natE hs.nat₂).symm p.2 : G) :=
  rfl

theorem burnsideC137_Φ_injective : Function.Injective (burnsideC137_Φ hs hU) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have h1 := congrArg IntMod.val hp
  rw [burnsideC137_Φ_val, IntMod.val_one] at h1
  set a := (burnsideC137_natE hs.nat₁).symm p.1 with ha
  set b := (burnsideC137_natE hs.nat₂).symm p.2 with hb
  have hab : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hmem : (a : G) ∈ U₁ ⊓ U₂ := ⟨a.2, hab ▸ U₂.inv_mem b.2⟩
  rw [hs.meet, Subgroup.mem_bot] at hmem
  have hb1 : (b : G) = 1 := by
    rw [hmem] at hab
    exact (inv_eq_one.1 hab.symm)
  have ha' : a = 1 := Subtype.ext hmem
  have hb' : b = 1 := Subtype.ext hb1
  have h1' : p.1 = 1 := by
    have := congrArg (burnsideC137_natE hs.nat₁) ha'
    rw [ha, MulEquiv.apply_symm_apply, map_one] at this
    exact this
  have h2' : p.2 = 1 := by
    have := congrArg (burnsideC137_natE hs.nat₂) hb'
    rw [hb, MulEquiv.apply_symm_apply, map_one] at this
    exact this
  exact Prod.ext h1' h2'

theorem burnsideC137_le_normalizer₂ : U₂ ≤ normalizer (U₁ : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  have hbU : b ∈ U := hs.le₂ hb
  constructor
  · intro ha
    have hc : b * a = a * b := hU.1.is_comm.comm ⟨b, hbU⟩ ⟨a, hs.le₁ ha⟩ |> congrArg Subtype.val
    rw [hc, mul_inv_cancel_right]
    exact ha
  · intro ha
    have haU : b * a * b⁻¹ ∈ U := hs.le₁ ha
    have hc : b⁻¹ * (b * a * b⁻¹) = (b * a * b⁻¹) * b⁻¹ :=
      hU.1.is_comm.comm ⟨b⁻¹, U.inv_mem hbU⟩ ⟨_, haU⟩ |> congrArg Subtype.val
    have : a = b * a * b⁻¹ := by
      calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
        _ = (b * a * b⁻¹) * b⁻¹ * b := by rw [hc]
        _ = b * a * b⁻¹ := by group
    rw [this]
    exact ha

theorem burnsideC137_Φ_surjective : Function.Surjective (burnsideC137_Φ hs hU) := by
  intro m
  have hm : m.val ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    rw [hs.join]
    exact m.val_mem
  rw [Subgroup.coe_mul_of_right_le_normalizer_left U₁ U₂ (burnsideC137_le_normalizer₂ hs hU)]
    at hm
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hm
  refine ⟨(β₁ ⟨a, ha⟩, β₂ ⟨b, hb⟩), IntMod.val_injective ?_⟩
  rw [burnsideC137_Φ_val, ← hab]
  have e1 : (burnsideC137_natE hs.nat₁).symm (β₁ ⟨a, ha⟩) = ⟨a, ha⟩ := by
    rw [MulEquiv.symm_apply_eq]; rfl
  have e2 : (burnsideC137_natE hs.nat₂).symm (β₂ ⟨b, hb⟩) = ⟨b, hb⟩ := by
    rw [MulEquiv.symm_apply_eq]; rfl
  rw [e1, e2]

@[expose] noncomputable def burnsideC137_κ :
    IntMod U hU ≃* Multiplicative Vec × Multiplicative Vec :=
  (MulEquiv.ofBijective (burnsideC137_Φ hs hU)
    ⟨burnsideC137_Φ_injective hs hU, burnsideC137_Φ_surjective hs hU⟩).symm

theorem burnsideC137_Φ_κ (m : IntMod U hU) : burnsideC137_Φ hs hU (burnsideC137_κ hs hU m) = m :=
  (MulEquiv.ofBijective (burnsideC137_Φ hs hU)
    ⟨burnsideC137_Φ_injective hs hU, burnsideC137_Φ_surjective hs hU⟩).apply_symm_apply m

theorem burnsideC137_κ_Φ (p : Multiplicative Vec × Multiplicative Vec) :
    burnsideC137_κ hs hU (burnsideC137_Φ hs hU p) = p :=
  (MulEquiv.ofBijective (burnsideC137_Φ hs hU)
    ⟨burnsideC137_Φ_injective hs hU, burnsideC137_Φ_surjective hs hU⟩).symm_apply_apply p

@[expose] def burnsideC137_dact (g : Γ) (p : Multiplicative Vec × Multiplicative Vec) :
    Multiplicative Vec × Multiplicative Vec :=
  (Multiplicative.ofAdd (act g (Multiplicative.toAdd p.1)),
    Multiplicative.ofAdd (act g (Multiplicative.toAdd p.2)))

theorem burnsideC137_Φ_conv (l : ↥L) (hl : (l : G) ∈ normalizer (U : Set G))
    (p : Multiplicative Vec × Multiplicative Vec) :
    convI hU ⟨l, hl⟩ (burnsideC137_Φ hs hU p) =
      burnsideC137_Φ hs hU (burnsideC137_dact (α l) p) := by
  apply IntMod.val_injective
  rw [convI_apply_val, burnsideC137_Φ_val, burnsideC137_Φ_val]
  simp only [burnsideC137_dact]
  rw [burnsideC137_natE_symm_conj hs.nat₁ hs.norm₁ l, burnsideC137_natE_symm_conj hs.nat₂ hs.norm₂ l]
  simp only [ofAdd_toAdd]
  group

theorem burnsideC137_κ_conv (l : ↥L) (hl : (l : G) ∈ normalizer (U : Set G)) (m : IntMod U hU) :
    burnsideC137_κ hs hU (convI hU ⟨l, hl⟩ m) =
      burnsideC137_dact (α l) (burnsideC137_κ hs hU m) := by
  conv_lhs => rw [← burnsideC137_Φ_κ hs hU m, burnsideC137_Φ_conv hs hU l hl]
  exact burnsideC137_κ_Φ hs hU _

theorem burnsideC137_card_U : Nat.card (IntMod U hU) = 64 := by
  rw [Nat.card_congr (burnsideC137_κ hs hU).toEquiv, Nat.card_prod]
  simp [Nat.card_eq_fintype_card]

theorem burnsideC137_ker_starHom :
    (C124.starHom hU L (burnsideC137_LN hs)).ker = α.ker := by
  ext l
  rw [C124.ker_starHom, Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
  constructor
  · rintro ⟨-, hc⟩
    exact burnsideC137_natVia_ker hs.nat₁ hs.norm₁ l
      (Subgroup.centralizer_le hs.le₁ hc)
  · intro h1
    refine ⟨l.2, ?_⟩
    have c1 := burnsideC137_natVia_cent hs.nat₁ hs.norm₁ l h1
    have c2 := burnsideC137_natVia_cent hs.nat₂ hs.norm₂ l h1
    have hle : U₁ ⊔ U₂ ≤ centralizer ({(l : G)} : Set G) := by
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (Subgroup.mem_centralizer_iff.1 c1 u hu).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (Subgroup.mem_centralizer_iff.1 c2 u hu).symm
    rw [hs.join] at hle
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.1 (hle hu) l rfl).symm

@[expose] noncomputable def burnsideC137_ψ : ↥(autI hU L) ≃* Γ :=
  (QuotientGroup.quotientKerEquivOfSurjective (C124.starHom hU L (burnsideC137_LN hs))
      (C124.starHom_surjective hU (burnsideC137_LN hs))).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (burnsideC137_ker_starHom hs hU)).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hs.alpha_onto))

theorem burnsideC137_ψ_starHom (l : ↥L) :
    burnsideC137_ψ hs hU (C124.starHom hU L (burnsideC137_LN hs) l) = α l := by
  unfold burnsideC137_ψ
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (C124.starHom hU L (burnsideC137_LN hs))
      (C124.starHom_surjective hU (burnsideC137_LN hs))).symm
        (C124.starHom hU L (burnsideC137_LN hs) l) = QuotientGroup.mk l := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1]
  rfl

theorem burnsideC137_ψ_conv (l : ↥L) (h : convI hU ⟨l, burnsideC137_LN hs l.2⟩ ∈ autI hU L) :
    burnsideC137_ψ hs hU ⟨_, h⟩ = α l := by
  rw [← burnsideC137_ψ_starHom hs hU l]
  rfl

theorem burnsideC137_κ_act (a : ↥(autI hU L)) (m : IntMod U hU) :
    burnsideC137_κ hs hU ((a : MulAut (IntMod U hU)) m) =
      burnsideC137_dact (burnsideC137_ψ hs hU a) (burnsideC137_κ hs hU m) := by
  obtain ⟨l, rfl⟩ := C124.starHom_surjective hU (burnsideC137_LN hs) a
  rw [burnsideC137_ψ_starHom, C124.starHom_apply]
  exact burnsideC137_κ_conv hs hU l _ m

@[expose] def burnsideC137_fixVec (H : Subgroup Γ) : AddSubgroup Vec where
  carrier := {v | ∀ g ∈ H, act g v = v}
  add_mem' := fun {a b} ha hb g hg => by rw [act_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => act_zero g
  neg_mem' := fun {a} ha g hg => by
    show (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (-a) = -a
    rw [Matrix.mulVec_neg]
    exact congrArg Neg.neg (ha g hg)

@[expose] noncomputable def burnsideC137_bar (B : Subgroup (MulAut (IntMod U hU))) : Subgroup Γ :=
  (B.subgroupOf (autI hU L)).map (burnsideC137_ψ hs hU).toMonoidHom

theorem burnsideC137_mem_bar {B : Subgroup (MulAut (IntMod U hU))} {g : Γ} :
    g ∈ burnsideC137_bar hs hU B ↔
      ∃ a : ↥(autI hU L), (a : MulAut (IntMod U hU)) ∈ B ∧ burnsideC137_ψ hs hU a = g := by
  unfold burnsideC137_bar
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]

theorem burnsideC137_mem_bar_iff {B : Subgroup (MulAut (IntMod U hU))} (a : ↥(autI hU L)) :
    burnsideC137_ψ hs hU a ∈ burnsideC137_bar hs hU B ↔ (a : MulAut (IntMod U hU)) ∈ B := by
  rw [burnsideC137_mem_bar]
  constructor
  · rintro ⟨b, hb, he⟩
    rw [(burnsideC137_ψ hs hU).injective he] at hb
    exact hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem burnsideC137_card_bar {B : Subgroup (MulAut (IntMod U hU))} (hBL : B ≤ autI hU L) :
    Nat.card (burnsideC137_bar hs hU B) = Nat.card B := by
  unfold burnsideC137_bar
  rw [Subgroup.card_map_of_injective (burnsideC137_ψ hs hU).injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv

theorem burnsideC137_card_fixV {B : Subgroup (MulAut (IntMod U hU))} (hBL : B ≤ autI hU L) :
    Nat.card (fixV B) = Nat.card (burnsideC137_fixVec (burnsideC137_bar hs hU B)) ^ 2 := by
  set H := burnsideC137_bar hs hU B with hH
  set E : IntMod U hU ≃ Vec × Vec :=
    (burnsideC137_κ hs hU).toEquiv.trans
      (Equiv.prodCongr Multiplicative.toAdd Multiplicative.toAdd) with hE
  have hEapply : ∀ m, E m = (Multiplicative.toAdd (burnsideC137_κ hs hU m).1,
      Multiplicative.toAdd (burnsideC137_κ hs hU m).2) := fun _ => rfl
  have key : ∀ m : IntMod U hU, m ∈ fixV B ↔
      (E m).1 ∈ burnsideC137_fixVec H ∧ (E m).2 ∈ burnsideC137_fixVec H := by
    intro m
    rw [hEapply]
    constructor
    · intro hm
      refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · obtain ⟨a, ha, rfl⟩ := (burnsideC137_mem_bar hs hU).1 hg
        have h1 := burnsideC137_κ_act hs hU a m
        rw [hm _ ha] at h1
        have := congrArg (fun p => Multiplicative.toAdd p.1) h1
        exact this.symm
      · obtain ⟨a, ha, rfl⟩ := (burnsideC137_mem_bar hs hU).1 hg
        have h1 := burnsideC137_κ_act hs hU a m
        rw [hm _ ha] at h1
        have := congrArg (fun p => Multiplicative.toAdd p.2) h1
        exact this.symm
    · rintro ⟨h1, h2⟩ b hb
      apply (burnsideC137_κ hs hU).injective
      have h3 := burnsideC137_κ_act hs hU ⟨b, hBL hb⟩ m
      simp only at h3
      rw [h3]
      have hg : burnsideC137_ψ hs hU ⟨b, hBL hb⟩ ∈ H :=
        (burnsideC137_mem_bar_iff hs hU ⟨b, hBL hb⟩).2 hb
      simp only [burnsideC137_dact]
      rw [h1 _ hg, h2 _ hg]
      rfl
  have e := (E.subtypeEquiv key).trans (Equiv.subtypeProdEquivProd)
  rw [Nat.card_congr e, Nat.card_prod, pow_two]

end Coords

end CFSG.ASVolI

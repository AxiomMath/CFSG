module

public import CFSG.Milestones.ASVolI.C137.SCrd
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZGen

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Quasithin.L3

variable {G : Type} [Group G]

section NatOf

variable {L I : Subgroup G} {α : ↥L →* Γ}

theorem burnsideC137_nat_of_inj (hα : Function.Surjective α) (hLI : L ≤ normalizer (I : Set G))
    (hI1 : I ≠ ⊥) (f : ↥I →* Multiplicative Vec) (hinj : Function.Injective f)
    (heq : ∀ (a : ↥L) (u v : ↥I), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (f v) = act (α a) (Multiplicative.toAdd (f u))) :
    IsNatVia L I ⊥ α f := by
  refine ⟨?_, ?_, fun a u v huv => heq a u v huv⟩
  · obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hI1
    have hv₀ : Multiplicative.toAdd (f ⟨u₀, hu₀⟩) ≠ 0 := by
      intro h0
      apply hu₀1
      apply hinj
      rw [map_one]
      exact h0
    intro y
    by_cases hy : Multiplicative.toAdd y = 0
    · exact ⟨1, by rw [map_one]; exact (toAdd_eq_zero.1 hy).symm⟩
    · obtain ⟨g, hg⟩ := act_trans _ _ hv₀ hy
      obtain ⟨a, rfl⟩ := hα g
      have hw : (a : G) * u₀ * (a : G)⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.1 (hLI a.2) u₀).1 hu₀
      refine ⟨⟨_, hw⟩, ?_⟩
      have := heq a ⟨u₀, hu₀⟩ ⟨_, hw⟩ rfl
      rw [hg] at this
      exact this
  · rw [Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff f).2 hinj

end NatOf

section Coords

variable [Finite G] {L U U₁ U₂ : Subgroup G} {α : ↥L →* Γ}
  {β₁ : ↥U₁ →* Multiplicative Vec} {β₂ : ↥U₂ →* Multiplicative Vec}
  (hs : SumOfTwoNat L U α U₁ U₂ β₁ β₂) (hU : IsElemAbelian 2 U)
include hs hU

@[expose] noncomputable def burnsideC137_κ₁ : IntMod U hU →* Multiplicative Vec :=
  (MonoidHom.fst _ _).comp (burnsideC137_κ hs hU).toMonoidHom

@[expose] noncomputable def burnsideC137_κ₂ : IntMod U hU →* Multiplicative Vec :=
  (MonoidHom.snd _ _).comp (burnsideC137_κ hs hU).toMonoidHom

theorem burnsideC137_κ₁_apply (m : IntMod U hU) :
    burnsideC137_κ₁ hs hU m = (burnsideC137_κ hs hU m).1 := rfl

theorem burnsideC137_κ₂_apply (m : IntMod U hU) :
    burnsideC137_κ₂ hs hU m = (burnsideC137_κ hs hU m).2 := rfl

theorem burnsideC137_val_eq (m : IntMod U hU) :
    m.val = ((burnsideC137_natE hs.nat₁).symm (burnsideC137_κ₁ hs hU m) : G) *
      ((burnsideC137_natE hs.nat₂).symm (burnsideC137_κ₂ hs hU m) : G) := by
  conv_lhs => rw [← burnsideC137_Φ_κ hs hU m]
  rfl

theorem burnsideC137_κ₁_eq_one_iff (m : IntMod U hU) :
    burnsideC137_κ₁ hs hU m = 1 ↔ m.val ∈ U₂ := by
  constructor
  · intro h1
    rw [burnsideC137_val_eq hs hU m, h1, map_one, Subgroup.coe_one, one_mul]
    exact Subtype.property _
  · intro h2
    have hΦ : burnsideC137_Φ hs hU (1, β₂ ⟨m.val, h2⟩) = m := by
      apply IntMod.val_injective
      rw [burnsideC137_Φ_val, map_one, Subgroup.coe_one, one_mul]
      have : (burnsideC137_natE hs.nat₂).symm (β₂ ⟨m.val, h2⟩) = ⟨m.val, h2⟩ := by
        rw [MulEquiv.symm_apply_eq]; rfl
      rw [this]
    rw [burnsideC137_κ₁_apply, ← hΦ, burnsideC137_κ_Φ]

theorem burnsideC137_κ₂_eq_one_iff (m : IntMod U hU) :
    burnsideC137_κ₂ hs hU m = 1 ↔ m.val ∈ U₁ := by
  constructor
  · intro h1
    rw [burnsideC137_val_eq hs hU m, h1, map_one, Subgroup.coe_one, mul_one]
    exact Subtype.property _
  · intro h2
    have hΦ : burnsideC137_Φ hs hU (β₁ ⟨m.val, h2⟩, 1) = m := by
      apply IntMod.val_injective
      rw [burnsideC137_Φ_val, map_one, Subgroup.coe_one, mul_one]
      have : (burnsideC137_natE hs.nat₁).symm (β₁ ⟨m.val, h2⟩) = ⟨m.val, h2⟩ := by
        rw [MulEquiv.symm_apply_eq]; rfl
      rw [this]
    rw [burnsideC137_κ₂_apply, ← hΦ, burnsideC137_κ_Φ]

theorem burnsideC137_κ₁_conv (l : ↥L) (hl : (l : G) ∈ normalizer (U : Set G)) (m : IntMod U hU) :
    Multiplicative.toAdd (burnsideC137_κ₁ hs hU (convI hU ⟨l, hl⟩ m)) =
      act (α l) (Multiplicative.toAdd (burnsideC137_κ₁ hs hU m)) := by
  rw [burnsideC137_κ₁_apply, burnsideC137_κ_conv hs hU l hl]
  rfl

theorem burnsideC137_κ₂_conv (l : ↥L) (hl : (l : G) ∈ normalizer (U : Set G)) (m : IntMod U hU) :
    Multiplicative.toAdd (burnsideC137_κ₂ hs hU (convI hU ⟨l, hl⟩ m)) =
      act (α l) (Multiplicative.toAdd (burnsideC137_κ₂ hs hU m)) := by
  rw [burnsideC137_κ₂_apply, burnsideC137_κ_conv hs hU l hl]
  rfl

theorem burnsideC137_fixL (m : IntMod U hU)
    (hm : ∀ (l : ↥L) (hl : (l : G) ∈ normalizer (U : Set G)), convI hU ⟨l, hl⟩ m = m) : m = 1 := by
  have key : ∀ x : Vec, (∀ g : Γ, act g x = x) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨g, hg⟩ := act_nofix x hne
    exact hg (hx g)
  have h1 : burnsideC137_κ₁ hs hU m = 1 := by
    apply toAdd_eq_zero.1
    apply key
    intro g
    obtain ⟨l, rfl⟩ := hs.alpha_onto g
    rw [← burnsideC137_κ₁_conv hs hU l (burnsideC137_LN hs l.2), hm]
  have h2 : burnsideC137_κ₂ hs hU m = 1 := by
    apply toAdd_eq_zero.1
    apply key
    intro g
    obtain ⟨l, rfl⟩ := hs.alpha_onto g
    rw [← burnsideC137_κ₂_conv hs hU l (burnsideC137_LN hs l.2), hm]
  have h3 : burnsideC137_κ hs hU m = 1 := Prod.ext h1 h2
  rw [← map_one (burnsideC137_κ hs hU)] at h3
  exact (burnsideC137_κ hs hU).injective h3

theorem burnsideC137_inf_centralizer {I : Subgroup G} (hIU : I ≤ U) :
    I ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hm := burnsideC137_fixL hs hU (IntMod.mk hU ⟨u, hIU hu.1⟩) fun l hl => by
    apply IntMod.val_injective
    rw [convI_apply_val]
    show (l : G) * u * (l : G)⁻¹ = u
    rw [Subgroup.mem_centralizer_iff.1 hu.2 l l.2, mul_inv_cancel_right]
  exact congrArg IntMod.val hm

open Classical in
@[expose] noncomputable def burnsideC137_crd (I : Subgroup G) (hIU : I ≤ U) :
    ↥I →* Multiplicative Vec :=
  if I ⊓ U₂ = ⊥ then (burnsideC137_κ₁ hs hU).comp (burnsideC137_ι hU hIU)
  else (burnsideC137_κ₂ hs hU).comp (burnsideC137_ι hU hIU)

theorem burnsideC137_crd_nat {I : Subgroup G} (hI : I ∈ internalIrrPlus L U) :
    IsNatVia L I ⊥ α (burnsideC137_crd hs hU I hI.1) := by
  obtain ⟨hIU, -, hlt, -, hLI, hirr⟩ := hI
  have hIC := burnsideC137_inf_centralizer hs hU hIU (L := L)
  rw [hIC] at hlt hirr
  have hI1 : I ≠ ⊥ := hlt.ne'
  have heq : ∀ (f : IntMod U hU →* Multiplicative Vec),
      (∀ (l : ↥L) (hl : (l : G) ∈ normalizer (U : Set G)) (m : IntMod U hU),
        Multiplicative.toAdd (f (convI hU ⟨l, hl⟩ m)) = act (α l) (Multiplicative.toAdd (f m))) →
      ∀ (a : ↥L) (u v : ↥I), (v : G) = a * u * a⁻¹ →
        Multiplicative.toAdd ((f.comp (burnsideC137_ι hU hIU)) v) =
          act (α a) (Multiplicative.toAdd ((f.comp (burnsideC137_ι hU hIU)) u)) := by
    intro f hf a u v huv
    have hm : burnsideC137_ι hU hIU v = convI hU ⟨a, burnsideC137_LN hs a.2⟩
        (burnsideC137_ι hU hIU u) := by
      apply IntMod.val_injective
      rw [convI_apply_val, burnsideC137_ι_val, burnsideC137_ι_val]
      exact huv
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [hm, hf]
  unfold burnsideC137_crd
  split_ifs with hI2
  · refine burnsideC137_nat_of_inj hs.alpha_onto hLI hI1 _ ?_
      (heq _ (burnsideC137_κ₁_conv hs hU))
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      burnsideC137_κ₁_eq_one_iff] at hu
    have : (u : G) ∈ I ⊓ U₂ := ⟨u.2, hu⟩
    rw [hI2, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  · have hIU₂ : I ≤ U₂ := by
      have hN : L ≤ normalizer ((I ⊓ U₂ : Subgroup G) : Set G) := fun l hl =>
        H13.U3.GC137.mem_normalizer_inf_gc (hLI hl) (hs.norm₂ hl)
      rcases hirr (I ⊓ U₂) bot_le inf_le_left hN with h0 | h1
      · exact absurd h0 hI2
      · rw [← h1]; exact inf_le_right
    refine burnsideC137_nat_of_inj hs.alpha_onto hLI hI1 _ ?_
      (heq _ (burnsideC137_κ₂_conv hs hU))
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      burnsideC137_κ₂_eq_one_iff] at hu
    have : (u : G) ∈ U₁ ⊓ U₂ := ⟨hu, hIU₂ u.2⟩
    rw [hs.meet, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)

theorem burnsideC137_nat_mem_irr {W : Subgroup G} (hWU : W ≤ U)
    (hLW : L ≤ normalizer (W : Set G)) {β : ↥W →* Multiplicative Vec}
    (hβ : IsNatVia L W ⊥ α β) : W ∈ internalIrrPlus L U := by
  have hWC := burnsideC137_inf_centralizer hs hU hWU (L := L)
  have hW1 : W ≠ ⊥ := by
    intro hb
    obtain ⟨w, hw⟩ := hβ.1 (Multiplicative.ofAdd ![1, 0, 0])
    have hw1 : (w : G) = 1 := (Subgroup.eq_bot_iff_forall W).1 hb w w.2
    have : w = 1 := Subtype.ext hw1
    rw [this, map_one] at hw
    have h3 := congrArg (fun y : Multiplicative Vec => (Multiplicative.toAdd y) 0) hw
    simp at h3
  refine ⟨hWU, le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hLW) ?_, ?_⟩
  · intro w hw
    obtain ⟨g, v, hgv⟩ := act_allcomm (Multiplicative.toAdd (β ⟨w, hw⟩))
    obtain ⟨l, rfl⟩ := hs.alpha_onto g
    set e := burnsideC137_natE hβ with he
    set x : ↥W := e.symm (Multiplicative.ofAdd v) with hx
    have h1 := burnsideC137_natE_symm_conj hβ hLW l v
    have hwx : (⟨w, hw⟩ : ↥W) = e.symm (Multiplicative.ofAdd (act (α l) v)) * x⁻¹ := by
      rw [← map_inv, ← map_mul, MulEquiv.eq_symm_apply, burnsideC137_natE_apply]
      apply Multiplicative.toAdd.injective
      rw [← hgv]
      simp [sub_eq_add_neg]
    have hw' : w = (l : G) * x * (l : G)⁻¹ * (x : G)⁻¹ := by
      have := congrArg Subtype.val hwx
      rw [Subgroup.coe_mul, Subgroup.coe_inv, h1] at this
      exact this
    rw [hw', Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator l.2 x.2
  · rw [hWC]
    refine ⟨bot_lt_iff_ne_bot.2 hW1, fun l _ => Subgroup.mem_normalizer_iff.2 fun y => by
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl; group
      · intro h1
        calc y = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * l := by group
          _ = 1 := by rw [h1]; group, hLW, fun K _ hKW hLK => ?_⟩
    by_cases hK : K = ⊥
    · exact Or.inl hK
    · right
      refine le_antisymm hKW fun w hw => ?_
      obtain ⟨⟨k, hk⟩, hk1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hK
      have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
      have hβk : Multiplicative.toAdd (β ⟨k, hKW hk⟩) ≠ 0 := by
        intro h0
        apply hk1'
        have := burnsideC137_natVia_inj hβ (a₁ := ⟨k, hKW hk⟩) (a₂ := 1) (by
          rw [map_one]; exact toAdd_eq_zero.1 h0)
        exact congrArg Subtype.val this
      by_cases hw1 : w = 1
      · rw [hw1]; exact K.one_mem
      · have hβw : Multiplicative.toAdd (β ⟨w, hw⟩) ≠ 0 := by
          intro h0
          apply hw1
          have := burnsideC137_natVia_inj hβ (a₁ := ⟨w, hw⟩) (a₂ := 1) (by
            rw [map_one]; exact toAdd_eq_zero.1 h0)
          exact congrArg Subtype.val this
        obtain ⟨g, hg⟩ := act_trans _ _ hβk hβw
        obtain ⟨l, rfl⟩ := hs.alpha_onto g
        have hlk : (l : G) * k * (l : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hLK l.2) k).1 hk
        have hlkW : (l : G) * k * (l : G)⁻¹ ∈ W := hKW hlk
        have h1 := hβ.2.2 l ⟨k, hKW hk⟩ ⟨_, hlkW⟩ rfl
        rw [show ((α l : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (β ⟨k, hKW hk⟩)) =
            act (α l) (Multiplicative.toAdd (β ⟨k, hKW hk⟩)) from rfl, hg] at h1
        have h2 : (⟨_, hlkW⟩ : ↥W) = ⟨w, hw⟩ :=
          burnsideC137_natVia_inj hβ (Multiplicative.toAdd.injective h1)
        have : (l : G) * k * (l : G)⁻¹ = w := congrArg Subtype.val h2
        rw [← this]
        exact hlk

end Coords

section Pre

variable {L I : Subgroup G} {α : ↥L →* Γ}

theorem burnsideC137_mem_preimageIn {β : ↥I →* Multiplicative Vec}
    {ℓ : Submodule (ZMod 2) Vec} {y : G} :
    y ∈ preimageIn I β ℓ ↔ ∃ hy : y ∈ I, Multiplicative.toAdd (β ⟨y, hy⟩) ∈ ℓ := by
  unfold preimageIn
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨hy, hβ⟩
    exact ⟨⟨y, hy⟩, hβ, rfl⟩

theorem burnsideC137_conj_mem_pre {β : ↥I →* Multiplicative Vec}
    (hβ : IsNatVia L I ⊥ α β) (hLI : L ≤ normalizer (I : Set G)) (ℓ : Submodule (ZMod 2) Vec)
    {x : G} (l : ↥L) (hxl : ∀ u ∈ I, x * u * x⁻¹ = (l : G) * u * (l : G)⁻¹)
    (hst : ∀ v ∈ ℓ, act (α l) v ∈ ℓ) {y : G} (hy : y ∈ preimageIn I β ℓ) :
    x * y * x⁻¹ ∈ preimageIn I β ℓ := by
  obtain ⟨hyI, hyℓ⟩ := burnsideC137_mem_preimageIn.1 hy
  rw [hxl y hyI]
  have hw : (l : G) * y * (l : G)⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hLI l.2) y).1 hyI
  refine burnsideC137_mem_preimageIn.2 ⟨hw, ?_⟩
  have := hβ.2.2 l ⟨y, hyI⟩ ⟨_, hw⟩ rfl
  rw [this]
  exact hst _ hyℓ

end Pre

end CFSG.ASVolI

module

public import CFSG.Quasithin.H13.GoldschmidtC137KMod3
public import CFSG.Quasithin.H13.GoldschmidtC137ZfBeta

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.B3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

@[expose] def incIntMod {U V : Subgroup G} (hU : IsElemAbelian 2 U) (hV : IsElemAbelian 2 V)
    (hUV : U ≤ V) : IntMod U hU →* IntMod V hV where
  toFun u := IntMod.mk hV ⟨u.val, hUV u.val_mem⟩
  map_one' := IntMod.val_injective rfl
  map_mul' _ _ := IntMod.val_injective rfl

theorem val_incIntMod {U V : Subgroup G} (hU : IsElemAbelian 2 U) (hV : IsElemAbelian 2 V)
    (hUV : U ≤ V) (u : IntMod U hU) : (incIntMod hU hV hUV u).val = u.val := rfl

theorem commutator_le_of_le_normalizer {V L : Subgroup G} (hLV : L ≤ normalizer (V : Set G)) :
    ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h1 := (Subgroup.mem_normalizer_iff.1 (hLV hl) v⁻¹).1 (V.inv_mem hv)
  have h2 : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact V.mul_mem hv h1

theorem exists_conv_rep {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLV : L ≤ normalizer (V : Set G)) (a : ↥(autI hV L)) :
    ∃ g : ↥L, convI hV ⟨g, hLV g.2⟩ = (a : MulAut (IntMod V hV)) := by
  obtain ⟨g, hg, e⟩ := (mem_autI hV).1 a.2
  exact ⟨⟨g, hg⟩, e⟩

theorem exists_rhoU {V L U : Subgroup G} (hV : IsElemAbelian 2 V) (hU : IsElemAbelian 2 U)
    (hLV : L ≤ normalizer (V : Set G)) (hLU : L ≤ normalizer (U : Set G)) (hUV : U ≤ V)
    (π : LG 6 →* ↥(autI hV L)) (hπ : Function.Surjective π) :
    ∃ ρ : LG 6 →* MulAut (IntMod U hU),
      (∀ (γ : LG 6) (g : ↥L), convI hV ⟨g, hLV g.2⟩ = (π γ : MulAut (IntMod V hV)) →
        ρ γ = convI hU ⟨g, hLU g.2⟩) ∧ (⊤ : Subgroup (LG 6)).map ρ = autI hU L := by
  let φV : ↥L →* ↥(autI hV L) := ((convI hV).comp (Subgroup.inclusion hLV)).codRestrict
    (autI hV L) fun g => (mem_autI hV).2 ⟨_, g.2, rfl⟩
  have hφV : Function.Surjective φV := by
    intro a
    obtain ⟨g, hg⟩ := exists_conv_rep hV hLV a
    exact ⟨g, Subtype.ext hg⟩
  let φU : ↥L →* MulAut (IntMod U hU) := (convI hU).comp (Subgroup.inclusion hLU)
  have hker : φV.ker ≤ φU.ker := by
    intro g hg
    have h1 : convI hV ⟨g, hLV g.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
    have h2 := (convI_eq_one_iff hV ⟨g, hLV g.2⟩).1 h1
    refine MonoidHom.mem_ker.2 ((convI_eq_one_iff hU ⟨g, hLU g.2⟩).2 ?_)
    intro u hu
    exact Subgroup.mem_centralizer_iff.1 h2 u (hUV hu)
  let r := MonoidHom.liftOfSurjective φV hφV ⟨φU, hker⟩
  have hr : ∀ g : ↥L, r (φV g) = φU g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φU, hker⟩ g
  refine ⟨r.comp π, fun γ g hg => ?_, ?_⟩
  · show r (π γ) = _
    rw [← show φV g = π γ from Subtype.ext hg]
    exact hr g
  · ext x
    constructor
    · rintro ⟨γ, -, rfl⟩
      obtain ⟨g, hg⟩ := hφV (π γ)
      show r (π γ) ∈ autI hU L
      rw [← hg, hr]
      exact convI_mem_autI hU g.2 (hLU g.2)
    · intro hx
      obtain ⟨g, hgL, rfl⟩ := (mem_autI hU).1 hx
      obtain ⟨γ, hγ⟩ := hπ (φV ⟨g, hgL⟩)
      refine ⟨γ, trivial, ?_⟩
      show r (π γ) = _
      rw [hγ, hr]
      rfl

theorem model_of_Z [Finite G] {V L U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : IsElemAbelian 2 U) (hLV : L ≤ normalizer (V : Set G)) (hLU : L ≤ normalizer (U : Set G))
    (hUV : ⁅V, L⁆ = U) (hUL : ⁅U, L⁆ = U)
    (hnat : ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤
      ((centralizer (L : Set G)).subgroupOf V) 6) :
    ∃ k, (k = Mod.ut0 ∨ k = Mod.u0) ∧ Nonempty (KModel k (autI hU L)) := by
  obtain ⟨π, β, hπs, hβs, hβk, hβe⟩ := exists_beta_of_natural_Z hV hnat
  have hUV' : U ≤ V := hUV ▸ commutator_le_of_le_normalizer hLV
  obtain ⟨ρ, hρrep, hρtop⟩ := exists_rhoU hV hU hLV hLU hUV' π hπs
  let β' : IntMod U hU →* Mod.V 6 Mod.ut0 := β.comp (incIntMod hU hV hUV')
  have hrel : ∀ (γ : LG 6) (u : IntMod U hU), incIntMod hU hV hUV' (ρ γ u) =
      (π γ : MulAut (IntMod V hV)) (incIntMod hU hV hUV' u) := by
    intro γ u
    obtain ⟨g, hg⟩ := exists_conv_rep hV hLV (π γ)
    rw [hρrep γ g hg, ← hg]
    refine IntMod.val_injective ?_
    rw [val_incIntMod, convI_apply_val, convI_apply_val]
    rfl
  have hequiv : ∀ (γ : LG 6) (u : IntMod U hU), β' (ρ γ u) = actL 6 Mod.ut0 γ (β' u) := by
    intro γ u
    show β (incIntMod hU hV hUV' (ρ γ u)) = Mod.act 6 Mod.ut0 γ.1 (β (incIntMod hU hV hUV' u))
    rw [hrel, hβe]
  have hsurj : Function.Surjective β' := by
    have hle : (⊤ : Subgroup (Mod.V 6 Mod.ut0)) ≤ β'.range := by
      rw [← commG_ut0]
      refine commOn_le fun γ w _ => ?_
      obtain ⟨v, rfl⟩ := hβs w
      obtain ⟨g, hg⟩ := exists_conv_rep hV hLV (π γ)
      have hcomm : ⁅(g : G), v.val⁆ ∈ U := by
        rw [← hUV, ← Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator g.2 v.val_mem
      refine ⟨IntMod.mk hU ⟨⁅(g : G), v.val⁆, hcomm⟩, ?_⟩
      have h1 : incIntMod hU hV hUV' (IntMod.mk hU ⟨⁅(g : G), v.val⁆, hcomm⟩) =
          (π γ : MulAut (IntMod V hV)) v * v⁻¹ := by
        refine IntMod.val_injective ?_
        rw [← hg, val_incIntMod, IntMod.val_mul, convI_apply_val]
        rfl
      show β (incIntMod hU hV hUV' _) = actL 6 Mod.ut0 γ (β v) * (β v)⁻¹
      rw [h1, map_mul, map_inv, hβe]
      rfl
    intro w
    exact hle (Subgroup.mem_top w)
  have E : ExtBot 6 ρ β'.ker β' :=
    { sq := fun m => IntMod.sq_eq_one m
      surj := hsurj
      equiv := hequiv
      ker := fun m => MonoidHom.mem_ker.symm
      fix := fun γ a ha => by
        obtain ⟨g, hg⟩ := exists_conv_rep hV hLV (π γ)
        rw [hρrep γ g hg]
        have ha' : a.val ∈ centralizer (L : Set G) :=
          (hβk (incIntMod hU hV hUV' a)).1 (MonoidHom.mem_ker.1 ha)
        refine IntMod.val_injective ?_
        rw [convI_apply_val]
        have := Subgroup.mem_centralizer_iff.1 ha' g g.2
        show (g : G) * a.val * (g : G)⁻¹ = a.val
        rw [this, mul_inv_cancel_right] }
  have hcommG : commG ρ = ⊤ := by
    let Cm : Subgroup G := (commG ρ).map
      { toFun := IntMod.val
        map_one' := rfl
        map_mul' := fun a b => IntMod.val_mul a b }
    have hle : ⁅U, L⁆ ≤ Cm := by
      rw [Subgroup.commutator_le]
      intro u hu l hl
      obtain ⟨γ, hγ⟩ := hπs ⟨convI hV ⟨l, hLV hl⟩, convI_mem_autI hV hl (hLV hl)⟩
      have hγ' : convI hV ⟨(⟨l, hl⟩ : ↥L), hLV hl⟩ = (π γ : MulAut (IntMod V hV)) :=
        (congrArg Subtype.val hγ).symm
      have hρl := hρrep γ ⟨l, hl⟩ hγ'
      have hmem : ρ γ (IntMod.mk hU ⟨u, hu⟩)⁻¹ * IntMod.mk hU ⟨u, hu⟩ ∈ commG ρ := by
        have := mul_inv_mem_commG (ρ := ρ) γ (IntMod.mk hU ⟨u, hu⟩)⁻¹
        rwa [inv_inv] at this
      refine ⟨_, hmem, ?_⟩
      have hcm := IntMod.val_comm (ρ γ (IntMod.mk hU ⟨u, hu⟩)⁻¹) (IntMod.mk hU ⟨u, hu⟩)
      rw [hρl, convI_apply_val] at hcm
      show (ρ γ (IntMod.mk hU ⟨u, hu⟩)⁻¹ * IntMod.mk hU ⟨u, hu⟩).val = ⁅u, l⁆
      rw [IntMod.val_mul, hρl, convI_apply_val, commutatorElement_def]
      show l * u⁻¹ * l⁻¹ * u = u * l * u⁻¹ * l⁻¹
      have hcm' : l * u⁻¹ * l⁻¹ * u = u * (l * u⁻¹ * l⁻¹) := hcm
      rw [hcm']
      group
    rw [eq_top_iff]
    intro c _
    have hcU : c.val ∈ ⁅U, L⁆ := by
      rw [hUL]
      exact c.val_mem
    have hc : c.val ∈ Cm := hle hcU
    obtain ⟨c', hc', hcc'⟩ := hc
    have : c' = c := IntMod.val_injective hcc'
    rw [← this]
    exact hc'
  have hcomm : β'.ker ≤ commG ρ := by
    rw [hcommG]
    exact le_top
  have hA := card_le_two_of_twoClass (n := 6) (by norm_num) E hcomm
    (H1_natural_even (Or.inl rfl))
  have hpos : 0 < Nat.card β'.ker := Nat.card_pos
  rcases (show Nat.card β'.ker = 1 ∨ Nat.card β'.ker = 2 by omega) with h1 | h2
  · have hbot : β'.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective β' := (MonoidHom.ker_eq_bot_iff β').1 hbot
    exact ⟨Mod.ut0, Or.inl rfl, ⟨KModel.ofModIso (Or.inl rfl)
      (MulEquiv.ofBijective β' ⟨hinj, hsurj⟩) ρ hequiv (autI hU L) hρtop⟩⟩
  · obtain ⟨Φ, hΦ⟩ := exists_iso_core (n := 6) (by norm_num) (Or.inl rfl) E hcomm h2
    exact ⟨Mod.u0, Or.inr rfl, ⟨KModel.ofModIso (Or.inr rfl) Φ ρ hΦ (autI hU L) hρtop⟩⟩

end CFSG.Quasithin.H13.U3.GC137

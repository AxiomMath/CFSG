module

public import CFSG.Quasithin.Background.B2FactorizationSum
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.JonesParshallCurtisInj
public import CFSG.Quasithin.Background.JonesParshallSL5Wedge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis

variable {V : Type} [CommGroup V]

@[reducible] noncomputable def zmod2Mod (h2 : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, h2, ofMul_one]

@[expose] def mulAutAdd : MulAut V →* AddMonoid.End (Additive V) where
  toFun f := (MulEquiv.toAdditive f).toAddMonoidHom
  map_one' := rfl
  map_mul' _ _ := rfl

section Rep

variable [Module (ZMod 2) (Additive V)] {L : Subgroup (MulAut V)}

noncomputable abbrev repOf (φ : ↥L ≃* G5) : Representation (ZMod 2) G5 (Additive V) :=
  repOfEnd (mulAutAdd.comp (L.subtype.comp φ.symm.toMonoidHom))

theorem repOf_apply (φ : ↥L ≃* G5) (g : G5) (v : V) :
    repOf φ g (Additive.ofMul v) = Additive.ofMul (((φ.symm g : ↥L) : MulAut V) v) := rfl

theorem repOf_apply_iso (φ : ↥L ≃* G5) (h : ↥L) (v : V) :
    repOf φ (φ h) (Additive.ofMul v) = Additive.ofMul ((h : MulAut V) v) := by
  rw [repOf_apply, MulEquiv.symm_apply_apply]

theorem isSimpleRep_repOf [Nontrivial V] (φ : ↥L ≃* G5)
    (hirr : ∀ W : Subgroup V, (∀ h ∈ L, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    IsSimpleRep (repOf φ) := by
  refine ⟨inferInstance, fun W hW => ?_⟩
  let W' : Subgroup V :=
    { carrier := {v | Additive.ofMul v ∈ W}
      mul_mem' := fun ha hb => W.add_mem ha hb
      one_mem' := W.zero_mem
      inv_mem' := fun ha => W.neg_mem ha }
  have hinv : ∀ h ∈ L, ∀ w ∈ W', (h : MulAut V) w ∈ W' := by
    intro h hh w hw
    have := hW (φ ⟨h, hh⟩) (Additive.ofMul w) hw
    rw [repOf_apply_iso] at this
    exact this
  rcases hirr W' hinv with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : Additive.toMul x ∈ W' := hx
    rw [h, Subgroup.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hx'
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : Additive.toMul x ∈ W' := h ▸ Subgroup.mem_top _
    exact hx'

theorem card_eq_two_pow_finrank [Finite V] :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
  have : Fintype (Additive V) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
  exact h

end Rep

theorem irr_of_isIrrSec {L : Subgroup (MulAut V)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) :
    ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ := by
  intro J hJ
  have hinv : XMod.IsInv ↥L J := by
    intro l v hv
    have h2 : l • v = (l : MulAut V) v := by simp [Subgroup.smul_def, MulAut.smul_def]
    rw [h2]
    exact hJ l l.2 v hv
  exact hirr.2 J hinv bot_le le_top

variable [Finite V]

theorem index_fixV_le_prod {ι : Type*} [Fintype ι] (B : ι → Subgroup (MulAut V))
    {X : Subgroup (MulAut V)} (hX : X ≤ ⨆ i, B i) :
    (fixV X).index ≤ ∏ i, (fixV (B i)).index := by
  have h1 : ⨅ i, fixV (B i) ≤ fixV X := by
    rw [← fixV_iSup]
    exact B1.fixV_le_fixV hX
  have h2 := Subgroup.index_iInf_le (fun i => fixV (B i))
  have h3 : (fixV X).index ∣ (⨅ i, fixV (B i)).index := Subgroup.index_dvd_of_le h1
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) h3).trans h2

theorem card_le_prod_index {ι : Type*} [Fintype ι] (B : ι → Subgroup (MulAut V))
    {X : Subgroup (MulAut V)} (hX : X ≤ ⨆ i, B i) (hfix : fixV X = ⊥) :
    Nat.card V ≤ ∏ i, (fixV (B i)).index := by
  have := index_fixV_le_prod B hX
  rwa [hfix, Subgroup.index_bot] at this

theorem index_fixV_mono {A B : Subgroup (MulAut V)} (hBA : B ≤ A) :
    (fixV B).index ≤ (fixV A).index :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le (B1.fixV_le_fixV hBA))

end CFSG.Quasithin.B42Ln

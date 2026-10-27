module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace TwE6TB

@[expose] def GGTorusWeylModel (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ (Φ : A ≃* Multiplicative (Fin 6 → ZMod p)) (w : Fin 6 → L'),
    (∀ i, ∀ a ∈ A, (w i * (a (w i))⁻¹) ^ p = 1 ∧
      ∀ a' ∈ A, a' (w i * (a (w i))⁻¹) = w i * (a (w i))⁻¹) ∧
    ∀ (i : Fin 6) (a : A), MulAut.conj (w i) * (a : MulAut L') * (MulAut.conj (w i))⁻¹ =
      ((Φ.symm (Multiplicative.ofAdd (reflE6 p i (Multiplicative.toAdd (Φ a)))) : A) :
        MulAut L')

@[expose] def GGTorusModelSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A → GGTorusWeylModel p A

theorem ggTorusIrredSCr_of_modelSCr {p r : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGTorusModelSCr p r R I) : GGTorusIrredSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  obtain ⟨Φ, w, hW, hact⟩ := h L' ψ hψ hker hperf A hA hAI hr h3 hsc
  refine ⟨Set.range w, ?_, ?_, ?_, ?_⟩
  · rintro n ⟨i, rfl⟩ a ha
    exact hW i a ha
  ·
    intro A' hA'A hinv
    set U : Subgroup (Multiplicative (Fin 6 → ZMod p)) := (A'.subgroupOf A).map Φ.toMonoidHom
      with hU
    let G : AddSubgroup (Fin 6 → ZMod p) :=
      { carrier := {v | Multiplicative.ofAdd v ∈ U}
        add_mem' := fun {a b} ha hb => by
          have h := U.mul_mem (show Multiplicative.ofAdd a ∈ U from ha)
            (show Multiplicative.ofAdd b ∈ U from hb)
          rwa [← ofAdd_add] at h
        zero_mem' := by
          have h := U.one_mem
          rwa [← ofAdd_zero] at h
        neg_mem' := fun {a} ha => by
          have h := U.inv_mem (show Multiplicative.ofAdd a ∈ U from ha)
          rwa [← ofAdd_neg] at h }
    have hmemG : ∀ x : A, (x : MulAut L') ∈ A' ↔ Multiplicative.toAdd (Φ x) ∈ G := by
      intro x
      constructor
      · intro hx
        exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Φ.injective hyx
        subst this
        exact Subgroup.mem_subgroupOf.mp hy
    have hG : ∀ i, ∀ v ∈ G, reflE6 p i v ∈ G := by
      intro i v hv
      obtain ⟨a, ha, hav⟩ := hv
      have haA' : (a : MulAut L') ∈ A' := Subgroup.mem_subgroupOf.mp ha
      have h1 := hinv (w i) ⟨i, rfl⟩ _ haA'
      rw [hact i a] at h1
      have h2 := (hmemG _).mp h1
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h2
      have h3 : Multiplicative.toAdd (Φ a) = v := congrArg Multiplicative.toAdd hav
      rwa [h3] at h2
    rcases eq_bot_or_eq_top_of_reflE6 hp5 G hG with h0 | h0
    · left
      rw [eq_bot_iff]
      intro a ha
      have h1 := (hmemG ⟨a, hA'A ha⟩).mp ha
      rw [h0, AddSubgroup.mem_bot] at h1
      have h2 : Φ ⟨a, hA'A ha⟩ = 1 := by
        rw [← ofAdd_toAdd (Φ ⟨a, hA'A ha⟩), h1]
        rfl
      have h3 : (⟨a, hA'A ha⟩ : A) = 1 := Φ.injective (by rw [h2, map_one])
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h3
    · right
      refine le_antisymm hA'A fun a ha => ?_
      exact (hmemG ⟨a, ha⟩).mpr (by rw [h0]; trivial)
  ·
    have hp2 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    refine ⟨w 0, ⟨0, rfl⟩, ((Φ.symm (Multiplicative.ofAdd (Pi.single 0 1))) : A),
      (Φ.symm (Multiplicative.ofAdd (Pi.single 0 1))).2, fun heq => ?_⟩
    have h1 := hact 0 (Φ.symm (Multiplicative.ofAdd (Pi.single 0 1)))
    rw [heq, MulEquiv.apply_symm_apply, toAdd_ofAdd, reflE6_single_self] at h1
    have h2 := Subtype.ext h1
    have h3 := Φ.symm.injective h2
    have h4 : (Pi.single 0 1 : Fin 6 → ZMod p) = - Pi.single 0 1 :=
      Multiplicative.ofAdd.injective h3
    have h5 := congrFun h4 0
    simp only [Pi.single_eq_same, Pi.neg_apply] at h5
    apply hp2
    linear_combination h5
  ·
    intro f hfA hfmul hfW
    let g : (Fin 6 → ZMod p) → (Fin 6 → ZMod p) := fun v =>
      Multiplicative.toAdd (Φ ⟨f ((Φ.symm (Multiplicative.ofAdd v) : A) : MulAut L'),
        hfA _ (Φ.symm (Multiplicative.ofAdd v)).2⟩)
    have hgadd : ∀ v v', g (v + v') = g v + g v' := by
      intro v v'
      have e1 : (Φ.symm (Multiplicative.ofAdd (v + v')) : A) =
          Φ.symm (Multiplicative.ofAdd v) * Φ.symm (Multiplicative.ofAdd v') := by
        rw [ofAdd_add, map_mul]
      simp only [g]
      rw [e1]
      have e2 : (⟨f ((Φ.symm (Multiplicative.ofAdd v) * Φ.symm (Multiplicative.ofAdd v') : A) :
          MulAut L'), hfA _ (Subgroup.mul_mem _ (Φ.symm (Multiplicative.ofAdd v)).2
            (Φ.symm (Multiplicative.ofAdd v')).2)⟩ : A) =
          ⟨f ((Φ.symm (Multiplicative.ofAdd v) : A) : MulAut L'),
            hfA _ (Φ.symm (Multiplicative.ofAdd v)).2⟩ *
          ⟨f ((Φ.symm (Multiplicative.ofAdd v') : A) : MulAut L'),
            hfA _ (Φ.symm (Multiplicative.ofAdd v')).2⟩ :=
        Subtype.ext (hfmul _ (Φ.symm (Multiplicative.ofAdd v)).2 _
          (Φ.symm (Multiplicative.ofAdd v')).2)
      rw [e2, map_mul, toAdd_mul]
    have hgcomm : ∀ i v, g (reflE6 p i v) = reflE6 p i (g v) := by
      intro i v
      set x : A := Φ.symm (Multiplicative.ofAdd v) with hx
      have hΦx : Φ x = Multiplicative.ofAdd v := by rw [hx, MulEquiv.apply_symm_apply]
      set y : A := ⟨f (x : MulAut L'), hfA _ x.2⟩ with hy
      have h1 := hact i x
      rw [hΦx, toAdd_ofAdd] at h1
      have h2 := hfW (w i) ⟨i, rfl⟩ _ x.2
      rw [h1] at h2
      have h3 := hact i y
      have hgv : g v = Multiplicative.toAdd (Φ y) := rfl
      have h4 : (⟨f ((Φ.symm (Multiplicative.ofAdd (reflE6 p i v)) : A) : MulAut L'),
          hfA _ (Φ.symm (Multiplicative.ofAdd (reflE6 p i v))).2⟩ : A) =
          Φ.symm (Multiplicative.ofAdd (reflE6 p i (Multiplicative.toAdd (Φ y)))) := by
        apply Subtype.ext
        show f ((Φ.symm (Multiplicative.ofAdd (reflE6 p i v)) : A) : MulAut L') = _
        rw [h2, h3]
      change Multiplicative.toAdd (Φ ⟨f ((Φ.symm (Multiplicative.ofAdd (reflE6 p i v)) : A) :
        MulAut L'), _⟩) = _
      rw [h4, MulEquiv.apply_symm_apply, toAdd_ofAdd, hgv]
    obtain ⟨c, hc⟩ := exists_smul_of_commute_reflE6 hp5 g hgadd hgcomm
    refine ⟨c.val, fun a ha => ?_⟩
    set x : A := ⟨a, ha⟩ with hx
    have hΦx : Multiplicative.ofAdd (Multiplicative.toAdd (Φ x)) = Φ x := ofAdd_toAdd _
    have h1 := hc (Multiplicative.toAdd (Φ x))
    simp only [g] at h1
    rw [hΦx, MulEquiv.symm_apply_apply] at h1
    have h2 : Φ ⟨f a, hfA a ha⟩ = Φ x ^ c.val := by
      rw [← ofAdd_toAdd (Φ ⟨f a, hfA a ha⟩), h1]
      have : c • Multiplicative.toAdd (Φ x) = c.val • Multiplicative.toAdd (Φ x) := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
      rw [this, ofAdd_nsmul, ofAdd_toAdd]
    have h3 : (⟨f a, hfA a ha⟩ : A) = x ^ c.val := Φ.injective (by rw [h2, map_pow])
    have h4 := congrArg Subtype.val h3
    simpa using h4

end TwE6TB

@[expose] def GGTwE6TorusModelInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → 5 ≤ p →
    TwE6TB.GGTorusModelSCr p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

theorem ggTwE6TorusIrredInput_of_model (h : GGTwE6TorusModelInput) : GGTwE6TorusIrredInput :=
  fun K _ _ n p hn hK hp hpn hp5 =>
    have := Fact.mk hp
    TwE6TB.ggTorusIrredSCr_of_modelSCr hp5 (h K n p hn hK hp hpn hp5)

section Certs


theorem ggTableBCxInputOn_of_not_twE6TB_of_model (hX : GGTwE6InnerDiagBound2LInput)
    (hM : GGTwE6TorusModelInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGTableBCxInputOn S :=
  ggTableBCxInputOn_of_not_twE6TB hX (ggTwE6TorusIrredInput_of_model hM) h

theorem ggTableBModuleInputOn_of_not_twE6TB_of_model (hX : GGTwE6InnerDiagBound2LInput)
    (hM : GGTwE6TorusModelInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGTableBModuleInputOn S :=
  ggTableBModuleInputOn_of_not_twE6TB hX (ggTwE6TorusIrredInput_of_model hM) h

theorem ggTableBActionInputOn_of_not_twE6TB_of_model (hX : GGTwE6InnerDiagBound2LInput)
    (hM : GGTwE6TorusModelInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGTableBActionInputOn S :=
  ggTableBActionInputOn_of_not_twE6TB hX (ggTwE6TorusIrredInput_of_model hM) h

theorem ggLNoInvariantLineInputOn_of_not_twE6TB_of_model (hM : GGTwE6TorusModelInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGLNoInvariantLineInputOn S :=
  ggLNoInvariantLineInputOn_of_not_twE6TB (ggTwE6TorusIrredInput_of_model hM) h

end Certs

end CFSG.StandardType

end

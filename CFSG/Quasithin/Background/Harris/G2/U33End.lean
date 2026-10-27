module

public import CFSG.Quasithin.Background.Harris.G2.U33Setup
public import CFSG.Quasithin.Background.Harris.G2.End
public import CFSG.Quasithin.Background.SmithB42U33SixProof
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_zero_of_apply_eq_zero {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤) {c : Module.End (ZMod 2) V}
    (hc : c ∈ endCommutant L) {w : V} (hw : w ≠ 0) (hcw : c w = 0) : c = 0 := by
  obtain ⟨-, -, hI⟩ := hirr
  have hinv : CFSG.Quasithin.G11.Invariant L (LinearMap.ker c) := fun l hl u hu => by
    rw [LinearMap.mem_ker] at hu ⊢
    rw [CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_apply_comm hc hl, hu,
      map_zero]
  rcases hI _ hinv bot_le le_top with h | h
  · have hwU : w ∈ LinearMap.ker c := hcw
    rw [h, Submodule.mem_bot] at hwU
    exact absurd hwU hw
  · ext v
    have : v ∈ LinearMap.ker c := h ▸ Submodule.mem_top
    simpa using this

theorem natCard_endCommutant_eq_two {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤) {P : Subgroup (GLV V)}
    (hPL : P ≤ L) {w₀ : V} (hw₀ : w₀ ≠ 0) (hw₀P : ∀ p ∈ P, (p : GLV V) w₀ = w₀)
    (hP : ∀ v : V, (∀ p ∈ P, (p : GLV V) v = v) → v = 0 ∨ v = w₀) :
    Nat.card (endCommutant L) = 2 := by
  have hnt : Nontrivial V := by
    obtain ⟨-, hlt, -⟩ := hirr
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hlt
    exact ⟨⟨v, 0, fun h => hv (h ▸ Submodule.zero_mem _)⟩⟩
  have hc01 : ∀ c : ↥(endCommutant L), c = 0 ∨ c = 1 := by
    intro c
    have hcP : ∀ p ∈ P, (p : GLV V) ((c : Module.End (ZMod 2) V) w₀) =
        (c : Module.End (ZMod 2) V) w₀ := fun p hp => by
      rw [← CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_apply_comm c.2 (hPL hp),
        hw₀P p hp]
    rcases hP _ hcP with h0 | h1
    · left
      exact Subtype.ext (eq_zero_of_apply_eq_zero hirr c.2 hw₀ h0)
    · right
      have hc1 : ((c : Module.End (ZMod 2) V) - 1) ∈ endCommutant L :=
        Subalgebra.sub_mem _ c.2 (Subalgebra.one_mem _)
      have := eq_zero_of_apply_eq_zero hirr hc1 hw₀ (by simp [h1])
      exact Subtype.ext (sub_eq_zero.mp this)
  have h01 : (0 : ↥(endCommutant L)) ≠ 1 := fun h =>
    one_ne_zero (congrArg (fun c : ↥(endCommutant L) => (c : Module.End (ZMod 2) V)) h).symm
  refine Nat.card_eq_two_iff.2 ⟨0, 1, h01, ?_⟩
  ext c
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact hc01 c

theorem exists_two_fixed {W : Type*} [Group W] (F : W → Prop) (h1 : F 1)
    (hcard : Nat.card {v : W // F v} = 2) :
    ∃ w₀, w₀ ≠ 1 ∧ F w₀ ∧ ∀ v, F v → v = 1 ∨ v = w₀ := by
  rw [Nat.card_eq_two_iff' (⟨1, h1⟩ : {v : W // F v})] at hcard
  obtain ⟨y, hy, huniq⟩ := hcard
  refine ⟨y.1, fun h => hy (Subtype.ext h), y.2, fun v hv => ?_⟩
  by_cases hv1 : v = 1
  · exact Or.inl hv1
  · exact Or.inr (congrArg Subtype.val (huniq ⟨v, hv⟩ fun h => hv1 (congrArg Subtype.val h)))

section U33


theorem endIsField_u33 [Finite V] {L : Subgroup (GLV V)} (hs : IsSimpleGroup ↥L)
    (hm : StatedClassicalModel ↥L .PSU 3 3 1) (hirr : IsIrr L ⊤)
    (hdim : Module.finrank (ZMod 2) V = 6) : EndIsField L 1 := by
  classical
  have hP : B42TypeU33 ↥L := b42TypeU33_of_simple hs hm
  obtain ⟨θ⟩ := B42U33.nonempty_equiv_g2Derived hP
  let η : U33G ≃* ↥L := B42U33.u33EquivDerived.trans θ.symm
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hW2 : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
  have hW : ∀ w : Multiplicative V, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW2 w
  have hcard : Nat.card (Multiplicative V) = 2 ^ 6 := by rw [natCard_multiplicative, hdim]
  have hLb : Nat.card ↥(toMulSub L) = 6048 :=
    (natCard_toMulSub L).trans (B42U33.card_of_b42TypeU33 hP)
  let ψ : U33G →* MulAut (Multiplicative V) :=
    (toMulSub L).subtype.comp ((toMulSubEquiv L).toMonoidHom.comp η.toMonoidHom)
  have hψ : ∀ g v, ψ g (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (((η g : ↥L) : GLV V) v) := fun _ _ => rfl
  have hfix : ∀ v : Multiplicative V, (∀ g, ψ g v = v) → v = 1 := by
    intro v hv
    refine B42U33.eq_one_of_fixed hW hcard ((toMulSubEquiv L).symm.isSimpleGroup) hLb
      (L := toMulSub L) fun l' hl' => ?_
    obtain ⟨l, hl, rfl⟩ := hl'
    have := hv (η.symm ⟨l, hl⟩)
    change linEquivMulAut ((η (η.symm ⟨l, hl⟩) : ↥L) : GLV V) v = v at this
    rwa [MulEquiv.apply_symm_apply] at this
  let S : Sylow 2 U33G := u33_syl.1.toSylow u33_syl.2
  have h2 := H13.U3.u33_sylow_fixed_card_two hW2 (by rw [hcard]; norm_num) ψ hfix S
  obtain ⟨w₀', hw₀1, hw₀S, hw₀⟩ := exists_two_fixed (fun v : Multiplicative V => ∀ s ∈ S, ψ s v = v)
    (fun s _ => map_one (ψ s)) h2
  let P : Subgroup (GLV V) := (S : Subgroup U33G).map (L.subtype.comp η.toMonoidHom)
  have hPL : P ≤ L := by
    rintro _ ⟨s, -, rfl⟩
    exact (η s).2
  refine endIsField_of_natCard hirr (n := 1) ?_
  refine (natCard_endCommutant_eq_two hirr hPL (w₀ := Multiplicative.toAdd w₀') ?_ ?_ ?_).trans
    (pow_one 2).symm
  · intro h
    exact hw₀1 (by simpa using h)
  · rintro _ ⟨s, hs', rfl⟩
    have h3 : ψ s (Multiplicative.ofAdd (Multiplicative.toAdd w₀')) =
        Multiplicative.ofAdd (Multiplicative.toAdd w₀') := hw₀S s hs'
    rw [hψ] at h3
    exact congrArg Multiplicative.toAdd h3
  · intro v hv
    have := hw₀ (Multiplicative.ofAdd v) fun s hs' => by
      have h1 := hv _ ⟨s, hs', rfl⟩
      rw [hψ]
      exact congrArg Multiplicative.ofAdd h1
    rcases this with h | h
    · left; simpa using congrArg Multiplicative.toAdd h
    · right; simpa using congrArg Multiplicative.toAdd h

end U33

end CFSG.Quasithin.G11.Harris.G2

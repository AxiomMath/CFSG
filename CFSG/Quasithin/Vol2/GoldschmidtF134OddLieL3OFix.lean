module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieDef

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup
open scoped Pointwise commutatorElement

@[expose] def OddInvariantSet {G : Type*} [Group G] (p : ℕ) (P : Subgroup G) : Prop :=
  ∃ X : Set (Subgroup G), X.Finite ∧ Odd X.ncard ∧ (∀ U ∈ X, U ≤ P ∧ Nat.card U = p) ∧
    ∀ φ : G ≃* G, P.map φ.toMonoidHom = P → ∀ U ∈ X, U.map φ.toMonoidHom ∈ X

theorem OddInvariantSet.of_mulEquiv {G G' : Type*} [Group G] [Group G'] {p : ℕ} {P : Subgroup G}
    (e : G ≃* G') (h : OddInvariantSet p P) : OddInvariantSet p (P.map e.toMonoidHom) := by
  obtain ⟨X, hXf, hXo, hXs, hXi⟩ := h
  have hinj : Function.Injective (Subgroup.map e.toMonoidHom : Subgroup G → Subgroup G') :=
    Subgroup.map_injective e.injective
  refine ⟨Subgroup.map e.toMonoidHom '' X, hXf.image _, ?_, ?_, ?_⟩
  · rw [Set.ncard_image_of_injective _ hinj]
    exact hXo
  · rintro _ ⟨U, hU, rfl⟩
    obtain ⟨h1, h2⟩ := hXs U hU
    exact ⟨Subgroup.map_mono h1, by rw [Subgroup.card_map_of_injective e.injective, h2]⟩
  · rintro φ hφ _ ⟨U, hU, rfl⟩
    have hψ : P.map (e.trans (φ.trans e.symm)).toMonoidHom = P := by
      have h1 : P.map (e.trans (φ.trans e.symm)).toMonoidHom =
          ((P.map e.toMonoidHom).map φ.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      rw [h1, hφ]
      ext x
      simp
    refine ⟨_, hXi _ hψ U hU, ?_⟩
    rw [Subgroup.map_map, Subgroup.map_map]
    ext x
    simp

theorem mem_normalizer_map_subtype {A : Type*} [Group A] {L : Subgroup A} [L.Normal] (t : A)
    (Q : Subgroup ↥L) (hQ : ∀ y : L, MulAut.conjNormal t y ∈ Q ↔ y ∈ Q) :
    t ∈ Subgroup.normalizer ((Q.map L.subtype : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (hQ x).2 hx, by simp [MulAut.conjNormal_apply]⟩
  · rintro ⟨y, hy, hyg⟩
    have hyg' : (y : A) = t * g * t⁻¹ := hyg
    have hgL : g ∈ L := by
      have := (inferInstance : L.Normal).conj_mem _ y.2 t⁻¹
      rwa [hyg', show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at this
    refine ⟨⟨g, hgL⟩, (hQ ⟨g, hgL⟩).1 ?_, rfl⟩
    have h1 : MulAut.conjNormal t (⟨g, hgL⟩ : L) = y := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hyg']
    rw [h1]
    exact hy

theorem false_of_oddInvariantSet {A : Type} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    {L P T : Subgroup A} {G : Type} [Group G] (hcfg : OddCfg p L P T) (e : ↥L ≃* G)
    (hP2 : Nat.card P = p ^ 2)
    (h : OddInvariantSet p ((P.subgroupOf L).map e.toMonoidHom)) : False := by
  classical
  have hLn : L.Normal := hcfg.normal
  have : Finite G := Finite.of_equiv ↥L e.toEquiv
  obtain ⟨X, hXf, hXo, hXs, hXi⟩ := h
  set PG : Subgroup G := (P.subgroupOf L).map e.toMonoidHom with hPG
  let α : A →* MulAut G := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : A →* MulAut ↥L)
  have hα : ∀ (t : A) (y : ↥L), α t (e y) = e (MulAut.conjNormal t y) := fun t y => by
    simp [α, MulAut.congr_apply]
  set W : Subgroup A := T ⊓ Subgroup.normalizer (P : Set A) with hW
  have hWp : IsPGroup 2 ↥W := hcfg.sylow.2.1.to_le inf_le_left
  have hαP : ∀ w ∈ W, PG.map (α w).toMonoidHom = PG := by
    intro w hw
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (f := (α w).toMonoidHom) (α w).injective).symm.le
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨MulAut.conjNormal w y, ?_, (hα w y).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.1 hw.2 y).1 (Subgroup.mem_subgroupOf.1 hy)
  let act : MulAction W (Subgroup G) := MulAction.compHom (Subgroup G) (α.comp W.subtype)
  let S : SubMulAction W (Subgroup G) :=
    { carrier := X
      smul_mem' := fun w U hU => hXi (α w) (hαP w w.2) U hU }
  have hcard : ¬ 2 ∣ Nat.card S := by
    have : Nat.card S = X.ncard := Nat.card_coe_set_eq X
    rw [this]
    exact Nat.not_even_iff_odd.2 hXo |> fun h => by simpa [even_iff_two_dvd] using h
  obtain ⟨⟨U, hUX⟩, hUfix⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hWp S hcard
  have hfix : ∀ t ∈ W, U.map (α t).toMonoidHom = U := fun t ht =>
    congrArg Subtype.val (hUfix ⟨t, ht⟩)
  obtain ⟨hUP, hUc⟩ := hXs U hUX
  set UL : Subgroup ↥L := U.map e.symm.toMonoidHom with hUL
  have hmemUL : ∀ y : ↥L, y ∈ UL ↔ e y ∈ U := fun y => by
    rw [hUL, Subgroup.mem_map_equiv]
    simp
  have hUAP : UL.map L.subtype ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hUP ((hmemUL y).1 hy))
    have : z = y := e.injective hzy
    subst this
    exact Subgroup.mem_subgroupOf.1 hz
  have hUAcard : Nat.card (UL.map L.subtype) = p := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hUL,
      Subgroup.card_map_of_injective e.symm.injective, hUc]
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer ((UL.map L.subtype : Subgroup A) : Set A) := by
    intro t ht
    refine mem_normalizer_map_subtype t UL fun y => ?_
    rw [hmemUL, hmemUL, ← hα]
    constructor
    · intro h
      have h1 : α t (e y) ∈ U.map (α t).toMonoidHom := by rw [hfix t ht]; exact h
      simpa using (Subgroup.mem_map_equiv.1 h1)
    · intro h
      rw [← hfix t ht]
      exact Subgroup.mem_map.2 ⟨_, h, rfl⟩
  have hcomm : ⁅P, P⁆ = ⊥ := by
    have : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP2
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have := this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    rw [commutatorElement_def, Subgroup.mem_bot]
    have h2 : a * b = b * a := congrArg Subtype.val this
    calc a * b * a⁻¹ * b⁻¹ = b * a * a⁻¹ * b⁻¹ := by rw [h2]
      _ = 1 := by group
  rcases hcfg.irred (UL.map L.subtype) (hcomm ▸ bot_le) hUAP hnorm with h | h
  · rw [h, hcomm, Subgroup.card_bot] at hUAcard
    exact hp.out.one_lt.ne hUAcard
  · rw [h, hP2] at hUAcard
    have h2 : p ^ 2 = p ^ 1 := by rw [hUAcard, pow_one]
    have := Nat.pow_right_injective hp.out.two_le h2
    omega

end CFSG.Quasithin.H13.NQCore

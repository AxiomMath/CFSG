module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def OddFixedBorelTits (X : Type*) [Group X] (T : Subgroup (MulAut X)) : Prop :=
  ∀ U : Subgroup X, IsPGroup 2 U → oddFixed X T ≤ Subgroup.normalizer (U : Set X) → U = ⊥

@[expose] def AutTorusBorelTits (X : Type*) [Group X] : Prop :=
  ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
    InnerThreeFixed X E →
    (∃ x : X, orderOf x = 3 ∧ x ∉ Subgroup.center X ∧ ∀ e ∈ E, e x = x) →
    ∀ T : Subgroup (MulAut X), IsPGroup 2 T → T ≠ ⊥ →
      T ≤ Subgroup.centralizer (E : Set (MulAut X)) → OddFixedBorelTits X T

@[expose] def OutTwoCyclic (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup (MulAut X), IsPGroup 2 P →
    P ⊓ (MulAut.conj : X →* MulAut X).range = ⊥ → IsCyclic P

theorem autElliptic_of_oddFixedBorelTits (hZ : Subgroup.center X = ⊥) (hO : OutTwoCyclic X)
    {T : Subgroup (MulAut X)} (hBT : OddFixedBorelTits X T) : AutElliptic X T := by
  intro P hP hPN
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hc : u ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun σ : MulAut X => σ g) hu
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * u = u * g * u⁻¹ * u := by rw [this]
        _ = u * g := by group
    rwa [hZ] at hc
  set U : Subgroup X := P.comap MulAut.conj with hU
  have hU2 : IsPGroup 2 U := hP.comap_of_injective _ hinj
  have hUN : oddFixed X T ≤ Subgroup.normalizer (U : Set X) := by
    intro d hd
    have hN := hPN ⟨d, hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro u
    change MulAut.conj u ∈ P ↔ MulAut.conj (d * u * d⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hN _
  have hUbot := hBT U hU2 hUN
  have hPI : ∀ u : X, MulAut.conj u ∈ P → u = 1 := by
    intro u hu
    have : u ∈ U := hu
    rw [hUbot] at this
    exact this
  refine ⟨fun p hp d hd => ?_, hO P hP ?_⟩
  · have h1 : MulAut.conj d * p * (MulAut.conj d)⁻¹ * p⁻¹ ∈ P :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hPN ⟨d, hd, rfl⟩) p).mp hp) (inv_mem hp)
    have h2 : MulAut.conj d * p * (MulAut.conj d)⁻¹ * p⁻¹ = MulAut.conj (d * (p d)⁻¹) := by
      rw [map_mul, map_inv, ← mul_conj_mul_inv p d]
      group
    rw [h2] at h1
    have h3 := hPI _ h1
    rw [mul_inv_eq_one] at h3
    exact h3.symm
  · rw [eq_bot_iff]
    rintro _ ⟨hp, u, rfl⟩
    rw [Subgroup.mem_bot, hPI u hp, map_one]

theorem outTwoCyclic_of_mulEquiv (e : X ≃* Y) (h : OutTwoCyclic Y) : OutTwoCyclic X := by
  intro P hP hPI
  set Φ := MulAut.congr e with hΦ
  have hP' : IsPGroup 2 (P.map Φ.toMonoidHom) := hP.map _
  have hPI' : P.map Φ.toMonoidHom ⊓ (MulAut.conj : Y →* MulAut Y).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨p, hp, rfl⟩, y, hy⟩
    have hp' : p = MulAut.conj (e.symm y) := by
      apply Φ.injective
      rw [congr_conj, MulEquiv.apply_symm_apply]
      exact (show Φ p = MulAut.conj y from hy.symm)
    have : p ∈ P ⊓ (MulAut.conj : X →* MulAut X).range := ⟨hp, e.symm y, hp'.symm⟩
    rw [hPI, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    change Φ p = 1
    rw [this, map_one]
  have hcyc := h _ hP' hPI'
  have hsurj : Function.Surjective
      ((Φ.symm.toMonoidHom.comp (P.map Φ.toMonoidHom).subtype).codRestrict P fun q => by
        obtain ⟨_, ⟨p, hp, rfl⟩⟩ := q
        change Φ.symm (Φ p) ∈ P
        rwa [MulEquiv.symm_apply_apply]) := by
    rintro ⟨p, hp⟩
    refine ⟨⟨Φ p, p, hp, rfl⟩, ?_⟩
    apply Subtype.ext
    change Φ.symm (Φ p) = p
    exact MulEquiv.symm_apply_apply Φ p
  exact isCyclic_of_surjective _ hsurj

theorem oddFixedBorelTits_of_map_congr (e : X ≃* Y) {T : Subgroup (MulAut X)}
    (h : OddFixedBorelTits Y (T.map (MulAut.congr e).toMonoidHom)) : OddFixedBorelTits X T := by
  intro U hU hUN
  have hU' : IsPGroup 2 (U.map e.toMonoidHom) := hU.map _
  have hUN' : oddFixed Y (T.map (MulAut.congr e).toMonoidHom) ≤
      Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [oddFixed_map_congr]
    rintro _ ⟨d, hd, rfl⟩
    have hN := hUN hd
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨d * u * d⁻¹, (hN u).mp hu, by simp [map_mul, map_inv]⟩
    · rintro ⟨w, hw, hwe⟩
      have hwe' : e w = e d * y * (e d)⁻¹ := hwe
      refine ⟨d⁻¹ * w * d, ?_, ?_⟩
      · exact (hN (d⁻¹ * w * d)).mpr (by rwa [show d * (d⁻¹ * w * d) * d⁻¹ = w by group])
      · change e (d⁻¹ * w * d) = y
        rw [map_mul, map_mul, map_inv, hwe']
        group
  have hbot := h _ hU' hUN'
  rw [eq_bot_iff]
  intro u hu
  have : e u ∈ U.map e.toMonoidHom := ⟨u, hu, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact e.injective (this.trans (map_one e).symm)

theorem autTorusBorelTits_of_mulEquiv (e : X ≃* Y) (h : AutTorusBorelTits Y) :
    AutTorusBorelTits X := by
  intro E hE hE9 hinner hfix T hT hT1 hTE
  set Φ := MulAut.congr e with hΦ
  have hinj : Function.Injective Φ.toMonoidHom := Φ.injective
  refine oddFixedBorelTits_of_map_congr e (h (E.map Φ.toMonoidHom) ?_ ?_ ?_ ?_
    (T.map Φ.toMonoidHom) (hT.map _) ?_ ?_)
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨_, ⟨α, hα, rfl⟩⟩ := a
      obtain ⟨_, ⟨β, hβ, rfl⟩⟩ := b
      apply Subtype.ext
      change Φ α * Φ β = Φ β * Φ α
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨α, hα⟩ ⟨β, hβ⟩)
    · obtain ⟨α, hα, rfl⟩ := ha
      change Φ α ^ 3 = 1
      rw [← map_pow, hE.2 α hα, map_one]
  · rwa [Subgroup.card_map_of_injective hinj]
  · intro y hy3 hyfix
    have hx3 : orderOf (e.symm y) = 3 := by rwa [MulEquiv.orderOf_eq]
    have hxfix : ∀ α ∈ E, α (e.symm y) = e.symm y := by
      rw [← fixed_map_congr_iff e E (e.symm y), MulEquiv.apply_symm_apply]
      exact hyfix
    refine ⟨MulAut.conj (e.symm y), hinner _ hx3 hxfix, ?_⟩
    change Φ (MulAut.conj (e.symm y)) = MulAut.conj y
    rw [congr_conj, MulEquiv.apply_symm_apply]
  · obtain ⟨x, hx3, hxZ, hxfix⟩ := hfix
    exact ⟨e x, by rwa [MulEquiv.orderOf_eq], fun h => hxZ ((mem_center_iff_of_mulEquiv e x).mp h),
      (fixed_map_congr_iff e E x).mpr hxfix⟩
  · intro h1
    apply hT1
    rw [← map_congr_symm_map_congr e T, h1, Subgroup.map_bot]
  · rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨α, hα, rfl⟩
    change Φ α * Φ t = Φ t * Φ α
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hTE ht)) α hα]

end CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
